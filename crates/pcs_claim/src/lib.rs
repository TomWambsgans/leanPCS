// Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The commitment and the opening call leanVM's WHIR
// (https://github.com/leanEthereum/leanVM, commit c445e3d5, vendored in crates/vendor/leanvm-c445e3d5) unchanged, as
// crates/membership/quotient/src/opening.rs does (its transcript shape and lane-tensor weights are reused here).
//! The EIP draft's PCS claim (`eip-draft_leanPCS.md`, "PCS claims"; `docs/PCS_CLAIM.md`): that the multilinear
//! polynomial `f` over `K = GF(2^64)` in `n` variables committed to as `commitment` takes the value `value` (in
//! `E = GF(2^192)`) at `point` (in `E^n`), encoded as
//!
//! ```text
//! PCS_claim = version (1 byte) || n (1 byte) || commitment (56 bytes) || point (24 * n bytes) || value (24 bytes)
//! ```
//!
//! where `commitment` is the 32-byte Merkle root of leanVM's WHIR commitment to `f` and the 24-byte out-of-domain
//! answer `f(z)`, `z` derived from the root alone ([`ood_point`]). The root binds `f` to a short list of
//! polynomials (WHIR at rate `1/2` is in the list-decoding regime and takes no out-of-domain sample of its own at
//! its first level); the answer at `z` singles one of them out, so claims on one commitment, opened separately, are
//! all of one polynomial.
//!
//! - [`PcsClaim`]: the claim, [`PcsClaim::encode`], [`PcsClaim::decode`] (well-formedness), [`PcsClaim::hash`]
//!   (`keccak256(PCS_claim)`, the dependency's payload).
//! - [`commit`] (owning the words) and [`commit_words`] (borrowing them): the commitment to `2^n` words (`n` from
//!   [`MIN_VARIABLES`] to [`MAX_VARIABLES`]), its root and out-of-domain answer.
//! - [`open`] ([`open_batch`] for several claims on one commitment): one opening proving `f(z) = ood` and
//!   `f(point) = value` together, at one random combination; [`verify`]: the EIP's `pcs_verify(PCS_claim,
//!   opening_proof)` for [`VERSION`].
//!
//! **Variables.** `f(x) = Σ_i f_i Π_j (x_j if bit j of i is 1, else 1 - x_j)`, `f_i` the `i`-th committed word,
//! bit 0 the least significant: `x_0 .. x_{n-7}` are the coordinates inside one of WHIR's `64` lanes of `2^(n-6)`
//! words, `x_{n-6} .. x_{n-1}` the lane's index (word `i` is word `i mod 2^(n-6)` of lane `i >> (n-6)`), which is
//! the order WHIR's prover and verifier read a point of the stack in.

use fiat_shamir::digest_words;
use fiat_shamir::merkle::Hash;
use fiat_shamir::transcript::{Proof, ProverState};
use std::sync::Mutex;

use pcs::whir::{
    KeptCodeword, LaneJob, LaneTensor, Low, commit_tree_skipping_in, config_for_rate, eq_bits,
    recursive_prover_with_lane_tensors_batch,
};
use primitives::field::{F64, F192};
use primitives::hash::hash as keccak256;
use primitives::multilinear::mle_eval_par;

// The claim's wire format (`evm_link::wire`, which the contracts pack): `VERSION` is the PCS version this crate
// implements, leanVM's WHIR (commit `c445e3d5`) at rate `1/2`, its deployed ladder (`pcs::whir::DEPLOYED_SCHEDULE`,
// `verifier::whir::Ladder::Deployed`), `64` lanes at its first fold; `MAX_PCS_VARIABLES` the EIP's bound on `n` (a
// claim with more variables is not well-formed); `claim_len(n)` its `82 + 24 n` bytes.
pub use evm_link::wire::{ELEMENT_BYTES, MAX_PCS_VARIABLES, VERSION, claim_len};

/// The variables [`VERSION`] commits and opens: WHIR's stacks of `2^15` to `2^28` words. A well-formed claim with
/// `n` outside this range is not supported: [`verify`] rejects it, the prover panics.
pub const MIN_VARIABLES: usize = 15;
pub const MAX_VARIABLES: usize = 28;

/// WHIR's rate, `2^-LOG_INV_RATE`.
pub const LOG_INV_RATE: usize = 1;

/// WHIR's first fold: `2^6` lanes.
pub const LANE_FOLD: usize = 6;

/// The domain tag of the out-of-domain point's derivation ([`ood_point`]).
pub const OOD_TAG: &[u8] = b"leanPCS-ood";

/// The public digest the opening's transcript starts from: zero.
pub const PUBLIC_DIGEST: [u8; 32] = [0; 32];

/// An element of `E` as a claim encodes it: the 192-bit integer `c0 | c1 << 64 | c2 << 128` (`c_k` the coefficient
/// of `X^k`), big-endian, 24 bytes: the low 24 bytes of the EVM word `MULFIELD` takes.
pub fn element_bytes(x: F192) -> [u8; ELEMENT_BYTES] {
    let mut out = [0; ELEMENT_BYTES];
    out[..8].copy_from_slice(&x.c2.to_be_bytes());
    out[8..16].copy_from_slice(&x.c1.to_be_bytes());
    out[16..].copy_from_slice(&x.c0.to_be_bytes());
    out
}

/// The element 24 bytes encode ([`element_bytes`]'s inverse; every 24 bytes encode one).
pub fn element_of(bytes: &[u8; ELEMENT_BYTES]) -> F192 {
    let limb = |k: usize| u64::from_be_bytes(bytes[8 * k..8 * k + 8].try_into().expect("8 bytes"));
    F192::new(limb(2), limb(1), limb(0))
}

/// The out-of-domain point of a commitment on `n` variables with root `root`: coordinate `j` is the element the low
/// 24 bytes of `keccak256(OOD_TAG || VERSION || n || root || j)` encode (`VERSION`, `n` and `j` one byte each).
pub fn ood_point(n: usize, root: &[u8; 32]) -> Vec<F192> {
    assert!((1..=MAX_PCS_VARIABLES).contains(&n));
    (0..n)
        .map(|j| {
            let digest = keccak256(&[OOD_TAG, &[VERSION, n as u8], root, &[j as u8]].concat());
            element_of(digest[8..].try_into().expect("24 bytes"))
        })
        .collect()
}

/// A PCS claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PcsClaim {
    pub n: u8,
    pub root: [u8; 32],
    /// The out-of-domain answer, `f(ood_point(n, root))`.
    pub ood: F192,
    pub point: Vec<F192>,
    pub value: F192,
}

impl PcsClaim {
    /// `PCS_claim`: `VERSION || n || root || ood || point_0 || ... || point_{n-1} || value`.
    pub fn encode(&self) -> Vec<u8> {
        assert_eq!(self.point.len(), self.n as usize, "a point of n coordinates");
        let mut bytes = Vec::with_capacity(claim_len(self.point.len()));
        bytes.extend([VERSION, self.n]);
        bytes.extend(self.root);
        for &x in [&self.ood].into_iter().chain(&self.point).chain([&self.value]) {
            bytes.extend(element_bytes(x));
        }
        bytes
    }

    /// The claim `bytes` encode, if they are well-formed: version [`VERSION`], `1 <= n <= MAX_PCS_VARIABLES`, and
    /// exactly [`claim_len`]`(n)` bytes.
    pub fn decode(bytes: &[u8]) -> Option<Self> {
        if !evm_link::wire::well_formed(bytes) {
            return None;
        }
        let (n, rest) = (bytes[1], &bytes[2..]);
        let vars = n as usize;
        let root: [u8; 32] = rest[..32].try_into().ok()?;
        let elements: Vec<F192> = rest[32..]
            .as_chunks::<ELEMENT_BYTES>()
            .0
            .iter()
            .map(element_of)
            .collect();
        Some(Self {
            n,
            root,
            ood: elements[0],
            point: elements[1..=vars].to_vec(),
            value: elements[vars + 1],
        })
    }

    /// The claim whose fields a contract holds as these words (`evm_link::Claim`): the root's 32 bytes, each element's
    /// word (its top 64 bits zero, its low 24 bytes [`element_bytes`]).
    pub fn of_words(words: &evm_link::Claim<[u8; 32]>) -> Self {
        let element = |w: &[u8; 32]| {
            assert!(w[..8].iter().all(|&b| b == 0), "an element's top 64 bits are zero");
            element_of(w[8..].try_into().expect("24 bytes"))
        };
        Self {
            n: words.point.len() as u8,
            root: words.root,
            ood: element(&words.ood),
            point: words.point.iter().map(element).collect(),
            value: element(&words.value),
        }
    }

    /// `keccak256(PCS_claim)`: the payload of the claim's dependency, and the opening's transcript IV ([`iv`]).
    pub fn hash(&self) -> [u8; 32] {
        keccak256(&self.encode())
    }
}

/// `f`'s value at `point`, `f` of [`commit`]'s variable order (`f_i`'s weight `eq(point, bits of i)`, bit 0 first).
pub fn evaluate(words: &[F64], point: &[F192]) -> F192 {
    assert_eq!(words.len(), 1 << point.len());
    mle_eval_par(words, point)
}

/// [`evaluate`] of the `2^n` words (`n = point.len()`) whose leading whole lanes are `words` and the rest zero:
/// `Σ_l eq(point_high, l) · Σ_y lane_l[y] eq(point_low, y)` over the lanes `words` holds.
pub fn evaluate_lanes(words: &[F64], point: &[F192]) -> F192 {
    let log_lane = point.len() - LANE_FOLD;
    combine_lanes(&lane_products(words, point, None), &point[log_lane..])
}

/// `Σ_y lane_l[y] eq(point_low, y)` for each lane `l` of `words` (its leading whole lanes of the `2^n` words, `n =
/// point.len()`), in one pass over them: what an opening's lane rounds start from, at a tensor of `eq(point, ·)`.
fn lane_products(words: &[F64], point: &[F192], zero: Option<&[bool]>) -> Vec<F192> {
    let n = point.len();
    let log_lane = n - LANE_FOLD;
    let lane = 1usize << log_lane;
    assert!(
        !words.is_empty() && words.len().is_multiple_of(lane) && words.len() <= 1 << n,
        "whole lanes of the 2^n words"
    );
    pcs::whir::dense_lane_inner_products_skipping(words, lane, &[&Low::Eq(point[..log_lane].to_vec())], zero)
        .pop()
        .expect("one low weight")
}

/// `Σ_l eq(high, l) · products[l]`.
fn combine_lanes(products: &[F192], high: &[F192]) -> F192 {
    products
        .iter()
        .enumerate()
        .fold(F192::ZERO, |acc, (l, &p)| acc + eq_bits(high, l) * p)
}

/// A commitment, and what its openings need but the words: the Merkle tree of the committed lanes' codeword, the
/// codeword itself if it was kept (which the first opening reads its queried rows from, and frees), and the committed
/// lanes' products with the out-of-domain point's low weight, which every opening's lane rounds start from. The words
/// are the caller's ([`commit_words`], [`open`]); [`Committed`] keeps them too.
pub struct Commitment {
    pub n: usize,
    pub root: Hash,
    /// `f(ood_point(n, root))`.
    pub ood: F192,
    tree: Vec<Hash>,
    codeword: Mutex<Option<KeptCodeword>>,
    /// `Σ_y lane_l[y] eq(z_low, y)` for each committed lane `l`, `z = ood_point(n, root)`.
    ood_lanes: Vec<F192>,
    /// Which committed lanes are all zero ([`zero_lanes`]): not encoded, at the commitment nor at an opening's queried
    /// rows, and left out of the openings' lane passes. A kept codeword says itself which lanes it holds.
    zero_lanes: Vec<bool>,
}

impl Commitment {
    /// The claim that `f(point) = value` on this commitment.
    pub fn claim(&self, point: Vec<F192>, value: F192) -> PcsClaim {
        assert_eq!(point.len(), self.n);
        PcsClaim {
            n: self.n as u8,
            root: self.root,
            ood: self.ood,
            point,
            value,
        }
    }
}

/// Commit to the `2^n` words whose leading whole lanes (of `2^(n-6)` words) are `words` and the rest zero
/// (`MIN_VARIABLES <= n <= MAX_VARIABLES`), without encoding the zero lanes: leanVM's commitment of the leading lanes
/// is the whole stack's (its root and its proofs are those of the `2^n` words: the zero lanes' codeword is zero, and a
/// Merkle leaf hashes them first; [`open`] pads its rows back to the whole stack's). With `keep_codeword`, the
/// codeword (`2^LOG_INV_RATE` words a word of the lanes not all zero) is kept for the openings; the root and the
/// proofs are the same.
pub fn commit_words(words: &[F64], n: usize, keep_codeword: bool) -> Commitment {
    assert!(
        (MIN_VARIABLES..=MAX_VARIABLES).contains(&n),
        "n from {MIN_VARIABLES} to {MAX_VARIABLES}"
    );
    let lane = 1usize << (n - LANE_FOLD);
    assert!(
        !words.is_empty() && words.len().is_multiple_of(lane) && words.len() <= 1 << n,
        "whole leading lanes of the 2^n words"
    );
    commit_flagged(words, n, keep_codeword, zero_lanes(words, lane))
}

/// [`commit_words`], the all-zero lanes `zero` (a flag a lane of `words`) already found.
fn commit_flagged(words: &[F64], n: usize, keep_codeword: bool, zero: Vec<bool>) -> Commitment {
    let (root, tree, codeword) = if keep_codeword {
        let (commitment, codeword, tree) = pcs::whir::commit_skipping(words, n, LANE_FOLD, LOG_INV_RATE, &zero);
        (commitment.root, tree, Some(codeword))
    } else {
        // The encoding buffer, one replica of the codeword, mapped by the workers: as many words as `words`, though
        // the zero lanes take none of them, so that an opening's buffers find this memory again once it is freed.
        // SAFETY: the encoding clears this buffer and writes every word it reads (`commit_tree_skipping_in`).
        let scratch = unsafe { mapped_words(words.len()) };
        let (commitment, tree) = commit_tree_skipping_in(words, n, LANE_FOLD, LOG_INV_RATE, &zero, scratch);
        (commitment.root, tree, None)
    };
    // The answer from the committed lanes' products with the point's low weight, which the openings reuse.
    let z = ood_point(n, &root);
    let ood_lanes = lane_products(words, &z, Some(&zero));
    let ood = combine_lanes(&ood_lanes, &z[n - LANE_FOLD..]);
    Commitment {
        n,
        root,
        ood,
        tree,
        codeword: Mutex::new(codeword),
        ood_lanes,
        zero_lanes: zero,
    }
}

/// Which lanes (of `lane` words) of `words` are all zero, read in parallel: a run of a lane is read up to its first
/// nonzero word, so that the scan reads the zero lanes and little else.
pub fn zero_lanes(words: &[F64], lane: usize) -> Vec<bool> {
    const RUN: usize = 1 << 16;
    let run = RUN.min(lane);
    let zero_runs =
        parallel::map_collect(words.len() / run, |r| words[r * run..(r + 1) * run].iter().all(|w| w.is_zero()));
    zero_runs.chunks(lane / run).map(|runs| runs.iter().all(|&z| z)).collect()
}

/// `len` words, unwritten, their memory mapped by the workers: each touches its own run of pages once, so that the
/// kernel maps (and clears) them in parallel, before a pass whose first touches are strided and would fault the same
/// pages from every thread at once.
///
/// # Safety
/// The words are uninitialised: the caller must write every word before reading it.
pub unsafe fn mapped_words(len: usize) -> Vec<F64> {
    /// A run of pages one task touches: a transparent huge page.
    const RUN: usize = (2 << 20) / size_of::<F64>();
    /// The words of the smallest page, one touched in each.
    const PAGE: usize = 4096 / size_of::<F64>();
    let mut v: Vec<F64> = Vec::with_capacity(len);
    let base = parallel::SendPtr(v.as_mut_ptr());
    parallel::for_each(len.div_ceil(RUN), |r| {
        for i in (r * RUN..len.min((r + 1) * RUN)).step_by(PAGE) {
            // SAFETY: inside the allocation; a word the caller writes before reading, written here only to map its
            // page (volatile, so that the store is not elided).
            unsafe { base.add(i).write_volatile(F64::ZERO) };
        }
    });
    // SAFETY: the capacity holds `len` plain words, which the caller writes before reading.
    unsafe { v.set_len(len) };
    v
}

/// A commitment with its words ([`commit`]); it reads as its [`Commitment`].
pub struct Committed {
    pub commitment: Commitment,
    words: Vec<F64>,
}

impl std::ops::Deref for Committed {
    type Target = Commitment;

    fn deref(&self) -> &Commitment {
        &self.commitment
    }
}

impl Committed {
    /// The committed words: the leading whole lanes of `f`'s `2^n` (the rest zero).
    pub fn words(&self) -> &[F64] {
        &self.words
    }

    /// The claim at `point` with `f`'s value there.
    pub fn claim_at(&self, point: Vec<F192>) -> PcsClaim {
        let value = evaluate_lanes(&self.words, &point);
        self.claim(point, value)
    }
}

/// Commit to `f`, given by its `2^n` words (`MIN_VARIABLES <= n <= MAX_VARIABLES`): leanVM's commitment
/// ([`pcs::whir::commit`]'s root and tree) of the `64` lanes of `2^(n-6)` words, and the out-of-domain answer, its
/// trailing all-zero lanes left out of the words kept ([`commit_words`]: the commitment and every opening are the
/// whole table's). The words are moved in: an opening reads them. `keep_codeword` as [`commit_words`]'s.
pub fn commit(mut words: Vec<F64>, keep_codeword: bool) -> Committed {
    assert!(words.len().is_power_of_two(), "2^n words");
    let n = words.len().trailing_zeros() as usize;
    assert!(
        (MIN_VARIABLES..=MAX_VARIABLES).contains(&n),
        "n from {MIN_VARIABLES} to {MAX_VARIABLES}"
    );
    let lane = 1usize << (n - LANE_FOLD);
    let mut zero = zero_lanes(&words, lane);
    let lanes = zero.iter().rposition(|&z| !z).map_or(1, |last| last + 1);
    zero.truncate(lanes);
    words.truncate(lanes * lane);
    // The allocation past them returned (the allocator shrinks a large one in place), for the memory to come.
    words.shrink_to_fit();
    Committed {
        commitment: commit_flagged(&words, n, keep_codeword, zero),
        words,
    }
}

/// The opening's IV: `keccak256(PCS_claim)`, the claim's dependency payload. It is the transcript's one hash step,
/// leanVM's shape that `formal/WhirBridge` proves sound (`family_sound`: one hash of a prefix the verifier fixes,
/// here `VERSION || n`, and the claims): the public digest is zero, and the root is the proof's first two scalars,
/// which the verifier checks are the claim's root before anything else.
pub fn iv(claim: &PcsClaim) -> [u8; 32] {
    claim.hash()
}

/// `scale · eq(point, ·)` on the stack, as a lane tensor: word `y` of lane `l` weighs `scale · eq(point_high, l) ·
/// eq(point_low, y)`.
fn eq_tensor(point: &[F192], scale: F192) -> LaneTensor {
    let log_lane = point.len() - LANE_FOLD;
    LaneTensor {
        scales: (0..1usize << LANE_FOLD)
            .map(|l| scale * eq_bits(&point[log_lane..], l))
            .collect(),
        low: Low::Eq(point[..log_lane].to_vec()),
    }
}

/// What an opening does with a commitment's kept codeword, which serves it: frees it, or keeps it for another opening
/// (a claim at each of several points, a setup every proof opens).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Codeword {
    Free,
    Keep,
}

/// Prove `claim`, a claim on `commitment` of `words` (the leading whole lanes [`commit_words`] committed): one WHIR
/// opening of `f(z) = ood` and `f(point) = value`, combined by `1, λ`, `λ` the transcript's first challenge. Its
/// level-0 rows are the whole stack's (`64` words, the absent lanes' zeros leading), as a verifier that knows only `n`
/// reads them.
pub fn open(words: &[F64], commitment: &Commitment, claim: &PcsClaim, codeword: Codeword) -> Proof {
    open_batch(words, commitment, std::slice::from_ref(claim), codeword)
        .pop()
        .expect("one proof")
}

/// [`open`] of each of `claims`, all on `commitment` of `words`: the proofs are those [`open`] gives each claim alone,
/// byte for byte, but the out-of-domain point's weight is built once for all of them, and their lane rounds read the
/// words twice in all rather than twice a claim (`pcs::whir::recursive_prover_with_lane_tensors_batch`).
pub fn open_batch(words: &[F64], commitment: &Commitment, claims: &[PcsClaim], codeword: Codeword) -> Vec<Proof> {
    let n = commitment.n;
    for claim in claims {
        assert!(
            claim.n as usize == n && claim.root == commitment.root && claim.ood == commitment.ood,
            "a claim on this commitment"
        );
    }
    let config = config_for_rate(n, LOG_INV_RATE).expect("a supported WHIR shape");
    // Each claim's transcript and its weight `eq(z, ·) + λ eq(point, ·)`: the batch's tensors are the out-of-domain
    // point's (its products with the lanes known from the commitment), then each claim's.
    let mut states: Vec<ProverState> = Vec::with_capacity(claims.len());
    let mut weight = vec![eq_tensor(&ood_point(n, &commitment.root), F192::ONE)];
    let mut targets = Vec::with_capacity(claims.len());
    for claim in claims {
        let mut ps = ProverState::new(digest_words(&iv(claim)), digest_words(&PUBLIC_DIGEST));
        ps.add_root(&commitment.root);
        let lambda = ps.sample();
        targets.push(claim.ood + lambda * claim.value);
        weight.push(eq_tensor(&claim.point, lambda));
        states.push(ps);
    }
    let mut known: Vec<Option<&[F192]>> = vec![None; weight.len()];
    known[0] = Some(&commitment.ood_lanes);
    let mut jobs: Vec<LaneJob<'_>> = states
        .iter_mut()
        .zip(&targets)
        .enumerate()
        .map(|(c, (ps, &target))| LaneJob {
            tensors: vec![0, c + 1],
            target,
            ps,
        })
        .collect();
    // The codeword is only read under the lock, or taken whole: an opening that panicked leaves it kept or gone, and
    // either serves the next (without it, an opening encodes its rows again), so a poisoned lock is recovered.
    let mut kept = commitment.codeword.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let taken = if codeword == Codeword::Free { kept.take() } else { None };
    let l0_codeword = if codeword == Codeword::Free { taken.as_ref() } else { kept.as_ref() };
    recursive_prover_with_lane_tensors_batch(
        &config,
        n,
        words,
        &weight,
        &known,
        &mut jobs,
        l0_codeword,
        Some(&commitment.zero_lanes),
        &commitment.tree[..],
    );
    drop(jobs);
    drop((taken, kept));
    states.into_iter().map(|ps| whole_rows(ps.into_proof())).collect()
}

/// `proof` with level 0's rows padded to the whole stack's: they hold the committed lanes alone, the tail of a leaf's
/// image, which the whole stack's leads with the absent lanes' zeros (`pcs::whir::commit`).
fn whole_rows(mut proof: Proof) -> Proof {
    let width = 1usize << LANE_FOLD;
    if let Some(level0) = proof.merkle.first_mut() {
        for row in &mut level0.leaf_data {
            if row.len() < width {
                let mut full = vec![F64::ZERO; width - row.len()];
                full.extend_from_slice(row);
                *row = full;
            }
        }
    }
    proof
}

fn ext(x: F192) -> verifier::E {
    verifier::E::new(x.c0, x.c1, x.c2)
}

/// The opening proof in the `verifier` crate's types: the same limbs, digests and row words.
pub fn wire_proof(proof: &Proof) -> verifier::Proof {
    let batches = proof.merkle.iter().map(|paths| verifier::PrunedMerklePaths {
        leaf_data: paths
            .leaf_data
            .iter()
            .map(|row| row.iter().map(|word| verifier::K(word.0)).collect())
            .collect(),
        sibling_hashes: paths.sibling_hashes.clone(),
    });
    verifier::Proof {
        stream: proof.stream.iter().map(|&x| ext(x)).collect(),
        merkle_openings: verifier::MerkleOpenings::Pruned(batches.collect()),
    }
}

/// The EIP's `pcs_verify(PCS_claim, opening_proof)` for [`VERSION`]: false unless `claim_bytes` is a well-formed
/// claim with `n` in `MIN_VARIABLES..=MAX_VARIABLES` and `proof` an opening of it, with leanVM's WHIR verifier.
pub fn verify(claim_bytes: &[u8], proof: &verifier::Proof) -> bool {
    PcsClaim::decode(claim_bytes).is_some_and(|claim| verify_claim(&claim, proof).is_ok())
}

/// [`verify`] of a decoded claim, with the verifier's error.
pub fn verify_claim(claim: &PcsClaim, proof: &verifier::Proof) -> Result<(), verifier::VerifierError> {
    verify_claim_paths(claim, proof).map(|_| ())
}

/// [`verify_claim`], returning the Merkle paths it checked: one full path a query, the pruned batches expanded (as
/// `verifier::Transcript::finish` returns them), which the Lean vectors carry ([`lean`]).
pub fn verify_claim_paths(
    claim: &PcsClaim,
    proof: &verifier::Proof,
) -> Result<Vec<verifier::MerklePath>, verifier::VerifierError> {
    use verifier::{Digest, E, Transcript};
    let n = claim.n as usize;
    if !(MIN_VARIABLES..=MAX_VARIABLES).contains(&n) || claim.point.len() != n {
        return Err(verifier::VerifierError::WhirShape);
    }
    let mut transcript = Transcript::new(proof, Digest(iv(claim)), Digest(PUBLIC_DIGEST), true);
    // The root, the proof's first two scalars: the claim's, or nothing further is read.
    let halves = transcript.next_scalars(2)?;
    if Digest::from_halves(halves[0], halves[1])? != Digest(claim.root) {
        return Err(verifier::VerifierError::MerkleRootMismatch);
    }
    let lambda = transcript.sample();
    let target = ext(claim.ood) + lambda * ext(claim.value);
    let z: Vec<E> = ood_point(n, &claim.root).into_iter().map(ext).collect();
    let point: Vec<E> = claim.point.iter().map(|&x| ext(x)).collect();
    let one = E::new(1, 0, 0);
    // `x` is a point of the stack in the order of `f`'s variables (the lane's coordinates, then the lane index's six).
    let eq = move |a: &[E], x: &[E]| {
        a.iter()
            .zip(x)
            .fold(one, |w, (&c, &p)| w * (c * p + (one + c) * (one + p)))
    };
    let weight = move |x: &[E]| eq(&z, x) + lambda * eq(&point, x);
    verifier::whir::verify_whir(
        &mut transcript,
        n,
        1u64 << n,
        LOG_INV_RATE,
        target,
        Digest(claim.root),
        &weight,
    )?;
    transcript.finish()
}

/// The text the Lean checks of `formal/WhirBridge` read: lines of a tag and decimal numbers.
pub mod lean {
    use super::*;

    /// `tag v_0 v_1 ...`, one line.
    pub fn line(tag: &str, values: impl IntoIterator<Item = u64>) -> String {
        let mut s = tag.to_string();
        for v in values {
            s.push(' ');
            s.push_str(&v.to_string());
        }
        s.push('\n');
        s
    }

    /// A digest's four little-endian words.
    pub fn words(digest: &[u8; 32]) -> [u64; 4] {
        digest_words(digest).map(|w| w.0)
    }

    pub fn limbs(x: &F192) -> [u64; 3] {
        [x.c0, x.c1, x.c2]
    }

    /// An opening's stream and one `open` line a query (the leaf's length and words, then the siblings), its paths
    /// those [`verify_claim_paths`] checks.
    pub fn opening(claim: &PcsClaim, proof: &Proof) -> String {
        let paths = verify_claim_paths(claim, &wire_proof(proof)).expect("the opening verifies");
        let mut out = line("stream", proof.stream.iter().flat_map(limbs));
        for path in &paths {
            out += &line(
                "open",
                [path.leaf.len() as u64]
                    .into_iter()
                    .chain(path.leaf.iter().map(|k| k.0))
                    .chain(path.siblings.iter().flat_map(words)),
            );
        }
        out
    }

    /// The vector `formal/WhirBridge`'s `Test/Check.lean` and `Test/CheckLarge.lean` read: the claim's bytes, the
    /// root, the claim's point and value, then [`opening`].
    pub fn bridge_vector(name: &str, claim: &PcsClaim, proof: &Proof) -> String {
        let mut out = format!("vector {name}\n");
        out += &line("pcsclaim", claim.encode().iter().map(|&b| b as u64));
        out += &line("root", words(&claim.root));
        out += &line("claim", claim.point.iter().chain([&claim.value]).flat_map(limbs));
        out + &opening(claim, proof) + "end\n"
    }
}

#[cfg(test)]
mod tests;
