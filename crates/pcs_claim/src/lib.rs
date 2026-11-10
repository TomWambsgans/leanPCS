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
//! - [`commit`]: the commitment to `2^n` words (`n` from [`MIN_VARIABLES`] to [`MAX_VARIABLES`]), its root and
//!   out-of-domain answer.
//! - [`open`]: one opening proving `f(z) = ood` and `f(point) = value` together, at one random combination;
//!   [`verify`]: the EIP's `pcs_verify(PCS_claim, opening_proof)` for [`VERSION`].
//!
//! **Variables.** `f(x) = Σ_i f_i Π_j (x_j if bit j of i is 1, else 1 - x_j)`, `f_i` the `i`-th committed word,
//! bit 0 the least significant: `x_0 .. x_{n-7}` are the coordinates inside one of WHIR's `64` lanes of `2^(n-6)`
//! words, `x_{n-6} .. x_{n-1}` the lane's index (word `i` is word `i mod 2^(n-6)` of lane `i >> (n-6)`), which is
//! the order WHIR's prover and verifier read a point of the stack in.

use fiat_shamir::digest_words;
use fiat_shamir::merkle::Hash;
use fiat_shamir::transcript::{Proof, ProverState};
use std::sync::Mutex;

use pcs::whir::{LaneTensor, commit_tree_in, config_for_rate, inner_product_base_ext, recursive_prover_with_lane_tensors};
use primitives::field::{F64, F192};
use primitives::hash::hash as keccak256;
use primitives::multilinear::{eq_table, mle_eval_par};

/// The PCS version this crate implements: leanVM's WHIR (commit `c445e3d5`) at rate `1/2`, its deployed ladder
/// (`pcs::whir::DEPLOYED_SCHEDULE`, `verifier::whir::Ladder::Deployed`), `64` lanes at its first fold.
pub const VERSION: u8 = 1;

/// The EIP's bound on `n` (`MAX_PCS_VARIABLES`): a claim with more variables is not well-formed.
pub const MAX_PCS_VARIABLES: usize = 32;

/// The variables [`VERSION`] commits and opens: WHIR's stacks of `2^15` to `2^28` words. A well-formed claim with
/// `n` outside this range is not supported: [`verify`] rejects it, the prover panics.
pub const MIN_VARIABLES: usize = 15;
pub const MAX_VARIABLES: usize = 28;

/// WHIR's rate, `2^-LOG_INV_RATE`.
pub const LOG_INV_RATE: usize = 1;

/// WHIR's first fold: `2^6` lanes.
pub const LANE_FOLD: usize = 6;

/// The bytes of an element of `E`.
pub const ELEMENT_BYTES: usize = 24;

/// The domain tag of the out-of-domain point's derivation ([`ood_point`]).
pub const OOD_TAG: &[u8] = b"leanPCS-ood";

/// The public digest the opening's transcript starts from: zero.
pub const PUBLIC_DIGEST: [u8; 32] = [0; 32];

/// The bytes of a claim on `n` variables: `82 + 24 n`.
pub const fn claim_len(n: usize) -> usize {
    2 + 32 + ELEMENT_BYTES + ELEMENT_BYTES * n + ELEMENT_BYTES
}

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
        let (&version, rest) = bytes.split_first()?;
        let (&n, rest) = rest.split_first()?;
        let vars = n as usize;
        if version != VERSION || !(1..=MAX_PCS_VARIABLES).contains(&vars) || bytes.len() != claim_len(vars) {
            return None;
        }
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
    let n = point.len();
    let log_lane = n - LANE_FOLD;
    let lane = 1usize << log_lane;
    assert!(
        words.len().is_multiple_of(lane) && words.len() <= 1 << n,
        "whole lanes of the 2^n words"
    );
    let low = eq_table(&point[..log_lane]);
    (0..words.len() / lane).fold(F192::ZERO, |acc, l| {
        acc + eq_bits(&point[log_lane..], l) * inner_product_base_ext(&words[l * lane..(l + 1) * lane], &low)
    })
}

/// A commitment, and what its openings need: the committed lanes' words, the Merkle tree of their codeword, and the
/// codeword itself if it was kept (which the first opening reads its queried rows from, and frees).
pub struct Committed {
    pub n: usize,
    pub root: Hash,
    /// `f(ood_point(n, root))`.
    pub ood: F192,
    words: Vec<F64>,
    tree: Vec<Hash>,
    codeword: Mutex<Option<Vec<F64>>>,
}

impl Committed {
    /// The committed words: the leading whole lanes of `f`'s `2^n` (the rest zero).
    pub fn words(&self) -> &[F64] {
        &self.words
    }

    /// The words, given back.
    pub fn into_words(self) -> Vec<F64> {
        self.words
    }

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

    /// The claim at `point` with `f`'s value there.
    pub fn claim_at(&self, point: Vec<F192>) -> PcsClaim {
        let value = evaluate_lanes(&self.words, &point);
        self.claim(point, value)
    }
}

/// Commit to `f`, given by its `2^n` words (`MIN_VARIABLES <= n <= MAX_VARIABLES`): leanVM's commitment
/// ([`pcs::whir::commit`]'s root and tree, encoded one replica of the codeword at a time) of the `64` lanes of
/// `2^(n-6)` words, and the out-of-domain answer. The words are moved in: an opening reads them.
pub fn commit(words: Vec<F64>) -> Committed {
    let n = words.len().trailing_zeros() as usize;
    assert!(words.len().is_power_of_two(), "2^n words");
    commit_lanes(words, n)
}

/// [`commit`] to the `2^n` words whose leading whole lanes (of `2^(n-6)` words) are `words` and the rest zero, without
/// encoding the zero lanes: leanVM's commitment of the leading lanes is the whole stack's (its root and its proofs are
/// those of the `2^n` words: the zero lanes' codeword is zero, and a Merkle leaf hashes them first). The opening
/// pads its rows back to the whole stack's ([`open`]).
pub fn commit_lanes(words: Vec<F64>, n: usize) -> Committed {
    check_lanes(&words, n);
    let (commitment, tree) = commit_tree_in(&words, n, LANE_FOLD, LOG_INV_RATE, Vec::new());
    committed(words, n, commitment.root, tree, None)
}

/// [`commit_lanes`], keeping the codeword (`2^LOG_INV_RATE` words a word of the lanes), which the first opening reads
/// its queried rows from instead of encoding them again, and frees. The root and the proofs are the same.
pub fn commit_lanes_keeping_codeword(words: Vec<F64>, n: usize) -> Committed {
    check_lanes(&words, n);
    let (commitment, data) = pcs::whir::commit(&words, n, LANE_FOLD, LOG_INV_RATE);
    committed(words, n, commitment.root, data.merkle_tree, Some(data.codeword))
}

fn check_lanes(words: &[F64], n: usize) {
    assert!(
        (MIN_VARIABLES..=MAX_VARIABLES).contains(&n),
        "n from {MIN_VARIABLES} to {MAX_VARIABLES}"
    );
    let lane = 1usize << (n - LANE_FOLD);
    assert!(
        !words.is_empty() && words.len().is_multiple_of(lane) && words.len() <= 1 << n,
        "whole leading lanes of the 2^n words"
    );
}

fn committed(words: Vec<F64>, n: usize, root: Hash, tree: Vec<Hash>, codeword: Option<Vec<F64>>) -> Committed {
    let ood = evaluate_lanes(&words, &ood_point(n, &root));
    Committed {
        n,
        root,
        ood,
        words,
        tree,
        codeword: Mutex::new(codeword),
    }
}

/// The opening's IV: `keccak256(PCS_claim)`, the claim's dependency payload. It is the transcript's one hash step,
/// leanVM's shape that `formal/WhirBridge` proves sound (`family_sound`: one hash of a prefix the verifier fixes,
/// here `VERSION || n`, and the claims): the public digest is zero, and the root is the proof's first two scalars,
/// which the verifier checks are the claim's root before anything else.
pub fn iv(claim: &PcsClaim) -> [u8; 32] {
    claim.hash()
}

/// `eq(point, bits of index)`, coordinate 0 first.
fn eq_bits(point: &[F192], index: usize) -> F192 {
    point.iter().enumerate().fold(F192::ONE, |w, (k, &p)| {
        w * if (index >> k) & 1 == 1 { p } else { F192::ONE + p }
    })
}

/// `scale · eq(point, ·)` on the stack, as a lane tensor: word `y` of lane `l` weighs `scale · eq(point_high, l) ·
/// eq(point_low, y)`.
fn eq_tensor(point: &[F192], scale: F192) -> LaneTensor {
    let log_lane = point.len() - LANE_FOLD;
    LaneTensor {
        scales: (0..1usize << LANE_FOLD)
            .map(|l| scale * eq_bits(&point[log_lane..], l))
            .collect(),
        low: eq_table(&point[..log_lane]),
    }
}

/// Prove `claim`, a claim on `committed` (its root, its out-of-domain answer, `n`): one WHIR opening of `f(z) =
/// ood` and `f(point) = value`, combined by `1, λ`, `λ` the transcript's first challenge. Its level-0 rows are the
/// whole stack's (`64` words, the absent lanes' zeros leading), as a verifier that knows only `n` reads them. A kept
/// codeword serves this opening and is freed.
pub fn open(committed: &Committed, claim: &PcsClaim) -> Proof {
    let n = committed.n;
    assert!(
        claim.n as usize == n && claim.root == committed.root && claim.ood == committed.ood,
        "a claim on this commitment"
    );
    let config = config_for_rate(n, LOG_INV_RATE).expect("a supported WHIR shape");
    let mut ps = ProverState::new(digest_words(&iv(claim)), digest_words(&PUBLIC_DIGEST));
    ps.add_root(&committed.root);
    let lambda = ps.sample();
    let target = claim.ood + lambda * claim.value;
    let weight = [
        eq_tensor(&ood_point(n, &committed.root), F192::ONE),
        eq_tensor(&claim.point, lambda),
    ];
    let codeword = committed.codeword.lock().expect("the codeword").take();
    recursive_prover_with_lane_tensors(
        &config,
        n,
        &committed.words[..],
        &weight,
        target,
        codeword.as_deref(),
        &committed.tree[..],
        &mut ps,
    );
    let mut proof = ps.into_proof();
    // Level 0's rows hold the committed lanes alone, the tail of a leaf's image: the whole stack's lead with the
    // absent lanes' zeros (`pcs::whir::commit`).
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
    transcript.finish().map(|_| ())
}

#[cfg(test)]
mod tests;
