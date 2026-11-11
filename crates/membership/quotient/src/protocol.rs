// Part of this repository. Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6, crates/flock/src/quotient.rs and crates/flock/src/membership.rs
// (`Scalar`, `Channel`, `VerifyError`): the copy argument is the same but for the gate (`V = Y + C + X·C` on bits,
// degree 2), the public values (pinned cells, not a weighted sum), the gate's quotient (with the pins, merged into
// the copy argument's) and the one quotient table, whose layout checks the sum (`x h`). MIT OR Apache-2.0; see
// AGENTS.md.
//! The membership statement reduced to three evaluation claims on two commitments and the circuit's, by six field
//! elements and no sumcheck (`docs/membership/PROTOCOL.md`).
//!
//! A multilinear claim at a point built from one field element `t` is a univariate evaluation ([`domain`]),
//! so this is a gate-and-copy argument on an additive subspace: one gate on four cells a row ([`circuit`]),
//! copy constraints as one sum of logarithmic derivatives, the public values as cells pinned by interpolation, and
//! one quotient, in one committed table with the sum's polynomial. No quotient value is sent: the claim on the
//! quotient table is the combination its identity gives. The verifier is [`reduce`], generic in its scalar so that
//! the same code is the EVM contract, and checks nothing but one nonzero product.
//!
//! **The tables** (`m = log_rows + 2`, `n = 2^m` cells): the witness `W` (the cells' polynomial `w`, `m`
//! variables: the four row polynomials interleaved), the circuit's wiring (`m`, public), and the quotient table `T`
//! (`m + 4`, [`table_slot`]): `x h`, `h` the copy argument's sum polynomial (blinded, `deg < n + 3`), and the one
//! quotient `q` (`deg ≤ 2n`), both read through `ζ = Z x` past their first `n` coefficients.
//!
//! **The identity**, with `d = α + w + β x`, `d' = α + w + β σ`, `Z = X_n` the cells' vanishing polynomial, and
//! `g = gate / Z_R + (w + v) / Z_P` (`Z_R` vanishing on the rows' first cells, `Z_P` on the
//! [`crate::circuit::PUBLIC_ROWS`] pinned cells, `v` the public values' interpolant on them):
//! `Z q + d d' h = d + d' + μ Z g`, and `Σ_cells h = 0`, `μ` a challenge drawn after `W` and before `T`. On a cell
//! the identity sets `h` to the logarithmic derivative plus `μ` times the gate's or the pin's error over `d d'`; the
//! sum then vanishes, at random `α, β, μ`, only if the copies, the gates and the pins all hold: no cycle of the
//! wiring lies within the rows' first cells and the pins but a free cell's own (the poles of `1 / (d d')` at the
//! first cell of each run of them on a cycle are the error's alone; `PROTOCOL.md`, "Soundness").
//!
//! **The sum, by the layout** (`PROTOCOL.md`, "Tables and claims"): `T` holds `P = B_0 + ζ B_1` for `x h` and `q = A_0 + ζ A_1`
//! (`B_j`, `A_j` of `n` coefficients). The claim checks `x Z q + d d' P = x (d + d' + μ Z g)` at `t`, so at `x = 0`
//! `d d'(0) B_0(0) = 0`: `h = B_0 / x + Z B_1` is a polynomial whose part on the cells has degree `≤ n − 2`, whose
//! sum over the cells is zero. The honest `q` has a coefficient `n` the layout cannot hold; the prover zeroes it with
//! one coefficient of the blinding.
//!
//! **The claims**: `W` at a point of the row polynomials' conic that binds the three row values the verifier reads
//! (`X`, `C`, `V + Y` at `t`: [`witness_point`]), the wiring at `t`, and `T` at `t` with the identity's combination
//! of `q` and `x h` ([`copy_point`]).
//!
//! [`domain`]: crate::domain
//! [`circuit`]: crate::circuit

use std::ops::{Add, Mul};
use std::sync::OnceLock;

use fiat_shamir::merkle::Hash;
use primitives::field::{F64, F192, F192Unreduced};

use crate::circuit::{Circuit, PUBLIC_ROWS, PUBLIC_WORDS, RANDOM_WORDS, THREE, anchor_cell, anchor_values};
use crate::domain::{self, beta, chain, point, row_vanishing};
use crate::ntt::{self, ESplat, Ex8, Kx8, MixedSum};
use crate::opening::{self, Claim, Codeword, Commitment, Committed, PcsClaim};
use crate::statement::Statement;
use crate::transcript::{Proof, ProverChain, TranscriptError, VerifierChain, halves_root};

/// Why the reduction rejected.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifyError {
    Transcript(TranscriptError),
    /// A denominator of the claims is zero.
    Degenerate,
    /// A circuit size the layouts do not support: `log_rows` outside [`MIN_LOG_ROWS`]`..=`[`MAX_LOG_ROWS`].
    Shape,
}

/// The protocol's 16-byte name, the transcript label's first bytes ([`label`]).
pub const NAME: &[u8; 16] = b"pcs-quotient-kc3";

/// What the verifier computes with: the field, or a recorder of its operations, which is how the EVM contract is
/// written (`crates/membership/evm`).
pub trait Scalar: Copy + Add<Output = Self> + Mul<Output = Self> {
    fn constant(value: F192) -> Self;
    /// `self^(2^64)`.
    fn frobenius(self) -> Self;
    /// A recorder answers yes, and records that the verifier requires it.
    fn is_nonzero(self) -> bool;
}

impl Scalar for F192 {
    fn constant(value: F192) -> Self {
        value
    }

    fn frobenius(self) -> Self {
        F192::frobenius(self)
    }

    fn is_nonzero(self) -> bool {
        self != F192::ZERO
    }
}

/// Where the verifier reads the statement and the proof, and draws its challenges.
pub trait Channel<S> {
    /// The statement's eight `K`-words ([`Statement::words`]): `y`'s four, then `root`'s.
    fn statement(&mut self) -> [S; PUBLIC_WORDS];
    /// A commitment's root, as the two scalars it rides the proof as.
    fn next_root(&mut self) -> Result<[S; 2], TranscriptError>;
    fn next(&mut self) -> Result<S, TranscriptError>;
    fn sample(&mut self) -> S;
    /// Nothing is left unread.
    fn finish(&mut self) -> Result<(), TranscriptError>;
}

/// The cells per row, and the variables of the cells' tables: `m = log_rows + 2`.
fn cell_vars(log_rows: usize) -> usize {
    log_rows + 2
}

/// The coefficients past `2^m` that blind the sum's polynomial `h`, per limb: `h + X_{2^m}·(b_0 + b_1 X_1 + b_2 X_2)`,
/// which `h` keeps on the cells (`X_{2^m}` vanishes there). `b_0, b_1` ([`FREE_BLIND`]) make the quotient table's
/// out-of-domain answer uniform (`PROTOCOL.md`, "Zero knowledge"); `b_2` is solved for, so that `q`'s coefficient `n` is zero, which the
/// table's layout needs (`PROTOCOL.md`). Three, so that `h d d'` stays at degree `3 n` and `q` at `2 n`.
pub const H_BLIND: usize = 3;

/// The blinding coefficients a proof draws per limb: `b_0, b_1` of [`H_BLIND`].
pub const FREE_BLIND: usize = H_BLIND - 1;

/// The fewest rows: below `2^13` the witness and wiring tables (`m` variables) are smaller than the `2^15` words
/// WHIR commits.
pub const MIN_LOG_ROWS: usize = 13;

/// The most rows: above `2^22` rows the quotient table (`m + 4` variables) is more than the `2^28` words leanVM's
/// WHIR commits.
pub const MAX_LOG_ROWS: usize = 22;

/// Whether the commitments support a circuit of `2^log_rows` rows.
pub fn supported(log_rows: usize) -> bool {
    (MIN_LOG_ROWS..=MAX_LOG_ROWS).contains(&log_rows)
}

/// The variables of the committed tables, for `2^log_rows` rows: the witness `W` (`m`: the four row polynomials'
/// coefficients interleaved), the wiring (`m`, public), and the quotient table `T` (`m + 4`, [`table_slot`]).
pub fn table_vars(log_rows: usize) -> [usize; 3] {
    let m = cell_vars(log_rows);
    [m, m, m + 4]
}

/// The quotient table's layout: word `i + n (digit + 2 limb + 8 kind)` (`m` variables a coefficient, then a digit,
/// a limb's two bits and a kind), each `(kind, limb)` two polynomials of `n` coefficients over `K`, digit 0 and
/// digit 1, read as `F_0 + ζ F_1`, `ζ = Z x` (the claim's digit coordinate is `ζ / (1 + ζ)`):
/// - kind 0, limb `e < 3`: limb `e` of the quotient, `q = A_0 + ζ A_1`;
/// - kind 1, limb `e < 3`: limb `e` of `x h = B_0 + ζ B_1`: `B_0 = x h_low`, `B_1` the blinding's [`H_BLIND`]
///   coefficients;
/// - limb 3 of either kind: zero.
///
/// A claim at `(u, u_d, y_0, y_1, k)` ([`extension`]'s `y`) reads `(1 + k) q + k (x h)` at `t`, up to the scale of
/// [`extension`] and the multilinear's normalisation, `q` and `x h` as `K`-limbs of `E`-polynomials (a limb 3, which
/// a prover may fill, as a fourth limb of weight `Y^3`).
pub fn table_slot(kind: usize, limb: usize, n: usize) -> usize {
    2 * n * (limb + 4 * kind)
}

/// The secret randomness of one proof (`PROTOCOL.md`, "Zero knowledge"): the random rows' words ([`Circuit::randomize`]) and the
/// blinding of the sum's polynomial, [`H_BLIND`] coefficients per limb. It must be uniform, secret, and **fresh per
/// proof, never reused**: two proofs that share it let a guessed witness be confirmed. [`prove`] draws its own seed,
/// [`prove_with_seed`] takes one; both derive this from it ([`Randomness::derive`]).
#[derive(Clone)]
pub struct Randomness {
    /// The random rows' words, two a row, in the order of [`Circuit::random_rows`].
    pub rows: [F64; RANDOM_WORDS],
    /// `blind[e][i]`: coefficient `2^m + i` of limb `e` of the sum's polynomial (coefficient `2^m + 2` is solved for:
    /// [`H_BLIND`]).
    pub blind: [[F64; FREE_BLIND]; 3],
}

/// The key derivation's tags: each in one use, none a prefix of another, each followed by fields of fixed length
/// or (the cells' digests) after their count.
const KDF_KEY: &[u8] = b"pcs-quotient-kdf-v3-key";
const KDF_CELLS: &[u8] = b"pcs-quotient-kdf-v3-cells";
const KDF_WORDS: &[u8] = b"pcs-quotient-kdf-v3-words";

impl Randomness {
    /// The randomness of a proof from its 32-byte `seed`, by Keccak-256 with distinct tags. A key binds the seed,
    /// the transcript's label (the protocol, the circuit's commitment and the statement: [`label`]) and a digest of
    /// the witness's cells; the words are those of Keccak-256(tag ‖ key ‖ `k`), `k = 0, 1, ...`, four a block, in
    /// order: the random rows' words, the blinding (`blind[e][i]` word `FREE_BLIND e + i`). A seed reused for another
    /// witness or another statement gives unrelated randomness; reused for the same ones, it gives the same proof
    /// again. The seed must still be fresh per proof and secret: [`prove`] draws it from the operating system.
    pub fn derive(seed: &[u8; 32], index: &Commitment, statement: &Statement, cells: &[F64]) -> Self {
        let label = label(index, statement);
        let key = primitives::hash::hash(&[KDF_KEY, seed, &label, &cells_digest(cells)].concat());
        const WORDS: usize = RANDOM_WORDS + 3 * FREE_BLIND;
        let words: Vec<F64> = (0..WORDS.div_ceil(4) as u8)
            .flat_map(|k| {
                let block = primitives::hash::hash(&[KDF_WORDS, &key, &[k]].concat());
                (0..4).map(move |i| F64(u64::from_le_bytes(block[8 * i..8 * i + 8].try_into().unwrap())))
            })
            .collect();
        Self {
            rows: std::array::from_fn(|r| words[r]),
            blind: std::array::from_fn(|e| std::array::from_fn(|i| words[RANDOM_WORDS + FREE_BLIND * e + i])),
        }
    }
}

/// The cells' digest the key binds: Keccak-256 of its tag, the number of cells, and the digests of their runs of
/// `2^12` cells (each the Keccak-256 of its cells' words, 8 little-endian bytes each), the runs hashed in parallel.
fn cells_digest(cells: &[F64]) -> Hash {
    const RUN: usize = 1 << 12;
    /// Whole runs a task hashes together, as the batched Keccak-256 takes them (`hash_many`: the same digests).
    const BATCH: usize = 16;
    let bytes = |run: &[F64]| -> Vec<u8> { run.iter().flat_map(|w| w.0.to_le_bytes()).collect() };
    let whole = cells.len() / RUN;
    let mut runs = vec![[0u8; 32]; cells.len().div_ceil(RUN)];
    parallel::chunks_mut(&mut runs[..whole], BATCH, |b, out| {
        let words = &cells[b * BATCH * RUN..(b * BATCH + out.len()) * RUN];
        // The words' little-endian bytes: on a little-endian target, their memory.
        #[cfg(target_endian = "little")]
        // SAFETY: `F64` is a transparent `u64`; the bytes of the words, read as they lie.
        let data = unsafe { std::slice::from_raw_parts(words.as_ptr().cast::<u8>(), 8 * words.len()) };
        #[cfg(not(target_endian = "little"))]
        let data = &bytes(words)[..];
        primitives::hash::hash_many(data, 8 * RUN, out.as_flattened_mut());
    });
    if whole < runs.len() {
        runs[whole] = primitives::hash::hash(&bytes(&cells[whole * RUN..]));
    }
    let mut hasher = primitives::hash::Hasher::new();
    hasher.update(KDF_CELLS).update(&(cells.len() as u64).to_le_bytes());
    runs.iter().for_each(|digest| {
        hasher.update(digest);
    });
    hasher.finalize()
}

/// A proof's 32-byte seed from the operating system's generator (`rand`'s `OsRng`, that is `getrandom`), which
/// keeps no state in the process: a forked process does not repeat it. [`prove`] draws one per proof.
pub fn fresh_seed() -> [u8; 32] {
    use rand::TryRngCore;
    let mut seed = [0; 32];
    rand::rngs::OsRng
        .try_fill_bytes(&mut seed)
        .expect("the operating system's random generator");
    seed
}

/// The circuit as the verifier's commitment sees it: the coefficients of its wiring polynomial, which sends a
/// cell's point to its successor's.
pub struct Index {
    pub log_rows: usize,
    /// The committed wiring table, the wiring polynomial's `2^m` coefficients ([`Index::wiring`]), its codeword kept
    /// for the opening every proof makes of it ([`open`]). Private, so that an index is only made by [`Index::new`],
    /// which checks the circuit.
    committed: Committed,
    /// The wiring polynomial's values on the quotients' coset, twice the cells: they depend on the circuit alone,
    /// and every proof reads them.
    sigma_values: Vec<F64>,
}

impl Index {
    /// The circuit's index. Panics on a circuit whose wiring the protocol's soundness does not cover
    /// ([`Circuit::errors_have_their_own_poles`]): no such circuit is indexed.
    pub fn new(circuit: &Circuit) -> Self {
        assert!(
            circuit.errors_have_their_own_poles(),
            "a cycle of the wiring holds only rows' first cells and pins: the sum would not catch their errors"
        );
        let index = Self::new_unchecked(circuit);
        // The prover's `b_2` needs `σ`'s coefficient `n − 2` (`PROTOCOL.md`): a property of the circuit, for
        // completeness (`Σ_cells σ(x) · x`, nonzero for wirings but rare ones).
        let wiring = index.wiring();
        let n = wiring.len();
        assert!(!wiring[n - 2].is_zero(), "the wiring's coefficient n − 2 is zero: the prover's b_2 is not defined");
        index
    }

    /// [`Index::new`] without the check (crate-visible for the test that shows what the check prevents).
    pub(crate) fn new_unchecked(circuit: &Circuit) -> Self {
        let mut sigma = parallel::map_collect(circuit.sigma.len(), |i| point(circuit.sigma[i] as usize));
        ntt::coefficients(&mut sigma, F64::ZERO);
        let n = sigma.len();
        // A permutation's: `Σ_cells σ(x) = Σ_cells x = 0`, so its top coefficient is zero (and `x σ` has `n`).
        assert!(sigma[n - 1].is_zero());
        let m = n.trailing_zeros() as usize;
        // SAFETY: each half is written whole by its transform below.
        let mut sigma_values = unsafe { words(2 * n) };
        for (k, half) in sigma_values.chunks_exact_mut(n).enumerate() {
            ntt::values_from(&sigma, half, half_offset(coset(m), n, k));
        }
        let committed = opening::commit(sigma, true);
        assert_eq!(committed.words().len(), n, "the wiring's top lane is not zero");
        Self {
            log_rows: circuit.log_rows,
            committed,
            sigma_values,
        }
    }

    /// The circuit's commitment: its wiring table's, made with the index, which keeps its codeword (`2^(m + 1)` words)
    /// for the opening every proof makes of it ([`open`]).
    pub fn commit(&self) -> &Committed {
        &self.committed
    }

    /// The committed wiring table: the wiring polynomial's `2^m` coefficients.
    pub fn wiring(&self) -> &[F64] {
        self.committed.words()
    }

    fn sigma_values(&self) -> &[F64] {
        &self.sigma_values
    }
}

/// `len` words, their pages mapped by the workers (`pcs_claim::mapped_words`: the passes that first write them would
/// fault each page from every thread at once).
///
/// # Safety
/// The words are uninitialised: the caller must write every word before reading it.
unsafe fn words(len: usize) -> Vec<F64> {
    // SAFETY: the caller's.
    unsafe { pcs_claim::mapped_words(len) }
}

/// `h`'s three limbs in the quotient table's kind-1 half `rest` ([`table_slot`]): limb `e` at `2 e n`.
fn h_slots(rest: &mut [F64], n: usize) -> [&mut [F64]; 3] {
    let mut parts = rest.chunks_exact_mut(n).step_by(2);
    std::array::from_fn(|_| parts.next().expect("three limbs"))
}

/// The words of a run the workers copy or clear at once.
const COPY_RUN: usize = 1 << 16;

/// `dst = src`, copied by the workers.
fn copy_par(dst: &mut [F64], src: &[F64]) {
    parallel::chunks_mut_zip(dst, src, COPY_RUN, |_, d, s| d.copy_from_slice(s));
}

/// `dst = 0`, cleared by the workers.
fn zero_par(dst: &mut [F64]) {
    parallel::chunks_mut(dst, COPY_RUN, |_, d| d.fill(F64::ZERO));
}

/// `low(j)`, the lowest power of two in `j > 0`.
fn low(j: usize) -> usize {
    j & j.wrapping_neg()
}

/// `x F` in the novel basis, `F` of `f.len() = 2^k` coefficients: the product's first `2^k` coefficients into `out`,
/// and its coefficient `2^k` returned (`F`'s top one: the basis is monic). With `F = F_e(w_1) + x F_o(w_1)` and
/// `x^2 = w_1 + x`, `x F = w_1 F_o(w_1) + x (F_e + F_o)(w_1)`, the even part again a product by the variable, one
/// level up; unrolled, coefficient `j ≥ 1` is `f[j − 1] + f[j + low(j) − 1]` and coefficient 0 is zero. No product:
/// the basis's own structure.
pub fn mul_x(f: &[F64], out: &mut [F64]) -> F64 {
    let len = f.len();
    assert!(len.is_power_of_two() && out.len() == len);
    parallel::chunks_mut(out, COPY_RUN, |chunk, out| {
        let base = chunk * COPY_RUN;
        for (i, o) in out.iter_mut().enumerate() {
            let j = base + i;
            *o = if j == 0 { F64::ZERO } else { f[j - 1] + f[j + low(j) - 1] };
        }
    });
    f[len - 1]
}

/// `w_1 F` in the novel basis (`w_1 = X_2 = x^2 + x`), `F` of `f.len() = 2^k ≥ 2` coefficients: the product's first
/// `2^k` coefficients into `out`, and its coefficients `2^k`, `2^k + 1` returned (`F`'s top two). `w_1 F = w_1
/// F_e(w_1) + x w_1 F_o(w_1)`: [`mul_x`] one level up on the even and the odd coefficients, coefficient `j ≥ 2`
/// `f[j − 2] + f[j + 2 low(j / 2) − 2]`.
pub fn mul_w1(f: &[F64], out: &mut [F64]) -> [F64; 2] {
    let len = f.len();
    assert!(len.is_power_of_two() && len >= 2 && out.len() == len);
    parallel::chunks_mut(out, COPY_RUN, |chunk, out| {
        let base = chunk * COPY_RUN;
        for (i, o) in out.iter_mut().enumerate() {
            let j = base + i;
            *o = if j < 2 { F64::ZERO } else { f[j - 2] + f[j + 2 * low(j / 2) - 2] };
        }
    });
    [f[len - 2], f[len - 1]]
}

/// `F` and `r` with `G = x F + r`, `G` of `g.len() = 2^k` coefficients in the novel basis: `F`'s coefficients into
/// `out` (its top one zero) and `r = G(0) = g[0]` returned. The inverse of [`mul_x`]: `f[i] = g[i + 1] + f[i +
/// low(i + 1)]`, a sum along `j ↦ j + low(j)` from `j = i + 1`, made level by level from the largest `low(j)` down,
/// the words of a level independent: the levels of `low(j)` at least a block's length over the whole table, then
/// each block's own, in cache, from the word its block's end holds.
pub fn div_x(g: &[F64], out: &mut [F64]) -> F64 {
    let len = g.len();
    assert!(len.is_power_of_two() && out.len() == len);
    const BLOCK: usize = 1 << 12;
    let block = len.min(BLOCK);
    out[len - 1] = F64::ZERO;
    let ptr = parallel::SendPtr(out.as_mut_ptr());
    // `j = step (2 i + 1)`: `out[j − 1] = g[j] + out[j + step − 1]`, the latter of a level made before (its `low` is
    // at least `2 step`) or zero past the end.
    let level = |step: usize, i: usize| {
        let j = step * (2 * i + 1);
        // SAFETY: a level writes the words `j − 1`, `low(j) = step`, each once, and reads only words of larger
        // `low`, written by the levels before.
        unsafe {
            let above = if j + step < len { *ptr.add(j + step - 1) } else { F64::ZERO };
            *ptr.add(j - 1) = g[j] + above;
        }
    };
    let mut step = len / 2;
    while step >= block {
        let count = len / (2 * step);
        const TASK: usize = 1 << 12;
        parallel::for_each(count.div_ceil(TASK), |task| {
            (task * TASK..((task + 1) * TASK).min(count)).for_each(|i| level(step, i));
        });
        step /= 2;
    }
    // Each block's levels below its length: its words `j − 1`, `j` inside it, read words inside it or its last,
    // `(k + 1) block − 1`, of a level above.
    parallel::for_each(len / block, |k| {
        let mut step = block / 2;
        while step >= 1 {
            let per = block / (2 * step);
            (k * per..(k + 1) * per).for_each(|i| level(step, i));
            step /= 2;
        }
    });
    g[0]
}

/// The offset of the `k`-th half of the quotients' coset of `2 n` points (offset `offset`): the points
/// `offset + B(k n + i)`, `i < n`, are those of the coset of `n` points offset `offset + B(k n)`.
fn half_offset(offset: F64, n: usize, k: usize) -> F64 {
    offset + point(k * n)
}

/// What the transform's top layer, on the coset of `2^(m + 1)` points offset `offset`, makes of a polynomial
/// `a + X_n b` in the novel basis (coefficients `a` below `2^m`, `b` from `2^m` on): the `k`-th half's input is
/// `a + c_k b`, `c_k = X_n` on that half, which this returns.
fn top_layer(offset: F64, m: usize, k: usize) -> F64 {
    let lambda = chain(offset, m + 1)[m];
    if k & 1 == 0 { lambda } else { lambda + F64::ONE }
}

/// [`domain::evaluate`] of the `step` interleaved polynomials of `coeffs` (the `j`-th of coefficients
/// `coeffs[j + step * i]`) at once: `sum_i c_i prod_(k in i) digits[k]`, as the products of a table of the low
/// digits' and one of the high digits', the low sums accumulated unreduced, in parallel over the high index.
fn evaluate_interleaved(coeffs: &[F64], step: usize, digits: &[F192]) -> Vec<F192> {
    let d = digits.len();
    // A committed table may hold fewer words, its trailing zero lanes left out (`opening::commit`): the rest zero.
    let len = coeffs.len();
    assert!(len <= step << d && len.is_multiple_of(step), "the leading words of the {step} polynomials");
    // `t[i]` the product of the digits at `i`'s bits.
    let tensor = |digits: &[F192]| {
        let mut t = vec![F192::ONE];
        for &x in digits {
            let len = t.len();
            for i in 0..len {
                let v = t[i] * x;
                t.push(v);
            }
        }
        t
    };
    let low = d.min(10);
    let (low_weights, high_weights) = (tensor(&digits[..low]), tensor(&digits[low..]));
    let run = step << low;
    let sums: Vec<Vec<F192>> = parallel::map_collect(high_weights.len(), |high| {
        let block = &coeffs[(high * run).min(len)..((high + 1) * run).min(len)];
        let mut acc = vec![F192Unreduced::ZERO; step];
        for (lo, cs) in block.chunks_exact(step).enumerate() {
            for (a, &c) in acc.iter_mut().zip(cs) {
                *a ^= low_weights[lo].mul_base_unreduced(c);
            }
        }
        acc.into_iter().map(|a| high_weights[high] * a.reduce()).collect()
    });
    (0..step)
        .map(|j| sums.iter().fold(F192::ZERO, |acc, s| acc + s[j]))
        .collect()
}

/// Eight extension elements' limbs, each as eight lanes.
fn limbs8(x: &[F192; 8]) -> [Kx8; 3] {
    [
        Kx8::new(x.map(|v| F64(v.c0))),
        Kx8::new(x.map(|v| F64(v.c1))),
        Kx8::new(x.map(|v| F64(v.c2))),
    ]
}

/// The offset of the quotients' coset of `2^(m + 1)` points, for `2^m` cells.
fn coset(m: usize) -> F64 {
    domain::beta_ext()[m + 1]
}

/// The pinned cells' points `p_k` ([`anchor_cell`]) and their Lagrange weights `λ_k = 1 / Π_(j ≠ k) (p_k + p_j)`:
/// the interpolant of values `v_k` on them is `v(x) = Z_P(x) Σ_k v_k λ_k / (x + p_k)`, `Z_P = Π_k (x + p_k)`.
pub fn pins() -> &'static ([F64; PUBLIC_ROWS], [F64; PUBLIC_ROWS]) {
    static PINS: OnceLock<([F64; PUBLIC_ROWS], [F64; PUBLIC_ROWS])> = OnceLock::new();
    PINS.get_or_init(|| {
        let p: [F64; PUBLIC_ROWS] = std::array::from_fn(|k| point(anchor_cell(k)));
        let lambda = std::array::from_fn(|k| {
            (0..PUBLIC_ROWS)
                .filter(|&j| j != k)
                .fold(F64::ONE, |acc, j| acc * (p[k] + p[j]))
                .inv()
        });
        (p, lambda)
    })
}

/// The interpolant of `values` on the pins, as monomial coefficients, lowest first.
fn pin_interpolant(values: &[F64; PUBLIC_ROWS]) -> Vec<F64> {
    let (p, lambda) = pins();
    let mut out = vec![F64::ZERO; PUBLIC_ROWS];
    for k in 0..PUBLIC_ROWS {
        // `λ_k v_k Π_(j ≠ k) (x + p_j)`.
        let mut basis = vec![F64::ONE];
        for j in (0..PUBLIC_ROWS).filter(|&j| j != k) {
            let mut next = vec![F64::ZERO; basis.len() + 1];
            for (i, &c) in basis.iter().enumerate() {
                next[i + 1] += c;
                next[i] += c * p[j];
            }
            basis = next;
        }
        let scale = lambda[k] * values[k];
        for (o, c) in out.iter_mut().zip(basis) {
            *o += scale * c;
        }
    }
    out
}

/// The commitments a proof names: the witness table's and the quotient table's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Commitments {
    pub witness: Commitment,
    pub table: Commitment,
}

/// What a proof leaves: three claims, one point each: on the witness table ([`witness_point`]), the circuit's wiring
/// table, and the quotient table at [`copy_point`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    pub witness: Claim,
    pub wiring: Claim,
    /// The identity's combination of `q` and `x h` at `t`.
    pub copy: Claim,
}

impl Claims {
    /// The claims in the order of [`Openings`], each with the table it is on: `0` the witness, `1` the wiring, `2`
    /// the quotient table ([`Claims::on`] names the commitments).
    pub fn all(&self) -> [(usize, &Claim); 3] {
        [(0, &self.witness), (1, &self.wiring), (2, &self.copy)]
    }

    /// The claims in the order of [`Openings`], each with the commitment it is on: the witness table's, the
    /// circuit's (`index`, the wiring), the quotient table's.
    pub fn on<'a>(&'a self, index: &Commitment, commitments: &Commitments) -> [(Commitment, &'a Claim); 3] {
        [(commitments.witness, &self.witness), (*index, &self.wiring), (commitments.table, &self.copy)]
    }

    /// The PCS claims, in that order: what [`verify_openings`] opens, and the EVM contract checks declared.
    pub fn pcs_claims(&self, index: &Commitment, commitments: &Commitments) -> [PcsClaim; 3] {
        self.on(index, commitments).map(|(on, claim)| on.pcs_claim(claim))
    }
}

/// Where the reduction's scalars sit in a proof's stream ([`reduce`] reads them in this order): the witness table's
/// root (two scalars) and out-of-domain answer, the quotient table's root and answer, the row values `X`, `C`, `V +
/// Y` at `t` ([`row_values`]), and the wiring's value at `t`.
pub mod stream {
    pub const WITNESS_ROOT: usize = 0;
    pub const WITNESS_OOD: usize = 2;
    pub const TABLE_ROOT: usize = 3;
    pub const TABLE_OOD: usize = 5;
    /// The three row values, from here.
    pub const ROW_VALUES: usize = 6;
    pub const NEXT: usize = 9;
    /// The scalars of a proof.
    pub const LEN: usize = 10;
}

/// The two coordinates of the extension over the base field, and the scale of their weights `(1, Y, Y^2, Y^3)`.
pub fn extension() -> ([F192; 2], F192) {
    let (y, y2) = (F192::Y, F192::Y * F192::Y);
    let (d0, d1) = (F192::ONE + y, F192::ONE + y2);
    ([y * d0.inv(), y2 * d1.inv()], (d0 * d1).inv())
}

/// The point of the claim on the quotient table that the identity gives: `t`'s coordinates `u` (`m + 1`: the
/// coefficient's `m`, then the digit's, `ζ / (1 + ζ)`, `ζ = Z x` at `t`), [`extension`]'s two, then `kappa`, which
/// weighs `x h` against `q`.
pub fn copy_point<S: Scalar>(u: &[S], kappa: S) -> Vec<S> {
    let ([y0, y1], _) = extension();
    [u, &[S::constant(y0), S::constant(y1), kappa]].concat()
}

/// The row of `t`, its four cells `(X, Y, C, V)` at `t + B(c)`, from the row polynomials' values `a` at `t`
/// (`w = a_0 + x a_1 + w_1 (a_2 + x a_3)`, the `a_j` in the higher coordinates, which `B(c)` leaves alone), `omega =
/// w_1(t)`: the three values the verifier reads, `X`, `C` and `V + Y` ([`crate::circuit`]: the gate is `V + Y + C +
/// X C`).
pub fn row_values<S: Scalar>(a: [S; 4], t: S, omega: S) -> [S; 3] {
    let theta = S::constant(F192::from(beta()[1]));
    let one = S::constant(F192::ONE);
    let cell = |first: S, second: S| a[0] + first * a[1] + second * (a[2] + first * a[3]);
    let x = cell(t, omega);
    let y = cell(t + one, omega);
    let c = cell(t + theta, omega + one);
    let v = cell(t + theta + one, omega + one);
    [x, c, v + y]
}

/// The witness table's claim at its row point `(z_0, z_1)` (its other coordinates `t`'s): its value is `Σ_j e_j a_j`
/// times the higher coordinates' normalisation, `e = (1 + z_0, z_0) ⊗ (1 + z_1, z_1)` the low coordinates'
/// weights. The row values `X`, `C`, `V + Y` are three linear forms of `a` (each a cell, or two, at `t`); their span
/// `S` is the plane `(t + θ ω) e_00 + e_10 + θ e_01 = 0` (`θ = β_1`), on which the rank-one weights form a conic
/// that no line of the Segre quadric lies in. So `z_0 = ρ` random and `z_1 = a / (a + b)`, `a = (t + θ ω)(1 + ρ) +
/// ρ`, `b = θ (1 + ρ)`, put `e` on `S` and spread it over all of `S` as `ρ` varies: the claim binds the three values.
/// This returns `(a, b)`; the verifier inverts `a + b` with its other denominators.
pub fn witness_conic<S: Scalar>(t: S, omega: S, rho: S) -> (S, S) {
    let theta = S::constant(F192::from(beta()[1]));
    let rho1 = S::constant(F192::ONE) + rho;
    ((t + omega * theta) * rho1 + rho, theta * rho1)
}

/// The weights `λ` with `e = λ_0 X + λ_1 C + λ_2 (V + Y)` as linear forms of `a` ([`witness_conic`]), at `z_0 = rho`,
/// `z_1`: the witness table's claim's value is `λ · (X, C, V + Y)` times the normalisation.
pub fn witness_weights<S: Scalar>(t: S, omega: S, rho: S, z1: S) -> [S; 3] {
    let theta = S::constant(F192::from(beta()[1]));
    let one = S::constant(F192::ONE);
    let (rho1, z11) = (one + rho, one + z1);
    let (e00, e01, e11) = (rho1 * z11, rho1 * z1, rho * z1);
    let k3 = t + theta * omega + theta + one;
    let lambda1 = e11 + t * omega * e00 + k3 * (e01 + omega * e00);
    [e00 + lambda1, lambda1, e01 + omega * e00 + lambda1]
}

/// The transcript's seed: the protocol's name, the circuit's commitment (its root and out-of-domain answer) and the
/// statement (136 bytes).
pub fn label(index: &Commitment, statement: &Statement) -> Vec<u8> {
    [
        NAME.as_slice(),
        &index.root,
        &pcs_claim::element_bytes(index.ood),
        &statement.y,
        &statement.root,
    ]
    .concat()
}

/// The gate, `V + Y + C + X·C`, which vanishes on a row's cells.
fn gate<T: Copy + Add<Output = T> + Mul<Output = T>>([x, y, c, v]: [T; 4]) -> T {
    v + y + c + x * c
}

fn batch_inverse(values: &mut [F192]) {
    let mut prefix = Vec::with_capacity(values.len());
    let mut acc = F192::ONE;
    for &v in values.iter() {
        prefix.push(acc);
        acc *= v;
    }
    let mut inverse = acc.inv();
    for (v, p) in values.iter_mut().zip(prefix).rev() {
        let next = inverse * *v;
        *v = inverse * p;
        inverse = next;
    }
}

/// Every lane of every vector of `values` inverted (all nonzero), by Montgomery's trick.
fn batch_inverse_k(values: &mut [Kx8]) {
    let mut prefix = Vec::with_capacity(values.len());
    let mut acc = Kx8::splat(F64::ONE);
    for &v in values.iter() {
        prefix.push(acc);
        acc = acc * v;
    }
    let mut inverse = Kx8::new(acc.to_row().0.map(|x| x.inv()));
    for (v, p) in values.iter_mut().zip(prefix).rev() {
        let next = inverse * *v;
        *v = inverse * p;
        inverse = next;
    }
}

/// `x^-1` for a nonzero `x`, by its norm to `GF(2^64)`: `m = x^(2^64) x^(2^128)` makes `x m` the norm, whose
/// inverse is its power `2^64 - 2`, reached through the powers `2^k - 1`.
fn inverse<S: Scalar>(x: S) -> S {
    let m = x.frobenius() * x.frobenius().frobenius();
    let norm = x * m;
    let (mut ones, mut k) = (norm, 1);
    for bit in (0..5).rev() {
        let mut shifted = ones;
        for _ in 0..k {
            shifted = shifted * shifted;
        }
        (ones, k) = (shifted * ones, 2 * k);
        if (63 >> bit) & 1 == 1 {
            (ones, k) = (ones * ones * norm, k + 1);
        }
    }
    debug_assert_eq!(k, 63);
    m * (ones * ones)
}

/// A proof and what the prover keeps to open its claims.
pub struct Proved {
    pub proof: Proof,
    pub commitments: Commitments,
    pub claims: Claims,
    pub tables: Tables,
}

/// The two tables a proof commits, which [`open`] consumes.
pub struct Tables {
    pub witness: Committed,
    pub table: Committed,
}

/// Prove `statement` from the cells of a witness, against the circuit committed as `index`, with randomness of its
/// own, fresh per proof and never reused: a 32-byte seed from the operating system ([`fresh_seed`]), from which
/// [`Randomness::derive`] makes the random rows' words and the blinding. Panics on a challenge the verifier
/// rejects.
pub fn prove(circuit: &Circuit, index: &Index, commitment: &Commitment, statement: &Statement, cells: &[F64]) -> Proved {
    prove_with_seed(circuit, index, commitment, statement, cells, &fresh_seed())
}

/// [`prove`] with its 32-byte seed given, deterministic: for tests and reproducible benchmarks. The randomness is
/// always [`Randomness::derive`]'s, bound to the statement and the witness, so a seed reused for another witness
/// gives unrelated randomness; the proof hides the witness only if `seed` is secret and fresh per proof, as
/// [`prove`]'s is. Panics on a challenge the verifier rejects.
pub fn prove_with_seed(
    circuit: &Circuit,
    index: &Index,
    commitment: &Commitment,
    statement: &Statement,
    cells: &[F64],
    seed: &[u8; 32],
) -> Proved {
    let randomness = Randomness::derive(seed, commitment, statement, cells);
    prove_with_randomness(circuit, index, commitment, statement, cells, &randomness)
}

/// The hooks of the tests' cheating prover (`tests::cheat`), which does what the honest one does but with a bad
/// witness's errors: here, nothing.
#[cfg(not(test))]
mod cheat {
    use primitives::field::{F64, F192};

    use crate::circuit::Circuit;
    use crate::statement::Statement;

    #[inline(always)]
    pub(super) fn absorb(_: &Circuit, _: &Statement, _: &[F64], _: [F192; 3], _: [&mut [F64]; 3]) {}

    #[inline(always)]
    pub(super) fn spill(_: [F64; 3]) -> [F64; 3] {
        [F64::ZERO; 3]
    }
}
#[cfg(test)]
use tests::cheat;

/// `q_e[j] += limb e of Σ_k c_k f_k[j]` for each limb `e` and word `j`, the `f_k` columns over `K`, eight words a step
/// and one reduction a limb.
fn add_mixed(q: [&mut [F64]; 3], terms: &[(F192, &[F64])]) {
    let [q0, q1, q2] = q;
    let len = q0.len();
    assert!(len.is_multiple_of(8) && terms.iter().all(|(_, f)| f.len() >= len));
    let terms: Vec<(ESplat, &[F64])> = terms.iter().map(|&(c, f)| (ESplat::new(c), f)).collect();
    const RUN: usize = 1 << 12;
    parallel::chunks_mut3(q0, q1, q2, RUN, |chunk, q0, q1, q2| {
        let base = chunk * RUN;
        for s in (0..q0.len()).step_by(8) {
            let mut acc = MixedSum::default();
            for (c, f) in &terms {
                acc.add(c, Kx8::load(&f[base + s..]));
            }
            for (q, l) in [&mut q0[..], &mut q1[..], &mut q2[..]].into_iter().zip(acc.reduce().limbs()) {
                (Kx8::load(&q[s..]) + l).store_to(&mut q[s..]);
            }
        }
    });
}

/// The `E` element whose limbs are the words `e` gives.
fn limbs_element(e: impl Fn(usize) -> F64) -> F192 {
    F192::new(e(0).0, e(1).0, e(2).0)
}

/// [`prove`] with its randomness given. Crate-private: outside the crate, randomness reaches the prover only through
/// [`Randomness::derive`] ([`prove`], [`prove_with_seed`]), so it cannot be reused across witnesses; the crate's
/// tests use it to fix the random rows and the blinding. Panics on a challenge the verifier rejects.
pub(crate) fn prove_with_randomness(
    circuit: &Circuit,
    index: &Index,
    commitment: &Commitment,
    statement: &Statement,
    cells: &[F64],
    randomness: &Randomness,
) -> Proved {
    let Randomness { rows, blind } = randomness;
    assert!(
        supported(circuit.log_rows),
        "2^{} rows: the layouts take 2^{MIN_LOG_ROWS} to 2^{MAX_LOG_ROWS}",
        circuit.log_rows
    );
    let m = cell_vars(circuit.log_rows);
    let n = 1usize << m;
    assert_eq!(cells.len(), n);
    assert!(m + 3 <= domain::EXT_BASIS);
    let mut ps = ProverChain::new(&label(commitment, statement));
    // SAFETY: written whole by the copy below.
    let mut randomized = unsafe { words(n) };
    copy_par(&mut randomized, cells);
    circuit.randomize(&mut randomized, rows);
    let cells = &randomized[..];

    // The witness: the cells' polynomial.
    let span = tracing::info_span!("Witness").entered();
    // SAFETY: written whole by the transform below.
    let mut w_hat = unsafe { words(n) };
    tracing::info_span!("cells to coefficients").in_scope(|| ntt::coefficients_from(cells, &mut w_hat, F64::ZERO));

    // The witness's values on the quotient's coset, twice the cells: two cosets of the cells' size, offset by
    // `B(k n)`. They do not depend on the challenges: made here, while the coefficients are at hand.
    let big = 2 * n;
    let offset = coset(m);
    // SAFETY: each half is written whole by its transform in `two_halves`.
    let mut values = unsafe { words(big) };
    // The transforms in two parts (the supported sizes have at least a leaf's cells): the layers above a leaf a
    // pass over memory each, and each leaf's own layers in the block-wise loop below, around the quotient's values,
    // a block in cache.
    assert!(n >= ntt::LEAF_WORDS);
    // The values on the two halves of `coeffs + X_n extra` (`extra`'s coefficients from `n` on): `coeffs` with
    // `extra` times `X_n`'s value on each half's coset added to its leading words ([`top_layer`]), one pass reading
    // `coeffs` for both halves' first layers.
    let half_offsets: [F64; 2] = std::array::from_fn(|k| half_offset(offset, n, k));
    let two_halves = |coeffs: &[F64], extra: &[F64], out: &mut [F64]| {
        let heads: [Vec<F64>; 2] = std::array::from_fn(|k| extra.iter().map(|&c| top_layer(offset, m, k) * c).collect());
        let heads: Vec<&[F64]> = heads.iter().map(|h| &h[..]).collect();
        let mut halves: Vec<&mut [F64]> = out.chunks_exact_mut(n).collect();
        ntt::values_upper_many(coeffs, &heads, &mut halves, &half_offsets);
    };
    tracing::info_span!("witness values").in_scope(|| two_halves(&w_hat, &[], &mut values));
    // `w`'s top coefficient, which `q`'s coefficient `2 n` reads.
    let w_top = w_hat[n - 1];
    let witness = tracing::info_span!("Commit").in_scope(|| opening::commit(w_hat, false));
    ps.send_root(&witness.root);
    ps.send(witness.ood);
    drop(span);
    let [alpha, beta_, mu] = [(); 3].map(|_| ps.sample());

    // The sum's polynomial on the cells, its coefficients a limb at a time, written in the quotient table's slots
    // for `x h` ([`table_slot`]): limb `e` at `table_slot(1, e, n)`.
    let span = tracing::info_span!("Sum").entered();
    let inner = tracing::info_span!("inverses").entered();
    // SAFETY: every slot is written before it is read: `h`'s limbs by the inverses, `q`'s by the halves' transforms
    // of `h`'s coefficients, the two products' columns in the quotient's pass, and the rest cleared before the
    // commitment.
    let mut table = unsafe { words(16 * n) };
    let (quotients, rest) = table.split_at_mut(4 * big);
    {
        let [h0, h1, h2] = h_slots(rest, n);
        let (alpha8, beta8) = (Ex8::splat(alpha), Ex8::splat(beta_));
        let beta_points = Ex8::from_limbs(limbs8(&std::array::from_fn(|l| beta_.mul_base(point(l)))));
        parallel::chunks_mut3(h0, h1, h2, 1 << 12, |chunk_index, h0, h1, h2| {
            // The denominators of eight cells at a time, `d0` to the cell's own point and `d1` to its successor's,
            // inverted by Montgomery's trick in sixteen interleaved chains, one a lane of each.
            let base = chunk_index << 12;
            let steps = h0.len() / 8;
            let (mut d0s, mut d1s, mut p0s, mut p1s) = (
                Vec::with_capacity(steps),
                Vec::with_capacity(steps),
                Vec::with_capacity(steps),
                Vec::with_capacity(steps),
            );
            let (mut acc0, mut acc1) = (Ex8::splat(F192::ONE), Ex8::splat(F192::ONE));
            for s in 0..steps {
                let i = base + 8 * s;
                let common = alpha8 + Ex8::from_k(Kx8::load(&cells[i..]));
                let d0 = common + Ex8::splat(beta_.mul_base(point(i))) + beta_points;
                let next = Kx8::new(std::array::from_fn(|l| point(circuit.sigma[i + l] as usize)));
                let d1 = common + beta8.mul_k(next);
                (p0s.push(acc0), p1s.push(acc1));
                (acc0, acc1) = (acc0 * d0, acc1 * d1);
                (d0s.push(d0), d1s.push(d1));
            }
            let mut last = [acc0.to_array(), acc1.to_array()].concat();
            batch_inverse(&mut last);
            let (mut inv0, mut inv1) = (
                Ex8::from_limbs(limbs8(&last[..8].try_into().unwrap())),
                Ex8::from_limbs(limbs8(&last[8..].try_into().unwrap())),
            );
            for s in (0..steps).rev() {
                let out = inv0 * p0s[s] + inv1 * p1s[s];
                (inv0, inv1) = (inv0 * d0s[s], inv1 * d1s[s]);
                for (h, c) in [&mut h0[..], &mut h1[..], &mut h2[..]].into_iter().zip(out.limbs()) {
                    h[8 * s..8 * s + 8].copy_from_slice(&c.to_row().0);
                }
            }
        });
    }
    drop(inner);
    // A cheating prover's absorption of a bad witness's errors into `h` (the tests' alone: [`cheat`]).
    cheat::absorb(circuit, statement, cells, [alpha, beta_, mu], h_slots(rest, n));
    drop(randomized);
    tracing::info_span!("coefficients")
        .in_scope(|| h_slots(rest, n).into_iter().for_each(|h| ntt::coefficients(h, F64::ZERO)));
    drop(span);

    // The quotient, on the coset of the witness's values, written into the quotient table's slots for `q`'s limbs
    // ([`table_slot`]), which hold `h`'s values first. The blinding `X_n (b_0 + b_1 X_1 + b_2 X_2)`, `b_2` zero for
    // now: it is solved for once `q` is known, and added then as `b_2 w_1 d d'` ([`H_BLIND`]).
    let span = tracing::info_span!("Quotients").entered();
    let sigma_values = index.sigma_values();
    let sigma = index.wiring();
    let extra: [[F64; H_BLIND]; 3] = std::array::from_fn(|e| [blind[e][0], blind[e][1], F64::ZERO]);
    tracing::info_span!("sum values").in_scope(|| {
        for ((h, column), extra) in h_slots(rest, n).into_iter().zip(quotients.chunks_exact_mut(big)).zip(&extra) {
            two_halves(&*h, extra, column);
        }
    });

    let inner = tracing::info_span!("quotient values").entered();
    // `w_1 w^2` has degree `2 n`, its coefficient `2 n` (monic basis) `w`'s top one squared. On the coset
    // `X_{2n} = 1` (its offset is `β_{m+1}`), so its values less that are those of its first `2 n` coefficients.
    let w_top2 = w_top * w_top;
    debug_assert_eq!(domain::chain(offset, m + 2)[m + 1], F64::ONE);
    let tau = row_vanishing(m);
    let row_poly = |x: F64| {
        chain(x, m - 1)
            .iter()
            .zip(&tau)
            .fold(F64::ZERO, |acc, (&w, &t)| acc + t * w)
    };
    let row_low: [F64; 4] = std::array::from_fn(|c| row_poly(point(c)));
    let offsets = chain(offset, m + 1);
    let (alpha8, beta8) = (Ex8::splat(alpha), Ex8::splat(beta_));
    let beta_points = Ex8::from_limbs(limbs8(&std::array::from_fn(|l| beta_.mul_base(point(l)))));
    let lane_points = Kx8::new(std::array::from_fn(point));
    let (mu8, w_top8) = (Ex8::splat(mu), Kx8::splat(w_top2));
    // The pins: their points, and the public values' interpolant on them.
    let (pin_points, _) = pins();
    let interpolant = pin_interpolant(&anchor_values(&statement.words()));
    // The quotient's values on the `len` points from `base`: `w` the witness's values there, `q` the sum's limbs
    // (overwritten with `q`'s): `(h d d' + d + d') / Z + μ g`, `g` the gates' and pins' quotient. And the products
    // `w_1 w^2` (less its coefficient `2 n`) and `w_1 w (x + σ)`, from which `w_1 d d'`'s coefficients are made for
    // `b_2`.
    let quotient_block = |base: usize, w_values: &[F64], q: [&mut [F64]; 3], u: [&mut [F64]; 2]| {
        let len = w_values.len();
        let cell_vanishing = (offsets[m] + point(base >> m)).inv();
        let row_base = row_poly(offset + point(base));
        let row_vanishing: [F64; 4] = std::array::from_fn(|c| (row_base + row_low[c]).inv());
        // Eight points at a time, lane `l` the `l`-th: `B(i + l) = B(i) + B(l)` for `i` a multiple of eight.
        let (cell_vanishing, row_vanishing) = (
            Kx8::splat(cell_vanishing),
            Kx8::new(std::array::from_fn(|l| row_vanishing[l & 3])),
        );
        let limb = |x: &[F64]| Kx8::load(x);
        let [q0, q1, q2] = q;
        let [u1, u2] = u;
        let mut gates = Vec::with_capacity(len / 8);
        let mut pinned = Vec::with_capacity(len / 8);
        let mut z_pins = Vec::with_capacity(len / 8);
        for low in (0..len).step_by(8) {
            let i = base + low;
            let x = Kx8::splat(offset + point(i)) + lane_points;
            let w = limb(&w_values[low..]);
            let sigma = limb(&sigma_values[i..]);
            let w1 = x * x + x;
            (w1 * w * w + w_top8).store_to(&mut u1[low..]);
            (w1 * w * (x + sigma)).store_to(&mut u2[low..]);
            let common = alpha8 + Ex8::from_k(w);
            let d = common + Ex8::splat(beta_.mul_base(offset + point(i))) + beta_points;
            let d_next = common + beta8.mul_k(sigma);
            let h = Ex8::from_limbs([limb(&q0[low..]), limb(&q1[low..]), limb(&q2[low..])]);
            let [c0, c1, c2] = ((h * d * d_next + d + d_next).mul_k(cell_vanishing)).limbs();
            for (out, c) in [&mut q0[..], &mut q1[..], &mut q2[..]].into_iter().zip([c0, c1, c2]) {
                out[low..low + 8].copy_from_slice(&c.to_row().0);
            }
            let row = [w, w.xor_lanes(1), w.xor_lanes(2), w.xor_lanes(3)];
            gates.push(gate(row) * row_vanishing);
            // `w + v` and `Z_P` at the eight points.
            let v = interpolant.iter().rev().fold(Kx8::splat(F64::ZERO), |acc, &c| acc * x + Kx8::splat(c));
            pinned.push(w + v);
            z_pins.push(pin_points.iter().fold(Kx8::splat(F64::ONE), |acc, &p| acc * (x + Kx8::splat(p))));
        }
        batch_inverse_k(&mut z_pins);
        for (s, ((&gate, &num), &inv)) in gates.iter().zip(&pinned).zip(&z_pins).enumerate() {
            let at = 8 * s;
            let copy = Ex8::from_limbs([limb(&q0[at..]), limb(&q1[at..]), limb(&q2[at..])]);
            let [c0, c1, c2] = (copy + mu8.mul_k(gate + num * inv)).limbs();
            for (out, c) in [&mut q0[..], &mut q1[..], &mut q2[..]].into_iter().zip([c0, c1, c2]) {
                out[at..at + 8].copy_from_slice(&c.to_row().0);
            }
        }
    };
    // The products' columns: the two limb-3 slots, empty in the table, `2 n` words each.
    let (q_cols, u1_col) = quotients.split_at_mut(3 * big);
    let (rest, u2_col) = rest.split_at_mut(3 * big);
    let block = ntt::LEAF_WORDS;
    let w_ptr = parallel::SendPtr(values.as_mut_ptr());
    let q_ptr = parallel::SendPtr(q_cols.as_mut_ptr());
    let u_ptrs = [parallel::SendPtr(u1_col.as_mut_ptr()), parallel::SendPtr(u2_col.as_mut_ptr())];
    parallel::for_each(big / block, |task| {
        let start = task * block;
        // SAFETY: the words `start..start + block` of each of the six columns are this task's alone.
        let (w, mut q, mut u) = unsafe {
            (
                w_ptr.slice(start, block),
                [0, 1, 2].map(|limb| q_ptr.slice(limb * big + start, block)),
                u_ptrs.each_ref().map(|p| p.slice(start, block)),
            )
        };
        let k = start / n;
        let at = half_offset(offset, n, k);
        ntt::values_leaf(w, start - k * n, n, at);
        q.iter_mut().for_each(|q| ntt::values_leaf(q, start - k * n, n, at));
        {
            let [q0, q1, q2] = &mut q;
            let [u1, u2] = &mut u;
            quotient_block(start, w, [&mut q0[..], &mut q1[..], &mut q2[..]], [&mut u1[..], &mut u2[..]]);
        }
        q.iter_mut().chain(u.iter_mut()).for_each(|q| ntt::coefficients_leaf(q, start, big, offset));
    });
    drop(inner);
    let backward = |column: &mut [F64]| ntt::coefficients_upper(column, offset);
    tracing::info_span!("quotient coefficients").in_scope(|| {
        q_cols.chunks_exact_mut(big).for_each(backward);
        backward(&mut u1_col[..big]);
        backward(&mut u2_col[..big]);
    });
    drop(values);

    // `x h`'s low part, `B_0 = x h_low`, into digit 0 of kind 1 (digit 1 its scratch). Its coefficient `n` is `h`'s
    // coefficient `n − 1`, zero when the sum over the cells is ([`mul_x`]).
    let inner = tracing::info_span!("tables").entered();
    let part = tracing::info_span!("x h").entered();
    let mut overflow = [F64::ZERO; 3];
    for (e, slot) in rest.chunks_exact_mut(big).enumerate() {
        let (low, high) = slot.split_at_mut(n);
        overflow[e] = mul_x(low, high);
        copy_par(low, high);
    }
    // Zero but for a witness that is not one: dropped (the honest prover's proof of it then fails), or spilled by a
    // cheating prover ([`cheat`]).
    let spill = cheat::spill(overflow);

    // `b_2`: `q = A_0 + Z x A_1` needs `q`'s high part `Q_h` (`q = q_low + Z Q_h`) to vanish at 0, its coefficient 0,
    // `q`'s coefficient `n`. `b_2` adds `b_2 E` to `q`, `E = w_1 d d'`, `d d' = α^2 + α β (x + σ) + w^2 + β w (x + σ) +
    // β^2 x σ`; `E`'s coefficient `2 n` is `w_top^2`, and `X_{2n} = Z (Z + 1)`, so `E`'s high part at 0 is
    // `γ = E_n + w_top^2 = (d d')_{n−2} ∋ α β σ_{n−2}`: not zero but for one `α` ([`Index::new`] checks `σ_{n−2}`).
    drop(part);
    let part = tracing::info_span!("b_2").entered();
    let (v1, v2) = (&u1_col[..big], &u2_col[..big]);
    let (s1, others) = rest[n..].split_at_mut(n);
    let (s2, s3) = others[n..4 * n].split_at_mut(n);
    let s3 = &mut s3[n..];
    // `w_1 (x + σ)` into `s2`, `w_1 x σ` into `s3`, their coefficients `n` and `n + 1` apart.
    copy_par(s1, sigma);
    s1[1] += F64::ONE;
    let w1_sigma_high = mul_w1(s1, s2);
    assert!(mul_x(sigma, s1).is_zero());
    let w1_x_sigma_high = mul_w1(s1, s3);
    let (s2, s3) = (&*s2, &*s3);
    let ab = alpha * beta_;
    let b2_ = beta_ * beta_;
    let e_high = |k: usize| {
        ab.mul_base(w1_sigma_high[k]) + b2_.mul_base(w1_x_sigma_high[k])
            + F192::from(v1[n + k])
            + beta_.mul_base(v2[n + k])
    };
    let gamma = e_high(0) + F192::from(w_top2);
    let target = limbs_element(|e| q_cols[e * big + n]);
    assert!(!gamma.is_zero(), "a challenge to reject: w_1 d d' has no coefficient n");
    let b2 = target * gamma.inv();
    let lc = b2.mul_base(w_top2);
    {
        let mut limbs = q_cols.chunks_exact_mut(big).map(|c| c.split_at_mut(n));
        let [(l0, h0), (l1, h1), (l2, h2)] = std::array::from_fn(|_| limbs.next().expect("three limbs"));
        add_mixed(
            [&mut *l0, &mut *l1, &mut *l2],
            &[(b2 * ab, s2), (b2, &v1[..n]), (b2 * beta_, &v2[..n]), (b2 * b2_, s3)],
        );
        add_mixed([&mut *h0, &mut *h1, &mut *h2], &[(b2, &v1[n..]), (b2 * beta_, &v2[n..])]);
        // `α^2 w_1` at coefficient 2; `E`'s small parts' coefficients `n`, `n + 1` in `Q_h`'s 0 and 1, and `E`'s
        // coefficient `2 n`, `w_top^2 X_{2n} = w_top^2 Z (Z + 1)`, in `Q_h`'s 0 (and its `n`, `lc`, below).
        let columns = [l0, l1, l2, h0, h1, h2];
        let small = |k: usize| ab.mul_base(w1_sigma_high[k]) + b2_.mul_base(w1_x_sigma_high[k]);
        let fix = [(2, b2 * alpha * alpha), (n, b2 * small(0) + lc), (n + 1, b2 * small(1))];
        for (j, add) in fix {
            for (e, c) in [add.c0, add.c1, add.c2].into_iter().enumerate() {
                columns[e + 3 * (j / n)][j % n] += F64(c);
            }
        }
        debug_assert!(columns[3][0].is_zero() && columns[4][0].is_zero() && columns[5][0].is_zero());
    }
    drop(part);
    let part = tracing::info_span!("A_1").entered();
    let lc_limbs = [F64(lc.c0), F64(lc.c1), F64(lc.c2)];
    // `A_1 = Q_h / x`: `q[n..2 n] / x`, exact now, and `lc X_n / x = lc Σ_(j < n) X_j`.
    {
        let scratch = &mut u1_col[..n];
        for (column, &lc) in q_cols.chunks_exact_mut(big).zip(&lc_limbs) {
            let high = &mut column[n..];
            let remainder = div_x(high, scratch);
            assert!(remainder.is_zero(), "b_2 zeroes q's coefficient n");
            parallel::chunks_mut_zip(high, scratch, COPY_RUN, |_, a, s| {
                for (a, &s) in a.iter_mut().zip(s) {
                    *a = s + lc;
                }
            });
        }
    }

    // The empty limbs; the blinding, `b_0, b_1, b_2`, in digit 1 of `x h`'s limbs, `B_1` (`P = B_0 + Z x B_1`).
    // The commitment leaves the zero lanes out of the encoding (`opening::commit`), and the trailing ones out of the
    // table.
    drop(part);
    let part = tracing::info_span!("clear").entered();
    zero_par(u1_col);
    zero_par(u2_col);
    let b2_limbs = [F64(b2.c0), F64(b2.c1), F64(b2.c2)];
    for (e, digit) in rest.chunks_exact_mut(n).skip(1).step_by(2).enumerate() {
        zero_par(digit);
        digit[..H_BLIND].copy_from_slice(&[blind[e][0] + spill[e], blind[e][1], b2_limbs[e]]);
    }
    drop(part);
    drop(inner);
    let table = tracing::info_span!("Commit").in_scope(|| opening::commit(table, false));
    ps.send_root(&table.root);
    ps.send(table.ood);
    drop(span);

    let t = ps.sample();
    let digits: Vec<F192> = std::iter::successors(Some(t), |&w| Some(w * w + w)).take(m).collect();
    let a = evaluate_interleaved(witness.words(), 4, &digits[2..m]);
    row_values([a[0], a[1], a[2], a[3]], t, digits[1]).into_iter().for_each(|x| ps.send(x));
    let next = evaluate_interleaved(index.wiring(), 1, &digits[..m])[0];
    ps.send(next);
    ps.sample();

    let proof = ps.into_proof();
    let (commitments, claims) = verify(commitment, statement, &proof, circuit.log_rows).expect("a challenge to reject");
    Proved {
        proof,
        commitments,
        claims,
        tables: Tables { witness, table },
    }
}

/// What [`reduce`] leaves: the two commitments, each as its root's two scalars and its out-of-domain answer (the
/// witness table, the quotient table), and the three claims as a point and a value.
pub struct Reduced<S> {
    pub roots: [[S; 2]; 2],
    pub oods: [S; 2],
    pub witness: (Vec<S>, S),
    pub wiring: (Vec<S>, S),
    pub copy: (Vec<S>, S),
}

/// The verifier, on any [`Scalar`]: the proof read from `channel`, down to the commitments it names and the three
/// claims. It rejects only a challenge at which a denominator vanishes.
pub fn reduce<S: Scalar>(channel: &mut impl Channel<S>, log_rows: usize) -> Result<Reduced<S>, VerifyError> {
    let transcript = VerifyError::Transcript;
    let m = cell_vars(log_rows);
    let base = |x: F64| S::constant(F192::from(x));
    let one = S::constant(F192::ONE);

    let public = channel.statement();
    let witness_root = channel.next_root().map_err(transcript)?;
    let witness_ood = channel.next().map_err(transcript)?;
    let [alpha, beta_, mu] = [(); 3].map(|_| channel.sample());
    let table_root = channel.next_root().map_err(transcript)?;
    let table_ood = channel.next().map_err(transcript)?;
    let t = channel.sample();
    // The row of `t`: `X`, `C` and `V + Y` there ([`row_values`]).
    let mut row = [t; 3];
    for value in &mut row {
        *value = channel.next().map_err(transcript)?;
    }
    let next = channel.next().map_err(transcript)?;
    let rho = channel.sample();
    channel.finish().map_err(transcript)?;

    // `w_k(t)`, up to the digit past the cells: `w_m = Z`, the cells' vanishing polynomial.
    let mut w = vec![t];
    for k in 0..m {
        w.push(w[k] * w[k] + w[k]);
    }
    let [x, c, vy] = row;
    let gate = vy + c + x * c;

    let tau = row_vanishing(m);
    let rows = (0..m - 1).fold(S::constant(F192::ZERO), |acc, k| acc + base(tau[k]) * w[k]);
    let (d, d_next) = (alpha + x + beta_ * t, alpha + x + beta_ * next);
    let product = d * d_next;
    let z = w[m];
    // The quotient table's digit 1 is read through `ζ = Z x` ([`table_slot`]).
    let zeta = z * t;
    let (pin_points, lambda) = pins();
    let (conic_a, conic_b) = witness_conic(t, w[1], rho);

    // One inversion: of every `1 + w_k` below the digit, of `1 + ζ`, of the identity's `ζ + d d'`, of the rows'
    // polynomial, of every `t + p_k`, and of the witness claim's `a + b`.
    let mut denominators: Vec<S> = w[..m].iter().map(|&w| one + w).collect();
    denominators.extend([one + zeta, zeta + product, rows]);
    denominators.extend(pin_points.iter().map(|&p| t + base(p)));
    denominators.push(conic_a + conic_b);
    let mut prefix = vec![one];
    for &value in &denominators {
        prefix.push(*prefix.last().unwrap() * value);
    }
    let all = prefix[denominators.len()];
    if !all.is_nonzero() {
        return Err(VerifyError::Degenerate);
    }
    let mut running = inverse(all);
    let mut inverses = denominators.clone();
    for i in (0..denominators.len()).rev() {
        inverses[i] = running * prefix[i];
        running = running * denominators[i];
    }
    let mut u: Vec<S> = (0..m).map(|k| w[k] * inverses[k]).collect();
    u.push(zeta * inverses[m]);
    let (copy_inverse, rows_inverse) = (inverses[m + 1], inverses[m + 2]);
    let pin_inverses = &inverses[m + 3..m + 3 + PUBLIC_ROWS];
    let conic_inverse = inverses[m + 3 + PUBLIC_ROWS];
    let middle = (3..m).fold(inverses[2], |acc, k| acc * inverses[k]);
    let wiring_scale = middle * inverses[0] * inverses[1];
    let table_scale = wiring_scale * inverses[m];

    // `g(t) = gate / Z_R + (w + v) / Z_P`, `v / Z_P = Σ_k v_k λ_k / (t + p_k)`: the words, then the constants
    // `0` (no term), `1` and `3`.
    let values = anchor_values(&[F64::ZERO; PUBLIC_WORDS]);
    let mut pinned = x * pin_inverses.iter().fold(one, |acc, &inv| acc * inv);
    for k in 0..PUBLIC_ROWS {
        let weight = if k < PUBLIC_WORDS {
            public[k] * base(lambda[k])
        } else if values[k].is_zero() {
            continue;
        } else {
            base(lambda[k] * values[k])
        };
        pinned = pinned + weight * pin_inverses[k];
    }
    debug_assert_eq!(values[PUBLIC_ROWS - 1], THREE);
    let g_value = gate * rows_inverse + pinned;

    // The identity's combination: `(1 + κ) q + κ (x h)` with `κ = d d' / (ζ + d d')` is
    // `(Z x q + d d' x h) / (ζ + d d') = x (d + d' + μ Z g) / (ζ + d d')`.
    let ([_, _], scale) = extension();
    let scale = S::constant(scale);
    let kappa = product * copy_inverse;
    let copy_value = scale * table_scale * t * (d + d_next + mu * z * g_value) * copy_inverse;

    // The witness table's claim on the row's conic ([`witness_conic`]).
    let z1 = conic_a * conic_inverse;
    let [lx, lc, lvy] = witness_weights(t, w[1], rho, z1);
    let opened = lx * x + lc * c + lvy * vy;
    Ok(Reduced {
        roots: [witness_root, table_root],
        oods: [witness_ood, table_ood],
        witness: ([&[rho, z1][..], &u[2..m]].concat(), opened * middle),
        wiring: (u[..m].to_vec(), next * wiring_scale),
        copy: (copy_point(&u, kappa), copy_value),
    })
}

/// The proof as the field verifier reads it.
pub struct Stream<'a> {
    pub chain: VerifierChain<'a>,
    pub statement: Statement,
}

impl Channel<F192> for Stream<'_> {
    fn statement(&mut self) -> [F192; PUBLIC_WORDS] {
        self.statement.words().map(F192::from)
    }

    fn next_root(&mut self) -> Result<[F192; 2], TranscriptError> {
        self.chain.next_root()
    }

    fn next(&mut self) -> Result<F192, TranscriptError> {
        self.chain.next()
    }

    fn sample(&mut self) -> F192 {
        self.chain.sample()
    }

    fn finish(&mut self) -> Result<(), TranscriptError> {
        self.chain.finish()
    }
}

/// Verify a proof of `statement` against the circuit committed as `index`, down to the two commitments it names
/// and three claims: it holds if every claim holds on its commitment (one opening a claim, [`verify_openings`]).
pub fn verify(
    index: &Commitment,
    statement: &Statement,
    proof: &Proof,
    log_rows: usize,
) -> Result<(Commitments, Claims), VerifyError> {
    if !supported(log_rows) {
        return Err(VerifyError::Shape);
    }
    let mut stream = Stream {
        chain: VerifierChain::new(&label(index, statement), proof),
        statement: *statement,
    };
    let reduced = reduce(&mut stream, log_rows)?;
    let mut commitments = [Commitment {
        root: [0; 32],
        ood: F192::ZERO,
    }; 2];
    for (c, (root, &ood)) in commitments.iter_mut().zip(reduced.roots.iter().zip(&reduced.oods)) {
        *c = Commitment {
            root: halves_root(root).map_err(VerifyError::Transcript)?,
            ood,
        };
    }
    let [witness, table] = commitments;
    let claim = |(point, value)| Claim { point, value };
    Ok((
        Commitments { witness, table },
        Claims {
            witness: claim(reduced.witness),
            wiring: claim(reduced.wiring),
            copy: claim(reduced.copy),
        },
    ))
}

/// The openings of a proof's three claims, in the order of [`Claims::all`].
pub struct Openings(pub [opening::Proof; 3]);

/// Open a proof's `claims` on the tables it committed. The wiring's opening is about public data: anyone can make
/// it; the index's kept codeword ([`Index::commit`]) serves it and is kept for the next proof's.
pub fn open(tables: &Tables, claims: &Claims, index: &Committed) -> Openings {
    let span = || tracing::info_span!("Open");
    Openings([
        span().in_scope(|| opening::open(&tables.witness, &claims.witness, Codeword::Free)),
        span().in_scope(|| opening::open(index, &claims.wiring, Codeword::Keep)),
        span().in_scope(|| opening::open(&tables.table, &claims.copy, Codeword::Free)),
    ])
}

/// A fingerprint of a proof and its openings: the Keccak-256 of every scalar, row word and digest they carry,
/// each list after its length. Two provers that agree on it made the same proof.
pub fn digest(proof: &Proof, openings: &Openings) -> Hash {
    let mut bytes = vec![];
    let scalars = |bytes: &mut Vec<u8>, xs: &[F192]| {
        bytes.extend_from_slice(&(xs.len() as u64).to_le_bytes());
        for x in xs {
            for limb in [x.c0, x.c1, x.c2] {
                bytes.extend_from_slice(&limb.to_le_bytes());
            }
        }
    };
    scalars(&mut bytes, &proof.stream);
    for opening in &openings.0 {
        scalars(&mut bytes, &opening.stream);
        bytes.extend_from_slice(&(opening.merkle.len() as u64).to_le_bytes());
        for paths in &opening.merkle {
            bytes.extend_from_slice(&(paths.leaf_data.len() as u64).to_le_bytes());
            for row in &paths.leaf_data {
                bytes.extend_from_slice(&(row.len() as u64).to_le_bytes());
                row.iter()
                    .for_each(|word| bytes.extend_from_slice(&word.0.to_le_bytes()));
            }
            bytes.extend_from_slice(&(paths.sibling_hashes.len() as u64).to_le_bytes());
            paths
                .sibling_hashes
                .iter()
                .for_each(|hash| bytes.extend_from_slice(hash));
        }
    }
    primitives::hash::hash(&bytes)
}

/// Check the openings of the three claims against the commitments they name.
pub fn verify_openings(
    log_rows: usize,
    index: &Commitment,
    commitments: &Commitments,
    claims: &Claims,
    openings: &Openings,
) -> Result<(), verifier::VerifierError> {
    if !supported(log_rows) {
        return Err(verifier::VerifierError::WhirShape);
    }
    for ((on, claim), proof) in claims.on(index, commitments).into_iter().zip(&openings.0) {
        opening::verify(&on, claim, proof)?;
    }
    Ok(())
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::circuit::{Builder, Src, public_words};
    use cheat::Cheat;
    use primitives::test_rng::Rng;

    /// The tests' cheating prover: [`prove_with_randomness`] with a bad witness's errors absorbed, by the hooks it
    /// calls ([`cheat::absorb`], [`cheat::spill`]) while [`cheat::with`] sets how.
    pub(crate) mod cheat {
        use std::cell::Cell;

        use super::super::*;

        /// What the prover does with a sum that is not zero, as a cheating prover would. It sets the sum's polynomial
        /// on the cells to `1/d + 1/d' + μ e / (d d')`, `e` the gates' and the pins' errors times `Z / Z_R` and `Z /
        /// Z_P` there, so that the quotient is a polynomial whatever the witness; the sum over the cells is then not
        /// zero but for a witness, so `x h`'s low part has a coefficient `n`, which the table's digit 0 cannot hold
        /// (`absorbed_errors_fail_the_copy_claim`).
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub(crate) enum Cheat {
            /// The honest prover.
            Honest,
            /// The errors absorbed, `x h`'s coefficient `n` dropped.
            Absorb,
            /// The errors absorbed, `x h`'s coefficient `n` added to digit 1's first word (read through `ζ`, not `Z`).
            AbsorbSpill,
            /// The errors absorbed, then the sum over the cells made zero at one cell, whose value the identity then
            /// misses.
            AbsorbBalance,
        }

        thread_local! {
            static HOW: Cell<Cheat> = const { Cell::new(Cheat::Honest) };
        }

        /// `f` with the prover cheating `how`.
        pub(crate) fn with<R>(how: Cheat, f: impl FnOnce() -> R) -> R {
            HOW.set(how);
            let out = f();
            HOW.set(Cheat::Honest);
            out
        }

        /// The errors absorbed into `h`'s values on the cells, `h` its three limbs.
        pub(crate) fn absorb(
            circuit: &Circuit,
            statement: &Statement,
            cells: &[F64],
            [alpha, beta_, mu]: [F192; 3],
            mut h: [&mut [F64]; 3],
        ) {
            let how = HOW.get();
            let m = cell_vars(circuit.log_rows);
            let n = 1usize << m;
            if how != Cheat::Honest {
                // `e` at a row's first cell: the gate times `Z / Z_R = Z' / Z_R'` there, the linearized polynomials'
                // linear coefficients `1` and `Σ τ`; at pin `k`: `w + v_k` times `Z / Z_P = λ_k`.
                let row_weight = row_vanishing(m).iter().fold(F64::ZERO, |acc, &t| acc + t).inv();
                let (_, lambda) = pins();
                let values = anchor_values(&statement.words());
                let mut errors: Vec<(usize, F64)> = (0..n / 4)
                    .map(|r| (4 * r, gate(std::array::from_fn(|c| cells[4 * r + c])) * row_weight))
                    .collect();
                errors.extend((0..PUBLIC_ROWS).map(|k| (anchor_cell(k), (cells[anchor_cell(k)] + values[k]) * lambda[k])));
                for (x, e) in errors.into_iter().filter(|(_, e)| !e.is_zero()) {
                    let w = F192::from(cells[x]);
                    let d = alpha + w + beta_.mul_base(point(x));
                    let d_next = alpha + w + beta_.mul_base(point(circuit.sigma[x] as usize));
                    let add = mu.mul_base(e) * (d * d_next).inv();
                    for (h, c) in h.iter_mut().zip([add.c0, add.c1, add.c2]) {
                        h[x] += F64(c);
                    }
                }
            }
            if how == Cheat::AbsorbBalance {
                for h in h.iter_mut() {
                    let sum = h.iter().fold(F64::ZERO, |acc, &v| acc + v);
                    h[n / 2] += sum;
                }
            }
        }

        /// The overflow of `x h`'s low part, spilled into the blinding or dropped.
        pub(crate) fn spill(overflow: [F64; 3]) -> [F64; 3] {
            if HOW.get() == Cheat::AbsorbSpill { overflow } else { [F64::ZERO; 3] }
        }
    }

    /// A size the commitments do not take is rejected, not a panic: the verifiers return an error before reading.
    #[test]
    fn unsupported_sizes_are_rejected() {
        let statement = Statement {
            y: [1; 32],
            root: [2; 32],
        };
        let proof = Proof {
            stream: vec![F192::ZERO; 9],
        };
        let index = Commitment {
            root: [0; 32],
            ood: F192::ZERO,
        };
        for log_rows in [0, MIN_LOG_ROWS - 1, MAX_LOG_ROWS + 1, 40] {
            assert!(!supported(log_rows));
            assert_eq!(verify(&index, &statement, &proof, log_rows), Err(VerifyError::Shape));
        }
        assert!((MIN_LOG_ROWS..=MAX_LOG_ROWS).all(supported));
        for log_rows in MIN_LOG_ROWS..=MAX_LOG_ROWS {
            assert!(table_vars(log_rows).iter().all(|&n| (opening::MIN_VARIABLES..=opening::MAX_VARIABLES).contains(&n)));
        }
    }

    /// A small circuit with the membership statement's shape: `root` is a Keccak-256 of `y`, the input.
    pub(crate) fn toy() -> Circuit {
        let mut b = Builder::new();
        let x: Vec<Src> = (0..256).map(|_| b.input()).collect();
        let digest = b.keccak256_64(&[&x[..], &x[..]].concat());
        b.finish(17, &public_words(&x, &digest))
    }

    pub(crate) fn toy_statement(x: &[u8; 32]) -> Statement {
        Statement {
            y: *x,
            root: crate::statement::pair(x, x),
        }
    }

    pub(crate) fn toy_cells(circuit: &Circuit, x: &[u8; 32]) -> Vec<F64> {
        let inputs: Vec<bool> = (0..256).map(|i| (x[i / 8] >> (i % 8)) & 1 == 1).collect();
        circuit.cells(&inputs)
    }

    fn seed(rng: &mut Rng) -> [u8; 32] {
        std::array::from_fn(|_| rng.next_u8())
    }

    fn truth(index: &Index, proved: &Proved) -> [bool; 3] {
        let words = [proved.tables.witness.words(), index.wiring(), proved.tables.table.words()];
        proved.claims.all().map(|(k, claim)| opening::evaluate(words[k], &claim.point) == claim.value)
    }

    /// The prover's output, pinned: the proof and its three openings on the toy circuit, so a change to how the
    /// prover computes cannot change a byte of what it proves. (Before the sum's claim left, with four claims, the pin
    /// was `c9938962…`; with six claims on four commitments, `114bb485…`; before the EIP's PCS claims, `8e39cf6a…`.)
    #[test]
    fn proofs_are_pinned() {
        let mut rng = Rng::new(0x1D);
        let circuit = toy();
        let index = Index::new(&circuit);
        let index_committed = index.commit();
        let commitment = Commitment::of(index_committed);
        let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
        let statement = toy_statement(&x);
        let cells = toy_cells(&circuit, &x);
        let randomness = Randomness::derive(&seed(&mut rng), &commitment, &statement, &cells);
        let proved = prove_with_randomness(&circuit, &index, &commitment, &statement, &cells, &randomness);
        let openings = open(&proved.tables, &proved.claims, index_committed);
        let hex: String = digest(&proved.proof, &openings)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(hex, "5b7e5aeb6aa63efa7e23b5ebce6c36d668e90d319f2d184286ecf6201a18a865");
    }

    /// The polynomials of `table`'s kind `kind`, limb `limb`, its two digits.
    fn digits(words: &[F64], kind: usize, limb: usize, n: usize) -> (&[F64], &[F64]) {
        words[table_slot(kind, limb, n)..table_slot(kind, limb, n) + 2 * n].split_at(n)
    }

    /// `F(r)` in the novel basis, `f` its coefficients.
    fn novel(f: &[F64], r: F192) -> F192 {
        let digits: Vec<F192> = std::iter::successors(Some(r), |&w| Some(w * w + w))
            .take(f.len().trailing_zeros() as usize)
            .collect();
        evaluate_interleaved(f, 1, &digits)[0]
    }

    /// The quotient table holds what [`table_slot`] says, for a witness: `x h`'s digit 0 without a constant term and
    /// of degree `n − 1` at most, which is the sum over the cells being zero (`h`'s top coefficient zero), the blinding
    /// in its digit 1 and nothing after; `q`'s two digits full; the empty limbs empty; and the table read through
    /// `ζ = Z x` is the identity's `q` and `x h` at a random point.
    #[test]
    fn the_quotient_table_is_laid_out() {
        let mut rng = Rng::new(0x7A);
        let circuit = toy();
        let index = Index::new(&circuit);
        let commitment = Commitment::of(index.commit());
        let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
        let statement = toy_statement(&x);
        let cells = toy_cells(&circuit, &x);
        let proved = prove(&circuit, &index, &commitment, &statement, &cells);
        let n = 1 << cell_vars(circuit.log_rows);
        // The wiring's top coefficient is a permutation's, zero; its coefficient `n − 2` is not, which makes `γ` a
        // nonzero polynomial in `α`, so that the prover can solve for `b_2` but at one value of `α`.
        assert!(index.wiring()[n - 1].is_zero() && !index.wiring()[n - 2].is_zero());
        // The committed words are the table's up to its last nonzero lane: the rest zero.
        let mut words = proved.tables.table.words().to_vec();
        assert!(words.len() <= 16 * n);
        words.resize(16 * n, F64::ZERO);
        for kind in 0..2 {
            let (low, high) = digits(&words, kind, 3, n);
            assert!(low.iter().chain(high).all(|w| w.is_zero()), "limb 3 of kind {kind}");
        }
        for limb in 0..3 {
            let (b0, b1) = digits(&words, 1, limb, n);
            assert!(b0[0].is_zero(), "x h has no constant term, limb {limb}");
            assert!(b1[..H_BLIND].iter().all(|w| !w.is_zero()));
            assert!(b1[H_BLIND..].iter().all(|w| w.is_zero()));
            let (a0, a1) = digits(&words, 0, limb, n);
            assert!(a0[n - 64..].iter().chain(&a1[n - 64..]).any(|w| !w.is_zero()), "q fills its digits");
        }
    }

    /// [`mul_x`] and [`div_x`] are the product by `x` and its inverse in the novel basis, at random points; the
    /// remainder is the polynomial's value at 0; and `X_n / x = Σ_(j < n) X_j`.
    #[test]
    fn products_by_x_in_the_novel_basis() {
        let mut rng = Rng::new(0xD1);
        for k in [1, 2, 3, 6, 11] {
            let len = 1usize << k;
            let mut f: Vec<F64> = (0..len).map(|_| F64(rng.next_u64())).collect();
            let mut g = vec![F64::ZERO; len];
            let top = mul_x(&f, &mut g);
            let r = F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64());
            let x_n = std::iter::successors(Some(r), |&w| Some(w * w + w)).nth(k).unwrap();
            assert_eq!(novel(&g, r) + x_n * F192::from(top), r * novel(&f, r), "x F, 2^{k}");
            // Back: exactly when the top coefficient is zero; with a remainder `G(0)` otherwise.
            f[len - 1] = F64::ZERO;
            mul_x(&f, &mut g);
            let c = F64(rng.next_u64());
            g[0] += c;
            let mut back = vec![F64::ZERO; len];
            assert_eq!(div_x(&g, &mut back), c);
            assert_eq!(back, f, "x F / x, 2^{k}");
            let mut x_n_coefficients = vec![F64::ZERO; 2 * len];
            x_n_coefficients[len] = F64::ONE;
            let mut quotient = vec![F64::ZERO; 2 * len];
            assert!(div_x(&x_n_coefficients, &mut quotient).is_zero());
            assert!(quotient[..len].iter().all(|&q| q == F64::ONE) && quotient[len..].iter().all(|q| q.is_zero()));
        }
    }

    /// The witness claim's weights: at random `t`, `ρ` and row polynomials' values `a`, the claim point's weights
    /// `e = (1 + ρ, ρ) ⊗ (1 + z_1, z_1)` are `λ · (X, C, V + Y)` as linear forms of `a`; as `ρ` varies they span the
    /// three forms (three points of the conic are independent), so the claim binds the three values.
    #[test]
    fn the_witness_claim_is_on_the_conic() {
        let mut rng = Rng::new(0xC0);
        let random = |rng: &mut Rng| F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64());
        for _ in 0..8 {
            let t = random(&mut rng);
            let omega = t * t + t;
            let a: [F192; 4] = std::array::from_fn(|_| random(&mut rng));
            let row = row_values(a, t, omega);
            let mut weights = vec![];
            for _ in 0..3 {
                let rho = random(&mut rng);
                let (ca, cb) = witness_conic(t, omega, rho);
                let z1 = ca * (ca + cb).inv();
                let lambda = witness_weights(t, omega, rho, z1);
                let e = [(F192::ONE + rho) * (F192::ONE + z1), rho * (F192::ONE + z1), (F192::ONE + rho) * z1, rho * z1];
                let direct = (0..4).fold(F192::ZERO, |acc, j| acc + e[j] * a[j]);
                assert_eq!(direct, (0..3).fold(F192::ZERO, |acc, i| acc + lambda[i] * row[i]));
                weights.push(lambda);
            }
            // The three weight vectors are independent: their determinant is not zero.
            let [p, q, r] = [weights[0], weights[1], weights[2]];
            let det = p[0] * (q[1] * r[2] + q[2] * r[1]) + p[1] * (q[0] * r[2] + q[2] * r[0]) + p[2] * (q[0] * r[1] + q[1] * r[0]);
            assert!(!det.is_zero());
        }
    }

    /// On a small circuit: an honest proof leaves three true claims that open, and a witness that breaks one gate,
    /// one copy, one input's range or one public value leaves a false one; and a revealed row value changed, with
    /// the stream's other scalars, leaves a false witness claim.
    #[test]
    fn claims_hold_exactly_for_a_witness() {
        let mut rng = Rng::new(0x51);
        let circuit = toy();
        let index = Index::new(&circuit);
        let index_committed = index.commit();
        let commitment = Commitment::of(index_committed);
        let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
        let statement = toy_statement(&x);
        let cells = toy_cells(&circuit, &x);
        for r in 0..cells.len() / 4 {
            assert!(gate(std::array::from_fn::<_, 4, _>(|c| cells[4 * r + c])).is_zero());
        }
        for (i, &next) in circuit.sigma.iter().enumerate() {
            assert_eq!(cells[i], cells[next as usize]);
        }
        assert!(circuit.errors_have_their_own_poles());

        let proved = prove(&circuit, &index, &commitment, &statement, &cells);
        assert_eq!(truth(&index, &proved), [true; 3]);
        assert_eq!(proved.proof.stream.len(), stream::LEN);
        let s = &proved.proof.stream;
        let root = |at: usize| halves_root(&[s[at], s[at + 1]]);
        assert_eq!(root(stream::WITNESS_ROOT), Ok(proved.commitments.witness.root));
        assert_eq!(root(stream::TABLE_ROOT), Ok(proved.commitments.table.root));
        assert_eq!([s[stream::WITNESS_OOD], s[stream::TABLE_OOD]], [proved.commitments.witness.ood, proved.commitments.table.ood]);
        let openings = open(&proved.tables, &proved.claims, index_committed);
        assert_eq!(
            verify_openings(circuit.log_rows, &commitment, &proved.commitments, &proved.claims, &openings),
            Ok(())
        );
        // An opening of one claim does not open another.
        let mut swapped = Openings(openings.0.clone());
        swapped.0.swap(0, 1);
        assert!(verify_openings(circuit.log_rows, &commitment, &proved.commitments, &proved.claims, &swapped).is_err());

        // A row value changed: the transcript replays with the change, and the witness claim no longer holds.
        for at in stream::ROW_VALUES..stream::ROW_VALUES + 3 {
            let mut stream = proved.proof.stream.clone();
            stream[at] += F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64());
            let proof = Proof { stream };
            let (_, claims) = verify(&commitment, &statement, &proof, circuit.log_rows).expect("a reduction");
            assert!(opening::evaluate(proved.tables.witness.words(), &claims.witness.point) != claims.witness.value);
        }

        // A proof made for one statement, read against another.
        let mut other = statement;
        other.root[3] ^= 0x10;
        let wrong = prove(&circuit, &index, &commitment, &other, &cells);
        assert!(truth(&index, &wrong).contains(&false));

        let input_row = PUBLIC_ROWS + 5;
        let some_row = PUBLIC_ROWS + 256 + 9000;
        let cycle_of = |start: usize| -> Vec<usize> {
            let mut cycle = vec![start];
            let mut i = circuit.sigma[start] as usize;
            while i != start {
                cycle.push(i);
                i = circuit.sigma[i] as usize;
            }
            cycle
        };
        type Tamper<'a> = &'a dyn Fn(&mut Vec<F64>);
        let cases: [(&str, Tamper); 5] = [
            // A row's output alone.
            ("gate", &|cells| cells[4 * some_row + 3] += F64::ONE),
            // An input that is not a bit, wherever it is read.
            ("range", &|cells| {
                for i in cycle_of(4 * input_row + 3) {
                    cells[i] = F64(0x1234_5678);
                }
            }),
            // The constant one, read as zero everywhere.
            ("one", &|cells| {
                for i in cycle_of(anchor_cell(PUBLIC_WORDS + 1)) {
                    cells[i] = F64::ZERO;
                }
            }),
            // A public word, changed on its whole cycle (the packing row that makes it no longer holds).
            ("public", &|cells| {
                for i in cycle_of(anchor_cell(2)) {
                    cells[i] += F64::ONE;
                }
            }),
            // A reader that departs from what it reads.
            ("copy", &|cells| cells[4 * some_row] += F64::ONE),
        ];
        for (name, tamper) in cases {
            let mut bad = cells.clone();
            tamper(&mut bad);
            let truth = truth(&index, &prove(&circuit, &index, &commitment, &statement, &bad));
            assert_eq!(truth, [true, true, false], "{name}");
        }
    }

    /// The cycle of `start`, from it.
    fn cycle_of(circuit: &Circuit, start: usize) -> Vec<usize> {
        let mut cycle = vec![start];
        let mut i = circuit.sigma[start] as usize;
        while i != start {
            cycle.push(i);
            i = circuit.sigma[i] as usize;
        }
        cycle
    }

    /// A cheating prover that absorbs a bad witness's errors into the sum's polynomial after `μ` ([`cheat`]): the
    /// witness's and the wiring's claims hold, and the copy claim rejects, since the sum over the cells is then not
    /// zero and `x h` has a coefficient `n` that the table's digit 0 cannot hold, dropped ([`Cheat::Absorb`]) or put in
    /// digit 1 ([`Cheat::AbsorbSpill`]), or the sum is made zero at one cell, which the identity then misses
    /// ([`Cheat::AbsorbBalance`]): for a gate's error, a pin's and a copy's, and for two equal gate errors that
    /// would cancel on a 2-cycle. As a negative control, on the toy circuit with two rows' `X` cells made a cycle of
    /// their own (which `errors_have_their_own_poles` rejects, and so [`Index::new`]), the same two errors cancel and
    /// every claim holds: the check has teeth.
    #[test]
    fn absorbed_errors_fail_the_copy_claim() {
        let mut rng = Rng::new(0xAB5);
        let circuit = toy();
        let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
        let statement = toy_statement(&x);
        let cells = toy_cells(&circuit, &x);
        let s = seed(&mut rng);
        let cheat = |circuit: &Circuit, index: &Index, cells: &[F64], how: Cheat| {
            let commitment = Commitment::of(index.commit());
            let randomness = Randomness::derive(&s, &commitment, &statement, cells);
            truth(index, &cheat::with(how, || prove_with_randomness(circuit, index, &commitment, &statement, cells, &randomness)))
        };
        let index = Index::new(&circuit);
        const CHEATS: [Cheat; 3] = [Cheat::Absorb, Cheat::AbsorbSpill, Cheat::AbsorbBalance];
        for how in CHEATS {
            assert_eq!(cheat(&circuit, &index, &cells, how), [true; 3], "a witness has no errors to absorb");
        }

        let some_row = PUBLIC_ROWS + 256 + 9000;
        let (r1, r2) = (circuit.used_rows + 1, circuit.used_rows + 2);
        assert!(circuit.rows[r1] == circuit.rows[r2] && circuit.rows[r1].x == Src::Zero, "two idle rows");
        let both = |cells: &mut Vec<F64>| {
            cells[4 * r1 + 3] += F64::ONE;
            cells[4 * r2 + 3] += F64::ONE;
        };
        type Tamper<'a> = &'a dyn Fn(&mut Vec<F64>);
        let cases: [(&str, Tamper); 5] = [
            // A row's output and every reader of it: the copies hold, the row's gate (and its readers') do not.
            ("gate", &|cells| cycle_of(&circuit, 4 * some_row + 3).into_iter().for_each(|i| cells[i] += F64::ONE)),
            // A public word on its whole cycle: its pin fails (and the packing row that makes it).
            ("pin", &|cells| cycle_of(&circuit, anchor_cell(2)).into_iter().for_each(|i| cells[i] += F64::ONE)),
            // A reader that departs from what it reads.
            ("copy", &|cells| cells[4 * some_row] += F64::ONE),
            // A copy alone: a row's `Y` and `V` moved together, its gate (`V = Y + C + X·C`) holding, its `Y` off its
            // source and its `V` off its readers: no error for `h` to absorb, the logarithmic derivatives' sum off.
            ("copy only", &|cells| {
                cells[4 * some_row + 1] += F64::ONE;
                cells[4 * some_row + 3] += F64::ONE;
            }),
            // Two idle rows' outputs, the same error twice.
            ("two gates", &both),
        ];
        for (name, tamper) in cases {
            let mut bad = cells.clone();
            tamper(&mut bad);
            for how in CHEATS {
                assert_eq!(cheat(&circuit, &index, &bad, how), [true, true, false], "{name}, {how:?}");
            }
        }

        // The negative control: the two idle rows' `X` cells, out of the zero's cycle, a cycle of their own.
        let mut broken = toy();
        for x in [4 * r1, 4 * r2] {
            let before = (0..broken.sigma.len()).find(|&i| broken.sigma[i] as usize == x).unwrap();
            broken.sigma[before] = broken.sigma[x];
        }
        (broken.sigma[4 * r1], broken.sigma[4 * r2]) = ((4 * r2) as u32, (4 * r1) as u32);
        assert!(!broken.errors_have_their_own_poles());
        let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| Index::new(&broken)));
        assert!(refused.is_err(), "the index refuses the circuit");
        // The two `X` cells 5 (an idle row's gate is then `V = 0 + 0 + 5·0`).
        let mut bad = cells.clone();
        (bad[4 * r1], bad[4 * r2]) = (F64(5), F64(5));
        let unchecked = Index::new_unchecked(&broken);
        assert_eq!(cheat(&broken, &unchecked, &bad, Cheat::Absorb), [true; 3], "a witness of the broken circuit");
        both(&mut bad);
        assert_eq!(cheat(&broken, &unchecked, &bad, Cheat::Absorb), [true; 3], "the two errors cancel");
    }

    /// A committed table whose top lane is zero holds fewer words (`opening::commit` leaves trailing zero lanes out):
    /// the interleaved evaluation of the witness's row polynomials, and the claim on it, are the whole table's.
    #[test]
    fn a_trimmed_witness_table_evaluates_as_the_whole() {
        let mut rng = Rng::new(0x7E1);
        let m = 15;
        let n = 1usize << m;
        let mut table: Vec<F64> = (0..n).map(|_| F64(rng.next_u64())).collect();
        table[n - n / 64..].fill(F64::ZERO);
        let committed = opening::commit(table.clone(), false);
        assert!(committed.words().len() < n, "the zero lane is left out");
        let t = F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64());
        let digits: Vec<F192> = std::iter::successors(Some(t), |&w| Some(w * w + w)).take(m).collect();
        assert_eq!(
            evaluate_interleaved(committed.words(), 4, &digits[2..m]),
            evaluate_interleaved(&table, 4, &digits[2..m])
        );
        assert_eq!(evaluate_interleaved(committed.words(), 1, &digits), evaluate_interleaved(&table, 1, &digits));
        let point: Vec<F192> = (0..m).map(|_| F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64())).collect();
        assert_eq!(opening::evaluate(committed.words(), &point), opening::evaluate(&table, &point));
    }

    /// [`Randomness::derive`] is a function of the seed, the circuit's commitment, the statement and the cells: the
    /// same ones give the same randomness, and another seed, commitment or statement, one cell changed or one cell
    /// fewer give words that share nothing with it.
    #[test]
    fn derived_randomness_binds_the_statement_and_the_witness() {
        let mut rng = Rng::new(0xD5);
        let cells: Vec<F64> = (0..(1 << 14) + 5).map(|_| F64(rng.next_u64())).collect();
        let statement = toy_statement(&[3; 32]);
        let s = seed(&mut rng);
        let index = Commitment {
            root: [7; 32],
            ood: F192::ONE,
        };
        let flat = |r: &Randomness| [&r.rows[..], r.blind.as_flattened()].concat();
        let base = flat(&Randomness::derive(&s, &index, &statement, &cells));
        assert_eq!(base, flat(&Randomness::derive(&s, &index, &statement, &cells)));
        assert!((1..base.len()).all(|k| !base[..k].contains(&base[k])), "distinct words");
        let mut other_cells = cells.clone();
        other_cells[9000].0 ^= 1;
        let mut other_statement = statement;
        other_statement.y[0] ^= 1;
        let other_index = Commitment { ood: F192::ZERO, ..index };
        let others = [
            Randomness::derive(&seed(&mut rng), &index, &statement, &cells),
            Randomness::derive(&s, &other_index, &statement, &cells),
            Randomness::derive(&s, &index, &other_statement, &cells),
            Randomness::derive(&s, &index, &statement, &other_cells),
            Randomness::derive(&s, &index, &statement, &cells[..cells.len() - 1]),
        ];
        for (k, other) in others.iter().enumerate() {
            let shared = flat(other).iter().filter(|w| base.contains(w)).count();
            assert_eq!(shared, 0, "case {k}");
        }
        assert_ne!(fresh_seed(), fresh_seed(), "the operating system's seeds");
    }
}
