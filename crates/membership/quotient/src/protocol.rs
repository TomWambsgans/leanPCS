// Part of this repository. Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6, crates/flock/src/quotient.rs and crates/flock/src/membership.rs
// (`Scalar`, `Channel`, `VerifyError`): the copy argument is the same but for the gate (`V = X + C + Y·C` on bits,
// degree 2), the public values (pinned cells, not a weighted sum), the gate's quotient (with the pins, checked by a
// claim of its own) and the one quotient table. MIT OR Apache-2.0; see AGENTS.md.
//! The membership statement reduced to four evaluation claims on two commitments by seven field elements and no
//! sumcheck.
//!
//! A multilinear claim at a point built from one field element `t` is a univariate evaluation ([`domain`]),
//! so this is a gate-and-copy argument on an additive subspace: one gate on four cells a row ([`circuit`]),
//! copy constraints as one sum of logarithmic derivatives, the public values as cells pinned by interpolation, and
//! one quotient, in one committed table with the sum's polynomial. No quotient value is sent: the claim on the
//! quotient table is the combination its identity gives. The verifier is [`reduce`], generic in its scalar so that the same code is the
//! EVM contract, and checks nothing but one nonzero product.
//!
//! **The tables** (`m = log_rows + 2`, `n = 2^m` cells): the witness `W` (the cells' polynomial `w`, `m`
//! variables: the four row polynomials interleaved), the circuit's wiring (`m`, public), and the quotient table `T`
//! (`m + 4`, [`table_slot`]): the copy argument's sum polynomial `h` (blinded, `deg < n + 2`) and the one quotient
//! `q` (`deg < 2n`).
//!
//! **The identity**, with `d = α + w + β x`, `d' = α + w + β σ`, `Z = X_n` the cells' vanishing polynomial, and
//! `g = gate / Z_R + (w + v) / Z_P` (`Z_R` vanishing on the rows' first cells, `Z_P` on the
//! [`crate::circuit::PUBLIC_ROWS`] pinned cells, `v` the public values' interpolant on them):
//! `Z q + d d' h = d + d' + μ Z g`, and `Σ_cells h = 0`, `μ` a challenge drawn after `W` and before `T`. On a cell
//! the identity sets `h` to the logarithmic derivative plus `μ` times the gate's or the pin's error over `d d'`; the
//! sum then vanishes, at random `α, β, μ`, only if the copies, the gates and the pins all hold: no cycle of the
//! wiring lies within the rows' first cells and the pins but a free cell's own (the poles of `1 / (d d')` at the
//! first cell of each run of them on a cycle are the error's alone; `PERF_GAS.md`).
//!
//! **The claims**: `W` at the row polynomials' point (four values `a_j` combined by `ρ`), the wiring at `t`, `T` at
//! `t` with the identity's combination of `q` and `h` ([`copy_point`]), and `T` at `h`'s top coefficient
//! ([`sum_point`]), whose value is zero.
//!
//! [`domain`]: crate::domain
//! [`circuit`]: crate::circuit

use std::ops::{Add, Mul};
use std::sync::OnceLock;

use fiat_shamir::merkle::Hash;
use primitives::field::{F64, F192, F192Unreduced};

use crate::circuit::{Circuit, PUBLIC_ROWS, PUBLIC_WORDS, RANDOM_WORDS, THREE, anchor_cell, anchor_values};
use crate::domain::{self, beta, chain, point, row_vanishing};
use crate::ntt::{self, Ex8, Kx8};
use crate::opening::{self, Claim, Commitment, Committed};
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
pub const NAME: &[u8; 16] = b"pcs-quotient-kc2";

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

/// The coefficients past `2^m` that blind the sum's polynomial `h`, per limb: `h + X_{2^m}·b_e`, which `h` keeps on
/// the cells (`X_{2^m}` vanishes there) and which makes the quotient table's out-of-domain answer uniform
/// (`HIDING.md`). Two, so that `h d d'` stays below degree `3 n` and `q` below `2 n`.
pub const H_BLIND: usize = 2;

/// The fewest rows: below `2^13` the witness and wiring tables (`m` variables) are smaller than the `2^15` words
/// WHIR commits.
pub const MIN_LOG_ROWS: usize = 13;

/// The most rows: above `2^22` rows the quotient table (`m + 4` variables) is more than the `2^28` words leanVM's
/// WHIR commits.
pub const MAX_LOG_ROWS: usize = 22;

/// The most rows the reduction alone takes (its domain's basis): circuits past [`MAX_LOG_ROWS`] reduce to claims on
/// tables leanVM's WHIR cannot commit, for a block whose openings take larger tables ([`verify_reduction`]).
pub const MAX_REDUCTION_LOG_ROWS: usize = domain::EXT_BASIS - 5;

/// Whether the reduction alone takes a circuit of `2^log_rows` rows.
pub fn reduction_supported(log_rows: usize) -> bool {
    (MIN_LOG_ROWS..=MAX_REDUCTION_LOG_ROWS).contains(&log_rows)
}

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
/// a limb's two bits and a kind), each `(kind, limb)` a polynomial of `2 n` coefficients over `K`:
/// - kind 0, limb `e < 3`: limb `e` of the quotient `q`;
/// - kind 1, limb `e < 3`: limb `e` of `h`, its blinding [`H_BLIND`] coefficients past `n`;
/// - limb 3 of either kind: zero.
///
/// A claim at `(u, u_m, y_0, y_1, k)` ([`extension`]'s `y`) reads `(1 + k) q + k h` at `t`, up to the scale of
/// [`extension`] and the multilinear's normalisation, `q` and `h` as `K`-limbs of `E`-polynomials (a limb 3, which a
/// prover may fill, as a fourth limb of weight `Y^3`).
pub fn table_slot(kind: usize, limb: usize, n: usize) -> usize {
    2 * n * (limb + 4 * kind)
}

/// The secret randomness of one proof (`HIDING.md`): the random rows' words ([`Circuit::randomize`]) and the
/// blinding of the sum's polynomial, [`H_BLIND`] coefficients per limb. It must be uniform, secret, and **fresh per
/// proof, never reused**: two proofs that share it let a guessed witness be confirmed. [`prove`] draws its own seed,
/// [`prove_with_seed`] takes one; both derive this from it ([`Randomness::derive`]).
#[derive(Clone)]
pub struct Randomness {
    /// The random rows' words, two a row, in the order of [`Circuit::random_rows`].
    pub rows: [F64; RANDOM_WORDS],
    /// `blind[e][i]`: coefficient `2^m + i` of limb `e` of the sum's polynomial.
    pub blind: [[F64; H_BLIND]; 3],
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
    /// order: the random rows' words, the blinding (`blind[e][i]` word `H_BLIND e + i`). A seed reused for another
    /// witness or another statement gives unrelated randomness; reused for the same ones, it gives the same proof
    /// again. The seed must still be fresh per proof and secret: [`prove`] draws it from the operating system.
    pub fn derive(seed: &[u8; 32], index: &Commitment, statement: &Statement, cells: &[F64]) -> Self {
        let label = label(index, statement);
        let key = primitives::hash::hash(&[KDF_KEY, seed, &label, &cells_digest(cells)].concat());
        const WORDS: usize = RANDOM_WORDS + 3 * H_BLIND;
        let words: Vec<F64> = (0..WORDS.div_ceil(4) as u8)
            .flat_map(|k| {
                let block = primitives::hash::hash(&[KDF_WORDS, &key, &[k]].concat());
                (0..4).map(move |i| F64(u64::from_le_bytes(block[8 * i..8 * i + 8].try_into().unwrap())))
            })
            .collect();
        Self {
            rows: std::array::from_fn(|r| words[r]),
            blind: std::array::from_fn(|e| std::array::from_fn(|i| words[RANDOM_WORDS + H_BLIND * e + i])),
        }
    }
}

/// The cells' digest the key binds: Keccak-256 of its tag, the number of cells, and the digests of their runs of
/// `2^12` cells (each the Keccak-256 of its cells' words, 8 little-endian bytes each), the runs hashed in parallel.
fn cells_digest(cells: &[F64]) -> Hash {
    const RUN: usize = 1 << 12;
    let runs = parallel::map_collect(cells.len().div_ceil(RUN), |r| {
        let run = &cells[r * RUN..cells.len().min((r + 1) * RUN)];
        let bytes: Vec<u8> = run.iter().flat_map(|w| w.0.to_le_bytes()).collect();
        primitives::hash::hash(&bytes)
    });
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
    /// The wiring polynomial's `2^m` coefficients: the committed wiring table.
    pub table: Vec<F64>,
    /// The wiring polynomial's values on the quotients' coset, twice the cells: they depend on the circuit alone,
    /// and every proof reads them.
    sigma_values: Vec<F64>,
}

impl Index {
    pub fn new(circuit: &Circuit) -> Self {
        let mut sigma = parallel::map_collect(circuit.sigma.len(), |i| point(circuit.sigma[i] as usize));
        ntt::coefficients(&mut sigma, F64::ZERO);
        let n = sigma.len();
        let m = n.trailing_zeros() as usize;
        let mut sigma_values = words(2 * n);
        for (k, half) in sigma_values.chunks_exact_mut(n).enumerate() {
            ntt::values_from(&sigma, half, half_offset(coset(m), n, k));
        }
        Self {
            log_rows: circuit.log_rows,
            table: sigma,
            sigma_values,
        }
    }

    /// The circuit's commitment: its wiring table's.
    pub fn commit(&self) -> Committed {
        opening::commit(self.table.clone())
    }

    fn sigma(&self) -> &[F64] {
        &self.table
    }

    fn sigma_values(&self) -> &[F64] {
        &self.sigma_values
    }
}

/// `len` words, every one of which the caller writes before it reads it.
fn words(len: usize) -> Vec<F64> {
    // SAFETY: plain words; the callers write each before reading it.
    unsafe { primitives::uninit_vec(len) }
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
    assert_eq!(coeffs.len(), step << d);
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
        let block = &coeffs[high * run..(high + 1) * run];
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

/// What a proof leaves: four claims, one point each: on the witness table, the circuit's wiring table, and the
/// quotient table at [`copy_point`] and [`sum_point`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claims {
    pub witness: Claim,
    pub wiring: Claim,
    /// The identity's combination of `q` and `h` at `t`.
    pub copy: Claim,
    /// The top coefficient of the sum's polynomial: zero.
    pub sum: Claim,
}

impl Claims {
    /// The claims in the order of [`Openings`], each with the table it is on: `0` the witness, `1` the wiring, `2`
    /// the quotient table.
    pub fn all(&self) -> [(usize, &Claim); 4] {
        [(0, &self.witness), (1, &self.wiring), (2, &self.copy), (2, &self.sum)]
    }
}

/// The two coordinates of the extension over the base field, and the scale of their weights `(1, Y, Y^2, Y^3)`.
pub fn extension() -> ([F192; 2], F192) {
    let (y, y2) = (F192::Y, F192::Y * F192::Y);
    let (d0, d1) = (F192::ONE + y, F192::ONE + y2);
    ([y * d0.inv(), y2 * d1.inv()], (d0 * d1).inv())
}

/// The point of the claim on the quotient table that the identity gives: `t`'s coordinates `u` (`m + 1`: the
/// coefficient's and the digit's), [`extension`]'s two, then `kappa`, which weighs `h` against `q`.
pub fn copy_point<S: Scalar>(u: &[S], kappa: S) -> Vec<S> {
    let ([y0, y1], _) = extension();
    [u, &[S::constant(y0), S::constant(y1), kappa]].concat()
}

/// The point of the claim on the quotient table at the top coefficient of the sum's polynomial: coefficient
/// `2^m - 1` of digit `0`, its limbs weighed by the extension's coordinates, kind 1. Its value is zero.
pub fn sum_point(log_rows: usize) -> Vec<F192> {
    let m = cell_vars(log_rows);
    [&vec![F192::ONE; m][..], &[F192::ZERO], &extension().0, &[F192::ONE]].concat()
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

/// The gate, `V + X + C + Y·C`, which vanishes on a row's cells.
fn gate<T: Copy + Add<Output = T> + Mul<Output = T>>([x, y, c, v]: [T; 4]) -> T {
    v + x + c + y * c
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

impl Tables {
    /// The committed table a claim of [`Claims::all`] is on (`1`, the wiring, is the circuit's).
    pub fn table(&self, k: usize) -> &Committed {
        match k {
            0 => &self.witness,
            2 => &self.table,
            _ => panic!("the wiring table is the index's"),
        }
    }
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
    let mut randomized = cells.to_vec();
    circuit.randomize(&mut randomized, rows);
    let cells = &randomized[..];

    // The witness: the cells' polynomial.
    let span = tracing::info_span!("Witness").entered();
    let mut w_hat = words(n);
    tracing::info_span!("cells to coefficients").in_scope(|| ntt::coefficients_from(cells, &mut w_hat, F64::ZERO));
    let witness = tracing::info_span!("Commit").in_scope(|| opening::commit(w_hat));
    ps.send_root(&witness.root);
    ps.send(witness.ood);
    drop(span);
    let [alpha, beta_, mu] = [(); 3].map(|_| ps.sample());

    // The sum's polynomial on the cells, its coefficients a limb at a time.
    let span = tracing::info_span!("Sum").entered();
    let inner = tracing::info_span!("inverses").entered();
    let mut h_hat: [Vec<F64>; 3] = std::array::from_fn(|_| words(n));
    {
        let [h0, h1, h2] = &mut h_hat;
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
    tracing::info_span!("coefficients").in_scope(|| h_hat.iter_mut().for_each(|h| ntt::coefficients(h, F64::ZERO)));
    drop(span);

    // The quotient, on a coset twice the cells: two cosets of the cells' size, offset by `B(k n)`, written into the
    // quotient table's slots for `q`'s limbs ([`table_slot`]), which hold `h`'s values first.
    let span = tracing::info_span!("Quotients").entered();
    let big = 2 * n;
    let offset = coset(m);
    let mut table = words(16 * n);
    let mut values = words(big);

    // The transforms in two parts where the cells are many: the layers above a leaf a pass over memory each, and
    // each leaf's own layers in the block-wise loop below, around the quotients' values, a block in cache.
    let fused = n >= ntt::LEAF_WORDS;
    let forward = |src: Option<&[F64]>, half: &mut [F64], k: usize| {
        let at = half_offset(offset, n, k);
        match (fused, src) {
            (true, _) => ntt::values_upper(src, half, at),
            (false, Some(src)) => ntt::values_from(src, half, at),
            (false, None) => ntt::values(half, at),
        }
    };
    let inner = tracing::info_span!("witness values").entered();
    for (k, half) in values.chunks_exact_mut(n).enumerate() {
        forward(Some(witness.words()), half, k);
    }
    drop(inner);
    let sigma_values = index.sigma_values();
    let (quotients, rest) = table.split_at_mut(4 * big);
    tracing::info_span!("sum values").in_scope(|| {
        for (limb, column) in quotients[..3 * big].chunks_exact_mut(big).enumerate() {
            for (k, half) in column.chunks_exact_mut(n).enumerate() {
                // `h + X_n b`: the blinding's coefficients, from `n` on, times `X_n`'s value on this half.
                half.copy_from_slice(&h_hat[limb]);
                let scale = top_layer(offset, m, k);
                for (v, &c) in half.iter_mut().zip(&blind[limb]) {
                    *v += scale * c;
                }
                forward(None, half, k);
            }
        }
    });

    let inner = tracing::info_span!("quotient values").entered();
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
    let mu8 = Ex8::splat(mu);
    // The pins: their points, and the public values' interpolant on them.
    let (pin_points, _) = pins();
    let interpolant = pin_interpolant(&anchor_values(&statement.words()));
    // The quotient's values on the `len` points from `base`: `w` the witness's values there, `q` the sum's limbs
    // (overwritten with `q`'s): `(h d d' + d + d') / Z + μ g`, `g` the gates' and pins' quotient.
    let quotient_block = |base: usize, w_values: &[F64], q: [&mut [F64]; 3]| {
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
        let mut gates = Vec::with_capacity(len / 8);
        let mut pinned = Vec::with_capacity(len / 8);
        let mut z_pins = Vec::with_capacity(len / 8);
        for low in (0..len).step_by(8) {
            let i = base + low;
            let x = Kx8::splat(offset + point(i)) + lane_points;
            let w = limb(&w_values[low..]);
            let common = alpha8 + Ex8::from_k(w);
            let d = common + Ex8::splat(beta_.mul_base(offset + point(i))) + beta_points;
            let d_next = common + beta8.mul_k(limb(&sigma_values[i..]));
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
    let block = if fused { ntt::LEAF_WORDS } else { n.min(1 << 11) };
    let w_ptr = parallel::SendPtr(values.as_mut_ptr());
    let q_ptr = parallel::SendPtr(quotients.as_mut_ptr());
    parallel::for_each(big / block, |task| {
        let start = task * block;
        // SAFETY: the words `start..start + block` of each of the four columns are this task's alone.
        let (w, mut q) = unsafe {
            (
                w_ptr.slice(start, block),
                [0, 1, 2].map(|limb| q_ptr.slice(limb * big + start, block)),
            )
        };
        if fused {
            let k = start / n;
            let at = half_offset(offset, n, k);
            ntt::values_leaf(w, start - k * n, n, at);
            q.iter_mut().for_each(|q| ntt::values_leaf(q, start - k * n, n, at));
        }
        {
            let [q0, q1, q2] = &mut q;
            quotient_block(start, w, [&mut q0[..], &mut q1[..], &mut q2[..]]);
        }
        if fused {
            q.iter_mut().for_each(|q| ntt::coefficients_leaf(q, start, big, offset));
        }
    });
    drop(inner);
    let backward = |column: &mut [F64]| {
        if fused {
            ntt::coefficients_upper(column, offset)
        } else {
            ntt::coefficients(column, offset)
        }
    };
    tracing::info_span!("quotient coefficients")
        .in_scope(|| quotients[..3 * big].chunks_exact_mut(big).for_each(backward));
    drop(values);

    // `q`'s empty limb; `h`'s limbs with their blinding, then the empty limb.
    let inner = tracing::info_span!("tables").entered();
    quotients[3 * big..].fill(F64::ZERO);
    for (limb, h) in h_hat.iter().enumerate() {
        let slot = &mut rest[limb * big..(limb + 1) * big];
        slot[..n].copy_from_slice(h);
        slot[n..n + H_BLIND].copy_from_slice(&blind[limb]);
        slot[n + H_BLIND..].fill(F64::ZERO);
    }
    rest[3 * big..].fill(F64::ZERO);
    drop(h_hat);
    drop(inner);
    let table = tracing::info_span!("Commit").in_scope(|| opening::commit(table));
    ps.send_root(&table.root);
    ps.send(table.ood);
    drop(span);

    let t = ps.sample();
    let digits: Vec<F192> = std::iter::successors(Some(t), |&w| Some(w * w + w)).take(m).collect();
    let a = evaluate_interleaved(witness.words(), 4, &digits[2..m]);
    a.iter().for_each(|&x| ps.send(x));
    let next = evaluate_interleaved(index.sigma(), 1, &digits[..m])[0];
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
/// witness table, the quotient table), and the claims as a point and a value.
pub struct Reduced<S> {
    pub roots: [[S; 2]; 2],
    pub oods: [S; 2],
    pub witness: (Vec<S>, S),
    pub wiring: (Vec<S>, S),
    pub copy: (Vec<S>, S),
    /// The value of the claim at [`sum_point`]: zero.
    pub sum: S,
}

/// The verifier, on any [`Scalar`]: the proof read from `channel`, down to the commitments it names and the four
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
    let mut a = [t; 4];
    for value in &mut a {
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

    // The four cells of the row of `t`, and its gate.
    let theta = beta()[1];
    let cell = |shift: F64, second: bool| {
        let (first, second) = (t + base(shift), if second { w[1] + one } else { w[1] });
        a[0] + first * a[1] + second * (a[2] + first * a[3])
    };
    let row = [
        cell(F64::ZERO, false),
        cell(F64::ONE, false),
        cell(theta, true),
        cell(theta + F64::ONE, true),
    ];
    let x = row[0];
    let gate = gate(row);

    let tau = row_vanishing(m);
    let rows = (0..m - 1).fold(S::constant(F192::ZERO), |acc, k| acc + base(tau[k]) * w[k]);
    let (d, d_next) = (alpha + x + beta_ * t, alpha + x + beta_ * next);
    let product = d * d_next;
    let z = w[m];
    let (pin_points, lambda) = pins();

    // One inversion: of every `1 + w_k`, of the copy identity's `Z + d d'`, of the rows' polynomial, and of every
    // `t + p_k`.
    let mut denominators: Vec<S> = w.iter().map(|&w| one + w).collect();
    denominators.extend([z + product, rows]);
    denominators.extend(pin_points.iter().map(|&p| t + base(p)));
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
    let u: Vec<S> = (0..m + 1).map(|k| w[k] * inverses[k]).collect();
    let (copy_inverse, rows_inverse) = (inverses[m + 1], inverses[m + 2]);
    let pin_inverses = &inverses[m + 3..];
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

    // The identity's combination: `(1 + κ) q + κ h` with `κ = d d' / (Z + d d')` is
    // `(Z q + d d' h) / (Z + d d') = (d + d' + μ Z g) / (Z + d d')`.
    let ([_, _], scale) = extension();
    let scale = S::constant(scale);
    let kappa = product * copy_inverse;
    let copy_value = scale * table_scale * (d + d_next + mu * z * g_value) * copy_inverse;

    let rho2 = rho * rho;
    let opened = (one + rho2) * (a[0] + rho * (a[0] + a[1])) + rho2 * (a[2] + rho * (a[2] + a[3]));
    Ok(Reduced {
        roots: [witness_root, table_root],
        oods: [witness_ood, table_ood],
        witness: ([&[rho, rho2][..], &u[2..m]].concat(), opened * middle),
        wiring: (u[..m].to_vec(), next * wiring_scale),
        copy: (copy_point(&u, kappa), copy_value),
        sum: S::constant(F192::ZERO),
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
/// and four claims: it holds if every claim holds on its commitment (one opening a claim, [`verify_openings`]).
pub fn verify(
    index: &Commitment,
    statement: &Statement,
    proof: &Proof,
    log_rows: usize,
) -> Result<(Commitments, Claims), VerifyError> {
    if !supported(log_rows) {
        return Err(VerifyError::Shape);
    }
    verify_reduction(index, statement, proof, log_rows)
}

/// [`verify`] at any size the reduction takes ([`reduction_supported`]), past the sizes whose claims leanVM's
/// WHIR opens: the commitments and the claims, for a block whose openings take the tables.
pub fn verify_reduction(
    index: &Commitment,
    statement: &Statement,
    proof: &Proof,
    log_rows: usize,
) -> Result<(Commitments, Claims), VerifyError> {
    if !reduction_supported(log_rows) {
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
            sum: Claim {
                point: sum_point(log_rows),
                value: reduced.sum,
            },
        },
    ))
}

/// The openings of a proof's four claims, in the order of [`Claims::all`].
pub struct Openings(pub [opening::Proof; 4]);

/// Open a proof's `claims` on the tables it committed. The wiring's opening is about public data: anyone can make
/// it.
pub fn open(tables: &Tables, claims: &Claims, index: &Committed) -> Openings {
    Openings(claims.all().map(|(k, claim)| {
        let table = if k == 1 { index } else { tables.table(k) };
        tracing::info_span!("Open").in_scope(|| opening::open(table, claim))
    }))
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

/// Check the openings of the four claims against the commitments they name.
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
    let on = [&commitments.witness, index, &commitments.table];
    for ((k, claim), proof) in claims.all().into_iter().zip(&openings.0) {
        opening::verify(on[k], claim, proof)?;
    }
    Ok(())
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::circuit::{Builder, Src, public_words};
    use primitives::test_rng::Rng;

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

    fn truth(index: &Index, proved: &Proved) -> [bool; 4] {
        proved.claims.all().map(|(k, claim)| {
            let words = if k == 1 { &index.table[..] } else { proved.tables.table(k).words() };
            opening::evaluate(words, &claim.point) == claim.value
        })
    }

    /// The prover's output, pinned: the proof and its four openings on the toy circuit, so a change to how the
    /// prover computes cannot change a byte of what it proves. (Before the one quotient table, with six claims on
    /// four commitments, the pin was `114bb485…`; before the EIP's PCS claims, `8e39cf6a…`.)
    #[test]
    fn proofs_are_pinned() {
        let mut rng = Rng::new(0x1D);
        let circuit = toy();
        let index = Index::new(&circuit);
        let index_committed = index.commit();
        let commitment = Commitment::of(&index_committed);
        let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
        let statement = toy_statement(&x);
        let cells = toy_cells(&circuit, &x);
        let randomness = Randomness::derive(&seed(&mut rng), &commitment, &statement, &cells);
        let proved = prove_with_randomness(&circuit, &index, &commitment, &statement, &cells, &randomness);
        let openings = open(&proved.tables, &proved.claims, &index_committed);
        let hex: String = digest(&proved.proof, &openings)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        assert_eq!(hex, "462e0b363a595e436023e23e11b36b4718d5600d0aee18497a93ff61f2f37e58");
    }

    /// The quotient table holds what [`table_slot`] says, for a witness: `h`'s top coefficient zero in every limb
    /// (the copy argument's sum over the cells), its blinding past its `n` coefficients and nothing after, `q` of
    /// degree `2 n - 1`, and the empty limbs empty.
    #[test]
    fn the_quotient_table_is_laid_out() {
        let mut rng = Rng::new(0x7A);
        let circuit = toy();
        let index = Index::new(&circuit);
        let commitment = Commitment::of(&index.commit());
        let x: [u8; 32] = std::array::from_fn(|_| rng.next_u64() as u8);
        let statement = toy_statement(&x);
        let cells = toy_cells(&circuit, &x);
        let proved = prove(&circuit, &index, &commitment, &statement, &cells);
        let words = proved.tables.table.words();
        let n = 1 << cell_vars(circuit.log_rows);
        assert_eq!(words.len(), 16 * n);
        let slot = |kind: usize, limb: usize| &words[table_slot(kind, limb, n)..table_slot(kind, limb, n) + 2 * n];
        assert!(slot(0, 3).iter().chain(slot(1, 3)).all(|w| w.is_zero()));
        for limb in 0..3 {
            assert!(slot(1, limb)[n - 1].is_zero(), "h's top coefficient, limb {limb}");
            assert!(slot(1, limb)[n..n + H_BLIND].iter().all(|w| !w.is_zero()));
            assert!(slot(1, limb)[n + H_BLIND..].iter().all(|w| w.is_zero()));
            assert!(slot(0, limb)[2 * n - 64..].iter().any(|w| !w.is_zero()), "q fills its 2 n coefficients");
        }
    }

    /// On a small circuit: an honest proof leaves four true claims that open, and a witness that breaks one gate,
    /// one copy, one input's range or one public value leaves a false one.
    #[test]
    fn claims_hold_exactly_for_a_witness() {
        let mut rng = Rng::new(0x51);
        let circuit = toy();
        let index = Index::new(&circuit);
        let index_committed = index.commit();
        let commitment = Commitment::of(&index_committed);
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
        assert_eq!(truth(&index, &proved), [true; 4]);
        assert_eq!(proved.proof.stream.len(), 2 * 3 + 4 + 1);
        let openings = open(&proved.tables, &proved.claims, &index_committed);
        assert_eq!(
            verify_openings(circuit.log_rows, &commitment, &proved.commitments, &proved.claims, &openings),
            Ok(())
        );
        // An opening of one claim does not open another.
        let mut swapped = Openings(openings.0.clone());
        swapped.0.swap(2, 3);
        assert!(verify_openings(circuit.log_rows, &commitment, &proved.commitments, &proved.claims, &swapped).is_err());

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
            assert!(truth.contains(&false), "{name}: {truth:?}");
            assert!(truth[0] && truth[1], "{name}: {truth:?}");
        }
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
