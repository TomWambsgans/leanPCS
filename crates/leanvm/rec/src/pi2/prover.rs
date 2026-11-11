// Part of this repository. The quotient's computation on an extension coset follows
// crates/membership/quotient/src/protocol.rs (`prove_with_randomness`, adapted there from leanVM's `flock::quotient`,
// branch PCS-openings-aggregation, commit 651453c6), without its hiding; the transforms are crates/membership/quotient's
// (`ntt`, AVX-512), the commitments and openings the EIP draft's PCS claims (`crates/pcs_claim`, leanVM's WHIR at
// c445e3d5). MIT OR Apache-2.0; see AGENTS.md.
//! π2's prover (`PI2.md` §3), for any [`Circuit`]:
//!
//! 1. `w`'s novel coefficients (one transform on `V_m`), then its `B` coefficients (subset sums): the table `W`,
//!    committed (`2^m` words);
//! 2. `α, β, γ`; the internal pushes `P_v` on `V_m` (a pair's formula, or the position's own value at a forward and
//!    a hole), and `h = (1 + 1_S)(1/(α + w + βx) + 1/(α + P_v + κ + βσ))` there (eight rows at a time, one batched
//!    inversion per run, `h_on_v`), in `Q`'s stack: zero at the holes, its sum zero; `h`'s and `P`'s novel
//!    coefficients (`P` the interpolation of `P_v`);
//! 3. on the coset `D = β_{m+1} + V_{m+1}` (`2N` points, disjoint from `V_m`), one coset of `V_m` at a time: `w`,
//!    `h`, `P` by transforms (`σ`, `κ` the setup's), the row's cells `w(x + ω_c)` (a coset of `V_r` stays in `D`),
//!    every pair's indicator (one batched inversion per chunk of points), `P_v` (the internal groups' pushes as one
//!    quadratic form of the cells, `Quadratic`), the ports' `T = Σ I_p (E_p + Φ_k)`, `d_pull`, `d_push = α + P + κ +
//!    βσ`, `q = (h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T) / Z_V` and `q_P = (P + P_v) / Z_V`; their novel
//!    coefficients (degree below `2N`);
//! 4. the stack `Q`: `h` (degree below `N`) and `q`'s two chunks, three limbs each, `P` and `q_P`'s two chunks, in
//!    sixteen slots of `N` words (`verifier::QUOTIENT_SLOTS`, four of them zero), committed;
//! 5. `t`; the fold values, `ξ = κ(t) + β σ(t)` (PI2.md §9) and `s = P(t)`; `ρ`; the claims (the verifier's five, each
//!    a point of its commitment's whole stack), opened: one opening per claim (`pcs_claim`).

use std::sync::Mutex;
use std::time::Instant;

use fiat_shamir::merkle::Hash;
use leanvm_statement::field::E;
use leanvm_statement::transcript::{Checks, KeccakWriter, root_halves, statement_words};
use primitives::field::{F64, F192};
use quotient::domain::{beta, chain, point};
use quotient::ntt::{self, ESplat, Ex8, Kx8, Kx8U, MixedSum};
use pcs_claim::{Commitment, PcsClaim};

use super::circuit::{Circuit, Formula, Lin, Read};
pub use super::verifier::{
    CERTIFIED_FROM, EMPTY_SLOTS, MIN_CERTIFIED_STACK, MIN_LOG_STACK, P_SLOT, QP_SLOT, QUOTIENT_SLOTS, h_slot, q_slot,
    stack_vars,
};
use super::verifier::{Pi2Stack, Reduced, Spec, claim};

/// Words copied by the workers in runs of this many (`parallel::map_collect` writes each run whole).
const COPY_RUN: usize = 64;

/// The `B` coefficients from the novel ones (or back), into a new column (no copy of `novel` first).
fn b_coefficients(novel: &[F64]) -> Vec<F64> {
    ntt::subset_sums_of_cols(&[novel]).pop().expect("one column")
}

/// The extension coset `D = β_{m+1} + V_{m+1}` (`2N` points, disjoint from `V_m`): its offset.
pub fn extension_offset(log_n: usize) -> F64 {
    beta()[log_n + 1]
}

/// The setup: `σ` and `κ` on the prover's extension coset `D` ([`extension_offset`]; fixed by the circuit, so
/// computed once here, not per proof), and the committed stack of their `B` coefficients (`κ`'s, then `κ + σ`'s).
pub struct Setup {
    /// `σ`'s values on `V_m`, the points `ω_(σ(i))`.
    pub sigma_on_v: Vec<F64>,
    pub sigma_on_d: Vec<F64>,
    pub kappa_on_d: Vec<F64>,
    /// The stack's words (`2^(m+1)`, its leading lanes).
    pub words: Vec<F64>,
    pub commitment: Commitment,
    /// `Q`'s stack, which a proof's openings hand back once done with it, for the next proof to build its own `Q` in:
    /// every word of it but the zero slots' is written again, so only those are zeroed (`16 N` words, 2.1 GB at `2^24`
    /// positions, kept between proofs).
    spare: Mutex<Vec<F64>>,
}

impl Setup {
    /// The setup of `circuit`, which must be valid ([`Circuit::validate`]).
    pub fn new(circuit: &Circuit) -> Self {
        circuit.validate().unwrap_or_else(|e| panic!("the circuit is not valid: {e}"));
        let (m, n) = (circuit.log_n, circuit.n());
        let sigma_on_v: Vec<F64> = parallel::map_collect(n, |i| point(circuit.sigma[i] as usize));
        let sigma = ntt::coefficients_cols_of(&[&sigma_on_v], F64::ZERO).pop().expect("one column");
        let mut kappa = circuit.kappa.clone();
        ntt::coefficients(&mut kappa, F64::ZERO);
        // The halves `κ` and `κ + σ` (PI2.md §9): the claim at the last coordinate `β` is `κ(t) + β σ(t)`, the one value
        // `d_push` needs.
        let (sb, kb) = (b_coefficients(&sigma), b_coefficients(&kappa));
        let mut words = kb;
        words.extend(sb.iter().zip(&words[..n]).map(|(&a, &b)| a + b).collect::<Vec<F64>>());
        drop(sb);
        // Kept with its codeword: every proof opens it, and reads its first queries' rows from it.
        let commitment = pcs_claim::commit_words(&words, stack_vars(m)[2], true);
        let offset = extension_offset(m);
        Self {
            sigma_on_v,
            sigma_on_d: on_extension(&sigma, m, offset),
            kappa_on_d: on_extension(&kappa, m, offset),
            words,
            commitment,
            spare: Mutex::new(Vec::new()),
        }
    }

    /// A buffer of `len` words for `Q`'s stack, the spare if it is that long, else zeros.
    fn stack(&self, len: usize) -> Vec<F64> {
        let spare = std::mem::take(&mut *self.spare.lock().expect("no panic held the spare"));
        if spare.len() == len {
            spare
        } else {
            drop(spare);
            parallel::map_collect(len, |_| F64::ZERO)
        }
    }

    pub fn root(&self) -> Hash {
        self.commitment.root
    }

    /// The setup commitment's out-of-domain answer.
    pub fn ood(&self) -> F192 {
        self.commitment.ood
    }
}

/// π2's IV: Keccak-256 of a tag, π1's contract IV, the setup commitment (its root, its out-of-domain answer as a
/// claim encodes it), the circuit's digest and `log_n` (one byte).
pub fn iv(pi1_iv: &[u8; 32], circuit_digest: &[u8; 32], setup_root: &Hash, setup_ood: F192, log_n: usize) -> [u8; 32] {
    primitives::hash::hash(
        &[
            b"leanvm-rec-iv-v3".as_slice(),
            pi1_iv,
            setup_root,
            &pcs_claim::element_bytes(setup_ood),
            circuit_digest,
            &[log_n as u8],
        ]
        .concat(),
    )
}

/// A public value as the stream carries it, one per [`Read`]: an integer, 32 bytes as they are (π1's roots as
/// claims' root words, which its calls take as they are), an element of `E`.
#[derive(Clone, Copy, Debug)]
pub enum PublicValue {
    Integer(u64),
    Root([u8; 32]),
    Scalar(F192),
    /// A frame word (`Read::Frame`): not in the stream, hashed by the seed.
    Word([u8; 32]),
}

/// The frame words among `values`, in order: what the seed hashes after the public input.
pub fn frame_words(values: &[PublicValue]) -> Vec<[u8; 32]> {
    values
        .iter()
        .filter_map(|v| match v {
            PublicValue::Word(w) => Some(*w),
            _ => None,
        })
        .collect()
}

/// The public scalars: the public input's four words, then the values ([`Circuit::public_scalars`]).
pub fn public_scalars(public_input: &[u8; 32], values: &[PublicValue]) -> Vec<F192> {
    let mut out: Vec<F192> = statement_words(public_input).map(F192::from).to_vec();
    for v in values {
        match *v {
            PublicValue::Integer(x) => out.push(F192::new(x, 0, 0)),
            PublicValue::Root(bytes) => out.extend(root_halves(&bytes).map(F192::from)),
            PublicValue::Scalar(x) => out.push(x),
            PublicValue::Word(w) => out.extend(statement_words(&w).map(F192::from)),
        }
    }
    out
}

/// A proof: the stream (the calldata after the public input), the roots, and what the openings need: each stack's
/// words and commitment.
pub struct Proved {
    pub stream: Vec<u8>,
    pub roots: [Hash; 2],
    pub witness: (Vec<F64>, Commitment),
    pub quotient: (Vec<F64>, Commitment),
    /// The verifier's reduction of the stream: its claims.
    pub reduced: Reduced<E>,
    /// Seconds per step.
    pub timings: Vec<(&'static str, f64)>,
}

/// `T` at the holes: each hole `i`'s push (its pair's formula of its row) plus its public term's value, `T(ω_i) =
/// E_p(ω_i) + F_J`, zero exactly when the port holds. On `V_m` the identity reads `h d_pull d_push = T` at a hole, so
/// `h` there is `T / (d_pull d_push)`: zero for a witness, and for any other `w` what keeps the identity a polynomial
/// one, the copy argument's sum catching the port (`PI2.md` §7; the tests' public mutations).
fn holes(circuit: &Circuit, w: &[F64], public: &[F192], gammas: &[F192]) -> Vec<(usize, F192)> {
    let values: std::collections::HashMap<u32, F192> = circuit
        .public
        .iter()
        .map(|t| (t.tag, t.value.eval(&|c| public[c], gammas)))
        .collect();
    let mut out = vec![];
    for pair in circuit.pairs.iter().filter(|p| !p.pulls) {
        let formula = &circuit.formulas[pair.formula];
        for row in pair.first_row..pair.first_row + (1 << pair.log_rows) {
            let base = row << circuit.log_row;
            let i = base + pair.role;
            let push = formula.eval(&|c| F192::from(w[base + c]), gammas);
            out.push((i, push + values[&circuit.sigma[i]]));
        }
    }
    out
}

/// A linear form in `K` on eight points, its cells' indices permuted by a role.
struct KLin {
    /// The cells of coefficient 1, and the others with theirs (summed unreduced, one reduction).
    ones: Vec<usize>,
    scaled: Vec<(Kx8, usize)>,
    constant: F64,
}

impl KLin {
    fn new(l: &Lin, role: usize) -> Self {
        let terms = l.terms.iter().map(|&(c, cell)| (F64(c.value[0]), cell as usize ^ role));
        Self {
            ones: terms.clone().filter(|&(c, _)| c == F64::ONE).map(|(_, i)| i).collect(),
            scaled: terms.filter(|&(c, _)| c != F64::ONE).map(|(c, i)| (Kx8::splat(c), i)).collect(),
            constant: l.constant.map_or(F64::ZERO, |c| F64(c.value[0])),
        }
    }

    #[inline(always)]
    fn eval(&self, cells: &[Kx8]) -> Kx8 {
        let sum = self.ones.iter().fold(Kx8::splat(self.constant), |acc, &i| acc + cells[i]);
        if self.scaled.is_empty() {
            sum
        } else {
            sum + self
                .scaled
                .iter()
                .fold(Kx8U::zero(), |acc, &(c, i)| acc + Kx8U::product(c, cells[i]))
                .reduce()
        }
    }
}

/// A group's formula on the extension coset: in `K` (every internal push), linear in `E` (a port's fingerprint, its
/// powers of `γ` evaluated), or any other formula of `E` (point by point).
enum Compiled {
    K {
        lin: KLin,
        products: Vec<(F64, KLin, KLin)>,
    },
    ELinear {
        terms: Vec<(ESplat, usize)>,
        constant: F192,
    },
    E {
        formula: Formula,
        role: usize,
    },
}

impl Compiled {
    fn new(f: &Formula, role: usize, gammas: &[F192]) -> Self {
        if f.is_base() {
            Compiled::K {
                lin: KLin::new(&f.lin, role),
                products: f
                    .products
                    .iter()
                    .map(|(c, a, b)| (F64(c.value[0]), KLin::new(a, role), KLin::new(b, role)))
                    .collect(),
            }
        } else if f.products.is_empty() {
            Compiled::ELinear {
                terms: f
                    .lin
                    .terms
                    .iter()
                    .map(|(c, cell)| (ESplat::new(c.eval(gammas)), *cell as usize ^ role))
                    .collect(),
                constant: f.lin.constant.map_or(F192::ZERO, |c| c.eval(gammas)),
            }
        } else {
            Compiled::E {
                formula: f.clone(),
                role,
            }
        }
    }
}

/// The `K` groups' pushes `Σ_g S_g (E_g + w)` (and every group's `S_g w`) as one quadratic form of the row's cells,
/// `Σ_a c_a (L_a + Σ_b T_ab c_b) + T_1`, whose coefficients are `K`-combinations of the groups' indicator sums. On a
/// chunk the wide pairs' indicators are periodic (`pv` vectors), and so are these combinations: they are computed once
/// a chunk, and a point's share costs one product a distinct monomial of the formulas (rather than one a product of
/// each group's formula, and one a group).
struct Quadratic {
    /// The cells `a` with products, each with its cells `b` (`T_ab`'s coefficients, then `L_a`'s, in this order).
    rows: Vec<(usize, Vec<usize>)>,
    /// The cells with a linear coefficient alone (one coefficient each, after the rows').
    linear: Vec<usize>,
    /// The coefficients a chunk's vector reads (the constant `T_1` last).
    len: usize,
    /// Each group's share: `(coefficient, factor)`, `T[coefficient] += factor S_g`.
    shares: Vec<Vec<(usize, F64)>>,
}

impl Quadratic {
    /// The plan of `spec`'s groups `groups` (rows of `width` cells; `shares[i]` is `groups[i]`'s): `K` groups' formulas
    /// expanded into monomials of their cells (`cell ^ role`), and every group's `w = c_0` (the push `E_g + w`).
    fn new(spec: &Spec, groups: &[usize], width: usize) -> Self {
        use std::collections::BTreeMap;
        let k = |c: &super::circuit::Coeff| F64(c.value[0]);
        // Each group's monomials: `(a, b)` with `a <= b`, `(a, NONE)` linear, `(NONE, NONE)` the constant.
        const NONE: usize = usize::MAX;
        let monomials: Vec<BTreeMap<(usize, usize), F64>> = groups
            .iter()
            .map(|&g| &spec.groups[g])
            .map(|g| {
                let mut m = BTreeMap::new();
                let mut add = |key: (usize, usize), c: F64| *m.entry(key).or_insert(F64::ZERO) += c;
                add((0, NONE), F64::ONE);
                if g.formula.is_base() {
                    let role = g.role;
                    let f = &g.formula;
                    let terms = |l: &Lin| -> Vec<(F64, usize)> {
                        l.terms.iter().map(|(c, cell)| (k(c), *cell as usize ^ role)).collect()
                    };
                    terms(&f.lin).into_iter().for_each(|(c, cell)| add((cell, NONE), c));
                    if let Some(c) = &f.lin.constant {
                        add((NONE, NONE), k(c));
                    }
                    for (c, a, b) in &f.products {
                        let c = k(c);
                        let (ka, kb) = (a.constant.as_ref().map(k), b.constant.as_ref().map(k));
                        for &(x, i) in &terms(a) {
                            for &(y, j) in &terms(b) {
                                add((i.min(j), i.max(j)), c * x * y);
                            }
                            if let Some(kb) = kb {
                                add((i, NONE), c * x * kb);
                            }
                        }
                        if let Some(ka) = ka {
                            terms(b).into_iter().for_each(|(y, j)| add((j, NONE), c * ka * y));
                            if let Some(kb) = kb {
                                add((NONE, NONE), c * ka * kb);
                            }
                        }
                    }
                }
                m.retain(|_, c| *c != F64::ZERO);
                m
            })
            .collect();
        // The coefficients' order: each row's products then its linear coefficient, the linear cells, the constant.
        let mut products: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        let mut linear = vec![false; width];
        for m in &monomials {
            for &(a, b) in m.keys() {
                if a != NONE && b != NONE {
                    products.entry(a).or_default().push(b);
                } else if a != NONE {
                    linear[a] = true;
                }
            }
        }
        let mut index = BTreeMap::new();
        let mut rows = vec![];
        let mut len = 0;
        for (a, mut bs) in products {
            bs.sort_unstable();
            bs.dedup();
            for &b in &bs {
                index.insert((a, b), len);
                len += 1;
            }
            index.insert((a, NONE), len);
            len += 1;
            rows.push((a, bs));
        }
        let linear: Vec<usize> = (0..width).filter(|a| linear[*a] && !index.contains_key(&(*a, NONE))).collect();
        for &a in &linear {
            index.insert((a, NONE), len);
            len += 1;
        }
        index.insert((NONE, NONE), len);
        len += 1;
        let shares = monomials
            .iter()
            .map(|m| m.iter().map(|(key, &c)| (index[key], c)).collect())
            .collect();
        Self {
            rows,
            linear,
            len,
            shares,
        }
    }

    /// A chunk's coefficients, `pv` sets of [`Self::len`]: the `g`-th planned group's wide sum at vector `k` is
    /// `sum(g, k)` (`None`: no wide pair).
    fn coefficients(&self, pv: usize, sum: impl Fn(usize, usize) -> Option<Kx8>) -> Vec<Kx8> {
        let mut t = vec![Kx8::splat(F64::ZERO); pv * self.len];
        for (g, shares) in self.shares.iter().enumerate() {
            for k in 0..pv {
                let Some(s) = sum(g, k) else { continue };
                let t = &mut t[k * self.len..(k + 1) * self.len];
                for &(i, c) in shares {
                    t[i] = t[i] + if c == F64::ONE { s } else { Kx8::splat(c) * s };
                }
            }
        }
        t
    }

    /// The form at a vector's `cells`, its coefficients `t`, unreduced.
    #[inline(always)]
    fn eval(&self, t: &[Kx8], cells: &[Kx8]) -> Kx8U {
        let mut t = t.iter();
        let mut next = || *t.next().expect("the plan's coefficients");
        let mut acc = Kx8U::zero();
        for (a, bs) in &self.rows {
            let inner = bs.iter().fold(Kx8U::zero(), |acc, &b| acc + Kx8U::product(next(), cells[b]));
            acc = acc + Kx8U::product(inner.reduce() + next(), cells[*a]);
        }
        for &a in &self.linear {
            acc = acc + Kx8U::product(next(), cells[a]);
        }
        acc + Kx8U::product(next(), Kx8::splat(F64::ONE))
    }
}

/// The lanes of eight elements.
fn lanes(x: Kx8) -> [F64; 8] {
    x.to_row().0
}

/// Eight elements of `E` as lanes.
fn ex8(x: [F192; 8]) -> Ex8 {
    let limb = |k: usize| Kx8::new(x.map(|e| F64([e.c0, e.c1, e.c2][k])));
    Ex8::from_limbs([limb(0), limb(1), limb(2)])
}

/// A formula of `K`'s value at eight points' cells.
#[inline(always)]
fn k_value(lin: &KLin, products: &[(F64, KLin, KLin)], cells: &[Kx8]) -> Kx8 {
    if products.is_empty() {
        lin.eval(cells)
    } else {
        let p = products.iter().fold(Kx8U::zero(), |acc, (c, a, b)| {
            let (x, y) = (a.eval(cells), b.eval(cells));
            acc + Kx8U::product(if *c == F64::ONE { x } else { Kx8::splat(*c) * x }, y)
        });
        lin.eval(cells) + p.reduce()
    }
}

impl Compiled {
    /// Its value at eight points' cells (`cells[c]` the cell `c` of the lanes' rows, before the role's permutation).
    fn eval(&self, cells: &[Kx8], gammas: &[F192]) -> Ex8 {
        match self {
            Compiled::K { lin, products } => Ex8::from_k(k_value(lin, products, cells)),
            Compiled::ELinear { terms, constant } => {
                let mut v = MixedSum::default();
                terms.iter().for_each(|(c, cell)| v.add(c, cells[*cell]));
                v.reduce() + Ex8::splat(*constant)
            }
            Compiled::E { formula, role } => {
                let rows: Vec<[F64; 8]> = cells.iter().map(|&c| lanes(c)).collect();
                ex8(std::array::from_fn(|l| {
                    formula.eval(&|c| F192::from(rows[c ^ role][l]), gammas)
                }))
            }
        }
    }
}

/// `parallel::chunks_mut3` with a fourth slice of the same length, its chunks handed out behind (uncontended)
/// locks: `leanvm_rec` takes no `unsafe`.
fn chunks_mut4<F>(a: &mut [F64], b: &mut [F64], c: &mut [F64], d: &mut [F64], chunk: usize, f: F)
where
    F: Fn(usize, &mut [F64], &mut [F64], &mut [F64], &mut [F64]) + Sync,
{
    assert_eq!(a.len(), d.len(), "chunks_mut4: slices differ in length");
    let parts: Vec<std::sync::Mutex<&mut [F64]>> = d.chunks_mut(chunk).map(std::sync::Mutex::new).collect();
    parallel::chunks_mut3(a, b, c, chunk, |i, a, b, c| {
        let mut d = parts[i].lock().expect("one task a chunk");
        f(i, a, b, c, &mut d)
    });
}

/// The ports' `Φ_k` on a chunk of `D`: for each of the chunk's rows (`run >> r` of them, `w_r(x)` constant on a row:
/// `w_r(offset) + ω_{i >> r}`), `Φ_k = Z_V Σ_J F_J / (w_r(x) + ω_{y_J})` (`Spec::phi`), eight rows a vector, one
/// batched inversion for the chunk.
struct Phi {
    /// Per role of `Spec::phi`: each term's `(ESplat of F_J, ω_{y_J})`.
    terms: Vec<Vec<(ESplat, F64)>>,
    /// `w_r(offset)`.
    at_offset: F64,
}

impl Phi {
    fn new(spec: &Spec, values: &[F192], offset: F64) -> Self {
        let mut at = 0;
        let terms = spec
            .phi
            .iter()
            .map(|(_, terms)| {
                terms
                    .iter()
                    .map(|t| {
                        at += 1;
                        (ESplat::new(values[at - 1]), point(t.row as usize))
                    })
                    .collect()
            })
            .collect();
        Self {
            terms,
            at_offset: chain(offset, spec.log_row + 1)[spec.log_row],
        }
    }

    /// The chunk's values, `[role][row]`, its first row `first` (an index on `D`), `rows` rows (a multiple of 8).
    fn chunk(&self, first: usize, rows: usize, zv: F64) -> Vec<Vec<F192>> {
        let vectors = rows / 8;
        let z: Vec<Kx8> = (0..vectors)
            .map(|v| Kx8::new(std::array::from_fn(|l| self.at_offset + point(first + 8 * v + l))))
            .collect();
        let mut dens: Vec<Kx8> = Vec::with_capacity(vectors * self.terms.iter().map(Vec::len).sum::<usize>());
        for terms in &self.terms {
            for &(_, y) in terms {
                let y = Kx8::splat(y);
                dens.extend(z.iter().map(|&z| z + y));
            }
        }
        let one8 = Kx8::splat(F64::ONE);
        let mut prefix = Vec::with_capacity(dens.len());
        let mut acc = one8;
        for &d in &dens {
            prefix.push(acc);
            acc = acc * d;
        }
        let mut inv = Kx8::new(lanes(acc).map(|x| x.inv())) * Kx8::splat(zv);
        for (d, &pre) in dens.iter_mut().zip(&prefix).rev() {
            let next = inv * *d;
            *d = inv * pre;
            inv = next;
        }
        let mut at = 0;
        self.terms
            .iter()
            .map(|terms| {
                let mut sums = vec![MixedSum::default(); vectors];
                for (c, _) in terms {
                    for (v, sum) in sums.iter_mut().enumerate() {
                        sum.add(c, dens[at + v]);
                    }
                    at += vectors;
                }
                sums.into_iter().flat_map(|s| s.reduce().to_array()).collect()
            })
            .collect()
    }
}

/// `q`'s and `q_P`'s values on `D = β_{m+1} + V_{m+1}` ([`extension_offset`]), limb by limb, eight consecutive points
/// at a time (`quotient::ntt`'s lanes: one AVX-512 carry-less product for eight), then their novel coefficients
/// (degree below `2N`): `q = (h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T) / Z_V` with `d_push = α + P + κ + βσ`
/// (`P` committed) and `T = Σ_port I_p (E_p + Φ_k)`, and `q_P = (P + P_v) / Z_V`, `P_v = w + Σ_int I_p (E_p + w)`.
#[allow(clippy::too_many_arguments)]
fn quotient_on_extension(
    circuit: &Circuit,
    spec: &Spec,
    setup: &Setup,
    w_novel: &[F64],
    h_novel: [&[F64]; 3],
    p_novel: &[F64],
    [alpha, beta_, gamma]: [F192; 3],
    port_values: &[F192],
    [l0, l1, l2]: [&mut [F64]; 3],
    qp: &mut [F64],
) {
    let (m, r, n) = (circuit.log_n, circuit.log_row, circuit.n());
    let big = 2 * n;
    let offset = extension_offset(m);
    let profile = std::env::var_os("PI2_PROFILE").is_some();
    let mut clock = Instant::now();
    let mut lap = |name: &str| {
        if profile && !name.is_empty() {
            eprintln!("    q: {:7.3} s  {name}", clock.elapsed().as_secs_f64());
        }
        clock = Instant::now();
    };
    if profile {
        let mut hist = std::collections::BTreeMap::new();
        spec.pairs.iter().for_each(|p| *hist.entry(p.log_rows).or_insert(0usize) += 1);
        let kinds = spec.groups.iter().fold([0usize; 3], |mut k, g| {
            k[if g.formula.is_base() { 0 } else if g.formula.products.is_empty() { 1 } else { 2 }] += 1;
            k
        });
        let terms: usize = spec.groups.iter().map(|g| g.formula.lin.terms.len()).sum();
        let products: usize = spec.groups.iter().map(|g| g.formula.products.len()).sum();
        eprintln!(
            "    q: m {m} r {r}; {} pairs by log_rows {hist:?}; {} pull-less; {} groups (K, E-linear, E: {kinds:?}), {terms} terms, {products} products; Φ: {:?} terms",
            spec.pairs.len(),
            spec.pull_less.len(),
            spec.groups.len(),
            spec.phi.iter().map(|(k, t)| (*k, t.len())).collect::<Vec<_>>()
        );
    }
    let (sd, kd) = (&setup.sigma_on_d, &setup.kappa_on_d);
    let gammas = primitives::field::powers(gamma, spec.max_gamma + 1);

    // `Z_V` on `D`: `w_m(β_{m+1}) + ω_{i >> m}`, one value per coset of `V_m`, and its inverses.
    let zv_off = chain(offset, m + 1)[m];
    let zv: [F64; 2] = std::array::from_fn(|c| zv_off + point(c));
    let zv_inv = zv.map(|z| z.inv());

    // The normalised `Ẑ_s` on `D`, linear: at `β_{m+1}`, and on the low and high bits of the index.
    let s_max = spec.max_log_rows();
    // `Ẑ_0(x) … Ẑ_{s_max}(x)`, each from the one before.
    let zhats = |x: F64| -> Vec<F64> {
        let mut out = Vec::with_capacity(s_max + 1);
        let mut z = x;
        out.push(z);
        for &c in &spec.c[..s_max] {
            z = z + c * z.square();
            out.push(z);
        }
        out
    };
    // A table of `Ẑ_s` at `count` points, `s` major.
    let table = |count: usize, at: &(dyn Fn(usize) -> F64 + Sync)| -> Vec<Vec<F64>> {
        let rows: Vec<Vec<F64>> = parallel::map_collect(count, |j| zhats(at(j)));
        (0..=s_max).map(|s| rows.iter().map(|r| r[s]).collect()).collect()
    };
    const LOW: usize = 12;
    let at_offset: Vec<F64> = zhats(offset);
    let low = table(1 << LOW, &point);
    let high = table((big >> LOW).max(1), &|j| point(j << LOW));

    // The indicators, a chunk of `run` points at a time: a chunk lies in one coset of `V_m` (one `Z_V` value) and
    // fixes the index's bits from `log run` up. `Ẑ_s` vanishes on `U_s = ⟨β_r, …, β_{r+s-1}⟩`, so pair `p`'s indicator
    // reads the bits below `r` and from `r + s_p` up only: if `r + s_p ≥ log run` it is periodic in the chunk, of
    // period `2^r` (a *wide* pair: `period` points of it per chunk); otherwise it is computed at every point of the
    // chunk. Every chunk's indicators are one batched inversion.
    let width = 1usize << r;
    let run = n.min(1 << LOW);
    // A vector of eight points lies in one row (`Φ` is one value on it).
    assert!(r >= 3 && run.is_power_of_two() && run >= 8 * width);
    let log_run = run.trailing_zeros() as usize;
    let period = width.max(8);
    let pv = period / 8;
    let wide: Vec<bool> = spec
        .pairs
        .iter()
        .map(|p| period <= run && r + p.log_rows >= log_run)
        .collect();
    // Pair `p`'s vectors in a chunk's table: from `at[p]`, `pv` of them if wide, else `run / 8`.
    let mut at = Vec::with_capacity(spec.pairs.len());
    let mut vectors = 0;
    for &w in &wide {
        at.push(vectors);
        vectors += if w { pv } else { run / 8 };
    }
    let narrow = |members: &[usize]| -> Vec<usize> { members.iter().copied().filter(|&p| !wide[p]).collect() };

    let pairs: Vec<(usize, F64)> = spec.pairs.iter().map(|p| (p.log_rows, p.z)).collect();
    let groups: Vec<(Compiled, &[usize], Vec<usize>)> = spec
        .groups
        .iter()
        .map(|g| (Compiled::new(&g.formula, g.role, &gammas), &g.pairs[..], narrow(&g.pairs)))
        .collect();
    // The internal groups' wide parts, as one quadratic form of the row's cells whose coefficients are periodic in a
    // chunk ([`Quadratic`]); their narrow pairs are evaluated group by group. The port groups, into `T`, each with
    // its role's `Φ`.
    let internal: Vec<usize> = (0..groups.len()).filter(|&g| spec.groups[g].pulls).collect();
    assert!(
        internal.iter().all(|&g| matches!(groups[g].0, Compiled::K { .. })),
        "the internal pushes are in K"
    );
    let quadratic = Quadratic::new(spec, &internal, width);
    let has_wide: Vec<bool> = spec.groups.iter().map(|g| g.pairs.iter().any(|&p| wide[p])).collect();
    let internal_narrow: Vec<usize> = internal.iter().copied().filter(|&g| !groups[g].2.is_empty()).collect();
    let ports: Vec<(usize, Option<usize>)> = (0..groups.len())
        .filter(|&g| !spec.groups[g].pulls)
        .map(|g| (g, spec.phi.iter().position(|(k, _)| *k == spec.groups[g].role)))
        .collect();
    let phi = Phi::new(spec, port_values, offset);
    let (alpha8, beta8) = (Ex8::splat(alpha), Ex8::splat(beta_));
    let one8 = Kx8::splat(F64::ONE);
    let zero8 = Kx8::splat(F64::ZERO);
    // `β x` at a chunk's points: `x = offset + ω_start + ω_(8 j + l)` (the index's bits below `log run` and above
    // are disjoint), so `β ω_(8 j + l)` is a table of the chunk's vectors and `β (offset + ω_start)` one product.
    let beta_low: Vec<Ex8> = (0..run / 8)
        .map(|j| {
            let x: [F64; 8] = std::array::from_fn(|l| point(8 * j + l));
            let b: [F192; 8] = x.map(|x| beta_.mul_base(x));
            Ex8::from_limbs([0, 1, 2].map(|k| Kx8::new(b.map(|e| F64([e.c0, e.c1, e.c2][k])))))
        })
        .collect();

    assert!(l0.len() == big && l1.len() == big && l2.len() == big && qp.len() == big);
    // One coset `offset + ω_(c N) + V_m = ω_((2 + c) N) + V_m` of `D` at a time: `w`'s, `h`'s and `P`'s values there
    // (one transform of `N` each, from their coefficients, the five in the same dispatches, into buffers the cosets
    // share), then the numerators on it.
    let polys: [&[F64]; 5] = [w_novel, h_novel[0], h_novel[1], h_novel[2], p_novel];
    let mut on_coset: Vec<Vec<F64>> = vec![];
    let (mut transforms, mut numerator) = (0.0, 0.0);
    for coset in 0..2 {
        let clock = Instant::now();
        let first = (2 + coset) << m;
        debug_assert_eq!(point(first), offset + point(coset << m));
        if coset == 0 {
            on_coset = ntt::on_coset_prefix_cols(&polys, first, m);
        } else {
            let mut buffers: Vec<&mut [F64]> = on_coset.iter_mut().map(|b| &mut b[..]).collect();
            ntt::values_from_cols(&polys, &mut buffers, point(first));
        }
        let [wd, h0d, h1d, h2d, pd] = &on_coset[..] else {
            unreachable!("five columns")
        };
        let hd = [h0d, h1d, h2d];
        transforms += clock.elapsed().as_secs_f64();
        let clock = Instant::now();
        let quarter = coset * n..(coset + 1) * n;
        let (l0, l1, l2, qp) = (
            &mut l0[quarter.clone()],
            &mut l1[quarter.clone()],
            &mut l2[quarter.clone()],
            &mut qp[quarter],
        );
        chunks_mut4(l0, l1, l2, qp, run, |chunk, o0, o1, o2, op| {
            let start = coset * n + chunk * run;
            // The chunk's indicators: denominators, then one batched inversion, times `Z_V`.
            let mut table = vec![one8; vectors];
            for (p, &(s, z)) in pairs.iter().enumerate() {
                let len = if wide[p] { pv } else { run / 8 };
                for v in 0..len {
                    let i = start + 8 * v;
                    table[at[p] + v] =
                        Kx8::load(&low[s][i & ((1 << LOW) - 1)..]) + Kx8::splat(at_offset[s] + high[s][i >> LOW] + z);
                }
            }
            let mut prefix = vec![one8; vectors];
            let mut acc = one8;
            for (pre, &d) in prefix.iter_mut().zip(&table) {
                *pre = acc;
                acc = acc * d;
            }
            let mut inv = Kx8::new(lanes(acc).map(|x| x.inv())) * Kx8::splat(zv[coset]);
            for (d, &pre) in table.iter_mut().zip(&prefix).rev() {
                let next = inv * *d;
                *d = inv * pre;
                inv = next;
            }
            drop(prefix);
            // The wide pairs' sums by group, `pv` vectors each.
            let wide_sum = |members: &[usize], k: usize| {
                members
                    .iter()
                    .filter(|&&p| wide[p])
                    .fold(zero8, |acc, &p| acc + table[at[p] + k])
            };
            let group_wide: Vec<Kx8> = groups
                .iter()
                .flat_map(|(_, members, _)| (0..pv).map(|k| wide_sum(members, k)).collect::<Vec<_>>())
                .collect();
            let coefficients = quadratic.coefficients(pv, |i, k| {
                let g = internal[i];
                has_wide[g].then(|| group_wide[g * pv + k])
            });
            let phis = phi.chunk(start >> r, run >> r, zv[coset]);
            let beta_start = Ex8::splat(beta_.mul_base(offset + point(start)));

            let mut cells = vec![one8; width];
            for j in 0..run / 8 {
                let i = start + 8 * j;
                let jw = j % pv;
                // Lane `l` is the point `i + l`, its row's cell `c` the point `(i + l) ^ c`.
                for (c, cell) in cells.iter_mut().enumerate() {
                    *cell = Kx8::load(&wd[(i ^ (c & !7)) & (n - 1)..]).xor_lanes(c & 7);
                }
                let w = cells[0];
                // `P_v - w`: the internal groups' wide share (the quadratic form), then their narrow pairs'.
                let mut pushed = quadratic.eval(&coefficients[jw * quadratic.len..(jw + 1) * quadratic.len], &cells);
                let mut selected = zero8;
                for &g in &internal_narrow {
                    let (compiled, _, narrow) = &groups[g];
                    let narrow_sum = narrow.iter().fold(zero8, |acc, &p| acc + table[at[p] + j]);
                    selected = selected + narrow_sum;
                    if let Compiled::K { lin, products } = compiled {
                        pushed = pushed + Kx8U::product(narrow_sum, k_value(lin, products, &cells));
                    }
                }
                let p_v = w + (pushed + Kx8U::product(w, selected)).reduce();
                // The ports: `1_S` and `T = Σ_g S_g (E_g + Φ_k)`.
                let mut one_s = zero8;
                let mut t_ports = Ex8::splat(F192::ZERO);
                for &(g, role_phi) in &ports {
                    let (compiled, _, narrow) = &groups[g];
                    let sum = narrow
                        .iter()
                        .fold(group_wide[g * pv + jw], |acc, &p| acc + table[at[p] + j]);
                    one_s = one_s + sum;
                    let mut value = compiled.eval(&cells, &gammas);
                    if let Some(k) = role_phi {
                        value = value + Ex8::splat(phis[k][(8 * j) >> r]);
                    }
                    t_ports = t_ports + value.mul_k(sum);
                }
                let at = i & (n - 1);
                let p = Kx8::load(&pd[at..]);
                // `q_P = (P + P_v) / Z_V`.
                let q_p = (p + p_v) * Kx8::splat(zv_inv[coset]);
                op[8 * j..8 * j + 8].copy_from_slice(&q_p.to_row().0);
                let d_pull = alpha8 + Ex8::from_k(w) + beta_start + beta_low[j];
                let d_push = alpha8 + Ex8::from_k(p + Kx8::load(&kd[i..])) + beta8.mul_k(Kx8::load(&sd[i..]));
                let h = Ex8::from_limbs([Kx8::load(&hd[0][at..]), Kx8::load(&hd[1][at..]), Kx8::load(&hd[2][at..])]);
                // `h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T`.
                let num = h * d_pull * d_push + (d_push + d_pull).mul_k(one8 + one_s) + t_ports;
                let [q0, q1, q2] = num.mul_k(Kx8::splat(zv_inv[coset])).limbs();
                o0[8 * j..8 * j + 8].copy_from_slice(&q0.to_row().0);
                o1[8 * j..8 * j + 8].copy_from_slice(&q1.to_row().0);
                o2[8 * j..8 * j + 8].copy_from_slice(&q2.to_row().0);
            }
        });
        numerator += clock.elapsed().as_secs_f64();
    }
    drop(on_coset);
    if profile {
        eprintln!("    q: {transforms:7.3} s  w, h, P on D");
        eprintln!("    q: {numerator:7.3} s  the numerators over Z_V");
    }
    lap(""); // the clock, from here
    // The four columns' transforms in the same dispatches.
    ntt::coefficients_cols(&mut [l0, l1, l2, qp], offset);
    lap("q's and q_P's coefficients");
}

/// `h = (1 + 1_S)(1/(α + w + βx) + 1/(α + P_v + κ + βσ))` on `V_m`, limb by limb (`out`), and the internal pushes
/// `P_v` (`p`: a pair's formula of its row, or the position's own value at a forward and at a hole), in chunks of
/// `run` positions. Each position's pull and push are `Circuit::pulls`'s and `Circuit::pushes`'s, found without
/// their tables: eight rows at a time, the positions of one role in them are one vector, of one formula when one pair
/// (or none) covers the eight rows (found by a search in the role's pairs, sorted row intervals), else lane by lane. A
/// pulling position's `h` is `(d_pull + d_push) / (d_pull d_push)`, a hole's zero; a chunk's denominators are one
/// batched inversion (eight chains).
#[allow(clippy::too_many_arguments)]
fn h_on_v(
    circuit: &Circuit,
    sigma_on_v: &[F64],
    w: &[F64],
    alpha: F192,
    beta_: F192,
    gammas: &[F192],
    run: usize,
    [o0, o1, o2]: [&mut [F64]; 3],
    p: &mut [F64],
) {
    let (r, n, width) = (circuit.log_row, circuit.n(), circuit.width());
    let tile = 8 * width;
    assert!(run.is_multiple_of(tile) && n.is_multiple_of(run), "chunks of whole eight-row tiles");
    let compiled: Vec<Compiled> = circuit.formulas.iter().map(|f| Compiled::new(f, 0, gammas)).collect();
    let mut by_role: Vec<Vec<(usize, usize, usize)>> = vec![vec![]; width];
    for (p, pair) in circuit.pairs.iter().enumerate() {
        by_role[pair.role].push((pair.first_row, pair.first_row + (1 << pair.log_rows), p));
    }
    by_role.iter_mut().for_each(|l| l.sort_unstable());
    // The pair of `role` covering `row` (`Ok`), and whether it (or none) covers the rows to `row + 8`.
    let column = |row: usize, role: usize| -> (Option<usize>, bool) {
        let list = &by_role[role];
        let k = list.partition_point(|e| e.0 <= row);
        if k > 0 && row < list[k - 1].1 {
            (Some(list[k - 1].2), list[k - 1].1 >= row + 8)
        } else {
            (None, list.get(k).is_none_or(|e| e.0 >= row + 8))
        }
    };
    // A position's pull, and its internal push's value (the formula of its pair, or its own value at a forward and a
    // hole).
    let push = |i: usize, cells: &dyn Fn(usize) -> F64| -> (bool, F64) {
        match column(i >> r, i & (width - 1)).0 {
            None => (true, w[i]),
            Some(p) => {
                let pair = &circuit.pairs[p];
                let formula = &circuit.formulas[pair.formula];
                if pair.pulls {
                    (true, formula.eval_k(cells))
                } else {
                    (false, w[i])
                }
            }
        }
    };
    let (alpha8, beta8) = (Ex8::splat(alpha), Ex8::splat(beta_));
    let one8 = Ex8::splat(F192::ONE);
    let zero8 = Ex8::splat(F192::ZERO);
    let lane_x = Kx8::new(std::array::from_fn(|l| point(l << r)));
    let cell_x: Vec<F64> = (0..width).map(point).collect();
    chunks_mut4(o0, o1, o2, p, run, |chunk, o0, o1, o2, op| {
        let start = chunk * run;
        let mut den: Vec<Ex8> = Vec::with_capacity(run / 8);
        let mut num: Vec<Ex8> = Vec::with_capacity(run / 8);
        let mut cells = vec![Kx8::splat(F64::ZERO); width];
        for t in 0..run / tile {
            let row0 = (start + t * tile) >> r;
            let at = |l: usize, c: usize| ((row0 + l) << r) + c;
            for (c, cell) in cells.iter_mut().enumerate() {
                *cell = Kx8::new(std::array::from_fn(|l| w[at(l, c)]));
            }
            // `ω_i` is linear in `i`'s bits: `ω_(row0 2^r) + ω_(l 2^r) + ω_c` (`row0` a multiple of 8, `c < 2^r`).
            let x_tile = point(row0 << r);
            for c in 0..width {
                let x = lane_x + Kx8::splat(x_tile + cell_x[c]);
                let sigma = Kx8::new(std::array::from_fn(|l| sigma_on_v[at(l, c)]));
                let kappa = Kx8::new(std::array::from_fn(|l| circuit.kappa[at(l, c)]));
                let d_pull = alpha8 + Ex8::from_k(cells[c]) + beta8.mul_k(x);
                let rest = alpha8 + Ex8::from_k(kappa) + beta8.mul_k(sigma);
                let (pair, whole) = column(row0, c);
                let own: [F64; 8] = if whole {
                    let (pull, own) = match pair {
                        None => (true, cells[c]),
                        Some(p) => {
                            let pair = &circuit.pairs[p];
                            if pair.pulls {
                                (true, compiled[pair.formula].eval(&cells, gammas).limbs()[0])
                            } else {
                                (false, cells[c])
                            }
                        }
                    };
                    if pull {
                        let d_push = rest + Ex8::from_k(own);
                        den.push(d_pull * d_push);
                        num.push(d_pull + d_push);
                    } else {
                        den.push(one8);
                        num.push(zero8);
                    }
                    lanes(own)
                } else {
                    let (d_pull, rest) = (d_pull.to_array(), rest.to_array());
                    let (mut d, mut u, mut own) = ([F192::ONE; 8], [F192::ZERO; 8], [F64::ZERO; 8]);
                    for l in 0..8 {
                        let i = at(l, c);
                        let base = i & !(width - 1);
                        let (pull, value) = push(i, &|c| w[base + c]);
                        own[l] = value;
                        if pull {
                            let d_push = rest[l] + F192::from(value);
                            (d[l], u[l]) = (d_pull[l] * d_push, d_pull[l] + d_push);
                        }
                    }
                    den.push(ex8(d));
                    num.push(ex8(u));
                    own
                };
                for (l, &x) in own.iter().enumerate() {
                    op[t * tile + (l << r) + c] = x;
                }
            }
        }
        // The batched inversion, eight chains in the lanes.
        let mut prefix = Vec::with_capacity(den.len());
        let mut acc = one8;
        for &d in &den {
            prefix.push(acc);
            acc = acc * d;
        }
        let mut inv = ex8(acc.to_array().map(|x| x.inv()));
        for (d, &pre) in den.iter_mut().zip(&prefix).rev() {
            let next = inv * *d;
            *d = inv * pre;
            inv = next;
        }
        for (k, (&d, &u)) in den.iter().zip(&num).enumerate() {
            let (t, c) = (k / width, k % width);
            let h = (u * d).to_array();
            for (l, x) in h.iter().enumerate() {
                let j = t * tile + (l << r) + c;
                (o0[j], o1[j], o2[j]) = (F64(x.c0), F64(x.c1), F64(x.c2));
            }
        }
    });
}

/// `f`'s values on `offset + V_{m+1}` from its novel coefficients (`2^m` of them: degree below `2^m`): one transform
/// of `2^m` points on each coset `offset + ω_{c 2^m} + V_m`, `c < 2`; the values of the transform of the coefficients
/// zero-padded to `2^(m+1)`, whose top layer copies them to the two halves.
fn on_extension(novel: &[F64], m: usize, offset: F64) -> Vec<F64> {
    let n = novel.len();
    assert_eq!(n, 1 << m);
    // The coefficients twice, in parallel runs.
    let mut out: Vec<F64> = if n >= COPY_RUN {
        parallel::map_collect(2 * n / COPY_RUN, |k| -> [F64; COPY_RUN] {
            let at = (k * COPY_RUN) & (n - 1);
            novel[at..at + COPY_RUN].try_into().expect("a run")
        })
        .into_flattened()
    } else {
        (0..2 * n).map(|i| novel[i & (n - 1)]).collect()
    };
    for (c, quarter) in out.chunks_mut(n).enumerate() {
        ntt::values(quarter, offset + point(c << m));
    }
    out
}

/// Prove that `w` satisfies `circuit` with the public data `values` (the public input's words in the seed): the
/// stream, the committed tables and the claims. Panics if `w` does not (the public side's sum differs).
pub fn prove(
    circuit: &Circuit,
    spec: &Spec,
    setup: &Setup,
    iv: &[u8; 32],
    public_input: &[u8; 32],
    values: &[PublicValue],
    w: &[F64],
) -> Proved {
    prove_with(circuit, spec, setup, iv, public_input, values, w, true)
}

/// [`prove`], with `check` false for any `w`: the proof is then made as for a witness (for the tests that show a
/// claim is false).
#[allow(clippy::too_many_arguments)]
pub fn prove_with(
    circuit: &Circuit,
    spec: &Spec,
    setup: &Setup,
    iv: &[u8; 32],
    public_input: &[u8; 32],
    values: &[PublicValue],
    w: &[F64],
    check: bool,
) -> Proved {
    let (m, r, n) = (circuit.log_n, circuit.log_row, circuit.n());
    assert_eq!(w.len(), n);
    assert_eq!(values.len(), circuit.reads.len());
    let mut timings = vec![];
    let mut clock = Instant::now();
    let mut lap = |name: &'static str, timings: &mut Vec<(&'static str, f64)>| {
        timings.push((name, clock.elapsed().as_secs_f64()));
        clock = Instant::now();
    };
    let [wv, qv, _] = stack_vars(m);
    let mut writer = KeccakWriter::new(super::verifier::seed(iv, public_input, &frame_words(values)));
    for (read, value) in circuit.reads.iter().zip(values) {
        match (*read, *value) {
            (Read::Integer(bytes), PublicValue::Integer(x)) => writer.send_integer(x, bytes as usize),
            (Read::Root, PublicValue::Root(bytes)) => writer.send_root(&bytes),
            (Read::Scalar, PublicValue::Scalar(x)) => writer.send(E::from(x)),
            (Read::Narrow, PublicValue::Scalar(x)) => writer.send_narrow(E::from(x)),
            (Read::Frame(_), PublicValue::Word(_)) => {}
            other => panic!("a public value of another kind than its read: {other:?}"),
        }
    }
    let public = public_scalars(public_input, values);

    // W: the B coefficients of w.
    let w_novel = ntt::coefficients_cols_of(&[w], F64::ZERO).pop().expect("one column");
    let w_b = b_coefficients(&w_novel);
    // Kept with its codeword (twice the stack, 256 MB at `2^24` positions), as `Q`: its opening reads the rows its
    // first queries open from it. The stack is `w_b` itself, its leading lanes.
    let witness_committed = pcs_claim::commit_words(&w_b, wv, true);
    writer.send_root(&witness_committed.root);
    writer.send(E::from(witness_committed.ood));
    let [alpha, beta_, gamma] = [(); 3].map(|_| F192::from(writer.sample()));
    lap("W: transform, commit", &mut timings);

    // h on V_m, limb by limb, and P_v ([`h_on_v`]).
    let gammas = super::circuit::gamma_powers(gamma, circuit.max_gamma());
    // Q's stack, built in place: sixteen slots of `N` words (`verifier::QUOTIENT_SLOTS`): `h`, a zero slot, `q`'s two
    // digits, for each limb, then a zero slot, `P`, `q_P`'s two digits. Every word of it but the zero slots' is written
    // below (`h_on_v`, then `quotient_on_extension`), whatever it holds: those are zeroed.
    let mut stack: Vec<F64> = setup.stack(QUOTIENT_SLOTS * n);
    for slot in EMPTY_SLOTS {
        stack[slot * n..(slot + 1) * n].iter_mut().for_each(|x| *x = F64::ZERO);
    }
    let run = n.min(1 << 12);
    // The ports' values `F_J` in `Spec::phi`'s order.
    let port_values: Vec<F192> = spec
        .phi
        .iter()
        .flat_map(|(_, terms)| terms.iter().map(|t| t.value.eval(&|c| public[c], &gammas)))
        .collect();
    let holes = holes(circuit, w, &public, &gammas);
    assert!(
        !check || holes.iter().all(|(_, t)| *t == F192::ZERO),
        "a port does not hold: the witness does not satisfy the circuit"
    );
    {
        // Slots `4 l` (`h`), `4 l + 1` (zero), `4 l + 2, 4 l + 3` (`q`) for each limb; `12` (zero), `13` (`P`), `14, 15`
        // (`q_P`).
        let (limb0, rest) = stack.split_at_mut(4 * n);
        let (h0, limb0) = limb0.split_at_mut(n);
        let q0 = &mut limb0[n..];
        let (limb1, rest) = rest.split_at_mut(4 * n);
        let (h1, limb1) = limb1.split_at_mut(n);
        let q1 = &mut limb1[n..];
        let (limb2, rest) = rest.split_at_mut(4 * n);
        let (h2, limb2) = limb2.split_at_mut(n);
        let q2 = &mut limb2[n..];
        let (p, qp) = rest[n..].split_at_mut(n);
        debug_assert_eq!((h_slot(1), q_slot(1), P_SLOT, QP_SLOT), (4, 6, 13, 14));
        h_on_v(
            circuit,
            &setup.sigma_on_v,
            w,
            alpha,
            beta_,
            &gammas,
            run,
            [&mut *h0, &mut *h1, &mut *h2],
            p,
        );
        // `h = T / (d_pull d_push)` at the holes ([`holes`]: zero for a witness), `d_push = α + w + βσ` there.
        for &(i, t) in holes.iter().filter(|(_, t)| *t != F192::ZERO) {
            let value = alpha + F192::from(w[i]);
            let d = (value + beta_.mul_base(point(i))) * (value + beta_.mul_base(point(circuit.sigma[i] as usize)));
            let h = t * d.inv();
            (h0[i], h1[i], h2[i]) = (F64(h.c0), F64(h.c1), F64(h.c2));
        }
        // The four columns' transforms in the same dispatches.
        ntt::coefficients_cols(&mut [&mut *h0, &mut *h1, &mut *h2, &mut *p], F64::ZERO);
        // `Σ_V h` is `h`'s top novel coefficient (the claim `Q` opens at `(1^m, 0, …)`), read rather than summed.
        let sum = F192::new(h0[n - 1].0, h1[n - 1].0, h2[n - 1].0);
        assert!(
            !check || sum == F192::ZERO,
            "the copy argument's sum is not zero: the witness does not satisfy the circuit"
        );
        lap("h, P on V_m, their coefficients", &mut timings);
        quotient_on_extension(
            circuit,
            spec,
            setup,
            &w_novel,
            [h0, h1, h2],
            p,
            [alpha, beta_, gamma],
            &port_values,
            [q0, q1, q2],
            qp,
        );
    }
    lap("q, q_P on the extension coset, their coefficients", &mut timings);

    // Kept with its codeword (twice the stack, 4.3 GB at `2^24` positions) until its opening, which reads the rows its
    // first queries open from it rather than encode them again.
    let quotient = stack;
    let quotient_committed = pcs_claim::commit_words(&quotient, qv, true);
    writer.send_root(&quotient_committed.root);
    writer.send(E::from(quotient_committed.ood));
    let t = F192::from(writer.sample());
    lap("Q: table, commit", &mut timings);

    let digits: Vec<F192> = std::iter::successors(Some(t), |&x| Some(x * x + x))
        .take(m + 1)
        .collect();
    let eq = primitives::multilinear::eq_table(&digits[r..m]);
    let width = 1usize << r;
    let folds = parallel::map_reduce(
        eq.len() >> 6.min(m - r),
        || vec![F192::ZERO; width],
        |c| {
            let run = 1usize << 6.min(m - r);
            let mut acc = vec![F192::ZERO; width];
            for j in c * run..(c + 1) * run {
                for k in 0..width {
                    acc[k] += eq[j].mul_base(w_b[(j << r) + k]);
                }
            }
            acc
        },
        |mut a, b| {
            a.iter_mut().zip(b).for_each(|(x, y)| *x += y);
            a
        },
    );
    // ξ = κ(t) + β σ(t), from the setup's halves `κ` and `κ + σ`; `h(t)` is not sent (PI2.md §9).
    let setup_stack = &setup.words;
    let kappa_t = primitives::multilinear::mle_eval_par(&setup_stack[..n], &digits[..m]);
    let sum_t = primitives::multilinear::mle_eval_par(&setup_stack[n..2 * n], &digits[..m]);
    let xi = kappa_t + beta_ * (kappa_t + sum_t);
    // s = P(t) from its novel coefficients: `Σ_k P_k Π_l w_l^(k_l) = Π_l (1 + w_l) · MLE(P)(u)`, `u_l = w_l / (1 + w_l)`,
    // `Π_(l < m) (1 + w_l) = w_m / t`.
    let u: Vec<F192> = digits[..m].iter().map(|&x| x * (F192::ONE + x).inv()).collect();
    let p_stack = &quotient[P_SLOT * n..(P_SLOT + 1) * n];
    let s = primitives::multilinear::mle_eval_par(p_stack, &u) * digits[m] * t.inv();
    folds.iter().chain([&xi, &s]).for_each(|&x| writer.send(E::from(x)));
    let _rho = writer.sample();
    lap("t: the values", &mut timings);

    let stream = writer.stream;
    let (reduced, _) = super::verifier::verify(spec, iv, public_input, &frame_words(values), &stream, Checks::Enforce)
        .expect("the verifier accepts its own stream");
    Proved {
        stream,
        roots: [witness_committed.root, quotient_committed.root],
        witness: (w_b, witness_committed),
        quotient: (quotient, quotient_committed),
        reduced,
        timings,
    }
}

/// The five openings, one a claim: `W`'s, the setup's, `Q`'s identity, pushes and sum (the contract's order).
pub struct Openings {
    pub proofs: [fiat_shamir::transcript::Proof; 5],
}

/// The five claims, in the contract's order (`W`, the setup, `Q`'s identity, pushes and sum): each the EIP draft's
/// PCS claim on its commitment (the roots the proof commits, their out-of-domain answers, the setup's).
pub fn claims(log_n: usize, reduced: &Reduced<E>, roots: &[Hash; 2], setup_root: &Hash, setup_ood: F192) -> [PcsClaim; 5] {
    let [wv, qv, sv] = stack_vars(log_n);
    let pcs = |vars: usize, root: &Hash, ood: F192, c: &(Vec<E>, E)| {
        let (point, value) = claim(c);
        assert_eq!(point.len(), vars, "a point of the whole stack");
        PcsClaim {
            n: vars as u8,
            root: *root,
            ood,
            point,
            value,
        }
    };
    let [w_ood, q_ood] = reduced.oods.map(F192::from);
    reduced.claims().map(|(stack, c)| match stack {
        Pi2Stack::Witness => pcs(wv, &roots[0], w_ood, c),
        Pi2Stack::Setup => pcs(sv, setup_root, setup_ood, c),
        Pi2Stack::Quotient => pcs(qv, &roots[1], q_ood, c),
    })
}

pub fn open(proved: Proved, setup: &Setup) -> (Reduced<E>, [Hash; 2], Openings) {
    let Proved {
        roots,
        witness,
        quotient,
        reduced,
        ..
    } = proved;
    let m = setup.sigma_on_v.len().trailing_zeros() as usize;
    let profile = std::env::var_os("PI2_PROFILE").is_some();
    let timed = |name: &str, f: &mut dyn FnMut() -> fiat_shamir::transcript::Proof| {
        let clock = Instant::now();
        let proof = f();
        if profile {
            eprintln!("    open: {:7.3} s  {name}", clock.elapsed().as_secs_f64());
        }
        proof
    };
    let [cw, cs, cq, cp, cz] = claims(m, &reduced, &roots, &setup.root(), setup.ood());
    let (w_words, w_commitment) = witness;
    let (q_words, q_commitment) = quotient;
    let pw = timed("W", &mut || pcs_claim::open_words(&w_words, &w_commitment, &cw));
    let ps = timed("setup", &mut || pcs_claim::open_words_keeping(&setup.words, &setup.commitment, &cs));
    // Q's three claims together: their lane rounds read the stack twice in all rather than twice each.
    let clock = Instant::now();
    let [pq, pp, pz]: [_; 3] = pcs_claim::open_words_batch(&q_words, &q_commitment, &[cq, cp, cz])
        .try_into()
        .unwrap_or_else(|_| unreachable!("three proofs"));
    if profile {
        eprintln!("    open: {:7.3} s  Q: identity, pushes, sum", clock.elapsed().as_secs_f64());
    }
    let proofs = [pw, ps, pq, pp, pz];
    drop(w_words);
    // Q's stack back to the setup's spare, for the next proof's.
    if let Ok(mut spare) = setup.spare.lock() {
        *spare = q_words;
    }
    (reduced, roots, Openings { proofs })
}

/// What the block's openings prove of π2's five claims: each opening with `pcs_claim::verify_claim` (the EIP draft's
/// `pcs_verify`).
pub fn verify_openings(
    log_n: usize,
    reduced: &Reduced<E>,
    roots: &[Hash; 2],
    setup_root: &Hash,
    setup_ood: F192,
    openings: &Openings,
) -> Result<(), ::verifier::VerifierError> {
    for (claim, proof) in claims(log_n, reduced, roots, setup_root, setup_ood).iter().zip(&openings.proofs) {
        pcs_claim::verify_claim(claim, &pcs_claim::wire_proof(proof))?;
    }
    Ok(())
}

/// Whether each claim holds on the stacks (by evaluation), in the contract's order: `W`, the setup, `Q`'s identity,
/// pushes and sum.
pub fn claims_hold(proved: &Proved, setup: &Setup) -> [bool; 5] {
    let holds = |words: &[F64], c: &(Vec<E>, E)| {
        let (point, value) = claim(c);
        pcs_claim::evaluate_lanes(words, &point) == value
    };
    proved.reduced.claims().map(|(stack, c)| match stack {
        Pi2Stack::Witness => holds(&proved.witness.0, c),
        Pi2Stack::Setup => holds(&setup.words, c),
        Pi2Stack::Quotient => holds(&proved.quotient.0, c),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `Q`'s slots: `h`, `q` (two digits) of three limbs, `P`, `q_P` (two digits) and four zero slots, sixteen in all,
    /// each where its bits say (`digit + 2 kind + 4 limb`).
    #[test]
    fn quotient_slots_are_their_bits() {
        let mut used = vec![false; QUOTIENT_SLOTS];
        let mut take = |slot: usize, digit: usize, kind: usize, limb: usize| {
            assert_eq!(slot, digit + 2 * kind + 4 * limb);
            assert!(!std::mem::replace(&mut used[slot], true), "slot {slot} once");
        };
        for l in 0..3 {
            take(h_slot(l), 0, 0, l);
            take(q_slot(l), 0, 1, l);
            take(q_slot(l) + 1, 1, 1, l);
        }
        take(P_SLOT, 1, 0, 3);
        take(QP_SLOT, 0, 1, 3);
        take(QP_SLOT + 1, 1, 1, 3);
        for slot in EMPTY_SLOTS {
            assert!(!used[slot], "slot {slot} is zero");
        }
        assert_eq!(used.iter().filter(|&&u| u).count() + EMPTY_SLOTS.len(), QUOTIENT_SLOTS);
    }
}
