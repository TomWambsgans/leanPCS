// Part of this repository. The reduction's shape (one quotient identity at `t`, claims on the tables that hold the
// polynomials, the Cantor digits and the extension's coordinates) follows crates/membership/quotient/src/protocol.rs (`reduce`,
// adapted there from leanVM's `flock::quotient`, branch PCS-openings-aggregation, commit 651453c6); the transcript is
// crates/leanvm_statement's Keccak-256 chain (`KeccakChannel`). MIT OR Apache-2.0; see AGENTS.md.
//! π2's verifier, generic over the scalar (`leanvm_statement::scalar::Scalar`): on `E` with the Keccak-256 chain it is
//! the contract's verifier in Rust ([`verify`]); on the recorder's symbol it is the graph the contract is compiled from
//! (`pi2::contract`). See `PI2.md` §2 for the protocol.
//!
//! The stream: the public data ([`Read`]s), `W`'s commitment (its root, its out-of-domain answer), then `α, β, γ`;
//! `Q`'s commitment, then `t`; the row's `2^r` fold values `a_k`, `ξ = κ(t) + β σ(t)` and `s = P(t)` (`P` the internal
//! pushes, committed in `Q`), then `ρ`. At `t` the verifier computes, as fractions with one inversion at the end:
//!
//! 1. the digits `w_l = w_l(t)`, `w_{l+1} = w_l^2 + w_l`, `l ≤ m + 1`;
//! 2. the row's cells `v_c = w(t + ω_c) = Σ_k a_k eq(k, (w_l + ω_{c >> l})_{l<r})`;
//! 3. every pair's indicator `I_p(t) = w_m / (Ẑ_s(t) + Ẑ_s(c_p))`, the indicators of a group (pairs of one role and
//!    formula) summed as one fraction `N_g / D_g`;
//! 4. the internal pushes `P_v(t) = v_0 + w_m A / B`, `A / B = Σ_g (N_g / D_g)(E_g(v_{c ⊕ k_g}) + v_0)` over the
//!    pulling groups, accumulated as one fraction;
//! 5. the ports' term: `Φ_k(t) = w_m G_n / G_d`, `G_n / G_d = Σ_J F_J / (w_r + ω_{y_J})` over the ports of role `k`
//!    of nonzero value (`y_J` the hole's row), and `R_n / R_d = Σ_g (N_g / D_g)(E_g + Δ + Φ_{k_g})` over the port
//!    groups, `Δ = d_pull + d_push`, `d_pull = α + v_0 + β t`, `d_push = α + s + ξ`: the identity's right side is
//!    `(1 + 1_S) Δ + T = Δ + w_m R_n / R_d`;
//! 6. the claims on `Q` (`PI2.md` §2): the identity `h d_pull d_push + q w_m = Δ + w_m R_n / R_d` is one combination
//!    of `h(t)` and `q(t)` (`c_h = d_pull d_push`, `c_q = w_m`, `Y = c_h + c_q`, `ρ' = w_m / Y`); `P(t) = s` and the
//!    definition `w_m q_P(t) = s + P_v(t)` are combined by `ρ`. Each claim is a point of `Q`'s whole stack (the EIP
//!    draft's PCS claim): its sixteen slots of `2^m` are `slot = digit + 2 kind + 4 limb` ([`QUOTIENT_SLOTS`]), `h`
//!    and `q` of limbs 0..2 at kinds 0 and 1, `P` (at digit 1) and `q_P` at limb code 3; so the identity's claim, at
//!    `(u, ρ', y_0, y_1)`, also weighs `P` and `q_P` (by `y_0 y_1`), whose values the claim at `(u, ρ, 1, 1)` fixes;
//! 7. one inversion of `R_d Y · w_{m+1} · B · c_h D_n` (nonzero required; `D_n = B (α + P_v(t) + ξ)`), and the digits'
//!    inverses down from `1/w_{m+1}`: `1/w_l = (1 + w_l) / w_{l+1}`;
//!
//! and leaves five claims, each a point of a commitment's whole stack (its coordinates past the table's zero:
//! [`stack_vars`]): `W` at `(ρ, ρ², …, ρ^{2^{r-1}}, w_r, …, w_{m-1})`, value `Σ_k eq(ρ⃗, k) a_k`; `Q` at
//! `(u_0, …, u_m, ρ', y_0, y_1)`, `u_l = w_l / (1 + w_l)` (the identity, and `P`, `q_P` by `y_0 y_1`), at
//! `(u_0, …, u_m, ρ, 1, 1)` (`P` and `q_P` alone) and at `(1^m, 0, 0, y_0, y_1)` (the top coefficient of `h`: `Σ_V h`),
//! value `0`; the setup (its halves `κ` and `κ + σ`) at `(w_0, …, w_{m-1}, β)`, value `ξ`.

use leanvm_statement::VerifierError;
use leanvm_statement::field::E;
use leanvm_statement::scalar::{Scalar, enter};
use leanvm_statement::transcript::{Channel, Checks, KeccakChannel, keccak256, statement_words};
use primitives::field::{F64, F192};
use quotient::domain::point;

use super::circuit::{Circuit, Coeff, Formula, Lin, Read, coset_constants, pair_constants};

/// The transcript's 16-byte name.
pub const NAME: [u8; 16] = *b"leanvm-rec-pi2v3";

/// The smallest stack leanVM's WHIR takes.
pub const MIN_LOG_STACK: usize = 15;

/// The smallest stack leanerVM's certified parameters cover (`params/whir_params.py --large`), kept for the stacks:
/// circuits of `2^CERTIFIED_FROM` positions or more commit no smaller stack (a `W` of `2^23` words takes a `2^24`
/// stack, half its lanes absent); smaller circuits, the tests', take [`MIN_LOG_STACK`].
pub const MIN_CERTIFIED_STACK: usize = 24;
pub const CERTIFIED_FROM: usize = 20;

/// The variables of π2's three committed stacks at `2^log_n` positions: `W` (its `2^m` words), `Q` (sixteen slots of
/// `2^m`, [`QUOTIENT_SLOTS`]) and the setup (`κ` then `κ + σ`: `2^(m+1)` words), each at least the smallest stack.
pub fn stack_vars(log_n: usize) -> [usize; 3] {
    let least = if log_n >= CERTIFIED_FROM {
        MIN_CERTIFIED_STACK
    } else {
        MIN_LOG_STACK
    };
    [log_n.max(least), (log_n + 4).max(least), (log_n + 1).max(least)]
}

/// `Q`'s sixteen slots of `2^m` words: slot `digit + 2 kind + 4 limb`. `h` (one digit) and `q` (two) of limbs 0, 1, 2
/// at kinds 0 and 1; at limb code 3, `P` (one chunk, at digit 1) and `q_P` (two digits, kind 1). Slots `1, 5, 9`
/// (`h`'s second digit) and `12` are zero.
pub const QUOTIENT_SLOTS: usize = 16;

/// The slot of `h`'s limb `l`, of `q`'s limb `l` digit 0 (digit 1 the next), of `P`, of `q_P`'s digit 0.
pub fn h_slot(l: usize) -> usize {
    4 * l
}
pub fn q_slot(l: usize) -> usize {
    2 + 4 * l
}
pub const P_SLOT: usize = 13;
pub const QP_SLOT: usize = 14;
/// The zero slots.
pub const EMPTY_SLOTS: [usize; 4] = [1, 5, 9, 12];

/// A pair as the verifier needs it: its block size `s` and `Z_{U_s}(c_p)`.
#[derive(Clone, Copy, Debug)]
pub struct SpecPair {
    pub log_rows: usize,
    /// `Ẑ_s(c_p)`, the block's normalised vanishing polynomial ([`Spec::c`]) at the coset's base.
    pub z: F64,
}

/// The pairs of one role and one formula (pulling, or all pull-less): the sum of their indicators multiplies the
/// formula's value, and is one fraction `N_g / D_g` (`D_g` the product of the pairs' denominators).
#[derive(Clone, Debug)]
pub struct Group {
    pub role: usize,
    pub formula: Formula,
    pub pulls: bool,
    pub pairs: Vec<usize>,
}

/// A port of nonzero value in its role's `Φ`: the row of its hole, and its value `F_J` on the public scalars.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortTerm {
    pub row: u32,
    pub value: Lin,
}

/// What the verifier is built from: the circuit's shape, its pairs grouped by (role, formula), the ports.
#[derive(Clone, Debug)]
pub struct Spec {
    pub log_n: usize,
    pub log_row: usize,
    pub pairs: Vec<SpecPair>,
    pub groups: Vec<Group>,
    /// The pull-less pairs (the ports').
    pub pull_less: Vec<usize>,
    /// The normalised vanishing polynomials `Ẑ_s = Z_{U_s} / Π_{j ≤ s} e_j` (linear coefficient 1):
    /// `Ẑ_s(x) = Ẑ_{s-1}(x) + c_s Ẑ_{s-1}(x)^2`, `c_s = Π_{j < s} e_j / e_s`; this is `c_1, …`. Then
    /// `I_p(x) = Z_V(x) / (Ẑ_s(x) + Ẑ_s(c_p))`.
    pub c: Vec<F64>,
    pub reads: Vec<Read>,
    /// The ports of nonzero value by their role `k` (in the order of the circuit's public terms): `Φ_k(x) = Σ_J F_J
    /// w_m(x) / (w_r(x) + ω_{y_J})`, which is `F_J` at the hole of row `y_J` (`w_r(ω_i) = ω_{i >> r}`,
    /// `w_m = w_{m-r} ∘ w_r`, `w_{m-r}' = 1`) and zero at the other rows' (`PI2.md` §1). The ports of value zero (π1's
    /// zero checks and their padding) are in no `Φ`.
    pub phi: Vec<(usize, Vec<PortTerm>)>,
    /// The circuit's public terms (ports), all of them.
    pub ports: usize,
    pub max_gamma: usize,
}

/// `Ẑ_s`'s recursion constants `c_1 … c_count`.
pub fn normalised_constants(e: &[F64]) -> Vec<F64> {
    let mut norm = F64::ONE;
    e.iter()
        .map(|&x| {
            let c = norm * x.inv();
            norm *= x;
            c
        })
        .collect()
}

/// Whether a linear form is zero (a port of value zero: a zero check, its padding).
fn is_zero(l: &Lin) -> bool {
    l.terms.is_empty() && l.constant.is_none_or(|c| c.field() == F192::ZERO)
}

impl Spec {
    /// The verifier of `circuit`, which must be valid ([`Circuit::validate`]: no formula reads a
    /// hole, `κ` only at expression slots).
    pub fn of(circuit: &Circuit) -> Self {
        circuit.validate().unwrap_or_else(|e| panic!("the circuit is not valid: {e}"));
        let (m, r, n) = (circuit.log_n, circuit.log_row, circuit.n());
        let e = coset_constants(r, m - r);
        let pairs: Vec<SpecPair> = circuit
            .pairs
            .iter()
            .map(|p| {
                let (z, norm) = pair_constants(p, r, &e);
                SpecPair {
                    log_rows: p.log_rows,
                    z: z * norm.inv(),
                }
            })
            .collect();
        let mut groups: Vec<Group> = Vec::new();
        for (index, p) in circuit.pairs.iter().enumerate() {
            let formula = &circuit.formulas[p.formula];
            match groups
                .iter_mut()
                .find(|g| g.role == p.role && g.pulls == p.pulls && g.formula == *formula)
            {
                Some(g) => g.pairs.push(index),
                None => groups.push(Group {
                    role: p.role,
                    formula: formula.clone(),
                    pulls: p.pulls,
                    pairs: vec![index],
                }),
            }
        }
        // Each outside tag's hole (the position pushing to it; `validate` makes it a pull-less one).
        let hole: std::collections::HashMap<u32, usize> =
            (0..n).filter(|&i| circuit.sigma[i] as usize >= n).map(|i| (circuit.sigma[i], i)).collect();
        let mut phi: Vec<(usize, Vec<PortTerm>)> = Vec::new();
        for term in circuit.public.iter().filter(|t| !is_zero(&t.value)) {
            let at = hole[&term.tag];
            let (role, row) = (at & ((1 << r) - 1), (at >> r) as u32);
            let port = PortTerm {
                row,
                value: term.value.clone(),
            };
            match phi.iter_mut().find(|(k, _)| *k == role) {
                Some((_, terms)) => terms.push(port),
                None => phi.push((role, vec![port])),
            }
        }
        Self {
            log_n: m,
            log_row: r,
            pairs,
            groups,
            pull_less: (0..circuit.pairs.len()).filter(|&p| !circuit.pairs[p].pulls).collect(),
            c: normalised_constants(&e),
            reads: circuit.reads.clone(),
            phi,
            ports: circuit.public.len(),
            max_gamma: circuit.max_gamma(),
        }
    }

    /// Scalars the proof sends after the roots: the `2^r` fold values, `ξ = κ(t) + β σ(t)` and `s = P(t)`.
    pub fn values(&self) -> usize {
        (1 << self.log_row) + 2
    }

    /// The largest block size.
    pub fn max_log_rows(&self) -> usize {
        self.pairs.iter().map(|p| p.log_rows).max().unwrap_or(0)
    }
}

/// What [`reduce`] leaves: the public scalars, `W`'s and `Q`'s commitments, and the five claims, each a point of its
/// commitment's whole stack and a value.
#[derive(Clone, Debug)]
pub struct Reduced<S> {
    pub public: Vec<S>,
    /// `transcript::pair_point` of every public scalar: the coordinates of π1-rec3's paired batch, which its calls
    /// take (`CallWord::Pair`); a contract computes only those its calls read.
    pub pair_points: Vec<[S; 2]>,
    pub roots: [[S; 2]; 2],
    /// `W`'s and `Q`'s out-of-domain answers (`crates/pcs_claim`), read after their roots.
    pub oods: [S; 2],
    pub witness: (Vec<S>, S),
    /// `Q`'s identity (with `P`, `q_P` weighed by `y_0 y_1`).
    pub quotient: (Vec<S>, S),
    /// `Q`'s `P` and `q_P`, combined by `ρ`.
    pub pushes: (Vec<S>, S),
    pub sum: (Vec<S>, S),
    pub setup: (Vec<S>, S),
}

/// π2's three committed stacks, which its claims are on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pi2Stack {
    /// `W`, the witness.
    Witness,
    /// The setup (`κ`, `κ + σ`): its commitment is the contract's constant.
    Setup,
    /// `Q`, the quotients and the pushes.
    Quotient,
}

impl<S> Reduced<S> {
    /// The five claims in the contract's order, each with its stack: `W`, the setup, then `Q`'s identity, pushes and
    /// sum.
    pub fn claims(&self) -> [(Pi2Stack, &(Vec<S>, S)); 5] {
        [
            (Pi2Stack::Witness, &self.witness),
            (Pi2Stack::Setup, &self.setup),
            (Pi2Stack::Quotient, &self.quotient),
            (Pi2Stack::Quotient, &self.pushes),
            (Pi2Stack::Quotient, &self.sum),
        ]
    }
}

fn base<S: Scalar>(x: F64) -> S {
    S::constant(E::new(x.0, 0, 0))
}

fn ext<S: Scalar>(x: F192) -> S {
    S::constant(x.into())
}

fn coeff<S: Scalar>(c: &Coeff, gammas: &[S]) -> S {
    let value = ext::<S>(c.field());
    if c.gamma == 0 {
        value
    } else {
        value * gammas[c.gamma as usize]
    }
}

fn lin<S: Scalar>(l: &Lin, cell: &dyn Fn(usize) -> S, gammas: &[S]) -> S {
    let constant = l.constant.map_or(S::zero(), |c| coeff(&c, gammas));
    l.terms.iter().fold(constant, |acc, (c, cell_index)| {
        let v = cell(*cell_index as usize);
        acc + if c.is_one() { v } else { coeff(c, gammas) * v }
    })
}

/// A formula on `S`, its cells given.
pub fn formula<S: Scalar>(f: &Formula, cell: &dyn Fn(usize) -> S, gammas: &[S]) -> S {
    f.products.iter().fold(lin(&f.lin, cell, gammas), |acc, (c, a, b)| {
        let p = lin(a, cell, gammas) * lin(b, cell, gammas);
        acc + if c.is_one() { p } else { coeff(c, gammas) * p }
    })
}

/// What the verifier needs of a scalar beyond `Scalar`: its limbs above the lowest, `x >> 64 = c_1 + c_2 Y` and
/// `x >> 128 = c_2` for `x = c_0 + c_1 Y + c_2 Y²`. On the recorder's symbol they are `Node::Bits(x, 64, 64)` and
/// `Node::Bits(x, 128, 64)`: one `SHR` each in the contract (a 64-bit field takes no mask).
pub trait Limbs: Scalar {
    fn shifted(self) -> [Self; 2];
}

impl Limbs for E {
    fn shifted(self) -> [Self; 2] {
        [E::new(self.c1, self.c2, 0), E::new(self.c2, 0, 0)]
    }
}

impl Limbs for leanvm_statement::evm::record::Sym {
    fn shifted(self) -> [Self; 2] {
        [self.bits(64, 64), self.bits(128, 64)]
    }
}

/// `x^(2^64)`: `(c_0, c_1, c_2) ↦ (c_0, c_2, c_1 + c_2)` (`Y^(2^64) = Y²`), that is `x + (Y + Y²)(x >> 64) + (1 + Y²)(x >> 128)`.
pub fn frobenius<S: Limbs>(x: S) -> S {
    let [u, v] = x.shifted();
    let (y, y2) = (F192::Y, F192::Y * F192::Y);
    x + ext::<S>(y + y2) * u + ext::<S>(F192::ONE + y2) * v
}

/// `x^-1` for a nonzero `x`, by its norm to `K`: `m = x^(2^64) x^(2^128)` makes `N = x m` the norm, in `K`, whose
/// inverse is `N^(2^64 - 2)` by Itoh–Tsujii (`t_k = N^(2^k - 1)`, the chain `1, 2, 3, 6, 7, …, 62, 63`: 63 squarings, 10
/// products); then `x^-1 = m N^-1`. Two Frobenius maps and 76 products (crates/membership/quotient's `protocol::inverse`).
pub fn inverse<S: Limbs>(x: S) -> S {
    let f = frobenius(x);
    let m = f * frobenius(f);
    let norm = x * m;
    let (mut t, mut k) = (norm, 1usize);
    for bit in (0..5).rev() {
        let mut s = t;
        for _ in 0..k {
            s = s.square();
        }
        t = s * t;
        k *= 2;
        if (63 >> bit) & 1 == 1 {
            t = t.square() * norm;
            k += 1;
        }
    }
    debug_assert_eq!(k, 63);
    m * t.square()
}

/// The two coordinates of the extension over `K` and the scale of their weights `(1, Y, Y², Y³)`.
pub fn extension() -> ([F192; 2], F192) {
    quotient::protocol::extension()
}

/// The verifier: the public data and the proof read from `channel`, down to the five claims. `statement` is the
/// public input's four words. It rejects only a challenge at which a denominator vanishes.
pub fn reduce<S: Limbs, C: Channel<S>>(
    spec: &Spec,
    statement: [S; 4],
    channel: &mut C,
) -> Result<Reduced<S>, VerifierError> {
    let (m, r) = (spec.log_n, spec.log_row);
    let one = S::one();
    let mut public = statement.to_vec();
    for read in &spec.reads {
        match *read {
            Read::Integer(bytes) => public.push(channel.next_integer(bytes as usize)?),
            Read::Root => public.extend(channel.next_root()?),
            Read::Scalar => public.push(channel.next_scalar()?),
            Read::Narrow => public.push(channel.next_narrow()?),
            Read::Frame(_) => public.extend(channel.next_frame()?),
        }
    }
    // Each commitment: its root, then its out-of-domain answer, which binds the root to one polynomial before the
    // challenges (docs/PCS_CLAIM.md).
    let witness_root = channel.next_root()?;
    let witness_ood = channel.next_scalar()?;
    let [alpha, beta, gamma] = [(); 3].map(|_| channel.sample());
    let quotient_root = channel.next_root()?;
    let quotient_ood = channel.next_scalar()?;
    let t = channel.sample();
    let a = channel.next_scalars(1 << r)?;
    let xi = channel.next_scalar()?;
    let s = channel.next_scalar()?;
    let rho = channel.sample();

    let w = {
        let _phase = enter("pi2: digits");
        let mut w = vec![t];
        for l in 0..m + 1 {
            let x = w[l];
            w.push(x.square() + x);
        }
        w
    };

    // The row's cells: fold the top variable first, each fold splitting by the next bit of `c`. Siblings `2k`, `2k + 1`
    // fold at `z` and `z + 1` (`ω_{2k+1} = ω_{2k} + β_0`, `β_0 = 1`): the odd one is the even one plus the difference
    // `p_j + p_{j+half}`, no product (`PI2.md` §9, lever 3a): `r 2^(r-1)` products, not `r 2^r`.
    let cells = {
        let _phase = enter("pi2: the row's cells (fold)");
        let mut layer: Vec<Vec<S>> = vec![a.clone()];
        for l in (0..r).rev() {
            let half = 1 << l;
            let mut next: Vec<Vec<S>> = Vec::with_capacity(2 * layer.len());
            for (k, parent) in layer.iter().enumerate() {
                let z = w[l] + base::<S>(point(2 * k));
                let d: Vec<S> = (0..half).map(|j| parent[j] + parent[j + half]).collect();
                let even: Vec<S> = (0..half).map(|j| parent[j] + z * d[j]).collect();
                let odd: Vec<S> = (0..half).map(|j| even[j] + d[j]).collect();
                next.push(even);
                next.push(odd);
            }
            layer = next;
        }
        layer.into_iter().map(|v| v[0]).collect::<Vec<S>>()
    };
    let v0 = cells[0];

    // `Ẑ_s(t)` for every block size.
    let zt = {
        let _phase = enter("pi2: indicators (block vanishing polynomials)");
        let mut zt = vec![t];
        for s in 1..=spec.max_log_rows() {
            let z = zt[s - 1];
            zt.push(z + base::<S>(spec.c[s - 1]) * z.square());
        }
        zt
    };

    // Each group's indicators, summed: `Σ_p 1/d_p = N_g / D_g`, by `N ← N d + D`, `D ← D d`. `Z_V(t) = w_m`
    // multiplies every indicator: it is factored out.
    let fraction = |dens: &mut dyn Iterator<Item = S>| -> (S, S) {
        let first = dens.next().expect("a denominator");
        dens.fold((one, first), |(n, d), x| (n * x + d, d * x))
    };
    let groups: Vec<(S, S)> = {
        let _phase = enter("pi2: indicators (denominators)");
        spec.groups
            .iter()
            .map(|g| {
                fraction(
                    &mut g
                        .pairs
                        .iter()
                        .map(|&p| zt[spec.pairs[p].log_rows] + base::<S>(spec.pairs[p].z)),
                )
            })
            .collect()
    };
    let gammas = leanvm_statement::scalar::powers(gamma, spec.max_gamma + 1);

    // `Φ_k(t) / w_m = G_n / G_d = Σ_J F_J / (w_r + ω_{y_J})` for each port role: `N ← N d + D F`, `D ← D d`.
    let phis: Vec<(usize, S, S)> = {
        let _phase = enter("pi2: public side (ports)");
        spec.phi
            .iter()
            .map(|(role, terms)| {
                let mut terms = terms
                    .iter()
                    .map(|j| (lin(&j.value, &|c| public[c], &gammas), w[r] + base::<S>(point(j.row as usize))));
                let (f, d) = terms.next().expect("a port");
                let (n, d) = terms.fold((f, d), |(n, d), (f, x)| (n * x + d * f, d * x));
                (*role, n, d)
            })
            .collect()
    };

    let d_pull = alpha + v0 + beta * t;
    let d_push = alpha + s + xi;
    let delta = d_pull + d_push;
    let w_phi: Vec<(usize, S, S)> = phis.iter().map(|&(k, n, d)| (k, w[m] * n, d)).collect();

    // The internal pushes `A / B = Σ_g (N_g / D_g)(E_g + v_0)` over the pulling groups, one fraction: a group of one
    // pair adds `X / d` (3 products), a larger one its `N_g X / D_g` (4). The ports' `R_n / R_d = Σ_g (N_g / D_g)(E_g +
    // Δ + Φ_k)` likewise, `E_g + Δ + Φ_k = ((E_g + Δ) G_d + w_m G_n) / G_d`.
    let (num, den, r_num, r_den) = {
        let _phase = enter("pi2: push formulas");
        let add = |acc: (Option<S>, Option<S>), term: S, denominator: S| match acc {
            (Some(a), Some(b)) => (Some(a * denominator + b * term), Some(b * denominator)),
            _ => (Some(term), Some(denominator)),
        };
        let none: (Option<S>, Option<S>) = (None, None);
        let (mut internal, mut ports) = (none, none);
        for (group, &(numerator, denominator)) in spec.groups.iter().zip(&groups) {
            let e = formula(&group.formula, &|c| cells[c ^ group.role], &gammas);
            let single = group.pairs.len() == 1;
            if group.pulls {
                let value = e + v0;
                internal = add(internal, if single { value } else { numerator * value }, denominator);
            } else {
                let (value, denominator) = match w_phi.iter().find(|(k, _, _)| *k == group.role) {
                    Some(&(_, n, d)) => ((e + delta) * d + n, denominator * d),
                    None => (e + delta, denominator),
                };
                ports = add(ports, if single { value } else { numerator * value }, denominator);
            }
        }
        (
            internal.0.unwrap_or(S::zero()),
            internal.1.unwrap_or(one),
            ports.0.unwrap_or(S::zero()),
            ports.1.unwrap_or(one),
        )
    };

    let _phase = enter("pi2: identity and claims");
    // The copy identity at `t`, `c_h h + c_q q = Δ + w_m R_n / R_d`, normalised: `(1 + ρ') h + ρ' q = num1 / (R_d Y)`
    // (`Y = c_h + c_q`, `ρ' = c_q / Y`, `1 + ρ' = c_h / Y`). The definition: `w_m q_P = s + v_0 + w_m A / B = num3 / B`.
    // With the digits' scale `D = scale t / w_{m+1}` (a chunk's weighted value is `D` times its polynomial's at `t`,
    // `PI2.md` §2), `Q`'s claims are worth: the identity's, at `(u, ρ', y_0, y_1)`,
    // `(D / Y)(num1 / R_d + c_3 (c_h w_m s + num3 / B))`, `c_3 = y_0 y_1 / ((1 + y_0)(1 + y_1))` (`P` at digit 1 weighs
    // `u_m (1 + ρ') y_0 y_1`, `q_P` `ρ' y_0 y_1`); the pushes', at `(u, ρ, 1, 1)`,
    // `(D / L_0)((1 + ρ) w_m s + ρ num3 / (w_m B))`, `L_0 = (1 + y_0)(1 + y_1)`.
    let c_h = d_pull * d_push;
    let y = c_h + w[m];
    // `D_n = B (α + P_v(t) + ξ)`, required nonzero with the rest: the pushes' fraction `A / B` whole in the check (the
    // contract computes `A` and `B` together, not `B`'s factors kept for `A`).
    let d_n = (alpha + v0 + xi) * den + w[m] * num;
    let num1 = delta * r_den + w[m] * r_num;
    let num3 = d_n + d_push * den;
    // One inversion: of `R_d Y`, `w_{m+1}`, `B`, `c_h` (nonzero: `1 + ρ'` is not zero, so the claim binds `h(t)` and
    // `P(t)`) and `D_n`.
    let p1 = r_den * y;
    let p2 = p1 * w[m + 1];
    let p3 = p2 * den;
    let cd = c_h * d_n;
    let all = p3 * cd;
    channel.require_nonzero(all, VerifierError::RecDegenerate)?;
    let inv_all = {
        let _phase = enter("pi2: the inversion");
        inverse(all)
    };
    let inv_p3 = inv_all * cd;
    let inv_p2 = inv_p3 * den;
    let inv_top = inv_p2 * p1;
    let rho_q = w[m] * (inv_p2 * (r_den * w[m + 1]));
    // `1/w_l = (1 + w_l) / w_{l+1}` (as `w_{l+1} = w_l (1 + w_l)`), down from `1/w_{m+1}`.
    let mut w_invs = vec![S::zero(); m + 2];
    w_invs[m + 1] = inv_top;
    for l in (0..m + 1).rev() {
        w_invs[l] = (one + w[l]) * w_invs[l + 1];
    }
    let ([y0, y1], scale) = extension();
    let l0 = (F192::ONE + y0) * (F192::ONE + y1);
    let c3 = ext::<S>(y0 * y1 * l0.inv());
    let scale_l0 = ext::<S>(scale * l0.inv());
    let (y0, y1, scale) = (ext::<S>(y0), ext::<S>(y1), ext::<S>(scale));
    let st = scale * t;
    // The identity's value: `scale t (num1 B + c_3 R_d (c_h w_m s B + num3)) / (w_{m+1} Y R_d B)`.
    let quotient_value = st * inv_p3 * (num1 * den + c3 * (r_den * (c_h * (w[m] * (s * den)) + num3)));
    // The pushes': `(scale / L_0) t ((1 + ρ) w_m² s B + ρ num3) / (w_{m+1} w_m B)`, `1 / (w_{m+1} B) = R_d Y / p3`.
    let pushes_value =
        scale_l0 * t * ((one + rho) * (w[m].square() * (s * den)) + rho * num3) * (inv_p3 * p1) * w_invs[m];

    // `1/(1 + w_l) = 1/w_l + 1/w_{l+1}`.
    let u: Vec<S> = (0..m + 1).map(|l| one + w_invs[l] + w_invs[l + 1]).collect();
    let [wv, qv, sv] = stack_vars(m);
    let padded = |point: Vec<S>, vars: usize| -> Vec<S> {
        let mut point = point;
        point.resize(vars, S::zero());
        point
    };
    let quotient_point = padded([&u[..], &[rho_q, y0, y1]].concat(), qv);
    let pushes_point = padded([&u[..], &[rho, one, one]].concat(), qv);
    let sum_point = padded([vec![one; m], vec![S::zero(); 2], vec![y0, y1]].concat(), qv);

    let mut rhos = vec![rho];
    for l in 1..r {
        rhos.push(rhos[l - 1].square());
    }
    let mut fold = a;
    for l in (0..r).rev() {
        let half = 1 << l;
        for j in 0..half {
            fold[j] = fold[j] + rhos[l] * (fold[j] + fold[j + half]);
        }
        fold.truncate(half);
    }
    let witness_point = padded([&rhos[..], &w[r..m]].concat(), wv);
    let setup_point = padded([&w[..m], &[beta]].concat(), sv);
    let pair_points = public.iter().map(|&x| leanvm_statement::transcript::pair_point(x)).collect();
    Ok(Reduced {
        pair_points,
        public,
        roots: [witness_root, quotient_root],
        oods: [witness_ood, quotient_ood],
        witness: (witness_point, fold[0]),
        quotient: (quotient_point, quotient_value),
        pushes: (pushes_point, pushes_value),
        sum: (sum_point, S::zero()),
        setup: (setup_point, xi),
    })
}


/// The transcript's seed: the Keccak-256 of the name, the IV, the public input, then the frame words (`Read::Frame`,
/// in order: the hashed claims' Keccak-256s), which the contract reads from the frame of PCS claims.
pub fn seed(iv: &[u8; 32], public_input: &[u8; 32], frame: &[[u8; 32]]) -> [u8; 32] {
    keccak256(&[&NAME[..], iv, public_input, &frame.concat()].concat())
}

/// The verifier on `E` with the Keccak-256 chain, the contract's in Rust: the stream must be read whole. `frame` are
/// the frame words its `Read::Frame`s read, in order; `checks` what it does with the identities it requires (enforced,
/// or collected for a comparison with the contract), returned as they end.
pub fn verify(
    spec: &Spec,
    iv: &[u8; 32],
    public_input: &[u8; 32],
    frame: &[[u8; 32]],
    stream: &[u8],
    checks: Checks,
) -> Result<(Reduced<E>, Checks), VerifierError> {
    let mut channel = KeccakChannel::new(seed(iv, public_input, frame), stream, checks);
    channel.frame = frame.to_vec();
    let reduced = reduce(spec, statement_words(public_input), &mut channel)?;
    channel.finish()?;
    Ok((reduced, channel.checks))
}

/// A claim of [`Reduced`] in the prover's field: its point and value.
pub fn claim((point, value): &(Vec<E>, E)) -> (Vec<F192>, F192) {
    (point.iter().map(|&x| x.into()).collect(), (*value).into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use quotient::domain::{beta, chain};

    #[test]
    fn inverse_inverts() {
        let mut x = E::new(0x1234_5678_9abc_def1, 0x0fed_cba9_8765_4321, 0x5555_aaaa_3333_cccc);
        for _ in 0..8 {
            assert_eq!(inverse(x) * x, E::new(1, 0, 0));
            x = x * x + E::new(3, 1, 4);
        }
    }

    /// `Φ`'s basis (`Spec::phi`): `w_r(ω_i) = ω_{i >> r}`, so `w_m(x) / (w_r(x) + ω_y) = L_y(w_r(x))` with
    /// `L_y(z) = w_{m-r}(z) / (z + ω_y)`, which is zero on `V_{m-r}` but at `ω_y`; and it is `V_{m-r}`'s Lagrange
    /// basis (`w_{m-r}' = 1`): the `L_y` sum to one everywhere (the interpolation of the constant one).
    #[test]
    fn the_ports_lagrange_basis() {
        let (m, r) = (10, 4);
        for i in (0..1usize << m).step_by(7) {
            assert_eq!(chain(point(i), r + 1)[r], point(i >> r), "w_r(ω_i) = ω_(i >> r)");
            assert!(chain(point(i), m + 1)[m].is_zero());
        }
        for x in [beta()[m + 1] + point(5), beta()[m + 2] + point(77), F64(0x1234_5678_9abc_def1)] {
            let z = chain(x, r + 1)[r];
            let wz = chain(z, m - r + 1)[m - r];
            assert_eq!(wz, chain(x, m + 1)[m], "w_m = w_(m-r) ∘ w_r");
            let sum = (0..1usize << (m - r)).fold(F64::ZERO, |acc, y| acc + wz * (z + point(y)).inv());
            assert_eq!(sum, F64::ONE, "the Lagrange basis of V_(m-r) sums to one");
        }
    }
}
