// Adapted from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/verifier/src/flock.rs: the
// pieces of its Flock verifier that `crate::flock_min` builds on, on a generic `Scalar` (constants computed natively,
// as leanVM's are): the fixed challenges and Lagrange weights of the univariate skip, and the ring switch's map and
// weight. MIT OR Apache-2.0; see AGENTS.md.
//! Flock's shared pieces: the skip's fixed challenges and Lagrange weights, the ring switch's map and weight.

use crate::field::{E, ONE};
use crate::layout::K_BITS;
use crate::multilinear::dot;
use crate::scalar::{Scalar, enter};

const PHI_BASIS: [u64; 8] = [
    0x0000000000000001,
    0x033CE8BEDDC8A656,
    0x512620375ED2A108,
    0x0C9E636090AAFC01,
    0xBA4F3CD82801769C,
    0xBA26E7904ADB4A47,
    0x467698598926DC01,
    0x4418AE808B28BDD0,
];

/// `PHI[value]`: the F2-linear image of the byte `value` in the PHI basis.
fn phi(value: usize) -> E {
    let bits = (0..8).filter(|bit| value >> bit & 1 == 1);
    E::new(bits.fold(0, |acc, bit| acc ^ PHI_BASIS[bit]), 0, 0)
}

const MEDIUM_GENERATOR: E = E::new(0x243F6A8885A308D3, 0x13198A2E03707344, 0xA4093822299F31D0);
pub(crate) const N_FIXED_CHALLENGES: usize = 7;

pub(crate) fn fixed_challenges() -> [E; N_FIXED_CHALLENGES] {
    let medium = |power: u32| {
        let value = MEDIUM_GENERATOR.pow(1 << power);
        value * (ONE + value).inv()
    };
    [
        phi(0xF7),
        phi(0x53),
        phi(0xB5),
        medium(0),
        medium(1),
        medium(2),
        medium(3),
    ]
}

/// The one barycentric denominator `PHI[:count]` has: `prod_(k != 0) PHI[k]`, inverted.
///
/// PHI is F2-linear in its index, so `PHI[i] + PHI[j] = PHI[i ^ j]`, and over a power-of-two prefix
/// `j -> i ^ j` only permutes the block. Every node is left the same product.
fn window_denominator(count: usize) -> E {
    (1..count).fold(ONE, |acc, k| acc * phi(k)).inv()
}

/// The barycentric weights of `PHI[:count]` at `point`, by prefix and suffix numerator products.
pub fn lagrange_weights<S: Scalar>(count: usize, point: S) -> Vec<S> {
    let differences: Vec<S> = (0..count).map(|node| point + S::constant(phi(node))).collect();
    let mut prefix = vec![S::one(); count + 1];
    let mut suffix = vec![S::one(); count + 1];
    for i in 0..count {
        prefix[i + 1] = prefix[i] * differences[i];
        suffix[count - 1 - i] = suffix[count - i] * differences[count - 1 - i];
    }
    let denominator = S::constant(window_denominator(count));
    (0..count).map(|i| prefix[i] * suffix[i + 1] * denominator).collect()
}

pub(crate) fn lagrange_interpolate<S: Scalar>(count: usize, values: &[S], point: S) -> S {
    dot(&lagrange_weights(count, point), values)
}

// The Frobenius shifts of the six stages composing Phi, one challenge each.
pub(crate) const RING_MAP_SHIFTS: [usize; 6] = [32, 16, 8, 4, 2, 1];

/// The weight `W(u) = Phi(eq(r, u))`, extended and evaluated by the opening at
/// `r_prime`: `sum_k c_k prod_n (1 + r_n^(2^k) + r'_n)`.
fn ring_weight<S: Scalar>(r: &[S], r_prime: &[S], coefficients: &[S]) -> S {
    assert_eq!(r.len(), r_prime.len());
    let _phase = enter("stack batch: ring-switch weight at the point");
    let mut total = S::zero();
    let mut frobenius = r.to_vec();
    for &c in coefficients {
        let mut product = c;
        for (value, &challenge) in frobenius.iter_mut().zip(r_prime) {
            product *= S::one() + *value + challenge;
            *value = value.square();
        }
        total += product;
    }
    total
}

/// The weight of the map drawn as `challenges`: the same map as a Frobenius sum, `Phi(a) = sum_k c_k a^(2^k)` for
/// k < 64.
pub fn ring_switch_weight<S: Scalar>(point: Vec<S>, challenges: &[S]) -> RingWeight<S> {
    let coefficient = |k: usize| {
        let stages = challenges
            .iter()
            .zip(RING_MAP_SHIFTS)
            .filter(|&(_, shift)| k & shift != 0);
        stages.fold(S::one(), |acc, (&f, shift)| acc * f.pow(1 << (k % shift)))
    };
    let coefficients: Vec<S> = (0..K_BITS).map(coefficient).collect();
    RingWeight { point, coefficients }
}

/// The ring switch's weight `W` (leanVM returns it as a closure).
pub struct RingWeight<S> {
    pub point: Vec<S>,
    pub coefficients: Vec<S>,
}

impl<S: Scalar> RingWeight<S> {
    pub fn at(&self, r_prime: &[S]) -> S {
        ring_weight(&self.point, r_prime, &self.coefficients)
    }
}
