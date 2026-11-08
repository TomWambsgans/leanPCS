// Adapted from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/verifier/src/flock.rs: the
// pieces of its Flock verifier that `crate::flock_min` builds on, on a generic `Scalar` (constants computed natively,
// as leanVM's are): the fixed challenges and Lagrange weights of the univariate skip, the BLAKE2s row walk (both
// matrices' sides at once) and the ring switch's map and weight. MIT OR Apache-2.0; see NOTICE.md.
//! Flock's shared pieces: the skip's Lagrange weights, the BLAKE2s circuit's row values, the ring switch's weight.

use crate::field::{E, ONE};
use crate::hash::{BLAKE2S_G_LANES, BLAKE2S_IV, BLAKE2S_SIGMA};
use crate::layout::{BLAKE2S_CONSTANT_COLUMN, BLAKE2S_R1CS_LOG_SIZE, K_BITS};
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

type Word<S> = [S; 32];

/// The forward walk's state: `A0 w` and `B0 w`, filled row by row.
struct RowValues<'a, S> {
    column_weights: &'a [S],
    left_values: Vec<S>,
    right_values: Vec<S>,
}

impl<S: Scalar> RowValues<'_, S> {
    fn slots(&self, base: usize) -> Word<S> {
        std::array::from_fn(|bit| self.column_weights[base + bit])
    }

    fn literal(&self, value: u32) -> Word<S> {
        let constant = self.column_weights[BLAKE2S_CONSTANT_COLUMN];
        std::array::from_fn(|bit| if value >> bit & 1 == 1 { constant } else { S::zero() })
    }

    fn add(&mut self, x: Word<S>, y: Word<S>, carry_base: usize) -> Word<S> {
        let mut carry = S::zero();
        let mut output = [S::zero(); 32];
        for bit in 0..32 {
            if bit < 31 {
                self.left_values[carry_base + bit] = x[bit] + carry;
                self.right_values[carry_base + bit] = y[bit] + carry;
            }
            output[bit] = x[bit] + y[bit] + carry;
            if bit < 31 {
                carry += self.column_weights[carry_base + bit];
            }
        }
        output
    }

    /// Fused three-operand add: 31 majority rows then 30 ripple rows.
    ///
    /// The majority of bit `i` is `maj_aux[i] + z[i]`, since over GF(2)
    /// `(x+z)(y+z) = xy + xz + yz + z`; then `x + y + z` is the ripple sum of
    /// `p = x^y^z` against `q[i] = maj[i-1]`, whose bit 0 is zero, so the
    /// ripple layer's bit 0 needs no row and slot `base + 31 + i - 1` carries
    /// bit `i`.
    fn add3(&mut self, x: Word<S>, y: Word<S>, z: Word<S>, base: usize) -> Word<S> {
        let mut majority = [S::zero(); 31];
        for bit in 0..31 {
            self.left_values[base + bit] = x[bit] + z[bit];
            self.right_values[base + bit] = y[bit] + z[bit];
            majority[bit] = self.column_weights[base + bit] + z[bit];
        }
        let ripple_base = base + 31;
        let mut carry = S::zero();
        let mut output = [S::zero(); 32];
        for bit in 0..32 {
            let q = if bit == 0 { S::zero() } else { majority[bit - 1] };
            let left = x[bit] + y[bit] + z[bit] + carry;
            output[bit] = left + q;
            if (1..=30).contains(&bit) {
                self.left_values[ripple_base + bit - 1] = left;
                self.right_values[ripple_base + bit - 1] = q + carry;
                carry += self.column_weights[ripple_base + bit - 1];
            }
        }
        output
    }

    fn linear_rows(&mut self, values: Word<S>, base: usize) {
        for bit in 0..32 {
            self.left_values[base + bit] = values[bit];
            self.right_values[base + bit] = self.column_weights[BLAKE2S_CONSTANT_COLUMN];
        }
    }
}

fn xor<S: Scalar>(x: Word<S>, y: Word<S>) -> Word<S> {
    std::array::from_fn(|bit| x[bit] + y[bit])
}

fn rotate_right<S: Scalar>(word: Word<S>, amount: usize) -> Word<S> {
    std::array::from_fn(|bit| word[(bit + amount) & 31])
}

/// Compute `A0 w` and `B0 w` by one forward walk of the circuit.
pub fn blake2s_row_values<S: Scalar>(column_weights: &[S]) -> (Vec<S>, Vec<S>) {
    let size = 1 << BLAKE2S_R1CS_LOG_SIZE;
    let constant = BLAKE2S_CONSTANT_COLUMN;
    let message_base = 640;
    let counter_low = 1152;
    let counter_high = 1184;
    let final_flag = 1216;
    let last_node_flag = 1248;
    let gates_base = 1280;
    let gate_stride = 184;
    let mut rows = RowValues {
        column_weights,
        left_values: vec![S::zero(); size],
        right_values: vec![S::zero(); size],
    };

    for (base, length) in [(0, 256), (message_base, 512), (counter_low, 128)] {
        for row in base..base + length {
            rows.left_values[row] = column_weights[row];
            rows.right_values[row] = column_weights[constant];
        }
    }

    // v[0..8] = h, v[8..12] = IV[0..4], v[12..16] = IV[4..8] ^ (t_lo, t_hi, f0, f1).
    let mut state = [[S::zero(); 32]; 16];
    for word in 0..8 {
        state[word] = rows.slots(32 * word);
    }
    for word in 0..4 {
        state[8 + word] = rows.literal(BLAKE2S_IV[word]);
    }
    for (word, base) in [counter_low, counter_high, final_flag, last_node_flag]
        .into_iter()
        .enumerate()
    {
        state[12 + word] = xor(rows.literal(BLAKE2S_IV[4 + word]), rows.slots(base));
    }

    for (round_index, sigma) in BLAKE2S_SIGMA.iter().enumerate() {
        for (gate_index, &[lane_a, lane_b, lane_c, lane_d]) in BLAKE2S_G_LANES.iter().enumerate() {
            let gate = round_index * 8 + gate_index;
            let gate_base = gates_base + gate_stride * gate;
            let (a, b, c, d) = (state[lane_a], state[lane_b], state[lane_c], state[lane_d]);
            let mx = rows.slots(message_base + 32 * sigma[2 * gate_index]);
            let my = rows.slots(message_base + 32 * sigma[2 * gate_index + 1]);
            let a1 = rows.add3(a, b, mx, gate_base);
            let d1 = rotate_right(xor(d, a1), 16);
            let c1 = rows.add(c, d1, gate_base + 61);
            let b1 = rotate_right(xor(b, c1), 12);
            let a2 = rows.add3(a1, b1, my, gate_base + 92);
            let d2 = rotate_right(xor(d1, a2), 8);
            let c2 = rows.add(c1, d2, gate_base + 153);
            let b2 = rotate_right(xor(b1, c2), 7);
            // Every lane cascades: this encoding materializes no intermediate word.
            state[lane_a] = a2;
            state[lane_b] = b2;
            state[lane_c] = c2;
            state[lane_d] = d2;
        }
    }

    // out[w] = h[w] ^ v[w] ^ v[w+8], the only materialized words.
    for word in 0..8 {
        let out = xor(xor(state[word], state[word + 8]), rows.slots(32 * word));
        rows.linear_rows(out, 256 + 32 * word);
    }

    rows.left_values[constant] = column_weights[constant];
    rows.right_values[constant] = column_weights[constant];
    (rows.left_values, rows.right_values)
}

// The Frobenius shifts of the six stages composing Phi, one challenge each.
pub(crate) const RING_MAP_SHIFTS: [usize; 6] = [32, 16, 8, 4, 2, 1];

/// The drawn map, stage by stage: `a_p+1 = a_p + f_p a_p^(2^shift)`.
pub(crate) fn ring_map<S: Scalar>(mut value: S, challenges: &[S]) -> S {
    for (&challenge, shift) in challenges.iter().zip(RING_MAP_SHIFTS) {
        value += challenge * value.pow(1 << shift);
    }
    value
}

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
