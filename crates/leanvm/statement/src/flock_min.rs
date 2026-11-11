// Part of this repository. Builds on `crate::flock`, adapted from leanVM (https://github.com/leanEthereum/leanVM),
// commit 42422001, file crates/verifier/src/flock.rs, whose zerocheck, lincheck and ring switch this module re-states
// with the univariate skip's size as a parameter. New here: the skip of any size `k ≤ 6`, π1-rec's zerocheck point
// (`FsShape::Rec`: its sampled coordinates successive squares of one), the ring map in tower order
// (`crate::ring_tower`), and the lincheck's terminal checked on the sent slices for any block circuit
// ([`WalkedCircuit`]: `crate::keccak_flock`'s Keccak-f block, docs/leanvm/univariate/FLOCK.md). MIT OR Apache-2.0; see
// AGENTS.md.
//! Flock's verifier as π1 runs it (docs/leanvm/univariate/FLOCK.md): the zerocheck with a univariate skip, the
//! lincheck, the 64 slices sent and the lincheck's terminal checked on them ([`WalkedCircuit::terminal`]), then the
//! ring switch's map and target, whose weight `Φ(eq(p, ·))` is left to the verifier's batching sumcheck.

use crate::VerifierError;
use crate::field::E;
use crate::flock::{N_FIXED_CHALLENGES, fixed_challenges, lagrange_interpolate, lagrange_weights};
use crate::layout::K_BITS;
use crate::multilinear::{dot, eq_eval, eq_kernel};
use crate::scalar::{Scalar, enter};
use crate::transcript::{Channel, FsShape, squares, sumcheck};

/// The packing bits of `q_flock`: 64 bits a word.
pub const PACKING: usize = 6;

/// Flock's parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Variant {
    /// The univariate skip's variables, `0..=6` (leanVM: 6). `0` is no skip: every round multilinear.
    pub skip: usize,
    /// The verifier's Fiat–Shamir shape: with [`FsShape::Rec`] (π1-rec, docs/leanvm/rec/SPEC-REC.md §1.4) the
    /// zerocheck's eq point after its seven fixed coordinates is `c, c², c⁴, …` of one challenge `c`. It is also the
    /// shape of the verifier Flock is part of (`leanvm_univariate`'s `reduce`: the bus's `α`).
    pub fs: FsShape,
}

/// A Flock block circuit as the walked terminal reads it: a block's slots, its constant wire, and its rows' values
/// `(A0 w, B0 w)` at column weights `w` (one forward walk). The lincheck runs `LOG_SIZE - 6` rounds.
pub trait WalkedCircuit {
    /// `log2` of a block's slots.
    const LOG_SIZE: usize;
    /// The constant wire's slot (lincheck's pin).
    const CONSTANT_COLUMN: usize;
    /// The phase the terminal is recorded under.
    const TERMINAL_PHASE: &'static str = "flock lincheck: the terminal by the circuit's walk";
    /// `(A0 w, B0 w)`, `w` of `2^LOG_SIZE` weights.
    fn row_values<S: Scalar>(w: &[S]) -> (Vec<S>, Vec<S>);
    /// The lincheck's terminal [`verify_walked_with`] checks: by default [`walked_terminal_with`] (the walk of
    /// [`Self::row_values`]); a block may compute the same value from its structure (`crate::keccak_flock::Keccak`).
    fn terminal<S: Scalar>(z_skip: Option<S>, row_low: &[S], chi_in: &[S], chi_in_prime: &[S], s: &[S], alpha: S) -> S
    where
        Self: Sized,
    {
        walked_terminal_with::<S, Self>(z_skip, row_low, chi_in, chi_in_prime, s, alpha)
    }
    /// The lincheck's rounds: the block's slot bits after the 6 packing bits.
    fn lincheck_rounds() -> usize {
        Self::LOG_SIZE - PACKING
    }
}

impl Variant {
    /// The scalars Flock reads at `log_n` variables for a block whose lincheck runs `lincheck_rounds` rounds
    /// ([`WalkedCircuit::lincheck_rounds`]): the skip's `2^k` values, the zerocheck's rounds and its two values, the
    /// lincheck's rounds and the 64 slices.
    pub fn scalars_with(&self, log_n: usize, lincheck_rounds: usize) -> usize {
        let skip = if self.skip > 0 { 1 << self.skip } else { 0 };
        skip + 2 * (log_n - self.skip) + 2 + 2 * lincheck_rounds + K_BITS
    }
}

/// What Flock leaves: the ring switch's claim `Σ_u W(u) q_flock(u) = target`, `W = Φ(eq(point, ·))`, `Φ` drawn by
/// `map`.
#[derive(Clone, Debug)]
pub struct End<S> {
    pub map: Vec<S>,
    pub target: S,
}

/// What the zerocheck leaves: the skip's point (none without a skip), the rounds' challenges, and the claims on
/// `Az`, `Bz`, `Cz` there.
type Zerocheck<S> = (Option<S>, Vec<S>, [S; 3]);

/// The zerocheck with a skip over `k` variables: `2^k` values on the skip's coset (none for `k = 0`), then
/// `log_n - k` rounds; seven fixed coordinates first, as leanVM's, then the others drawn as `fs` has it (one by one,
/// or with [`FsShape::Rec`] the first drawn and each next the square of the one before).
fn zerocheck<S: Scalar>(
    log_n: usize,
    k: usize,
    fs: FsShape,
    eq_first: Option<S>,
    transcript: &mut impl Channel<S>,
) -> Result<Zerocheck<S>, VerifierError> {
    let _phase = enter("flock zerocheck: skip round");
    let mut r: Vec<Option<S>> = fixed_challenges().map(|c| Some(S::constant(c))).into();
    let sampled = log_n - k - N_FIXED_CHALLENGES;
    let drawn = match eq_first {
        // π1-rec4: the first sampled coordinate drawn before Flock (with the bus's challenges), the others its squares.
        Some(c) => squares(c, sampled),
        None => fs.draw(transcript, sampled),
    };
    r.extend(drawn.into_iter().map(Some));
    let (z_skip, claim) = if k > 0 {
        let coset = transcript.next_scalars(1 << k)?;
        let z = transcript.sample();
        let values = [vec![S::zero(); 1 << k], coset].concat();
        (Some(z), lagrange_interpolate(2 << k, &values, z))
    } else {
        (None, S::zero())
    };
    let (chi, running) = {
        let _rounds = enter("flock zerocheck: rounds");
        sumcheck(transcript, claim, 3, &r)?
    };
    let (v_a, v_b) = (transcript.next_scalar()?, transcript.next_scalar()?);
    Ok((z_skip, chi, [v_a, v_b, running + v_a * v_b]))
}

/// The weights of the row's 6 packing bits: the skip's Lagrange weights on its `k`, eq on the `6 - k` others.
fn row_low_weights<S: Scalar>(z_skip: Option<S>, low: &[S]) -> (Vec<S>, Vec<S>) {
    let skip = match z_skip {
        Some(z) => lagrange_weights(1 << (PACKING - low.len()), z),
        None => vec![S::one()],
    };
    let mle = eq_kernel(low);
    let weights = mle.iter().flat_map(|&m| skip.iter().map(move |&l| l * m)).collect();
    (skip, weights)
}

/// Flock on the block circuit `C`: the zerocheck, the lincheck, the slices, the terminal `r_lc` against
/// [`WalkedCircuit::terminal`], then the ring switch's map and target. What it leaves: the slices' point (`q_flock`'s
/// word coordinates) and the ring switch's end.
pub fn verify_walked_with<S: Scalar, C: WalkedCircuit>(
    log_n: usize,
    variant: Variant,
    transcript: &mut impl Channel<S>,
) -> Result<(Vec<S>, End<S>), VerifierError> {
    let (point, slices) = verify_walked_deferred::<S, C>(log_n, variant, transcript, None)?;
    let end = ring_end(&slices, transcript);
    Ok((point, end))
}

/// [`verify_walked_with`] without the ring switch's map: the zerocheck, the lincheck, the slices and the terminal
/// check; returns the slices' point and the slices, the map drawn by the caller ([`ring_end_at`]). With `eq_first`
/// the zerocheck's first sampled coordinate is the caller's (π1-rec4, `FsShape::Rec4`: drawn with the bus's
/// challenges, then the map after `C2`'s commitment, `docs/leanvm/univariate/SPEC.md` §14.4).
pub fn verify_walked_deferred<S: Scalar, C: WalkedCircuit>(
    log_n: usize,
    variant: Variant,
    transcript: &mut impl Channel<S>,
    eq_first: Option<S>,
) -> Result<(Vec<S>, Vec<S>), VerifierError> {
    let front = front_with(log_n, variant, C::LOG_SIZE, transcript, eq_first)?;
    let slices = &front.slices;
    let terminal = {
        let _phase = enter(C::TERMINAL_PHASE);
        C::terminal(
            front.z_skip,
            &front.row_low,
            &front.chi_in,
            &front.chi_in_prime,
            slices,
            front.alpha,
        )
    };
    transcript.require_zero(terminal + front.r_lc, VerifierError::FlockMatrixTerminal)?;
    Ok((front.point, front.slices))
}

/// The lincheck's terminal as leanVM's verifier computes it, on the block circuit `C`, at the skip's `k` row bits (`PACKING - row_low.len()`):
/// the matrix terms `Σ_(row, col) e(row) (Â0 + α B̂0)(row, col) w(col)`, `e = (L(z_skip) ⊗ eq(row_low)) ⊗ eq(chi_in)`
/// and `w = s ⊗ eq(chi_in')` (one forward walk of the block circuit gives `A0 w` and `B0 w`), the `C = I` claim's
/// term and the constant position's pin.
pub fn walked_terminal_with<S: Scalar, C: WalkedCircuit>(
    z_skip: Option<S>,
    row_low: &[S],
    chi_in: &[S],
    chi_in_prime: &[S],
    s: &[S],
    alpha: S,
) -> S {
    let (_, low_weights) = row_low_weights(z_skip, row_low);
    let high = eq_kernel(chi_in_prime);
    let mut w = vec![S::zero(); 1 << C::LOG_SIZE];
    for (h, &weight) in high.iter().enumerate() {
        for (l, &slice) in s.iter().enumerate() {
            w[h * K_BITS + l] = slice * weight;
        }
    }
    let (left, right) = C::row_values(&w);
    let rows = eq_kernel(chi_in);
    let mut matrix = S::zero();
    for (h, &row_weight) in rows.iter().enumerate() {
        let (mut l_sum, mut r_sum) = (S::zero(), S::zero());
        for (low, &weight) in low_weights.iter().enumerate() {
            l_sum += weight * left[h * K_BITS + low];
            r_sum += weight * right[h * K_BITS + low];
        }
        matrix += row_weight * (l_sum + alpha * r_sum);
    }
    let (c_weight, pin_weight) = known_weights_with(alpha, chi_in, chi_in_prime, C::CONSTANT_COLUMN);
    matrix + c_weight * dot(&low_weights, s) + pin_weight * s[C::CONSTANT_COLUMN % K_BITS]
}

/// What the zerocheck and the lincheck leave, and the slices.
struct Front<S> {
    z_skip: Option<S>,
    row_low: Vec<S>,
    chi_in: Vec<S>,
    chi_in_prime: Vec<S>,
    alpha: S,
    r_lc: S,
    slices: Vec<S>,
    /// `q_flock`'s word coordinates of the slices: the lincheck's column bits, then the instance bits.
    point: Vec<S>,
}

/// The zerocheck and the lincheck for a block of `2^log_size` slots (the lincheck's `log_size - 6` rounds), then the
/// slices.
fn front_with<S: Scalar>(
    log_n: usize,
    variant: Variant,
    log_size: usize,
    transcript: &mut impl Channel<S>,
    eq_first: Option<S>,
) -> Result<Front<S>, VerifierError> {
    let k = variant.skip;
    let lincheck_rounds = log_size - PACKING;
    assert!(k <= PACKING && log_n >= log_size + N_FIXED_CHALLENGES);
    let (z_skip, chi, [v_a, v_b, v_c]) = zerocheck(log_n, k, variant.fs, eq_first, transcript)?;
    // The row point: the skip, the packing bits left to rounds, the 8 slot bits, the instance bits.
    let (row_low, rest) = chi.split_at(PACKING - k);
    let (chi_in, chi_rest) = rest.split_at(lincheck_rounds);

    let _phase = enter("flock lincheck: rounds");
    let alpha = transcript.sample();
    let claim = v_a + alpha * v_b + alpha.pow(2) * v_c + alpha.pow(3);
    let (round_challenges, r_lc) = sumcheck(transcript, claim, 3, &vec![None; lincheck_rounds])?;
    let chi_in_prime: Vec<S> = round_challenges.iter().rev().copied().collect();
    let slices = transcript.next_scalars(K_BITS)?;
    let point: Vec<S> = [&chi_in_prime[..], chi_rest].concat();
    Ok(Front {
        z_skip,
        row_low: row_low.to_vec(),
        chi_in: chi_in.to_vec(),
        chi_in_prime,
        alpha,
        r_lc,
        slices,
        point,
    })
}

/// The ring switch on the sent slices: its map drawn, its target with the map's stages in tower order.
fn ring_end<S: Scalar>(s: &[S], transcript: &mut impl Channel<S>) -> End<S> {
    let map = {
        let _phase = enter("ring switch: map, coefficients, target");
        transcript.samples(RING_MAP_LEN)
    };
    ring_end_at(s, map)
}

/// The ring switch's map: leanVM's `RING_MAP_SHIFTS`, six challenges.
pub const RING_MAP_LEN: usize = crate::flock::RING_MAP_SHIFTS.len();

/// The ring switch's end on the slices `s` at the map `map` (drawn after the slices).
pub fn ring_end_at<S: Scalar>(s: &[S], map: Vec<S>) -> End<S> {
    let _phase = enter("ring switch: map, coefficients, target");
    assert_eq!(map.len(), RING_MAP_LEN);
    let target = crate::ring_tower::target(s, &map);
    End { map, target }
}

/// The weights of the terminal's two known terms, the `C = I` claim's and the constant position's pin, with the
/// constant wire at `constant_column` (its word's bits, `chi_in'.len()` of them).
fn known_weights_with<S: Scalar>(alpha: S, chi_in: &[S], chi_in_prime: &[S], constant_column: usize) -> (S, S) {
    let constant_bits: Vec<S> = (0..chi_in_prime.len())
        .map(|bit| S::constant(E::new((constant_column / K_BITS) as u64 >> bit & 1, 0, 0)))
        .collect();
    let pin_weight = alpha.pow(3) * eq_eval(&constant_bits, chi_in_prime);
    let c_weight = alpha.pow(2) * eq_eval(chi_in, chi_in_prime);
    (c_weight, pin_weight)
}
