// Part of this repository. The method names and `add_round_poly`'s body are leanVM's (https://github.com/leanEthereum/
// leanVM), commit 42422001, file crates/fiat_shamir/src/transcript.rs; the transcript is a trait here, so that flock's
// prover writes to whatever chain implements it (the univariate PIOP's Keccak-256 chain). Formerly its own crate
// (`lv42_fiat_shamir`, its module `transcript`); the unit tests' implementation on leanVM c445e3d5's `ProverState` is
// new. MIT OR Apache-2.0; see AGENTS.md.
//! The transcript flock's prover writes to.

use primitives::field::F192;

/// What flock's prover does with a transcript: send scalars, draw challenges.
pub trait Transcript {
    fn add_scalar(&mut self, x: F192);

    fn sample(&mut self) -> F192;

    fn sample_vec(&mut self, n: usize) -> Vec<F192> {
        (0..n).map(|_| self.sample()).collect()
    }

    fn add_scalars(&mut self, xs: &[F192]) {
        for &x in xs {
            self.add_scalar(x);
        }
    }

    /// leanVM's: a round polynomial's coefficients but the one the verifier derives (the constant with an eq
    /// factor, the linear one without).
    fn add_round_poly(&mut self, coeffs: &[F192], eq: bool) {
        assert!(coeffs.len() >= 2, "a round polynomial has at least two coefficients");
        let fixed = usize::from(!eq);
        for (i, &c) in coeffs.iter().enumerate() {
            if i != fixed {
                self.add_scalar(c);
            }
        }
    }
}

/// leanVM's name for the prover's transcript, here any [`Transcript`] (which may borrow: the lifetime is elided
/// where flock names it).
pub type ProverState<'a> = dyn Transcript + 'a;

/// The unit tests' transcript: leanVM c445e3d5's duplex, each method its own.
#[cfg(test)]
impl Transcript for fiat_shamir::transcript::ProverState {
    fn add_scalar(&mut self, x: F192) {
        fiat_shamir::transcript::ProverState::add_scalar(self, x);
    }

    fn sample(&mut self) -> F192 {
        fiat_shamir::transcript::ProverState::sample(self)
    }

    fn sample_vec(&mut self, n: usize) -> Vec<F192> {
        fiat_shamir::transcript::ProverState::sample_vec(self, n)
    }

    fn add_scalars(&mut self, xs: &[F192]) {
        fiat_shamir::transcript::ProverState::add_scalars(self, xs);
    }

    fn add_round_poly(&mut self, coeffs: &[F192], eq: bool) {
        fiat_shamir::transcript::ProverState::add_round_poly(self, coeffs, eq);
    }
}
