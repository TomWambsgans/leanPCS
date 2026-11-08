// Part of this repository. The chain's hashing is leanvm_statement::transcript's `KeccakChannel`. MIT OR Apache-2.0;
// see AGENTS.md.
//! The verifier's combined claims on the point-claim stream.
//!
//! The prover learns each commitment's combined claim (its terms, points and value) by running the verifier's own
//! `reduce` in weighted mode on the stream so far: weighted mode returns the claims, and reads nothing after `ρ`.
//!
//! The claims are the same in both modes: the same relations, in the same order, at the same challenges, the ring
//! switch's weight as one term (point mode) or as its 64 twisted terms (weighted mode), which is the same weight.
//! [`Replay`] is the contract's Keccak chain on the point-claim stream, its checks collected.
//!
//! The verifier does not expose its combined claims in point mode (PROVER.md, "Notes for the verifier").

use leanvm_statement::VerifierError;
use leanvm_statement::field::E;
use leanvm_statement::transcript::{Channel, Checks, challenge_of, keccak256};

pub struct Replay<'a> {
    data: &'a [u8],
    cursor: usize,
    absorbed: usize,
    state: [u8; 32],
    pub checks: Checks,
}

impl<'a> Replay<'a> {
    /// The chain on `stream`.
    pub fn new(seed: [u8; 32], stream: &'a [u8]) -> Self {
        Self {
            data: stream,
            cursor: 0,
            absorbed: 0,
            state: seed,
            checks: Checks::Collect {
                zero: vec![],
                nonzero: vec![],
            },
        }
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], VerifierError> {
        let bytes = self
            .data
            .get(self.cursor..self.cursor + N)
            .ok_or(VerifierError::StreamExhausted)?;
        self.cursor += N;
        Ok(bytes.try_into().expect("N bytes"))
    }

    /// The whole stream was read.
    pub fn finish(&self) -> Result<(), String> {
        if self.cursor != self.data.len() {
            return Err(format!("the verifier read {} of the stream's {} bytes", self.cursor, self.data.len()));
        }
        Ok(())
    }

    /// Whether the checks collected (zero, then nonzero) all hold.
    pub fn checks_hold(&self) -> bool {
        match &self.checks {
            Checks::Enforce => true,
            Checks::Collect { zero, nonzero } => {
                zero.iter().all(|x| *x == E::default()) && nonzero.iter().all(|x| *x != E::default())
            }
        }
    }
}

impl Channel<E> for Replay<'_> {
    fn next_scalar(&mut self) -> Result<E, VerifierError> {
        let bytes = self.take::<24>()?;
        let limb = |i: usize| u64::from_be_bytes(bytes[16 - 8 * i..24 - 8 * i].try_into().unwrap());
        Ok(E::new(limb(0), limb(1), limb(2)))
    }

    fn next_integer(&mut self, bytes: usize) -> Result<E, VerifierError> {
        assert!((1..=8).contains(&bytes));
        let data = self
            .data
            .get(self.cursor..self.cursor + bytes)
            .ok_or(VerifierError::StreamExhausted)?;
        self.cursor += bytes;
        Ok(E::new(data.iter().fold(0u64, |acc, &b| acc << 8 | b as u64), 0, 0))
    }

    fn next_root(&mut self) -> Result<[E; 2], VerifierError> {
        let mut half = || -> Result<E, VerifierError> {
            let bytes = self.take::<16>()?;
            let limb = |i: usize| u64::from_be_bytes(bytes[8 - 8 * i..16 - 8 * i].try_into().unwrap());
            Ok(E::new(limb(0), limb(1), 0))
        };
        Ok([half()?, half()?])
    }

    fn sample(&mut self) -> E {
        let input = [&self.state[..], &self.data[self.absorbed..self.cursor]].concat();
        self.absorbed = self.cursor;
        self.state = keccak256(&input);
        challenge_of(&self.state)
    }

    fn require_zero(&mut self, value: E, error: VerifierError) -> Result<(), VerifierError> {
        match &mut self.checks {
            Checks::Enforce => (value == E::default()).then_some(()).ok_or(error),
            Checks::Collect { zero, .. } => {
                zero.push(value);
                Ok(())
            }
        }
    }

    fn require_nonzero(&mut self, value: E, error: VerifierError) -> Result<(), VerifierError> {
        match &mut self.checks {
            Checks::Enforce => (value != E::default()).then_some(()).ok_or(error),
            Checks::Collect { nonzero, .. } => {
                nonzero.push(value);
                Ok(())
            }
        }
    }
}
