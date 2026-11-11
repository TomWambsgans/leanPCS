// Part of this repository. Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6, `FiatShamirState::keccak` (crates/fiat_shamir/src/lib.rs).
// MIT OR Apache-2.0; see AGENTS.md.
//! The reduction's transcript: a Keccak-256 chain, because its verifier is also an EVM contract, where
//! `KECCAK256` is one instruction.
//!
//! The state is a 256-bit word. A challenge is one Keccak-256 of the state and of every scalar sent since
//! the last challenge, each a 256-bit big-endian word (limb 0 lowest, which is how the EVM holds a field
//! element); the digest is the new state, and its low 192 bits the challenge. The protocol fixes how many
//! scalars precede each challenge, so no length or tag is hashed. A commitment rides the stream as the two
//! scalars of [`root_halves`]; the seed is the Keccak-256 of a label that holds the statement.

use fiat_shamir::merkle::Hash;
use primitives::field::F192;
use primitives::hash::hash as keccak256;

/// A root as the two scalars the membership stream carries: its 128-bit halves, each a big-endian number (`c1` its
/// first 8 bytes, `c0` the next 8), so that `s_0 · 2^128 + s_1` is the word whose big-endian bytes are the root: the
/// word the EVM reads it as from calldata or storage, and the root a PCS claim encodes.
pub fn root_halves(root: &Hash) -> [F192; 2] {
    let word = |at: usize| u64::from_be_bytes(root[at..at + 8].try_into().expect("8 bytes"));
    [F192::new(word(8), word(0), 0), F192::new(word(24), word(16), 0)]
}

/// The root two scalars of [`root_halves`] stand for, if they are two halves (no third limb).
pub fn halves_root(scalars: &[F192; 2]) -> Result<Hash, TranscriptError> {
    if scalars.iter().any(|s| s.c2 != 0) {
        return Err(TranscriptError::NotARoot);
    }
    let mut root = [0u8; 32];
    for (h, s) in scalars.iter().enumerate() {
        root[16 * h..16 * h + 8].copy_from_slice(&s.c1.to_be_bytes());
        root[16 * h + 8..16 * h + 16].copy_from_slice(&s.c0.to_be_bytes());
    }
    Ok(root)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TranscriptError {
    /// The stream ended before the verifier read all it needs.
    Exhausted,
    /// The stream holds more than the verifier reads.
    Trailing,
    /// A commitment's scalars are not two 128-bit halves.
    NotARoot,
}

/// A proof: the scalars, in the order sent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
    pub stream: Vec<F192>,
}

/// The chain itself, shared by both sides.
#[derive(Clone, Debug)]
struct Chain {
    state: [u8; 32],
    pending: Vec<F192>,
    draws: usize,
}

#[cfg(test)]
thread_local! {
    /// Test-only: challenges every chain of this thread returns in place of its draws, `k`-th for its `k`-th draw
    /// (the hiding test fixes the challenges to see the proof as a function of the prover's randomness).
    pub(crate) static FIXED: std::cell::RefCell<Option<Vec<F192>>> = const { std::cell::RefCell::new(None) };
}

impl Chain {
    fn new(label: &[u8]) -> Self {
        Self {
            state: keccak256(label),
            pending: Vec::new(),
            draws: 0,
        }
    }

    fn sample(&mut self) -> F192 {
        let mut input = Vec::with_capacity(32 * (1 + self.pending.len()));
        input.extend_from_slice(&self.state);
        for x in self.pending.drain(..) {
            input.extend_from_slice(&[0u8; 8]);
            input.extend_from_slice(&pcs_claim::element_bytes(x));
        }
        self.state = keccak256(&input);
        self.draws += 1;
        #[cfg(test)]
        if let Some(x) = FIXED.with(|fixed| fixed.borrow().as_ref().map(|f| f[self.draws - 1])) {
            return x;
        }
        pcs_claim::element_of(self.state[8..].try_into().unwrap())
    }
}

/// The prover's side: sends scalars and draws challenges.
#[derive(Clone)]
pub struct ProverChain {
    chain: Chain,
    stream: Vec<F192>,
}

impl ProverChain {
    pub fn new(label: &[u8]) -> Self {
        Self {
            chain: Chain::new(label),
            stream: Vec::new(),
        }
    }

    pub fn send(&mut self, x: F192) {
        self.chain.pending.push(x);
        self.stream.push(x);
    }

    pub fn send_root(&mut self, root: &Hash) {
        root_halves(root).into_iter().for_each(|x| self.send(x));
    }

    pub fn sample(&mut self) -> F192 {
        self.chain.sample()
    }

    pub fn into_proof(self) -> Proof {
        Proof { stream: self.stream }
    }
}

/// The verifier's side: reads scalars off a proof and draws the same challenges.
pub struct VerifierChain<'a> {
    chain: Chain,
    stream: &'a [F192],
}

#[allow(clippy::should_implement_trait)]
impl<'a> VerifierChain<'a> {
    pub fn new(label: &[u8], proof: &'a Proof) -> Self {
        Self {
            chain: Chain::new(label),
            stream: &proof.stream,
        }
    }

    pub fn next(&mut self) -> Result<F192, TranscriptError> {
        let (&x, rest) = self.stream.split_first().ok_or(TranscriptError::Exhausted)?;
        self.stream = rest;
        self.chain.pending.push(x);
        Ok(x)
    }

    pub fn next_root(&mut self) -> Result<[F192; 2], TranscriptError> {
        let scalars = [self.next()?, self.next()?];
        halves_root(&scalars).map(|_| scalars)
    }

    pub fn sample(&mut self) -> F192 {
        self.chain.sample()
    }

    pub fn finish(&self) -> Result<(), TranscriptError> {
        if self.stream.is_empty() {
            Ok(())
        } else {
            Err(TranscriptError::Trailing)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roots_round_trip_and_sides_agree() {
        let root: Hash = std::array::from_fn(|i| (7 * i + 3) as u8);
        assert_eq!(halves_root(&root_halves(&root)), Ok(root));
        let mut p = ProverChain::new(b"label");
        p.send_root(&root);
        let a = p.sample();
        p.send(F192::new(1, 2, 3));
        let b = p.sample();
        let proof = p.into_proof();
        let mut v = VerifierChain::new(b"label", &proof);
        assert_eq!(v.next_root(), Ok(root_halves(&root)));
        assert_eq!(v.sample(), a);
        assert_eq!(v.next(), Ok(F192::new(1, 2, 3)));
        assert_eq!(v.sample(), b);
        assert_eq!(v.finish(), Ok(()));
    }
}
