// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The commitments the membership proof's claims are on, and their openings: the EIP draft's PCS claims
//! (`crates/pcs_claim`, version 1, `docs/PCS_CLAIM.md`). A table is committed as the multilinear of its `2^n` words
//! (leanVM's WHIR, rate `1/2`), with its out-of-domain answer, which binds the root to one table; a claim is a plain
//! evaluation of that multilinear at a point, one point a claim, each opened by one WHIR opening.
//!
//! The openings are leanVM's WHIR, which is not zero-knowledge: the protocol's zero knowledge assumes a
//! zero-knowledge PCS opening (ZK-WHIR), as the EIP does (`HIDING.md`).

use fiat_shamir::merkle::Hash;
pub use pcs_claim::{Codeword, Committed, MAX_VARIABLES, MIN_VARIABLES, PcsClaim, wire_proof};
use primitives::field::{F64, F192};

/// An opening proof.
pub type Proof = fiat_shamir::transcript::Proof;

/// A claim on a committed table: its multilinear takes `value` at `point`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub point: Vec<F192>,
    pub value: F192,
}

/// A commitment as the claims name it: the Merkle root and the out-of-domain answer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Commitment {
    pub root: Hash,
    pub ood: F192,
}

impl Commitment {
    pub fn of(committed: &Committed) -> Self {
        Self {
            root: committed.root,
            ood: committed.ood,
        }
    }

    /// The PCS claim `claim` on this commitment, of a table in `n` variables.
    pub fn pcs_claim(&self, claim: &Claim) -> PcsClaim {
        PcsClaim {
            n: claim.point.len() as u8,
            root: self.root,
            ood: self.ood,
            point: claim.point.clone(),
            value: claim.value,
        }
    }
}

/// Commit to a table of `2^n` words, keeping its codeword for the openings or not: its trailing zero lanes left out
/// of the words kept and every zero lane out of the encodes (`pcs_claim::commit`: the root, the out-of-domain answer
/// and every opening are the whole table's); [`Committed::words`] are the lanes kept.
pub fn commit(words: Vec<F64>, keep_codeword: bool) -> Committed {
    #[allow(unused_mut)]
    let mut committed = pcs_claim::commit(words, keep_codeword);
    #[cfg(test)]
    if let Some(z) = fixed_ood_point(committed.n) {
        committed.commitment.ood = pcs_claim::evaluate_lanes(committed.words(), &z);
    }
    committed
}

#[cfg(test)]
thread_local! {
    /// Test-only: out-of-domain points in place of the root-derived ones (the hiding test fixes every challenge,
    /// these included, to see the revealed scalars as a function of the prover's randomness): the seed, and the
    /// count of commitments made since it was set, which picks the point.
    pub(crate) static FIXED_OOD: std::cell::RefCell<Option<(u64, u64)>> = const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
fn fixed_ood_point(n: usize) -> Option<Vec<F192>> {
    FIXED_OOD.with(|fixed| {
        let mut fixed = fixed.borrow_mut();
        let (seed, count) = fixed.as_mut()?;
        let mut rng = primitives::test_rng::Rng::new(*seed ^ (*count << 32) ^ n as u64);
        *count += 1;
        Some((0..n).map(|_| F192::new(rng.next_u64(), rng.next_u64(), rng.next_u64())).collect())
    })
}

/// The table's multilinear at `point`: of the `2^n` words (`n = point.len()`) whose leading whole lanes are `words`
/// and the rest zero, as [`Committed::words`] holds them.
pub fn evaluate(words: &[F64], point: &[F192]) -> F192 {
    if words.len() == 1 << point.len() {
        pcs_claim::evaluate(words, point)
    } else {
        pcs_claim::evaluate_lanes(words, point)
    }
}

/// Open `claim` on `committed`; a kept codeword serves it, and is freed or kept for another opening.
pub fn open(committed: &Committed, claim: &Claim, codeword: Codeword) -> Proof {
    let claim = Commitment::of(committed).pcs_claim(claim);
    pcs_claim::open(committed.words(), committed, &claim, codeword)
}

/// Check an opening of `claim` against `commitment`.
pub fn verify(commitment: &Commitment, claim: &Claim, proof: &Proof) -> Result<(), verifier::VerifierError> {
    pcs_claim::verify_claim(&commitment.pcs_claim(claim), &wire_proof(proof))
}
