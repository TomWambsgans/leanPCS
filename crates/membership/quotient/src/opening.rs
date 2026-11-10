// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The commitments the membership proof's claims are on, and their openings: the EIP draft's PCS claims
//! (`crates/pcs_claim`, version 1, `docs/PCS_CLAIM.md`). A table is committed as the multilinear of its `2^n` words
//! (leanVM's WHIR, rate `1/2`), with its out-of-domain answer, which binds the root to one table; a claim is a plain
//! evaluation of that multilinear at a point, one point a claim, each opened by one WHIR opening.
//!
//! The openings are leanVM's WHIR, which is not zero-knowledge: the protocol's zero knowledge assumes a
//! zero-knowledge PCS opening (ZK-WHIR), as the EIP does (`HIDING.md`).

use fiat_shamir::merkle::Hash;
pub use pcs_claim::{Committed, MAX_VARIABLES, MIN_VARIABLES, PcsClaim, wire_proof};
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

/// Commit to a table of `2^n` words.
pub fn commit(words: Vec<F64>) -> Committed {
    pcs_claim::commit(words)
}

/// The table's multilinear at `point`.
pub fn evaluate(words: &[F64], point: &[F192]) -> F192 {
    pcs_claim::evaluate(words, point)
}

/// Open `claim` on `committed`.
pub fn open(committed: &Committed, claim: &Claim) -> Proof {
    pcs_claim::open(committed, &Commitment::of(committed).pcs_claim(claim))
}

/// Check an opening of `claim` against `commitment`.
pub fn verify(commitment: &Commitment, claim: &Claim, proof: &Proof) -> Result<(), verifier::VerifierError> {
    pcs_claim::verify_claim(&commitment.pcs_claim(claim), &wire_proof(proof))
}
