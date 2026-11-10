// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! What the block's openings prove, for the univariate PIOP's commitments: each stack is the EIP draft's committed
//! polynomial (`crates/pcs_claim`, `docs/PCS_CLAIM.md`): the multilinear in the stack's `vars` variables of its
//! `2^vars` words (the zero tail past its blocks included), committed as `(root, ood)` and claimed at one point a
//! claim (SPEC.md §8), each claim opened by one WHIR opening of PCS version 1 (leanVM's WHIR at rate `1/2`, its ladder,
//! `64` lanes at its first fold).
//!
//! The stack's words are its leading whole lanes, the rest zero: the commitment encodes those lanes alone, and is the
//! whole stack's ([`pcs_claim::commit_words`]).

use fiat_shamir::transcript::Proof;
use pcs_claim::PcsClaim;
pub use pcs_claim::{Commitment as Committed, LANE_FOLD, LOG_INV_RATE, wire_proof};
use primitives::field::{F64, F192};

/// Commit to a stack of whole lanes in `vars` variables (`words.len()` a multiple of `2^(vars - 6)`), keeping the
/// Merkle tree alone: the opening encodes the rows its queries open again from the stack.
pub fn commit(words: &[F64], vars: usize) -> Committed {
    pcs_claim::commit_words(words, vars, false)
}

/// [`commit`], keeping the codeword too (`2^LOG_INV_RATE` words per word of the stack), from which the first opening
/// reads the rows its queries open instead of encoding them again, and which it frees. The root, the out-of-domain
/// answer and the proofs are [`commit`]'s.
pub fn commit_keeping_codeword(words: &[F64], vars: usize) -> Committed {
    pcs_claim::commit_words(words, vars, true)
}

/// The claim `stack(point) = value` on `committed`.
pub fn claim(committed: &Committed, point: &[F192], value: F192) -> PcsClaim {
    committed.claim(point.to_vec(), value)
}

/// Prove `stack(point) = value` (one opening of the claim). A kept codeword serves this opening and is freed after it.
pub fn open(words: &[F64], committed: &Committed, point: &[F192], value: F192) -> Proof {
    pcs_claim::open_words(words, committed, &claim(committed, point, value))
}

/// Check an opening of `claim`: the EIP draft's `pcs_verify` (`pcs_claim::verify_claim`).
pub fn verify(claim: &PcsClaim, proof: &verifier::Proof) -> Result<(), verifier::VerifierError> {
    pcs_claim::verify_claim(claim, proof)
}
