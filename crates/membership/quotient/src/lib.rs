// Part of this repository. Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch
// PCS-openings-aggregation, commit 651453c6 (`flock::quotient`). MIT OR Apache-2.0; see AGENTS.md.
//! Merkle membership with Keccak-256, its claims the EIP's PCS claims ([`opening`], `pcs_claim`), zero knowledge
//! assuming a zero-knowledge PCS opening (`HIDING.md`: the rank conditions are checked at random challenges),
//! reduced to six one-point evaluation claims on four commitments by a few field elements and no sumcheck: the
//! protocol of leanVM's `flock::quotient` (`doc/quotient/main.tex` there), on a circuit of one χ gate on bits, its
//! claims opened by leanVM's WHIR.

pub mod circuit;
pub mod domain;
pub mod ntt;
#[cfg(test)]
mod hiding;
pub mod opening;
pub mod protocol;
pub mod statement;
pub mod transcript;
