// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! A univariate PIOP for the Keccak VM's statement (leanVM 9d50c92a3), for the EVM: docs/leanvm/univariate/SPEC.md.
//!
//! [`verifier::reduce`] is the verifier, generic over the scalar it computes on: on `E` with the Keccak-256 chain it
//! is the contract's verifier in Rust; on the recorder's symbol it is the graph [`contract`] compiles to EVM code.

#![forbid(unsafe_code)]

pub mod claims;
pub mod contract;
pub mod domain;
pub mod heap;
pub mod prover;
pub mod stacks;
pub mod verifier;

pub use leanvm_statement::transcript::FsShape;
pub use leanvm_statement::flock_min::Variant;
pub use verifier::{Claims, KECCAK_MAIN, KECCAK_REC3, Opening, Reduced, Shape, reduce};
