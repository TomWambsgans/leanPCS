// Adapted from leanVM (https://github.com/leanEthereum/leanVM), branch PCS-openings-aggregation, commit 651453c6,
// file crates/membership/evm/src/lib.rs. MIT OR Apache-2.0; see AGENTS.md.
//! The membership verifier as an EVM contract, run in tests on `evm_link::machine` (revm with `FIELD_MUL`, a product
//! in `GF(2^192)`, and EIP-8141's frames).
//!
//! The contract is not written by hand. [`quotient::contract`] runs the Rust verifier
//! (`quotient::protocol::reduce`) on a scalar type that records every operation, and compiles the recorded
//! graph: the two cannot disagree on what is computed. A field element is the low 192 bits of a word, limb 0
//! lowest; addition is `XOR`.

#[cfg(test)]
mod adversarial;
mod codegen;
mod contract;
#[cfg(test)]
mod lean;
pub mod quotient;
mod record;
