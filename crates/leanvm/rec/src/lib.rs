// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! Recursion for the univariate verifier of the Keccak VM (docs/leanvm/rec/SPEC-REC.md): `π2`, a SNARK of `π1`'s
//! verifier minus its openings, its circuit compiled from that verifier's recorded graph, and the contract that runs
//! `π2`'s verifier.
//!
//! `π1` is `crates/leanvm/univariate`'s proof. Its verifier, run on the recorder's symbol, is a graph
//! (`leanvm_statement::evm::record`): the stream's reads, the Keccak-256 chain, `E`'s additions and products, the
//! checks, and the declared claims. That graph is the circuit `π2` proves, PCS openings excluded.
//!
//! - [`eval`]: the graph evaluated on a real proof's calldata, every node's value: the witness `π2`'s prover starts
//!   from, checked against the recorded claims of the committed test vectors.
//! - [`circuit`]: `π2`'s circuit (D16v) and its witness, compiled from the graph; `circuit::spec` is the
//!   PIOP's interface (SPEC-REC.md §10).
//! - [`pi2`]: `π2`'s PIOP: prover, verifier, contract.

#![forbid(unsafe_code)]

pub mod circuit;
pub mod eval;
pub mod pi2;

use leanvm_univariate::{KECCAK_REC4, Shape, Variant};

/// π1's variant under the recursion: π1-rec4 (`docs/leanvm/univariate/SPEC.md` §14.4; π1-rec3 before it, which `formal/`
/// states).
pub const PI1: Variant = KECCAK_REC4;

/// The committed real π1 proofs the recursion's tests read (`crates/leanvm/univariate/tests/vectors/`): at the
/// reference shape (128 signatures) and at 400.
pub const PI1_VECTOR_128: &str = "keccak128_rec4";
pub const PI1_VECTOR_400: &str = "keccak_rec4";

/// The reference shape: the Keccak VM's 128-signature workload (`leanvm_statement::shapes::reference()`, leanVM
/// 9d50c92a3, 154,148 cycles): memory `2^20`, bytecode `2^18`, rows XOR, MUL, SET, DEREF, JUMP, SHA3.
pub const REFERENCE: Shape = Shape {
    log_memory: 20,
    log_bytecode: 18,
    table_rows: [24_260, 36_229, 24_626, 35_812, 15_509, 17_712],
};

/// Keccak-256's rate in bytes.
pub const KECCAK_RATE: usize = 136;

/// Keccak-f\[1600\] permutations of one Keccak-256 of `len` bytes: pad10*1 adds at least one byte.
pub fn permutations(len: usize) -> usize {
    len / KECCAK_RATE + 1
}
