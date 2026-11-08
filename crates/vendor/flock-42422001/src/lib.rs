// Vendored from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/flock/src/lib.rs.
// Changed: its one circuit, the BLAKE2s block (`hash`, with the `gf2` adder gadgets), is not vendored, and `slice`
// keeps that module's circuit-agnostic `SliceClaim`; the module `keccak` is new in this repository (the Keccak-f[1600]
// block, docs/leanvm/flock/KECCAK.md). Ported onto leanVM c445e3d5's `primitives`, `parallel` and `pcs`
// (crates/vendor/leanvm-c445e3d5) in place of 42422001's own copies: the parts of those that c445e3d5 lacks are
// modules here, `field` (GF(2^8) and φ₈), `lagrange` (the φ₈ barycentric weights) and `ntt` (the GF(2^8) additive NTT),
// and the transcript is the trait of `transcript` (formerly the crate `lv42_fiat_shamir`).
// MIT OR Apache-2.0 (see LICENSE-MIT, LICENSE-APACHE and AGENTS.md at the repository root).
// CREDIT: https://github.com/succinctlabs/flock, MIT OR Apache-2.0.
//! flock: a batched R1CS proving system for hash circuits over GF(2), reduced
//! to evaluation claims on the committed packed witness.
//!
//! Protocol flow (all challenges from the shared [`transcript`]):
//!   1. The caller commits the packed Boolean witness `q_flock` (inside the VM's
//!      one stacked [`pcs`] commitment).
//!   2. [`zerocheck`] reduces `a·b ⊕ c = 0` over the cube to evaluation claims
//!      on `(â, b̂, ĉ)`.
//!   3. [`lincheck`] reduces those to the `2^k_skip` bit-slice values of `z` at
//!      one point, against the per-block matrices.
//!   4. The PCS binds that family of slices ([`slice::SliceClaim`]) to the
//!      commitment.
//!
//! [`keccak`] is the one circuit: the Keccak-f[1600] permutation as a per-block
//! R1CS, its witness generation and its reduction entry point. Steps 2 to 4
//! above are circuit-agnostic: they take the block shape as plain numbers and
//! reach the matrices only through [`lincheck::LincheckCircuit`], whose impl
//! walks the circuit rather than reading any matrix.

pub mod field;
pub mod keccak;
pub mod lagrange;
pub mod lincheck;
pub mod ntt;
pub mod slice;
pub mod transcript;
mod witness;
pub mod zerocheck;
