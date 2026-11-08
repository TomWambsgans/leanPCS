// Vendored from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/flock/src/lib.rs.
// Changed: its one circuit, the BLAKE2s block (`hash`, with the `gf2` adder gadgets), is not vendored, and `slice`
// keeps that module's circuit-agnostic `SliceClaim`; the module `keccak` is new in this repository (the Keccak-f[1600]
// block, docs/leanvm/flock/KECCAK.md). The crate's `fiat_shamir` is crates/vendor/leanvm-42422001/fiat_shamir (the
// transcript as a trait).
// MIT OR Apache-2.0 (see LICENSE-MIT, LICENSE-APACHE and NOTICE.md at the repository root).
// CREDIT: https://github.com/succinctlabs/flock, MIT OR Apache-2.0.
//! flock: a batched R1CS proving system for hash circuits over GF(2), reduced
//! to evaluation claims on the committed packed witness.
//!
//! Protocol flow (all challenges from the shared [`fiat_shamir`] transcript):
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

pub mod keccak;
pub mod lincheck;
pub mod slice;
mod witness;
pub mod zerocheck;
