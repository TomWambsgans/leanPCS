// Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
//! The prover of SPEC.md (`PROVER.md`): on an execution trace of the Keccak VM (leanVM 9d50c92a3's own execution,
//! dumped by `dump_keccak/`), the stream the verifier reads and one WHIR opening per commitment.
//!
//! - [`trace`]: the trace leanVM wrote;
//! - [`flock`]: Flock on the Keccak-f block;
//! - [`poly`]: the Cantor subspaces' transforms (vectorized in `quotient::ntt`), basis `B`, the extension cosets;
//! - [`columns`]: `C1`'s and the setup's polynomials;
//! - [`fingerprint`], [`prints`], [`bus`]: the bus's fingerprints (one point at a time, and eight), leaves and
//!   product heap;
//! - [`quotients`]: the tree, leaf and constraint quotients;
//! - [`stack`]: the three stacks, as the verifier's layouts place the columns;
//! - [`weight`], [`batch`]: the combined claims' weights, the batching sumcheck (point-claim ABI);
//! - [`opening`]: the point claims proven with leanVM's WHIR;
//! - [`prove`]: the driver, and [`check`]: the identities on the domain.

pub mod batch;
pub mod bus;
pub mod check;
pub mod columns;
pub mod fingerprint;
pub mod flock;
pub mod opening;
pub mod poly;
pub mod prints;
pub mod prove;
pub mod quotients;
pub mod setup;
pub mod stack;
pub mod trace;
pub mod weight;
