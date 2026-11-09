// Vendored from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/flock/src/hash.rs: its
// circuit-agnostic `SliceClaim` (its doc made circuit-agnostic) and `min_n_blocks_log`. The rest of that file,
// upstream's block, is not vendored (src/lib.rs; this repository's one block is `keccak`). MIT OR Apache-2.0 (see
// LICENSE-MIT, LICENSE-APACHE and AGENTS.md at the repository root).
// CREDIT: https://github.com/succinctlabs/flock, MIT OR Apache-2.0.
//! The claim Flock's reduction leaves on the committed witness, and the block count's log.

use primitives::field::F192;

/// Minimum `n_blocks_log` needed to prove `n_blocks` compressions.
pub fn min_n_blocks_log(n_blocks: usize) -> usize {
    assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
    n_blocks.next_power_of_two().trailing_zeros() as usize
}

/// The one claim on the committed witness `q_flock` left by the Flock zerocheck
/// + lincheck reduction, for the PCS to discharge: the `2^k_skip`
/// bit-slice values of `z` at `suffix_point`, transmitted and pinned inside the
/// reduction by lincheck's terminal identity (which batches A, B, the
/// constant-wire pin and C), so the PCS only has to bind them to the
/// commitment.
///
/// This is the clean seam between Flock's reduction and the PCS.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SliceClaim {
    pub suffix_point: Vec<F192>,
    pub s_hat_v: Vec<F192>,
}
