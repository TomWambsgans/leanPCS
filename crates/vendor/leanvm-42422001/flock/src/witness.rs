// Vendored from leanVM (https://github.com/leanEthereum/leanVM), commit 42422001, file crates/flock/src/witness.rs,
// without the BLAKE2s block's bit and adder helpers.
// MIT OR Apache-2.0 (see LICENSE-MIT, LICENSE-APACHE and AGENTS.md at the repository root).
// CREDIT: https://github.com/succinctlabs/flock (flock-prover), MIT OR Apache-2.0.
//! Bit-packing and the witness driver for the block R1CS modules (`keccak`).

use primitives::bits::bit_transpose_64bytes;
use primitives::stream::Stream;

/// of the `u64` words on a little-endian target.
pub(crate) fn packed_bytes(words: &[u64]) -> &[u8] {
    const _: () = assert!(
        cfg!(target_endian = "little"),
        "packed witness bytes assume little-endian"
    );
    // SAFETY: `u64` has no padding or invalid bit patterns, and `u8`'s
    // alignment divides `u64`'s, so the words are a valid `8 · len` byte slice.
    unsafe { core::slice::from_raw_parts(words.as_ptr().cast::<u8>(), words.len() * 8) }
}

// ---------------------------------------------------------------------------
// Generic witness packing driver.
// ---------------------------------------------------------------------------

/// Drive the parallel chunked witness build for `n_blocks` instances padded
/// to `2^n_blocks_log` slots. Returns `(z, a, b, z_lincheck)`: the three
/// bit-packed `u64` tables (`K / 64` words per instance) and the lincheck
/// byte stripe.
///
/// `per_block(initial, z_u64, a_u64, b_u64)` populates one block's worth of
/// `(z, a, b)` data: 3 zero-initialized `u64`-buffers of length `K / 64`.
/// `K` is derived from `k_log`. `initial_states.len()` may be less than
/// `2^n_blocks_log`.
///
/// `padding` controls what fills the trailing `2^n_blocks_log −
/// initial_states.len()` slots:
/// - `None`: leave them all-zero (trivial constraint satisfaction).
/// - `Some(p)`: build a real block from `p` in every padding slot. Encoders
///   that pin a constant wire need this so the constant column is all-ones
///   across *every* batched instance (see `lincheck's `LincheckCircuit::const_pin_col``).
pub(crate) fn drive_witness_packed_and_lincheck<S: Sync, F>(
    initial_states: &[S],
    padding: Option<&S>,
    n_blocks_log: usize,
    k_log: usize,
    per_block: F,
) -> (Vec<u64>, Vec<u64>, Vec<u64>, Vec<u8>)
where
    F: Fn(&S, &mut [u64], &mut [u64], &mut [u64]) + Sync,
{
    let k = 1usize << k_log;
    let u64_per_block = k / 64;
    let n_total = 1usize << n_blocks_log;
    let n_blocks = initial_states.len();
    assert!(
        n_blocks <= n_total,
        "{n_blocks} blocks > 2^{n_blocks_log} = {n_total} slots"
    );
    // A group is one stripe's eight blocks; below eight, one group holds them all and its stripe's other bits stay zero.
    let group_blocks = n_total.min(8);
    let n_groups = n_total / group_blocks;

    let total_words = n_total * u64_per_block;
    // SAFETY (x4): group `g` publishes chunk `g` of every table in full below, and the chunk counts match.
    // The z/a/b chunks are a group's blocks of packed words, and the stripe chunk is the transpose's k bytes.
    let mut z = unsafe { primitives::uninit_vec::<u64>(total_words) };
    let mut a = unsafe { primitives::uninit_vec::<u64>(total_words) };
    let mut b = unsafe { primitives::uninit_vec::<u64>(total_words) };
    let mut z_lincheck = unsafe { primitives::uninit_vec::<u8>(n_groups * k) };

    // Four output tables at two widths, indexed by the same group: `z`/`a`/`b`
    // take the group's blocks' packed words, `z_lincheck` takes one byte stripe.
    let group_words = group_blocks * u64_per_block;
    let scratch_words = 8 * u64_per_block;
    let z_chunks = parallel::Chunks::new(&mut z, group_words);
    let a_chunks = parallel::Chunks::new(&mut a, group_words);
    let b_chunks = parallel::Chunks::new(&mut b, group_words);
    let stripe_chunks = parallel::Chunks::new(&mut z_lincheck, k);
    debug_assert_eq!(z_chunks.count(), stripe_chunks.count());

    // Each group builds in its worker's scratch, which stays in cache, then streams out.
    //
    //     scratch  z | a | b   8 blocks each, zeroed then ORed into
    //     stripe               the bit transpose of the 8 z blocks
    //
    // Building in place instead would fetch every output line before writing it.
    parallel::map_reduce_with_state(
        z_chunks.count(),
        || (vec![0u64; 3 * scratch_words], vec![0u8; k]),
        || (),
        |(scratch, stripe), (), g| {
            scratch.fill(0);
            let (z_grp, rest) = scratch.split_at_mut(scratch_words);
            let (a_grp, b_grp) = rest.split_at_mut(scratch_words);
            for k_in in 0..group_blocks {
                let global_idx = 8 * g + k_in;
                let init: &S = if global_idx < n_blocks {
                    &initial_states[global_idx]
                } else if let Some(p) = padding {
                    // Fill the padding slot with a real block so its constant
                    // wire is set (see `padding` docs above).
                    p
                } else {
                    // No padding block, leave this slot zero.
                    continue;
                };
                let range = k_in * u64_per_block..(k_in + 1) * u64_per_block;
                per_block(
                    init,
                    &mut z_grp[range.clone()],
                    &mut a_grp[range.clone()],
                    &mut b_grp[range],
                );
            }

            // Bit-transpose 8 z chunks into the lincheck stripe.
            for (i, out) in stripe.as_chunks_mut::<64>().0.iter_mut().enumerate() {
                let rows: [[u8; 8]; 8] = std::array::from_fn(|l| z_grp[l * u64_per_block + i].to_le_bytes());
                bit_transpose_64bytes(rows.as_flattened().try_into().expect("64 bytes"), out);
            }

            // SAFETY: each group `g` takes chunk `g` of each table exactly once, and
            // all four tables stay borrowed for the whole dispatch.
            let stream = Stream::new();
            unsafe {
                stream.copy(z_chunks.get(g), &z_grp[..group_words]);
                stream.copy(a_chunks.get(g), &a_grp[..group_words]);
                stream.copy(b_chunks.get(g), &b_grp[..group_words]);
                stream.copy(stripe_chunks.get(g), stripe);
            }
        },
        |(), ()| (),
    );

    (z, a, b, z_lincheck)
}
