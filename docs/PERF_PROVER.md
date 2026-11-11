<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# The provers' speed

Both provers of the EIP draft's benchmarks: the membership proof (`crates/membership/quotient`) and the recursion's
pipeline (`crates/leanvm/rec/tests/pipeline.rs`: leanVM's trace of 128 signatures → π1-rec4 and its three openings →
π2 and its four openings). Every change below is a prover change: the proofs are the same byte for byte, so the
calldata, the claims, the gas and the Lean are untouched. Superseded figures (64 threads, the M4 Max, earlier
protocols) are in [`HISTORY.md`](HISTORY.md), "Provers".

## How it is measured

`bench.sh` reproduces both benchmarks. On h3 (AMD EPYC 9355P, Zen 5, AVX-512; cores 0-7 are two of its eight CCDs),
with `RUSTFLAGS` as [`README.md`](../README.md) gives them for Zen 5:

```sh
LEANVM_NUM_THREADS=8 BENCH_PIN="taskset -c 0-7" REPEAT=5 sh bench.sh
```

It builds first (unpinned), then runs the two provers `REPEAT` times interleaved (membership, leanVM, membership, …)
and reports their medians: the membership figure is `cargo bench -p quotient --bench membership`'s prover total (one
cold proof a run), the leanVM figure the pipeline's total (`PIPELINE_REPEAT=5`, each run itself the median of five
warm passes). Then the gas: the membership contract's `gas_report` and π2's `real_end_to_end`. It ends with the EIP
draft's table: the prover column is the median plus 0.1 s a PCS claim (1.01 + 3 · 0.1 = 1.3 s; 2.29 + 7 · 0.1 =
3.0 s), the PIOP column `max(standard, floor)` of the PIOP's frame alone (20,097 and 40,396 gas).

The proofs are pinned: the membership bench prints a proof digest (and `protocol::tests::proofs_are_pinned` pins a
toy circuit's), and the pipeline asserts the Keccak-256 fingerprints of π1's stream and openings and π2's stream and
openings (`REFERENCE_PRINTS`). A prover change must leave them as they are.

## Per phase

8 threads (cores 0-7), medians of five interleaved runs, 2026-11-11, `main`:

| | time | peak memory |
|---|---:|---:|
| membership: reduction (witness, `W`, the quotient, `T`) | 0.66 s | |
| membership: three openings | 0.34 s | |
| **membership: prover total** | **1.01 s** | 6.0 GiB |
| leanVM: π1-rec4, trace to its stream | 0.86 s | |
| leanVM: π1-rec4's three openings (π2's witness replayed meanwhile, about 0.01 s) | 0.18 s | |
| leanVM: π2's proof | 0.74 s | |
| leanVM: π2's four openings (π2v4; π2v3's five: 0.73 s) | 0.51 s | |
| **leanVM: total a proof** (π2v3: 2.52 s) | **2.29 s** | 15.6 GB |

From `perf` at 8 threads: membership, Keccak-f (the Merkle leaves and nodes) 28%, the WHIR encodes' radix-8 layers
(`run_layers`) 20% and their sweeps 7%, the kernel clearing fresh pages 6%, the quotient's block-wise pass 5%,
`memmove` 4.5%, the quotient crate's transforms 6%; leanVM, Keccak-f 22%, `run_layers` 15%, π2's numerators on the
extension coset 8%, Flock's zerocheck 9%, the quotient crate's transforms 9%, `memmove` 3.5%. All eight cores are busy
throughout but at a phase's start: the time is work, not waiting.

## Optimisations

Each in the file its header names; every one keeps the proofs.

- **Out-of-domain answers in one pass** over every lane, unreduced `dot_base` products (`pcs::whir::dense_lane_inner_products`;
  `pcs_claim::evaluate_lanes`), and the lane products kept for the openings' first lane round
  (`pcs_claim::Commitment::ood_lanes`, `recursive_prover_with_lane_tensors_known`).
- **Several openings on one commitment at once** (π2's `Q`: `pcs_claim::open_words_batch`,
  `recursive_prover_with_lane_tensors_batch`): their lane rounds read the stack twice in all, not twice each.
- **`eq` low weights never written out** (`pcs::whir::Low::Eq`): the product of two tables of `2^11`, exact.
- **Tables committed up to their last nonzero lane** (`pcs_claim::commit_lanes`, `opening::commit_lanes`): the
  commitment and openings of the leading lanes are those of the whole stack.
- **All-zero lanes skipped** in commitments, openings' re-encodes and lane rounds (`pcs::whir::commit_tree_skipping_in`,
  `encoded_rows_skipping`, `recursive_prover_with_lane_tensors_skipping`, `lane_inner_products`, `collapse_lanes`,
  `dense_lane_inner_products_skipping`), and left out of kept codewords (`commit_skipping`, `L0Rows::Compact`,
  `AdditiveNttF64::encode_two_sweep_blocks_into`): π2's `Q` keeps 3 rather than 4 GiB.
- **The encode in two block-wise sweeps** from the message as it lies (`AdditiveNttF64::encode_two_sweep_with`,
  `encode_two_sweep_blocks_with`), into the kept codeword in place.
- **A batch's openings made in turn keep their level-1 codewords up to 2 GiB** (`LEAN_LIGERO_BYTES_IN_TURN`; a lone
  opening 1 GiB, `LEAN_LIGERO_BYTES`): their queried rows are read, not encoded again.
- **Memory mapped by the workers** (`pcs_claim::mapped_words`): each worker first-touches its own pages; the
  commitments run largest first so that each freed buffer serves the next.
- **No copies on one thread** in the membership prover: the quarters' transforms read their source as their first
  pass writes them (`ntt::values_upper`, `values_upper_many`); the witness's values made in `W`'s allocation.
- **The membership index keeps its codeword** (`opening::commit_lanes_keeping_codeword`, `opening::open_keeping`): the wiring's opening, made
  by every proof, encodes no rows again.
- **The cells' digest by the batched Keccak-256** (`protocol::cells_digest`, `hash_many`): the same digest.
- **The public weight's tensor factored** in the quotient's block-wise pass (`protocol.rs`, `quotient_block`): one
  `Ex8` of the three lowest coordinates times one of 256.
- **The quotient crate's transforms** (`quotient::ntt`, shared by the membership prover, π1 and π2): a row's own three
  layers eight rows at a time, transposed (`own_transposed`, `group_steps`); the row layers two at a time (`quads`,
  `tile_layers`): forward 7.66 → 6.34, inverse 10.3 → 5.9 cycles a vector of butterflies.
- **AVX-512 Keccak-256** with its transposes in registers (`primitives/src/hash.rs`); affine dispatches, each worker
  the same contiguous range every call (`parallel/src/lib.rs`); jemalloc's extents on transparent huge pages
  (`bench/src/allocator.rs`).

## Rejected

Measured, no gain or a loss:

- Keccak-f's round schedule: unrolled by two or 24, parities recomputed, two or four groups interleaved, states in L1.
- The pcs NTT's deepest layers block by block in L1: faster on 8-lane tiles, slower on 64-lane ones.
- Other two-sweep tiles (`TWO_SWEEP_TILE_WORDS` `2^16`, `2^18`), first-sweep groups, gathered rows; the quotient
  crate's wide passes of 8 to 12 layers; its row layers two rows a step.
- Keeping every table's codeword, or `H`'s for its two openings (membership, `f96a7938`): up to +5 GiB of peak for
  ±20 ms.
- The openings concurrently on OS threads sharing the pool: slower, +1.5 to 2.7 GiB.
- A batch's level-0 rows encoded once for all its openings, or `LEAN_BATCH` 16: holds every opening's level-1
  commitment at once (+1.5 GiB).
- π1's openings overlapping π2's proof (a `PIPELINE_OVERLAP` knob, since removed): the machine is saturated; no gain,
  +0.4 GB.
- Reusing `Q`'s codeword buffer between proofs, caching π1's setup commitment `F`: each well under 1%.
- Shrinking the commitments' encoding buffer to the encoded lanes: the openings then map fresh memory.

## What bounds it

About 40% of both provers is two kernels near their bounds, their counts fixed by PCS version 1 (the Merkle leaves
and nodes, the codewords' sizes):

- **Keccak-f[1600], eight states a ZMM** (`primitives::hash`): 100 cycles a permutation on one core (42-45 M/s).
  A round is 95 vector ALU operations; at the measured issue rates 26 cycles a round is the bound, against 33. The
  rest is θ's barrier and spills (25 lanes, 5 parities, 5 θ effects in 32 registers).
- **The additive NTT's butterfly** (`pcs`, `quotient`): `vpclmulqdq` issues once every two cycles on Zen 5 at any
  width, so eight butterflies cost at least 4 cycles; the radix-8 sweep takes 4.8 in L1, 5.3-7 from L2.

The rest, each a few percent: π2's numerators on the extension coset (about 150 products a point, within 3x of
`vpclmulqdq`'s bound), Flock's bit rounds, the commitments' memory sweeps (about 150 GB/s on two CCDs), the cold
membership proof's first touches of its 6 GiB. Not tried: the clmul-free half of a butterfly layer on GFNI (about
1.4x at best on the butterflies); Merkle leaves hashed from compact rows; one fused kernel interleaving a tile's
hashing with the next tile's layers.

## Tests

- Differential tests of every low-memory and fast path against the dense prover: `pcs`'s
  `src/whir/adversarial.rs` (the lean paths against the untouched `commit` and `recursive_prover_with_basis`,
  randomized shapes), `whir::tests::skipped_zero_lanes_encode_the_codeword`, `batched_openings_skip_zero_lanes`;
  `pcs_claim::tests::zero_lanes_left_out_change_no_proof` and `pcs_claim`'s `tests/self_consistency.rs` (randomized
  stacks, zero-lane patterns and points: every proof the same alone or batched, kept, compact or encoded again; `wide`
  ignored); the membership proof's pinned digest.
- Miri: `cargo +nightly miri test --target x86_64-unknown-linux-gnu -p pcs --lib miri_` and `-p quotient --lib
  miri_` (`MIRIFLAGS=-Zmiri-ignore-leaks`) run `miri_batched_openings`, `miri_compact_codeword`,
  `miri_fused_layers_are_the_domains` and `pcs`'s earlier `miri_` tests clean, on the portable lanes (the AVX-512
  paths are not Miri's; under Miri `primitives::stream`'s non-temporal stores are ordinary copies). The in-place NTT
  encodes are free of the aliasing bug Miri flags in leanVM's (`additive_ntt_f64.rs`).
- The workspace's tests also run with `CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=true
  CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true`.
