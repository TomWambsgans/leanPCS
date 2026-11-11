<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# The provers at 8 threads (branch `perf2/provers`)

Both benchmarks of the EIP draft, timed as its figures are: `LEANVM_NUM_THREADS=8 taskset -c 0-7` on h3 (AMD EPYC
9355P, Zen 5, AVX-512; cores 0-7 are two of its eight CCDs), `RUSTFLAGS="-C target-cpu=x86-64-v4 -C
target-feature=+gfni,+vpclmulqdq,+vaes,+pclmulqdq,+avx512vbmi,+aes,+bmi2"`. `main` is `866ba889`. Every change is a
prover change: the proofs are `main`'s byte for byte (the membership bench's digest `64e58899266e…`; the pipeline's
π1 stream, π1 openings, π2 stream and π2 openings fingerprints `37a7cf1d…`, `b147a1f6…`, `f6dd0e79…`, `46293543…`), so
the calldata, the claims, the gas and the Lean are untouched; they are the same at 1, 3, 8 and 64 threads.

## Numbers

`main` (h3's build `/root/pcs-perf/final/all`, identical to `866ba889`) and this branch run alternately, each run
under the shared bench lock after `waitidle.sh`, five rounds, medians; the membership figures are
`cargo bench -p quotient --bench membership`'s (one cold proof), the leanVM figures the pipeline's
(`tests/pipeline.rs`, `PIPELINE_REPEAT=5`, its own median of five warm passes a run).

| 8 threads (cores 0-7) | `main` | this branch | |
|---|---|---|---|
| membership: reduction | 0.595 s | 0.576 s | |
| membership: openings | 0.624 s | 0.566 s | |
| **membership: prover total** | **1.235 s** | **1.158 s** | **−6.2%** |
| membership: peak memory | 6.01 GiB | 6.01 GiB | |
| leanVM: π1-rec3, proof | 0.863 s | 0.861 s | |
| leanVM: π1-rec3's openings | 0.184 s | 0.184 s | |
| leanVM: π2, proof | 0.792 s | 0.738 s | |
| leanVM: π2's openings | 0.785 s | 0.727 s | |
| **leanVM: total a proof** | **2.629 s** | **2.511 s** | **−4.5%** |
| leanVM: peak RSS | 15.05 GB | 15.59 GB | |

64 threads (reference: `LEANVM_NUM_THREADS=64 taskset -c 0-63`, three and two rounds, medians): membership 0.426 →
0.400 s (−6%; reduction 0.206 → 0.200, openings 0.205 → 0.186), peak 6.24 GiB both; leanVM 0.859 → 0.813 s (−5%;
π1-rec3 0.300 → 0.296, its openings 0.064 both, π2 0.246 → 0.234, its openings 0.244 → 0.220), peak 15.9 → 16.5 GB.

The same digest and fingerprints at 1, 3, 8 and 64 threads (membership at 1 and 3 threads: 8.01 and 2.84 s; leanVM,
one pass: 18.0 and 6.3 s).

The peak RSS of the pipeline grows by 0.5 GB: change 5 holds `Q`'s 1.5 GB level-1 codeword while change 3 drops 1 GB of
`Q`'s kept codeword.

## Where the time was (8 threads, `main`)

`perf` over the warm passes. Membership (one cold proof): Keccak-f (`hash_many_from_state`, the Merkle leaves and
nodes) 28%, the WHIR encodes' radix-8 layers (`run_layers`) 20% and their sweeps 7%, the kernel clearing fresh pages
(`kernel_init_pages`) 6%, the quotient's block-wise pass 5%, `memmove` 4.5%, the quotient crate's transforms 6%.
leanVM: Keccak-f 22%, `run_layers` 15%, π2's numerators on the extension coset 8%, Flock's zerocheck 9%, the quotient
crate's transforms 9%, `memmove` 3.5%. All eight cores are busy throughout (samples in 50 ms buckets: 395-400 of 400
but at a phase's start): the time is work, not waiting.

Two kernels near their bounds dominate:

- **Keccak-f\[1600\], eight states a ZMM** (`primitives::hash`, AVX-512): 100 cycles a permutation on one core
  (42-45 M/s). A round is 95 vector ALU operations (35 `vpternlogq`, 29 `vprolq`, 31 `vpxorq`); measured on this core
  `vpternlogq`/`vpxorq` issue at 3.7 a cycle, `vprolq` at 2, so 26 cycles a round is the bound, against 33 measured.
  The rest is the round's barrier (θ needs every column of the last χ) and spills (25 lanes, 5 parities, 5 θ effects
  in 32 registers). Tried in a scratch microbenchmark of the eight-way permutation: the rounds unrolled by two or all
  24 (98 against 100 cycles: noise), the parities recomputed rather than accumulated (98), two groups interleaved with
  the compiler's spills (144), and two or four groups with their states in L1, rounds interleaved (118, 114). None is
  worth a change.
- **The additive NTT's butterfly** (`pcs` and `quotient`): `vpclmulqdq` issues once every two cycles on Zen 5 at any
  width (four products a ZMM), so a vector of eight butterflies costs at least 4 cycles. The radix-8 sweep takes 4.8
  in L1 and 5.3-7 from L2.

## What changed

1. **The membership proof's two claims on `T` opened together** (`protocol::open`, `opening::open_batch`). `main`
   opened the copy and sum claims on the quotient table one at a time; `pcs_claim::open_words_batch` (π2's, for `Q`)
   gives the same two proofs with one pass of their lane rounds over `T` (1.3 GB) rather than two.
2. **A batch's level-0 rows encoded once** (`pcs::whir`: `after_lane_rounds` split into `level_1` and
   `after_level_1`, `l0_images`). Without a kept codeword each opening encoded its queried level-0 rows again
   (`T`: a 48 ms sweep over the table each). A batch now commits every opening's level 1 and draws its queries, then
   encodes all their rows in one sweep. Each transcript is the one it has alone. With 1 and 2: membership openings
   0.62 → 0.57 s.
3. **Zero lanes left out of kept codewords** (`pcs::whir::commit_skipping`, `L0Rows::Compact`,
   `AdditiveNttF64::encode_two_sweep_blocks_into`; `pcs_claim::commit_words`). π2's `Q` has four empty slots, 16 of
   its 64 lanes, between the others; only commitments without their codeword skipped them. Now a kept codeword is the
   other lanes' alone (3 rather than 4 GiB for `Q`), their rows spread back with zeros where they are hashed and where
   an opening reads them. π2's proof −30 ms, peak −1 GB.
4. **Zero lanes left out of the lane rounds** (`lane_inner_products`, `collapse_lanes`, the out-of-domain answer's
   `dense_lane_inner_products_skipping`): the flagged lanes' products are zero; their words are not read.
5. **A lone opening keeps its level-1 codeword up to 2 GiB** (`LEAN_LIGERO_BYTES_ALONE`; a batch sharing its level-0
   encode keeps 1 GiB, as before, since its openings' level-1 commitments are all held at once). `Q`'s level-1
   codewords are 1.5 GB: kept, their queried rows are read rather than encoded again (9.5 ms an opening), and the
   commit skips the lean path's batches. π2's openings −48 ms, peak +1.6 GB (net of 3: +0.5 GB over `main`).
6. **The quotient crate's transforms** (`quotient::ntt`, shared by both lines: the membership prover's, π1's and
   π2's): (a) a row's own three layers (between the eight words of a row) eight rows at a time, transposed
   (`own_transposed`): each layer's products are whole vector products, the twiddles a vector of the eight rows'
   (`B` linear), stepped from group to group (`group_steps`) rather than computed; before, two rows shared a product
   (`paired`) with shuffles and per-row twiddles; (b) the row layers two at a time (`quads`, `layer_steps`,
   `tile_layers`, in `leaves`, `wide`, `leaf`, `upper`, `upper_from_many`): one load and one store a row for two
   layers. One column, one thread, `2^20` words: forward 7.66 → 6.34 cycles a vector of butterflies, inverse 10.3 →
   5.9. Membership reduction −17 ms.

New tests: `pcs::whir::tests::batched_openings_share_their_rows_and_skip_zero_lanes` (the batch, shared rows, flagged
lanes and compact codeword against each opening alone from the whole codeword), `pcs_claim::tests::
zero_lanes_left_out_change_no_proof` (`Q`'s slot pattern: root, answer, every proof alone and batched, kept or
encoded again), `quotient::ntt::tests::miri_fused_layers_are_the_domains`, `pcs::whir::tests::miri_batched_openings`;
Miri (`cargo +nightly miri test --target x86_64-unknown-linux-gnu -p pcs --lib miri_`, and `-p quotient --lib
miri_`) runs these and `pcs`'s earlier `miri_` tests clean, on the portable lanes (the AVX-512 paths, the transposition
among them, are not Miri's). On x86 the earlier ones stopped at `primitives::stream`'s non-temporal stores (inline
assembly, which Miri does not run): under Miri those copies are now ordinary ones.

## Tried and rejected

Measured on the bench (medians of 2-3 interleaved runs) unless said otherwise.

- **Keccak-f's round schedule** (above): unrolled, parities recomputed, two or four groups interleaved, states in L1.
  No gain, or a loss.
- **The pcs NTT's deepest layers block by block in L1** (`run_layers` on 32 KiB sub-blocks after the upper layers,
  in the two-sweep tiles and the deep pass): one column, one core: 1 MiB tiles of 8 lanes 8.5 → 7.4 cycles a vector of
  butterflies, but 512 KiB of 64 lanes 5.3 → 5.7, the rest unchanged. Dropped.
- **The two-sweep tile** (`TWO_SWEEP_TILE_WORDS` 2^16 rather than 2^17): openings −10 ms, the reduction's `T` +11 ms
  (one more first-sweep layer); leanVM +30 ms. `2^18`: worse on both. **The first sweep's group** (`2 L2_WORDS` → `L2`
  or `4 L2`) and its gathered rows (`WIDE_GATHER_WORDS` 32, 128): no change.
- **The quotient crate's wide passes, up to 8, 9 or 12 layers a pass** rather than 6 (fewer passes over memory for
  the largest columns): no change.
- **A whole batch of lean replicas** (`LEAN_BATCH` 16 rather than 4: the level-1 message read once): −8 ms before
  change 2, but with it the two openings' level-1 commitments are held together: peak 6.0 → 7.5 GiB. Not kept.
- **Every level-1 codeword kept below 2 GiB** (change 5 in the batch's shared path too): its two openings would hold
  3 GB of codewords at once; before change 2 it was −23 ms for +0.94 GiB. Kept only for a lone opening.
- **The quotient crate's row layers two rows a step** (`quads` over `C = 2` rows, more independent chains): no change;
  the radix-4 step is not latency-bound.

## What bounds it now

At 8 threads both provers spend about 40% in the two kernels above, Keccak-f near 75% of its instruction bound and
the radix-8 butterflies near 75-80% of `vpclmulqdq`'s, their counts fixed by PCS version 1 (the Merkle leaves and
nodes, the codewords' sizes). The rest, each a few percent: π2's numerators on the extension coset (a quadratic form of
a row's sixteen cells, about 150 products a point, within 3x of `vpclmulqdq`'s bound), Flock's bit rounds (π1-rec3,
220 ms), the commitments' memory sweeps (two CCDs' bandwidth: about 150 GB/s of writes and copies), and the cold
membership proof's first touches of its 6 GiB (`kernel_init_pages`, about 6%). Ideas not tried: the clmul-free half of
a butterfly layer on GFNI (byte-sliced constant products run on the shuffle pipes, beside `vpclmulqdq`: about 1.4x at
best on the butterflies, with transposes and a second code path); the Merkle leaves hashed from compact rows rather
than spread ones (`Q`'s zero slots); interleaving a tile's hashing with the next tile's layers, whose units differ
(`vpclmulqdq` against the vector ALUs), which would need one fused kernel.
