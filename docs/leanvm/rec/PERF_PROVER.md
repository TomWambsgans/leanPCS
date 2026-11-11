<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# The recursion prover's time: what was tried

The EIP draft's second benchmark: from leanVM's trace of 128 leanXMSS signatures to π1-rec3's proof and three openings,
π2's proof and its five openings (`crates/leanvm/rec/tests/pipeline.rs`). Every change below is a pure prover change:
the proofs are byte for byte main's (π1's stream is the committed vector `keccak128_rec3.txt`; the pipeline prints the
Keccak-256 of π1's stream and openings and of π2's stream and openings, which are main's), so the calldata (1,101 B),
the eight claims and the gas (99,912 with the frame) are unchanged, and the verifiers are untouched.

## Numbers

AMD EPYC 9355P (h3, Zen 5, 32 cores, 64 threads), `RUSTFLAGS="-C target-cpu=x86-64-v4 -C
target-feature=+gfni,+vpclmulqdq,+vaes,+pclmulqdq,+avx512vbmi,+aes,+bmi2"`, `PIPELINE_REPEAT=5`, medians; main and the
branch run alternately (π2's proof after π1's openings, as main), each run once the machine is
quiet. 16 threads: `LEANVM_NUM_THREADS=16 taskset -c 0-15` (16 physical cores). h3 is shared with other agents' builds:
a run that one of them perturbed (a pass 10% or more above its round's others) is left out.

| | main | this branch | |
|---|---|---|---|
| h3, 64 threads: π1-rec3, proof and openings | 0.38 s | 0.31 + 0.07 s | |
| π2: proof | 0.255 s | 0.227 s | |
| π2: openings | 0.273 s | 0.243 s | |
| **total** | **0.91 s** | **0.847 s** | −7% |
| h3, 16 threads: π1-rec3 | 0.61 s | 0.48 + 0.10 s | |
| π2: proof | 0.46 s | 0.39 s | |
| π2: openings | 0.48 s | 0.43 s | |
| **total** | **1.55 s** | **1.40 s** | −10% |
| M4 Max (one run, `PIPELINE_REPEAT=5`, power mode not checked; the same fingerprints): π1-rec3 | 1.41 s | 1.06 + 0.27 s | |
| π2: proof | 0.95 s | 0.85 s | |
| π2: openings | 1.25 s | 1.12 s | |
| **total** | **3.7 s** (bench.sh) | **3.29 s** | −11% |
| peak RSS (h3, 64 threads; Mac) | 15.9 GB; 14.3 GB | 16.2 GB; 14.7 GB | `Q`'s batch holds three folded witnesses and weights |

## What worked

1. **The out-of-domain answer from the lanes' products.** A commitment's answer `f(z)` was `Σ_l eq(z_high, l) ·
   inner_product_base_ext(lane_l, eq(z_low, ·))`: one reduced `E × K` product a word, 64 dispatches (one a lane), over
   the whole stack (`Q`: `2^28` words, about 30 ms at 64 threads). It is now one pass with `dot_base` (eight words, six
   carry-less products, unreduced) over every lane at once (`pcs::whir::dense_lane_inner_products`), 5 ms. Every
   commitment gains (π1's `C1`, `C2`, `F`; π2's `W`, `Q`).
2. **The answer's lane products are kept for the openings.** Every opening's weight is `eq(z, ·) + λ eq(point, ·)`, and
   its first lane round needs `Σ_x lane_l[x] eq(z_low, x)` for each lane: exactly what the commitment computed. The
   commitment keeps them (`pcs_claim::Commitment::ood_lanes`, 64 elements) and the lane rounds take them as known
   (`recursive_prover_with_lane_tensors_known`): the opening's first pass reads one weight rather than two.
3. **Q's three openings batched** (`pcs_claim::open_words_batch`, `pcs::whir::recursive_prover_with_lane_tensors_batch`).
   The three claims on `Q` are three openings with three transcripts, but the lane rounds of all three read the same
   `2^28` words twice each (the inner products, then the collapse at the six lane challenges). They now run together:
   the three claims' inner products in one pass, then each transcript's six lane rounds (small), then the three
   collapses in one pass (a stage of 128 words of the 64 lanes, in L2, folded at each opening's coefficients in turn),
   then each opening goes on alone from its level-1 commitment (`after_lane_rounds`). Six passes over 2 GB become two
   (48 ms of lane rounds become 24 ms at 64 threads).
4. **`eq` low weights never written out** (`pcs::whir::Low::Eq`). A claim's low weight `eq(point_low, ·)` was a table of a
   lane's length (`2^22` elements of `E`, 100 MB for `Q`), built for every opening and read by both passes, its chunk
   packed again for `dot_base` in every task. It is now the product of two tables of `2^11` (`eq(p_lo, x mod 2^11) ·
   eq(p_hi, x >> 11)`, exact): a chunk's sums are taken against the small table, packed once, then multiplied by one
   factor. A point with boolean coordinates (sparse) is summed at its entries, as before.

## What did not

- **π1's openings concurrent with π2's proof** (`PIPELINE_OVERLAP=1`: π2 on its own thread from π1's stream, while π1's
  openings run): no gain (0.845 s against 0.848 s at 64 threads). The pool runs one dispatch at a time and the machine
  is saturated: sampled, 55 to 64 of the 64 threads are busy through the whole proof; π1's openings stretch to 0.3 s and
  π2's proof by as much. Peak memory grows by 0.4 GB. The pipeline keeps the structure (π2 on its own thread, its
  witness replayed while π1's openings run, as main) with the overlap off by default.
- **Reusing `Q`'s 4 GB codeword buffer between proofs**: the page faults of its first touch are 0.2% of a warm proof's
  samples (jemalloc keeps the extents): not worth an API.
- **The Keccak-256 Merkle hashing** is 20% of the samples at 64 threads, 24% at 16 (about 175 M permutations a proof:
  `Q`'s commitment 42 M, the level-1 commitments of `Q`'s three openings 50 M, …), all fixed by PCS version 1. The
  AVX-512 eight-way permutation runs at 107 cycles a permutation on one core (`primitives`' `hash_throughput`:
  42 M/s), near the 8-way ternary-logic bound; nothing to take there.
- **Skipping `Q`'s four zero slots** (16 of its 64 lanes) in the lane passes: about 1% at 64 threads (the passes are
  now 30 ms in all), less once the check that the lanes are zero is paid; the encode cannot skip them (each is half a
  vector of a 64-word row, and the leaf hashes them). Not done.
- **Caching π1's setup commitment `F`** (re-committed every proof, `2^23`): about 4 ms at 64 threads, an API change of
  π1's prover. Not done.

## Where the time is (64 threads, a warm pass)

From `perf` (1999 Hz) over the last pass: Keccak-256 (`hash_many_from_state`) 20%, the WHIR encodes' additive NTT
(`run_layers`, `two_sweep_gathered`, `fill_tile`) 18%, `quotient`'s transforms (`wide`, `leaves`) 11%, π2's numerators
on the extension coset 5%, Flock's zerocheck 7%, the lane passes 5%, `memmove` 4%. Per phase (the branch, medians):
π1-rec3 to its stream 0.30 s (Flock 88 ms, the commitments 50 ms, the quotients 62 ms, the batching sumcheck 38 ms),
its three openings 0.07 s, π2's proof 0.23 s (`Q`'s commitment 95 ms, its quotient 88 ms), π2's openings 0.24 s (`Q`'s
three 0.22 s: per opening the level-1 commitment 30 ms, level 2 12 ms).

`PIPELINE_TRACING=1` prints the last pass's trace tree (the WHIR spans, π1, π2's proof and openings).
