# The membership prover's speed (branch `perf/membership-prover`)

> Merged into `main` on 2026-11-11. Below, `main` means `main` before the merge (commit `f96a7938`), and "this
> branch" the branch this note describes; the figures are those measured on it.

Pure prover changes: every proof is the same, byte for byte (the bench's proof digest `95df593d…` and the toy
circuit's pin `proofs_are_pinned` are unchanged; leanVM's π2 openings, which share `pcs` and `pcs_claim`, keep their
digest `52ccb57a…`). The protocol, the PCS claims (version 1), WHIR's parameters, the calldata (461 B), the claims
(6) and the gas (18,899 execution, 52,856 transaction) are unchanged.

## Numbers

`cargo bench -p quotient --bench membership`, median of five (h3) or of two (the Mac) passes, main `f96a7938`
against this branch:

| | main: reduction / openings / total | branch | peak memory |
|---|---|---|---|
| h3 (AMD EPYC 9355P), 64 threads | 0.648 / 0.260 / 0.91 s | 0.289 / 0.237 / **0.53 s** (−42%) | 8.71 → 6.83 GiB |
| h3, 16 threads (`LEANVM_NUM_THREADS=16`) | 0.903 / 0.434 / 1.34 s | 0.437 / 0.373 / **0.81 s** (−39%) | 8.61 → 6.62 GiB |
| M4 Max, 16 cores (load about 1.6) | 1.65 / 1.08 / 2.74 s | 1.22 / 0.95 / **2.19 s** (−20%) | 8.64 → 6.67 GiB |

The Mac gains less: its transforms and its Keccak-f (NEON) are compute bound where h3's are partly bound by memory
and its page faults, which most of the changes below remove.

## What changed

In the order they were made. Times are h3's spans (`BENCH_TRACING=1`), 64 / 16 threads.

1. **The out-of-domain answers in one pass** (`pcs_claim::evaluate_lanes`): it took one inner product a lane against
   a written-out `eq` table of the lane's `2^(n-6)` points (`Q`: 64 × (32 MiB of words + 96 MiB of table)); now rows
   of `2^10` words against weights in L1, accumulated unreduced (`dot_base`), times the row's weight: one read of the
   words. It was 9% of the prover's samples.
2. **Tables committed up to their last nonzero lane** (`opening::commit`, on `pcs_claim::commit`, whose
   commitment and openings of the leading lanes are those of the whole stack): `W` 33 lanes of 64, `H` 41, `Q` 45,
   `G` 57 (the gate's quotient's degree), so neither encoded nor zeroed nor read past them.
3. **No copy on one thread**: the cells, the witness's and the sum's coefficients went into `W`, `H`, `G` and every
   transform's quarter by `copy_from_slice` and `vec![0; …]` on the calling thread (the "tables" span alone 94 ms,
   "sum values" 125 ms at 64 threads). Now: the quarters' transforms read their source as their first pass writes
   them (`values_upper(Some(src))`, the masks' and the blinding's words added to the source and taken off again);
   `H`'s limbs are computed in `H`'s table; the gate's quotient is its own buffer, whose first half is `G`; the
   witness's values are made from `W`'s coefficients before `W` is committed, in `W`'s allocation.
4. **Memory mapped by the workers** (`pcs_claim::mapped_words`): a fresh buffer's first writes were the transforms'
   strided ones, every thread faulting the same huge pages at once; now each worker touches its own run of pages
   first. The commitments' encoding buffers are mapped the same way, and the commitments run largest first, so that
   each freed buffer serves the next. Together with (3), 0.65 → 0.31 s of reduction at 64 threads, 8.7 → 6.7 GiB.
5. **The index keeps its codeword** (`Index::commit`; `opening::open` with `Codeword::Keep`): the wiring's opening, which every
   proof makes, no longer encodes its queried rows again (3.4 / 4.6 ms; 256 MiB held with the index).
6. **The cells' digest by the batched Keccak-256** (`cells_digest`, `hash_many` sixteen runs a task): 8.5 / 14 →
   1.2 / 2 ms. The same digest, so the same randomness.
7. **All-zero lanes skipped** (`pcs::whir::commit_tree_skipping_in`, `encoded_rows_skipping`
   (then `recursive_prover_with_lane_tensors_skipping`, since folded into the batched openings), over the two-sweep encode of a message given block by block,
   `encode_two_sweep_blocks_with`): `pcs_claim` flags a commitment's all-zero lanes (a scan that reads them and little
   else) and encodes the others alone, the zero lanes' words of each row zero when it is hashed; an opening encodes
   its queried rows again the same way. `H` has 14 zero lanes of 41 (limb blinding past `H_BLIND`), `Q` 6 of 45. The
   test `skipped_zero_lanes_encode_the_codeword` pins the trees and rows to the whole encode's. 16 threads: −30 ms
   reduction, −10 ms openings.
8. **The public weight's tensor factored** (`quotient_block`): each block of `2^11` cells made its `2^11` weights
   by two scalar `E` products a cell; now the eight weights of its three lowest coordinates (one `Ex8`) times one of
   256 for the others, a vector product a row of eight cells: quotient values 65 / 120 → 48 / 88 ms.
9. **The four quarters' first upper pass reads its source once** (`ntt::values_upper_many`): −5 / −2 ms.

## Tried and rejected

- **Keeping `H`'s codeword for its two openings** (no re-encode of its queried rows, 2 × 7 / 13 ms): 1.3 GiB held
  through the openings, whose own buffers then map fresh memory; the openings got slower at 64 threads (+18 ms) and
  faster at 16 (−10 ms), peak +1.35 GiB. Rejected.
- **Keeping every table's codeword** (no re-encode at all), with the codeword mapped by the workers: 16 threads −19
  ms, 64 threads +20 ms, peak 6.7 → 11.8 GiB. Rejected.
- **The six openings concurrently**, two to six OS threads sharing the pool (dispatches serialized, the sequential
  parts overlapping): 2 streams 0.23 → 0.28 s at 64 threads, 0.38 → 0.40 s at 16, peak +1.5 to 2.7 GiB (the
  concurrent openings' buffers map fresh memory). Rejected; independent thread pools were not tried.
- **Shrinking the commitments' encoding buffer to the encoded lanes** (with (7)): the openings then mapped fresh
  memory (peak 6.7 → 7.8 GiB, openings +40 ms at 64 threads). The buffer stays the size of the table.

## What bounds it now

At 16 threads on h3, about a quarter of the prover is Keccak-f (the Merkle leaves and nodes of the five
commitments and of the openings' deeper levels: about 40 M permutations a second a core with AVX-512, no gain from
SMT), a fifth the commitments' and openings' NTTs, an eighth the quotients' leaf transforms and arithmetic, and the
rest memory passes (the upper transform passes, the openings' first sumcheck rounds over the tables, the
out-of-domain answers and the replay's evaluations) and page faults (the `Q` commitment's encoding buffer, 1.4 GiB,
is mapped fresh). Possible further steps, each a few percent: the near-zero lanes (`H`'s three blinding lanes, `W`'s
mask lane: eight or sixteen nonzero words of `2^21`) by a pruned transform; the openings' lane rounds and the
out-of-domain answers skipping the zero lanes; the `Q` commitment's buffer taken from memory the reduction frees.
