<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# The recursion's gas: what was tried (branch `perf/leanvm-gas`)

Benchmark 2 of the EIP draft: π2's contract verifying π1-rec3 of 128 leanXMSS signatures, as an EIP-8141 frame
transaction under EIP-7976's floor. The floor binds by far (standard 49,678 against floor 70,464 on `main`), so the gas
is `64 · calldata bytes`, plus the frame of PCS claims (`1 + 32` bytes a claim, 64 a byte) and the PCS gas (`5,000 +
1,000` a claim) on both sides: a byte is 64 gas, a claim 3,112. Execution may grow while the standard price stays under
the floor. Measured by `tests/pi2_real.rs` (`real_end_to_end`, `real_gas`) on h3 (AMD EPYC 9355P).

## Results

| | calldata | floor | with the frame and PCS gas | execution (standard) |
|---|---:|---:|---:|---:|
| `main` | 1,101 B (61 zero) | 70,464 | 99,912 | 32,794 (49,678) |
| 1. narrow challenges as 20 bytes | 1,045 B | 66,880 | 96,328 | 32,780 (49,440) |
| 2. no selector | 1,041 B | 66,624 | 96,072 | 32,758 (49,354) |
| 3. `C1`'s claim hashed in π2's circuit | **941 B** (8 zero) | **60,224** | **89,672** | 37,406 (52,366) |
| 3. at 400 signatures | 961 B | 61,504 | 90,952 | 42,308 (57,612) |

**−10,240 gas (−10.2%)** at the reference shape. Calldata now: π1's public input (32 B); the stream (908 B): `C2`'s root
(32), π1's elements (364: `C2`'s out-of-domain answer, the 13 narrow challenges `z_0 … z_12` at 20 bytes, `C2`'s and
`F`'s values), `W`'s and `Q`'s commitments (2 × 56), the 18 values at `t` (432); the frame's index (1). The frame still
declares 8 claims (257 B, 16,448 gas; PCS gas 13,000).

The contract: 17,185 B of code at 128 signatures (13,219 on `main`), 19,425 B at 400, under EIP-170's 24,576; 205
selector pairs (133), 910 `FIELD_MUL`s. The execution grows with the pairs (§3), the standard price stays 7,858 under the
floor (3,892 at 400).

**The prover** (`tests/pipeline.rs` on the 128-signature trace, h3, `main` and this branch interleaved, 4 runs of 5
passes each, medians; the box shared with other jobs, load 20–28): see the table at the end of this file.

## 1. Narrow challenges as 20 bytes (`Read::Narrow`)

π1-rec3's batch challenges are narrow (`c2 < 2^32`, `transcript::NARROW_BITS`): their 24 calldata bytes began with four
zeros (PI2.md §9, lever 1c, "not taken"). The circuit compiler marks the elements that are narrow challenges
(`spec::Circuit::narrow`); π2's stream carries their low 20 bytes (`Channel::next_narrow`, `KeccakWriter::send_narrow`),
the contract reads `CALLDATALOAD >> 96`. The port's value is the same element, so π2's circuit, π1 and its vectors are
unchanged; only π2's reads (hence its digest and IV) and its transcript's bytes change. −56 B (14 × 4).

## 2. No selector (`codegen::Entry::selector`)

π2's contract has one entry, the verifier: its calldata is the public input, the stream and the frame's index, checked
by length and no value. π1's contracts (test-only) keep theirs. −4 B.

## 3. π1's claim on `C1` hashed in π2's circuit (lever 1, in part)

The contract needs π1's three claims only to hash them and find the hashes among the frame's payloads. A claim the
circuit hashes itself leaves calldata: π2's public word is then the claim's Keccak-256, which the contract reads from
the frame (it is the claim's payload) instead of encoding the claim.

- **The circuit** (`circuit::compile`, `HASHED_CLAIMS = [0]`): the claim's encoding (`version ‖ n ‖ root ‖ ood ‖ point ‖
  value`, `82 + 24n` bytes) as message bits, its Keccak-256 (`Sponge::keccak256`), the digest's four big-endian words a
  four-limb port (`spec::Source::ClaimHash`, the statement's fingerprint `(H_0 + Y H_1) + γ (H_2 + Y H_3)`). The root's
  and the out-of-domain answer's bytes are the stream's bits (π1's transcript hashed them; `units::Copies` gives an
  endable copy where the first block ends them at the permutation's input); another element's (the coordinates, the
  value, the plain round's challenge) are free bits (`compile::Given::Bit`, which the witness plan replays from the
  element's computed limbs) packed into limbs checked equal to the element's (an `E` sum, a zero port).
- **The verifier** reads the word as `Read::Frame(0)` (four scalars, not in the stream); the seed is
  `keccak(NAME ‖ IV ‖ public input ‖ frame words)` (`verifier::seed`), so the word is bound before every challenge. The
  contract's seed reads payload 0 with `FRAMEDATALOAD` (`codegen::Entry::frame`; the statement's words `4 ..` are the
  frame word's, `Node::Statement(k ≥ 4)`), and checks the other seven claims at payloads 1 … 7 (`Ending::ClaimsAt`).
- **What leaves calldata**: `C1`'s root (32 B), its out-of-domain answer (24), its value (24) and the batch's last
  challenge (the plain round's, which only `C1`'s 27th coordinate takes: 20). −100 B.
- **Capacity.** The claim is 730 bytes at 27 variables: six permutations, about 0.81M positions with the bits, packings
  and the `C1` port gone. π2 fills 16,482,912 of `2^24` positions at 128 signatures (98.2%, 93.4% on `main`) and
  16,756,288 at 400 (99.9%: 127 rows to spare; 28 variables there). Past that, `compile_keeping` compiles without it
  (`FIT_LOG_N`): the recursion's capacity (π1's `C1` at `2^28` near 470 signatures) is kept, the 100 bytes are not.
  The fallback is not exercised by a vector (none past 400 signatures).
- **Soundness.** π2's rounds are unchanged: `N`, the lists, and three four-limb ports (the statement, `C2`'s root, the
  claim hash; `C1`'s root port is gone): `params/leanvm_rec_params.py` gives π2 128.93 bits as `Q/ε` at `Q = 2^64` (its
  weakest round `t`, 141.33 after the lists) and the recursion 127.86 (127.70 with the Lean's π1-rec3 bound), as on
  `main`. The claim is bound to its payload by Keccak-256's collision resistance, as the frame binds every declared
  claim (the EIP's own assumption); the hash is computed in π2's circuit at Keccak-f[1600], the model gap π1's
  Fiat–Shamir in π2's circuit already has (AGENTS.md, "Remaining").
- **The cost**: 72 more selector pairs (the regions padded to fewer blocks have less room: 205 against 133), hence
  +4,612 execution and the prover's `P_v`/`T` work on the extension coset (the A/B below).

## Not taken

- **All three of π1's claims hashed in the circuit** (the whole of lever 1, −464 B): 6 + 6 + 5 permutations (`n = 27, 26,
  23`), about 2.3M positions, against 1.11M free at 128 signatures (0.84M at 400) on `main`. `C1`'s alone fits; with
  `C2`'s (−100 B more) `N = 2^25`, whose quotient table (sixteen slots of `N`) is `2^29` words, past WHIR's certified
  `2^28`: `Q` split in two commitments (+56 B and two more claims on `Q`, about +9.8K gas) and π2's prover and openings
  about twice (≈ +1 s on the M4 Max). Rejected for the prover's time.
- **D32v at `2^23`** (rows of 32, 51,200 positions a Keccak-f; `params/leanvm_rec_params.py`: 6.42M positions): room for
  the three claims' hashes, but 34 values at `t` (+384 B): about 961 B of calldata, no better than step 3, and its
  verifier's execution (about 52K when measured, SPEC-REC §2.6) puts the standard price over the floor. Its code is no
  longer in the repository.
- **Fewer claims on `Q`** (a claim is 3,112 gas). The sum's claim (`Σ_V h = 0`, `h`'s top novel coefficient at `1^m`)
  is a point of the stack whose position coordinates differ from the identity's; a product-weight point cannot carry
  both. The pushes' claim needs `ρ` drawn after `s`: with one claim at the identity's fixed ratio `ρ' = c_q/Y` the
  prover solves for `s`. π2v1 (no `P`, two claims on `Q`: −24 B and a claim, about −4.6K) needs the `5N` identity (a `4N`
  coset, about +25% on π2's proof), and its fifteen slots (`h`'s three limbs, `q`'s four chunks of three) do not split
  into the stack's product weights (`h`'s limbs would take the digit coordinates `q`'s chunks need).
- **Narrower challenges** (19 bytes, 152 bits): π1's paired batch keeps 132.25 bits after `C1`'s and `C2`'s lists at 160
  bits; at 152 it would fall under 128 (and π1's proof and vectors would change).
- **The frame's index byte** (−64 gas): a fixed index for the frame of PCS claims constrains the transaction's frames;
  `evm_link`'s convention (the index the calldata's last byte) is shared with the membership contract.
- **Values the verifier derives.** π1's three values are tied by its batch's final check, but its final claim is π1's
  internal value, which the contract does not have. The 18 values at `t` are the prover's messages (D8v's 8 values:
  capacity, PI2.md §9).

## What the Lean would need (not updated on this branch)

- `formal/RecStatement`: π2's statement data (`Data.lean`, `tests/lean_statement_keccak.rs`, ignored test now stale):
  the reads (`Read.narrow`, 20 bytes; `Read.frame p`, four scalars from the frame), the `ClaimHash` port and its terms,
  π1's calls (the encoded two), the digest and setup root; the verifier's seed over the frame words and its reads.
- `formal/RecCircuit` (`rec-circuit-keccak`, the identical circuit): the hashed claim's section (message bits, the copy
  units, the free bits of an element and their packing and zero check, the digest's port), the narrow elements, the
  fallback rule; `DigestChecked`, `SetupRootChecked`, `IvChecked` re-evaluated.
- `formal/RecCompose`: the contract model (no selector, narrow reads, payload 0 read into the seed and the statement
  words `4 ..`, the claims at payloads `1 … 7`); `pi1rec3K_end` extended to "a satisfied π2 circuit carries the
  Keccak-256 of the graph's first claim"; `recKnowledgeSoundness_reduction_real`'s extractor then names π1's claim on
  `C1` by its hash, with a Keccak-256 collision term (or the frame's binding as an assumption, as for every declared
  claim). The bounds' arithmetic (`pi2Bound`) is unchanged.
- `tests/lean_pi2_prover.rs`'s vectors (π2's Lean prover) carry the new reads and values (`N`, `F`, `W`).

## The prover, A/B on h3

`tests/pipeline.rs` (`LEANVM_TRACE` the 128-signature trace, `PIPELINE_REPEAT=5`), `main` (`/root/pcs-perf/base`) and
this branch interleaved, four runs each under the bench lock, 2026-11-11; each run's median of 5 passes:

| | `main` (runs 1–4) | this branch (runs 1–4) | median of the runs |
|---|---|---|---:|
| π1-rec3, proof and openings | 0.385 0.387 0.389 0.390 | 0.390 0.401 0.390 0.422 | 0.388 → 0.396 (unchanged code: noise) |
| π2, proof | 0.256 0.262 0.255 0.261 | 0.276 0.279 0.272 0.289 | **0.259 → 0.278 (+19 ms, +7%)** |
| π2, openings | 0.272 0.271 0.273 0.272 | 0.273 0.279 0.273 0.291 | 0.272 → 0.276 |
| total | 0.917 0.921 0.922 0.919 | 0.941 0.959 0.949 1.002 | **0.920 → 0.954 (+3.7%)** |

π2's proof grows with the selector pairs (205 against 133: every pair's indicator and formula on the extension coset);
its openings and π1's work are unchanged. Scaled to the M4 Max's 3.7 s a proof (π2's proof 0.95 s there), about +0.07 s.
The witness plan's replay (the claim's six permutations and bits) stays under 0.01 s.
