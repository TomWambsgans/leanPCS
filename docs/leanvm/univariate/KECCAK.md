<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# The Keccak VM: leanVM with Keccak-f in the VM, verified on the EVM

This document is the VM π1 proves and what it measures: the statement, the workloads, the capacity, the gas, the
recursion and the prover. The protocol is `SPEC.md`, Flock's part `SPEC-FLOCK.md`, the prover's mechanics `PROVER.md`.

**Status (2026-11-08): proven end to end on real executions.** The verifier (`verifier::reduce` with `KECCAK_MAIN` or
`KECCAK_REC3`) is recorded, compiled to EVM code, run on revm, and checked word for word against the Rust verifier.
The prover (`src/prover/`) proves real leanVM `9d50c92a3` executions (`cargo leanvm aggregate --xmss N`, N = 32, 128,
400):
- the Rust verifier accepts, the three WHIR openings verify, and the straight and deployable contracts accept the real
  calldata, with `PCS_OPEN` attesting exactly the claims the openings prove; mutated proofs are rejected;
- π2 (`crates/leanvm/rec`) proves the real 128- and 400-signature π1-rec3 proofs, and the recursion's contract accepts
  them.

**The reference workload is 128 signatures** (`leanvm_statement::shapes::reference()`, `leanvm_rec::REFERENCE`): the
committed vector `tests/vectors/keccak128_rec3.txt`, the contract's reference setup root, the recursion's reference.
The gas is a function of the shape, not of the proof: the real proofs run at the gas measured from the shapes.

## The statement

- **The VM** is leanVM's Keccak branch, as it stood before its switch to a GKR (commit `9d50c92a3`, "flock: fix what
  the three-step block left stale"). It is leanVM `42422001` with its BLAKE2S table replaced by a `SHA3` table:
  - one row is one Keccak-f step over a thirteen-cell sponge state;
  - the four `m` cells are addressed independently, then come the `tail` run of four cells and the `cap` run of five;
  - thirteen cells are read and thirteen written, each holding two lanes and a zero top (`memory_128`), except the
    lone lane-16 cell (`memory_k`);
  - the bytecode operands are the seven bases;
  - there are 86 columns: 9 operands, 25 + 25 lanes, and 27 counts.

  `leanvm_statement::layout::tables` states the table and its 28 flush pairs; the other five tables are leanVM
  42422001's. In Lean the statement is `formal/KeccakVm`'s `KvHolds`.
- **The hash argument is not leanVM's.** leanVM `9d50c92a3`'s Flock block packs three permutations into `2^17` slots
  and commits only the χ products. Its matrices are dense in the θ cascade, so its lincheck terminal is a walk of the
  whole circuit (leanVM's `bilinear_walk`), which `docs/leanvm/flock/KECCAK.md` §4.2 estimates at about 1.3M additions
  a permutation: unaffordable in a contract.
  - This verifier uses instead the Keccak-f block of `lv42_flock::keccak` (`docs/leanvm/flock/KECCAK.md`, M1): one
    permutation per `2^17` slots, with every round's state materialised.
  - Its terminal is the structured one (`keccak_flock::structured_terminal`, `docs/leanvm/flock/KECCAK.md`, M3),
    3,019 `E` operations at a skip of 3.
  - The block's matrices are never committed, so there are no claims on them: 3 claims in 3 calls (`C1`, `C2`, `F`).
- **The link.** The 50 lane columns are committed in `C1` as the univariate copies, which the bus reads. `Q_W` binds
  each one to `q_flock`'s word at its row's block: input lane `l` at the block's input port word, output lane `l` at
  its output port word (`layout::keccak_slot`). Each block is `2^11` words, so a `QflockSlot` term has 11 slot bits
  (`verifier::weight_at`).
- **leanVM's opcode exactly.** leanVM's step is `Keccak-f(in ⊕ END_BIT·e₁₆)` (`END_BIT = 0x80 << 56`, SHA3's last
  padding bit). The block proves `Keccak-f` of its input port, so the port of input lane 16 holds `in₁₆ ⊕ END_BIT`, and
  `Q_W`'s copy identity for `in_16` is `copy − port = END_BIT` (`layout::keccak_slot_offset`): one constant.

## Workloads

The workloads are runs of leanVM `9d50c92a3` on a Mac: `cargo leanvm aggregate --xmss N --log-inv-rate 1`, giving
each table's executed rows (`leanvm_statement::shapes::WORKLOADS`). The memory is the cells used, and the bytecode is
`2^17.54` instructions, padded to `2^18`.

| signatures | XOR | MUL | SET | DEREF | JUMP | SHA3 (Keccak-f) | memory | heights |
|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 32 | 6,956 | 9,877 | 6,578 | 9,652 | 3,995 | 4,440 | 2^17.5 | 13 14 13 14 12 13 |
| **128** | 24,260 | 36,229 | 24,626 | 35,812 | 15,509 | 17,712 | 2^19.5 | 15 16 15 16 14 15 |
| 400 | 73,288 | 110,893 | 75,762 | 109,932 | 48,157 | 55,316 | 2^21.1 | 17 17 17 17 16 16 |
| 1,000 | 181,438 | 275,593 | 188,562 | 273,432 | 120,085 | 138,266 | 2^22.4 | |

A signature takes about 138 Keccak-f: 128 bytes are absorbed per permutation.

**Capacity.** `q_flock` is `2^11` words per permutation, so `C1` reaches WHIR's `2^28` words at `2^16` permutations,
about 470 signatures. At 400 signatures `C1` is `2^28` words. At 1,000 signatures (138,266 permutations) `q_flock`
alone is `2^29` words: **no proof**. `tests/keccak_vm.rs`, `keccak_stacks_against_whir`, checks this.

## Gas

Measured on revm (`tests/keccak_vm.rs`, `keccak_gas_report`), `KECCAK_MAIN`, point claims. Transaction gas excludes the
21,000 base and uses EIP-7623. `c` is the price of a `PCS_OPEN` claim.

| signatures | largest stack | calldata | execution | `FIELD_MUL` | claims / calls | tx, `c` = 0 | tx, `c` = 5,000 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 32 | 2^25 | 7,828 B | 222,928 | 5,166 | 3 / 3 | 347,840 | 362,840 |
| **128** | 2^27 | 8,020 B | 230,985 | 5,253 | 3 / 3 | **358,957** | **373,957** |
| 400 | 2^28 | 8,116 B | 236,976 | 5,364 | 3 / 3 | 366,484 | 381,484 |
| 1,000 (`C1` over `2^28`: infeasible) | 2^30 | 8,308 B | 247,340 | 5,531 | 3 / 3 | 379,908 | 394,908 |

The 400-signature contract, cut into EIP-170 contracts, is 4 contracts with 252,591 of execution and 382,099
transaction gas. The 1,000-signature row is a contract no WHIR opening could serve.

**Where it goes.** At 128 signatures the calldata is the selector and public input (36 B), the row counts (24 B), the
two roots (64 B), Flock's 154 scalars (3,696 B), the 118 values at `t` (2,832 B) and the batching sumcheck's 27 rounds
and 3 values (1,368 B). Only Flock's rounds and the batch grow with the shape, with the logarithms of the sizes. The
contract is execution-bound. Its largest parts are the ring switch's weight at the batch's point (`SPEC.md` §13, "The
floor") and Flock's structured terminal (about 42K at 400 signatures); `keccak_gas_report` prints the phases at 128
and 400 signatures.

### Under the recursion (`crates/leanvm/rec`)

π1 is recorded with π1-rec3's Fiat–Shamir shape (`KECCAK_REC3`), compiled into π2's D16v circuit, and π2's contract
is measured (`crates/leanvm/rec/tests/keccak_vm_rec.rs`). The contract's gas depends on the circuit alone.

| π1-rec3 | Keccak-f | Keccak-256 calls, stream | `E` products / linear | π2 positions used of 2^24 | π2 blocks / selector pairs | contract code | execution |
|---|---:|---|---:|---:|---:|---:|---:|
| **128 signatures** | 116 | 70, 9,232 B | 8,476 / 6,633 | 15,668,416 (93.4%) | 21 / 133 | 13,491 B | 28,325 |
| 400 signatures | 118 | 71, 9,424 B | 8,673 / 6,885 | 15,940,800 (95.0%) | 22 / 144 | | 29,105 |

**On the real proofs** (`crates/leanvm/rec/tests/pi2_real.rs`, `real_end_to_end`, Mac). The recursion's contract
accepts with `PCS_OPEN` attesting its 7 claims in 6 calls, and 18 flipped calldata bytes are rejected.

| | 128 signatures | 400 signatures |
|---|---:|---:|
| calldata | 980 B (58 zero) | 980 B (56 zero) |
| execution | 28,325 | 29,105 |
| transaction, EIP-7623, `c` = 0, without the base | **43,309** | 44,113 |
| transaction, EIP-7976 | 62,720 | |
| π2: witness compile, adapt and check | 3.8 s | 2.9 s |
| π2: prove / open | 4.4 s / 1.7 s | 3.0 s / 0.9 s |
| peak RSS | 9.79 GB | 9.8 GB |

At 128 signatures the setup commitment takes 1.5 s, once per circuit; the runs were on the Mac of "Measured" below,
under the same load, 3 runs. Since then (2026-11-08, same Mac, load 2–7) the recursion end to end from the trace
(`crates/leanvm/rec/tests/pipeline.rs`, median of 3 warm passes) takes **4.1 s a proof**: π1-rec3's proof and openings
with π2's witness compiled meanwhile 1.87 s (the compile 0.49 s, overlapped with π1's openings), π2's proof 1.58 s,
its openings 0.70 s; what depends on the circuit only (π1's setup roots, π2's circuit, spec, setup commitment, IV)
0.9 s once; peak RSS 12.5 GB. On x86 (h2, Intel Core Ultra 7 265, AVX2 without AVX-512, load 11–17) it takes 7.5–8.9 s
(π2's witness: compile, adapt and check 3.3 s → 1.3 s, of which the compile a proof needs 0.8 s); on h1 (Zen 4, AVX-512, load 13–15 from other jobs)
11.5–12.1 s. At 400 signatures the sample stream gave 44,737 transaction gas; the real proof's
calldata has more zero bytes.

π2 holds π1 in `2^24` positions: the structured terminal is 3K operations, so the arithmetic regions nearly vanish.
The layout's padding (`leanvm_rec::circuit::layout::pad_counts`, and `formal/RecCircuit`'s `padCounts`) looks past
digit counts that save no rows (a carry: the region `keccak16/k1` pads to the same rows at 2 and 3 digits); a
one-digit greedy gave 70 blocks and 429 selector pairs (47,791 of execution) for the 400-signature π1.

## The prover

`PROVER.md` describes it: the trace `src/prover/dump_keccak/` makes leanVM `9d50c92a3` write (its run without the fill
blocks), the placement, the Keccak-f blocks built from the placed `SHA3` rows, the phases, the skip kernels, and how to
run. The traces' sizes:

| signatures | rows (XOR, MUL, SET, DEREF, JUMP, SHA3) | heights | memory | bytecode |
|---:|---|---|---:|---:|
| 32 | 6,956 / 9,877 / 6,578 / 9,652 / 3,995 / 4,440 | 13 14 13 14 12 13 | 2^18 | 2^18 |
| **128** | 24,260 / 36,229 / 24,626 / 35,812 / 15,509 / 17,712 | 15 16 15 16 14 15 | 2^20 | 2^18 |
| 400 | 73,288 / 110,893 / 75,762 / 109,932 / 48,157 / 55,316 | 17 17 17 17 16 16 | 2^22 | 2^18 |

```sh
LEANVM_TRACE=<dir> RUSTFLAGS="-C target-cpu=native" \
  cargo test --release -p leanvm_univariate --test prove_real -- --ignored --nocapture --test-threads 1 keccak
PI2_VECTOR=keccak128_rec3 cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end
```

The committed vectors are `tests/vectors/keccak.txt` (32 signatures, `KECCAK_MAIN`), `keccak128_rec3.txt` (128,
`KECCAK_REC3`, the reference) and `keccak_rec3.txt` (400, `KECCAK_REC3`); `tests/evm_vectors.rs` replays them.

### The real proofs' gas

The contract's execution at a claim price of 0, from `prove_real`. It equals the gas measured from the shapes alone.

| signatures | π1 | calldata | straight | deployable (contracts) |
|---:|---|---:|---:|---:|
| 32 | `KECCAK_MAIN` | 7,828 B | 222,928 | 238,182 (4) |
| 32 | `KECCAK_REC3` | 8,980 B | 223,357 | 239,010 (4) |
| 128 | `KECCAK_MAIN` | 8,020 B | 230,985 | 246,393 (4) |
| **128** | **`KECCAK_REC3`** | 9,268 B | 231,447 | 247,457 (4) |
| 400 | `KECCAK_MAIN` | 8,116 B | 236,976 | 252,591 (4) |
| 400 | `KECCAK_REC3` | 9,460 B | 237,510 | 253,909 (4) |

### Measured

**The reference, 128 signatures, `KECCAK_REC3`** (Apple M4 Max, 16 cores, 48 GiB, aarch64: no GFNI, so round 1 runs
`round1_table`; `RUSTFLAGS="-C target-cpu=native"`; 2026-11-08, other agents' jobs on the machine, load average 9–14):
3.65 s warm (the median of 3 passes, `keccak_prover_benchmark`, 3 s cooldown), peak RSS 6.86 GB; one cold run with
the checks, 2.72 s and 6.75 GB. Flock is the largest phase (1.15 s), then the openings (0.66 s), the `C1` and setup
commits (0.45 s), the leaves (0.44 s) and the batching sumcheck (0.38 s); `PROVER.md` ("Measured") has every phase.

**400 signatures, `KECCAK_MAIN`, on the same Mac.** Each figure is one cold run in its own process, the machine idle
before it, from `prove_real`, the test-only combined-claims check left out; the laptop throttles under sustained load,
so these are the best conditions seen, not medians. "Before" is the first working prover; "after" adds the round-1
table kernel, `q_flock` committed from the Flock witness (no copy in the trace), and `C1`'s polynomials and the
leaves freed before `C2`'s commitment. The `SHA3` leaf's grouped transforms and pull/push fingerprints
(`quotients::prefix_quotient`, `prints::PullPush`, aarch64 only) came later: measured alone, they take that leaf from
0.50 to 0.31 s.

| phase (400 signatures, `KECCAK_MAIN`) | before | after |
|---|---:|---:|
| the Keccak-f blocks: `q_flock` and Flock's witness (65,536 blocks), and the placement | 0.20 | 0.10 |
| `C1` and setup: inverse NTTs to basis `B` | 0.08 | 0.07 |
| `C1` and setup: WHIR commits (`2^28`, `2^23`) | 0.54 | 0.54 |
| Flock: zerocheck (round 1), lincheck, slices | 3.04 (2.14) | 1.05 (0.16) |
| heap | 0.07 | 0.07 |
| quotient: tree | 0.11 | 0.11 |
| quotients: leaves (of which `SHA3`'s, 2^16 rows, 86 columns) | 0.57 (0.41) | 0.61 |
| quotient: constraints `Q_W` | 0.13 | 0.13 |
| `C2`: chunks, WHIR commit (`2^28`) | 0.48 | 0.51 |
| values at `t`, claims, weights | 0.03 | 0.05 |
| batching sumcheck | 0.53 | 0.55 |
| openings: WHIR (3) | 0.83 | 0.90 |
| **total** | **6.61** | **4.69** |
| peak RSS | 15.5 GB | 14.4 GB |

Under the same conditions, at 128 signatures the total went from 4.25 to 1.99 s (Flock 1.97 → 0.51 s, round 1 1.41 →
0.07 s) and the peak from 7.2 to 6.7 GB; at 32 signatures, after: 0.76 s, 2.3 GB. The peak is reached at `C2`'s
commitment: both stacks are then at their largest, and `C1`'s codeword (twice its stack) is kept for its opening.
`PI1_LOW_MEMORY=1` trades that codeword for re-encoding at the opening.

**leanVM `9d50c92a3`'s own prover on the same Mac** (`cargo leanvm aggregate --xmss N --log-inv-rate 1 --repeat 3`,
its tables filled to powers of two, one commitment of `2^26.5` words): 0.28 s and 4.0 GiB at 128
signatures, 0.93 s and 13.1 GiB at 400.

**h1** (AMD Ryzen 7 PRO 8700GE, 8 cores and 16 threads, 61 GiB; x86 with GFNI, so round 1 runs `round1_bytes`): warm
medians of 3 passes with a 2 s cooldown (`keccak_prover_benchmark`), while other agents' Lean jobs held the load at
3–8. The aarch64-only `SHA3` leaf changes do not apply there. The proofs are byte-identical to the Mac's.

| | 128 signatures | 400 signatures |
|---|---:|---:|
| this prover, `KECCAK_MAIN` | 2.8–3.4 s, 6.7 GB | 7.1–8.4 s, 14.5 GB |
| this prover, `KECCAK_REC3` | | 7.0 s, 14.5 GB |
| leanVM `9d50c92a3` | 0.53–0.61 s, 2.6 GiB | 1.9–2.2 s, 9.6 GiB |

Where the 400-signature `KECCAK_MAIN` proof's time goes on h1 (load 6): Flock 2.07 s, openings 1.65 s, leaves 0.99 s,
batching 0.87 s, `C1` commit 0.86 s, `C2` commit 0.64 s, tree 0.34 s, constraints 0.26 s, the rest 0.76 s. With
`PI1_LOW_MEMORY=1` the peak falls from 14.7 to 13.3 GB and the openings take 0.27 s more.

## What remains

1. **Capacity.** Above about 470 signatures, either commit `q_flock` in two commitments (one more call), or use a
   denser Keccak-f block that keeps a cheap terminal. `docs/leanvm/flock/KECCAK.md` §4.2's `k_log = 16` with a
   general `C` would be `2^10` words per permutation: 1,000 signatures would then put `q_flock` alone at `2^28`.
2. **The prover's speed.** It is several times slower than leanVM `9d50c92a3`'s own prover on the same workload
   (above). Most of the gap is the protocol's: two proof commitments, their openings and the quotients, against
   leanVM's single commitment. What is left to try:
   - on aarch64, a NEON `lanes` module for `crates/membership/quotient/src/ntt.rs`, which today multiplies one lane
     at a time. It would speed up every transform: `C1`'s, the tree, the leaves, `Q_W`.
   - Flock's level-0 bit pass: two kernels were tried and neither was faster. One halved the products; the other read
     L1-resident nibble tables. Its cost is per-quad overhead, not multiplications or cache misses.
3. **Lean.** `formal/UniKeccak` transcribes the verifier and agrees with the Rust on the differential vectors; the
   knowledge soundness and completeness of the univariate verifier for the Keccak VM (a port of `UniSound` and
   `UniComplete`) and the recursion's end theorems for the Keccak π1 are not done (`formal/README.md`, "The Keccak
   VM").
4. **The soundness calculator** (`params/leanvm_univariate_params.py`) still models the BLAKE2s VM (`SPEC.md` §9).
