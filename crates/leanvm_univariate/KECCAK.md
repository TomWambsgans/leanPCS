<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# The Keccak VM: leanVM with Keccak-f in the VM, verified on the EVM

**Status (2026-11-08): proven end to end on real executions.** The univariate PIOP's verifier (`verifier::reduce`) runs
on a VM whose hash is Keccak-f: `Blake2s::Keccak(KECCAK_MAIN)`. It is recorded, compiled to EVM code, run on revm, and
checked word for word against the Rust verifier. The prover (`src/prover/`, "The prover" below) proves real leanVM
`9d50c92a3` executions (`cargo leanvm aggregate --xmss N`, N = 32, 128, 400):
- the Rust verifier accepts, the three WHIR openings verify, and the straight and deployable contracts accept the real
  calldata, with `PCS_OPEN` attesting exactly the claims the openings prove; mutated proofs are rejected;
- the same holds for π1-rec3 (`KECCAK_REC3`);
- π2 (`crates/leanvm_rec`) proves the real 400-signature π1-rec3 proof, and the recursion's contract accepts it.

The gas is a function of the shape, not of the proof: the real proofs run at the gas measured below without a prover.

## The statement

- **The VM** is leanVM's Keccak branch, as it stood before the switch to a GKR (commit `9d50c92a3`, "flock: fix what
  the three-step block left stale"). It is leanVM `42422001` with its BLAKE2S table replaced by a `SHA3` table:
  - one row is one Keccak-f step over a thirteen-cell sponge state;
  - the four `m` cells are addressed independently, then come the `tail` run of four cells and the `cap` run of five;
  - thirteen cells are read and thirteen written, each holding two lanes and a zero top (`memory_128`), except the
    lone lane-16 cell (`memory_k`);
  - the bytecode operands are the seven bases;
  - there are 86 columns: 9 operands, 25 + 25 lanes, and 27 counts.

  `leanvm_flock_gas::layout::tables_keccak` states the table and its 28 flush pairs, and the other five tables are
  unchanged.
- **The hash argument is not leanVM's.** leanVM's Flock block packs three permutations into 2^17 slots and commits
  only the χ products. Its matrices are dense in the θ cascade, so the lincheck terminal is a walk of the whole circuit
  (leanVM's `bilinear_walk`). `crates/lv42_flock/KECCAK.md` §4.2 estimates such a walk at about 1.3M additions a
  permutation, which is unaffordable in a contract.
  - This verifier uses instead the Keccak-f block of `lv42_flock::keccak` (`crates/lv42_flock/KECCAK.md`, M1): one permutation per 2^17
    slots, with every round's state materialised.
  - Its terminal is the structured one (`keccak_flock::structured_terminal`, `crates/lv42_flock/KECCAK.md`, M3), about 3K `E` operations.
  - The `A0` and `B0` matrices (2^34 entries) are never committed, so there are no claims on them: 3 claims in 3 calls,
    against the BLAKE2s main line's 5.
- **The link** is BLAKE2S's. The 50 lane columns are committed in `C1` as the univariate copies. `Q_W` binds each one
  to `q_flock`'s word at its row's block: input lane `l` at the block's input port word `4l + 2`, output lane `l` at
  the output port word `4l`. Each block is 2^11 words, so a `QflockSlot` term has 11 slot bits instead of 8
  (`verifier::weight_at`).
- **leanVM's opcode exactly.** leanVM's step is `Keccak-f(in ⊕ END_BIT·e₁₆)` (`END_BIT = 0x80 << 56`, SHA3's last
  padding bit). The block proves `Keccak-f` of its input port, so the port of input lane 16 holds `in₁₆ ⊕ END_BIT`, and
  `Q_W`'s copy identity for `in_16` is `copy − port = END_BIT` (`layout::keccak_slot_offset`): one constant, +36 gas.

## Workloads

The workloads are runs of leanVM `9d50c92a3` on a Mac: `cargo leanvm aggregate --xmss N --log-inv-rate 1`, giving
each table's executed rows. The memory is the cells used, and the bytecode is 2^17.54 instructions, padded to 2^18.

| signatures | XOR | MUL | SET | DEREF | JUMP | SHA3 (Keccak-f) | memory |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 32 | 6,956 | 9,877 | 6,578 | 9,652 | 3,995 | 4,440 | 2^17.5 |
| 128 | 24,260 | 36,229 | 24,626 | 35,812 | 15,509 | 17,712 | 2^19.5 |
| 400 | 73,288 | 110,893 | 75,762 | 109,932 | 48,157 | 55,316 | 2^21.1 |
| 1,000 | 181,438 | 275,593 | 188,562 | 273,432 | 120,085 | 138,266 | 2^22.4 |

A signature takes about 138 Keccak-f, against about 202 BLAKE2s compressions in `42422001`'s guest, because 128 bytes
are absorbed per permutation.

**Capacity.** `q_flock` is 2^11 words per permutation, against 2^8 per BLAKE2s compression, so `C1` reaches WHIR's
2^28 words at 2^16 permutations, about 470 signatures. At 400 signatures `C1` is 2^28 words. At 1,000 signatures
(138,266 permutations) `q_flock` alone is 2^29 words: **no proof**. The BLAKE2s VM fits 2,000 signatures.
`tests/keccak_vm.rs`, `keccak_stacks_against_whir`, checks this.

## Gas

Measured on revm (`tests/keccak_vm.rs`, `keccak_gas_report`). Transaction gas excludes the 21,000 base and uses
EIP-7623. `c` is the price of a `PCS_OPEN` claim.

| VM, hash argument | signatures | largest stack | calldata | execution | claims / calls | tx, `c` = 0 | tx, `c` = 5,000 |
|---|---:|---:|---:|---:|---:|---:|---:|
| BLAKE2s VM (`42422001`), Flock (a′) | 400 | 2^27 | 7,060 B | 182,031 | 5 / 5 | 294,679 | 319,679 |
| BLAKE2s VM (`42422001`), Flock (a′) | 1,000 | 2^27 | 7,108 B | 182,104 | 5 / 5 | 295,520 | 320,520 |
| **Keccak VM, Flock Keccak-f** | 32 | 2^25 | 7,828 B | 222,928 | 3 / 3 | 347,840 | 362,840 |
| **Keccak VM, Flock Keccak-f** | 128 | 2^27 | 8,020 B | 230,985 | 3 / 3 | 358,957 | 373,957 |
| **Keccak VM, Flock Keccak-f** | 400 | 2^28 | 8,116 B | 236,976 | 3 / 3 | **366,484** | **381,484** |
| Keccak VM's 400 shape with the BLAKE2S table and its Flock (a′) | 400 | 2^28 | 7,060 B | 178,029 | 5 / 5 | 290,677 | 315,677 |
| the same, no hash argument | 400 | 2^28 | 3,556 B | 67,927 | 3 / 3 | 141,910 | 141,910 |

The Keccak contract at 400 signatures, cut into EIP-170 contracts, is 4 contracts with 252,545 of execution and
382,053 transaction gas.

**Where the Keccak argument's cost goes.** These are differences in execution at the same shape (400 signatures),
against BLAKE2s's Flock (a′), +58.9K in total:
- the structured terminal, 42.2K, replacing the matrices' reduction (6.1K): **+36.1K**;
- the ring switch's weight at the batch's point: +8.1K;
- the batch's weights, with 50 more lane columns and 17 more counters in `C1`: +6.9K;
- the combination: +3.3K;
- the bus, where the `SHA3` table's 28 flush pairs send more fingerprints: +2.1K;
- `Q_W`: +1.6K;
- calldata reads and the transcript: +2.2K;
- `PCS_OPEN`, with two calls fewer: −1.4K.

Calldata is 1,056 B more:
- the values at `t`, with 17 more counters: +408 B;
- the bus's fingerprints: +408 B;
- three more zerocheck rounds and three more lincheck rounds: +288 B;
- one batch round fewer: −48 B.

### Under the recursion (`crates/leanvm_rec`)

π1 is recorded with π1-rec3's Fiat–Shamir shape (`Variant { skip: 3, TowerWalk, Rec3 }`), compiled into π2's D16v
circuit on a sample stream, and π2's contract is measured. The gas depends on the circuit alone
(`crates/leanvm_rec/tests/keccak_vm_rec.rs`).

| π1 | Keccak-f | `E` products / linear | π2 positions | π2 blocks / selector pairs | contract execution | tx, `c` = 0 |
|---|---:|---:|---:|---:|---:|---:|
| BLAKE2s VM π1-rec3, 1,000 signatures | 107 | 53,666 / 115,628 | 15.93M of 2^24 (94.9%) | 25 / 156 | 29,832 | 45,464 |
| Keccak VM π1-rec3, 400 signatures | 118 | 8,673 / 6,885 | 15.94M of 2^24 (95.0%) | 22 / 144 | 29,105 | **44,737** |

The BLAKE2s line's 45,464 uses a sample stream. The README's 44,804 uses the real proof, whose stream has more zero
bytes.

- **π2 still holds π1 in 2^24 positions.** The Keccak VM's π1 has 11 more Keccak-f (71 Keccak-256 calls against 67,
  over a stream of 9,424 B against 8,272 B). Its terminal, though, is 3K operations instead of BLAKE2s's walked 49K
  products, so the arithmetic regions nearly vanish.
- **The recursion's contract costs the same as BLAKE2s's,** slightly less.
- **The layout's padding was fixed for this** (`leanvm_rec::circuit::layout::pad_counts`):
  - Before the fix, the Keccak π1 gave 70 blocks and 429 selector pairs: 47,791 of execution and 63,423 of
    transaction gas.
  - The cause was the greedy padding. It added one binary digit at a time and took the region that saved the most
    rows. The largest region, `keccak16/k1` (118 × 6,144 = 724,992 rows), saves nothing from 2 to 3 digits (a carry:
    both pad to 786,432), and saves 61K rows from 3 to 4.
  - So the greedy restored every small region's digits before it took `k1`'s steps.
  - It now looks past steps that save nothing: the best rows saved per added digit over every further digit count.
  - The BLAKE2s π1's layout is unchanged (25 blocks, 156 pairs, the same gas), and `leanvm_rec`'s tests pass.
  - The Lean transcription of the compiler (`formal/RecCircuit/RecCircuit/Layout.lean`, `pad_counts`) still has the
    one-digit greedy and must take the same change.

## The prover

### The trace (`src/prover/dump_keccak/`)

`sh src/prover/dump_keccak/apply.sh <tree>` patches a leanVM `9d50c92a3` tree
(`git -C <leanVM checkout> archive 9d50c92a3 | tar -x -C <tree>`). A proof leanVM starts with `LEANVM_TRACE_DUMP=<dir>`
then runs the program again **without its fill blocks**, writes the run to `<dir>` and exits:

```sh
cd <tree> && LEANVM_TRACE_DUMP=<dir>/xmss400 cargo leanvm aggregate --xmss 400 --log-inv-rate 1
```

- **The fill.** leanVM `9d50c92a3` brings every table to a power of two by executing fill cycles after the halt, `SHA3`
  to a quarter rule with a zero-state dummy on every fourth row (its three-steps-a-block Flock layout). The univariate
  PIOP has its own padding rows (at the complement of `domain::active_positions`, their leaves 1), so the dump is the
  program's own run: `program.filler` emptied, the interpreter halts at the sentinel. The tables hold exactly
  `Stats::base_counts` rows, and the memory's and the bytecode's final counts are those of the rows dumped (the fill's
  frames are never allocated, its instructions keep the count `g^0`).
- The interpreter still reorders the `SHA3` rows when their count is a multiple of four
  (`hash_flock::interleave_dummies`). That is a permutation of executed rows, which the bus does not see.
- The columns are leanVM's own (`tables::fill_table` with the executed row count). Memory cells 0 and 1 are the public
  input. `q_flock` is not dumped.
- `Trace::load` pads each table to `2^ceil(log2 rows)` with its padding row. That row is zero but for two things:
  the counters, set to 1 by `Trace::place`; and a `SHA3` row's output lanes, which hold `step(0) = Keccak-f(END_BIT·e₁₆)`,
  so that `Q_W`'s copy identities hold on padding rows too.
- The dump takes 0.1–0.3 s. The traces are deterministic: the Mac's and h1's are the same bytes.

| signatures | rows (XOR, MUL, SET, DEREF, JUMP, SHA3) | heights | memory | bytecode |
|---:|---|---|---:|---:|
| 32 | 6,956 / 9,877 / 6,578 / 9,652 / 3,995 / 4,440 | 13 14 13 14 12 13 | 2^18 | 2^18 |
| 128 | 24,260 / 36,229 / 24,626 / 35,812 / 15,509 / 17,712 | 15 16 15 16 14 15 | 2^20 | 2^18 |
| 400 | 73,288 / 110,893 / 75,762 / 109,932 / 48,157 / 55,316 | 17 17 17 17 16 16 | 2^22 | 2^18 |

### What the prover does for the Keccak VM

The BLAKE2s VM's prover, with the VM's tables (`verifier::vm_tables`) wherever it read leanVM 42422001's. `Trace::keccak` selects it, and so does
`Blake2s::Keccak` in `prove::Config`.

- **`q_flock`** (`Trace::keccak_flock`): one Keccak-f block a `SHA3` row, padding rows included. Block `i` sits at
  row `i` of the placed table. Its input port is the row's input lanes with `END_BIT` added to lane 16, so its output
  port is the row's output lanes (`step(in) = Keccak-f(in ⊕ END_BIT·e₁₆)`). The witness (`z`, `A z`, `B z`, the
  lincheck's stripes) is `lv42_flock::keccak::generate_witness_with_ab_packed_and_lincheck`'s, over all `2^r` blocks.
  `C1` commits `z` from the witness (`Stack::put_k_words`); the trace keeps no copy.
- **Flock**: `prover::flock::prove_keccak`, the walked (structured) terminal, then the ring map's six challenges.
- **`Q_W`'s copies** (`quotients::constraints_with`): the 50 lane columns against `q_flock`'s port words, 11 slot bits a
  row. `in_16`'s constant `END_BIT` is folded into the slot table, since a multilinear plus a constant is the table
  plus that constant.
- **The batch's weights** (`Weight::with_slot_bits`): `q_flock`'s slot terms with 11 slot bits.
- **The layout words** (`prove::layout_word_for`): the Keccak VM's stacks.
- **π1-rec3's paired batch** (`batch::prove_pairs`) now accepts a stack shorter than the batch with an odd number of
  variables (the setup's `2^23` against `2^25`). Past the words' rounds, the folded table zero-extends itself.

### How to run

Build with `RUSTFLAGS="-C target-cpu=native"`; `LEANVM_TRACE=<dir of a dump_keccak trace>`.

```sh
cargo test --release -p leanvm_univariate --test prove_real -- --ignored --nocapture --test-threads 1 keccak
```

- `proves_and_verifies_keccak` (`KECCAK_MAIN`) and `proves_and_verifies_keccak_rec3` (`KECCAK_REC3`) each:
  - prove, and check the quotients' degrees, the combined claims against the stacks, and the Rust verifier;
  - check that the WHIR openings verify;
  - run the straight and deployable contracts on the real calldata, with word-for-word parity with the Rust
    verifier, each `PCS_OPEN` call equal to the claim an opening proves, every call required, and a flipped byte
    rejected;
  - check that five stream mutations are rejected.
  With `WRITE_VECTORS=<dir>` each writes its test vector.
- `identities_hold_on_the_domain` checks the bus balance, the copies on every row, and the counters.
- `keccak_prover_benchmark`: warm passes with a cooldown between them, as leanVM's benchmark runs (`PI1_REPEAT`,
  `PI1_COOLDOWN`, `PI1_VARIANT=rec3`).

The committed vectors are `tests/vectors/keccak.txt` (32 signatures, `KECCAK_MAIN`) and `tests/vectors/keccak_rec3.txt`
(400 signatures, `KECCAK_REC3`). `tests/evm_vectors.rs` replays them with every other vector, its contract now binding
the vector's own `F` (its third call's root). π2 on the real 400-signature π1-rec3 proof:

```sh
PI2_VECTOR=keccak_rec3 cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end
```

### The real proofs' gas

The contract's execution at a claim price of 0, from `prove_real`. It equals the gas measured above from the shapes alone.

| signatures | π1 | calldata | straight | deployable (contracts) |
|---:|---|---:|---:|---:|
| 32 | `KECCAK_MAIN` | 7,828 B | 222,928 | 238,182 (4) |
| 32 | `KECCAK_REC3` | 8,980 B | 223,357 | 239,010 (4) |
| 128 | `KECCAK_MAIN` | 8,020 B | 230,985 | 246,393 (4) |
| 128 | `KECCAK_REC3` | 9,268 B | 231,447 | 247,457 (4) |
| 400 | `KECCAK_MAIN` | 8,116 B | 236,976 | 252,591 (4) |
| 400 | `KECCAK_REC3` | 9,460 B | 237,510 | 253,909 (4) |

**Recursion, on the real 400-signature π1-rec3 proof.** π2 D16v takes 2.9 s to compile, adapt and check, 3.0 s to
prove and 0.9 s to open, with a peak of 9.8 GB (Mac). The recursion's contract accepts with `PCS_OPEN` attesting its 7
claims in 6 calls, and 18 flipped calldata bytes are rejected. The figures:
- calldata: 980 B (56 zero);
- execution: 29,105;
- transaction: **44,113** (EIP-7623, `c` = 0).

The sample stream gave 44,737; the real proof's calldata has more zero bytes.

### Measured

TIMINGS

## What remains

1. **Capacity.** Above about 470 signatures, either commit `q_flock` in two commitments (one more call), or use a
   denser Keccak-f block that keeps a cheap terminal. `crates/lv42_flock/KECCAK.md` §4.2's `k_log = 16` with a general `C` would be
   2^10 words per permutation: 1,000 signatures would then put `q_flock` alone at 2^28.
2. **The prover's speed.** It is 4–8× slower than leanVM `9d50c92a3`'s own prover on the same workload
   ("Measured"). Most of the gap is the protocol's: two `2^28` commitments, their openings and the quotients, against
   leanVM's single `2^26.5` commitment. What is left to try:
   - the Flock bit passes and the `SHA3` leaf quotient on aarch64.

   `PI1_LOW_MEMORY=1` makes the prover drop `C1`'s codeword after its commitment, so that its opening re-encodes the
   rows its queries open. The proof is the same. At 400 signatures on h1 the peak falls from 14.7 to 13.3 GB, and the
   openings take 0.27 s more.
3. **The Lean transcription's `pad_counts`** (above), and a review of the composition, as for BLAKE2s.
