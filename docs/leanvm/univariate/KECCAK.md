<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# The Keccak VM: leanVM with Keccak-f in the VM, verified on the EVM

The VM π1 proves: its statement, the workloads, the capacity and the committed proofs. The protocol is
[`SPEC.md`](SPEC.md) (π1 alone as a contract: its gas, §10), Flock's part [`FLOCK.md`](FLOCK.md), the prover
[`PROVER.md`](PROVER.md) and its measurements [`docs/PERF_PROVER.md`](../../PERF_PROVER.md); under the recursion π2
verifies π1 ([`docs/leanvm/rec/SPEC-REC.md`](../rec/SPEC-REC.md), its gas §6).

**Status: proven end to end on real executions** of leanVM `9d50c92a3` (`cargo leanvm aggregate --xmss N`, N = 32, 128,
400):
- the Rust verifier accepts and the three WHIR openings verify, for `KECCAK_MAIN`, `KECCAK_REC3` and `KECCAK_REC4`;
- π1's contract (`KECCAK_MAIN`, `KECCAK_REC3`: the verifier recorded, compiled to EVM code, run on revm) equals the
  Rust verifier word for word and accepts the real calldata, its frame declaring exactly the claims the openings prove;
  mutated proofs are rejected. π1-rec4 has no contract (SPEC.md §14.4): its claims are checked against the Rust
  verifier's;
- π2 (`crates/leanvm/rec`) proves the real 128- and 400-signature π1-rec4 proofs, and the recursion's contract accepts
  them with its frame declaring its 8 claims (`tests/pi2_real.rs`, `real_end_to_end`). It rejects 21 chosen calldata
  bytes flipped at bit 0, and every one of the 576 calldata bytes before the frame's index flipped at bits 0 and 7,
  with the frame's attacks (`frame_and_calldata_attacks`).

**The reference workload is 128 signatures** (`leanvm_statement::shapes::reference()`, `leanvm_rec::REFERENCE`): the
committed vector `tests/vectors/keccak128_rec4.txt`, the contract's reference setup commitment, the recursion's
reference. The gas is a function of the shape, not of the proof: the real proofs run at the gas measured from the
shapes.

## The statement

- **The VM** is leanVM's Keccak branch, as it stood before its switch to a GKR (commit `9d50c92a3`, "flock: fix what
  the three-step block left stale"). It is leanVM `42422001`'s five instruction tables and a `SHA3` table, opcode 5:
  - one row is one Keccak-f step over a thirteen-cell sponge state;
  - the four `m` cells are addressed independently, then come the `tail` run of four cells and the `cap` run of five;
  - thirteen cells are read and thirteen written, each holding two lanes and a zero top (`memory_128`), except the
    lone lane-16 cell (`memory_k`);
  - the bytecode operands are the seven bases;
  - there are 86 columns: 9 operands, 25 + 25 lanes, and 27 counts.

  `leanvm_statement::layout::tables` states the table and its 28 flush pairs; the other five tables are leanVM
  `42422001`'s. In Lean the statement is `formal/KeccakVm`'s `KvHolds`.
- **The hash argument is not leanVM's.** leanVM `9d50c92a3`'s Flock block packs three permutations into `2^17` slots,
  and its lincheck terminal is a walk of the whole circuit, unaffordable in a contract. This verifier uses the
  Keccak-f block of `flock::keccak`, one permutation per `2^17` slots with every round's state materialised, and its
  structured terminal, 3,019 `E` operations at a skip of 3 ([`FLOCK.md`](FLOCK.md)). The block's matrices are never
  committed, so there are no claims on them: 3 claims (`C1`, `C2`, `F`).
- **The link.** The 50 lane columns are committed in `C1` as the univariate copies, which the bus reads. `Q_W` binds
  each one to `q_flock`'s word at its row's block: input lane `l` at the block's input port word, output lane `l` at
  its output port word (`layout::keccak_slot`; FLOCK.md, "The ports"). Each block is `2^11` words, so a `QflockSlot`
  term has 11 slot bits (`verifier::weight_at`).
- **leanVM's opcode exactly.** leanVM's step is `Keccak-f(in ⊕ END_BIT·e₁₆)` (`END_BIT = 0x80 << 56`, SHA3's last
  padding bit). The block proves `Keccak-f` of its input port, so the port of input lane 16 holds `in₁₆ ⊕ END_BIT`, and
  `Q_W`'s copy identity for `in_16` is `copy − port = END_BIT` (`layout::keccak_slot_offset`): one constant.

## Workloads

The workloads are runs of leanVM `9d50c92a3`: `cargo leanvm aggregate --xmss N --log-inv-rate 1`, giving each
table's executed rows (`leanvm_statement::shapes::WORKLOADS`; the traces `src/prover/dump_keccak/` writes have the
same rows). The memory is the cells used, padded to a power of two; the bytecode is `2^17.54` instructions, padded to
`2^18`.

| signatures | XOR | MUL | SET | DEREF | JUMP | SHA3 (Keccak-f) | memory (padded) | heights |
|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 32 | 6,956 | 9,877 | 6,578 | 9,652 | 3,995 | 4,440 | 2^17.5 (2^18) | 13 14 13 14 12 13 |
| **128** | 24,260 | 36,229 | 24,626 | 35,812 | 15,509 | 17,712 | 2^19.5 (2^20) | 15 16 15 16 14 15 |
| 400 | 73,288 | 110,893 | 75,762 | 109,932 | 48,157 | 55,316 | 2^21.1 (2^22) | 17 17 17 17 16 16 |
| 1,000 | 181,438 | 275,593 | 188,562 | 273,432 | 120,085 | 138,266 | 2^22.4 (2^23) | 18 19 18 19 17 18 |

A signature takes about 138 Keccak-f: 128 bytes are absorbed per permutation.

## Capacity

`q_flock` is `2^11` words per permutation, so `C1` reaches WHIR's `2^28` words at `2^16` permutations, **about 470
signatures**. At 400 signatures `C1` is `2^28` words. At 1,000 signatures (138,266 permutations) `q_flock` alone is
`2^29` words: **no proof** (`tests/keccak_vm.rs`, `keccak_stacks_against_whir`). π2's circuit keeps the recursion's
capacity: past `2^24` positions it hashes fewer of π1's claims (SPEC-REC.md).

Beyond 470 signatures: commit `q_flock` in two commitments (one more claim), or a denser Keccak-f block that keeps a
cheap terminal; the block with `k_log = 16` and a general `C` (FLOCK.md, "The block") would be `2^10` words per
permutation, putting 1,000 signatures' `q_flock` at `2^28`.

## Vectors

`tests/vectors/` holds five real proofs, written by `tests/prove_real.rs` (`WRITE_VECTORS=<dir>`, `VECTOR_FILE`),
never by hand:

| file | signatures | variant |
|---|---:|---|
| `keccak.txt` | 32 | `KECCAK_MAIN` |
| `keccak128_rec4.txt` | 128 | `KECCAK_REC4`: the reference, the deployed recursion's π1 |
| `keccak_rec4.txt` | 400 | `KECCAK_REC4` |
| `keccak128_rec3.txt` | 128 | `KECCAK_REC3`: kept because the Lean proves π1-rec3 and the recursion over it |
| `keccak_rec3.txt` | 400 | `KECCAK_REC3` |

`tests/evm_vectors.rs` replays them ([`PROVER.md`](PROVER.md), "Status"); `tests/lean_keccak_vectors.rs` makes the Lean
transcription's vectors from them. Their header lines cite this file. How to write a trace and prove it:
[`PROVER.md`](PROVER.md), "How it runs".

## What remains

1. **Capacity** beyond about 470 signatures (above).
2. **The prover's speed** against leanVM `9d50c92a3`'s own prover on the same workload: most of the gap is the
   protocol's (two proof commitments, their openings and the quotients, against leanVM's single commitment);
   [`docs/PERF_PROVER.md`](../../PERF_PROVER.md).
3. **Lean.** The statement, π1's knowledge soundness and completeness (main line and π1-rec3) and the recursion over
   π1-rec3 are proved at the reference shape (`formal/README.md`); π1-rec4 and π2 hashing π1's claims are not yet
   stated ([`docs/LEAN_PORT.md`](../../LEAN_PORT.md)).
4. **Soundness at other shapes** is modelled only: `params/leanvm_univariate_params.py` gives every workload's rounds
   (SPEC.md §9).
