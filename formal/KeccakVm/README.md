<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# KeccakVm: the Keccak VM's statement

The Keccak VM (`crates/leanvm_univariate/KECCAK.md`) is leanVM 42422001 with its `BLAKE2S` instruction replaced by
leanVM `9d50c92a3`'s `SHA3`. This library is its statement: the instruction set, and the relation its univariate
verifier would prove knowledge of, in the form `formal/Lv42` gives leanVM 42422001's. It holds definitions (and
`KeccakVm/Lemmas.lean`, the machine's lemmas), with no end theorem about a verifier yet. It is a library of
`formal/EndToEnd` (`KeccakVm`, `srcDir = "../KeccakVm"`, `warningAsError`), next to `Lv42`, whose definitions it reuses.

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only, with formal/leanervm linked
systemd-run --scope -p MemoryMax=12G lake build KeccakVm UniStatement.KeccakTables   # #guard_msgs checks the axioms
lake env lean ../KeccakVm/KeccakVmTest/Isa.lean                     # sha3Step against SHA3-256
lake env lean ../UniStatement/UniStatementTest/KeccakTables.lean    # the verifier's tables against the Rust's
```

## The instruction set (`KeccakVm/Isa.lean`)

- **`SHA3 m₀ m₁ m₂ m₃ tail cap out`**, as leanVM `9d50c92a3` executes it (`cpu/isa.rs`, `cpu/execute.rs`,
  `tables.rs::sha3_cells`, `hash_flock.rs`, `primitives/src/hash.rs::step`):
  - it reads thirteen cells: `[o_mᵢ]` (`i < 4`), `[g^k · o_tail]` (`k < 4`), `[g^k · o_cap]` (`k < 5`)
    (`sha3InOffset`);
  - it writes thirteen cells `[g^k · o_out]` (`k < 13`) (`sha3OutOffset`);
  - the cells hold the 25 lanes in the order `sha3CellLanes`: cell `c < 8` lanes `2c, 2c + 1`, cell 8 lane 16 alone,
    cell `9 ≤ c < 13` lanes `2c − 1, 2c`. `laneCell` is its inverse (`laneCell_cellLanes`, by `decide`);
  - a read cell is canonical: its top limb is zero, and so is the lone cell's middle limb (`Sha3Canonical`, the
    executor's `NotCanonical`);
  - the written cells are `cellsOfState (sha3Step s)` of the state `s` the read cells hold (`Sha3Cells`), where
    `sha3Step s = keccakF1600 (s with lane 16 XOR END_BIT)` and `END_BIT = 0x80 << 56`. `keccakF1600` is leanerVM
    `6175f1a0`'s (`Statement/Keccak.lean`), the definition the rest of the repository uses.
- **The other five instructions** run through `Lv42.Semantics.executeWith` (`executeWith_base`).
- **The machine** is Lv42's with this instruction set: `Program`, `step`, `run` (halting at `finalPc`), `Trace`,
  `HasPublicBoundary`, `ValidExecution`, `SentinelSafe`, `Trace.count`.
- **The bytecode entry** of `SHA3` is `(g^5, o_m₀, …, o_m₃, o_tail, o_cap, o_out)`, the order of the table's
  bytecode flush (`entry`, `encodeSlots`).
- **Tested:** `KeccakVmTest/Isa.lean` checks `sha3Step` against SHA3-256 (`hashlib`). A message of at most 128
  bytes is one step of the cell sponge, so the step of `"abc" ‖ 0x06` gives SHA3-256(`"abc"`) in lanes `0..3`.
  The test also checks that `cellsOfState` and `stateOfCells` keep the state, and that the step without `END_BIT`
  differs.

## The relation (`KeccakVm/Instance.lean`)

- **`keccakIsaInstance prog s`**, an `Lv42.Protocol.M3Instance` with nine tables:
  - the memory columns, `BFCNT`, and `QFLOCK` with `2^(11 + τ_SHA3)` cells (`2^11` words a permutation);
  - Lv42's five opcode tables, whose polynomials come from Clean's components;
  - the `SHA3` table (`Sha3Table`): 86 columns, no constraint. Its flushes are the state step, the bytecode read
    and 26 memory reads in Lv42's encoding (pull `(g, addr, cnt, v)`, push `(g, addr, g · cnt, v)`). Their degree is
    at most 2 (`flushExprs_degreeBound`, by `decide +kernel`). The 27 `cnt` columns are its counts;
  - Lv42's boundary blocks, public lines and stacking, with the Keccak VM's bytecode entries;
  - zero padding rows, and no `FlockRegion`.
- **Every column is committed, the lanes included.** In Lv42, the `BLAKE2S` limbs are read off the Flock column.
  This cannot be done for `in_16`, which is its port word plus `END_BIT`, an affine reading that a `Layout` cannot
  express. The lanes are tied to the Flock column by `KeccakAux` instead, as the univariate verifier's `Q_W` ties
  its copies.
- **`KeccakFlockSpec`**, the Keccak-f block as a parameter, as Lv42's instance takes a `FlockSpec`. It has:
  - an R1CS on blocks of `2^17` bits, and its constant position;
  - the input and output port word of each lane;
  - soundness (`step_of_holds`): every block of a column satisfying the predicate holds `keccakF1600` of its input
    port at its output port;
  - completeness: `gen`, `holds_gen`, `in_gen`.
- **`KvHolds F prog s input q`** is `M3Holds (keccakIsaInstance prog s) input q ∧ KeccakAux F prog s q`.
  `KeccakAux` says two things:
  - every block of `QFLOCK` satisfies the block R1CS, with `1` at its constant position;
  - on every executed `SHA3` row `t`, output lane `l` is block `t`'s output port word `l`, and input lane `l` is
    its input port word `l`, plus `END_BIT` for `l = 16` (`laneOffset`).

  `KvHonest` is the same with `M3Honest`.

## The verifier's tables (`formal/UniStatement/UniStatement/KeccakTables.lean`)

- `tablesKeccak` holds `tables`' five tables, and the `SHA3` table in `BLAKE2S`'s place (`sha3Columns`,
  `flushesSha3`).
- `keccakSlot` places input lane `l` at port word `4l + 2` and output lane `l` at `4l`; `keccakSlotOffset` is the
  offset (`END_BIT` for `in_16`); `keccakR1csLogSize` is 17.
- The flushes use the statement's `sha3CellLanes`.
- `UniStatementTest/KeccakTables.lean` compares every table, column, slot, offset and flush form, term by term, with
  the Rust's `tables_keccak()` (`crates/leanvm_flock_gas/tests/lean_keccak_tables.rs`). All 261 lines agree; a
  mutated line fails.

## What is built on it, and what is not done

- **The Keccak-f block** ([`formal/KeccakFlock`](../KeccakFlock/README.md)): `KeccakFlock.keccakFlockSpec`, the
  inhabitant of `KeccakFlockSpec`. `step_of_holds`, `holds_gen` and `in_gen` are proved, with no hypothesis.
- **The arithmetization** ([`formal/KeccakArith`](../KeccakArith/README.md)):
  - the `SHA3` table as a Clean component;
  - `sha3M3_flushes`: its M3 flushes are `Sha3Table.flushes`, polynomial for polynomial;
  - the per-row soundness: under `KeccakAux`, an executed `SHA3` row executes its instruction;
  - **soundness** `KeccakArith.kvSoundness`: under admissible sizes and `SentinelSafe prog`, a stack satisfying
    `KvHolds F prog s input q` represents a `ValidExecution prog input t`;
  - **completeness** `KeccakArith.kvCompleteness`: a `ValidExecution` with at most `2^32` instructions of every opcode
    has a stack satisfying `KvHonest F prog s input q` at the sizes it carries.

  Both are Lv42's `Arithmetization/{Soundness,Completeness}` and `LeanIsa/{Sound,Complete}` ported, sorry-free on the
  three standard axioms. `KeccakVm/Lemmas.lean` holds the machine lemmas they use (`Program.fetch_gpow`, `run_add`,
  `Trace.regs`, `decode_entry`, `entry_injective`).
- **The univariate verifier** ([`formal/UniKeccak`](../UniKeccak/README.md)):
  - `Blake2s::Keccak` transcribed, differential-tested on 74 vectors, the two real Keccak proofs among them;
  - its statements against `KvHolds`: `UniKnowledgeSoundnessKeccak`, the Rec3 variant, completeness.

  The statements are not proved.
- **`Sha3Table.flushes` against the verifier's `flushesSha3`** ([`formal/KeccakFlushes`](../KeccakFlushes/KeccakFlushes.lean)):
  `KeccakFlushes.flushesSha3_eq`: on every row, the verifier's `SHA3` forms of each side (`UniSound.Ids.tupleK`) are, in
  order, the instance's `SHA3` flushes of that side evaluated at the row (UniSound's `uni_tuples_eq` for the `SHA3`
  table, by the same reflection).
