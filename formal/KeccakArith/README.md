<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# KeccakArith: the Keccak VM's arithmetization

The Keccak VM (`crates/leanvm_univariate/KECCAK.md`, `formal/KeccakVm`) is leanVM 42422001 with `BLAKE2S` replaced
by `SHA3`. Its relation is `KeccakVm.KvHolds F prog s input q` (`M3Holds` of `keccakIsaInstance prog s` and
`KeccakAux F prog s q`). This library gives the `SHA3` table the Clean component Lv42 gives its `BLAKE2S` table, and
proves what one `SHA3` row of a stack satisfying `KvHolds` means. It is a library of `formal/EndToEnd`
(`KeccakArith`, `srcDir = "../KeccakArith"`, `warningAsError`), on top of `Lv42` and `KeccakVm`.

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only, with formal/leanervm linked
systemd-run --scope -p MemoryMax=10G lake build KeccakArith   # #guard_msgs checks the axioms
```

## The `SHA3` table (`KeccakArith/Sha3Table.lean`)

- **`Sha3Row`**: the 86 columns in `SHA3_COLUMNS`' order: `pc, fp`, `om : Vector _ 4`, `otail, ocap, oout`,
  `inLane : Vector _ 25`, `outLane : Vector _ 25`, `cnt : Vector _ 26` (the 13 input cells' counts, then the 13
  output cells'), `cntBc`. Its flat layout is `KeccakVm.Sha3Table`'s column numbering (the flush equality below
  checks every variable index).
- **`sha3Table`**, a `GeneralFormalCircuit K Sha3Row Regs`: the state pull `(pc, fp)` and push `(g·pc, fp)` (its
  output), Lv42's `bytecodeRead` of `(g^5, o_m₀, …, o_m₃, o_tail, o_cap, o_out)`, then 26 of Lv42's `memRead`: input
  cell `c` at `inAddrE c` (`fp·o_m_c`, `g^(c−4)·(fp·o_tail)`, `g^(c−8)·(fp·o_cap)`) and output cell `c` at
  `g^c·(fp·o_out)`, each holding `cellLimbs lane c = (lane lo, lane hi, 0)` for its lanes `sha3CellLanes c` (`0` for
  the lone cell 8's missing high lane).
- **The relation.**
  - `Sha3Bindings mem r`: each of the 26 cells reads, at `fp · sha3InOffset … c` (resp. `sha3OutOffset`), the row's
    cell word `cellWord`;
  - `Sha3Relation r`: `laneState r.outLane = sha3Step (laneState r.inLane)`, the table's `Assumptions`;
  - `Sha3Refines mem r next`: the bindings, and `KeccakVm.executeWith mem.read ⟨pc, fp⟩ (.sha3 …) = some next`;
  - `sha3_refines_iff`: `Sha3Refines mem r next ↔ Sha3Bindings mem r ∧ Sha3Relation r ∧ next = (g·pc, fp)`. The
    executor's canonicality check (`Sha3Canonical`: top limb zero, the lone cell's middle limb zero) holds of every
    cell word, which is the literal zeros of the bus tuples (`sha3Canonical_cellWord`); `readCells_eq_some`
    characterises the executor's thirteen-cell reads.
- **Soundness and completeness of the component** are Clean's fields: soundness gives `Sha3Spec` (`Sha3Refines`
  over the image the prover data names) from `Sha3Relation` and the pull guarantees; completeness takes
  `Sha3Bindings` (it does not check the permutation, as Lv42's `BLAKE2S` table does not check the compression).
- **Rows from executions**: `sha3RowOf mem pc fp om otail ocap oout cnt cntBc` reads the lanes back from the image
  (`lanesOf`, `cellsAt`); `sha3RowOf_refines`: a valid execution of `SHA3` is represented by it, with any counts.
- **The M3 table**: `sha3M3 := (⟨sha3Table⟩ : Component K).toM3 channelSep channelDir counted`, as Lv42 reads its
  opcode tables.
  - `sha3M3_flushes : sha3M3.flushes.map (fun f ↦ (sideOf f.1, f.2)) = KeccakVm.Sha3Table.flushes`: equality of the
    lists of (side, sixteen `CMvPolynomial`s), so the instance's `SHA3` flushes are this component's. Proved from
    `flushForms_eq : flushForms ⟨sha3Table⟩ = Sha3Table.flushExprs` (each interaction is the listed flush, expression
    for expression, separator first; by `decide +kernel` on a tree encoding of the expressions) and
    `flushPolys_eq_tuple`.
  - `sha3M3_count : sha3M3.count = KeccakVm.Sha3Table.counts`, `sha3M3_constraints : sha3M3.constraints = []`
    (`decide +kernel`).

## One row (`KeccakArith/RowSound.lean`)

- `sha3_row_sound env hA hg`: for any row environment, under `Sha3Relation` of the row and the guarantees of its pulls
  (`FullGuarantees`: the 26 memory pulls are reads of the image the data names, the bytecode tuple decodes, as Lv42's
  bus soundness supplies them), the row is bound to the image and
  `KeccakVm.executeWith (imageOf env.data).2.read ⟨pc, fp⟩ r.instr = some ⟨g·pc, fp⟩`.
- `sha3Relation_stackRow F prog s q (h : KeccakAux F prog s q) t (ht : t < s.rows 5)`: the stack's row `t`
  (`stackRow`, read with `rowOfCells` off `(keccakIsaInstance prog s).row q 8 t`) satisfies `Sha3Relation`. From
  `KeccakAux`'s copies (`out_l` = output port word `l`, `in_l` = input port word `l` plus `laneOffset l`) and
  `F.step_of_holds`: the output port is Keccak-f[1600] of the input port, and the input port is the input lanes with
  `END_BIT` XORed into lane 16 again (`laneOffset_endLane`), which is `sha3Step`'s argument.
- `sha3_stackRow_sound`: the two together, for the stack's row read as Clean reads a raw row
  (`valueFromOffset_ofFn`): under `KeccakAux` and the row's pull guarantees, the instruction executes, with
  canonical read cells and `END_BIT` on lane 16.

## The six tables' rows (`KeccakArith/Rows.lean`) and the walk (`KeccakArith/Walk.lean`)

The per-row layer of Lv42's soundness (`Lv42/Arithmetization/Soundness/Rows.lean`), for the Keccak VM:

- `KOpRow c env`: the row sends the messages of a record (Lv42's `RowRec`: state pull and push, the bytecode pull
  and push of an entry `e`, a pull and a push per memory read; `sendsOf`), with at most 26 reads, and under the
  table's `Assumptions`, its constraints and its pulls' guarantees some `ins : KeccakVm.Instr` with
  `KeccakVm.entry ins = e` executes (`KeccakVm.execute`) from the pulled state to the pushed one, to `(g·pc, fp)`
  unless it is a `JUMP`.
- `sha3_sends_gen`: the `SHA3` row circuit's sends in closed form, `sendsOf pc fp (g·pc, fp) cntBc
  (KeccakVm.entry r.instr) (sha3Reads r)`, the 26 reads `(address, count, cellLimbs lane c)`; `kInAddr_eq` ties the
  addresses to `sha3InOffset`.
- `sha3_opRow`, and `xor_kOpRow`, `mul_kOpRow`, `set_kOpRow`, `deref_kOpRow`, `jump_kOpRow` (from Lv42's closed forms
  `*_sends_gen` and `*_refines_iff`; the five instructions execute identically, `KeccakVm.executeWith` being Lv42's
  on them): every row of the six opcode tables is a `KOpRow`.
- `sha3_channelOk`: every interaction of the `SHA3` table is on one of the six channels (Lv42's `ChannelOk`).
- `exists_run_of_perm` (`Walk.lean`): Lv42's walk decomposition (specification Proposition 6.1) at `KeccakVm.step`
  and `KeccakVm.run`.
- Completeness side (`Sha3Table.lean`): `sha3Row_complete` and `sha3_exec_complete`, the constraints of `main` hold
  of `sha3RowOf` of a valid `SHA3` execution in the row environment (Lv42's `blake2s_exec_complete`).

Axioms: every theorem above depends on `[propext, Classical.choice, Quot.sound]` (the `#guard_msgs` in
`KeccakArith.lean`).

## What is not done

- **Whole soundness**: `KvHolds F prog s input q` (admissible sizes, `SentinelSafe`) ⇒ a `KeccakVm.ValidExecution`.
  Done: the per-row layer (all six tables, `KOpRow`; the `SHA3` assumption from `KeccakAux`, `sha3Relation_stackRow`)
  and the walk decomposition. Missing, all stated in Lv42 over `EnsembleWitness (leanIsaEnsemble prog)` and Lv42's
  `Program`, `Instr`, `entry`, `execute`, `run` and so not reusable as they are:
  - the Keccak VM's ensemble (`sha3Table` in `BLAKE2S`'s place, the verifier and bytecode block over
    `KeccakVm.Program`; Lv42's `leanIsaVerifier` depends on the program only through `finalPc`) and its
    `SatisfiedBy`, with `KeccakAux`'s consequence (`Sha3Relation` on every executed row) in place of
    `Blake2sRowsValid` (`Statement.lean`, about 250 lines of definitions);
  - the bus decomposition, the memory and bytecode channels and the sentinel and state-walk arguments
    (`Soundness/{Bus,MemChannel,BytecodeChannel,StateWalk,Theorem}.lean`, about 1,400 lines; `lookup_sound` is
    generic and reusable, the read bound becomes `26 · 6 · 2^32 < 2^64 − 1`), plus `KeccakVm` versions of
    `Program.fetch_gpow`, `Trace.regs`, `regs_eq_map` and the injectivity of `KeccakVm.entry`;
  - the adaptor from the M3 stack to that witness (`witnessOf` for `keccakIsaInstance`, whose columns are all
    committed, and `Protocol/LeanIsa/{Bus,Relation,Sound}.lean`, about 1,300 lines; the `SHA3` table's part of the
    flush and count correspondence is `sha3M3_flushes`, `sha3M3_count`, `toM3_flushes_eq`).
  Estimated 3,000 lines, mostly transcription of Lv42.
- **Completeness**: a valid execution gives a stack with `KvHonest`, via `F.gen`, `F.holds_gen`, `F.in_gen` and
  Lv42's `Completeness/*` and `LeanIsa/Complete.lean` (about 3,300 lines) ported likewise. Done: the `SHA3` row's part
  (`sha3RowOf_refines`, `sha3_exec_complete`). Also needed: `KeccakAux`'s copy clause for the honest stack, whose
  input lane 16 is the port word plus `END_BIT` (`F.in_gen` gives the port words; the output port words need
  `F.step_of_holds` on `F.gen`, which `holds_gen` allows).
