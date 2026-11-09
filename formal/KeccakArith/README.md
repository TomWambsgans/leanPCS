<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# KeccakArith: the Keccak VM's arithmetization

The Keccak VM (`docs/leanvm/univariate/KECCAK.md`, `formal/KeccakVm`) is leanVM 42422001 with its hash instruction
replaced by `SHA3`. Its relation is `KeccakVm.KvHolds F prog s input q` (`M3Holds` of `keccakIsaInstance prog s` and
`KeccakAux F prog s q`). This library gives the `SHA3` table a Clean component in the form of Lv42's tables,
proves what one `SHA3` row of a stack satisfying `KvHolds` means, and proves the relation's soundness
(`kvSoundness`: `KvHolds` gives a valid execution) and completeness (`kvCompleteness`: a valid execution gives a
stack satisfying `KvHonest`), by Lv42's arithmetization proofs ported to the Keccak VM. It is a library of
`formal/EndToEnd` (`KeccakArith`, `srcDir = "../KeccakArith"`, `warningAsError`), on top of `Lv42` and `KeccakVm`.

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only, with formal/leanervm linked
systemd-run --scope -p MemoryMax=12G lake build KeccakArith KeccakFlushes   # #guard_msgs checks the axioms
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
  `Sha3Bindings` (it does not check the permutation).
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
  (`FullGuarantees`: the 26 memory pulls are reads of the image the data names, the bytecode tuple is well formed, Lv42's `EntryOk`:
  its opcode is `g^5`, as Lv42's bus soundness supplies them), the row is bound to the image and
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
  of `sha3RowOf` of a valid `SHA3` execution in the row environment.

Axioms: every theorem above depends on `[propext, Classical.choice, Quot.sound]` (the `#guard_msgs` in
`KeccakArith.lean`).

## The end theorems

```lean
theorem KeccakArith.kvSoundness (F : KeccakFlockSpec) {input : PublicInput} (hs : Admissible prog s)
    (hsafe : SentinelSafe prog) (h : KvHolds F prog s input q) :
    ∃ t, AssignmentRepresents (witnessOf prog s q) t ∧ KeccakVm.ValidExecution prog input t

theorem KeccakArith.kvCompleteness (F : KeccakFlockSpec) {prog : KeccakVm.Program} {input : PublicInput}
    {t : KeccakVm.Trace prog} (h : KeccakVm.ValidExecution prog input t)
    (hcount : ∀ op, t.count op ≤ 2 ^ maxLogRows) :
    ∃ (s : Sizes) (q : Column (keccakIsaμ prog s)), KvHonest F prog s input q ∧ s.logMem = t.κ ∧
      ∀ j : Fin 6, s.rows j = t.count (tableOpcode j)
```

`kvSoundness_exists` drops the representation. `Admissible prog s` is the verifier's announcement check (memory window
`[2^16, 2^32]`, at most `2^32` rows a table, `keccakIsaμ prog s ≤ 28`), Lv42's `Sizes.Admissible` at the Keccak VM's
instance; `SentinelSafe prog` (the last instruction is not a `JUMP`) is Lv42's one condition on the program.

## Soundness (`Ensemble`, `SBus`, `SMemChannel`, `SBcChannel`, `SStateWalk`, `WitnessOf`, `ABus`, `ARelation`, `ASound`)

Lv42's `Arithmetization/Soundness/*` and `Protocol/LeanIsa/{Bus,Relation,Sound}.lean`, at the Keccak VM:

- `Ensemble.lean`: the Keccak VM's Clean ensemble `kEnsemble prog` (Lv42's five tables, `sha3Table`, Lv42's memory and
  bytecode blocks, the verifier `kVerifier prog`), and its statement `SatisfiedBy prog input w`, Lv42's with
  `Sha3RowsValid` (every `SHA3` row satisfies `Sha3Relation`) and the Keccak VM program's
  bytecode rows (`kBytecodeRowOf`); `AssignmentRepresents` at `KeccakVm.Trace`.
- `SBus.lean` … `SStateWalk.lean`: the rows' records (`OpRecs`, from `KOpRow`), the memory and bytecode channels
  (`lookup_sound`, at most `26 · 6 · 2^32` reads), no row at the sentinel, the state walk (`exists_run_of_perm`), and
  `constraintSoundness`: a satisfying witness represents a valid execution.
- `WitnessOf.lean`: the witness read off a stack (`witnessOf`), and the instance's opcode table `j` as its component
  `kOpComponent j` (`inst_flushes_eval`, `inst_constraints_iff`, `mem_inst_counts`, from `sha3M3_flushes`, …).
- `ABus.lean`, `ARelation.lean`: the M3 bus is the three channel pairs (`balanced_iff`, `tuples_perm`), the constraint and
  count clauses are the witness's (`opcode_constraints_iff`, `countsNonzero_iff`).
- `ASound.lean`: `satisfiedBy_witnessOf` (the Keccak relation of the rows from `KeccakAux`, `sha3Relation_stackRow`),
  `kvSoundness`, `kvSoundness_exists`.

## Completeness (`CSkel`, `CBus`, `CWitness`, `CSatisfied`, `CTheorem`, `AComplete`)

After leanerVM's `Arithmetization/Completeness/*` and `Protocol/LeanIsa/Complete.lean` (their
instruction-set-independent parts are `formal/Lv42`'s `*Base` modules), at the Keccak VM:

- `CSkel.lean`: the run's skeletons (`runSkels`, `runRows`, `count_eq_runRows`), the cells an instruction reads
  (`readAddrs`: `SHA3`'s 26 cells), the row of an executing instruction (`rowOf`, `SHA3`'s `sha3RowOf`) and
  `rowOf_sends` (`sha3_exec_sends`: the lanes read back from a canonical image are the image's limbs).
- `CBus.lean`, `CWitness.lean`, `CSatisfied.lean`, `CTheorem.lean`: the rows with their counts, the witness of a run
  (`skelWitness`), `skelWitness_satisfiedBy` (with `skelWitness_sha3_valid`: an executing `SHA3`'s row satisfies the
  Keccak relation, `sha3RowOf_refines`), and `constraintCompleteness_rows`.
- `AComplete.lean`: the stack of a witness (`stackOf`: every column committed at its block, `QFLOCK` the honest column
  `F.gen (sha3States …)` of the executed rows' input states, `END_BIT` XORed into lane 16), `m3Honest_stackOf` (the
  padding rows are zero), `keccakAux_stackOf` (`F.holds_gen`; the input copies from `F.in_gen`, `END_BIT` cancelling in
  characteristic two; the output copies from `F.step_of_holds` and the rows' Keccak relation), `kvHonest_stackOf`,
  `kvCompleteness`.

## Helpers

- `BusBasics.lean`: what a list of sends carries on a channel (`chanOf`, `sendsOf_*`), ISA-independent, copied from
  leanerVM's `Arithmetization/Completeness/{Bus,Satisfied}.lean`.
- `formal/KeccakVm/KeccakVm/Lemmas.lean`: Lv42's program, step and run lemmas at the Keccak VM's machine
  (`Program.fetch_gpow`, `run_add`, `Trace.regs`, …), and the decoder of its bytecode entries (`decode_entry`,
  `entry_injective`).

## The verifier's `SHA3` flushes (`formal/KeccakFlushes`)

`KeccakFlushes.flushesSha3_eq (side : Side) (R : ℕ → K)`: on every row `R : ℕ → K`, the verifier's `SHA3` forms of one
side (`UniStatement.flushesSha3`, read by `UniSound.Ids.tupleK`) are, in order, the instance's `SHA3` flushes of that
side (`KeccakVm.Sha3Table.flushes` filtered by side) evaluated at the row's first 86 cells: the statement UniSound's
`uni_tuples_eq` gives Lv42's five tables, by the same reflection (`LvR.spNorm`, `decide +kernel`). A separate library
(`KeccakFlushes`, a plain-`import` file, since it imports `UniSound.Ids.LvRealize`) so that `KeccakArith` does not
depend on `UniSound`.

## What is not done

Nothing of the scope above. Lv42's read-back (`witnessOf_stackOf`) and the spine `Refinement` (`leanIsaRefinement`) are
not ported (no consumer yet).
