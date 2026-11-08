-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
module

public import KeccakArith.Sha3Table
public import KeccakArith.RowSound
public import KeccakArith.Rows
public import KeccakArith.Walk

/-!
# KeccakArith: the Keccak VM's arithmetization

The `SHA3` table of the Keccak VM (`KeccakVm.Sha3Table`) as a Clean component, in the form of Lv42's `BLAKE2S` table,
and its per-row soundness against `KeccakVm.executeWith` from `KeccakVm.KeccakAux`. See `README.md`.

* `KeccakArith.Sha3Table`: the row (`Sha3Row`, the 86 columns), the component (`sha3Table`), its relation
  (`Sha3Bindings`, `Sha3Relation`, `Sha3Refines`, `sha3_refines_iff`), rows from executions (`sha3RowOf_refines`),
  and the M3 table it gives (`sha3M3`): its flushes are `KeccakVm.Sha3Table.flushes` (`sha3M3_flushes`), its count
  columns `KeccakVm.Sha3Table.counts` (`sha3M3_count`), no constraint (`sha3M3_constraints`).
* `KeccakArith.RowSound`: a row is a step under the Keccak relation and its pulls' guarantees (`sha3_row_sound`);
  on a stack with `KeccakAux` every executed row satisfies the Keccak relation (`sha3Relation_stackRow`), so an
  executed row whose pulls are genuine reads executes (`sha3_stackRow_sound`).
* `KeccakArith.Rows`: the rows of the six opcode tables of the Keccak VM in the shape Lv42's soundness consumes
  (`KOpRow`: the sends of a record `RowRec` with at most 26 reads, and a step of the Keccak VM under the table's
  assumptions, constraints and pull guarantees): `sha3_sends_gen`, `sha3_opRow`, `xor_kOpRow`, `mul_kOpRow`,
  `set_kOpRow`, `deref_kOpRow`, `jump_kOpRow`, `sha3_channelOk`.
* `KeccakArith.Walk`: the walk decomposition at `KeccakVm.run` (`exists_run_of_perm`).

The build fails if the axiom footprint of these theorems grows beyond Lean's three standard axioms.
-/

/-- info: 'KeccakArith.sha3M3_flushes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.sha3M3_flushes

/-- info: 'KeccakArith.sha3M3_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.sha3M3_count

/-- info: 'KeccakArith.sha3_refines_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.sha3_refines_iff

/-- info: 'KeccakArith.sha3RowOf_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.sha3RowOf_refines

/-- info: 'KeccakArith.sha3_row_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.sha3_row_sound

/-- info: 'KeccakArith.sha3Relation_stackRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.sha3Relation_stackRow

/-- info: 'KeccakArith.sha3_stackRow_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.sha3_stackRow_sound

/-- info: 'KeccakArith.sha3_exec_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.sha3_exec_complete

/-- info: 'KeccakArith.sha3_sends_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.sha3_sends_gen

/-- info: 'KeccakArith.sha3_opRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.sha3_opRow

/-- info: 'KeccakArith.xor_kOpRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.xor_kOpRow

/-- info: 'KeccakArith.mul_kOpRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.mul_kOpRow

/-- info: 'KeccakArith.set_kOpRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.set_kOpRow

/-- info: 'KeccakArith.deref_kOpRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.deref_kOpRow

/-- info: 'KeccakArith.jump_kOpRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.jump_kOpRow

/-- info: 'KeccakArith.sha3_channelOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.sha3_channelOk

/-- info: 'KeccakArith.exists_run_of_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakArith.exists_run_of_perm
