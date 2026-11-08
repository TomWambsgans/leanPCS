-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import KeccakVm.Isa
import KeccakVm.Instance

/-!
# KeccakVm: the Keccak VM's statement

The Keccak VM (`crates/leanvm_univariate/KECCAK.md`): leanVM 42422001 with its `BLAKE2S` instruction replaced by
leanVM `9d50c92a3`'s `SHA3`, one step of that leanVM's cell sponge over Keccak-f[1600] (`Isa.lean`), and its
relation in the form of leanVM 42422001's, with the Keccak-f block a parameter (`Instance.lean`). See `README.md`.

The build fails if a definition the statement rests on uses an axiom beyond Lean's three standard ones.
-/

/-- info: 'KeccakVm.ValidExecution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KeccakVm.ValidExecution

/-- info: 'KeccakVm.executeWith_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KeccakVm.executeWith_base

/-- info: 'KeccakVm.laneCell_cellLanes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms KeccakVm.laneCell_cellLanes

/-- info: 'KeccakVm.KvHolds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KeccakVm.KvHolds

/-- info: 'KeccakVm.KvHonest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KeccakVm.KvHonest
