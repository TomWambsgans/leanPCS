-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import KeccakFlock.Block
import KeccakFlock.Sound
import KeccakFlock.Complete
import KeccakFlock.Terminal

/-!
# KeccakFlock: the Keccak-f block of the Keccak VM's Flock argument

The R1CS of `crates/lv42_flock/src/keccak.rs`'s block (`Block.lean`: `KeccakFlock.r1cs`, `cpos`, `inSlot`,
`outSlot`), its soundness (`Sound.lean`: `step_of_holds`), its completeness and the inhabitant of
`KeccakVm.KeccakFlockSpec` (`Complete.lean`: `genColumn`, `holds_gen`, `in_gen`, `keccakFlockSpec`). See
`README.md`.
-/

/-- info: 'KeccakFlock.step_of_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KeccakFlock.step_of_holds

/-- info: 'KeccakFlock.holds_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KeccakFlock.holds_gen

/-- info: 'KeccakFlock.in_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KeccakFlock.in_gen

/-- info: 'KeccakFlock.keccakFlockSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KeccakFlock.keccakFlockSpec
