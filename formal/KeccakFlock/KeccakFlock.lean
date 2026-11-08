-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import KeccakFlock.Block
import KeccakFlock.Sound
import KeccakFlock.Complete
import KeccakFlock.Terminal
import KeccakFlock.TerminalWalk
import KeccakFlock.TerminalCore
import KeccakFlock.TerminalStruct
import KeccakFlock.TerminalShifts
import KeccakFlock.TerminalEq
import KeccakFlock.TerminalFront
import KeccakFlock.TerminalMain

/-!
# KeccakFlock: the Keccak-f block of the Keccak VM's Flock argument

The R1CS of `crates/vendor/leanvm-42422001/flock/src/keccak.rs`'s block (`Block.lean`: `KeccakFlock.r1cs`, `cpos`, `inSlot`,
`outSlot`), its soundness (`Sound.lean`: `step_of_holds`), its completeness and the inhabitant of
`KeccakVm.KeccakFlockSpec` (`Complete.lean`: `genColumn`, `holds_gen`, `in_gen`, `keccakFlockSpec`), and the lincheck
terminal (`Terminal*.lean`: `structuredTerminal_eq_walked`, `walkedTerminal_eq_bilinear`). See `README.md`.
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

/-- info: 'KeccakFlock.Terminal.walkedTerminal_eq_bilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KeccakFlock.Terminal.walkedTerminal_eq_bilinear

/-- info: 'KeccakFlock.Core.structuredTerminal_eq_walked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KeccakFlock.Core.structuredTerminal_eq_walked

/-- info: 'KeccakFlock.Core.structuredTerminal_eq_bilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KeccakFlock.Core.structuredTerminal_eq_bilinear
