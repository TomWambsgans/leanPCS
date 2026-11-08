-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import KeccakVm.Isa

/-!
# `sha3Step` against SHA3-256

A message of at most 128 bytes is hashed by one step of leanVM `9d50c92a3`'s cell sponge (plain SHA3-256 there):
the step of the final block `"abc" ‖ 0x06` (the rate's last byte, `END_BIT`, is the step's own) gives
SHA3-256(`"abc"`) = `3a985da7…11431532` in lanes `0..3` (Python's `hashlib.sha3_256`, as little-endian lanes);
`cellsOfState` and `stateOfCells` keep the state. Run with `lake env lean ../KeccakVm/KeccakVmTest/Isa.lean` from
`formal/EndToEnd`.
-/

open LeanVM.Semantics KeccakVm

def sha3AbcCheck : Bool :=
  let s := sha3Step (finalState [0x61, 0x62, 0x63])
  ((List.range 4).map fun l ↦ Keccak.lane s l) ==
      [0xb225e24fa75d983a, 0xbd90d36b2d175c04, 0x5b529d3e6e085f85, 0x3215431145e2bf46] &&
    stateOfCells (cellsOfState s) == s

#guard sha3AbcCheck

-- Without `END_BIT` the step is not SHA3-256: the check is not vacuous.
#guard
  let s := keccakF1600 (finalState [0x61, 0x62, 0x63])
  Keccak.lane s 0 != 0xb225e24fa75d983a
