-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import KeccakFlock

/-!
# The honest column, evaluated

`genColumn` of two states (the zero state and a fixed pseudo-random one), as one batch of two blocks:
* every position of each block holds the AND of its row's two parities and the constant wire holds 1 (the Boolean
  form of `BatchHolds`, `holds_rows`); block 0's lifted block satisfies `r1cs.Holds` itself, decided by one walk;
* the output port holds `keccakF1600` of the input port, and Keccak-f[1600] of the zero state starts with the
  lane `0xF1258F7940E1DDE7` (the Keccak team's test vector);
* a flipped output bit, a flipped `t` bit or a flipped state bit breaks a row.
Run with `lake env lean ../KeccakFlock/KeccakFlockTest/Honest.lean` from `formal/EndToEnd`.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol Lv42.Protocol KeccakFlock CompPoly

namespace KeccakFlockTest.Honest

def randomState : KeccakState := Vector.ofFn fun i ↦
  ((0x0123456789abcdef : UInt64) * (i.val.toUInt64 + 1)) ^^^ ((0xfedcba9876543210 : UInt64) >>> (i.val.toUInt64 % 64))

def col : Column (KeccakVm.kWords + 1) := genColumn #v[Vector.replicate 25 0, randomState]

/-- The Boolean form of the predicate on block `t`: the constant wire and every row. -/
def rowsHold {κ : ℕ} (c : Column (KeccakVm.kWords + κ)) (t : Fin (2 ^ κ)) : Bool :=
  blockBit c t cpos && (List.finRange (2 ^ m)).all fun k ↦
    blockBit c t k == (parity (blockBit c t) (row k).1 && parity (blockBit c t) (row k).2)

#guard rowsHold col 0 && rowsHold col 1

#guard KeccakVm.kBlockState col 0 inSlot == Vector.replicate 25 0 && KeccakVm.kBlockState col 1 inSlot == randomState

#guard KeccakVm.kBlockState col 0 outSlot == keccakF1600 (Vector.replicate 25 0) &&
  KeccakVm.kBlockState col 1 outSlot == keccakF1600 randomState

#guard (KeccakVm.kBlockState col 0 outSlot)[0] == 0xF1258F7940E1DDE7

/-- Block 0 lifted to `E`: the block `BatchHolds` reads (`batchBlock_bitTable`). -/
def block0 : CMlPolynomialEval E m :=
  (Vector.ofFn fun p : Pos ↦ ProductCircuit.ofBool E (blockBit col 0 p) : Vector E (2 ^ m))

#guard decide (r1cs.Holds block0)

/-- The column with bit `z` of block 1's word `w` flipped. -/
def flip (c : Column (KeccakVm.kWords + 1)) (w z : ℕ) : Column (KeccakVm.kWords + 1) :=
  ⟨(c.values.setIfInBounds (w + 2048) (BF64.ofBitVec (c.values[w + 2048]!.toBitVec ^^^ BitVec.twoPow 64 z)) :
    Vector K (2 ^ (KeccakVm.kWords + 1)))⟩

-- An output bit (X of quad 3), a `t_5` bit, a state bit of `A_10`, an input bit (C of quad 0: the rows above it
-- break), an empty bit: each breaks block 1 and leaves block 0.
#guard rowsHold (flip col (portWord 3 0) 17) 0 && !rowsHold (flip col (portWord 3 0) 17) 1
#guard !rowsHold (flip col (tWord 5 7) 40) 1
#guard !rowsHold (flip col (aWord 10 12) 0) 1
#guard !rowsHold (flip col (portWord 0 2) 63) 1
#guard !rowsHold (flip col (tWord 3 27) 5) 1

end KeccakFlockTest.Honest
