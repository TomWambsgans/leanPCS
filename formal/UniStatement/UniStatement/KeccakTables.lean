-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `crates/leanvm/statement/src/layout.rs`
-- (`SHA3_COLUMNS`, `flushes_sha3`, `SHA3_STATE_CELLS`, `SHA3_CELL_LANES`, `tables_keccak`, `keccak_slot`,
-- `SHA3_END_BIT`, `keccak_slot_offset`, `KECCAK_R1CS_LOG_SIZE`) and `keccak_flock.rs` (`LOG_SIZE`, `state_word`),
-- adapted there from leanVM `9d50c92a3`'s `Sha3Table` (`crates/leanvm_core/src/tables.rs`).
module

public import UniStatement.TablesBase
public import KeccakVm.Isa

/-!
# The Keccak VM's tables (`layout.rs::tables_keccak`)

The Keccak VM's six tables as the verifier reads them: `tables`' five, and the `SHA3` table in `BLAKE2S`'s place
(`opSha3 = 5`). The `SHA3` table has 86 columns: `pc`, `fp`, the seven operands, the 25 input and 25 output lanes,
one read count a cell in flush order (`cnt_0 … cnt_25`), the bytecode count. Its flushes are the state step, the
bytecode read (the seven operands), and the thirteen cells read and the thirteen written, each its two lanes and a
zero top, the lone lane-16 cell its one lane (`memoryCols`'s missing limbs are zero). The cell layout is the
statement's (`KeccakVm.sha3CellLanes`), so the table reads the cells `KeccakVm.executeWith` reads, at the addresses
`KeccakVm.sha3InOffset`, `sha3OutOffset` name.

**The lanes in `q_flock`** (`keccakSlot`): input lane `l` is the block's input port word `4l + 2`
(`state_word(-1, l)`, the port's `C` role), output lane `l` its output port word `4l` (`state_word(23, l)`, the `X`
role); a block is `2^17` positions, one permutation (`keccakR1csLogSize`). The `SHA3` column `in_16` is its port
word plus `END_BIT` (`keccakSlotOffset`): the block proves Keccak-f of its input port, and the instruction's step
XORs `END_BIT` into lane 16 first (`KeccakVm.sha3Step`).

`UniStatementTest/KeccakTables.lean` compares every table, column, slot, offset and flush form with the Rust's
(`crates/leanvm/statement/tests/lean_keccak_tables.rs`).
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters

/-- `OP_SHA3`: the `SHA3` table, in `BLAKE2S`'s place. -/
def opSha3 : ℕ := 5

/-- `SHA3_STATE_CELLS`. -/
def sha3StateCells : ℕ := 13

/-- `SHA3_COLUMNS`: `pc`, `fp`, the seven operands, the input and output lanes (`q_flock`'s port words, committed
again as the univariate copies), a read count a cell in flush order, the bytecode count. -/
def sha3Columns : List String :=
  ["pc", "fp", "o_m0", "o_m1", "o_m2", "o_m3", "o_tail", "o_cap", "o_out"] ++
    (List.range 25).map (fun l ↦ s!"in_{l}") ++ (List.range 25).map (fun l ↦ s!"out_{l}") ++
    (List.range 26).map (fun c ↦ s!"cnt_{c}") ++ ["cnt_bc"]

/-- `flushes_sha3()`: the state step, the bytecode read, and the thirteen cells read and the thirteen written in
`SHA3_CELL_LANES`' order; input cell `c` at `fp · o_m_c` (`c < 4`), `fp · g^(c−4) · o_tail` (`c < 8`),
`fp · g^(c−8) · o_cap`; output cell `c` at `fp · g^c · o_out`. -/
def flushesSha3 : Flushes :=
  let c := colIdx sha3Columns
  let (pc, fp, cntBc) := (c "pc", c "fp", c "cnt_bc")
  let om := [c "o_m0", c "o_m1", c "o_m2", c "o_m3"]
  let (oTail, oCap, oOut) := (c "o_tail", c "o_cap", c "o_out")
  let operands := (om ++ [oTail, oCap, oOut]).map fun i ↦ col i 0
  let inputAddress (cell : ℕ) : Form :=
    if cell < 4 then prod fp (om.getD cell 0) 0
    else if cell < 8 then prod fp oTail (cell - 4)
    else prod fp oCap (cell - 8)
  let start := (({ push := [], pull := [] } : Flushes).stateStep pc fp).bytecode pc cntBc opSha3 operands
  ([(0, "in"), (1, "out")] : List (ℕ × String)).foldl (fun f (side, pre) ↦
    (List.range sha3StateCells).foldl (fun f cell ↦
      let address := if side == 0 then inputAddress cell else prod fp oOut cell
      let count := c s!"cnt_{side * sha3StateCells + cell}"
      let lo := c s!"{pre}_{(KeccakVm.sha3CellLanes cell).1}"
      match (KeccakVm.sha3CellLanes cell).2 with
      | some hi => f.memoryCols address count [lo, c s!"{pre}_{hi}"]
      | none => f.memoryCols address count [lo]) f) start

/-- **The Keccak VM's tables** (`tables_keccak()`): `tables`' five and the `SHA3` table in `BLAKE2S`'s place. -/
def tablesKeccak : List Table :=
  [⟨opXor, arithColumns, flushesArith opXor false⟩, ⟨opMul, arithColumns, flushesArith opMul true⟩,
    ⟨opSet, setColumns, flushesSet⟩, ⟨opDeref, derefColumns, flushesDeref⟩,
    ⟨opJump, jumpColumns, flushesJump⟩, ⟨opSha3, sha3Columns, flushesSha3⟩]

/-- `KECCAK_R1CS_LOG_SIZE = keccak_flock::LOG_SIZE`: one permutation is a block of `2^17` positions, `2^11` words. -/
def keccakR1csLogSize : ℕ := 17

/-- `port_word(q, role) = 4q + role`. -/
def keccakPortWord (q role : ℕ) : ℕ := 4 * q + role

/-- `state_word(j, l)`, `−1 ≤ j ≤ 23`: the input port's `C` (`j = −1`), the output port's `X` (`j = 23`), a
materialised state otherwise. -/
def keccakStateWord (j : ℤ) (l : ℕ) : ℕ :=
  if j < 0 then keccakPortWord l 2
  else if j = 23 then keccakPortWord l 0
  else 64 * (j.toNat + 2) + 32 + l

/-- The lane a name `prefix_l` names. -/
def laneOf (prefix_ n : String) : Option ℕ :=
  if n.startsWith prefix_ then (String.ofList (n.toList.drop prefix_.length)).toNat? else none

/-- `keccak_slot(name)`: input lane `l` at `state_word(−1, l)`, output lane `l` at `state_word(23, l)`. -/
def keccakSlot (n : String) : Option ℕ :=
  match laneOf "in_" n with
  | some l => some (keccakStateWord (-1) l)
  | none => (laneOf "out_" n).map (keccakStateWord 23)

/-- `SHA3_END_BIT = 0x80 << 56`, the statement's `KeccakVm.endBit`. -/
def sha3EndBit : UInt64 := KeccakVm.endBit

/-- `keccak_slot_offset(name)`: `END_BIT` for `in_16`, else `0`. -/
def keccakSlotOffset (n : String) : UInt64 := if n == "in_16" then sha3EndBit else 0

end UniStatement

end
