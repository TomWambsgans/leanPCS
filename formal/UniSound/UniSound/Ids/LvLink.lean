-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The reading lemmas follow `formal/Lv42`'s
-- `LeanIsa/Complete.lean` (`column_stackOf`, `stackColumn_get`); `rowPosition`'s loop is read as
-- `formal/UniComplete`'s `DomainPositions.lean` reads it (`walk`).
import UniSound.Ids.Bridges
import Lv42.Protocol.LeanIsaBase
import Lv42.Protocol.Stack
import Lv42.Protocol.FixedColumns
import Lv42.Arithmetization.Completeness.RowsBase

/-!
# Lv42's tables on `C1`: the shared lemmas

What the Keccak line (`UniKeccakSound`) uses of the removed BLAKE2s VM's link from the verifier's checks on `C1` to
Lv42's relation:

* **`rowPosition` stays in its table** (`rowPosition_lt`): Lv42's row `x < 2^⌈log₂ count⌉` sits at `C1`'s row
  `rowPosition count r x < 2^r`, whatever the count.
* **`JUMP`** at the five shared tables: its width and constraints (`jump_width_base`, `jump_constraintsHold_base`),
  its columns `b, v_cond, w` at `13, 5, 12` (`jump_idx`).
* **`busBound`** (the verifier's flush counts times `2^h_j`, plus the boundary) and `busBound_reference`; small
  helpers (`batchBlock_congr`, `bitTable_get`, `layoutOf_c1`).
-/

namespace UniSound.Ids

/-! `busBound` is in `UniSound.Ids`; the helpers in `UniSound.Ids.LvLink`, clear of the other files' names. -/

namespace LvLink

/-! ## `JUMP`'s constraints at a row -/

section JumpRow

open Lv42.Parameters Lv42.Semantics Lv42.Arithmetization LeanVM.Parameters
open Air.Flat (Component)

/-- A `JUMP` row has twelve columns before its two local witnesses. -/
theorem jumpRow_size : size JumpRow = 12 := rfl

/-- `JUMP`'s shared component has fourteen columns. -/
theorem jump_width_base : (Lv42.Protocol.LeanIsa.baseComponent 4).width = 14 := by decide +kernel

/-- **`jump_constraintsHold` at the shared `JUMP` table** (`baseComponent 4`, the one both instruction sets have). -/
theorem jump_constraintsHold_base (row : Fin (Lv42.Protocol.LeanIsa.baseComponent 4).width → K)
    (data : ProverData K)
    (h1 : row ⟨13, by rw [jump_width_base]; omega⟩ + row ⟨5, by rw [jump_width_base]; omega⟩ *
      row ⟨12, by rw [jump_width_base]; omega⟩ = 0)
    (h2 : row ⟨5, by rw [jump_width_base]; omega⟩ * (row ⟨13, by rw [jump_width_base]; omega⟩ + 1) = 0) :
    (⟨jumpTable⟩ : Component K).operations.ConstraintsHold
      (Environment.fromArray (Array.ofFn row) data) := by
  rw [Component.constraintsHold_iff, Component.rowOperations_mk]
  have hget : ∀ (i : ℕ) (hi : i < 14), (Environment.fromArray (Array.ofFn row) data).get i =
      row ⟨i, by rw [jump_width_base]; exact hi⟩ := by
    intro i hi
    show ((Array.ofFn row)[i]?).getD 0 = _
    rw [Array.getElem?_ofFn]
    simp [jump_width_base, hi]
  have hv : (eval (Environment.fromArray (Array.ofFn row) data)
      (varFromOffset JumpRow 0 : Var JumpRow K)).vcond =
        (Environment.fromArray (Array.ofFn row) data).get 5 := by
    rw [eval_varFromOffset_valueFromOffset]
    simp [valueFromOffset, explicit_provable_type, circuit_norm]
  refine (jump_constraints_iff (varFromOffset JumpRow 0) (Environment.fromArray (Array.ofFn row) data)
    (size JumpRow) _ rfl ((Environment.fromArray (Array.ofFn row) data).get 12)
    ((Environment.fromArray (Array.ofFn row) data).get 13) (by rw [jumpRow_size])
    (by rw [jumpRow_size])).mpr ?_
  rw [hv, hget 5 (by omega), hget 12 (by omega), hget 13 (by omega)]
  exact ⟨h1, h2⟩

end JumpRow

end LvLink

open LeanVM.Parameters UniStatement
open Lv42.Protocol.LeanIsa (opIdx)
open Lv42.Semantics (Program)
open LeanVM.Protocol (cubeIndex)
open LvLink

namespace LvLink

/-! ## `rowPosition` stays in its table -/

private theorem ite_neg_of' {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by
  simp [h]

/-- `rowPosition`'s loop as a recursion over the bits `bs` (`r − 1, …, 0`), its state `(answer, y)`. -/
def rpWalk (count r : ℕ) (v : Bool) : List ℕ → ℕ → Option ℕ × ℕ
  | [], y => (none, y)
  | b :: bs, y =>
    if count.testBit b = v then
      if y < 2 ^ b then (some (2 ^ r - 2 ^ (b + 1) + y), y) else rpWalk count r v bs (y - 2 ^ b)
    else rpWalk count r v bs y

/-- An answer of the walk over bits below `r` is below `2^r`. -/
theorem rpWalk_lt (count r : ℕ) (v : Bool) : ∀ (bs : List ℕ) (y p : ℕ), (∀ b ∈ bs, b < r) →
    (rpWalk count r v bs y).1 = some p → p < 2 ^ r
  | [], y, p, _, h => by simp [rpWalk] at h
  | b :: bs, y, p, hb, h => by
    have hbr : b < r := hb b (List.mem_cons_self ..)
    have hbs : ∀ b' ∈ bs, b' < r := fun b' hb' ↦ hb b' (List.mem_cons_of_mem _ hb')
    rw [rpWalk] at h
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq] at h
      subst h
      have h3 : 2 ^ (b + 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hbr
      have h4 : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ, mul_comm]
      omega
    · exact rpWalk_lt count r v bs _ p hbs h
    · exact rpWalk_lt count r v bs _ p hbs h

/-- **The `for` loop of `rowPosition` is `rpWalk`** over the reversed indices. -/
theorem forIn_rpWalk (count r : ℕ) (v : Bool) (F : ℕ → Option ℕ × ℕ → Id (ForInStep (Option ℕ × ℕ)))
    (hF : ∀ i s, F i s = if (count.testBit (r - 1 - i) == v) = true then
        (if s.2 < 2 ^ (r - 1 - i) then pure (ForInStep.done (some (2 ^ r - 2 ^ (r - 1 - i + 1) + s.2), s.2))
          else pure (ForInStep.yield (none, s.2 - 2 ^ (r - 1 - i))))
        else pure (ForInStep.yield (none, s.2)))
    (L : List ℕ) (y : ℕ) :
    forIn L ((none : Option ℕ), y) F =
      (rpWalk count r v (L.map fun i ↦ r - 1 - i) y : Id (Option ℕ × ℕ)) := by
  induction L generalizing y with
  | nil => rfl
  | cons i L ih =>
    rw [List.forIn_cons, hF, List.map_cons, rpWalk]
    simp only [beq_iff_eq]
    split_ifs with h1 h2
    · rfl
    · exact ih _
    · exact ih _

private theorem range'_map_reverse' (r : ℕ) :
    (List.range' 0 r).map (fun i ↦ r - 1 - i) = (List.range r).reverse := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range', List.getElem_reverse, List.getElem_range,
      List.length_range]
    omega

/-- **`rowPosition` of a non-full table**, by its loop. -/
theorem rowPosition_of_ne' {count r : ℕ} (hf : count ≠ 2 ^ r) (x : ℕ) :
    rowPosition count r x =
      ((rpWalk count r (decide (x < count)) (List.range r).reverse
        (if x < count then x else x - count)).1).getD (2 ^ r - 1) := by
  unfold rowPosition
  simp only [Id.run, ite_neg_of' hf]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_rpWalk count r (decide (x < count)) _ (fun _ _ ↦ rfl)]
  have hsize : (Std.Legacy.Range.mk 0 r 1 (by omega)).size = r := by
    simp [Std.Legacy.Range.size]
  have hL := range'_map_reverse' r
  simp only [decide_eq_true_eq]
  rw [hsize, hL]
  rcases rpWalk count r (decide (x < count)) (List.range r).reverse (if x < count then x else x - count) with
    ⟨_ | v, y'⟩ <;> rfl

theorem rowPosition_full' (r x : ℕ) : rowPosition (2 ^ r) r x = x := by
  unfold rowPosition
  simp only [Id.run]
  rfl

/-- A non-full table's `rowPosition` is below `2^r`, at every `x`. -/
theorem rowPosition_lt_of_ne {count r : ℕ} (hf : count ≠ 2 ^ r) (x : ℕ) : rowPosition count r x < 2 ^ r := by
  rw [rowPosition_of_ne' hf]
  cases h : (rpWalk count r (decide (x < count)) (List.range r).reverse
      (if x < count then x else x - count)).1 with
  | none => exact Nat.sub_lt (Nat.two_pow_pos r) one_pos
  | some p =>
    exact rpWalk_lt count r _ _ _ p (fun b hb ↦ List.mem_range.mp (List.mem_reverse.mp hb)) h

/-- **`rowPosition` stays in its table**: Lv42's row `x < 2^⌈log₂ count⌉` is `C1`'s row
`rowPosition count r x < 2^r`, whatever `count` (for `count ≠ 2^r` at every `x`; for `count = 2^r` the
identity on `x < 2^r`). -/
theorem rowPosition_lt {count r x : ℕ} (hx : x < 2 ^ Nat.clog 2 count) : rowPosition count r x < 2 ^ r := by
  by_cases hf : count = 2 ^ r
  · subst hf
    rw [rowPosition_full']
    rwa [Nat.clog_pow 2 r (by norm_num)] at hx
  · exact rowPosition_lt_of_ne hf x

/-! ## Reading `C1`'s Lv42 stack -/

end LvLink

namespace LvLink

/-! ## The tables agree -/

/-- **`JUMP`'s columns**: `b`, `v_cond`, `w` are columns `13, 5, 12`, Lv42's `JumpRow` order with its
witnesses `w, b` last. -/
theorem jump_idx : colIdx jumpColumns "b" = 13 ∧ colIdx jumpColumns "v_cond" = 5 ∧
    colIdx jumpColumns "w" = 12 := by decide

/-! ## The constraints, the counts, the public lines -/

section Constraints

variable (D : Deployment) (rows : List ℕ) (c : Stk)

/-- `E`'s zero has a zero base limb. -/
theorem toK_zero : toK (0 : E) = 0 := by
  show (0 : E).limb 0 = 0
  simpa using limb_ofK (0 : K) 0

end Constraints

end LvLink

namespace LvLink

/-! ## `QFLOCK` is `q_flock` -/

/-- `C1`'s layout as the identity model finds it (`layoutOf`) is the mapping's (`c1Layout`). -/
theorem layoutOf_c1 (S : UniStatement.Shape) : layoutOf S .c1 = c1Layout S := rfl

/-! ## Flock's region -/

/-- A batch's block depends only on its cells: blocks `t`, `t'` of two batches agree when every
table's cells `cubeIndex jin t`, `cubeIndex jin t'` do. -/
theorem batchBlock_congr {R : Type*} [CommRing R] {s m κ κ' : ℕ}
    (z : Fin (2 ^ s) → CompPoly.CMlPolynomialEval R (m + κ))
    (z' : Fin (2 ^ s) → CompPoly.CMlPolynomialEval R (m + κ')) (t : Fin (2 ^ κ)) (t' : Fin (2 ^ κ'))
    (h : ∀ jsk jin, (z jsk)[cubeIndex jin t] = (z' jsk)[cubeIndex jin t']) :
    Lv42.Protocol.BlockR1CS.batchBlock z t = Lv42.Protocol.BlockR1CS.batchBlock z' t' := by
  apply Vector.ext
  intro j hj
  simp only [Lv42.Protocol.BlockR1CS.batchBlock, Vector.getElem_ofFn]
  exact h _ _

/-- The bit tables' cells are the column's cells' bits. -/
theorem bitTable_get {n : ℕ} (c : LeanVM.Protocol.Column n) (i : Fin (2 ^ Lv42.Parameters.Flock.kSkip))
    (u : Fin (2 ^ n)) : (Lv42.Protocol.bitTable c i)[u] = Lv42.Protocol.cellBit (c.values.get u) i := by
  simp [Lv42.Protocol.bitTable]

end LvLink

/-! ## The bus counts -/

/-- **The bus bound** at a shape: every table's flushes (the verifier's push tuples, as many as its
pulls) times its height, the memory's and the bytecode's blocks, the state boundary. -/
def busBound (S : UniStatement.Shape) : ℕ :=
  ∑ j ∈ Finset.range 6, (tables.getD j default).flushes.push.length * 2 ^ S.heights.getD j 0 +
    2 ^ S.logMemory + 2 ^ S.logBytecode + 1

/-- **The reference shape's bus bound fits**: `busBound reference = 10,878,977` (heights
`18, 18, 18, 18, 17, 18`, the memory `2^21`, the bytecode `2^19`). -/
theorem busBound_reference : 4 * busBound reference + 100 ≤ 2 ^ 32 := by
  decide +kernel

/-! ## Axioms -/

/-- info: 'UniSound.Ids.busBound_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms busBound_reference

end UniSound.Ids
