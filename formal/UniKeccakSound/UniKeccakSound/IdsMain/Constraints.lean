-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The proofs are `UniSound/Ids/LvLink.lean`'s
-- (`constraintsVanish_lv42Stack`, `countsNonzero_lv42Stack`, `publicLinesHold_lv42Stack`, `lvConstraints`) for
-- `formal/KeccakVm`'s instance and `kvStack`.
import UniKeccakSound.IdsMain.Reading

/-!
# `KvConstraintsK`: the constraints on `C1`'s rows are the Keccak VM's

**`kvConstraintsK D : KvConstraintsK D`**: `RowConstraintsK` (what the constraint quotient gives on `C1`'s rows)
gives `ConstraintsVanish`, `CountsNonzero` and `PublicLinesHold` of `C1`'s Keccak VM stack (`kvStack`), at every
shape: every cell of the instance is `C1`'s (`column_kvStack`), a table's row `x` at `C1`'s row `rowPosition x`
(below `2^h`, whatever the counts: `rowPosition_lt`); `JUMP`'s two constraints are Lv42's (`jump_constraintsHold`),
the other tables have none (`SHA3` included); the instance's count columns are the verifier's counters
(`counts_eqK`, kernel); the public lines are Lv42's.
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.LvLink UniKeccak
open KeccakVm.KeccakIsa (memCol)

/-- **The instance's count columns are the verifier's counters**, table by table and in order. -/
theorem counts_eqK : ∀ j : Fin 6,
    (KeccakVm.KeccakIsa.counts ⟨j.val + 3, by omega⟩).map (·.val) = (tablesKeccak.getD j.val default).countColumns := by
  decide +kernel

section Cells

variable (D : KDeployment) (rows : List ℕ) (c : Stk)

/-- **A row of a table of `C1`'s Keccak VM stack**: `C1`'s values at `rowPosition`. -/
theorem row_kvStack (j : ℕ) (hj : j + 3 < 9) (x : Fin (2 ^ (D.inst rows).τ ⟨j + 3, hj⟩))
    (i : Fin (KeccakVm.KeccakIsa.width ⟨j + 3, hj⟩)) :
    (D.inst rows).row (kvStack D.prog (D.sizes rows) D.shape c) ⟨j + 3, hj⟩ x i =
      c1ValK D c (.table j i.val) (D.shape.heights.getD j 0)
        (rowPosition (rows.getD j 0) (D.shape.heights.getD j 0) x.val) :=
  (column_kvStack D.prog (D.sizes rows) D.shape c ⟨⟨j + 3, hj⟩, i⟩ x).trans (Vector.get_ofFn _ _)

/-- A memory column's cell: `C1`'s value. -/
theorem mem_kvStack (k : Fin 4) (x : Fin (2 ^ (D.sizes rows).logMem)) :
    ((D.inst rows).column (kvStack D.prog (D.sizes rows) D.shape c) (memCol k)).values.get x =
      c1ValK D c (.memory k.val) D.shape.logMemory x.val :=
  (column_kvStack D.prog (D.sizes rows) D.shape c (memCol k) x).trans (Vector.get_ofFn _ _)

/-- **`ConstraintsVanish`** from `JUMP`'s two constraints on every row of `C1`. -/
theorem constraintsVanish_kvStack (hjump : ∀ x < 2 ^ D.shape.heights.getD opJump 0,
      c1ValK D c (.table opJump 13) (D.shape.heights.getD opJump 0) x +
          c1ValK D c (.table opJump 5) (D.shape.heights.getD opJump 0) x *
            c1ValK D c (.table opJump 12) (D.shape.heights.getD opJump 0) x = 0 ∧
        c1ValK D c (.table opJump 5) (D.shape.heights.getD opJump 0) x *
          (c1ValK D c (.table opJump 13) (D.shape.heights.getD opJump 0) x + 1) = 0) :
    (D.inst rows).ConstraintsVanish (kvStack D.prog (D.sizes rows) D.shape c) := by
  intro j C hC x
  rcases j with ⟨_ | _ | _ | j, hj⟩
  · exact absurd hC List.not_mem_nil
  · exact absurd hC List.not_mem_nil
  · exact absurd hC List.not_mem_nil
  · by_cases h4 : j = 4
    · subst h4
      have hpos : rowPosition (rows.getD 4 0) (D.shape.heights.getD opJump 0) x.val <
          2 ^ D.shape.heights.getD opJump 0 := rowPosition_lt (count := rows.getD 4 0) x.isLt
      obtain ⟨h1, h2⟩ := hjump _ hpos
      let row : Fin (Lv42.Protocol.LeanIsa.opcodeComponent 4).width → K := fun i ↦
        c1ValK D c (.table 4 i.val) (D.shape.heights.getD 4 0)
          (rowPosition (rows.getD 4 0) (D.shape.heights.getD 4 0) x.val)
      have hrow : (D.inst rows).row (kvStack D.prog (D.sizes rows) D.shape c) ⟨4 + 3, hj⟩ x = row := by
        funext i
        exact row_kvStack D rows c 4 hj x i
      rw [hrow]
      have hl := List.isEmpty_iff.mp (Lv42.Protocol.LeanIsa.opcode_lookups 4)
      exact (LeanVM.Protocol.toM3_constraints_iff (Lv42.Protocol.LeanIsa.opcodeComponent 4)
        Lv42.Arithmetization.channelSep Lv42.Arithmetization.channelDir Lv42.Protocol.LeanIsa.counted hl row
        (fun _ _ ↦ #[])).mpr (jump_constraintsHold row _ h1 h2) C hC
    · by_cases h5 : j = 5
      · subst h5
        exact absurd hC List.not_mem_nil
      · have h9 : (D.inst rows).ntab = 9 := rfl
        have hj5 : j < 5 := by omega
        have hl := List.length_pos_of_mem hC
        interval_cases j
        · have h0 := Lv42.Protocol.LeanIsa.opcode_constraints_nil 0 (by decide)
          exact absurd hl (by change ¬ 0 < (Lv42.Protocol.LeanIsa.opcodeTable 0).constraints.length; omega)
        · have h0 := Lv42.Protocol.LeanIsa.opcode_constraints_nil 1 (by decide)
          exact absurd hl (by change ¬ 0 < (Lv42.Protocol.LeanIsa.opcodeTable 1).constraints.length; omega)
        · have h0 := Lv42.Protocol.LeanIsa.opcode_constraints_nil 2 (by decide)
          exact absurd hl (by change ¬ 0 < (Lv42.Protocol.LeanIsa.opcodeTable 2).constraints.length; omega)
        · have h0 := Lv42.Protocol.LeanIsa.opcode_constraints_nil 3 (by decide)
          exact absurd hl (by change ¬ 0 < (Lv42.Protocol.LeanIsa.opcodeTable 3).constraints.length; omega)
        · exact absurd rfl h4

/-- **`CountsNonzero`** from the counters' inverse `z·Πc = 1` on every row of `C1`. -/
theorem countsNonzero_kvStack (hcnt : ∀ o < 6, ∀ x < 2 ^ D.shape.heights.getD o 0,
    c1ValK D c (.inverse o) (D.shape.heights.getD o 0) x *
      ((tablesKeccak.getD o default).countColumns.map fun j ↦
        c1ValK D c (.table o j) (D.shape.heights.getD o 0) x).prod = 1) :
    (D.inst rows).CountsNonzero (kvStack D.prog (D.sizes rows) D.shape c) := by
  intro j i hi x _hx
  rcases j with ⟨_ | _ | _ | j, hj⟩
  · exact absurd hi List.not_mem_nil
  · exact absurd hi List.not_mem_nil
  · exact absurd hi List.not_mem_nil
  · have h9 : (D.inst rows).ntab = 9 := rfl
    have hj6 : j < 6 := by omega
    have hmem : i.val ∈ (tablesKeccak.getD j default).countColumns := by
      rw [← counts_eqK ⟨j, hj6⟩]
      exact List.mem_map_of_mem hi
    refine (row_kvStack D rows c j hj x i).trans_ne ?_
    intro h0
    have hc := hcnt j hj6 _ (rowPosition_lt (count := rows.getD j 0) x.isLt)
    rw [List.prod_eq_zero (List.mem_map.mpr ⟨i.val, hmem, h0⟩), mul_zero] at hc
    exact zero_ne_one hc

/-- **`PublicLinesHold`** from the public lines on `C1`. -/
theorem publicLinesHold_kvStack (bytes : List UInt8) (hlines : ∀ k < 3,
    c1ValK D c (.memory k) D.shape.logMemory 0 = toK ((linesOf (publicWordsOf bytes)).getD k (0, 0)).1 ∧
      c1ValK D c (.memory k) D.shape.logMemory 1 = toK ((linesOf (publicWordsOf bytes)).getD k (0, 0)).2) :
    (D.inst rows).PublicLinesHold (publicInputOf bytes) (kvStack D.prog (D.sizes rows) D.shape c) := by
  intro l hl
  have hls : ((D.inst rows).publicLines (publicInputOf bytes)).toList =
      [⟨memCol 0, (publicInputOf bytes).lanes 0, (publicInputOf bytes).lanes 2, false,
          (D.sizes rows).logMem_pos⟩,
        ⟨memCol 1, (publicInputOf bytes).lanes 1, (publicInputOf bytes).lanes 3, false,
          (D.sizes rows).logMem_pos⟩,
        ⟨memCol 2, 0, 0, false, (D.sizes rows).logMem_pos⟩] := rfl
  rw [hls] at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  have hm : ∀ (k : Fin 4) (x : ℕ) (hx : x < 2 ^ (D.sizes rows).logMem),
      ((D.inst rows).column (kvStack D.prog (D.sizes rows) D.shape c) (memCol k)).values.get ⟨x, hx⟩ =
        c1ValK D c (.memory k.val) D.shape.logMemory x :=
    fun k x hx ↦ mem_kvStack D rows c k ⟨x, hx⟩
  rcases hl with rfl | rfl | rfl
  · refine ⟨(hm 0 0 _).trans ((hlines 0 (by norm_num)).1.trans ?_),
      (hm 0 1 _).trans ((hlines 0 (by norm_num)).2.trans ?_)⟩ <;>
      simp [linesOf, publicWordsOf, publicInputOf, toK, eK, eNew]
  · refine ⟨(hm 1 0 _).trans ((hlines 1 (by norm_num)).1.trans ?_),
      (hm 1 1 _).trans ((hlines 1 (by norm_num)).2.trans ?_)⟩ <;>
      simp [linesOf, publicWordsOf, publicInputOf, toK, eK, eNew]
  · refine ⟨(hm 2 0 _).trans ((hlines 2 (by norm_num)).1.trans ?_),
      (hm 2 1 _).trans ((hlines 2 (by norm_num)).2.trans ?_)⟩ <;>
      simp [linesOf, toK_zero]

end Cells

/-- **The constraints on `C1`'s rows are the Keccak VM's** (`KvConstraintsK`), at every shape. -/
theorem kvConstraintsK (D : KDeployment) : KvConstraintsK D := by
  intro s c _ hR
  obtain ⟨hb, hv, hw⟩ := jump_idx
  refine ⟨constraintsVanish_kvStack D s.2 c fun x hx ↦ ?_, countsNonzero_kvStack D s.2 c hR.counters,
    publicLinesHold_kvStack D s.2 c s.1.toList hR.lines⟩
  have h := hR.jump x hx
  rw [hb, hv, hw] at h
  exact h

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.kvConstraintsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.kvConstraintsK
