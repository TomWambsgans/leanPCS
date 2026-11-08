-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proofs are `UniSound/Ids/Cvec.lean`'s
-- (`c1P_eval_pointE`, `slotP_eval_pointE`) and `UniSound/Ids/CvecOk.lean`'s (`cvecOk`), for the Keccak VM.
import UniSound.Ids.CvecOk
import UniKeccakSound.IdsMain.Reading

/-!
# `CvecOkK`: the constraint vectors' vanishing gives the rows' constraints

**`cvecOkK`**: where every entry of every row's constraint vector (`cvecK`) vanishes on `V_{r_W}`, the counts are
in range and `RowConstraintsK` holds: each constraint `(M_i, W_i)` of `constraintsPK` has `M_i = 1` on its table's
domain, so `W_i(ω_x) = 0` there, and `W_i(ω_x)` is the constraint on `C1`'s row `x` read in `K`
(`c1PK_eval_pointE`). A lane's copy `copy + slot(y) + offset` reads `q_flock`'s word `slot + 2^11 x`
(`slotPK_eval_pointE`: `y_l(ω_x) = x_l` by the coordinate functionals at `h_SHA3`).

Hypotheses (named in `Ids`): the coordinate functionals at `h_SHA3` (`FunctionalsCorrect`), `r_W ≤ 24`, and the
lanes' slots (`LaneSlotsK`: the kernel does not evaluate `keccakSlot` on a lane's name).
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak Finset Polynomial

/-! ## `C1`'s columns at the points -/

/-- A `C1` column of one limb: its polynomial at `ω_x` is its value. -/
theorem c1PK_eval_pointE (D : KDeployment) (c : Stk) (col : Column) (v off x : ℕ)
    (hl : (layoutOfK D.shape .c1).limbs col = [(0, v, off)]) (hv : v ≤ 24) (hx : x < 2 ^ v) :
    (c1PK D.shape c col).eval (pointE x) = ofK (c1ValK D c col v x) := by
  have hb := c1AlignedK D.shape _ (limbs_mem_blocks (b := (0, v, off))
    (by rw [hl]; exact List.mem_singleton_self _))
  unfold c1PK
  have hV : (layoutOfK D.shape .c1).vars ≤ batchVarsK D.shape :=
    UniSound.layoutOf_vars_le (layoutsOfK D.shape) .c1
  rw [colPoly_eval_pointE betaCantor _ _ c col v off x hl hb.1 hb.2 hV hv hx]
  unfold c1ValK c1Block
  rw [← layoutOfK_c1, hl]

/-- **`q_flock`'s word `slot` at `y(ω_x)`** is the word `slot + 2^11 x`. -/
theorem slotPK_eval_pointE (D : KDeployment) (hf : FunctionalsCorrect (D.shape.heights.getD opBlake2s 0))
    (hB24 : D.shape.heights.getD opBlake2s 0 ≤ 24) (c : Stk) (slot x : ℕ) (hs : slot < 2 ^ 11)
    (hx : x < 2 ^ D.shape.heights.getD opBlake2s 0) :
    (slotPK D.shape c slot).eval (pointE x) = ofK (c (qfOffK D + (slot + 2 ^ 11 * x))) := by
  set hB := D.shape.heights.getD opBlake2s 0
  obtain ⟨off, hl⟩ := c1LayoutK_qflock D.shape
  rw [← layoutOfK_c1] at hl
  have hq11 : qflockRowBits = 11 := rfl
  rw [hq11] at hl
  have hqf : qfOffK D = off := by
    unfold qfOffK
    rw [← layoutOfK_c1, show qflockRowBits = 11 from rfl] at *
    rw [hl]
    rfl
  have hb := c1AlignedK D.shape _ (limbs_mem_blocks (b := (0, hB + 11, off))
    (by rw [hl]; exact List.mem_singleton_self _))
  have hb1 : 2 ^ (hB + 11) ∣ off := hb.1
  have hb2 : off + 2 ^ (hB + 11) ≤ 2 ^ (layoutOfK D.shape .c1).vars := hb.2
  have hV : (layoutOfK D.shape .c1).vars ≤ batchVarsK D.shape :=
    UniSound.layoutOf_vars_le (layoutsOfK D.shape) .c1
  have hoff : off < 2 ^ batchVarsK D.shape := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hV
    have := Nat.two_pow_pos (hB + 11)
    omega
  have hj : slot + 2 ^ 11 * x < 2 ^ (hB + 11) := by
    rw [pow_add]
    have : 2 ^ 11 * x + 2 ^ 11 ≤ 2 ^ 11 * 2 ^ hB := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hx
    rw [mul_comm (2 ^ hB)]
    omega
  have hbit : ∀ l, (slot + 2 ^ 11 * x).testBit l = if l < 11 then slot.testBit l else x.testBit (l - 11) := by
    intro l
    rw [add_comm]
    exact Nat.testBit_two_pow_mul_add x hs l
  unfold slotPK colPoly
  rw [hl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    blockBase_of_aligned hb1 hoff]
  simp only [limbScale, ite_true, map_one, one_mul, hq11]
  rw [eval_mlP _ (hB + 11) _ (pointE x) ((List.range (hB + 11)).map (bitE (slot + 2 ^ 11 * x)))
    (fun l hl' ↦ by
      conv_rhs => rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl']
      simp only [Option.map_some, Option.getD_some]
      unfold bitE
      rw [hbit l]
      by_cases h8 : l < 11
      · simp only [h8, ite_true, eval_C]
      · simp only [h8, ite_false]
        rw [eval_yP_pointE betaCantor hf hB24 (by omega) hx]
        rfl)]
  rw [Finset.sum_congr rfl fun i hi ↦ by
    rw [cubeEq_eq_ite _ (hB + 11) i (slot + 2 ^ 11 * x) (fun l hl' ↦ by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl']; rfl)
      (Finset.mem_range.mp hi) hj]]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' (range (2 ^ (hB + 11))) (slot + 2 ^ 11 * x)]
  simp only [Finset.mem_range, hj, ite_true]
  unfold stE
  rw [ite_eq_left (by omega), hqf]

/-! ## The lanes' slots -/

/-- No column of `SHA3` but a lane has a slot (`keccakSlot` on the names that start neither `in_` nor `out_`). -/
theorem keccakSlot_other : ∀ c : Fin 86, (c.val < 9 ∨ 59 ≤ c.val) →
    keccakSlot (sha3Columns.getD c.val "") = none := by
  decide +kernel

theorem keccakSlot_empty : keccakSlot "" = none := by decide

theorem sha3Columns_length : sha3Columns.length = 86 := by decide

/-- **A lane's slot is below `2^11`** (`LaneSlotsK`). -/
theorem keccakSlot_lt (hL : LaneSlotsK) {col slot : ℕ} (hs : keccakSlot (sha3Columns.getD col "") = some slot) :
    col < 86 ∧ slot < 2 ^ 11 := by
  have hc : col < 86 := by
    by_contra h
    rw [List.getD_eq_default _ _ (by rw [sha3Columns_length]; omega), keccakSlot_empty] at hs
    cases hs
  refine ⟨hc, ?_⟩
  by_cases h1 : col < 9
  · rw [keccakSlot_other ⟨col, hc⟩ (Or.inl h1)] at hs; cases hs
  by_cases h2 : 59 ≤ col
  · rw [keccakSlot_other ⟨col, hc⟩ (Or.inr h2)] at hs; cases hs
  by_cases h3 : col < 34
  · have := (hL ⟨col - 9, by omega⟩).1
    rw [show 9 + (col - 9) = col by omega, hs] at this
    simp only [Option.some.injEq] at this
    rw [this]
    simp only [keccakStateWord, keccakPortWord]
    norm_num
    omega
  · have := (hL ⟨col - 34, by omega⟩).2
    rw [show 34 + (col - 34) = col by omega, hs] at this
    simp only [Option.some.injEq] at this
    rw [this]
    simp only [keccakStateWord, keccakPortWord]
    norm_num
    omega

/-! ## The constraint vectors -/

theorem lift_mul_evalK (r m x : ℕ) (hx : x < 2 ^ r) (hx24 : x < 2 ^ 24) (W : Polynomial E) :
    (liftP r m * W).eval (pointE x) = W.eval (pointE x) :=
  lift_mul_eval betaCantor r m x hx hx24 W

/-- **The constraint vectors give the rows' constraints** (`CvecOkK`). -/
theorem cvecOkK (D : KDeployment) (hf : FunctionalsCorrect (D.shape.heights.getD opBlake2s 0))
    (hrW : D.shape.constraintVars ≤ 24) (hL : LaneSlotsK) : CvecOkK D := by
  intro s c hall
  have hfit : CountsFit D.shape s.2 := by
    by_contra hn
    have := hall 0 (Nat.two_pow_pos _) 1 (by simp [cvecK, hn])
    exact one_ne_zero this
  set S := D.shape
  set rW := S.constraintVars
  set pw := publicWordsOf s.1.toList
  have hzero : ∀ mw ∈ constraintsPK S c pw, ∀ x < 2 ^ rW, (mw.1 * mw.2).eval (pointE x) = 0 :=
    fun mw hmw x hx ↦ hall x hx _ (by
      unfold cvecK
      rw [ite_eq_left (show CountsFit D.shape s.2 from hfit)]
      exact List.mem_map_of_mem (f := fun mw ↦ (mw.1 * mw.2).eval (pointE x)) hmw)
  have htab : ∀ o < 6, ∀ W, (liftP (S.heights.getD o 0) rW, W) ∈
      tableConstraintsPK S c (tablesKeccak.getD o default) →
      ∀ x < 2 ^ S.heights.getD o 0, W.eval (pointE x) = 0 := by
    intro o ho W hW x hx
    have hx' : x < 2 ^ rW := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (height_le_rW S o))
    have hx24 : x < 2 ^ 24 := lt_of_lt_of_le hx' (Nat.pow_le_pow_right (by norm_num) hrW)
    have := hzero _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, tablesKeccak_mem o ho, hW⟩)) x hx'
    rwa [lift_mul_evalK _ _ x hx hx24] at this
  have hcol : ∀ o < 6, ∀ i < (tablesKeccak.getD o default).width, ∀ x < 2 ^ S.heights.getD o 0,
      (c1PK S c (.table o i)).eval (pointE x) = ofK (c1ValK D c (.table o i) (S.heights.getD o 0) x) := by
    intro o ho i hi x hx
    obtain ⟨off, hl⟩ := (c1LimbsK S).table o ho i hi
    exact c1PK_eval_pointE D c _ _ off x hl ((height_le_rW S o).trans hrW) hx
  have hinv : ∀ o < 6, ∀ x < 2 ^ S.heights.getD o 0,
      (c1PK S c (.inverse o)).eval (pointE x) = ofK (c1ValK D c (.inverse o) (S.heights.getD o 0) x) := by
    intro o ho x hx
    obtain ⟨off, hl⟩ := (c1LimbsK S).inverse o ho
    exact c1PK_eval_pointE D c _ _ off x hl ((height_le_rW S o).trans hrW) hx
  refine ⟨hfit, ⟨?_, ?_, ?_, ?_⟩⟩
  · -- JUMP
    intro x hx
    have hmem1 : (liftP (S.heights.getD 4 0) rW,
        c1PK S c (.table 4 (colIdx jumpColumns "b")) + c1PK S c (.table 4 (colIdx jumpColumns "v_cond")) *
          c1PK S c (.table 4 (colIdx jumpColumns "w"))) ∈
            tableConstraintsPK S c (tablesKeccak.getD 4 default) := by
      unfold tableConstraintsPK
      rw [show tablesKeccak.getD 4 default = ⟨opJump, jumpColumns, flushesJump⟩ from rfl]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))
    have hmem2 : (liftP (S.heights.getD 4 0) rW,
        c1PK S c (.table 4 (colIdx jumpColumns "v_cond")) *
          (c1PK S c (.table 4 (colIdx jumpColumns "b")) + 1)) ∈
            tableConstraintsPK S c (tablesKeccak.getD 4 default) := by
      unfold tableConstraintsPK
      rw [show tablesKeccak.getD 4 default = ⟨opJump, jumpColumns, flushesJump⟩ from rfl]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have e1 := htab 4 (by norm_num) _ hmem1 x hx
    have e2 := htab 4 (by norm_num) _ hmem2 x hx
    have hw : ∀ n, colIdx jumpColumns n < 14 → (c1PK S c (.table 4 (colIdx jumpColumns n))).eval (pointE x) =
        ofK (c1ValK D c (.table 4 (colIdx jumpColumns n)) (S.heights.getD 4 0) x) :=
      fun n hn ↦ hcol 4 (by norm_num) _ (by
        rw [show tablesKeccak.getD 4 default = ⟨opJump, jumpColumns, flushesJump⟩ from rfl]
        simpa [Table.width, jumpColumns] using hn) x hx
    simp only [Polynomial.eval_add, Polynomial.eval_mul, eval_one] at e1 e2
    rw [hw "b" (by decide), hw "v_cond" (by decide), hw "w" (by decide)] at e1
    rw [hw "b" (by decide), hw "v_cond" (by decide)] at e2
    refine ⟨ofK_injective ?_, ofK_injective ?_⟩
    · rw [UniSound.Ids.ofK_add, UniSound.Ids.ofK_mul, UniSound.Ids.ofK_zero]; exact e1
    · rw [UniSound.Ids.ofK_mul, UniSound.Ids.ofK_add, UniSound.Ids.ofK_one, UniSound.Ids.ofK_zero]; exact e2
  · -- the counters
    intro o ho x hx
    have hmem : (liftP (S.heights.getD o 0) rW, c1PK S c (.inverse o) *
        ((tablesKeccak.getD o default).countColumns.map fun j ↦ c1PK S c (.table o j)).prod + 1) ∈
          tableConstraintsPK S c (tablesKeccak.getD o default) := by
      unfold tableConstraintsPK
      rw [tablesKeccak_opcode o ho]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    have e := htab o ho _ hmem x hx
    rw [Polynomial.eval_add, Polynomial.eval_mul, eval_one, eval_list_prod_of, List.map_map,
      hinv o ho x hx] at e
    have hc : ∀ j ∈ (tablesKeccak.getD o default).countColumns,
        (Polynomial.eval (pointE x) ∘ fun j ↦ c1PK S c (.table o j)) j =
          ofK (c1ValK D c (.table o j) (S.heights.getD o 0) x) := by
      intro j hj
      have : j < (tablesKeccak.getD o default).width := by
        unfold Table.countColumns at hj
        exact List.mem_range.mp (List.mem_filter.mp hj).1
      exact hcol o ho j this x hx
    rw [List.map_congr_left hc] at e
    refine ofK_injective ?_
    rw [UniSound.Ids.ofK_mul, UniSound.Ids.ofK_one, ofK_list_prod, List.map_map]
    exact (CharTwo.add_eq_zero.mp e)
  · -- the copies
    intro x hx col slot hs
    obtain ⟨hc86, hslt⟩ := keccakSlot_lt hL hs
    have hmem : (liftP (S.heights.getD 5 0) rW, c1PK S c (.table 5 col) + slotPK S c slot +
        C (eK (keccakSlotOffset (sha3Columns.getD col "")))) ∈
          tableConstraintsPK S c (tablesKeccak.getD 5 default) := by
      unfold tableConstraintsPK
      rw [show tablesKeccak.getD 5 default = ⟨opSha3, sha3Columns, flushesSha3⟩ from rfl]
      simp only [opJump, opBlake2s, opSha3, show ¬ (5 : ℕ) = 4 by norm_num, ite_false, ite_true,
        List.nil_append]
      refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨col, ?_, ?_⟩)
      · exact List.mem_range.mpr (by simpa [Table.width, sha3Columns_length] using hc86)
      · rw [hs]; rfl
    have e := htab 5 (by norm_num) _ hmem x hx
    rw [Polynomial.eval_add, Polynomial.eval_add, hcol 5 (by norm_num) col (by
      rw [show tablesKeccak.getD 5 default = ⟨opSha3, sha3Columns, flushesSha3⟩ from rfl]
      simpa [Table.width, sha3Columns_length] using hc86) x hx,
      slotPK_eval_pointE D hf ((height_le_rW S 5).trans hrW) c slot x hslt hx, eval_C, eK_eq] at e
    have e2 := CharTwo.add_eq_zero.mp (show ofK (c1ValK D c (.table 5 col) (S.heights.getD 5 0) x) +
        (ofK (c (qfOffK D + (slot + 2 ^ 11 * x))) +
          ofK (K.ofLane (keccakSlotOffset (sha3Columns.getD col "")))) = 0 by rw [← add_assoc]; exact e)
    rw [← UniSound.Ids.ofK_add] at e2
    have e3 := ofK_injective e2
    show c1ValK D c (.table 5 col) (S.heights.getD 5 0) x = _
    rw [e3, show qflockRowBits = 11 from rfl, add_assoc]
    rfl
  · -- the public lines
    intro k hk
    obtain ⟨off, hl⟩ := (c1LimbsK S).memory k (by omega)
    have hmem : (liftP 1 rW, c1PK S c (.memory k) + C ((linesOf pw).getD k (0, 0)).1 +
        X * C (((linesOf pw).getD k (0, 0)).1 + ((linesOf pw).getD k (0, 0)).2)) ∈ constraintsPK S c pw := by
      refine List.mem_append_right _ (List.mem_map.mpr ⟨((linesOf pw).getD k (0, 0), k), ?_, rfl⟩)
      have hk3 : k < ((linesOf pw).zip (List.range 3)).length := by simp [linesOf]; omega
      have := List.getElem_mem hk3
      rw [List.getElem_zip, List.getElem_range] at this
      rw [List.getD_eq_getElem _ _ (by simp [linesOf]; omega)]
      exact this
    have hlm : S.logMemory ≤ 24 := (logMemory_le_rW S).trans hrW
    have h1 : 1 < 2 ^ S.logMemory := Nat.one_lt_two_pow D.logMemory_pos.ne'
    have hpt : ∀ x < 2, (c1PK S c (.memory k)).eval (pointE x) =
        ofK (c1ValK D c (.memory k) S.logMemory x) := fun x hx ↦
      c1PK_eval_pointE D c _ _ off x hl hlm (by omega)
    have hrW1 : 1 ≤ rW := (Nat.one_le_iff_ne_zero.mpr D.logMemory_pos.ne').trans (logMemory_le_rW S)
    have e0 := hzero _ hmem 0 (Nat.two_pow_pos _)
    have e1 := hzero _ hmem 1 (Nat.one_lt_two_pow (by omega))
    rw [lift_mul_evalK 1 rW 0 (by norm_num) (by norm_num)] at e0
    rw [lift_mul_evalK 1 rW 1 (by norm_num) (by norm_num)] at e1
    simp only [Polynomial.eval_add, Polynomial.eval_mul, eval_C, eval_X] at e0 e1
    rw [hpt 0 (by norm_num), pointE_zero, zero_mul, add_zero] at e0
    rw [hpt 1 (by norm_num)] at e1
    have hp1 : pointE 1 = 1 := by
      rw [pointE_eq_omega betaCantor (by norm_num), Heap.omega_one (cantorE betaCantor) (by norm_num)]
    rw [hp1, one_mul] at e1
    constructor
    · rw [← CharTwo.add_eq_zero.mp e0]
      unfold toK
      simp
      rfl
    · have h2 : ofK (c1ValK D c (.memory k) S.logMemory 1) = ((linesOf pw).getD k (0, 0)).2 := by
        have := e1
        rw [add_assoc, ← add_assoc ((linesOf pw).getD k (0, 0)).1, CharTwo.add_self_eq_zero,
          zero_add] at this
        exact CharTwo.add_eq_zero.mp this
      rw [← h2]
      unfold toK
      simp
      rfl

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.cvecOkK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.cvecOkK
