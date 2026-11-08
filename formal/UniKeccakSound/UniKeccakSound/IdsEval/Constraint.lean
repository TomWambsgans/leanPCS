-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The program is `formal/UniKeccak`'s
-- `constraintRelationK` (`Verifier.lean`); the proofs are `UniSound/Ids/Eval.lean`'s (`constraintRelation_eq`,
-- `crOf_holds`, `crOf_terms`) for the Keccak lanes' copies.
import UniKeccakSound.IdsEval.Rels

/-!
# The Keccak constraint relation (`constraintRelationK`), as folds, and at `t`

* **`constraintRelationK_eq`**: `constraintRelationK` is its folds (`crOfK`: a table's step `crStepK`, the `SHA3`
  lanes' copies `copyStepK`, the public lines `UniSound.Ids.Eval.lineStep`);
* **`crOfK_holds`**: where it holds under an evaluation reading each table's columns, its counters' inverse and its
  lanes' slots as their polynomials at `t` (`CrTableOkK`), the constraints of `constraintsPK` batched by `γ` plus
  `Q_W(t) w_{r_W}(t)` vanish; each lane copy is `copy + slot(y) + END_BIT·[in_16]` (`keccakSlotOffset`);
* **`crOfK_terms`**: its terms are untwisted, on `C1`, at prefixes of the digits or at `y(t)` (`CrPt`);
* **`crOfK_deg`**: its degree is `Shape.constraintDegreeK`.
-/

namespace UniKeccakSound.IdsEval

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.Eval UniKeccak UniKeccakSound.Ids
  Polynomial

/-! ## The folds -/

/-- **The `SHA3` lanes' copies** (`constraintRelationK`'s inner loop), on (known, terms, power): a lane column `c`
adds `copy_c` and `q_flock`'s slot at `y`, both at the power times the lift, and `END_BIT` for `in_16`. -/
def copyStepK (o r : ℕ) (columns : List String) (w y : List E) (lift gamma : E) (s : E × Array Term × E)
    (c : ℕ) : E × Array Term × E :=
  match keccakSlot (columns.getD c "") with
  | some slot =>
    (if keccakSlotOffset (columns.getD c "") != 0 then
        s.1 + s.2.2 * lift * eK (keccakSlotOffset (columns.getD c "")) else s.1,
      (s.2.1.push (term (.table o c) (w.take r) (s.2.2 * lift))).push (term (.qflockSlot slot) y (s.2.2 * lift)),
      s.2.2 * gamma)
  | none => s

/-- One table's step of `constraintRelationK`'s loop, on (known, terms, power, degree). -/
def crStepK (shape : Shape) (gamma t : E) (w : List E) (s : E × Array Term × E × ℕ)
    (x : Table × TablePart) : E × Array Term × E × ℕ :=
  let r := shape.heights.getD x.1.opcode 0
  let n := 2 ^ r
  let lift := vanishingRatio w r shape.constraintVars
  let s1 : E × Array Term × E × ℕ := if x.1.opcode = opJump then
      (s.1 + s.2.2.1 * lift * (x.2.sent.getD (colIdx x.1.columns "b") none).getD 0 +
          s.2.2.1 * gamma * lift * (x.2.sent.getD (colIdx x.1.columns "v_cond") none).getD 0 *
            ((x.2.sent.getD (colIdx x.1.columns "b") none).getD 0 + 1),
        s.2.1.push (term (.table x.1.opcode (colIdx x.1.columns "w")) (w.take r)
          (s.2.2.1 * lift * (x.2.sent.getD (colIdx x.1.columns "v_cond") none).getD 0)),
        s.2.2.1 * gamma * gamma, max s.2.2.2 (degree n 2))
    else s
  let s2 : E × Array Term × E × ℕ := (s1.1 + s1.2.2.1 * lift,
    s1.2.1.push (term (.inverse x.1.opcode) (w.take r)
      (s1.2.2.1 * lift * x.1.countColumns.foldl (fun acc c ↦ acc * (x.2.sent.getD c none).getD 0) 1)),
    s1.2.2.1 * gamma, max s1.2.2.2 (degree ((n - 1) * (1 + x.1.countColumns.length)) n))
  if x.1.opcode = opBlake2s then
    let inner := (List.range x.1.width).foldl
      (copyStepK x.1.opcode r x.1.columns w (coordinatesAt t (coordinateFunctionals r)) lift gamma)
      (s2.1, s2.2.1, s2.2.2.1)
    (inner.1, inner.2.1, inner.2.2, max s2.2.2.2 (degree (r * (n / 2)) n))
  else s2

/-- **`constraintRelationK`, as folds.** -/
def crOfK (shape : Shape) (parts : List TablePart) (publicWords : List E) (gamma t constraintValue : E)
    (w : List E) : Relation × ℕ :=
  let s := (tablesKeccak.zip parts).foldl (crStepK shape gamma t w) (0, #[], 1, 0)
  let s' := ((linesOf publicWords).zip (List.range 3)).foldl (lineStep shape gamma t w) (s.1, s.2.1, s.2.2.1)
  (⟨s'.2.1.toList, constraintValue * w.getD shape.constraintVars 0 + s'.1⟩,
    max s.2.2.2 (degree (2 ^ shape.logMemory) 3))

/-- **`constraintRelationK` is its folds** (its `Id.run do` loops, unfolded). -/
theorem constraintRelationK_eq (shape : Shape) (parts : List TablePart) (publicWords : List E)
    (gamma t constraintValue : E) (w : List E) :
    constraintRelationK shape parts publicWords gamma t constraintValue w =
      crOfK shape parts publicWords gamma t constraintValue w := by
  unfold constraintRelationK crOfK
  simp only [Id.run]
  rw [forIn_id_eq_foldl' _ _ _ (crStepK shape gamma t w)]
  · simp only [pure_bind, List.forIn_pure_yield_eq_foldl]
    rfl
  · intro x s
    by_cases hj : x.1.opcode = opJump
    · have hb : ¬ x.1.opcode = opBlake2s := by rw [hj]; decide
      simp only [crStepK, ite_eq_left hj, ite_eq_right hb]
    · by_cases hb : x.1.opcode = opBlake2s
      · simp only [crStepK, ite_eq_right hj, ite_eq_left hb]
        rw [forIn_id_eq_foldl' _ _ _ (copyStepK x.1.opcode (shape.heights.getD x.1.opcode 0) x.1.columns w
          (coordinatesAt t (coordinateFunctionals (shape.heights.getD x.1.opcode 0)))
          (vanishingRatio w (shape.heights.getD x.1.opcode 0) shape.constraintVars) gamma)]
        · rfl
        · intro c s'
          unfold copyStepK
          rcases keccakSlot (x.1.columns.getD c "") with _ | slot
          · rfl
          · by_cases ho : (keccakSlotOffset (x.1.columns.getD c "") != 0) = true
            · simp only [ho, ite_true]
            · simp only [ho, Bool.false_eq_true, ite_false]
      · simp only [crStepK, ite_eq_right hj, ite_eq_right hb]

/-! ## At `t` -/

theorem eK_zero : eK 0 = 0 := rfl

/-- `END_BIT`'s known part, `0` when the offset is. -/
theorem offset_known (o : UInt64) (k g : E) :
    (if (o != 0) = true then k + g * eK o else k) = k + g * eK o := by
  by_cases h : (o != 0) = true
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    have : o = 0 := by simpa using h
    rw [this, eK_zero, mul_zero, add_zero]

theorem copyFoldK_spec (ev : Column → List E → E) (o r : ℕ) (columns : List String) (w y : List E)
    (lift gamma : E) : ∀ (l : List ℕ) (s : E × Array Term × E),
      (l.foldl (copyStepK o r columns w y lift gamma) s).1 +
          termsVal ev (l.foldl (copyStepK o r columns w y lift gamma) s).2.1 = s.1 + termsVal ev s.2.1 +
          s.2.2 * powComb (l.filterMap fun c ↦ (keccakSlot (columns.getD c "")).map fun slot ↦
            lift * (ev (.table o c) (w.take r) + ev (.qflockSlot slot) y +
              eK (keccakSlotOffset (columns.getD c "")))) gamma ∧
        (l.foldl (copyStepK o r columns w y lift gamma) s).2.2 =
          s.2.2 * gamma ^ (l.filterMap fun c ↦ keccakSlot (columns.getD c "")).length
  | [], s => by simp [powComb_nil]
  | c :: l, s => by
    rw [List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := copyFoldK_spec ev o r columns w y lift gamma l (copyStepK o r columns w y lift gamma s c)
    rw [ih1, ih2]
    simp only [List.filterMap_cons]
    unfold copyStepK
    rcases keccakSlot (columns.getD c "") with _ | slot
    · simp only [Option.map_none]
      trivial
    · simp only [Option.map_some, termsVal_push, term, powComb_cons, List.length_cons, pow_succ, offset_known]
      exact ⟨by ring, by ring⟩

/-- What the Keccak constraint relation's step needs of the evaluation at a table. -/
structure CrTableOkK (S : Shape) (c1 : Stk) (t : E) (w : List E) (ev : Column → List E → E)
    (tab : Table) (part : TablePart) : Prop where
  lift : vanishingRatio w (S.heights.getD tab.opcode 0) S.constraintVars =
    (liftP (S.heights.getD tab.opcode 0) S.constraintVars).eval t
  col : ∀ c, ev (.table tab.opcode c) (w.take (S.heights.getD tab.opcode 0)) =
    (c1PK S c1 (.table tab.opcode c)).eval t
  inv : ev (.inverse tab.opcode) (w.take (S.heights.getD tab.opcode 0)) = (c1PK S c1 (.inverse tab.opcode)).eval t
  slot : tab.opcode = opBlake2s → ∀ c slot, c < tab.width → keccakSlot (tab.columns.getD c "") = some slot →
    ev (.qflockSlot slot) (coordinatesAt t (coordinateFunctionals (S.heights.getD tab.opcode 0))) =
      (slotPK S c1 slot).eval t
  sent : ∀ c ∈ sentColumns tab, part.sent.getD c none = some ((c1PK S c1 (.table tab.opcode c)).eval t)
  jumpSent : tab.opcode = opJump →
    colIdx tab.columns "b" ∈ sentColumns tab ∧ colIdx tab.columns "v_cond" ∈ sentColumns tab

theorem filterMap_congr_mem {α β : Type} (f g : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x (List.mem_cons_self ..),
      filterMap_congr_mem f g l fun y hy ↦ h y (List.mem_cons_of_mem _ hy)]

/-- **One table's step of the Keccak constraint relation at `t`**: it adds the table's constraints at `t`, batched
by the powers of `γ` from the current power. -/
theorem crStepK_spec (S : Shape) (c1 : Stk) (gamma t : E) (w : List E) (ev : Column → List E → E)
    (tab : Table) (part : TablePart) (h : CrTableOkK S c1 t w ev tab part) (s : E × Array Term × E × ℕ) :
    (crStepK S gamma t w s (tab, part)).1 + termsVal ev (crStepK S gamma t w s (tab, part)).2.1 =
        s.1 + termsVal ev s.2.1 +
          s.2.2.1 * powComb ((tableConstraintsPK S c1 tab).map fun mw ↦ (mw.1 * mw.2).eval t) gamma ∧
      (crStepK S gamma t w s (tab, part)).2.2.1 = s.2.2.1 * gamma ^ (tableConstraintsPK S c1 tab).length := by
  have hcnt : tab.countColumns.foldl (fun acc c ↦ acc * (part.sent.getD c none).getD 0) 1 =
      (tab.countColumns.map fun c ↦ (c1PK S c1 (.table tab.opcode c)).eval t).prod := by
    rw [foldl_mul_getD _ _ _ 1 fun c hc ↦ h.sent c (countColumns_sent tab c hc), one_mul]
  have hprod : ((tab.countColumns.map fun c ↦ c1PK S c1 (.table tab.opcode c)).prod).eval t =
      (tab.countColumns.map fun c ↦ (c1PK S c1 (.table tab.opcode c)).eval t).prod := by
    rw [eval_list_prod_of, List.map_map]
    rfl
  have hcopies := copyFoldK_spec ev tab.opcode (S.heights.getD tab.opcode 0) tab.columns w
    (coordinatesAt t (coordinateFunctionals (S.heights.getD tab.opcode 0)))
    ((liftP (S.heights.getD tab.opcode 0) S.constraintVars).eval t) gamma (List.range tab.width)
  unfold crStepK tableConstraintsPK
  dsimp only
  rw [h.lift]
  by_cases hj : tab.opcode = opJump
  · have hb : ¬ tab.opcode = opBlake2s := by rw [hj]; decide
    obtain ⟨hsb, hsv⟩ := h.jumpSent hj
    simp only [ite_eq_left hj, ite_eq_right hb, List.append_nil, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil, List.length_cons, List.length_nil, powComb_cons, powComb_nil,
      termsVal_push, term, h.sent _ hsb, h.sent _ hsv, Option.getD_some, h.col, h.inv, hcnt,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one, hprod]
    constructor <;> ring
  · by_cases hb : tab.opcode = opBlake2s
    · simp only [ite_eq_right hj, ite_eq_left hb, List.nil_append, List.cons_append, List.map_cons,
        List.length_cons, powComb_cons, term, hcnt, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_one, hprod]
      obtain ⟨hc1, hc2⟩ := hcopies (s.1 + s.2.2.1 * (liftP (S.heights.getD tab.opcode 0) S.constraintVars).eval t,
        s.2.1.push ⟨.inverse tab.opcode, w.take (S.heights.getD tab.opcode 0), 0,
          s.2.2.1 * (liftP (S.heights.getD tab.opcode 0) S.constraintVars).eval t *
            (tab.countColumns.map fun c ↦ (c1PK S c1 (.table tab.opcode c)).eval t).prod⟩, s.2.2.1 * gamma)
      have hfm : ((List.range tab.width).filterMap fun c ↦ (keccakSlot (tab.columns.getD c "")).map fun slot ↦
          (liftP (S.heights.getD tab.opcode 0) S.constraintVars).eval t *
            (ev (.table tab.opcode c) (w.take (S.heights.getD tab.opcode 0)) +
              ev (.qflockSlot slot) (coordinatesAt t (coordinateFunctionals (S.heights.getD tab.opcode 0))) +
              eK (keccakSlotOffset (tab.columns.getD c "")))) =
          (((List.range tab.width).filterMap fun c ↦ (keccakSlot (tab.columns.getD c "")).map fun slot ↦
            (liftP (S.heights.getD tab.opcode 0) S.constraintVars,
              c1PK S c1 (.table tab.opcode c) + slotPK S c1 slot +
                C (eK (keccakSlotOffset (tab.columns.getD c ""))))).map fun mw ↦ (mw.1 * mw.2).eval t) := by
        rw [List.map_filterMap]
        refine filterMap_congr_mem _ _ _ fun c hc ↦ ?_
        rcases hk : keccakSlot (tab.columns.getD c "") with _ | slot
        · rfl
        · simp only [Option.map_some, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, h.col,
            h.slot hb c slot (List.mem_range.mp hc) hk]
      rw [hc1, hc2, termsVal_push, hfm, length_filterMap_map]
      simp only [h.inv, Polynomial.eval_mul]
      constructor
      · ring
      · rw [pow_succ]
        ring
    · simp only [ite_eq_right hj, ite_eq_right hb, List.nil_append, List.append_nil, List.map_cons,
        List.map_nil, List.length_cons, List.length_nil, powComb_cons, powComb_nil, termsVal_push, term,
        h.inv, hcnt, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one, hprod]
      constructor <;> ring

theorem crFoldK_spec (S : Shape) (c1 : Stk) (gamma t : E) (w : List E) (ev : Column → List E → E) :
    ∀ (L : List (Table × TablePart)) (s : E × Array Term × E × ℕ), (∀ x ∈ L, CrTableOkK S c1 t w ev x.1 x.2) →
      (L.foldl (crStepK S gamma t w) s).1 + termsVal ev (L.foldl (crStepK S gamma t w) s).2.1 =
          s.1 + termsVal ev s.2.1 + s.2.2.1 * powComb (L.flatMap fun x ↦
            (tableConstraintsPK S c1 x.1).map fun mw ↦ (mw.1 * mw.2).eval t) gamma ∧
        (L.foldl (crStepK S gamma t w) s).2.2.1 = s.2.2.1 * gamma ^ (L.flatMap fun x ↦
            (tableConstraintsPK S c1 x.1).map fun mw ↦ (mw.1 * mw.2).eval t).length
  | [], s, _ => by simp [powComb_nil]
  | x :: L, s, h => by
    rw [List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := crFoldK_spec S c1 gamma t w ev L (crStepK S gamma t w s x)
      fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    obtain ⟨s1, s2⟩ := crStepK_spec S c1 gamma t w ev x.1 x.2 (h x (List.mem_cons_self ..)) s
    rw [ih1, ih2, s1, s2, List.flatMap_cons, powComb_append, List.length_append, pow_add, List.length_map]
    constructor <;> ring

/-- **The Keccak constraint relation at `t`**: where it holds, the batched constraints at `t` plus
`Q_W(t) w_{r_W}(t)` vanish. -/
theorem crOfK_holds (S : Shape) (c1 : Stk) (parts : List TablePart) (pw : List E) (gamma t cv : E)
    (w : List E) (ev : Column → List E → E) (hlen : tablesKeccak.length ≤ parts.length)
    (hok : ∀ x ∈ tablesKeccak.zip parts, CrTableOkK S c1 t w ev x.1 x.2)
    (hmem : ∀ k < 3, ev (.memory k) (w.take S.logMemory) = (c1PK S c1 (.memory k)).eval t)
    (hlift : vanishingRatio w 1 S.constraintVars = (liftP 1 S.constraintVars).eval t)
    (hh : RelHolds ev (crOfK S parts pw gamma t cv w).1) :
    powComb ((constraintsPK S c1 pw).map fun mw ↦ (mw.1 * mw.2).eval t) gamma +
      cv * w.getD S.constraintVars 0 = 0 := by
  unfold RelHolds crOfK at hh
  dsimp only at hh
  obtain ⟨f1, f2⟩ := crFoldK_spec S c1 gamma t w ev (tablesKeccak.zip parts) (0, #[], 1, 0) hok
  generalize (tablesKeccak.zip parts).foldl (crStepK S gamma t w) (0, #[], 1, 0) = s at hh f1 f2
  obtain ⟨l1, -⟩ := lineFold_spec S gamma t w ev ((linesOf pw).zip (List.range 3)) (s.1, s.2.1, s.2.2.1)
  generalize ((linesOf pw).zip (List.range 3)).foldl (lineStep S gamma t w) (s.1, s.2.1, s.2.2.1) = s'
    at hh l1
  change termsVal ev s'.2.1 + _ = 0 at hh
  have hl : ((linesOf pw).zip (List.range 3)).map (fun x ↦ vanishingRatio w 1 S.constraintVars *
      (ev (.memory x.2) (w.take S.logMemory) + x.1.1 + t * (x.1.1 + x.1.2))) =
      (linesPK S c1 pw).map fun mw ↦ (mw.1 * mw.2).eval t := by
    unfold linesPK
    rw [List.map_map]
    refine List.map_congr_left fun x hx ↦ ?_
    have hx3 : x.2 < 3 := List.mem_range.mp (List.of_mem_zip hx).2
    simp only [Function.comp_apply, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X, hlift, hmem x.2 hx3]
  rw [hl] at l1
  dsimp only at f1 f2
  rw [termsVal_empty] at f1
  simp only [add_zero, zero_add, one_mul] at f1 f2
  unfold constraintsPK
  rw [List.map_append, powComb_append, List.map_flatMap,
    ← flatMap_zip_fst (fun tab ↦ (tableConstraintsPK S c1 tab).map fun mw ↦ (mw.1 * mw.2).eval t) tablesKeccak
      parts hlen]
  rw [← f1, ← f2]
  dsimp only at l1
  linear_combination hh - l1

/-! ## The terms -/

theorem copyFoldK_terms (o r : ℕ) (columns : List String) (w y : List E) (lift gamma : E) :
    ∀ (l : List ℕ) (s : E × Array Term × E), ∃ X,
      (l.foldl (copyStepK o r columns w y lift gamma) s).2.1.toList = s.2.1.toList ++ X ∧ ∀ tm ∈ X, CrPt w y tm
  | [], s => ⟨[], by simp, by simp⟩
  | c :: l, s => by
    rw [List.foldl_cons]
    obtain ⟨X, hX, hP⟩ := copyFoldK_terms o r columns w y lift gamma l (copyStepK o r columns w y lift gamma s c)
    rw [hX]
    unfold copyStepK
    split
    · rename_i _ slot _
      refine ⟨[term (.table o c) (w.take r) (s.2.2 * lift), term (.qflockSlot slot) y (s.2.2 * lift)] ++ X,
        by simp, fun tm htm ↦ ?_⟩
      simp only [List.cons_append, List.nil_append, List.mem_cons] at htm
      rcases htm with rfl | rfl | htm
      · exact ⟨rfl, rfl, Or.inl ⟨r, rfl⟩⟩
      · exact ⟨rfl, rfl, Or.inr rfl⟩
      · exact hP tm htm
    · exact ⟨X, rfl, hP⟩

theorem copyFoldK_sub (o r : ℕ) (columns : List String) (w y : List E) (lift gamma : E)
    (l : List ℕ) (s : E × Array Term × E) (tm : Term) (h : tm ∈ s.2.1.toList) :
    tm ∈ (l.foldl (copyStepK o r columns w y lift gamma) s).2.1.toList := by
  obtain ⟨X, hX, -⟩ := copyFoldK_terms o r columns w y lift gamma l s
  rw [hX]
  exact List.mem_append_left _ h

theorem copyFoldK_slot (o r : ℕ) (columns : List String) (w y : List E) (lift gamma : E) :
    ∀ (l : List ℕ) (s : E × Array Term × E) (c slot : ℕ), c ∈ l → keccakSlot (columns.getD c "") = some slot →
      ∃ tm ∈ (l.foldl (copyStepK o r columns w y lift gamma) s).2.1.toList, tm.point = y
  | [], _, _, _, h, _ => by simp at h
  | c' :: l, s, c, slot, h, hs => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · refine ⟨term (.qflockSlot slot) y (s.2.2 * lift), copyFoldK_sub o r columns w y lift gamma l _ _ ?_, rfl⟩
      unfold copyStepK
      rw [hs]
      simp
    · exact copyFoldK_slot o r columns w y lift gamma l _ c slot h' hs

theorem crStepK_terms (S : Shape) (gamma t : E) (w : List E) (s : E × Array Term × E × ℕ)
    (x : Table × TablePart) : ∃ X, (crStepK S gamma t w s x).2.1.toList = s.2.1.toList ++ X ∧
      ∀ tm ∈ X, CrPt w (coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0))) tm := by
  unfold crStepK
  dsimp only
  by_cases hj : x.1.opcode = opJump
  · have hb : ¬ x.1.opcode = opBlake2s := by rw [hj]; decide
    simp only [ite_eq_left hj, ite_eq_right hb, Array.toList_push, List.append_assoc]
    refine ⟨_, rfl, fun tm htm ↦ ?_⟩
    simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at htm
    rcases htm with rfl | rfl <;> exact ⟨rfl, rfl, Or.inl ⟨_, rfl⟩⟩
  · by_cases hb : x.1.opcode = opBlake2s
    · simp only [ite_eq_right hj, ite_eq_left hb]
      obtain ⟨X, hX, hP⟩ := copyFoldK_terms _ _ _ _ _ _ _ _ _
      rw [hX, Array.toList_push, List.append_assoc]
      refine ⟨_, rfl, fun tm htm ↦ ?_⟩
      simp only [List.singleton_append, List.mem_cons] at htm
      rcases htm with rfl | htm
      · exact ⟨rfl, rfl, Or.inl ⟨_, rfl⟩⟩
      · have := hP tm htm
        rwa [hb] at this
    · simp only [ite_eq_right hj, ite_eq_right hb, Array.toList_push]
      refine ⟨_, rfl, fun tm htm ↦ ?_⟩
      simp only [List.mem_singleton] at htm
      subst htm
      exact ⟨rfl, rfl, Or.inl ⟨_, rfl⟩⟩

theorem crStepK_sub (S : Shape) (gamma t : E) (w : List E) (s : E × Array Term × E × ℕ)
    (x : Table × TablePart) (tm : Term) (h : tm ∈ s.2.1.toList) : tm ∈ (crStepK S gamma t w s x).2.1.toList := by
  obtain ⟨X, hX, -⟩ := crStepK_terms S gamma t w s x
  rw [hX]
  exact List.mem_append_left _ h

theorem crFoldK_terms (S : Shape) (gamma t : E) (w : List E) : ∀ (L : List (Table × TablePart))
    (s : E × Array Term × E × ℕ), ∀ tm ∈ (L.foldl (crStepK S gamma t w) s).2.1.toList,
      tm ∈ s.2.1.toList ∨ CrPt w (coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0))) tm
  | [], _, _, h => Or.inl h
  | x :: L, s, tm, h => by
    rw [List.foldl_cons] at h
    rcases crFoldK_terms S gamma t w L _ tm h with h1 | h1
    · obtain ⟨X, hX, hP⟩ := crStepK_terms S gamma t w s x
      rw [hX, List.mem_append] at h1
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (hP tm h1)
    · exact Or.inr h1

theorem crFoldK_sub (S : Shape) (gamma t : E) (w : List E) : ∀ (L : List (Table × TablePart))
    (s : E × Array Term × E × ℕ), ∀ tm ∈ s.2.1.toList, tm ∈ (L.foldl (crStepK S gamma t w) s).2.1.toList
  | [], _, _, h => h
  | x :: L, s, tm, h => by
    rw [List.foldl_cons]
    exact crFoldK_sub S gamma t w L _ tm (crStepK_sub S gamma t w s x tm h)

/-- **The Keccak constraint relation's terms**: untwisted, on `C1`, at prefixes of the digits or at `y`. -/
theorem crOfK_terms (S : Shape) (parts : List TablePart) (pw : List E) (gamma t cv : E) (w : List E) :
    ∀ tm ∈ (crOfK S parts pw gamma t cv w).1.terms,
      CrPt w (coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0))) tm := by
  intro tm htm
  unfold crOfK at htm
  dsimp only at htm
  rcases lineFold_terms S gamma t w _ _ _ tm htm with h | h
  · rcases crFoldK_terms S gamma t w _ _ tm h with h' | h'
    · simp at h'
    · exact h'
  · exact h

theorem tablesKeccak_getD5 : (tablesKeccak.getD 5 default).opcode = opBlake2s := rfl

/-- **The Keccak constraint relation has a term at `y`** where a `SHA3` column has a lane slot. -/
theorem crOfK_slot (S : Shape) (parts : List TablePart) (pw : List E) (gamma t cv : E) (w : List E)
    (hlen : tablesKeccak.length ≤ parts.length) (c slot : ℕ) (hc : c < (tablesKeccak.getD 5 default).width)
    (hs : keccakSlot ((tablesKeccak.getD 5 default).columns.getD c "") = some slot) :
    ∃ tm ∈ (crOfK S parts pw gamma t cv w).1.terms,
      tm.point = coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0)) := by
  have hx : (tablesKeccak.getD 5 default, parts.getD 5 default) ∈ tablesKeccak.zip parts := by
    have h5 : 5 < (tablesKeccak.zip parts).length := by
      rw [List.length_zip]; have : tablesKeccak.length = 6 := rfl; omega
    have := List.getElem_mem h5
    rwa [List.getElem_zip, ← List.getD_eq_getElem _ default, ← List.getD_eq_getElem _ default] at this
  obtain ⟨L1, L2, hL⟩ := List.append_of_mem hx
  have key : ∀ s : E × Array Term × E × ℕ, ∃ tm ∈ (crStepK S gamma t w s
      (tablesKeccak.getD 5 default, parts.getD 5 default)).2.1.toList,
      tm.point = coordinatesAt t (coordinateFunctionals (S.heights.getD opBlake2s 0)) := by
    intro s
    have h1 : ¬ (tablesKeccak.getD 5 default).opcode = opJump := by decide
    unfold crStepK
    dsimp only
    simp only [ite_eq_right h1, ite_eq_left tablesKeccak_getD5]
    exact copyFoldK_slot _ _ _ _ _ _ _ _ _ c slot (List.mem_range.mpr hc) hs
  unfold crOfK
  dsimp only
  rw [hL, List.foldl_append, List.foldl_cons]
  obtain ⟨tm, htm, hp⟩ := key (L1.foldl (crStepK S gamma t w) (0, #[], 1, 0))
  exact ⟨tm, lineFold_sub S gamma t w _ _ tm (crFoldK_sub S gamma t w L2 _ tm htm), hp⟩

/-! ## The degree -/

theorem crFoldK_deg (S : Shape) (gamma t : E) (w : List E) : ∀ (L : List (Table × TablePart))
    (s : E × Array Term × E × ℕ), (L.foldl (crStepK S gamma t w) s).2.2.2 =
      (L.map Prod.fst).foldl (UniSound.cdStep S) s.2.2.2
  | [], _ => rfl
  | x :: L, s => by
    rw [List.foldl_cons, crFoldK_deg S gamma t w L, List.map_cons, List.foldl_cons]
    congr 1
    unfold crStepK UniSound.cdStep
    dsimp only
    by_cases hj : x.1.opcode = opJump
    · have hb : ¬ x.1.opcode = opBlake2s := by rw [hj]; decide
      simp only [ite_eq_left hj, ite_eq_right hb]
    · by_cases hb : x.1.opcode = opBlake2s
      · simp only [ite_eq_right hj, ite_eq_left hb]
      · simp only [ite_eq_right hj, ite_eq_right hb]

/-- **The Keccak constraint relation's degree is the shape's** (`constraintDegreeK`), with a part per table. -/
theorem crOfK_deg (S : Shape) (parts : List TablePart) (pw : List E) (gamma t cv : E) (w : List E)
    (hlen : tablesKeccak.length ≤ parts.length) :
    (crOfK S parts pw gamma t cv w).2 = UniKeccak.Shape.constraintDegreeK S := by
  unfold crOfK UniKeccak.Shape.constraintDegreeK
  dsimp only
  rw [crFoldK_deg, List.map_fst_zip hlen]
  rfl

end UniKeccakSound.IdsEval
