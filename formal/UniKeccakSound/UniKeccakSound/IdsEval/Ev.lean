-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proofs are `UniSound/Ids/Eval.lean`'s (`evOf`,
-- `holds_of_diffs`, `ev_colPoly`, `ev_slot`, `treeP_eval`, `rootP_eval`, `c1_points`, `y_self`, `part_spec`) on the
-- Keccak identity model (`UniKeccakSound/Ids/Model.lean`).
import UniKeccakSound.IdsEval.Constraint
import UniKeccakSound.IdsEval.Weights
import UniKeccakSound.IdsEval.Facts

/-!
# The Keccak differences read each column at its merged point

For the Keccak identity model (`diffsK`, on `relsAtK`) at a statement, round `0`'s challenges `ch` (at least four),
Flock's transcript, `t` and the values:

* **`evOfK`**: what the differences read a column at a point as (`termWK` at its merged point, against the
  zero-extended stack); where they vanish, every untwisted relation on one commitment holds under `evOfK`
  (`holds_of_diffsK`, `HoldAllK`);
* **a term's reading is its column's polynomial at `t`** (`ev_c1K`, `ev_c2K`, `ev_setupK`; `q_flock`'s slot at `y(t)`
  with `11` slot bits, `ev_slotK`, where `y(t)` is not merged: `y_selfK`, off `Z_bad`'s roots);
* the tree's and the root's identities at `t` (`treePK_eval`, `rootPK_eval`); each Keccak table's part at `t`
  (`part_specK`).
-/

namespace UniKeccakSound.IdsEval

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.Eval UniKeccak UniKeccakSound.Ids Finset
  Polynomial

section Ctx

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant} (Fl : KFlockSound F κ v)
  (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E) (vals : List E)

/-- The relations' input. -/
abbrev inpK : RelInput := relInputK D s ch (Fl.prog.out fd []) t vals

/-- The relations at `t`, read a value at a time. -/
abbrev relsK : List Relation := relsOfK (inpK D Fl s ch fd t vals)

/-- **What the Keccak differences read a column at a point as**: the term's weight at its merged point on its
commitment's stack, against the zero-extended stack. -/
noncomputable def evOfK (col : Column) (p : List E) : E :=
  ∑ u ∈ range (2 ^ batchVarsK D.shape), termWK (layoutOfK D.shape col.commitment) (ringMapAtK Fl fd)
    (batchVarsK D.shape) col (mergedPoint (mine (relsK D Fl s ch fd t vals) col.commitment) p) 0 u *
      stE (stackForK D c1 c2 col.commitment) (layoutOfK D.shape col.commitment).vars u

/-- **The differences, all zero, make every untwisted relation on one commitment hold** under `evOfK`. -/
theorem holds_of_diffsK (hch : 4 ≤ ch.length) (hg : CountsFit D.shape s.2 ∧ FlockGoodK κ (Fl.prog.out fd []))
    (hd : ∀ d ∈ diffsK D Fl s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) (r : Relation)
    (hr : r ∈ relsK D Fl s ch fd t vals) (c : Commitment)
    (hterms : ∀ tm ∈ r.terms, tm.twist = 0 ∧ tm.column.commitment = c) :
    RelHolds (evOfK D Fl s c1 ch fd c2 t vals) r := by
  have hc : ∀ tm ∈ r.terms, tm.column.commitment = r.commitment := by
    intro tm htm
    unfold Relation.commitment
    rcases hr' : r.terms with _ | ⟨tm0, rest⟩
    · rw [hr'] at htm; simp at htm
    · rw [(hterms tm htm).2]
      exact (hterms tm0 (by rw [hr']; exact List.mem_cons_self ..)).2.symm
  unfold diffsK at hd
  rw [ite_eq_left hg, relsAtK_eq D Fl s ch fd t vals hch] at hd
  have hcm : r.commitment ∈ commitments := by cases r.commitment <;> simp [commitments]
  have h0 := hd _ (List.mem_map.mpr ⟨r.commitment, hcm, rfl⟩) _
    (List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simp⟩, rfl⟩)
  unfold relDiffK at h0
  unfold RelHolds
  rw [← h0]
  refine congrArg (· + r.value) (congrArg List.sum (List.map_congr_left fun tm htm ↦ ?_))
  rw [(hterms tm htm).1]
  unfold evOfK
  rw [hc tm htm]

/-- **A column's value at a point of its commitment's relations** is its polynomial at `t`. -/
theorem ev_colPolyK (col : Column) (p : List E) (P : ℕ → Polynomial E) (hcol : ∀ j, col ≠ .qflockSlot j)
    (hp : ∃ r ∈ relsK D Fl s ch fd t vals, r.commitment = col.commitment ∧ ∃ tm ∈ r.terms, tm.point = p)
    (hb : ∀ b ∈ (layoutOfK D.shape col.commitment).limbs col, b.2.1 ≤ p.length ∧ b.2.1 ≤ batchVarsK D.shape)
    (hP : ∀ b ∈ (layoutOfK D.shape col.commitment).limbs col, ∀ l < b.2.1, (P l).eval t = p.getD l 0) :
    evOfK D Fl s c1 ch fd c2 t vals col p =
      (colPoly (layoutOfK D.shape col.commitment) (batchVarsK D.shape) (stackForK D c1 c2 col.commitment) col
        P).eval t := by
  obtain ⟨r, hr, hrc, tm, htm, hpt⟩ := hp
  have hpre := (mergedPrefix (mine (relsK D Fl s ch fd t vals) col.commitment) p
    ⟨r, List.mem_filter.mpr ⟨hr, by simp [hrc]⟩, tm, htm, hpt⟩).1
  exact inner_colPolyK _ _ _ _ col p _ t P hcol hpre hb hP

/-- **`q_flock`'s slot at `y`**, where no longer `C1` point extends `y`: the slot's polynomial at `t` (`11` slot
bits). -/
theorem ev_slotK (j : ℕ) (y : List E) (Y : ℕ → Polynomial E)
    (hp : ∃ r ∈ relsK D Fl s ch fd t vals, r.commitment = .c1 ∧ ∃ tm ∈ r.terms, tm.point = y)
    (hself : ∀ r ∈ relsK D Fl s ch fd t vals, r.commitment = .c1 → ∀ tm ∈ r.terms,
      y.length < tm.point.length → tm.point.take y.length ≠ y)
    (hb : ∀ b ∈ (layoutOfK D.shape .c1).limbs .qflock,
      b.2.1 = qflockRowBits + y.length ∧ b.2.1 ≤ batchVarsK D.shape)
    (hq : qvOf (layoutOfK D.shape .c1) = qflockRowBits + y.length)
    (hY : ∀ m < y.length, (Y m).eval t = y.getD m 0) :
    evOfK D Fl s c1 ch fd c2 t vals (.qflockSlot j) y =
      (colPoly (layoutOfK D.shape .c1) (batchVarsK D.shape) c1 .qflock fun l ↦
        if l < qflockRowBits then Polynomial.C (bitE j l) else Y (l - qflockRowBits)).eval t := by
  obtain ⟨r, hr, hrc, tm, htm, hpt⟩ := hp
  have hm := mergedSelf (mine (relsK D Fl s ch fd t vals) .c1) y
    ⟨r, List.mem_filter.mpr ⟨hr, by simp [hrc]⟩, tm, htm, hpt⟩
    (fun r' hr' tm' htm' hlt ↦ hself r' (List.mem_filter.mp hr').1 (by simpa using (List.mem_filter.mp hr').2)
      tm' htm' hlt)
  unfold evOfK
  show ∑ u ∈ range _, termWK (layoutOfK D.shape .c1) _ _ _ (mergedPoint (mine _ .c1) y) 0 u * stE c1 _ u = _
  rw [hm]
  exact inner_slotK _ _ _ c1 j y t Y hb hq hY

/-- **Every relation holds** that is untwisted on one commitment. -/
def HoldAllK : Prop :=
  ∀ r ∈ relsK D Fl s ch fd t vals, ∀ c, (∀ tm ∈ r.terms, tm.twist = 0 ∧ tm.column.commitment = c) →
    RelHolds (evOfK D Fl s c1 ch fd c2 t vals) r

/-- A point some relation on a commitment reads a term at. -/
def IsPtK (c : Commitment) (p : List E) : Prop :=
  ∃ r ∈ relsK D Fl s ch fd t vals, r.commitment = c ∧ ∃ tm ∈ r.terms, tm.point = p

theorem wK_length : (inpK D Fl s ch fd t vals).w.length = nDigits D.shape :=
  digits_length t _ (by omega)

theorem wK_getD (l : ℕ) (hl : l < nDigits D.shape) :
    (inpK D Fl s ch fd t vals).w.getD l 0 = (digitP l).eval t :=
  digits_getD t _ l hl

theorem wtakeK_length (k : ℕ) (hk : k ≤ nDigits D.shape) :
    ((inpK D Fl s ch fd t vals).w.take k).length = k := by
  rw [List.length_take, wK_length]; omega

theorem wtakeK_getD (k : ℕ) (hk : k ≤ nDigits D.shape) (l : ℕ) (hl : l < k) :
    ((inpK D Fl s ch fd t vals).w.take k).getD l 0 = (digitP l).eval t := by
  rw [take_getD _ hl, wK_getD D Fl s ch fd t vals l (by omega)]

/-- **A `C1` column at a prefix of the digits** (not a slot): its polynomial at `t`. -/
theorem ev_c1K (col : Column) (hcol : col.commitment = .c1) (hns : ∀ j, col ≠ .qflockSlot j) (k : ℕ)
    (hk : k ≤ nDigits D.shape) (hv : c1VarsK D.shape col ≤ k)
    (hp : IsPtK D Fl s ch fd t vals .c1 ((inpK D Fl s ch fd t vals).w.take k)) :
    evOfK D Fl s c1 ch fd c2 t vals col ((inpK D Fl s ch fd t vals).w.take k) = (c1PK D.shape c1 col).eval t := by
  have h := ev_colPolyK D Fl s c1 ch fd c2 t vals col _ digitP hns (by rw [hcol]; exact hp)
    (by
      rw [hcol]
      intro b hb
      obtain ⟨h1, h2⟩ := c1_limbsK D.shape col b hb
      rw [wtakeK_length D Fl s ch fd t vals k hk]
      omega)
    (by
      rw [hcol]
      intro b hb l hl
      obtain ⟨h1, -⟩ := c1_limbsK D.shape col b hb
      rw [wtakeK_getD D Fl s ch fd t vals k hk l (by omega)])
  rw [h]
  simp only [hcol]
  rfl

/-- **A `C2` column at a point** whose values at `t` are a polynomial point's: its polynomial at `t`. -/
theorem ev_c2K (col : Column) (hcol : col.commitment = .c2) (p : List E) (P : ℕ → Polynomial E)
    (hp : IsPtK D Fl s ch fd t vals .c2 p) (hlen : c2VarsK D.shape col ≤ p.length)
    (hP : ∀ l < c2VarsK D.shape col, (P l).eval t = p.getD l 0) :
    evOfK D Fl s c1 ch fd c2 t vals col p = (c2PK D.shape c2 col P).eval t := by
  have hns : ∀ j, col ≠ .qflockSlot j := by
    intro j hj
    rw [hj] at hcol
    simp [Column.commitment] at hcol
  have h := ev_colPolyK D Fl s c1 ch fd c2 t vals col p P hns (by rw [hcol]; exact hp)
    (by
      rw [hcol]
      intro b hb
      obtain ⟨h1, h2⟩ := c2_limbsK D.shape col b hb
      omega)
    (by
      rw [hcol]
      intro b hb l hl
      obtain ⟨h1, -⟩ := c2_limbsK D.shape col b hb
      exact hP l (by omega))
  rw [h]
  simp only [hcol]
  rfl

/-- **A setup column at a point** whose values at `t` are a polynomial point's. -/
theorem ev_setupK (col : Column) (hcol : col.commitment = .setup) (p : List E) (P : ℕ → Polynomial E)
    (hp : IsPtK D Fl s ch fd t vals .setup p)
    (hlen : ∀ b ∈ (layoutOfK D.shape .setup).limbs col, b.2.1 ≤ p.length)
    (hP : ∀ b ∈ (layoutOfK D.shape .setup).limbs col, ∀ l < b.2.1, (P l).eval t = p.getD l 0) :
    evOfK D Fl s c1 ch fd c2 t vals col p = (suPK D.shape (setupStkK D) col P).eval t := by
  have hns : ∀ j, col ≠ .qflockSlot j := by
    intro j hj
    rw [hj] at hcol
    simp [Column.commitment] at hcol
  have h := ev_colPolyK D Fl s c1 ch fd c2 t vals col p P hns (by rw [hcol]; exact hp)
    (by
      rw [hcol]
      intro b hb
      exact ⟨hlen b hb, (setup_limbsK D.shape col b hb).2.2⟩)
    (by rw [hcol]; exact hP)
  rw [h]
  simp only [hcol]
  rfl

theorem mem_rels_tpK {r : Relation} (h : r ∈ (tpK (inpK D Fl s ch fd t vals)).2.1) :
    r ∈ relsK D Fl s ch fd t vals := by
  unfold relsK relsOfK; simp [h]

theorem mem_rels_memK {r : Relation} (h : r ∈ memRelsK (inpK D Fl s ch fd t vals)) :
    r ∈ relsK D Fl s ch fd t vals := by
  unfold relsK relsOfK; simp [h]

theorem mem_rels_bcK {r : Relation} (h : r ∈ bcRelsK (inpK D Fl s ch fd t vals)) :
    r ∈ relsK D Fl s ch fd t vals := by
  unfold relsK relsOfK; simp [h]

theorem mem_rels_constraintK : (constraintK (inpK D Fl s ch fd t vals)).1 ∈ relsK D Fl s ch fd t vals := by
  unfold relsK relsOfK; simp

theorem mem_rels_heapK {r : Relation} (h : r ∈ (heapK (inpK D Fl s ch fd t vals)).1) :
    r ∈ relsK D Fl s ch fd t vals := by
  unfold relsK relsOfK; simp [h]

theorem heapK_fst : (heapK (inpK D Fl s ch fd t vals)).1 =
    [Relation.equal .heap ((inpK D Fl s ch fd t vals).w.take D.shape.heap.h) (hvK (inpK D Fl s ch fd t vals)),
      ⟨[term .heap (((inpK D Fl s ch fd t vals).w.drop 1).take D.shape.heap.h)
          ((inpK D Fl s ch fd t vals).w.getD 1 0),
        term .heap (((inpK D Fl s ch fd t vals).w.take D.shape.heap.h).modify 0 (· + 1))
          ((inpK D Fl s ch fd t vals).w.getD 1 0 * hvK (inpK D Fl s ch fd t vals)),
        term (.treeQuotient 0) ((inpK D Fl s ch fd t vals).w.take D.shape.heap.h)
          ((inpK D Fl s ch fd t vals).w.getD D.shape.heap.h 0),
        term (.treeQuotient 1) [] ((inpK D Fl s ch fd t vals).w.getD D.shape.heap.h 0 *
          (inpK D Fl s ch fd t vals).w.getD D.shape.heap.h 0)], 0⟩,
      ⟨[term .heap ((List.range D.shape.heap.h).map fun l ↦ if l = 0 then (1 : E) else 0)
        (rootInit (inpK D Fl s ch fd t vals).weights (inpK D Fl s ch fd t vals).beta)],
        rootFin D.shape (inpK D Fl s ch fd t vals).weights (inpK D Fl s ch fd t vals).beta⟩] ++
    (D.shape.heap.blocks.zip (List.range D.shape.heap.blocks.length)).map
      (blockRel D.shape (inpK D Fl s ch fd t vals).active (tpK (inpK D Fl s ch fd t vals)).1
        (mpullK (inpK D Fl s ch fd t vals)) (mpushK (inpK D Fl s ch fd t vals))
        (bpullK (inpK D Fl s ch fd t vals)) (bpushK (inpK D Fl s ch fd t vals))
        (inpK D Fl s ch fd t vals).w) ++
    [⟨quotientTerms .constraintQuotient (chunks ((constraintK (inpK D Fl s ch fd t vals)).2 + 1))
      (inpK D Fl s ch fd t vals).w 1, cvK (inpK D Fl s ch fd t vals)⟩] :=
  heapRelations_fst _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The tree's identity at `t`.** -/
theorem treePK_eval (hold : HoldAllK D Fl s c1 ch fd c2 t vals) : (treePK D.shape c2).eval t = 0 := by
  have hh := heapK_fst D Fl s ch fd t vals
  have hN := h_lt_nDigitsK D.shape
  have mT := mem_rels_heapK D Fl s ch fd t vals (by
    rw [hh]; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)))
  have mTree := mem_rels_heapK D Fl s ch fd t vals (by
    rw [hh]; exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have hRT := hold _ mT .c2 (by simp [Relation.equal, term, Column.commitment])
  have hRtree := hold _ mTree .c2 (by simp [term, Column.commitment])
  have hT := holds_equal hRT
  unfold RelHolds at hRtree
  simp only [term, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hRtree
  have hpT : IsPtK D Fl s ch fd t vals .c2 ((inpK D Fl s ch fd t vals).w.take D.shape.heap.h) :=
    ⟨_, mT, rfl, ⟨term .heap _ 1, List.mem_singleton_self _, rfl⟩⟩
  have hmemTree : ∀ tm ∈ ([term .heap (((inpK D Fl s ch fd t vals).w.drop 1).take D.shape.heap.h)
          ((inpK D Fl s ch fd t vals).w.getD 1 0),
        term .heap (((inpK D Fl s ch fd t vals).w.take D.shape.heap.h).modify 0 (· + 1))
          ((inpK D Fl s ch fd t vals).w.getD 1 0 * hvK (inpK D Fl s ch fd t vals)),
        term (.treeQuotient 0) ((inpK D Fl s ch fd t vals).w.take D.shape.heap.h)
          ((inpK D Fl s ch fd t vals).w.getD D.shape.heap.h 0),
        term (.treeQuotient 1) [] ((inpK D Fl s ch fd t vals).w.getD D.shape.heap.h 0 *
          (inpK D Fl s ch fd t vals).w.getD D.shape.heap.h 0)] : List Term),
      IsPtK D Fl s ch fd t vals .c2 tm.point := by
    intro tm htm
    exact ⟨_, mTree, rfl, tm, htm, rfl⟩
  have eT := ev_c2K D Fl s c1 ch fd c2 t vals .heap rfl _ digitP hpT
    (by rw [wtakeK_length D Fl s ch fd t vals _ (by omega)]; rfl)
    (fun l hl ↦ by
      change l < D.shape.heap.h at hl
      exact (wtakeK_getD D Fl s ch fd t vals _ (by omega) l hl).symm)
  have eS := ev_c2K D Fl s c1 ch fd c2 t vals .heap rfl
    (((inpK D Fl s ch fd t vals).w.drop 1).take D.shape.heap.h) (fun l ↦ digitP (l + 1))
    (hmemTree _ (List.mem_cons_self ..))
    (by
      show D.shape.heap.h ≤ _
      simp only [List.length_take, List.length_drop, wK_length]; omega)
    (fun l hl ↦ by
      change l < D.shape.heap.h at hl
      rw [take_getD _ hl, List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
        add_comm, wK_getD D Fl s ch fd t vals _ (by omega)])
  have eN := ev_c2K D Fl s c1 ch fd c2 t vals .heap rfl
    (((inpK D Fl s ch fd t vals).w.take D.shape.heap.h).modify 0 (· + 1))
    (fun l ↦ if l = 0 then digitP 0 + 1 else digitP l)
    (hmemTree _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (by
      show D.shape.heap.h ≤ _
      rw [List.length_modify, wtakeK_length D Fl s ch fd t vals _ (by omega)])
    (fun l hl ↦ by
      change l < D.shape.heap.h at hl
      have hx : ((inpK D Fl s ch fd t vals).w.take D.shape.heap.h)[l]? = some ((digitP l).eval t) := by
        rw [List.getElem?_eq_getElem (by rw [wtakeK_length D Fl s ch fd t vals _ (by omega)]; exact hl),
          ← List.getD_eq_getElem _ 0, wtakeK_getD D Fl s ch fd t vals _ (by omega) l hl]
      rw [List.getD_eq_getElem?_getD, List.getElem?_modify, hx]
      by_cases h0 : l = 0
      · subst h0
        simp
      · simp [h0, Ne.symm h0])
  have eQ0 := ev_c2K D Fl s c1 ch fd c2 t vals (.treeQuotient 0) rfl _ digitP hpT
    (by rw [wtakeK_length D Fl s ch fd t vals _ (by omega)]; rfl)
    (fun l hl ↦ by
      change l < D.shape.heap.h at hl
      exact (wtakeK_getD D Fl s ch fd t vals _ (by omega) l hl).symm)
  have eQ1 := ev_c2K D Fl s c1 ch fd c2 t vals (.treeQuotient 1) rfl [] digitP
    (hmemTree _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))) (by simp [c2VarsK]) (fun l hl ↦ by simp [c2VarsK] at hl)
  have w1 := wK_getD D Fl s ch fd t vals 1 (by omega)
  have wh := wK_getD D Fl s ch fd t vals D.shape.heap.h (by omega)
  rw [eT] at hT
  rw [eS, eN, eQ0, eQ1, ← hT, w1, wh] at hRtree
  unfold treePK
  simp only [Polynomial.eval_add, Polynomial.eval_mul]
  linear_combination hRtree

/-- **The root's identity at `t`.** -/
theorem rootPK_eval (hold : HoldAllK D Fl s c1 ch fd c2 t vals) :
    (rootPK D.shape c2 (eqKernel (alphasOf ch)) (betaOf ch)).eval t = 0 := by
  have hh := heapK_fst D Fl s ch fd t vals
  have mR := mem_rels_heapK D Fl s ch fd t vals (by
    rw [hh]; exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
  have hR := hold _ mR .c2 (by simp [term, Column.commitment])
  unfold RelHolds at hR
  simp only [term, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hR
  have e1 := ev_c2K D Fl s c1 ch fd c2 t vals .heap rfl
    ((List.range D.shape.heap.h).map fun l ↦ if l = 0 then (1 : E) else 0)
    (fun l ↦ if l = 0 then 1 else 0) ⟨_, mR, rfl, _, List.mem_singleton_self _, rfl⟩
    (by simp [c2VarsK])
    (fun l hl ↦ by
      change l < D.shape.heap.h at hl
      rw [getD_map_range _ hl]
      split_ifs <;> simp)
  rw [e1] at hR
  unfold rootPK
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  exact hR

/-- `y(t)`, `SHA3`'s coordinates of `t`. -/
def yOfK : List E := coordinatesAt t (coordinateFunctionals (D.shape.heights.getD opBlake2s 0))

/-- **Every Keccak `C1` point**: a prefix of the digits, `y(t)`, or Flock's point. -/
theorem c1_pointsK : ∀ r ∈ relsK D Fl s ch fd t vals, r.commitment = .c1 → ∀ tm ∈ r.terms,
    (∃ k, tm.point = (inpK D Fl s ch fd t vals).w.take k) ∨ tm.point = yOfK D t ∨
      tm.point = (inpK D Fl s ch fd t vals).flockPoint := by
  intro r hr hc tm htm
  unfold relsK relsOfK at hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with ((((hr | hr) | hr) | rfl) | hr) | hr
  · obtain ⟨tab, -, v', hv⟩ := tablesPart_rels _ _ _ _ _ _ r hr
    exact Or.inl ⟨_, (tablePartOf_terms tab _ _ _ _ v' r hv tm htm).2.1⟩
  · simp only [memRelsK, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp only [Relation.equal, term, List.mem_singleton] at htm; subst htm; exact Or.inl ⟨_, rfl⟩
    · simp only [Relation.equal, term, List.mem_singleton] at htm; subst htm; exact Or.inl ⟨_, rfl⟩
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp htm
      exact Or.inl ⟨_, rfl⟩
  · simp only [bcRelsK, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Relation.equal, term, List.mem_singleton] at htm; subst htm; exact Or.inl ⟨_, rfl⟩
    · simp [Relation.equal, Relation.commitment, term, Column.commitment] at hc
  · have := crOfK_terms _ _ _ _ _ _ _ tm (by rw [← constraintRelationK_eq]; exact htm)
    rcases this.2.2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have := terms_nil_of (fun tm' htm' ↦ (heap_terms _ _ _ _ _ _ _ _ _ _ _ _ _ r hr tm' htm').1) hc
    rw [this] at htm
    simp at htm
  · unfold RelInput.ringRels at hr
    split at hr
    · simp only [List.mem_singleton] at hr
      subst hr
      simp only [List.mem_singleton] at htm
      subst htm
      exact Or.inr (Or.inr rfl)
    · simp at hr

/-- **No longer `C1` point extends `y(t)`** where `Z_bad(t) ≠ 0`. -/
theorem y_selfK (h2 : 1 ≤ D.shape.heights.getD opBlake2s 0)
    (hz : (zBad D.shape ((Fl.prog.out fd []).1.getD 0 0)).eval t ≠ 0) :
    ∀ r ∈ relsK D Fl s ch fd t vals, r.commitment = .c1 → ∀ tm ∈ r.terms,
      (yOfK D t).length < tm.point.length → tm.point.take (yOfK D t).length ≠ yOfK D t := by
  have hlen : (yOfK D t).length = D.shape.heights.getD opBlake2s 0 := by
    rw [yOfK, coordinatesAt_length, coordinateFunctionals_size]
  have hy0 : (yOfK D t).getD 0 0 =
      (yP (coordinateFunctionals (D.shape.heights.getD opBlake2s 0)) 0).eval t := by
    rw [yOfK, coordinatesAt_getD _ _ _ (by rw [coordinateFunctionals_size]; omega)]
  unfold zBad at hz
  rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    ← hy0] at hz
  have hne1 : (yOfK D t).getD 0 0 ≠ t := fun h ↦ hz (by rw [h, CharTwo.add_self_eq_zero, zero_mul])
  have hne2 : (yOfK D t).getD 0 0 ≠ (Fl.prog.out fd []).1.getD 0 0 :=
    fun h ↦ hz (by rw [h, CharTwo.add_self_eq_zero, mul_zero])
  intro r hr hc tm htm hlt heq
  have h0 : (tm.point.take (yOfK D t).length).getD 0 0 = (yOfK D t).getD 0 0 := by rw [heq]
  rw [take_getD _ (by omega)] at h0
  rcases c1_pointsK D Fl s ch fd t vals r hr hc tm htm with ⟨k, hk⟩ | hk | hk
  · rw [hk] at h0 hlt
    rw [take_getD _ (by rw [List.length_take] at hlt; omega),
      wK_getD D Fl s ch fd t vals 0 (by unfold nDigits; omega)] at h0
    exact hne1 (by rw [← h0]; simp [digitP])
  · rw [hk] at hlt
    exact lt_irrefl _ hlt
  · rw [hk] at h0
    exact hne2 h0.symm

theorem height_lt_nDigitsK (o : ℕ) : D.shape.heights.getD o 0 < nDigits D.shape := by
  have := height_le_rW D.shape o
  unfold nDigits; omega

theorem lm_lt_nDigitsK : D.shape.logMemory < nDigits D.shape := by
  have := logMemory_le_rW D.shape
  unfold nDigits; omega

/-- **Each Keccak table's part at `t`**: its point is a `C1` point, its sent values are its columns at `t`, its
leaf's products the flushes' fingerprints at `t`, its degrees `tableDegrees`. -/
theorem part_specK (hold : HoldAllK D Fl s c1 ch fd c2 t vals) (o : ℕ) (ho : o < 6) :
    IsPtK D Fl s ch fd t vals .c1 ((inpK D Fl s ch fd t vals).w.take (D.shape.heights.getD o 0)) ∧
    (∀ c ∈ sentColumns (tablesKeccak.getD o default),
      ((tpK (inpK D Fl s ch fd t vals)).1.getD o default).sent.getD c none =
        some ((c1PK D.shape c1 (.table o c)).eval t)) ∧
    ((tpK (inpK D Fl s ch fd t vals)).1.getD o default).pull =
      (((tablesKeccak.getD o default).flushes.pull.zip (tablesKeccak.getD o default).flushes.push).map fun fl ↦
        (inpK D Fl s ch fd t vals).beta +
          tupleE fl.1 (inpK D Fl s ch fd t vals).weights fun c ↦ (c1PK D.shape c1 (.table o c)).eval t).prod ∧
    ((tpK (inpK D Fl s ch fd t vals)).1.getD o default).push =
      (((tablesKeccak.getD o default).flushes.pull.zip (tablesKeccak.getD o default).flushes.push).map fun fl ↦
        (inpK D Fl s ch fd t vals).beta +
          tupleE fl.2 (inpK D Fl s ch fd t vals).weights fun c ↦ (c1PK D.shape c1 (.table o c)).eval t).prod ∧
    ((tpK (inpK D Fl s ch fd t vals)).1.getD o default).pullDegree = (tableDegrees (tablesKeccak.getD o default)).1 ∧
    ((tpK (inpK D Fl s ch fd t vals)).1.getD o default).pushDegree =
      (tableDegrees (tablesKeccak.getD o default)).2 := by
  have h6 : o < tablesKeccak.length := by rw [tablesKeccak_length]; exact ho
  obtain ⟨v', hpart, hsub⟩ := tablesPart_getD D.shape (inpK D Fl s ch fd t vals).weights
    (inpK D Fl s ch fd t vals).beta (inpK D Fl s ch fd t vals).w tablesKeccak (inpK D Fl s ch fd t vals).vals o h6
  rw [← List.getD_eq_getElem _ default h6, tablesKeccak_opcode o ho] at hpart hsub
  have hw0 := tablePartOf_equal_mem (tablesKeccak.getD o default) (D.shape.heights.getD o 0)
    (inpK D Fl s ch fd t vals).weights (inpK D Fl s ch fd t vals).beta (inpK D Fl s ch fd t vals).w v' 0
    (List.length_pos_iff.mpr (sentColumns_ne_nil _))
  have hpt : IsPtK D Fl s ch fd t vals .c1 ((inpK D Fl s ch fd t vals).w.take (D.shape.heights.getD o 0)) :=
    ⟨_, mem_rels_tpK D Fl s ch fd t vals (hsub _ hw0), rfl, _, List.mem_singleton_self _, rfl⟩
  have hev : ∀ c, evOfK D Fl s c1 ch fd c2 t vals (.table (tablesKeccak.getD o default).opcode c)
      ((inpK D Fl s ch fd t vals).w.take (D.shape.heights.getD o 0)) = (c1PK D.shape c1 (.table o c)).eval t := by
    intro c
    rw [tablesKeccak_opcode o ho]
    exact ev_c1K D Fl s c1 ch fd c2 t vals (.table o c) rfl (fun j h ↦ by cases h) _
      (height_lt_nDigitsK D o).le le_rfl hpt
  have hh : ∀ r ∈ (tablePartOf (tablesKeccak.getD o default) (D.shape.heights.getD o 0)
      (inpK D Fl s ch fd t vals).weights (inpK D Fl s ch fd t vals).beta (inpK D Fl s ch fd t vals).w v').2.1,
      RelHolds (evOfK D Fl s c1 ch fd c2 t vals) r := by
    intro r hr
    refine hold r (mem_rels_tpK D Fl s ch fd t vals (hsub r hr)) .c1 fun tm htm ↦ ?_
    obtain ⟨⟨c, hc⟩, -, htw⟩ := tablePartOf_terms _ _ _ _ _ _ r hr tm htm
    exact ⟨htw, by rw [hc]; rfl⟩
  obtain ⟨s1, s2, s3, s4, s5⟩ := tablePartOf_specOf (tablesKeccak.getD o default)
    (tablesLinK _ (tablesKeccak_mem o ho)) _ _ _ _ v'
    (evOfK D Fl s c1 ch fd c2 t vals) (fun c ↦ (c1PK D.shape c1 (.table o c)).eval t) hev hh
  have hpart' : (tpK (inpK D Fl s ch fd t vals)).1.getD o default = (tablePartOf (tablesKeccak.getD o default)
      (D.shape.heights.getD o 0) (inpK D Fl s ch fd t vals).weights (inpK D Fl s ch fd t vals).beta
      (inpK D Fl s ch fd t vals).w v').1 := hpart
  rw [hpart']
  exact ⟨hpt, s1, s2, s3, s4, s5⟩

end Ctx

end UniKeccakSound.IdsEval
