-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proof is `UniSound/Ids/WeightMle.lean`'s
-- (`combAt_mle`) for `formal/UniKeccak`'s `weightAtK` (`Verifier.lean`) and the Keccak relations (`relsAtK`:
-- `mainRelsK`, `constraintRelationK`, `flockClaimK`).
import UniSound.Ids.WeightMle
import UniSound.Ids.Align
import UniKeccakSound.Ids.Final
import UniKeccakSound.Ids.FlockReg

/-!
# The Keccak batch's weights are multilinear off `Z_bad`'s roots (`WeightMleK`)

**`weightMleK_of`**: `WeightMleK D Fl` for Flock's phase at `κ = h_SHA3`: where `Z_bad(t) ≠ 0` and Flock's point has
`q_flock`'s `11 + κ` coordinates (`FlockGoodK`), each commitment's combined claim's `weightAtK` at a point `r` of the
batch's variables is the fold of its values on the cube (`weightAtK` is the multilinear extension of its cube values).

The proof is `UniSound.Ids.combAt_mle`'s, with `UniSound.Ids.Multilin`'s generic multilinear algebra (`Mle`,
`mle_block`, `mle_plain`, `mle_ring`):

* **One term under `weightAtK`** (`wSumK`): an ordinary column's and the ring-switch term's are `weightAt`'s
  (`mle_plainK`, `mle_ringK`); `q_flock`'s slot `j` at `y` reads `(bits_{qv − |y|}(j), y)`, one block of `q_flock`
  when `qv − |y| + |y|` is within its block's variables (`mle_slotK`).
* **The terms of the run** (`relsAtK_kinds`): every term of `relsAtK` is untwisted and not a slot, at a prefix of the
  digits if its relation is on `C1` (the tables' parts `tablesK_kinds`, the memory's and the bytecode's, the heap's);
  or untwisted on `C1` at `y(t)` (the constraint relation `crK_kinds`, `constraintRelationK`'s loops by invariants);
  or the ring-switch term on `q_flock` at Flock's point.
* **No merge** (`y_selfK`): off `Z_bad`'s roots no longer `C1` point extends `y(t)` (its first coordinate is neither
  `t`, the digits', nor Flock's point's), so `y(t)` is its own merged point (`mergedSelf`), `11 + h_SHA3 = qv`
  coordinates read (`qflock_le_batchK`, `qvOfK_c1`).
* **The combined claim** (`combAt_isMleK`): `weightAtK_linear` and `combineEq`.
-/

namespace UniKeccakSound.Ids.MultilinK

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.Weights UniSound.Ids.Multilin UniKeccak
open UniKeccakSound.Ids Finset

/-! ## One term under `weightAtK` -/

theorem slotViewK_of_ne {column : Column} (h : ∀ j, column ≠ .qflockSlot j) (qv : ℕ) (pt point : List E) :
    slotViewK qv column pt point = (column, point, 0) := by
  unfold slotViewK
  split
  · rename_i j
    exact absurd rfl (h j)
  · rfl

/-- **An ordinary column's term** under `weightAtK` (untwisted, not a slot) is multilinear. -/
theorem mle_plainK (L : StackLayout) (rm : Option (List E)) (V : ℕ) (mp : List E) (col : Column)
    (hcol : ∀ j, col ≠ .qflockSlot j) :
    Mle V (fun p ↦ wSumK L p rm mp (twistPt mp 0) col 0) := by
  refine Mle.congr (mle_plain L rm V mp col hcol) fun p _ ↦ ?_
  rw [wSum, wSumK, ite_eq_right zero_ne_ringTwist, ite_eq_right zero_ne_ringTwist, slotView_of_ne hcol,
    slotViewK_of_ne hcol]

/-- **`q_flock`'s slot `j` at `y`** under `weightAtK` (`qv − |y|` slot bits) is multilinear where its row's
`qv − |y| + |y|` coordinates are within its block's variables. -/
theorem mle_slotK (L : StackLayout) (rm : Option (List E)) (V j : ℕ) (y : List E)
    (hpos : 0 < qvOf L - y.length + y.length)
    (hv : ∀ b ∈ L.limbs .qflock, qvOf L - y.length + y.length ≤ b.2.1) :
    Mle V (fun p ↦ wSumK L p rm y (twistPt y 0) (.qflockSlot j) 0) := by
  have hlen : ((List.range (qvOf L - y.length)).map (bitE j) ++ y).length = qvOf L - y.length + y.length := by
    simp
  refine Mle.congr (Mle.listSum (L.limbs .qflock) (fun b p ↦ limbScale b.1 *
    (rowEq ((List.range (qvOf L - y.length)).map (bitE j) ++ y) (qvOf L - y.length + y.length) p *
      selector p b.2.1 b.2.2))
    fun b hb ↦ (mle_block V _ b.2.1 b.2.2 _ (hv b hb)).const_mul _) fun p _ ↦ ?_
  have h0 : twistPt y 0 = y := rfl
  rw [wSumK, ite_eq_right zero_ne_ringTwist, h0]
  refine congrArg List.sum (List.map_congr_left fun b _ ↦ ?_)
  simp only [slotViewK, hlen, gt_iff_lt, hpos, ↓reduceIte]

theorem wSumK_ring_eq (L : StackLayout) (r : List E) (rm : Option (List E)) (pt point : List E) (col : Column) :
    wSumK L r rm pt point col ringTwist = wSum L r rm pt point col ringTwist := by
  simp only [wSumK, wSum, ite_true]

/-- **The ring-switch term** under `weightAtK` is `weightAt`'s, multilinear. -/
theorem mle_ringK (L : StackLayout) (V : ℕ) (map mp fp : List E) (hext : mp.take fp.length = fp)
    (hv : ∀ b ∈ L.limbs .qflock, b.2.1 = fp.length ∧ b.2.1 ≤ V) :
    Mle V (fun p ↦ wSumK L p (some map) mp (twistPt mp ringTwist) .qflock ringTwist) :=
  Mle.congr (mle_ring L V map mp fp hext hv) fun _ _ ↦ (wSumK_ring_eq _ _ _ _ _ _).symm

/-- **The ring-switch term without a map** under `weightAtK` is zero. -/
theorem mle_ring_noneK (L : StackLayout) (V : ℕ) (mp mp' : List E) :
    Mle V (fun p ↦ wSumK L p none mp mp' .qflock ringTwist) :=
  Mle.congr (mle_ring_none L V mp mp') fun _ _ ↦ (wSumK_ring_eq _ _ _ _ _ _).symm

/-! ## The terms of the Keccak relations -/

/-- The digits of `t` the Keccak relations read (`mainRelsK`'s `w`). -/
def wK (S : Shape) (t : E) : List E := digits t (max S.heap.h (S.constraintVars + 4) + 2)

/-- `y(t)`, `SHA3`'s coordinates of `t` (the copies' slot point). -/
def yK (S : Shape) (t : E) : List E := coordinatesAt t (coordinateFunctionals (S.heights.getD opSha3 0))

/-- **A constraint term**: untwisted, on `C1`, either not a slot at a prefix of the digits, or at `y`. -/
def CrKind (w y : List E) (tm : Term) : Prop :=
  tm.twist = 0 ∧ tm.column.commitment = .c1 ∧
    (((∀ j, tm.column ≠ .qflockSlot j) ∧ ∃ k, tm.point = w.take k) ∨ tm.point = y)

theorem opJump_ne_opSha3 : opJump ≠ opSha3 := by decide

/-- **The constraint relation's terms** (`constraintRelationK`): untwisted, on `C1`, not a slot at a prefix of the
digits or at `y(t)` (the lanes' copies' slots). -/
theorem crK_kinds (S : Shape) (parts : List TablePart) (pw : List E) (gamma t cv : E) :
    ∀ tm ∈ (constraintRelationK S parts pw gamma t cv (wK S t)).1.terms, CrKind (wK S t) (yK S t) tm := by
  unfold constraintRelationK
  simp only [Id.run_bind, Id.run_pure]
  refine forIn_id_inv (fun s : E × Array Term × E => ∀ tm ∈ s.2.1.toList, CrKind (wK S t) (yK S t) tm) _ ?_ _ _ ?_
  · rintro ⟨⟨low, high⟩, k⟩ s hs
    refine ⟨_, rfl, fun tm htm ↦ ?_⟩
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at htm
    rcases htm with htm | rfl
    · exact hs tm htm
    · exact ⟨rfl, rfl, Or.inl ⟨(fun j h ↦ by cases h), _, rfl⟩⟩
  · refine forIn_id_inv (fun s : E × Array Term × E × ℕ => ∀ tm ∈ s.2.1.toList, CrKind (wK S t) (yK S t) tm) _ ?_
      _ _ (by simp)
    rintro ⟨table, part⟩ s hs
    by_cases hj : table.opcode = opJump
    · have hb : ¬ table.opcode = opSha3 := fun h ↦ opJump_ne_opSha3 (hj ▸ h)
      simp only [hj, ↓reduceIte, opJump_ne_opSha3]
      refine ⟨_, rfl, fun tm htm ↦ ?_⟩
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at htm
      rcases htm with (htm | rfl) | rfl
      · exact hs tm htm
      · exact ⟨rfl, rfl, Or.inl ⟨(fun j h ↦ by cases h), _, rfl⟩⟩
      · exact ⟨rfl, rfl, Or.inl ⟨(fun j h ↦ by cases h), _, rfl⟩⟩
    · by_cases hb : table.opcode = opSha3
      · simp only [hb, ↓reduceIte]
        refine ⟨_, rfl, ?_⟩
        refine forIn_id_inv (fun s : E × Array Term × E => ∀ tm ∈ s.2.1.toList, CrKind (wK S t) (yK S t) tm) _ ?_
          _ _ ?_
        · intro c s' hs'
          split
          · split
            all_goals
              refine ⟨_, rfl, fun tm htm ↦ ?_⟩
              simp only [Array.toList_push, List.mem_append, List.mem_singleton] at htm
              rcases htm with (htm | rfl) | rfl
              · exact hs' tm htm
              · exact ⟨rfl, rfl, Or.inl ⟨(fun j h ↦ by cases h), _, rfl⟩⟩
              · exact ⟨rfl, rfl, Or.inr rfl⟩
          · exact ⟨_, rfl, hs'⟩
        · intro tm htm
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at htm
          rcases htm with htm | rfl
          · exact hs tm htm
          · exact ⟨rfl, rfl, Or.inl ⟨(fun j h ↦ by cases h), _, rfl⟩⟩
      · simp only [hj, hb, ↓reduceIte]
        refine ⟨_, rfl, fun tm htm ↦ ?_⟩
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at htm
        rcases htm with htm | rfl
        · exact hs tm htm
        · exact ⟨rfl, rfl, Or.inl ⟨(fun j h ↦ by cases h), _, rfl⟩⟩

/-- The constraint relation is on `C1`. -/
theorem crK_commitment (S : Shape) (parts : List TablePart) (pw : List E) (gamma t cv : E) :
    (constraintRelationK S parts pw gamma t cv (wK S t)).1.commitment = .c1 :=
  Eval.commitment_c1 fun tm htm ↦ (crK_kinds S parts pw gamma t cv tm htm).2.1

/-- A table's term: on a table's column, at a prefix of the digits, untwisted. -/
def TabKind (w : List E) (tm : Term) : Prop :=
  (∃ o c, tm.column = .table o c) ∧ (∃ k, tm.point = w.take k) ∧ tm.twist = 0

/-- **The tables' parts' terms** (`reduceWithK`'s tables loop): on the tables' columns at prefixes of the digits,
untwisted. -/
theorem tablesK_kinds (heights : List ℕ) (weights : Array E) (beta : E) (w : List E) :
    ∀ (ts : List Table) (s : Array Relation × Array TablePart) (vs : List E),
      (∀ r ∈ s.1.toList, ∀ tm ∈ r.terms, TabKind w tm) →
      ∀ r ∈ (consumeFold tableReads (tablesStep heights weights beta w) ts s vs).1.toList, ∀ tm ∈ r.terms,
        TabKind w tm
  | [], _, _, h => h
  | x :: ts, s, vs, h => by
    simp only [consumeFold]
    refine tablesK_kinds heights weights beta w ts _ _ fun r hr tm htm ↦ ?_
    simp only [tablesStep, Array.toList_append, List.mem_append] at hr
    rcases hr with hr | hr
    · exact h r hr tm htm
    · have he := congrArg (fun z ↦ z.2.1) (tablePartOf_eq x (heights.getD x.opcode 0) weights beta w vs)
      simp only [] at he
      have hr' : r ∈ (tablePartOf x (heights.getD x.opcode 0) weights beta w vs).2.1 := by
        rw [he]
        simpa using hr
      obtain ⟨⟨c, hc⟩, hp, htw⟩ := Eval.tablePartOf_terms x _ weights beta w vs r hr' tm htm
      exact ⟨⟨_, c, hc⟩, ⟨_, hp⟩, htw⟩

/-- **The terms of the relations before Flock's claim** (`mainRelsK`): untwisted and not a slot, at a prefix of the
digits if the relation is on `C1`; or untwisted on `C1` at `y(t)`. -/
theorem mainRelsK_kinds (S : Shape) (pw : List E) (counts : List (List E)) (alphas : List E) (beta gamma t : E)
    (vals : List E) :
    ∀ r ∈ (mainRelsK S pw counts alphas beta gamma t vals).1.toList, ∀ tm ∈ r.terms,
      (tm.twist = 0 ∧ (∀ j, tm.column ≠ .qflockSlot j) ∧ (r.commitment = .c1 → ∃ k, tm.point = (wK S t).take k)) ∨
        (tm.twist = 0 ∧ r.commitment = .c1 ∧ tm.point = yK S t) := by
  intro r hr tm htm
  unfold mainRelsK at hr
  simp only [Array.toList_append, Array.toList_push, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    at hr
  rcases hr with ((((((hr | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | hr
  · obtain ⟨⟨o, c, hc⟩, ⟨k, hk⟩, htw⟩ := tablesK_kinds _ _ _ _ _ _ _ (by simp) r hr tm htm
    exact Or.inl ⟨htw, (fun j h ↦ by rw [hc] at h; cases h), fun _ ↦ ⟨k, hk⟩⟩
  · simp only [Relation.equal, term, List.mem_singleton] at htm
    subst htm
    exact Or.inl ⟨rfl, (fun j h ↦ by cases h), fun _ ↦ ⟨_, rfl⟩⟩
  · simp only [Relation.equal, term, List.mem_singleton] at htm
    subst htm
    exact Or.inl ⟨rfl, (fun j h ↦ by cases h), fun _ ↦ ⟨_, rfl⟩⟩
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp htm
    exact Or.inl ⟨rfl, (fun j h ↦ by cases h), fun _ ↦ ⟨_, rfl⟩⟩
  · simp only [Relation.equal, term, List.mem_singleton] at htm
    subst htm
    exact Or.inl ⟨rfl, (fun j h ↦ by cases h), fun _ ↦ ⟨_, rfl⟩⟩
  · simp only [Relation.equal, term, List.mem_singleton] at htm
    subst htm
    exact Or.inl ⟨rfl, (fun j h ↦ by cases h),
      fun h ↦ (by simp [Relation.equal, Relation.commitment, term, Column.commitment] at h)⟩
  · obtain ⟨htw, -, hk⟩ := crK_kinds S _ pw gamma t _ tm htm
    rcases hk with ⟨hns, hpt⟩ | hy
    · exact Or.inl ⟨htw, hns, fun _ ↦ hpt⟩
    · exact Or.inr ⟨htw, crK_commitment _ _ _ _ _ _, hy⟩
  · obtain ⟨hc2, htw⟩ := Eval.heap_terms _ _ _ _ _ _ _ _ _ _ _ _ _ r hr tm htm
    refine Or.inl ⟨htw, (fun j h ↦ by rw [h] at hc2; cases hc2), fun h ↦ ?_⟩
    have := Eval.terms_nil_of (fun tm' htm' ↦ (Eval.heap_terms _ _ _ _ _ _ _ _ _ _ _ _ _ r hr tm' htm').1) h
    rw [this] at htm
    cases htm

section Run

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant} (Fl : KFlockSound F κ v)

/-- **Every term of the run's relations at `t`** (`relsAtK`): untwisted and not a slot, at a prefix of the digits if
its relation is on `C1`; or untwisted on `C1` at `y(t)`; or the ring-switch term, on `q_flock` at Flock's point. -/
theorem relsAtK_kinds (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) :
    ∀ r ∈ relsAtK D Fl s ch fd t vals, ∀ tm ∈ r.terms,
      (tm.twist = 0 ∧ (∀ j, tm.column ≠ .qflockSlot j) ∧
          (r.commitment = .c1 → ∃ k, tm.point = (wK D.shape t).take k)) ∨
        (tm.twist = 0 ∧ r.commitment = .c1 ∧ tm.point = yK D.shape t) ∨
        (tm.twist = ringTwist ∧ tm.column = .qflock ∧ tm.point = (Fl.prog.out fd []).1 ∧ r.commitment = .c1) := by
  intro r hr tm htm
  unfold relsAtK flockClaimK at hr
  split at hr
  · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact (mainRelsK_kinds _ _ _ _ _ _ _ _ r hr tm htm).imp id Or.inl
    · simp only [List.mem_singleton] at htm
      subst htm
      exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)
  · exact (mainRelsK_kinds _ _ _ _ _ _ _ _ r hr tm htm).imp id Or.inl

theorem yK_length (S : Shape) (t : E) : (yK S t).length = S.heights.getD opSha3 0 := by
  rw [yK, Eval.coordinatesAt_length, Eval.coordinateFunctionals_size]

/-- `SHA3` has at least one row variable (a valid shape). -/
theorem hSha3_pos : 1 ≤ D.shape.heights.getD opSha3 0 := by
  have h := D.valid.2
  unfold Shape.validate at h
  simp at h
  rw [List.getD_eq_getElem?_getD]
  omega

/-- **No longer `C1` point extends `y(t)`** where `Z_bad(t) ≠ 0`. -/
theorem y_selfK (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) (hz : (zbK D Fl fd).eval t ≠ 0) :
    ∀ r ∈ mine (relsAtK D Fl s ch fd t vals) .c1, ∀ tm ∈ r.terms,
      (yK D.shape t).length < tm.point.length → tm.point.take (yK D.shape t).length ≠ yK D.shape t := by
  have h1 := hSha3_pos D
  have hlen := yK_length D.shape t
  have hy0 : (yK D.shape t).getD 0 0 =
      (yP (coordinateFunctionals (D.shape.heights.getD opSha3 0)) 0).eval t := by
    rw [yK, Eval.coordinatesAt_getD _ _ _ (by rw [Eval.coordinateFunctionals_size]; omega)]
  unfold zbK zBad at hz
  rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    ← hy0] at hz
  have hne1 : (yK D.shape t).getD 0 0 ≠ t := fun h ↦ hz (by rw [h, CharTwo.add_self_eq_zero, zero_mul])
  have hne2 : (yK D.shape t).getD 0 0 ≠ (Fl.prog.out fd []).1.getD 0 0 :=
    fun h ↦ hz (by rw [h, CharTwo.add_self_eq_zero, mul_zero])
  intro r hr tm htm hlt heq
  have hmem := List.mem_filter.mp hr
  have hc : r.commitment = .c1 := by simpa using hmem.2
  have h0 : (tm.point.take (yK D.shape t).length).getD 0 0 = (yK D.shape t).getD 0 0 := by rw [heq]
  rw [Eval.take_getD _ (by omega)] at h0
  rcases relsAtK_kinds D Fl s ch fd t vals r hmem.1 tm htm with ⟨-, -, hk⟩ | ⟨-, -, hk⟩ | ⟨-, -, hk, -⟩
  · obtain ⟨k, hk⟩ := hk hc
    rw [hk] at h0 hlt
    rw [Eval.take_getD _ (by rw [List.length_take] at hlt; omega), wK,
      digits_getD t _ 0 (by omega)] at h0
    exact hne1 (by rw [← h0]; simp [digitP])
  · rw [hk] at hlt
    exact lt_irrefl _ hlt
  · rw [hk] at h0
    exact hne2 h0.symm

theorem layoutOfK_c1W (S : Shape) : layoutOfK S .c1 = c1LayoutK S := rfl

/-- `q_flock` in `C1`'s layout reads `h_SHA3 + 11` variables, within the batch's. -/
theorem qflock_le_batchK (S : Shape) : S.heights.getD opSha3 0 + qflockRowBits ≤ batchVarsK S := by
  obtain ⟨off, hl⟩ := c1LayoutK_qflock S
  rw [← layoutOfK_c1W] at hl
  have hbl := layoutAligned_new _ _ (limbs_mem_blocks (L := layoutOfK S .c1)
    (b := (0, S.heights.getD opSha3 0 + qflockRowBits, off)) (by rw [hl]; exact List.mem_singleton_self _))
  have hb2 : off + 2 ^ (S.heights.getD opSha3 0 + qflockRowBits) ≤ 2 ^ (layoutOfK S .c1).vars := hbl.2
  have hvars : (layoutOfK S .c1).vars ≤ batchVarsK S := UniSound.layoutOf_vars_le _ _
  have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hvars
  have h3 : 2 ^ (S.heights.getD opSha3 0 + qflockRowBits) ≤ 2 ^ (batchVarsK S) := by omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h3

theorem qvOfK_c1 (S : Shape) : qvOf (layoutOfK S .c1) = S.heights.getD opSha3 0 + qflockRowBits := by
  obtain ⟨off, hl⟩ := c1LayoutK_qflock S
  rw [← layoutOfK_c1W] at hl
  simp [qvOf, hl]

theorem qflockRowBits_eq : qflockRowBits = 11 := rfl

/-- **A relation term's `weightAtK` at its merged point is multilinear**, off `Z_bad`'s roots and with Flock's point
of `q_flock`'s `11 + κ` coordinates, `κ = h_SHA3`. -/
theorem term_mleK (hκ : D.shape.heights.getD opSha3 0 = κ) (s : USt) (ch : List E) (fd : Done) (t : E)
    (vals : List E) (hfp : (Fl.prog.out fd []).1.length = KeccakVm.kWords + κ) (hz : (zbK D Fl fd).eval t ≠ 0)
    (c : Commitment) (r : Relation) (hr : r ∈ mine (relsAtK D Fl s ch fd t vals) c) (tm : Term)
    (htm : tm ∈ r.terms) (rm : Option (List E)) :
    Mle (batchVarsK D.shape) (fun p ↦ weightAtK ⟨[mergedPoint (mine (relsAtK D Fl s ch fd t vals) c) tm.point],
      [(tm.column, 0, tm.twist, 1)], 0, 1⟩ (layoutOfK D.shape c) p rm) := by
  have hmem := List.mem_filter.mp hr
  have hrc : r.commitment = c := by simpa using hmem.2
  refine Mle.congr ?_ fun p _ ↦ (weightAtK_single (layoutOfK D.shape c) p rm _ tm.column tm.twist).symm
  rcases relsAtK_kinds D Fl s ch fd t vals r hmem.1 tm htm with ⟨htw, hns, -⟩ | ⟨htw, hc1, hy⟩ |
    ⟨htw, hcol, hpt, hrc1⟩
  · rw [htw]
    exact mle_plainK _ rm _ _ tm.column hns
  · rw [htw]
    by_cases hslot : ∃ j, tm.column = .qflockSlot j
    · obtain ⟨j, hj⟩ := hslot
      rw [hrc] at hc1
      subst hc1
      have hmp : mergedPoint (mine (relsAtK D Fl s ch fd t vals) .c1) tm.point = yK D.shape t := by
        rw [hy]
        exact mergedSelf _ _ ⟨r, hr, tm, htm, hy⟩ (y_selfK D Fl s ch fd t vals hz)
      rw [hmp, hj]
      have hq := qvOfK_c1 D.shape
      have hyl := yK_length D.shape t
      obtain ⟨off, hl⟩ := c1LayoutK_qflock D.shape
      rw [← layoutOfK_c1W] at hl
      refine mle_slotK _ rm _ j (yK D.shape t) (by rw [hq, hyl, qflockRowBits_eq]; omega) fun b hb ↦ ?_
      rw [hl, List.mem_singleton] at hb
      subst hb
      rw [hq, hyl]
      show _ ≤ D.shape.heights.getD opSha3 0 + qflockRowBits
      omega
    · simp only [not_exists] at hslot
      exact mle_plainK _ rm _ _ tm.column hslot
  · rw [hrc] at hrc1
    subst hrc1
    have hext := (mergedPrefix (mine (relsAtK D Fl s ch fd t vals) .c1) (Fl.prog.out fd []).1
      ⟨r, hr, tm, htm, hpt⟩).1
    rw [htw, hcol, hpt]
    cases rm with
    | none => exact mle_ring_noneK _ _ _ _
    | some map =>
      refine mle_ringK _ _ map _ (Fl.prog.out fd []).1 hext fun b hb ↦ ?_
      obtain ⟨off, hl⟩ := c1LayoutK_qflock D.shape
      rw [← layoutOfK_c1W] at hl
      rw [hl, List.mem_singleton] at hb
      subst hb
      have hle := qflock_le_batchK D.shape
      refine ⟨?_, hle⟩
      show D.shape.heights.getD opSha3 0 + qflockRowBits = (Fl.prog.out fd []).1.length
      rw [hfp, hκ, qflockRowBits_eq]
      show κ + 11 = 11 + κ
      omega

/-- **A combined claim's `weightAtK` is multilinear in the batch's point**, off `Z_bad`'s roots and with Flock's
point of `q_flock`'s `11 + κ` coordinates, `κ = h_SHA3`. -/
theorem combAt_isMleK (hκ : D.shape.heights.getD opSha3 0 = κ) (s : USt) (ch : List E) (fd : Done) (t : E)
    (vals : List E) (ρ : E) (hfp : (Fl.prog.out fd []).1.length = KeccakVm.kWords + κ)
    (hz : (zbK D Fl fd).eval t ≠ 0) (c : Commitment) :
    Mle (batchVarsK D.shape) (fun p ↦
      weightAtK (combAtK D Fl s ch fd t vals ρ c) (layoutOfK D.shape c) p (ringMapAtK Fl fd)) := by
  by_cases hm : mine (relsAtK D Fl s ch fd t vals) c = []
  · have hnone : combine (relsAtK D Fl s ch fd t vals) c ρ = none := by
      unfold combine
      simp only [mine] at hm
      simp [hm]
    refine Mle.congr (Mle.zero _) fun p _ ↦ ?_
    simp only [combAtK, hnone, Option.getD_none]
    rfl
  · obtain ⟨cb, hcb, -, hF⟩ := combineEq (relsAtK D Fl s ch fd t vals) c ρ hm
    have hca : combAtK D Fl s ch fd t vals ρ c = cb := by
      simp only [combAtK, hcb, Option.getD_some]
    rw [hca]
    refine Mle.congr (Mle.listSum (mine (relsAtK D Fl s ch fd t vals) c).zipIdx
      (fun ri p ↦ ρ ^ ri.2 * (ri.1.terms.map fun tm ↦ tm.coefficient *
        weightAtK ⟨[mergedPoint (mine (relsAtK D Fl s ch fd t vals) c) tm.point],
          [(tm.column, 0, tm.twist, 1)], 0, 1⟩ (layoutOfK D.shape c) p (ringMapAtK Fl fd)).sum)
      fun ri hri ↦ Mle.const_mul _ (Mle.listSum ri.1.terms _ fun tm htm ↦ Mle.const_mul _
        (term_mleK D Fl hκ s ch fd t vals hfp hz c ri.1 (fst_mem_zipIdx _ _ _ hri) tm htm _)))
      fun p _ ↦ ?_
    rw [weightAtK_linear cb (layoutOfK D.shape c) p (ringMapAtK Fl fd)]
    exact (hF fun col pt tw ↦
      weightAtK ⟨[pt], [(col, 0, tw, 1)], 0, 1⟩ (layoutOfK D.shape c) p (ringMapAtK Fl fd)).symm

end Run

end UniKeccakSound.Ids.MultilinK

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniKeccak MultilinK

/-- **The Keccak batch's weights are multilinear off `Z_bad`'s roots** (`WeightMleK`), for Flock's phase at
`κ = h_SHA3`: where `Z_bad(t) ≠ 0` and Flock's result is the main line's (`FlockGoodK`), each commitment's combined
claim's `weightAtK` at a point `r` of the batch's variables is the fold of its values on the cube. -/
theorem weightMleK_of (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (hκ : D.shape.heights.getD opSha3 0 = κ) : WeightMleK D Fl := by
  intro s ch fd t vals rho r _ hgood _ _ hz hr c _
  exact combAt_isMleK D Fl hκ s ch fd t vals rho hgood.2 hz c r hr

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.weightMleK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.weightMleK_of

/-- info: 'UniKeccakSound.Ids.MultilinK.relsAtK_kinds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.MultilinK.relsAtK_kinds
