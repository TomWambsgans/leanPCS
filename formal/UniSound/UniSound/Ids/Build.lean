-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniSound.Ids.Batch

/-!
# `BusModel` and `UniIdsRest`, constructed

**`busModelOf D N h`** and **`idsRestOf D N h Fl g`**: the bus model and the identity model of
`UniSound.Bus`, for a deployment `D` and Flock's phase `Fl`, from the data of `Model.lean`, the proved
reductions (the batch's start, `batch_start_of`; the pending matrices', `pending_of_diffs`; the bounds),
and two structures of named hypotheses:

* `IdsHyps D N` — the bridges of `Bridges.lean` (the batch's algebra, the deployment's constants, Lv42),
  each a statement about the verifier's, Lv42's or the deployment's definitions;
* `IdsGaps D Fl` — the reductions between the verifier's checks and the identities not yet proved
  here: the relations at `t` give the identities at `t` (`DiffsEvalP`), the identities as polynomials give
  the heap and the constraint vectors (`MainOfPolysP`), the constraint vectors give the rows' constraints
  (`CvecOkP`), the ring-switch relation gives Flock's claim (`DiffsFlockP`), the degrees (`DegBoundP`), the
  relations' number (`RelCountP`).

`uniKnowledgeSoundness_ids`: the end theorem with these in place of `B` and `J`.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

/-! ## The reductions, stated -/

/-- **The constraint vectors' vanishing gives the counts in range and the rows' constraints.** -/
def CvecOkP (D : Deployment) : Prop :=
  ∀ s c, (∀ x < 2 ^ D.shape.constraintVars, ∀ v ∈ cvecOf D c s x, v = 0) →
    CountsFit D.shape s.2 ∧ RowConstraints D c s

/-! ## Proved fields -/

/-- The number of constraints, any `C1` (the list's shape does not depend on the stack). -/
noncomputable def ncvOf (S : Shape) : ℕ := (constraintsP S (fun _ ↦ 0) []).length + 1

theorem length_filterMap_map {α β γ : Type} (l : List α) (o : α → Option β) (g : α → β → γ) :
    (l.filterMap fun x ↦ (o x).map (g x)).length = (l.filterMap o).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons]
    cases o a <;> simp [ih]

theorem length_constraintsP (S : Shape) (c : Stk) (pw : List E) :
    (constraintsP S c pw).length = (constraintsP S (fun _ ↦ 0) []).length := by
  unfold constraintsP linesP tableConstraintsP
  generalize tables = ts
  simp only [List.length_append, List.length_flatMap, List.length_map, List.length_zip, linesOf,
    List.length_cons, List.length_nil, List.length_range]
  refine congrArg (· + _) (congrArg List.sum (List.map_congr_left fun tab _ ↦ ?_))
  split_ifs <;> simp [length_filterMap_map]

theorem cvecOf_len (D : Deployment) (s : USt) (c : Stk) (x : ℕ) :
    (cvecOf D c s x).length ≤ ncvOf D.shape := by
  unfold cvecOf ncvOf
  split_ifs
  · rw [List.length_map, length_constraintsP]; omega
  · simp

/-- Each heap block's leaves read off `C1` has the block's size. -/
theorem blockK_r (D : Deployment) (c : Stk) (rows : List ℕ) (b : Block) :
    (blockK D c rows b).r = b.r := by
  unfold blockK
  cases b.leaves <;> rfl

/-- **The heap read off `C1` is well formed** (`HeapGood`: the blocks fill the leaves). -/
theorem hdOf_wf (D : Deployment) (hH : HeapGood D.shape) (c : Stk) (s : USt) :
    (hdOf D c s).WellFormed := by
  refine ⟨hH.1, ?_⟩
  show Heap.total (D.shape.heap.blocks.map (blockK D c s.2)) = 2 ^ (D.shape.heap.h - 1)
  unfold Heap.total
  rw [List.map_map]
  rw [← hH.2.2.1]
  congr 1
  refine List.map_congr_left fun b _ ↦ ?_
  simp [blockK_r]

theorem natDegree_listSum_le (l : List (Polynomial E)) (n : ℕ) (h : ∀ p ∈ l, p.natDegree ≤ n) :
    l.sum.natDegree ≤ n := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.sum_cons]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (h p (List.mem_cons_self ..)) (ih fun q hq ↦ h q (List.mem_cons_of_mem _ hq)))

/-- A coordinate functional's degree: at most `2^m` for `m` of its coefficients. -/
theorem natDegree_yP_le (a : Array (Array K)) (l : ℕ) : (yP a l).natDegree ≤ 2 ^ a.size := by
  unfold yP
  refine natDegree_listSum_le _ _ fun p hp ↦ ?_
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
  rw [List.mem_range] at hm
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    (Nat.pow_le_pow_right (by norm_num) hm.le)

/-- The merge polynomial's degree bound: `2^(h_B + 1)` (`coordinateFunctionals h_B` has `h_B` rows,
`Eval.lean`'s `coordinateFunctionals_size`). -/
def zBadDeg (S : Shape) : ℕ := 2 ^ ((coordinateFunctionals (S.heights.getD opSha3 0)).size + 1)

/-- **`Z_bad`'s degree** is at most `zBadDeg`. -/
theorem natDegree_zBad_le (S : Shape) (p0 : E) : (zBad S p0).natDegree ≤ zBadDeg S := by
  unfold zBad zBadDeg
  have hy := natDegree_yP_le (coordinateFunctionals (S.heights.getD opSha3 0)) 0
  have h1 : 1 ≤ 2 ^ (coordinateFunctionals (S.heights.getD opSha3 0)).size := Nat.one_le_two_pow
  refine (Polynomial.natDegree_mul_le).trans ?_
  have ha := (Polynomial.natDegree_add_le
    (yP (coordinateFunctionals (S.heights.getD opSha3 0)) 0) Polynomial.X).trans
      (max_le hy (Polynomial.natDegree_X_le.trans h1))
  have hb := (Polynomial.natDegree_add_le
    (yP (coordinateFunctionals (S.heights.getD opSha3 0)) 0) (Polynomial.C p0)).trans
      (max_le hy (by rw [Polynomial.natDegree_C]; exact Nat.zero_le _))
  rw [pow_succ]
  omega

/-! ## The models -/

/-- The values the stream sends at `t`: each table's sent columns and sent fingerprints, then the
memory's three, the bytecode's two, `T(t)`, `Q_W(t)` (as `tablePartOf` reads them). -/
def nVOf (S : Shape) : ℕ :=
  (tablesPart S #[] 0 [] tables (List.replicate 4096 0)).2.2.length |> fun left ↦ 4096 - left + 7

end UniSound.Ids
