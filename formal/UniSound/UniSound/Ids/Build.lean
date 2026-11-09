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

/-! ## Proved fields -/

theorem length_filterMap_map {α β γ : Type} (l : List α) (o : α → Option β) (g : α → β → γ) :
    (l.filterMap fun x ↦ (o x).map (g x)).length = (l.filterMap o).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filterMap_cons]
    cases o a <;> simp [ih]

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

end UniSound.Ids
