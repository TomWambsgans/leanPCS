-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniSound.Ids.Cvec

/-!
# `CvecOkP`: the constraint vectors' vanishing gives the rows' constraints

`cvecOk`: where every entry of every row's constraint vector vanishes on `V_{r_W}`, the counts are in
range (out of range the vectors hold a `1`) and `RowConstraints` holds: each constraint `(M_i, W_i)` has
`M_i = 1` on its table's domain, so `W_i(ω_x) = 0` there, and `W_i(ω_x)` is the constraint on `C1`'s row
`x` read in `K`.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Polynomial

theorem le_foldl_max : ∀ (l : List ℕ) (b a : ℕ), a ∈ l ∨ a ≤ b → a ≤ l.foldl max b
  | [], _, _, h => by simpa using h
  | x :: l, b, a, h => by
    rw [List.foldl_cons]
    refine le_foldl_max l (max b x) a ?_
    rcases h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (le_max_right _ _)
      · exact Or.inl h
    · exact Or.inr (le_trans h (le_max_left _ _))

theorem height_le_rW (S : Shape) (o : ℕ) : S.heights.getD o 0 ≤ S.constraintVars := by
  unfold Shape.constraintVars
  by_cases ho : o < S.heights.length
  · refine le_foldl_max _ 0 _ (Or.inl (List.mem_append_left _ ?_))
    rw [List.getD_eq_getElem _ _ ho]
    exact List.getElem_mem ho
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

theorem logMemory_le_rW (S : Shape) : S.logMemory ≤ S.constraintVars :=
  le_foldl_max _ 0 _ (Or.inl (List.mem_append_right _ (List.mem_singleton_self _)))

theorem ofK_list_prod (l : List K) : ofK l.prod = (l.map ofK).prod := map_list_prod (algebraMap K E) l

theorem lift_mul_eval (h : BetaCantor) (r m x : ℕ) (hx : x < 2 ^ r) (hx24 : x < 2 ^ 24) (W : Polynomial E) :
    (liftP r m * W).eval (pointE x) = W.eval (pointE x) := by
  rw [Polynomial.eval_mul, liftP_eval_pointE h r m x hx hx24, one_mul]
