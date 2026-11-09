-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniSound.Ids.Build
import UniSound.Ids.Cantor

/-!
# The constraint vectors give the rows' constraints (`CvecOkP`)

Each constraint `(M_i, W_i)` of `constraintsP` is lifted to `V_{r_W}` by `M_i = Π_{j=r_i}^{r_W−1} (w_j + 1)`,
which is `1` on `V_{r_i}` (`liftP_eval_pointE`); so where the constraint vectors vanish on `V_{r_W}`, each
`W_i` vanishes on its table's domain, and `W_i(ω_x)` is the constraint on `C1`'s row `x` read in `K`
(`colPoly_eval_pointE`). `q_flock`'s slot `j` at `y(ω_x)` is the word `j + 256 x` (`slotP_eval_pointE`):
the coordinate functionals give `y_l(ω_x) = x_l` (`yP_eval_pointE`, from `FunctionalsCorrect`), and the
claim at a cube point is the word there (`cubeEq_eq_ite`).
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Polynomial

/-! ## Powers and the coordinate functionals -/

theorem frobK_eq (x : K) : ∀ m, frobK x m = x ^ (2 ^ m)
  | 0 => by simp [frobK]
  | m + 1 => by rw [frobK, frobK_eq (x * x) m, ← pow_two, ← pow_mul, pow_succ', mul_comm]

theorem eval_listSum (l : List (Polynomial E)) (t : E) : l.sum.eval t = (l.map (Polynomial.eval t)).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp [ih]

theorem eval_list_prod_of (l : List (Polynomial E)) (t : E) :
    l.prod.eval t = (l.map (Polynomial.eval t)).prod := by
  induction l with
  | nil => simp
  | cons p l ih => simp [ih]

instance instCharPK' : CharP K 2 := RingHom.charP (algebraMap K E) (algebraMap K E).injective 2

/-- The coordinate functionals are additive. -/
theorem eval_yP_add (a : Array (Array K)) (l : ℕ) (u v : E) :
    (yP a l).eval (u + v) = (yP a l).eval u + (yP a l).eval v := by
  unfold yP
  simp only [eval_listSum, List.map_map]
  rw [← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun m _ ↦ ?_
  simp only [Function.comp_apply, Polynomial.eval_mul, eval_C, eval_pow, eval_X]
  rw [add_pow_char_pow, mul_add]

theorem eval_yP_zero (a : Array (Array K)) (l : ℕ) : (yP a l).eval 0 = 0 := by
  unfold yP
  simp only [eval_listSum, List.map_map]
  refine List.sum_eq_zero fun x hx ↦ ?_
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
  simp

theorem eval_yP_sum (a : Array (Array K)) (l : ℕ) {ι : Type} (s : Finset ι) (f : ι → E) :
    (yP a l).eval (∑ i ∈ s, f i) = ∑ i ∈ s, (yP a l).eval (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eval_yP_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, eval_yP_add, ih]

/-- `y_l(β_k) = [l = k]`. -/
theorem eval_yP_beta {r : ℕ} (hf : FunctionalsCorrect r) {l k : ℕ} (hl : l < r) (hk : k < r) :
    (yP (coordinateFunctionals r) l).eval (ofK (beta.getD k 0)) = if l = k then 1 else 0 := by
  have h := hf.2 l hl k hk
  have h' := congrArg ofK h
  unfold yP
  simp only [eval_listSum, List.map_map]
  rw [hf.1]
  convert h' using 1
  · show _ = algebraMap K E _
    rw [map_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun m _ ↦ ?_
    simp only [Function.comp_apply, Polynomial.eval_mul, eval_C, eval_pow, eval_X, frobK_eq, map_mul,
      map_pow]
    rfl
  · split_ifs <;> simp

/-- **`y_l(ω_x) = x_l`** on `V_r`. -/
theorem eval_yP_pointE (h : BetaCantor) {r : ℕ} (hf : FunctionalsCorrect r) (hr : r ≤ 24) {l x : ℕ}
    (hl : l < r) (hx : x < 2 ^ r) :
    (yP (coordinateFunctionals r) l).eval (pointE x) = bitE x l := by
  have hx24 : x < 2 ^ 24 := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hr)
  rw [pointE_eq_omega h hx24]
  unfold Heap.omega
  rw [← Finset.sum_range_add_sum_Ico _ hr, eval_yP_add]
  have hz : ∑ k ∈ Ico r 24, (if x.testBit k then (cantorE h).β k else 0) = 0 :=
    Finset.sum_eq_zero fun k hk ↦ by
      rw [Finset.mem_Ico] at hk
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk.1))]
      simp
  rw [hz, eval_yP_zero, add_zero, eval_yP_sum]
  have hterm : ∀ k ∈ range r, (yP (coordinateFunctionals r) l).eval
      (if x.testBit k then (cantorE h).β k else 0) = if k = l then bitE x k else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hb : x.testBit k
    · simp only [hb, ite_true]
      show (yP (coordinateFunctionals r) l).eval (ofK (beta.getD k 0)) = _
      rw [eval_yP_beta hf hl hk]
      unfold bitE
      by_cases hkl : k = l
      · subst hkl; simp [hb]
      · simp [hkl, Ne.symm hkl]
    · simp only [hb, Bool.false_eq_true, ite_false, eval_yP_zero]
      unfold bitE
      simp [hb]
  rw [Finset.sum_congr rfl hterm]
  simp [Finset.sum_ite_eq', hl]

/-! ## Claims at cube points, the slot view, the lift -/

theorem one_add_bitE (a b : ℕ) (l : ℕ) :
    (1 + bitE a l + if b.testBit l then 1 else 0 : E) = if a.testBit l = b.testBit l then 1 else 0 := by
  unfold bitE
  cases a.testBit l <;> cases b.testBit l <;> simp [CharTwo.add_self_eq_zero]

/-- **A claim at a cube point is the word there.** -/
theorem cubeEq_eq_ite (p : List E) (n i j : ℕ) (hp : ∀ l < n, p.getD l 0 = bitE j l) (hi : i < 2 ^ n)
    (hj : j < 2 ^ n) : cubeEq p n i = if i = j then 1 else 0 := by
  unfold cubeEq
  rw [Finset.prod_congr rfl fun l hl ↦ by rw [hp l (Finset.mem_range.mp hl), one_add_bitE]]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [ite_eq_right hij]
    have : ∃ l < n, j.testBit l ≠ i.testBit l := by
      by_contra hne
      simp only [not_exists, not_and, not_not] at hne
      apply hij
      refine Nat.eq_of_testBit_eq fun l ↦ ?_
      by_cases hl : l < n
      · exact (hne l hl).symm
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    obtain ⟨l, hl, hne⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hl) (by simp [hne])

/-- `w_m / w_r` is `1` on `V_r`. -/
theorem liftP_eval_pointE (h : BetaCantor) (r m x : ℕ) (hx : x < 2 ^ r) (hx24 : x < 2 ^ 24) :
    (liftP r m).eval (pointE x) = 1 := by
  unfold liftP
  rw [eval_list_prod_of]
  rw [List.map_map]
  refine List.prod_eq_one fun e he ↦ ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  rw [List.mem_range'_1] at hj
  simp only [Function.comp_apply]
  rw [Polynomial.eval_add, eval_one, eval_digitP_pointE h j hx24,
    show x >>> j = 0 by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hj.1)),
    pointE_zero, zero_add]

/-! ## `C1`'s columns at the points -/

theorem limbs_mem_blocks {L : StackLayout} {col : Column} {b : ℕ × ℕ × ℕ} (hb : b ∈ L.limbs col) :
    (col, b.1, b.2.1, b.2.2) ∈ L.blocks := by
  unfold StackLayout.limbs at hb
  obtain ⟨⟨c', limb, vars, offset⟩, hm, he⟩ := List.mem_filterMap.mp hb
  by_cases hc : c' = col
  · subst hc
    simp only [beq_self_eq_true, ite_true, Option.some.injEq] at he
    subst he
    exact hm
  · simp [hc] at he

end UniSound.Ids
