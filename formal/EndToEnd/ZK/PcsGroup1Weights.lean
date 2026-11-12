-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsGroup1Alg
import E2ECompleteness.PcsHValues
import E2ECompleteness.PcsHCoset

/-!
# Group 1: the weights of the cells

The cells `v` (`2^m` words, `m ≤ 24`) enter `W`'s out-of-domain answer and the values at `t` through
their coefficients `c = coefficients m 0 v` (novel basis). Both are sums over the cells with weights in product form,
`pᵢ_b = B(⌊i / 2^b⌋)` the digits of the cell `i`'s point (`w_b(B(i)) = B(⌊i / 2^b⌋)`, the Cantor basis):

* `sum_prod_gen`: the interpolation identity on the grid of digits, `Σ_i Π_b [j_b ? pᵢ_b : 1] (α_b + β_b pᵢ_b) =
  Π_b [j_b ? α_b + β_b : β_b]`, by the parity of `i` (`p(2k + 1) = p(2k) + 1`);
* **`tableEval_coefficients`**: `W`'s answer at `z` is `Σ_i vᵢ Π_b (1 + (1 + z_b) pᵢ_b)`;
* **`nov_coefficients_eval`**: the cells' polynomial at `x ∈ E` is `Σ_i vᵢ Λᵢ(x)`, `Λᵢ(x) = Π_b (1 + w_b(x) + pᵢ_b)`;
* `lam_mul`: `Λᵢ(x) (x + B(i)) = w_24(x)` (`(1 + w_b) w_b = w_{b+1}`), so `Λᵢ(x) = w_24(x) / (x + B(i))` off `K`
  (the Lagrange weight), and `Σ_i Λᵢ = 1`;
* **`valuesAt_cells`**: the values at `t` are the cells' polynomial at `t`, `t + θ`, and `t + 1` plus `t + θ + 1`.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open PcsQuotient.Domain QuotientSecurity Finset

namespace PcsQuotient.EndToEnd.Group1

/-- The point of index `n`, in `E`. -/
noncomputable def pt (n : ℕ) : E := ofK (point n)

theorem pt_zero : pt 0 = 0 := by rw [pt, E2ECompleteness.Pcs.H.point_zero, ofK_zero]

theorem hCantor : Bridge.Ntt.CantorUpTo 24 := E2ECompleteness.Pcs.H.cantorUpTo (by norm_num)

theorem pt_odd (k : ℕ) : pt (2 * k + 1) = pt (2 * k) + 1 := by
  rw [pt, pt, Bridge.Ntt.point_two_mul_add_one hCantor.1, ofK_add, ofK_one]

/-- `w_b(B(i)) = B(⌊i / 2^b⌋)` in `E`. -/
theorem sq_iterate_pt {i : ℕ} (hi : i < 2 ^ 24) {b : ℕ} (hb : b ≤ 24) : sq^[b] (pt i) = pt (i / 2 ^ b) := by
  rw [pt, ← E2ECompleteness.Pcs.H.ofK_S_iterate, Bridge.Ntt.iterate_point hCantor (by unfold basisSize; omega) hi hb]
  rfl

/-! ### The interpolation identity -/

theorem div_two_pow_succ (i e b : ℕ) (he : e < 2) : (2 * i + e) / 2 ^ (b + 1) = i / 2 ^ b := by
  rw [pow_succ', ← Nat.div_div_eq_div_mul, show (2 * i + e) / 2 = i by omega]

/-- **The interpolation identity** on the grid of digits. -/
theorem sum_prod_gen (p : ℕ → E) (hp : ∀ k, p (2 * k + 1) = p (2 * k) + 1) :
    ∀ (m : ℕ) (α β : ℕ → E) (j : ℕ),
      ∑ i ∈ range (2 ^ m), ∏ b ∈ range m,
          ((if j.testBit b then p (i / 2 ^ b) else 1) * (α b + β b * p (i / 2 ^ b))) =
        ∏ b ∈ range m, (if j.testBit b then α b + β b else β b)
  | 0, α, β, j => by simp
  | m + 1, α, β, j => by
    rw [E2ECompleteness.Pcs.Novel.sum_range_two_pow_succ, ← Finset.sum_add_distrib, prod_range_succ']
    have hsplit : ∀ i e, e < 2 → ∏ b ∈ range (m + 1),
        ((if j.testBit b then p ((2 * i + e) / 2 ^ b) else 1) * (α b + β b * p ((2 * i + e) / 2 ^ b))) =
        ((if j.testBit 0 then p (2 * i + e) else 1) * (α 0 + β 0 * p (2 * i + e))) *
          ∏ b ∈ range m, ((if (j / 2).testBit b then p (i / 2 ^ b) else 1) *
            (α (b + 1) + β (b + 1) * p (i / 2 ^ b))) := by
      intro i e he
      rw [prod_range_succ', mul_comm, pow_zero, Nat.div_one]
      refine congrArg (fun P ↦ _ * P) (prod_congr rfl fun b _ ↦ ?_)
      rw [div_two_pow_succ i e b he, Nat.testBit_succ]
    have h0 : ∀ i, ∏ b ∈ range (m + 1),
        ((if j.testBit b then p ((2 * i) / 2 ^ b) else 1) * (α b + β b * p ((2 * i) / 2 ^ b))) =
        ((if j.testBit 0 then p (2 * i) else 1) * (α 0 + β 0 * p (2 * i))) *
          ∏ b ∈ range m, ((if (j / 2).testBit b then p (i / 2 ^ b) else 1) *
            (α (b + 1) + β (b + 1) * p (i / 2 ^ b))) := fun i ↦ by
      simpa using hsplit i 0 (by norm_num)
    simp only [h0, hsplit _ 1 (by norm_num), ← add_mul]
    have hf : ∀ i, (if j.testBit 0 then p (2 * i) else 1) * (α 0 + β 0 * p (2 * i)) +
        (if j.testBit 0 then p (2 * i + 1) else 1) * (α 0 + β 0 * p (2 * i + 1)) =
        if j.testBit 0 then α 0 + β 0 else β 0 := fun i ↦ by
      rw [hp]
      split_ifs
      · linear_combination (p (2 * i) * α 0 + β 0 * p (2 * i) * p (2 * i) + β 0 * p (2 * i)) * two_E
      · linear_combination (α 0 + β 0 * p (2 * i)) * two_E
    simp only [hf, ← Finset.mul_sum]
    rw [sum_prod_gen p hp m (fun b ↦ α (b + 1)) (fun b ↦ β (b + 1)) (j / 2), mul_comm]
    congr 1
    refine prod_congr rfl fun b _ ↦ ?_
    rw [Nat.testBit_succ]

/-! ### The coefficients' sums as sums over the cells -/

theorem ofK_X (m j : ℕ) (x : K) :
    ofK (Bridge.Ntt.X m j x) = ∏ b ∈ range m, if j.testBit b then ofK (S^[b] x) else 1 := by
  rw [Bridge.Ntt.X, E2ECompleteness.Pcs.H.ofK_prod]
  refine prod_congr rfl fun b _ ↦ ?_
  split_ifs
  · rfl
  · exact ofK_one

/-- **A cell is its coefficients' sum** with the digit weights. -/
theorem ofK_cell (m : ℕ) (hm : m ≤ 24) (A : Array K) (hA : A.size = 2 ^ m) {i : ℕ} (hi : i < 2 ^ m) :
    ofK (A.getD i 0) = ∑ j ∈ range (2 ^ m), ofK ((coefficients m 0 A).getD j 0) *
      ∏ b ∈ range m, if j.testBit b then pt (i / 2 ^ b) else 1 := by
  have hi24 : i < 2 ^ 24 := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hm)
  conv_lhs => rw [← Bridge.Ntt.values_coefficients_K m 0 A hA]
  rw [Bridge.Ntt.values_getD_K (E2ECompleteness.Pcs.H.cantorUpTo (by omega)) (by unfold basisSize; omega) 0 _
    (by rw [Bridge.Ntt.coefficients_size, hA]) hi, zero_add, E2ECompleteness.Pcs.H.ofK_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [ofK_mul, ofK_X, mul_comm]
  congr 1
  refine prod_congr rfl fun b hb ↦ ?_
  have hb' : b ≤ 24 := by have := mem_range.1 hb; omega
  split_ifs
  · rw [E2ECompleteness.Pcs.H.ofK_S_iterate, ← pt, sq_iterate_pt hi24 hb']
  · rfl

/-- **The coefficients' sum with product weights is the cells' sum with the grid's weights.** -/
theorem sum_coeffs (m : ℕ) (hm : m ≤ 24) (A : Array K) (hA : A.size = 2 ^ m) (α β : ℕ → E) :
    ∑ j ∈ range (2 ^ m), ofK ((coefficients m 0 A).getD j 0) *
        ∏ b ∈ range m, (if j.testBit b then α b + β b else β b) =
      ∑ i ∈ range (2 ^ m), ofK (A.getD i 0) * ∏ b ∈ range m, (α b + β b * pt (i / 2 ^ b)) := by
  have hR : ∀ i ∈ range (2 ^ m), ofK (A.getD i 0) * ∏ b ∈ range m, (α b + β b * pt (i / 2 ^ b)) =
      ∑ j ∈ range (2 ^ m), ofK ((coefficients m 0 A).getD j 0) *
        ∏ b ∈ range m, ((if j.testBit b then pt (i / 2 ^ b) else 1) * (α b + β b * pt (i / 2 ^ b))) := by
    intro i hi
    rw [ofK_cell m hm A hA (mem_range.1 hi), sum_mul]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [prod_mul_distrib, mul_assoc]
  rw [sum_congr rfl hR, sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← mul_sum, sum_prod_gen pt pt_odd m α β j]

/-- **`W`'s answer at `z` as a sum over the cells.** -/
theorem tableEval_coefficients (m : ℕ) (hm : m ≤ 24) (A : Array K) (hA : A.size = 2 ^ m) (z : List E)
    (hz : z.length = m) :
    tableEval (coefficients m 0 A) z =
      ∑ i ∈ range (2 ^ m), ofK (A.getD i 0) * ∏ b ∈ range m, (1 + (1 + xc z b) * pt (i / 2 ^ b)) := by
  rw [tableEval_sum _ m (by rw [Bridge.Ntt.coefficients_size, hA]) z hz, ← sum_coeffs m hm A hA]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [eqEval_boolPoint_prod m j z hz]
  refine congrArg (fun P ↦ _ * P) (prod_congr rfl fun b _ ↦ ?_)
  unfold fz
  split_ifs
  · linear_combination (-1 : E) * two_E
  · rfl

/-- `Λᵢ(x)`: the weight of cell `i` in the cells' polynomial at `x`. -/
noncomputable def lam (x : E) (i : ℕ) : E := ∏ b ∈ range 24, (1 + sq^[b] x + pt (i / 2 ^ b))

/-- The cells' polynomial at `x ∈ E` as a sum over the cells, `2^m` of them. -/
theorem nov_coefficients_eval' (m : ℕ) (hm : m ≤ 24) (A : Array K) (hA : A.size = 2 ^ m) (x : E) :
    (E2ECompleteness.Pcs.Novel.nov 0 m fun j ↦ ofK ((coefficients m 0 A).getD j 0)).eval x =
      ∑ i ∈ range (2 ^ m), ofK (A.getD i 0) * ∏ b ∈ range m, (1 + sq^[b] x + pt (i / 2 ^ b)) := by
  rw [E2ECompleteness.Pcs.H.nov_eval]
  have h := sum_coeffs m hm A hA (fun b ↦ 1 + sq^[b] x) (fun _ ↦ 1)
  simp only [one_mul] at h
  rw [← h]
  refine sum_congr rfl fun j _ ↦ ?_
  refine congrArg (fun P ↦ _ * P) (prod_congr rfl fun b _ ↦ ?_)
  split_ifs
  · linear_combination (-1 : E) * two_E
  · rfl

/-- **The cells' polynomial at `x ∈ E` as a sum over the cells.** -/
theorem nov_coefficients_eval (A : Array K) (hA : A.size = 2 ^ 24) (x : E) :
    (E2ECompleteness.Pcs.Novel.nov 0 24 fun j ↦ ofK ((coefficients 24 0 A).getD j 0)).eval x =
      ∑ i ∈ range (2 ^ 24), ofK (A.getD i 0) * lam x i :=
  nov_coefficients_eval' 24 le_rfl A hA x

/-! ### The weights in closed form -/

/-- `(Π_{b < B} (1 + w_b(y))) · y = w_B(y)`. -/
theorem telescope (y : E) : ∀ B : ℕ, (∏ b ∈ range B, (1 + sq^[b] y)) * y = sq^[B] y
  | 0 => by simp
  | B + 1 => by
    have IH := telescope y B
    rw [prod_range_succ, Function.iterate_succ_apply']
    calc (∏ b ∈ range B, (1 + sq^[b] y)) * (1 + sq^[B] y) * y
        = (1 + sq^[B] y) * ((∏ b ∈ range B, (1 + sq^[b] y)) * y) := by ring
      _ = (1 + sq^[B] y) * sq^[B] y := by rw [IH]
      _ = QuotientSecurity.sq (sq^[B] y) := by unfold QuotientSecurity.sq; ring

/-- **`Λᵢ(x) (x + B(i)) = w_24(x)`.** -/
theorem lam_mul (x : E) {i : ℕ} (hi : i < 2 ^ 24) : lam x i * (x + pt i) = sq^[24] x := by
  have hf : ∀ b ∈ range 24, 1 + sq^[b] x + pt (i / 2 ^ b) = 1 + sq^[b] (x + pt i) := fun b hb ↦ by
    rw [sq_iterate_add, sq_iterate_pt hi (by have := mem_range.1 hb; omega), add_assoc]
  rw [lam, prod_congr rfl hf, telescope, sq_iterate_add, sq_iterate_pt hi le_rfl,
    Nat.div_eq_of_lt hi, pt_zero, add_zero]

/-- **The weights sum to `1`.** -/
theorem sum_lam (x : E) : ∑ i ∈ range (2 ^ 24), lam x i = 1 := by
  have h := sum_prod_gen pt pt_odd 24 (fun b ↦ 1 + sq^[b] x) (fun _ ↦ 1) 0
  simp only [Nat.zero_testBit, Bool.false_eq_true, ite_false, one_mul, prod_const_one] at h
  unfold lam
  exact h

/-! ### The values at `t` -/

/-- `θ = β₁`, in `E`. -/
noncomputable def θE : E := ofK (betaAt 1)

theorem θE_sq : θE * θE + θE + 1 = 0 :=
  QuotientSecurity.cantor_theta E2ECompleteness.Pcs.H.BE (by norm_num)

theorem sq_θE : QuotientSecurity.sq θE = 1 := by
  unfold QuotientSecurity.sq; linear_combination θE_sq - two_E

theorem sq_one : QuotientSecurity.sq (1 : E) = 0 := by
  unfold QuotientSecurity.sq; linear_combination two_E

theorem sq_zero : QuotientSecurity.sq (0 : E) = 0 := by
  unfold QuotientSecurity.sq; ring

/-- One coordinate split off a novel-basis sum. -/
theorem sum_split_one (m : ℕ) (f : ℕ → E) (d : ℕ → E) :
    ∑ i ∈ range (2 ^ (m + 1)), f i * ∏ k ∈ range (m + 1), (if i.testBit k then d k else 1) =
      ∑ i ∈ range (2 ^ m), (f (2 * i) + f (2 * i + 1) * d 0) *
        ∏ k ∈ range m, (if i.testBit k then d (k + 1) else 1) := by
  rw [E2ECompleteness.Pcs.Novel.sum_range_two_pow_succ, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [prod_range_succ', prod_range_succ']
  have h0 : (2 * i).testBit 0 = false := by simp [Nat.testBit_zero]
  have h1 : (2 * i + 1).testBit 0 = true := by simp [Nat.testBit_zero]
  have hs0 : ∀ k, (2 * i).testBit (k + 1) = i.testBit k := fun k ↦ by
    rw [Nat.testBit_succ]; congr 1; omega
  have hs1 : ∀ k, (2 * i + 1).testBit (k + 1) = i.testBit k := fun k ↦ by
    rw [Nat.testBit_succ]; congr 1; omega
  simp only [h0, h1, hs0, hs1, Bool.false_eq_true, ite_true, ite_false]
  ring

/-- **The cells' polynomial by its row polynomials**: `w = a₀ + x a₁ + w₁ (a₂ + x a₃)`, `a_j` the polynomial of the
coefficients `4 i + j` at `w₂(x)`. -/
theorem nov_split (m : ℕ) (f : ℕ → E) (x : E) :
    (E2ECompleteness.Pcs.Novel.nov 0 (m + 2) f).eval x =
      (E2ECompleteness.Pcs.Novel.nov 0 m fun i ↦ f (4 * i)).eval (sq^[2] x) +
      x * (E2ECompleteness.Pcs.Novel.nov 0 m fun i ↦ f (4 * i + 1)).eval (sq^[2] x) +
      QuotientSecurity.sq x * (E2ECompleteness.Pcs.Novel.nov 0 m fun i ↦ f (4 * i + 2)).eval (sq^[2] x) +
      x * QuotientSecurity.sq x * (E2ECompleteness.Pcs.Novel.nov 0 m fun i ↦ f (4 * i + 3)).eval (sq^[2] x) := by
  simp only [E2ECompleteness.Pcs.H.nov_eval]
  rw [sum_split_one (m + 1), sum_split_one m, mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  have hp : ∏ k ∈ range m, (if i.testBit k then sq^[k + 1 + 1] x else 1) =
      ∏ k ∈ range m, (if i.testBit k then sq^[k] (sq^[2] x) else 1) :=
    prod_congr rfl fun k _ ↦ by rw [← Function.iterate_add_apply]
  rw [hp, show 2 * (2 * i) + 1 = 4 * i + 1 by ring, show 2 * (2 * i + 1) + 1 = 4 * i + 3 by ring,
    show 2 * (2 * i + 1) = 4 * i + 2 by ring, show 2 * (2 * i) = 4 * i by ring]
  simp only [Function.iterate_zero, id, zero_add, Function.iterate_one]
  ring

/-- `w₂` is constant on a row: `w₂(t + θ) = w₂(t + 1) = w₂(t)`. -/
theorem sq2_θ (t : E) : sq^[2] (t + θE) = sq^[2] t := by
  rw [sq_iterate_add]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, sq_θE, sq_one, add_zero]

theorem sq2_one (t : E) : sq^[2] (t + 1) = sq^[2] t := by
  rw [sq_iterate_add]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, sq_one, sq_zero, add_zero]

/-- **The values at `t` are the cells' polynomial at `t`, `t + θ`, and `t + 1` plus `t + θ + 1`.** -/
theorem valuesAt_cells (cir : Circuit) (hl : cir.logRows = 22) (cells₀ : Array K) (coins : Coins) (t : E) :
    (valuesAt cir cells₀ coins t).1[0] =
        (E2ECompleteness.Pcs.Novel.nov 0 24 fun j ↦ ofK ((witnessParts cir cells₀ coins).2.getD j 0)).eval t ∧
      (valuesAt cir cells₀ coins t).1[1] =
        (E2ECompleteness.Pcs.Novel.nov 0 24 fun j ↦ ofK ((witnessParts cir cells₀ coins).2.getD j 0)).eval
          (t + θE) ∧
      (valuesAt cir cells₀ coins t).1[2] =
        (E2ECompleteness.Pcs.Novel.nov 0 24 fun j ↦ ofK ((witnessParts cir cells₀ coins).2.getD j 0)).eval
          (t + 1) +
        (E2ECompleteness.Pcs.Novel.nov 0 24 fun j ↦ ofK ((witnessParts cir cells₀ coins).2.getD j 0)).eval
          (t + θE + 1) := by
  rw [E2ECompleteness.Pcs.H.valuesAt_fst cir cells₀ coins hl t]
  generalize (witnessParts cir cells₀ coins).2 = wh
  have hn := nov_split 22 (fun j ↦ ofK (wh.getD j 0))
  set a : Fin 4 → E := fun j ↦ (E2ECompleteness.Pcs.Novel.nov 0 22 fun i ↦
    ofK (wh.getD (↑j + 4 * i) 0)).eval (sq^[2] t) with ha_def
  have ha : ∀ (j : Fin 4) (r : ℕ), (j : ℕ) = r →
      a j = (E2ECompleteness.Pcs.Novel.nov 0 22 fun i ↦ ofK (wh.getD (4 * i + r) 0)).eval (sq^[2] t) :=
    fun j r hj ↦ by
      subst hj; simp only [ha_def]; congr 2; funext i; rw [add_comm]
  have e0 : (Vector.ofFn (Kc3.rowVals (ofK (betaAt 1)) t a))[0] =
      a 0 + t * a 1 + QuotientSecurity.sq t * a 2 + QuotientSecurity.sq t * t * a 3 := rfl
  have e1 : (Vector.ofFn (Kc3.rowVals (ofK (betaAt 1)) t a))[1] =
      a 0 + (t + θE) * a 1 + (QuotientSecurity.sq t + 1) * a 2 + (QuotientSecurity.sq t + 1) * (t + θE) * a 3 :=
    rfl
  have e2 : (Vector.ofFn (Kc3.rowVals (ofK (betaAt 1)) t a))[2] =
      θE * a 1 + a 2 + (t + θE * QuotientSecurity.sq t + θE + 1) * a 3 := rfl
  rw [e0, e1, e2, ha 0 0 rfl, ha 1 1 rfl, ha 2 2 rfl, ha 3 3 rfl]
  simp only [Nat.add_zero]
  have hn' : ∀ x, (E2ECompleteness.Pcs.Novel.nov 0 24 fun j ↦ ofK (wh.getD j 0)).eval x = _ := hn
  rw [hn' t, hn' (t + θE), hn' (t + 1), hn' (t + θE + 1), sq2_θ, sq2_one,
    show t + θE + 1 = (t + 1) + θE by ring, sq2_θ, sq2_one]
  have hs1 : QuotientSecurity.sq (t + 1) = QuotientSecurity.sq t := by rw [sq_add, sq_one, add_zero]
  have hsθ : QuotientSecurity.sq (t + θE) = QuotientSecurity.sq t + 1 := by rw [sq_add, sq_θE]
  have hsθ1 : QuotientSecurity.sq (t + 1 + θE) = QuotientSecurity.sq t + 1 := by rw [sq_add, hs1, sq_θE]
  rw [hs1, hsθ, hsθ1]
  refine ⟨by ring, by ring, ?_⟩
  linear_combination (norm := char2_norm)

end PcsQuotient.EndToEnd.Group1
