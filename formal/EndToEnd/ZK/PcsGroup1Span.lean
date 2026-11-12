-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsGroup1Unif

/-!
# Group 1: the random-rows map is onto off a small set of challenges

* `surj_of_steps`: four `K`-linear maps `L_W, L_C, L_{V+Y}, L_X` onto `E⁴`, by steps: three vectors whose `P = X + C +
  (V + Y)` values are independent; three with `P = 0` whose `V + Y` values are; three with `P = V + Y = 0` whose `C`
  values are; three with `P = V + Y = C = 0` whose `W` values are.
* The value weights off `K` (`lam_closed`): `Λᵢ(t + δ) = w₂₄(t) / (t + δ + B(i))`, so a random row's words weigh, with
  `s = t + B(4R)`, `φ_m = w₂₄(t) / (s + B(m))`: `r`-word `X, C`: `φ₁ + φ₃`, `V + Y`: `0`; `s`-word of a sum row `P`: `0`,
  `V + Y`: `φ₀ + φ₁ + φ₂ + φ₃`; `s`-word of a select or pass row `P`: `φ₀ + φ₁ + φ₂ + φ₃`. In closed form
  `Σ φ = w₂₄(t) / (w₂(t) + B(R))` and `φ₁ + φ₃ = w₂₄(t) θ / (t² + θ t + δ_R)`, `δ_R ∈ K`.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open PcsQuotient.Domain QuotientSecurity Finset

namespace PcsQuotient.EndToEnd.Group1

/-! ### Onto by steps -/

theorem lin3 {V : Type*} [AddCommGroup V] [Module K V] (L : V →ₗ[K] E) (f : Fin 3 → V) (a b c : K) :
    L (a • f 0 + b • f 1 + c • f 2) = ofK a * L (f 0) + ofK b * L (f 1) + ofK c * L (f 2) := by
  simp only [map_add, map_smul, Algebra.smul_def, ← ofK_eq]

/-- **Four `K`-linear maps onto `E⁴`, by steps.** -/
theorem surj_of_steps {V : Type*} [AddCommGroup V] [Module K V] (LW LC LVY LX : V →ₗ[K] E)
    (p v c k : Fin 3 → V)
    (hP : Indep3 (LX (p 0) + LC (p 0) + LVY (p 0)) (LX (p 1) + LC (p 1) + LVY (p 1))
      (LX (p 2) + LC (p 2) + LVY (p 2)))
    (hv0 : ∀ i, LX (v i) + LC (v i) + LVY (v i) = 0) (hV : Indep3 (LVY (v 0)) (LVY (v 1)) (LVY (v 2)))
    (hc0 : ∀ i, LX (c i) + LC (c i) + LVY (c i) = 0 ∧ LVY (c i) = 0)
    (hC : Indep3 (LC (c 0)) (LC (c 1)) (LC (c 2)))
    (hk0 : ∀ i, LX (k i) + LC (k i) + LVY (k i) = 0 ∧ LVY (k i) = 0 ∧ LC (k i) = 0)
    (hW : Indep3 (LW (k 0)) (LW (k 1)) (LW (k 2))) (y : E × E × E × E) :
    ∃ x : V, (LW x, LC x, LVY x, LX x) = y := by
  obtain ⟨yW, yC, yVY, yX⟩ := y
  obtain ⟨a0, a1, a2, ha⟩ := hP.spans (yX + yC + yVY)
  set σ1 := a0 • p 0 + a1 • p 1 + a2 • p 2
  obtain ⟨b0, b1, b2, hb⟩ := hV.spans (yVY - LVY σ1)
  set σ2 := b0 • v 0 + b1 • v 1 + b2 • v 2
  obtain ⟨c0, c1, c2, hc⟩ := hC.spans (yC - LC σ1 - LC σ2)
  set σ3 := c0 • c 0 + c1 • c 1 + c2 • c 2
  obtain ⟨d0, d1, d2, hd⟩ := hW.spans (yW - LW σ1 - LW σ2 - LW σ3)
  set σ4 := d0 • k 0 + d1 • k 1 + d2 • k 2
  have P1 : LX σ1 + LC σ1 + LVY σ1 = yX + yC + yVY := by
    rw [← ha, lin3, lin3, lin3]; ring
  have P2 : LX σ2 + LC σ2 + LVY σ2 = 0 := by
    rw [lin3, lin3, lin3]
    linear_combination ofK b0 * hv0 0 + ofK b1 * hv0 1 + ofK b2 * hv0 2
  have V2 : LVY σ2 = yVY - LVY σ1 := by rw [← hb, lin3]
  have P3 : LX σ3 + LC σ3 + LVY σ3 = 0 := by
    rw [lin3, lin3, lin3]
    linear_combination ofK c0 * (hc0 0).1 + ofK c1 * (hc0 1).1 + ofK c2 * (hc0 2).1
  have V3 : LVY σ3 = 0 := by rw [lin3, (hc0 0).2, (hc0 1).2, (hc0 2).2]; ring
  have C3 : LC σ3 = yC - LC σ1 - LC σ2 := by rw [← hc, lin3]
  have P4 : LX σ4 + LC σ4 + LVY σ4 = 0 := by
    rw [lin3, lin3, lin3]
    linear_combination ofK d0 * (hk0 0).1 + ofK d1 * (hk0 1).1 + ofK d2 * (hk0 2).1
  have V4 : LVY σ4 = 0 := by rw [lin3, (hk0 0).2.1, (hk0 1).2.1, (hk0 2).2.1]; ring
  have C4 : LC σ4 = 0 := by rw [lin3, (hk0 0).2.2, (hk0 1).2.2, (hk0 2).2.2]; ring
  have W4 : LW σ4 = yW - LW σ1 - LW σ2 - LW σ3 := by rw [← hd, lin3]
  refine ⟨σ1 + σ2 + σ3 + σ4, ?_⟩
  simp only [map_add]
  have eW : LW σ1 + LW σ2 + LW σ3 + LW σ4 = yW := by rw [W4]; ring
  have eC : LC σ1 + LC σ2 + LC σ3 + LC σ4 = yC := by rw [C3, C4]; ring
  have eV : LVY σ1 + LVY σ2 + LVY σ3 + LVY σ4 = yVY := by rw [V2, V3, V4]; ring
  have eX : LX σ1 + LX σ2 + LX σ3 + LX σ4 = yX := by
    linear_combination P1 + P2 + P3 + P4 - eC - eV
  rw [eW, eC, eV, eX]

/-! ### Points -/

theorem add_eq_xor (c a b : ℕ) (hb : b < 2 ^ c) : 2 ^ c * a + b = 2 ^ c * a ^^^ b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add a hb, show 2 ^ c * a = 2 ^ c * a + 0 by ring,
    Nat.testBit_two_pow_mul_add a (Nat.two_pow_pos c)]
  split_ifs with h
  · simp
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp

/-- `B(2^c a + b) = B(2^c a) + B(b)` for `b < 2^c`. -/
theorem pt_split (c a b : ℕ) (hb : b < 2 ^ c) : pt (2 ^ c * a + b) = pt (2 ^ c * a) + pt b := by
  rw [add_eq_xor c a b hb, pt, E2ECompleteness.Pcs.H.point_xor_low, ofK_add]; rfl

theorem pt_xor (a b : ℕ) : pt (a ^^^ b) = pt a + pt b := by
  rw [pt, E2ECompleteness.Pcs.H.point_xor_low, ofK_add]; rfl

theorem pt_one : pt 1 = 1 := by rw [pt, E2ECompleteness.Pcs.H.point_one, ofK_one]

theorem pt_two : pt 2 = θE := by rw [pt, E2ECompleteness.Pcs.H.point_two]; rfl

theorem pt_three : pt 3 = 1 + θE := by rw [pt, E2ECompleteness.Pcs.H.point_three, ofK_add, ofK_one]; rfl

theorem S_iterate_zero (h : ℕ) : S^[h] (0 : K) = 0 :=
  Function.iterate_fixed (by unfold S; ring) h

/-- **A nonzero index has a nonzero point**: `w_h` of it, `h` its top bit, is `1`. -/
theorem point_ne_zero {n : ℕ} (h0 : n ≠ 0) (hn : n < 2 ^ 24) : point n ≠ 0 := by
  intro hp
  have hh : n.log2 ≤ 24 := by
    have := Nat.log2_self_le h0
    by_contra hc
    have : 2 ^ 24 < 2 ^ n.log2 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hdiv : n / 2 ^ n.log2 = 1 :=
    Nat.div_eq_of_lt_le (by rw [one_mul]; exact Nat.log2_self_le h0) (by rw [show (1 + 1) * 2 ^ n.log2 = 2 ^ (n.log2 + 1) by ring]; exact Nat.lt_log2_self)
  have := Bridge.Ntt.iterate_point hCantor (by unfold basisSize; omega) hn hh
  rw [hp, S_iterate_zero, hdiv, E2ECompleteness.Pcs.H.point_one] at this
  exact zero_ne_one this

/-- Distinct indices below `2^24` have distinct points. -/
theorem point_ne {a b : ℕ} (hab : a ≠ b) (ha : a < 2 ^ 24) (hb : b < 2 ^ 24) : point a ≠ point b := by
  intro h
  have hx : a ^^^ b ≠ 0 := fun h0 ↦ hab (Nat.eq_of_testBit_eq fun i ↦ by
    have := congrArg (Nat.testBit · i) h0
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    revert this; cases a.testBit i <;> cases b.testBit i <;> decide)
  have hlt : a ^^^ b < 2 ^ 24 := Nat.xor_lt_two_pow ha hb
  refine point_ne_zero hx hlt ?_
  rw [E2ECompleteness.Pcs.H.point_xor_low, h]
  exact CharTwo.add_self_eq_zero _

/-! ### The value weights off `K` -/

/-- `w₂₄(t)`, the value weights' common factor. -/
noncomputable def μt (t : E) : E := sq^[24] t

theorem sq24_pt {d : ℕ} (hd : d < 2 ^ 24) : sq^[24] (pt d) = 0 := by
  rw [sq_iterate_pt hd le_rfl, Nat.div_eq_of_lt hd, pt_zero]

/-- **The value weights off `K`**: `Λᵢ(t + B(d)) = w₂₄(t) / (t + B(d) + B(i))`. -/
theorem lam_closed {t : E} (ht : ¬ InK t) {d i : ℕ} (hd : d < 2 ^ 24) (hi : i < 2 ^ 24) :
    lam (t + pt d) i = μt t / (t + pt d + pt i) := by
  have hne : t + pt d + pt i ≠ 0 := by
    rw [add_assoc, pt, pt, ← ofK_add]; exact add_ofK_ne_zero ht _
  rw [eq_div_iff hne, lam_mul _ hi, sq_iterate_add, sq24_pt hd, add_zero]; rfl

/-- **`w₂₄(t) ≠ 0` off `K`**: the weights sum to `1`. -/
theorem μt_ne_zero {t : E} (ht : ¬ InK t) : μt t ≠ 0 := by
  intro h0
  have h := sum_lam t
  rw [sum_eq_zero fun i hi ↦ by
    rw [show t = t + pt 0 by rw [pt_zero, add_zero], lam_closed ht (by norm_num) (mem_range.1 hi), h0, zero_div]] at h
  exact zero_ne_one h

/-- `φ_m = w₂₄(t) / (t + B(4R) + B(m))`. -/
noncomputable def φ (t : E) (R m : ℕ) : E := μt t / (t + pt (4 * R) + pt m)

theorem lam_cell {t : E} (ht : ¬ InK t) {d R j : ℕ} (hd : d < 4) (hR : R < 2 ^ 22) (hj : j < 4) :
    lam (t + pt d) (4 * R + j) = φ t R (d ^^^ j) := by
  rw [lam_closed ht (by omega) (by omega), φ, pt_xor, show 4 * R + j = 2 ^ 2 * R + j by ring,
    pt_split 2 R j (by norm_num; omega), show 2 ^ 2 * R = 4 * R by ring]
  rw [show t + pt d + (pt (4 * R) + pt j) = t + pt (4 * R) + (pt d + pt j) by ring]

theorem wX_cell {t : E} (ht : ¬ InK t) {R j : ℕ} (hR : R < 2 ^ 22) (hj : j < 4) :
    wX t (4 * R + j) = φ t R j := by
  have h := lam_cell ht (d := 0) (by norm_num) hR hj
  rw [pt_zero, add_zero, Nat.zero_xor] at h
  exact h

theorem wC_cell {t : E} (ht : ¬ InK t) {R j : ℕ} (hR : R < 2 ^ 22) (hj : j < 4) :
    wC t (4 * R + j) = φ t R (2 ^^^ j) := by
  rw [wC, ← pt_two, lam_cell ht (by norm_num) hR hj]

theorem wVY_cell {t : E} (ht : ¬ InK t) {R j : ℕ} (hR : R < 2 ^ 22) (hj : j < 4) :
    wVY t (4 * R + j) = φ t R (1 ^^^ j) + φ t R (3 ^^^ j) := by
  rw [wVY, show t + θE + 1 = t + pt 3 by rw [pt_three]; ring, show t + 1 = t + pt 1 by rw [pt_one],
    lam_cell ht (by norm_num) hR hj, lam_cell ht (by norm_num) hR hj]

theorem Rk_lt {k : ℕ} (hk : k < 16) : Rk k < 2 ^ 22 := by unfold Rk; omega

/-! ### The words' weights off `K` -/

theorem RW_X {t : E} (ht : ¬ InK t) {k : ℕ} (hk : k < 16) : RW (wX t) k = φ t (Rk k) 1 + φ t (Rk k) 3 := by
  rw [RW, wX_cell ht (Rk_lt hk) (by norm_num), wX_cell ht (Rk_lt hk) (by norm_num)]

theorem RW_C {t : E} (ht : ¬ InK t) {k : ℕ} (hk : k < 16) : RW (wC t) k = φ t (Rk k) 1 + φ t (Rk k) 3 := by
  rw [RW, wC_cell ht (Rk_lt hk) (by norm_num), wC_cell ht (Rk_lt hk) (by norm_num),
    show (2 : ℕ) ^^^ 1 = 3 by decide, show (2 : ℕ) ^^^ 3 = 1 by decide, add_comm]

theorem RW_VY {t : E} (ht : ¬ InK t) {k : ℕ} (hk : k < 16) : RW (wVY t) k = 0 := by
  rw [RW, wVY_cell ht (Rk_lt hk) (by norm_num), wVY_cell ht (Rk_lt hk) (by norm_num),
    show (1 : ℕ) ^^^ 1 = 0 by decide, show (3 : ℕ) ^^^ 1 = 2 by decide, show (1 : ℕ) ^^^ 3 = 2 by decide,
    show (3 : ℕ) ^^^ 3 = 0 by decide]
  linear_combination (φ t (Rk k) 0 + φ t (Rk k) 2) * two_E

theorem SW_of_sum (wt : ℕ → E) {k : ℕ} (h : RandomShape.of k = .sum) :
    SW wt k = wt (4 * Rk k + 2) + wt (4 * Rk k + 3) := by unfold SW; rw [h]

theorem SW_of_select (wt : ℕ → E) {k : ℕ} (h : RandomShape.of k = .select) :
    SW wt k = wt (4 * Rk k + 0) := by unfold SW; rw [h]; rfl

theorem SW_of_pass (wt : ℕ → E) {k : ℕ} (h : RandomShape.of k = .pass) :
    SW wt k = wt (4 * Rk k + 2) := by unfold SW; rw [h]

/-- `Σ_m φ_m`. -/
noncomputable def S4 (t : E) (R : ℕ) : E := φ t R 0 + φ t R 1 + φ t R 2 + φ t R 3

/-- An `s`-word of a sum row: `P = 0`, `V + Y = Σ φ`. -/
theorem SW_sum {t : E} (ht : ¬ InK t) {k : ℕ} (hk : k < 16) (h : RandomShape.of k = .sum) :
    SW (wX t) k + SW (wC t) k + SW (wVY t) k = 0 ∧ SW (wVY t) k = S4 t (Rk k) := by
  simp only [SW_of_sum _ h, wX_cell ht (Rk_lt hk) (by norm_num : 2 < 4), wX_cell ht (Rk_lt hk) (by norm_num : 3 < 4),
    wC_cell ht (Rk_lt hk) (by norm_num : 2 < 4), wC_cell ht (Rk_lt hk) (by norm_num : 3 < 4),
    wVY_cell ht (Rk_lt hk) (by norm_num : 2 < 4), wVY_cell ht (Rk_lt hk) (by norm_num : 3 < 4),
    show (2 : ℕ) ^^^ 2 = 0 by decide, show (2 : ℕ) ^^^ 3 = 1 by decide, show (1 : ℕ) ^^^ 2 = 3 by decide,
    show (3 : ℕ) ^^^ 2 = 1 by decide, show (1 : ℕ) ^^^ 3 = 2 by decide, show (3 : ℕ) ^^^ 3 = 0 by decide, S4]
  constructor
  · linear_combination (φ t (Rk k) 0 + φ t (Rk k) 1 + φ t (Rk k) 2 + φ t (Rk k) 3) * two_E
  · ring

/-- An `s`-word of a select row: `P = Σ φ`. -/
theorem SW_select {t : E} (ht : ¬ InK t) {k : ℕ} (hk : k < 16) (h : RandomShape.of k = .select) :
    SW (wX t) k + SW (wC t) k + SW (wVY t) k = S4 t (Rk k) := by
  simp only [SW_of_select _ h, wX_cell ht (Rk_lt hk) (by norm_num : 0 < 4),
    wC_cell ht (Rk_lt hk) (by norm_num : 0 < 4), wVY_cell ht (Rk_lt hk) (by norm_num : 0 < 4),
    show (2 : ℕ) ^^^ 0 = 2 by decide, show (1 : ℕ) ^^^ 0 = 1 by decide, show (3 : ℕ) ^^^ 0 = 3 by decide, S4]
  ring

/-- An `s`-word of a pass row: `P = Σ φ`. -/
theorem SW_pass {t : E} (ht : ¬ InK t) {k : ℕ} (hk : k < 16) (h : RandomShape.of k = .pass) :
    SW (wX t) k + SW (wC t) k + SW (wVY t) k = S4 t (Rk k) := by
  simp only [SW_of_pass _ h, wX_cell ht (Rk_lt hk) (by norm_num : 2 < 4),
    wC_cell ht (Rk_lt hk) (by norm_num : 2 < 4), wVY_cell ht (Rk_lt hk) (by norm_num : 2 < 4),
    show (2 : ℕ) ^^^ 2 = 0 by decide, show (1 : ℕ) ^^^ 2 = 3 by decide, show (3 : ℕ) ^^^ 2 = 1 by decide, S4]
  ring

end PcsQuotient.EndToEnd.Group1
