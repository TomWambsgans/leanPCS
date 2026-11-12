-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsGroup1Rows

/-!
# Group 1: the random-rows map is onto on the good event

**`onto_of_good`**: where `w₂(t) ∉ K`, `t² + θ t ∉ K` and `W`'s point avoids the values `GoodW` lists (each pinned
by the coordinates before it, or at most `|K|` of them), the map of the random rows' words to `W`'s answer, `C`,
`V + Y`, `X` is onto `E⁴` (`surj_of_steps`):

* `P = X + C + (V + Y)`: the `s`-words of rows `1, 2, 4` (select, pass, select), `w₂₄(t)/(w₂(t) + B(R))`;
* `V + Y`: the `s`-words of rows `0, 3, 6` (sum; `P = 0`), the same;
* `C`: the `r`-words of rows `0, 1, 2` (`P = V + Y = 0`), `w₂₄(t) θ / (t² + θ t + δ_R)`;
* `W`: for each quarter of rows a combination of its `r`-words that `C` does not see (`kernel4`), three of the four
  independent (`H_ne_zero`, `indep_half`, `merge_indep`).
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open PcsQuotient.Domain QuotientSecurity Finset

namespace PcsQuotient.EndToEnd.Group1

/-! ### The kernel combinations -/

/-- **Quarter `Q`'s kernel combination**: its four `r`-words' `C` weights cancel. -/
noncomputable def cK (t : E) (Q : Fin 4) : Fin 4 → K := Classical.choose (kernel4 fun q ↦ RW (wC t) (kq Q q))

theorem cK_spec (t : E) (Q : Fin 4) : cK t Q ≠ 0 ∧ ∑ q, ofK (cK t Q q) * RW (wC t) (kq Q q) = 0 :=
  Classical.choose_spec (kernel4 fun q ↦ RW (wC t) (kq Q q))

theorem two_kq_lt (Q q : Fin 4) : 2 * kq Q q < randomWords := by
  have := kq_lt Q q; unfold randomWords randomRows; omega

/-- The kernel combination as a vector of words. -/
noncomputable def κv (t : E) (Q : Fin 4) : Fin randomWords → K :=
  ∑ q, cK t Q q • sw (2 * kq Q q) (two_kq_lt Q q)

theorem LsumL_κv (wt : ℕ → E) (t : E) (Q : Fin 4) :
    LsumL wt (κv t Q) = ∑ q, ofK (cK t Q q) * RW wt (kq Q q) := by
  rw [κv, map_sum]
  refine sum_congr rfl fun q _ ↦ ?_
  rw [map_smul, LsumL_r wt (kq_lt Q q), Algebra.smul_def, ← ofK_eq]

/-- `H_Q` at `W`'s point. -/
noncomputable def HQ (t : E) (z : List E) (Q : Fin 4) : E :=
  Hq θE (γQ Q) (δQ Q) (eQ Q) (cK t Q) (uz z 0) (uz z 1) (uz z 2) (uz z 3)

/-- `y_Q = (1 + u₄ c_Q) H_Q`. -/
noncomputable def yQ (t : E) (z : List E) (Q : Fin 4) : E := (1 + uz z 4 * c4Q Q) * HQ t z Q

/-- **`W`'s weight of quarter `Q`'s kernel combination.** -/
theorem LW_κv (t : E) (z : List E) (Q : Fin 4) :
    LsumL (wW z) (κv t Q) = Fz z * (1 + uz z 5 * dQ Q) * yQ t z Q := by
  rw [LsumL_κv]
  simp only [RW_W, yQ, HQ, Hq, mul_sum]
  refine sum_congr rfl fun q _ ↦ ?_
  ring

/-! ### The good event -/

/-- **The good event of `W`'s point** for the challenge `t`: `F(z) ≠ 0`; each quarter's `H ≠ 0`
(`GoodH`); each half's quarters independent (`u₄`); three quarters independent (`u₅`). -/
def GoodW (t : E) (z : List E) : Prop :=
  (∀ b < 18, uz z (b + 6) ≠ (pt (Hc / 2 ^ b))⁻¹) ∧
  (∀ Q, GoodH θE (γQ Q) (δQ Q) (eQ Q) (cK t Q) (uz z 0) (uz z 1) (uz z 2) (uz z 3)) ∧
  uz z 4 ≠ (c4Q 0)⁻¹ ∧ (∀ l, uz z 4 ≠ g4 (c4Q 0) (c4Q 1) (HQ t z 0) (HQ t z 1) l) ∧
  uz z 4 ≠ (c4Q 2)⁻¹ ∧ (∀ l, uz z 4 ≠ g4 (c4Q 2) (c4Q 3) (HQ t z 2) (HQ t z 3) l) ∧
  uz z 5 ≠ (dQ 0)⁻¹ ∧ uz z 5 ≠ (dQ 2)⁻¹ ∧
  ∀ l, uz z 5 ≠ g5 (dQ 0) (dQ 2) (yQ t z 0) (yQ t z 1) (yQ t z 2) (yQ t z 3) l

/-- **The good event**: `w₂(t) ∉ K`, `t² + θ t ∉ K`, and `W`'s point's. -/
def Good (t : E) (z : List E) : Prop := ¬ InK (sq^[2] t) ∧ ¬ InK (t * t + θE * t) ∧ GoodW t z

theorem θE_ne_zero : θE ≠ 0 := fun h ↦ by
  have := θE_sq; rw [h] at this; exact one_ne_zero (by linear_combination this)

theorem Fz_ne_zero {z : List E} (h : ∀ b < 18, uz z (b + 6) ≠ (pt (Hc / 2 ^ b))⁻¹) : Fz z ≠ 0 := by
  refine prod_ne_zero_iff.2 fun b hb ↦ fun h0 ↦ ?_
  have hb' := mem_range.1 hb
  by_cases hp : pt (Hc / 2 ^ b) = 0
  · rw [hp, mul_zero, add_zero] at h0; exact one_ne_zero h0
  · exact h b hb' (eq_inv_of_mul_eq_one_left (by linear_combination h0 - two_E))

theorem c4Q_succ0 : c4Q 1 = c4Q 0 + 1 := by
  simp only [c4Q, Fin.val_one, Fin.val_zero, pt_one, pt_zero]; ring

theorem c4Q_succ2 : c4Q 3 = c4Q 2 + 1 := by
  simp only [c4Q, show ((3 : Fin 4) : ℕ) = 3 from rfl, show ((2 : Fin 4) : ℕ) = 2 from rfl, pt_three, pt_two]
  ring

theorem dQ_1 : dQ 1 = dQ 0 := rfl

theorem dQ_3 : dQ 3 = dQ 2 := rfl

theorem dQ_succ : dQ 2 = dQ 0 + 1 := by
  simp only [dQ, show ((2 : Fin 4) : ℕ) / 2 = 1 from rfl, show ((0 : Fin 4) : ℕ) / 2 = 0 from rfl, pt_one,
    pt_zero]; ring

/-- **On the good event, three quarters' kernel combinations reach `W`'s answer independently.** -/
theorem w_indep {t : E} {z : List E} (hW : GoodW t z) :
    Indep3 (LsumL (wW z) (κv t 0)) (LsumL (wW z) (κv t 1)) (LsumL (wW z) (κv t 2)) ∨
      Indep3 (LsumL (wW z) (κv t 0)) (LsumL (wW z) (κv t 1)) (LsumL (wW z) (κv t 3)) := by
  obtain ⟨hF, hG, h4a, h4b, h4c, h4d, h5a, h5b, h5c⟩ := hW
  have hH : ∀ Q, HQ t z Q ≠ 0 := fun Q ↦ H_ne_zero _ _ _ _ _ θE_ne_zero (cK_spec t Q).1 (hG Q)
  have half0 : Indep2 (yQ t z 0) (yQ t z 1) := by
    unfold yQ; exact indep_half c4Q_succ0 (hH 0) (hH 1) h4a h4b
  have half1 : Indep2 (yQ t z 2) (yQ t z 3) := by
    unfold yQ; exact indep_half c4Q_succ2 (hH 2) (hH 3) h4c h4d
  have hm := merge_indep dQ_succ (Fz_ne_zero hF) half0 half1 h5a h5b h5c
  rw [LW_κv, LW_κv, LW_κv, LW_κv, dQ_1, dQ_3]
  exact hm

/-! ### Distinct constants -/

theorem two_K : (2 : K) = 0 := CharTwo.two_eq_zero

/-- `δ_R + δ_R' = B(n) B(n ⊕ 2)`, `n = 4R ⊕ 4R'`. -/
theorem δK_add (R R' : ℕ) :
    δK R + δK R' = point (4 * R ^^^ 4 * R') * point ((4 * R ^^^ 4 * R') ^^^ 2) := by
  rw [E2ECompleteness.Pcs.H.point_xor_low (4 * R ^^^ 4 * R'), E2ECompleteness.Pcs.H.point_two,
    E2ECompleteness.Pcs.H.point_xor_low]
  unfold δK
  linear_combination (point (4 * R) + point (4 * R') + 1 - point (4 * R) * point (4 * R') + betaAt 1) * two_K

theorem δK_ne {R R' n : ℕ} (hn : 4 * R ^^^ 4 * R' = n) (h0 : n ≠ 0) (h1 : n ^^^ 2 ≠ 0) (hl0 : n < 2 ^ 24)
    (hl1 : n ^^^ 2 < 2 ^ 24) : δK R ≠ δK R' := by
  intro h
  have hs := δK_add R R'
  rw [h, hn, show δK R' + δK R' = 2 * δK R' by ring, two_K, zero_mul] at hs
  rcases mul_eq_zero.1 hs.symm with h' | h'
  · exact point_ne_zero h0 hl0 h'
  · exact point_ne_zero h1 hl1 h'

theorem point_Rk_ne {k k' : ℕ} (hk : k < 16) (hk' : k' < 16) (h : k ≠ k') : point (Rk k) ≠ point (Rk k') :=
  point_ne (by unfold Rk; omega) (by unfold Rk; omega) (by unfold Rk; omega)

/-! ### Onto -/

/-- A kernel combination is seen by neither `X`, `C` nor `V + Y`. -/
theorem κv_zero {t : E} (ht : ¬ InK t) (Q : Fin 4) :
    LsumL (wX t) (κv t Q) = 0 ∧ LsumL (wC t) (κv t Q) = 0 ∧ LsumL (wVY t) (κv t Q) = 0 := by
  have hC := (cK_spec t Q).2
  refine ⟨?_, ?_, ?_⟩
  · rw [LsumL_κv, ← hC]
    exact sum_congr rfl fun q _ ↦ by rw [RW_X ht (kq_lt Q q), RW_C ht (kq_lt Q q)]
  · rw [LsumL_κv, hC]
  · rw [LsumL_κv]
    exact sum_eq_zero fun q _ ↦ by rw [RW_VY ht (kq_lt Q q), mul_zero]

/-- **On the good event the random-rows map is onto `E⁴`.** -/
theorem onto_of_good {t : E} {z : List E} (hg : Good t z) :
    Function.Surjective (Lmap (wW z) (wC t) (wVY t) (wX t)) := by
  obtain ⟨hT2, hZ1, hW⟩ := hg
  have ht : ¬ InK t := fun h ↦ hT2 (InK_sq2 h)
  have hμ := μt_ne_zero ht
  obtain ⟨Q3, hQ3⟩ : ∃ Q3 : Fin 4,
      Indep3 (LsumL (wW z) (κv t 0)) (LsumL (wW z) (κv t 1)) (LsumL (wW z) (κv t Q3)) := by
    rcases w_indep hW with h | h
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  intro y
  -- `P`: the `s`-words of rows `1, 2, 4`.
  have hP : Indep3
      (LsumL (wX t) (sw (2 * 1 + 1) (by decide)) + LsumL (wC t) (sw (2 * 1 + 1) (by decide)) +
        LsumL (wVY t) (sw (2 * 1 + 1) (by decide)))
      (LsumL (wX t) (sw (2 * 2 + 1) (by decide)) + LsumL (wC t) (sw (2 * 2 + 1) (by decide)) +
        LsumL (wVY t) (sw (2 * 2 + 1) (by decide)))
      (LsumL (wX t) (sw (2 * 4 + 1) (by decide)) + LsumL (wC t) (sw (2 * 4 + 1) (by decide)) +
        LsumL (wVY t) (sw (2 * 4 + 1) (by decide))) := by
    simp only [LsumL_s _ (show 1 < 16 by norm_num), LsumL_s _ (show 2 < 16 by norm_num),
      LsumL_s _ (show 4 < 16 by norm_num)]
    rw [SW_select ht (by norm_num) rfl, SW_pass ht (by norm_num) rfl, SW_select ht (by norm_num) rfl,
      S4_eq ht (Rk_lt (by norm_num)), S4_eq ht (Rk_lt (by norm_num)), S4_eq ht (Rk_lt (by norm_num))]
    exact (indep3_inv hT2 (point_Rk_ne (by norm_num) (by norm_num) (by norm_num))
      (point_Rk_ne (by norm_num) (by norm_num) (by norm_num))
      (point_Rk_ne (by norm_num) (by norm_num) (by norm_num))).mul hμ
  -- `V + Y`: the `s`-words of rows `0, 3, 6`.
  have hv0 : ∀ k : ℕ, (hk : k < 16) → RandomShape.of k = .sum →
      LsumL (wX t) (sw (2 * k + 1) (by unfold randomWords randomRows; omega)) +
        LsumL (wC t) (sw (2 * k + 1) (by unfold randomWords randomRows; omega)) +
        LsumL (wVY t) (sw (2 * k + 1) (by unfold randomWords randomRows; omega)) = 0 := fun k hk hs ↦ by
    rw [LsumL_s _ hk, LsumL_s _ hk, LsumL_s _ hk]; exact (SW_sum ht hk hs).1
  have hV : Indep3 (LsumL (wVY t) (sw (2 * 0 + 1) (by decide))) (LsumL (wVY t) (sw (2 * 3 + 1) (by decide)))
      (LsumL (wVY t) (sw (2 * 6 + 1) (by decide))) := by
    rw [LsumL_s _ (show 0 < 16 by norm_num), LsumL_s _ (show 3 < 16 by norm_num),
      LsumL_s _ (show 6 < 16 by norm_num), (SW_sum ht (by norm_num) rfl).2, (SW_sum ht (by norm_num) rfl).2,
      (SW_sum ht (by norm_num) rfl).2, S4_eq ht (Rk_lt (by norm_num)), S4_eq ht (Rk_lt (by norm_num)),
      S4_eq ht (Rk_lt (by norm_num))]
    exact (indep3_inv hT2 (point_Rk_ne (by norm_num) (by norm_num) (by norm_num))
      (point_Rk_ne (by norm_num) (by norm_num) (by norm_num))
      (point_Rk_ne (by norm_num) (by norm_num) (by norm_num))).mul hμ
  -- `C`: the `r`-words of rows `0, 1, 2`.
  have hc0 : ∀ k : ℕ, (hk : k < 16) →
      LsumL (wX t) (sw (2 * k) (by unfold randomWords randomRows; omega)) +
        LsumL (wC t) (sw (2 * k) (by unfold randomWords randomRows; omega)) +
        LsumL (wVY t) (sw (2 * k) (by unfold randomWords randomRows; omega)) = 0 ∧
      LsumL (wVY t) (sw (2 * k) (by unfold randomWords randomRows; omega)) = 0 := fun k hk ↦ by
    rw [LsumL_r _ hk, LsumL_r _ hk, LsumL_r _ hk, RW_X ht hk, RW_C ht hk, RW_VY ht hk]
    exact ⟨by linear_combination (φ t (Rk k) 1 + φ t (Rk k) 3) * two_E, rfl⟩
  have hC : Indep3 (LsumL (wC t) (sw (2 * 0) (by decide))) (LsumL (wC t) (sw (2 * 1) (by decide)))
      (LsumL (wC t) (sw (2 * 2) (by decide))) := by
    rw [LsumL_r _ (show 0 < 16 by norm_num), LsumL_r _ (show 1 < 16 by norm_num),
      LsumL_r _ (show 2 < 16 by norm_num), RW_C ht (by norm_num), RW_C ht (by norm_num), RW_C ht (by norm_num),
      A_eq ht, A_eq ht, A_eq ht]
    exact (indep3_inv hZ1 (δK_ne (n := 4) (by decide) (by decide) (by decide) (by norm_num) (by decide))
      (δK_ne (n := 8) (by decide) (by decide) (by decide) (by norm_num) (by decide))
      (δK_ne (n := 12) (by decide) (by decide) (by decide) (by norm_num) (by decide))).mul
      (mul_ne_zero hμ θE_ne_zero)
  obtain ⟨x, hx⟩ := surj_of_steps (LsumL (wW z)) (LsumL (wC t)) (LsumL (wVY t)) (LsumL (wX t))
    ![sw (2 * 1 + 1) (by decide), sw (2 * 2 + 1) (by decide), sw (2 * 4 + 1) (by decide)]
    ![sw (2 * 0 + 1) (by decide), sw (2 * 3 + 1) (by decide), sw (2 * 6 + 1) (by decide)]
    ![sw (2 * 0) (by decide), sw (2 * 1) (by decide), sw (2 * 2) (by decide)]
    ![κv t 0, κv t 1, κv t Q3] hP
    (by
      intro i; fin_cases i
      · exact hv0 0 (by norm_num) rfl
      · exact hv0 3 (by norm_num) rfl
      · exact hv0 6 (by norm_num) rfl) hV
    (by
      intro i; fin_cases i
      · exact hc0 0 (by norm_num)
      · exact hc0 1 (by norm_num)
      · exact hc0 2 (by norm_num)) hC
    (by
      intro i
      have h3 : ∀ Q, LsumL (wX t) (κv t Q) + LsumL (wC t) (κv t Q) + LsumL (wVY t) (κv t Q) = 0 ∧
          LsumL (wVY t) (κv t Q) = 0 ∧ LsumL (wC t) (κv t Q) = 0 := fun Q ↦ by
        obtain ⟨a, b, c⟩ := κv_zero ht Q
        exact ⟨by rw [a, b, c]; ring, c, b⟩
      fin_cases i
      · exact h3 0
      · exact h3 1
      · exact h3 Q3) hQ3 y
  exact ⟨x, hx⟩

end PcsQuotient.EndToEnd.Group1
