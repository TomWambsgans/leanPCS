-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsGroup1Span

/-!
# Group 1: the random rows' words, one at a time, and `W`'s weights by quarter

* `LsumL_r`, `LsumL_s`: a single word reaches each scalar with its row's `RW`, `SW`.
* The rows by quarter: row `kq Q q' = 15 − (4Q + q')` has index `R = 16 H + 4 Q + q'`, `H = 2^18 − 1`, and its
  `r`-word's weight in `W`'s answer factors (`RW_W`) as
  `F(z) · (1 + u₅ d_Q)(1 + u₄ c_Q)(1 + u₃ Δ_{Q q'})(1 + u₂ Γ_{Q q'})(u₁ + θ u₀ + e_{Q q'} u₀ u₁)`, `u_b = 1 + z_b`,
  `F(z) = Π_{b < 18} (1 + u_{b+6} B(⌊H / 2^b⌋))` common to all rows (`PcsGroup1W.lean`'s form).
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open PcsQuotient.Domain QuotientSecurity Finset

namespace PcsQuotient.EndToEnd.Group1

/-! ### One word -/

/-- The unit vector of word `w`. -/
def sw (w : ℕ) (hw : w < randomWords) : Fin randomWords → K := Pi.single (⟨w, hw⟩ : Fin randomWords) 1

theorem wd_sw (w : ℕ) (hw : w < randomWords) (i : ℕ) : wd (sw w hw) i = if i = w then 1 else 0 := by
  unfold wd sw
  split_ifs with h1 h2 h2
  · subst h2; simp
  · rw [Pi.single_apply, if_neg (fun h ↦ h2 (congrArg Fin.val h))]
  · omega
  · rfl

/-- **An `r`-word reaches a scalar with its row's `RW`.** -/
theorem LsumL_r (wt : ℕ → E) {k : ℕ} (hk : k < 16) :
    LsumL wt (sw (2 * k) (by unfold randomWords randomRows; omega)) = RW wt k := by
  rw [LsumL_apply, Lsum, sum_eq_single k]
  · rw [wd_sw, wd_sw, if_pos rfl, if_neg (by omega), ofK_one, ofK_zero]; ring
  · intro k' _ hk'
    rw [wd_sw, wd_sw, if_neg (by omega), if_neg (by omega), ofK_zero]; ring
  · intro h; exact absurd (mem_range.2 hk) h

/-- **An `s`-word reaches a scalar with its row's `SW`.** -/
theorem LsumL_s (wt : ℕ → E) {k : ℕ} (hk : k < 16) :
    LsumL wt (sw (2 * k + 1) (by unfold randomWords randomRows; omega)) = SW wt k := by
  rw [LsumL_apply, Lsum, sum_eq_single k]
  · rw [wd_sw, wd_sw, if_neg (by omega), if_pos rfl, ofK_one, ofK_zero]; ring
  · intro k' _ hk'
    rw [wd_sw, wd_sw, if_neg (by omega), if_neg (by omega), ofK_zero]; ring
  · intro h; exact absurd (mem_range.2 hk) h

/-! ### `W`'s weights by quarter -/

/-- `H = 2^18 − 1`: a random row's index is `16 H + q`, `q < 16`. -/
def Hc : ℕ := 2 ^ 18 - 1

/-- Row `q'` of quarter `Q`: `15 − (4 Q + q')`. -/
def kq (Q q : Fin 4) : ℕ := 15 - (4 * Q.val + q.val)

theorem kq_lt (Q q : Fin 4) : kq Q q < 16 := by unfold kq; omega

theorem Rk_kq (Q q : Fin 4) : Rk (kq Q q) = 16 * Hc + 4 * Q.val + q.val := by
  unfold Rk kq Hc; have := Q.isLt; have := q.isLt; omega

/-- `u_b = 1 + z_b`. -/
def uz (z : List E) (b : ℕ) : E := 1 + xc z b

/-- The rows' common factor of `W`'s weights. -/
noncomputable def Fz (z : List E) : E := ∏ b ∈ range 18, (1 + uz z (b + 6) * pt (Hc / 2 ^ b))

/-- The quarter's constants: `Γ`'s, `Δ`'s, `c`, `d`. -/
noncomputable def γQ (Q : Fin 4) : E := pt (16 * Hc) + pt (4 * Q.val)
noncomputable def δQ (Q : Fin 4) : E := pt (8 * Hc) + pt (2 * Q.val)
noncomputable def c4Q (Q : Fin 4) : E := pt (4 * Hc) + pt Q.val
noncomputable def dQ (Q : Fin 4) : E := pt (2 * Hc) + pt (Q.val / 2)

/-- The row's `e = B(4R) + 1 + θ (B(2R) + 1)`. -/
noncomputable def eQ (Q : Fin 4) (q : Fin 4) : E :=
  pt (4 * Rk (kq Q q)) + 1 + θE * (pt (2 * Rk (kq Q q)) + 1)

theorem pt_fin4 (q : Fin 4) : pt q.val = b0E q + θE * b1E q := by
  fin_cases q
  · simp [pt_zero, b0E, b1E]
  · simp [pt_one, b0E, b1E]
  · simp [pt_two, b0E, b1E]
  · simp [pt_three, b0E, b1E]

theorem pt_fin4_half (q : Fin 4) : pt (q.val / 2) = b1E q := by
  fin_cases q
  · simp [pt_zero, b1E]
  · simp [pt_zero, b1E]
  · simp [pt_one, b1E]
  · simp [pt_one, b1E]

/-- `W`'s weight of cell `i = 4R + j`, `R = 16 H + q`, by its digits. -/
theorem wW_cell (z : List E) {R j : ℕ} (hj : j < 4) (hR : R < 2 ^ 22) :
    wW z (4 * R + j) = (1 + uz z 0 * pt (4 * R + j)) * (1 + uz z 1 * pt (2 * R + j / 2)) *
      ∏ b ∈ range 22, (1 + uz z (b + 2) * pt (R / 2 ^ b)) := by
  rw [wW, prod_range_succ', prod_range_succ']
  have hb : ∀ b, (4 * R + j) / 2 ^ (b + 1 + 1) = R / 2 ^ b := fun b ↦ by
    rw [pow_succ, pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    rw [show (4 * R + j) / 2 ^ b / 2 / 2 = (4 * R + j) / 4 / 2 ^ b by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]; ring_nf]
    rw [show (4 * R + j) / 4 = R by omega]
  simp only [hb, uz, zero_add, pow_zero, Nat.div_one, pow_one, show (4 * R + j) / 2 = 2 * R + j / 2 by omega]
  ring

/-- `B'`: the two cells `Y`, `V` of the row in `u₀, u₁`. -/
theorem B_pair (u0 u1 a a' : E) :
    (1 + u0 * (a + 1)) * (1 + u1 * a') + (1 + u0 * (a + (1 + θE))) * (1 + u1 * (a' + 1)) =
      u1 + θE * u0 + (a + 1 + θE * (a' + 1)) * u0 * u1 := by
  linear_combination (1 + u1 * a' + u0 * (a + 1) + u0 * u1 * (a + 1) * a') * two_E

/-- **A row's `r`-word in `W`'s answer, by quarter.** -/
theorem RW_W (z : List E) (Q q : Fin 4) :
    RW (wW z) (kq Q q) = Fz z * ((1 + uz z 5 * dQ Q) * ((1 + uz z 4 * c4Q Q) *
      ((1 + uz z 2 * Γq θE (γQ Q) q) * (1 + uz z 3 * Δq (δQ Q) q) *
        (uz z 1 + θE * uz z 0 + eQ Q q * uz z 0 * uz z 1)))) := by
  have hR := Rk_kq Q q
  have hRlt : Rk (kq Q q) < 2 ^ 22 := Rk_lt (kq_lt Q q)
  set R := Rk (kq Q q) with hRdef
  rw [RW, wW_cell z (by norm_num) hRlt, wW_cell z (by norm_num) hRlt]
  -- The four digits of the row within the block, and the common factor.
  have hsplit : ∏ b ∈ range 22, (1 + uz z (b + 2) * pt (R / 2 ^ b)) =
      (1 + uz z 2 * pt R) * (1 + uz z 3 * pt (R / 2)) * (1 + uz z 4 * pt (R / 4)) * (1 + uz z 5 * pt (R / 8)) *
        Fz z := by
    rw [show (22 : ℕ) = 4 + 18 from rfl, prod_range_add]
    have hF : ∏ b ∈ range 18, (1 + uz z (4 + b + 2) * pt (R / 2 ^ (4 + b))) = Fz z := by
      refine prod_congr rfl fun b _ ↦ ?_
      rw [show 4 + b + 2 = b + 6 by ring, pow_add, ← Nat.div_div_eq_div_mul,
        show R / 2 ^ 4 = Hc by rw [hR]; have := Q.isLt; have := q.isLt; norm_num; omega]
    rw [hF]
    simp only [prod_range_succ, prod_range_zero, one_mul, pow_zero, Nat.div_one, pow_one]
    norm_num
  rw [hsplit]
  -- The digits in the quarter's constants.
  have e2 : pt R = Γq θE (γQ Q) q := by
    rw [hR, show 16 * Hc + 4 * Q.val + q.val = 2 ^ 4 * Hc + (4 * Q.val + q.val) by ring,
      pt_split 4 Hc _ (by have := Q.isLt; have := q.isLt; norm_num <;> omega),
      show 4 * Q.val + q.val = 2 ^ 2 * Q.val + q.val by ring, pt_split 2 Q.val q.val (by have := q.isLt; norm_num <;> omega),
      pt_fin4, Γq, γQ]
    norm_num
    ring
  have e3 : pt (R / 2) = Δq (δQ Q) q := by
    rw [show R / 2 = 2 ^ 3 * Hc + (2 * Q.val + q.val / 2) by rw [hR]; omega,
      pt_split 3 Hc _ (by have := Q.isLt; have := q.isLt; norm_num <;> omega),
      show 2 * Q.val + q.val / 2 = 2 ^ 1 * Q.val + q.val / 2 by ring,
      pt_split 1 Q.val _ (by have := q.isLt; norm_num <;> omega), pt_fin4_half, Δq, δQ]
    norm_num
    ring
  have e4 : pt (R / 4) = c4Q Q := by
    rw [show R / 4 = 2 ^ 2 * Hc + Q.val by rw [hR]; omega, pt_split 2 Hc _ (by have := Q.isLt; norm_num <;> omega), c4Q]
    norm_num
  have e5 : pt (R / 8) = dQ Q := by
    rw [show R / 8 = 2 ^ 1 * Hc + Q.val / 2 by rw [hR]; omega, pt_split 1 Hc _ (by have := Q.isLt; norm_num <;> omega),
      dQ]
    norm_num
  -- The pair of cells.
  have p1 : pt (4 * R + 1) = pt (4 * R) + 1 := by
    rw [show 4 * R + 1 = 2 ^ 2 * R + 1 by ring, pt_split 2 R 1 (by norm_num), pt_one]; norm_num
  have p3 : pt (4 * R + 3) = pt (4 * R) + (1 + θE) := by
    rw [show 4 * R + 3 = 2 ^ 2 * R + 3 by ring, pt_split 2 R 3 (by norm_num), pt_three]; norm_num
  have q1 : pt (2 * R + 1 / 2) = pt (2 * R) := by norm_num
  have q3 : pt (2 * R + 3 / 2) = pt (2 * R) + 1 := by
    rw [show 2 * R + 3 / 2 = 2 ^ 1 * R + 1 by norm_num, pt_split 1 R 1 (by norm_num), pt_one]; norm_num
  rw [e2, e3, e4, e5, p1, p3, q1, q3]
  have hB := B_pair (uz z 0) (uz z 1) (pt (4 * R)) (pt (2 * R))
  have he : eQ Q q = pt (4 * R) + 1 + θE * (pt (2 * R) + 1) := rfl
  rw [he]
  linear_combination (Fz z * (1 + uz z 2 * Γq θE (γQ Q) q) * (1 + uz z 3 * Δq (δQ Q) q) *
    (1 + uz z 4 * c4Q Q) * (1 + uz z 5 * dQ Q)) * hB

end PcsQuotient.EndToEnd.Group1
