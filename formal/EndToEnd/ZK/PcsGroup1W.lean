-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsGroup1Alg

/-!
# Group 1: `W`'s answer spans `E`, in the abstract

The random rows' `r`-words reach `W`'s answer with weights that factor along `W`'s out-of-domain coordinates
`u_b = 1 + z_b` (`PcsGroup1Map.lean`). The rows come in four quarters `Q` of four rows `q'` (the row's bits `2, 3` and
`0, 1`); quarter `Q`'s row `q'` weighs

`F · (1 + u₅ d_Q) (1 + u₄ c_Q) (1 + u₃ Δ_{Q q'}) (1 + u₂ Γ_{Q q'}) (u₁ + θ u₀ + e_{Q q'} u₀ u₁)`,

`Γ_{Q q'} = γ_Q + q₀ + θ q₁`, `Δ_{Q q'} = δ_Q + q₁` (`q' = q₀ + 2 q₁`), `c_{Q+1} = c_Q + 1` within a half, `d` one more on
the second half. A combination `κ_Q ∈ K⁴` of a quarter's rows (one the `C` value does not see) reaches `W`'s answer
with `x_Q = F (1 + u₅ d_Q)(1 + u₄ c_Q) H_Q`, `H_Q = Σ κ (1 + u₂ Γ)(1 + u₃ Δ)(u₁ + θ u₀ + e u₀ u₁)`. Each coordinate
outside a set of at most one value (or `|K|` values) of it, given the others:

* `H_ne_zero`: `H_Q ≠ 0` (`H_Q = u₁ β + θ u₀ P`, `P = P₀(u₂) + u₃ P₁(u₂)`, `P₀, P₁` not both zero as polynomials:
  `coeffs_ne_zero`);
* `indep_half`: the two quarters of a half are independent (`y₁ = λ y₀` pins `u₄` for each `λ ∈ K`);
* **`w_spans`**: three of the four `x_Q` are independent: else both of the second half's lie in the first half's
  plane, and two values of `u₅` doing so have `ρ(u₅) = (1 + u₅ d₁)/(1 + u₅ d₀)` in a ratio in `K`
  (`inK_ratio_of_spans`), which pins `u₅` for each `λ ∈ K`.
-/

open LeanVM.Parameters
open Finset

namespace PcsQuotient.EndToEnd.Group1

/-- Bit `0` of a quarter's row, in `E`. -/
def b0E (q : Fin 4) : E := if q.val % 2 = 1 then 1 else 0

/-- Bit `1` of a quarter's row, in `E`. -/
def b1E (q : Fin 4) : E := if q.val / 2 = 1 then 1 else 0

section Quarter

variable (θ γ δ : E) (e : Fin 4 → E) (κ : Fin 4 → K)

/-- `Γ_{q'}`. -/
def Γq (q : Fin 4) : E := γ + b0E q + θ * b1E q

/-- `Δ_{q'}`. -/
def Δq (q : Fin 4) : E := δ + b1E q

/-- The coefficients of `P = (A₀ + u₂ A₁) + u₃ (A₂ + u₂ A₃)`. -/
def A0 : E := ∑ q, ofK (κ q)
def A1 : E := ∑ q, ofK (κ q) * Γq θ γ q
def A2 : E := ∑ q, ofK (κ q) * Δq δ q
def A3 : E := ∑ q, ofK (κ q) * Δq δ q * Γq θ γ q

/-- `P(u₂, u₃)`. -/
def Pq (u2 u3 : E) : E := ∑ q, ofK (κ q) * (1 + u2 * Γq θ γ q) * (1 + u3 * Δq δ q)

/-- `β(u₀, u₂, u₃)`, the coefficient of `u₁` in `H`. -/
def βq (u0 u2 u3 : E) : E := ∑ q, ofK (κ q) * (1 + u2 * Γq θ γ q) * (1 + u3 * Δq δ q) * (1 + e q * u0)

/-- `H(u₀, …, u₃)`. -/
def Hq (u0 u1 u2 u3 : E) : E :=
  ∑ q, ofK (κ q) * (1 + u2 * Γq θ γ q) * (1 + u3 * Δq δ q) * (u1 + θ * u0 + e q * u0 * u1)

theorem sum_four (f : Fin 4 → E) : ∑ q, f q = f 0 + f 1 + f 2 + f 3 := Fin.sum_univ_four f

theorem b0E_0 : b0E 0 = 0 := rfl
theorem b0E_1 : b0E 1 = 1 := rfl
theorem b0E_2 : b0E 2 = 0 := rfl
theorem b0E_3 : b0E 3 = 1 := rfl
theorem b1E_0 : b1E 0 = 0 := rfl
theorem b1E_1 : b1E 1 = 0 := rfl
theorem b1E_2 : b1E 2 = 1 := rfl
theorem b1E_3 : b1E 3 = 1 := rfl

/-- **`P`'s coefficients vanish only for `κ = 0`.** -/
theorem coeffs_ne_zero (hκ : κ ≠ 0) :
    ¬ (A0 κ = 0 ∧ A1 θ γ κ = 0 ∧ A2 δ κ = 0 ∧ A3 θ γ δ κ = 0) := by
  rintro ⟨h0, h1, h2, h3⟩
  simp only [A0, A1, A2, A3, Γq, Δq, sum_four, b0E_0, b0E_1, b0E_2, b0E_3, b1E_0, b1E_1, b1E_2, b1E_3] at h0 h1 h2 h3
  have x3 : ofK (κ 3) = 0 := by
    linear_combination h3 - δ * h1 - (γ + θ) * h2 + (γ + θ) * δ * h0
  have x2 : ofK (κ 2) = 0 := by linear_combination h2 - δ * h0 - x3
  have x1 : ofK (κ 1) = 0 := by linear_combination h1 - γ * h0 - θ * (h2 - δ * h0) - x3
  have x0 : ofK (κ 0) = 0 := by linear_combination h0 - x1 - x2 - x3
  refine hκ (funext fun q ↦ ?_)
  have hz : ∀ q, ofK (κ q) = 0 → κ q = 0 := fun q h ↦ (map_eq_zero (algebraMap K E)).1 h
  fin_cases q
  · exact hz 0 x0
  · exact hz 1 x1
  · exact hz 2 x2
  · exact hz 3 x3

theorem Pq_eq (u2 u3 : E) :
    Pq θ γ δ κ u2 u3 = (A0 κ + u2 * A1 θ γ κ) + u3 * (A2 δ κ + u2 * A3 θ γ δ κ) := by
  simp only [Pq, A0, A1, A2, A3, sum_four]; ring

theorem Hq_eq (u0 u1 u2 u3 : E) : Hq θ γ δ e κ u0 u1 u2 u3 = u1 * βq θ γ δ e κ u0 u2 u3 + θ * u0 * Pq θ γ δ κ u2 u3 := by
  simp only [Hq, βq, Pq, sum_four]; ring

/-- **The good event of `H`**: `u₀ ≠ 0`, `u₂` off the roots of `P₀` and `P₁`, `u₃` off the root of `P`, `u₁` off the
root of `H`. -/
def GoodH (u0 u1 u2 u3 : E) : Prop :=
  u0 ≠ 0 ∧ u2 ≠ A0 κ / A1 θ γ κ ∧ u2 ≠ A2 δ κ / A3 θ γ δ κ ∧
    u3 ≠ (A0 κ + u2 * A1 θ γ κ) / (A2 δ κ + u2 * A3 θ γ δ κ) ∧
    u1 ≠ θ * u0 * Pq θ γ δ κ u2 u3 / βq θ γ δ e κ u0 u2 u3

/-- In characteristic two, `a + u b = 0` with `b ≠ 0` pins `u = a / b`. -/
theorem eq_div_of_add {a b u : E} (hb : b ≠ 0) (h : a + u * b = 0) : u = a / b := by
  rw [eq_div_iff hb]; linear_combination h - a * two_E

/-- **`H ≠ 0` on the good event.** -/
theorem H_ne_zero (hθ : θ ≠ 0) (hκ : κ ≠ 0) {u0 u1 u2 u3 : E} (hg : GoodH θ γ δ e κ u0 u1 u2 u3) :
    Hq θ γ δ e κ u0 u1 u2 u3 ≠ 0 := by
  obtain ⟨g0, g2a, g2b, g3, g1⟩ := hg
  -- `P₀(u₂)` and `P₁(u₂)` are not both zero.
  have hP01 : ¬ (A0 κ + u2 * A1 θ γ κ = 0 ∧ A2 δ κ + u2 * A3 θ γ δ κ = 0) := by
    rintro ⟨p0, p1⟩
    have a1 : A1 θ γ κ = 0 := by
      by_contra h; exact g2a (eq_div_of_add h p0)
    have a3 : A3 θ γ δ κ = 0 := by
      by_contra h; exact g2b (eq_div_of_add h p1)
    rw [a1, mul_zero, add_zero] at p0
    rw [a3, mul_zero, add_zero] at p1
    exact coeffs_ne_zero θ γ δ κ hκ ⟨p0, a1, p1, a3⟩
  have hP : Pq θ γ δ κ u2 u3 ≠ 0 := by
    rw [Pq_eq]
    intro hp
    by_cases h1 : A2 δ κ + u2 * A3 θ γ δ κ = 0
    · rw [h1, mul_zero, add_zero] at hp
      exact hP01 ⟨hp, h1⟩
    · exact g3 (eq_div_of_add h1 hp)
  rw [Hq_eq]
  intro hH
  by_cases hβ : βq θ γ δ e κ u0 u2 u3 = 0
  · rw [hβ, mul_zero, zero_add] at hH
    exact hP ((mul_eq_zero.1 hH).resolve_left (mul_ne_zero hθ g0))
  · exact g1 (eq_div_of_add hβ (by linear_combination hH))

end Quarter

/-! ### Two quarters of a half -/

/-- `u₄`'s bad value for `λ ∈ K`: where `(1 + u₄ c₁) H₁ = λ (1 + u₄ c₀) H₀`. -/
noncomputable def g4 (c0 c1 H0 H1 : E) (l : K) : E := (ofK l * H0 - H1) / (c1 * H1 - ofK l * c0 * H0)

/-- **The two quarters of a half are independent** off `u₄ = c₀⁻¹` and `u₄ = g4 … λ`, `λ ∈ K`. -/
theorem indep_half {c0 c1 H0 H1 u4 : E} (hc : c1 = c0 + 1) (h0 : H0 ≠ 0) (h1 : H1 ≠ 0) (ha : u4 ≠ c0⁻¹)
    (hb : ∀ l : K, u4 ≠ g4 c0 c1 H0 H1 l) : Indep2 ((1 + u4 * c0) * H0) ((1 + u4 * c1) * H1) := by
  refine indep2_of (mul_ne_zero ?_ h0) fun l hl ↦ ?_
  · intro hz
    have hc0 : c0 ≠ 0 := by rintro rfl; rw [mul_zero, add_zero] at hz; exact one_ne_zero hz
    exact ha (eq_inv_of_mul_eq_one_left (by linear_combination hz - two_E))
  · by_cases hD : c1 * H1 - ofK l * c0 * H0 = 0
    · have e1 : ofK l * H0 = H1 := by linear_combination -hl + u4 * hD
      have : H1 = 0 := by
        have := hD
        rw [hc, ← e1] at this
        linear_combination this - e1
      exact h1 this
    · exact hb l (by rw [g4, eq_div_iff hD]; linear_combination hl)

/-! ### The two halves -/

/-- `ρ(u₅) = (1 + u₅ d₁) / (1 + u₅ d₀)`. -/
noncomputable def ρ5 (d0 d1 u : E) : E := (1 + u * d1) / (1 + u * d0)

/-- `u₅` scales the second half's plane into the first's. -/
def MergeBad (d0 d1 y0 y1 y2 y3 u : E) : Prop :=
  1 + u * d0 ≠ 0 ∧ 1 + u * d1 ≠ 0 ∧ (∃ a b : K, ρ5 d0 d1 u * y2 = ofK a * y0 + ofK b * y1) ∧
    ∃ a b : K, ρ5 d0 d1 u * y3 = ofK a * y0 + ofK b * y1

open Classical in
/-- One such `ρ(u₅)`, if any. -/
noncomputable def ρStar (d0 d1 y0 y1 y2 y3 : E) : E :=
  if h : ∃ u, MergeBad d0 d1 y0 y1 y2 y3 u then ρ5 d0 d1 (Classical.choose h) else 0

/-- `u₅`'s bad value for `λ ∈ K`: where `ρ(u₅) = λ ρ*`. -/
noncomputable def g5 (d0 d1 y0 y1 y2 y3 : E) (l : K) : E :=
  (ofK l * ρStar d0 d1 y0 y1 y2 y3 - 1) / (d1 - ofK l * ρStar d0 d1 y0 y1 y2 y3 * d0)

/-- `¬ Indep3` of an independent pair and a third: the third in their plane. -/
theorem mem_plane_of_not_indep3 {y0 y1 y2 : E} (h01 : Indep2 y0 y1) (h : ¬ Indep3 y0 y1 y2) :
    ∃ a b : K, y2 = ofK a * y0 + ofK b * y1 := by
  by_contra hn
  push Not at hn
  exact h (indep3_of h01 hn)

/-- **Three of the four are independent** off `u₅ ∈ {d₀⁻¹, d₁⁻¹}` and `u₅ = g5 … λ`, `λ ∈ K`. -/
theorem merge_indep {d0 d1 y0 y1 y2 y3 F u5 : E} (hd : d1 = d0 + 1) (hF : F ≠ 0) (h01 : Indep2 y0 y1)
    (h23 : Indep2 y2 y3) (ha : u5 ≠ d0⁻¹) (hb : u5 ≠ d1⁻¹) (hc : ∀ l : K, u5 ≠ g5 d0 d1 y0 y1 y2 y3 l) :
    Indep3 (F * (1 + u5 * d0) * y0) (F * (1 + u5 * d0) * y1) (F * (1 + u5 * d1) * y2) ∨
      Indep3 (F * (1 + u5 * d0) * y0) (F * (1 + u5 * d0) * y1) (F * (1 + u5 * d1) * y3) := by
  have nz : ∀ d : E, u5 ≠ d⁻¹ → 1 + u5 * d ≠ 0 := fun d hd' hz ↦ by
    have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero, add_zero] at hz; exact one_ne_zero hz
    exact hd' (eq_inv_of_mul_eq_one_left (by linear_combination hz - two_E))
  have f0 := nz d0 ha
  have f1 := nz d1 hb
  have hFf0 : F * (1 + u5 * d0) ≠ 0 := mul_ne_zero hF f0
  have hI : Indep2 (F * (1 + u5 * d0) * y0) (F * (1 + u5 * d0) * y1) := by
    simpa only [mul_assoc] using h01.mul hFf0
  by_contra hn
  push Not at hn
  obtain ⟨a, b, hab⟩ := mem_plane_of_not_indep3 hI hn.1
  obtain ⟨a', b', hab'⟩ := mem_plane_of_not_indep3 hI hn.2
  -- `ρ(u₅) y₂, ρ(u₅) y₃` lie in the first half's plane.
  have hρ : ∀ (w : E) (a b : K), F * (1 + u5 * d1) * w = ofK a * (F * (1 + u5 * d0) * y0) +
      ofK b * (F * (1 + u5 * d0) * y1) → ρ5 d0 d1 u5 * w = ofK a * y0 + ofK b * y1 := fun w a b h ↦ by
    rw [ρ5]
    field_simp
    have := congrArg (· / F) h
    field_simp at this
    linear_combination this
  have hbad : MergeBad d0 d1 y0 y1 y2 y3 u5 := ⟨f0, f1, ⟨a, b, hρ y2 a b hab⟩, ⟨a', b', hρ y3 a' b' hab'⟩⟩
  have hex : ∃ u, MergeBad d0 d1 y0 y1 y2 y3 u := ⟨u5, hbad⟩
  have hstar : ρStar d0 d1 y0 y1 y2 y3 = ρ5 d0 d1 (Classical.choose hex) := by rw [ρStar, dif_pos hex]
  obtain ⟨s0, s1, ⟨a2, b2, e2⟩, ⟨a3, b3, e3⟩⟩ := Classical.choose_spec hex
  have hρs : ρ5 d0 d1 (Classical.choose hex) ≠ 0 := div_ne_zero s1 s0
  obtain ⟨l, hl⟩ := inK_ratio_of_spans h23 hρs e2 e3 (hρ y2 a b hab) (hρ y3 a' b' hab')
  rw [← hstar] at hl hρs
  have hρl : ρ5 d0 d1 u5 = ofK l * ρStar d0 d1 y0 y1 y2 y3 := by
    rw [← hl]; field_simp
  -- So `u₅` is `g5 … λ`.
  rw [ρ5, div_eq_iff f0] at hρl
  by_cases hD : d1 - ofK l * ρStar d0 d1 y0 y1 y2 y3 * d0 = 0
  · have h1 : ofK l * ρStar d0 d1 y0 y1 y2 y3 = 1 := by linear_combination -hρl + u5 * hD
    rw [h1, hd] at hD
    exact one_ne_zero (by linear_combination hD)
  · exact hc l (by rw [g5, eq_div_iff hD]; linear_combination hρl)

end PcsQuotient.EndToEnd.Group1
