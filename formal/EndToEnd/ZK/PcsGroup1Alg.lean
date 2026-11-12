-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsSpan

/-!
# Group 1: the linear algebra of `E` over `K`

`E` is three-dimensional over `K` (`finrank_KE`), so an element of `E` that is a root of a monic quadratic over `K`
lies in `K` (`mem_K_of_quad`: its minimal polynomial's degree divides `3`). From it:

* `Indep3.spans`: three `K`-independent elements span `E` (an injective `K`-linear map `K³ → E` is onto);
* `indep3_inv`: for `s ∉ K` and distinct `γᵢ ∈ K`, the three `1/(s + γᵢ)` are `K`-independent (a relation would give
  `s` a polynomial of degree at most `2` over `K`, or vanish at the `γᵢ`);
* `inK_of_stab`, `inK_ratio_of_spans`: an element mapping a `K`-plane of `E` into itself lies in `K` (its
  characteristic polynomial on the plane is a monic quadratic over `K`), so two scalings of one plane into another
  differ by an element of `K`;
* `kernel4`: four elements of `E` are `K`-dependent (`|K⁴| > |E|`).
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open Polynomial

namespace PcsQuotient.EndToEnd.Group1

theorem ofK_eq (a : K) : ofK a = algebraMap K E a := rfl

theorem ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem ofK_sub (a b : K) : ofK (a - b) = ofK a - ofK b := map_sub (algebraMap K E) a b

theorem ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem ofK_neg (a : K) : ofK (-a) = -ofK a := map_neg (algebraMap K E) a

theorem ofK_div (a b : K) : ofK (a / b) = ofK a / ofK b := map_div₀ (algebraMap K E) a b

theorem ofK_inv (a : K) : ofK a⁻¹ = (ofK a)⁻¹ := map_inv₀ (algebraMap K E) a

theorem ofK_zero : ofK (0 : K) = 0 := map_zero (algebraMap K E)

theorem ofK_one : ofK (1 : K) = 1 := map_one (algebraMap K E)

theorem ofK_ne_zero {a : K} (h : a ≠ 0) : ofK a ≠ 0 := (map_ne_zero (algebraMap K E)).2 h

theorem two_E : (2 : E) = 0 := CharTwo.two_eq_zero

/-- `x` lies in `K`. -/
def InK (x : E) : Prop := ∃ a : K, x = ofK a

/-- **`E` is three-dimensional over `K`.** -/
theorem finrank_KE : Module.finrank K E = 3 := by
  haveI : Module.Finite K E := Module.Finite.of_finite
  have h := Module.card_eq_pow_finrank (K := K) (V := E)
  rw [card_E, BF64.card_bf64, ← pow_mul] at h
  have := Nat.pow_right_injective (le_refl 2) h
  omega

/-- **A root in `E` of a monic quadratic over `K` lies in `K`**: its minimal polynomial has degree at most `2`
and divides `[E : K] = 3`. -/
theorem mem_K_of_quad (γ : E) (p q : K) (h : γ * γ + ofK p * γ + ofK q = 0) : InK γ := by
  haveI : Module.Finite K E := Module.Finite.of_finite
  have hint : IsIntegral K γ := .of_finite K γ
  have hdvd := minpoly.degree_dvd hint
  rw [finrank_KE] at hdvd
  have hmonic : (X ^ 2 + C p * X + C q : K[X]).Monic := by monicity!
  have hroot : aeval γ (X ^ 2 + C p * X + C q : K[X]) = 0 := by
    simp only [map_add, map_mul, aeval_X_pow, aeval_C, aeval_X]
    rw [← h, ← ofK_eq, ← ofK_eq]; ring
  have hle := minpoly.min K γ hmonic hroot
  have hdeg : (X ^ 2 + C p * X + C q : K[X]).degree = 2 := by compute_degree!
  rw [hdeg, degree_eq_natDegree (minpoly.ne_zero hint)] at hle
  have hle' : (minpoly K γ).natDegree ≤ 2 := by exact_mod_cast hle
  have hpos := minpoly.natDegree_pos hint
  have h1 : (minpoly K γ).natDegree = 1 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : (minpoly K γ).natDegree
    · rfl
    · omega
  obtain ⟨a, ha⟩ := minpoly.natDegree_eq_one_iff.1 h1
  exact ⟨a, ha.symm⟩

/-- A root of a nonzero polynomial of degree at most `2` over `K` lies in `K`. -/
theorem mem_K_of_deg2 (s : E) (A B C' : K) (h : ofK A * (s * s) + ofK B * s + ofK C' = 0)
    (hne : A ≠ 0 ∨ B ≠ 0) : InK s := by
  by_cases hA : A = 0
  · have hB : B ≠ 0 := hne.resolve_left (not_not.2 hA)
    refine ⟨-(C' / B), ?_⟩
    rw [hA, ofK_zero, zero_mul, zero_add] at h
    have hB' := ofK_ne_zero hB
    rw [ofK_neg, ofK_div]
    field_simp
    linear_combination h
  · refine mem_K_of_quad s (B / A) (C' / A) ?_
    have hA' := ofK_ne_zero hA
    rw [ofK_div, ofK_div]
    field_simp
    linear_combination h

/-! ### Independence and spans -/

/-- Two elements of `E` are `K`-independent. -/
def Indep2 (y0 y1 : E) : Prop := ∀ a b : K, ofK a * y0 + ofK b * y1 = 0 → a = 0 ∧ b = 0

/-- Three elements of `E` are `K`-independent. -/
def Indep3 (y0 y1 y2 : E) : Prop :=
  ∀ a b c : K, ofK a * y0 + ofK b * y1 + ofK c * y2 = 0 → a = 0 ∧ b = 0 ∧ c = 0

/-- **Three `K`-independent elements span `E`**: `(a, b, c) ↦ a y₀ + b y₁ + c y₂` is injective, so onto,
`|K³| = |E|`. -/
theorem Indep3.spans {y0 y1 y2 : E} (h : Indep3 y0 y1 y2) (e : E) :
    ∃ a b c : K, ofK a * y0 + ofK b * y1 + ofK c * y2 = e := by
  classical
  let f : K × K × K → E := fun p ↦ ofK p.1 * y0 + ofK p.2.1 * y1 + ofK p.2.2 * y2
  have hinj : Function.Injective f := by
    intro p q hpq
    have hd : ofK (p.1 - q.1) * y0 + ofK (p.2.1 - q.2.1) * y1 + ofK (p.2.2 - q.2.2) * y2 = 0 := by
      simp only [f] at hpq
      rw [ofK_sub, ofK_sub, ofK_sub]
      linear_combination hpq
    obtain ⟨h1, h2, h3⟩ := h _ _ _ hd
    exact Prod.ext (sub_eq_zero.1 h1) (Prod.ext (sub_eq_zero.1 h2) (sub_eq_zero.1 h3))
  have hcard : Fintype.card (K × K × K) = Fintype.card E := by
    simp only [Fintype.card_prod, BF64.card_bf64, card_E]; norm_num
  obtain ⟨⟨a, b, c⟩, h⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩).2 e
  exact ⟨a, b, c, h⟩

/-- Independence is kept by a common nonzero factor. -/
theorem Indep3.mul {y0 y1 y2 : E} (h : Indep3 y0 y1 y2) {μ : E} (hμ : μ ≠ 0) :
    Indep3 (μ * y0) (μ * y1) (μ * y2) := fun a b c habc ↦
  h a b c ((mul_eq_zero.1 (by linear_combination habc : μ * (ofK a * y0 + ofK b * y1 + ofK c * y2) = 0)).resolve_left
    hμ)

theorem Indep2.mul {y0 y1 : E} (h : Indep2 y0 y1) {μ : E} (hμ : μ ≠ 0) : Indep2 (μ * y0) (μ * y1) :=
  fun a b hab ↦ h a b ((mul_eq_zero.1 (by linear_combination hab : μ * (ofK a * y0 + ofK b * y1) = 0)).resolve_left hμ)

/-- `y₀ ≠ 0` and `y₁ ∉ K y₀`: independent. -/
theorem indep2_of {y0 y1 : E} (h0 : y0 ≠ 0) (h1 : ∀ l : K, y1 ≠ ofK l * y0) : Indep2 y0 y1 := by
  intro a b hab
  by_cases hb : b = 0
  · rw [hb, ofK_zero, zero_mul, add_zero] at hab
    exact ⟨(map_eq_zero (algebraMap K E)).1 ((mul_eq_zero.1 hab).resolve_right h0), hb⟩
  · refine absurd ?_ (h1 (-(a / b)))
    have hb' := ofK_ne_zero hb
    rw [ofK_neg, ofK_div]
    field_simp
    linear_combination hab

/-- `y₀, y₁` independent and `y₂ ∉ K y₀ + K y₁`: independent. -/
theorem indep3_of {y0 y1 y2 : E} (h01 : Indep2 y0 y1) (h2 : ∀ a b : K, y2 ≠ ofK a * y0 + ofK b * y1) :
    Indep3 y0 y1 y2 := by
  intro a b c habc
  by_cases hc : c = 0
  · rw [hc, ofK_zero, zero_mul, add_zero] at habc
    exact ⟨(h01 a b habc).1, (h01 a b habc).2, hc⟩
  · refine absurd ?_ (h2 (-(a / c)) (-(b / c)))
    have hc' := ofK_ne_zero hc
    rw [ofK_neg, ofK_div, ofK_neg, ofK_div]
    field_simp
    linear_combination habc

/-- `s + γ ≠ 0` for `s ∉ K`. -/
theorem add_ofK_ne_zero {s : E} (hs : ¬ InK s) (g : K) : s + ofK g ≠ 0 := fun h ↦
  hs ⟨-g, by rw [ofK_neg]; linear_combination h⟩

/-- **For `s ∉ K` and distinct `γᵢ ∈ K`, the `1/(s + γᵢ)` are `K`-independent.** -/
theorem indep3_inv {s : E} (hs : ¬ InK s) {g1 g2 g3 : K} (h12 : g1 ≠ g2) (h13 : g1 ≠ g3) (h23 : g2 ≠ g3) :
    Indep3 (s + ofK g1)⁻¹ (s + ofK g2)⁻¹ (s + ofK g3)⁻¹ := by
  intro a b c habc
  have d1 := add_ofK_ne_zero hs g1
  have d2 := add_ofK_ne_zero hs g2
  have d3 := add_ofK_ne_zero hs g3
  -- Cleared of denominators: a quadratic in `s` over `K`.
  have hq : ofK (a + b + c) * (s * s) + ofK (a * (g2 + g3) + b * (g1 + g3) + c * (g1 + g2)) * s +
      ofK (a * g2 * g3 + b * g1 * g3 + c * g1 * g2) = 0 := by
    have h' : ofK a * ((s + ofK g2) * (s + ofK g3)) + ofK b * ((s + ofK g1) * (s + ofK g3)) +
        ofK c * ((s + ofK g1) * (s + ofK g2)) = 0 := by
      have := congrArg (· * ((s + ofK g1) * (s + ofK g2) * (s + ofK g3))) habc
      simp only [zero_mul] at this
      rw [← this]
      field_simp
    simp only [ofK_add, ofK_mul]
    linear_combination h'
  have hA : a + b + c = 0 := by
    by_contra hA
    exact hs (mem_K_of_deg2 s _ _ _ hq (Or.inl hA))
  have hB : a * (g2 + g3) + b * (g1 + g3) + c * (g1 + g2) = 0 := by
    by_contra hB
    exact hs (mem_K_of_deg2 s _ _ _ hq (Or.inr hB))
  have hC : a * g2 * g3 + b * g1 * g3 + c * g1 * g2 = 0 := by
    rw [hA, hB, ofK_zero, zero_mul, zero_mul, zero_add, zero_add] at hq
    exact (map_eq_zero (algebraMap K E)).1 hq
  -- The polynomial vanishes identically, so at each `γᵢ`.
  have two_K : (2 : K) = 0 := CharTwo.two_eq_zero
  have e1 : a * ((g1 + g2) * (g1 + g3)) = 0 := by
    linear_combination g1 * g1 * hA + g1 * hB + hC - (b * g1 * g1 + c * g1 * g1 + b * g1 * g3 + c * g1 * g2) * two_K
  have e2 : b * ((g2 + g1) * (g2 + g3)) = 0 := by
    linear_combination g2 * g2 * hA + g2 * hB + hC - (a * g2 * g2 + c * g2 * g2 + a * g2 * g3 + c * g1 * g2) * two_K
  have e3 : c * ((g3 + g1) * (g3 + g2)) = 0 := by
    linear_combination g3 * g3 * hA + g3 * hB + hC - (a * g3 * g3 + b * g3 * g3 + a * g2 * g3 + b * g1 * g3) * two_K
  have n : ∀ x y : K, x ≠ y → x + y ≠ 0 := fun x y hxy h ↦ hxy (by linear_combination h - y * two_K)
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.1 e1).resolve_right (mul_ne_zero (n _ _ h12) (n _ _ h13))
  · exact (mul_eq_zero.1 e2).resolve_right (mul_ne_zero (n _ _ h12.symm) (n _ _ h23))
  · exact (mul_eq_zero.1 e3).resolve_right (mul_ne_zero (n _ _ h13.symm) (n _ _ h23.symm))

/-! ### Planes -/

/-- **An element mapping a `K`-plane into itself lies in `K`**: on the plane it satisfies its characteristic
polynomial, a monic quadratic over `K`. -/
theorem inK_of_stab {y0 y1 γ : E} (h01 : Indep2 y0 y1) {a b c d : K}
    (h0 : γ * y0 = ofK a * y0 + ofK b * y1) (h1 : γ * y1 = ofK c * y0 + ofK d * y1) : InK γ := by
  have hy0 : y0 ≠ 0 := fun h ↦ by
    have := h01 1 0 (by rw [h, ofK_zero]; ring)
    exact one_ne_zero this.1
  refine mem_K_of_quad γ (-(a + d)) (a * d - b * c) ?_
  have : (γ * γ + ofK (-(a + d)) * γ + ofK (a * d - b * c)) * y0 = 0 := by
    rw [ofK_neg, ofK_add, ofK_sub, ofK_mul, ofK_mul]
    linear_combination (γ - ofK d) * h0 + ofK b * h1
  exact (mul_eq_zero.1 this).resolve_right hy0

theorem Indep2.left_ne_zero {y0 y1 : E} (h : Indep2 y0 y1) : y0 ≠ 0 := fun h0 ↦
  one_ne_zero (h 1 0 (by rw [h0, ofK_zero]; ring)).1

/-- **Two scalings of a plane into another differ by an element of `K`**: if `ρ w₀, ρ w₁, ρ' w₀, ρ' w₁` all lie in
the plane of `y₀, y₁`, with `w₀, w₁` independent and `ρ ≠ 0`, then `ρ' / ρ ∈ K`. -/
theorem inK_ratio_of_spans {y0 y1 w0 w1 ρ ρ' : E} (hw : Indep2 w0 w1) (hρ : ρ ≠ 0)
    {a b c d a' b' c' d' : K}
    (e0 : ρ * w0 = ofK a * y0 + ofK b * y1) (e1 : ρ * w1 = ofK c * y0 + ofK d * y1)
    (e0' : ρ' * w0 = ofK a' * y0 + ofK b' * y1) (e1' : ρ' * w1 = ofK c' * y0 + ofK d' * y1) :
    InK (ρ' / ρ) := by
  have hw' : Indep2 (ρ * w0) (ρ * w1) := hw.mul hρ
  -- The determinant is nonzero: else `ρ w₀, ρ w₁` would be dependent.
  have hD : ofK a * ofK d - ofK b * ofK c ≠ 0 := by
    intro hD
    have k1 := hw' d (-b) (by rw [e0, e1, ofK_neg]; linear_combination y0 * hD)
    have k2 := hw' (-c) a (by rw [e0, e1, ofK_neg]; linear_combination y1 * hD)
    refine hw'.left_ne_zero ?_
    rw [e0, k2.2, neg_eq_zero.1 k1.2, ofK_zero]; ring
  have hγ0 : ρ' / ρ * (ρ * w0) = ρ' * w0 := by field_simp
  have hγ1 : ρ' / ρ * (ρ * w1) = ρ' * w1 := by field_simp
  refine inK_of_stab hw' (a := (a' * d - b' * c) / (a * d - b * c)) (b := (a * b' - a' * b) / (a * d - b * c))
    (c := (c' * d - d' * c) / (a * d - b * c)) (d := (a * d' - c' * b) / (a * d - b * c)) ?_ ?_
  · rw [hγ0, e0', e0, e1]
    simp only [ofK_div, ofK_sub, ofK_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
    ring
  · rw [hγ1, e1', e0, e1]
    simp only [ofK_div, ofK_sub, ofK_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
    ring

/-! ### Four elements are dependent -/

/-- **Four elements of `E` are `K`-dependent**: `c ↦ Σ c_r A_r` on `K⁴` is not injective, `|K⁴| > |E|`. -/
theorem kernel4 (A : Fin 4 → E) : ∃ c : Fin 4 → K, c ≠ 0 ∧ ∑ r, ofK (c r) * A r = 0 := by
  classical
  let f : (Fin 4 → K) → E := fun c ↦ ∑ r, ofK (c r) * A r
  have hnot : ¬ Function.Injective f := by
    intro hinj
    have := Fintype.card_le_of_injective f hinj
    rw [Fintype.card_fun, BF64.card_bf64, card_E, Fintype.card_fin] at this
    norm_num at this
  obtain ⟨c, c', hcc, hne⟩ : ∃ c c', f c = f c' ∧ c ≠ c' := by
    by_contra h
    push Not at h
    exact hnot fun c c' hc ↦ h c c' hc
  refine ⟨c - c', sub_ne_zero.2 hne, ?_⟩
  simp only [f] at hcc
  simp only [Pi.sub_apply, ofK_sub, sub_mul, Finset.sum_sub_distrib, hcc, sub_self]

end PcsQuotient.EndToEnd.Group1
