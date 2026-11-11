-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Extends `formal/Completeness/Completeness/Reduction.lean` (the previous protocol's degenerate challenges)
-- with the PCS claims' two denominators. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch
-- `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the field `E` of `2^192` elements.
import E2ECompleteness.PcsHonest

/-!
# The degenerate challenges of the PCS claims' reduction

The new reduction (`claimsAt`) inverts two more denominators than the previous one: the copy identity's
product `d d'` and `1 + ρ`. A quadruple `(α, β, t, ρ)` is **degenerate** for a first message `g`
(`BadP4`) when the honest sum does not exist (`BadAB`), the previous Rust check fails (`Degenerate`), the
product `d(t) d'(t)` vanishes, or `ρ = 1`. **`card_badP4_le`**: of the `q^4` quadruples at most
`(19 · 2^24 + 31) q^3` are degenerate: the previous `(17 · 2^24 + 8) q^2` triples, at a good pair `(α, β)` at
most `2^25 + 22` roots `t` of `d d'` (a nonzero polynomial: it does not vanish at a cell), and one `ρ`.
**`badP4_fraction_le`**: over `E` (`2^192` elements) the fraction is at most `(19 · 2^24 + 31) / 2^192`,
below `2^-163` (`bad4_bound_lt`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM.Parameters QuotientSecurity
open scoped ENNReal

namespace E2ECompleteness.Pcs

variable (I : Instance E)

/-- **A degenerate quadruple** `(α, β, t, ρ)` for the first message `g`. -/
def BadP4 (g : Fin 4 → E[X]) (x : E × E × E × E) : Prop :=
  Completeness.Reduction.BadAB I g x.1 x.2.1 ∨ Completeness.Reduction.Degenerate I g x.1 x.2.1 x.2.2.1 ∨
    (Params.dPoly I.params g x.1 x.2.1 * Params.dNextPoly I.params g x.1 x.2.1).eval x.2.2.1 = 0 ∨
    x.2.2.2 = 1

/-- `d d'` does not vanish as a polynomial at a good pair. -/
theorem dd_ne_zero (g : Fin 4 → E[X]) (α β : E) (hab : ¬ Completeness.Reduction.BadAB I g α β) :
    Params.dPoly I.params g α β * Params.dNextPoly I.params g α β ≠ 0 := by
  classical
  obtain ⟨i₀⟩ : Nonempty (I.params.T × Fin 4) := ⟨I.cellEquiv fun _ ↦ false⟩
  intro h
  have h' := congrArg (fun p : E[X] ↦ p.eval (I.params.pt i₀)) h
  rw [Polynomial.eval_mul, Polynomial.eval_zero, Params.dPoly_eval_pt, Params.dNextPoly_eval_pt] at h'
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact hab ⟨i₀, Or.inl h0⟩
  · exact hab ⟨i₀, Or.inr h0⟩

/-- **Counting, for any finite field**: triples bad with density `A`, then at a good pair the roots of a
nonzero polynomial of degree at most `D`, then one value of the last coordinate. -/
theorem card_quad_le {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] [SampleableType F] (B3 : F × F × F → Prop)
    [DecidablePred B3] (AB : F → F → Prop) [∀ a b, Decidable (AB a b)] (P : F → F → F[X]) (A D : ℕ)
    (hB3 : (univ.filter B3).card ≤ A * Fintype.card F ^ 2)
    (hP : ∀ a b, ¬ AB a b → P a b ≠ 0 ∧ (P a b).natDegree ≤ D) :
    (univ.filter fun x : F × F × F × F ↦ B3 (x.1, x.2.1, x.2.2.1) ∨
        (¬ AB x.1 x.2.1 ∧ (P x.1 x.2.1).eval x.2.2.1 = 0) ∨ x.2.2.2 = 1).card ≤
      (A + D + 1) * Fintype.card F ^ 3 := by
  classical
  set q := Fintype.card F
  set S₁ := univ.filter fun x : F × F × F × F ↦ B3 (x.1, x.2.1, x.2.2.1)
  set S₂ := univ.filter fun x : F × F × F × F ↦ ¬ AB x.1 x.2.1 ∧ (P x.1 x.2.1).eval x.2.2.1 = 0
  set S₃ := univ.filter fun x : F × F × F × F ↦ x.2.2.2 = 1
  have hsub : (univ.filter fun x : F × F × F × F ↦ B3 (x.1, x.2.1, x.2.2.1) ∨
      (¬ AB x.1 x.2.1 ∧ (P x.1 x.2.1).eval x.2.2.1 = 0) ∨ x.2.2.2 = 1) ⊆ S₁ ∪ S₂ ∪ S₃ := by
    intro x hx
    obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
    simp only [S₁, S₂, S₃, mem_union, Finset.mem_filter, mem_univ, true_and]
    rcases hx with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have h₁ : S₁.card ≤ A * q ^ 2 * q := by
    have hs : S₁ ⊆ ((univ.filter B3) ×ˢ (univ : Finset F)).image
        fun p ↦ (p.1.1, p.1.2.1, p.1.2.2, p.2) := by
      intro x hx
      obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_image.mpr ⟨((x.1, x.2.1, x.2.2.1), x.2.2.2),
        Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, hx⟩, mem_univ _⟩, rfl⟩
    refine (card_le_card hs).trans (card_image_le.trans ?_)
    rw [card_product, card_univ]
    exact Nat.mul_le_mul_right _ hB3
  have h₂ : S₂.card ≤ q * q * (D * q) := by
    let R : F × F → Finset (F × F × F × F) := fun p ↦
      if AB p.1 p.2 then ∅ else
        ((univ.filter fun t : F ↦ (P p.1 p.2).eval t = 0) ×ˢ (univ : Finset F)).image
          fun tr ↦ (p.1, p.2, tr.1, tr.2)
    have hs : S₂ ⊆ (univ : Finset (F × F)).biUnion R := by
      intro x hx
      obtain ⟨-, hab, hx⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_biUnion.mpr ⟨(x.1, x.2.1), mem_univ _, ?_⟩
      simp only [R, hab, ↓reduceIte]
      exact Finset.mem_image.mpr ⟨(x.2.2.1, x.2.2.2),
        Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, hx⟩, mem_univ _⟩, rfl⟩
    have hR : ∀ p, (R p).card ≤ D * q := fun p ↦ by
      simp only [R]
      split_ifs with hb
      · simp
      · refine card_image_le.trans ?_
        rw [card_product, card_univ]
        exact Nat.mul_le_mul_right _ (Completeness.card_filter_eval_eq_zero_le _ (hP _ _ hb).1
          (hP _ _ hb).2)
    refine (card_le_card hs).trans (card_biUnion_le.trans ((sum_le_sum fun p _ ↦ hR p).trans
      (le_of_eq ?_)))
    rw [sum_const, card_univ, Fintype.card_prod, smul_eq_mul]
  have h₃ : S₃.card ≤ q ^ 3 := by
    have hs : S₃ ⊆ (univ : Finset (F × F × F)).image fun p ↦ (p.1, p.2.1, p.2.2, (1 : F)) := by
      intro x hx
      obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_image.mpr ⟨(x.1, x.2.1, x.2.2.1), mem_univ _, by rw [← hx]⟩
    refine (card_le_card hs).trans (card_image_le.trans (le_of_eq ?_))
    rw [card_univ, Fintype.card_prod, Fintype.card_prod]
    ring
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add
    ((card_union_le _ _).trans (add_le_add h₁ h₂)) h₃) |>.trans (le_of_eq ?_))
  ring

open Classical in
/-- **The degenerate quadruples**: at most `(19 · 2^24 + 31) q^3`. -/
theorem card_badP4_le (g : Fin 4 → E[X]) (hg : ∀ j, (g j).natDegree ≤ 2 ^ 22 + 2) :
    (univ.filter fun x : E × E × E × E ↦ BadP4 I g x).card ≤
      (19 * 2 ^ 24 + 31) * Fintype.card E ^ 3 := by
  have hg23 : ∀ j, (g j).natDegree ≤ 2 ^ 23 := fun j ↦ (hg j).trans (by norm_num)
  have h := card_quad_le
    (fun x : E × E × E ↦ Completeness.Reduction.BadAB I g x.1 x.2.1 ∨
      Completeness.Reduction.Degenerate I g x.1 x.2.1 x.2.2)
    (fun a b ↦ Completeness.Reduction.BadAB I g a b)
    (fun a b ↦ Params.dPoly I.params g a b * Params.dNextPoly I.params g a b) (17 * 2 ^ 24 + 8)
    33554454 (Completeness.Reduction.card_bad_le I g hg23)
    (fun a b hb ↦ ⟨dd_ne_zero I g a b hb, natDegree_dd_le I g hg a b⟩)
  refine (card_le_card fun x hx ↦ ?_).trans (h.trans (le_of_eq (by ring)))
  obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩
  unfold BadP4 at hx
  by_cases hab : Completeness.Reduction.BadAB I g x.1 x.2.1
  · exact Or.inl (Or.inl hab)
  · rcases hx with h | h | h | h
    · exact absurd h hab
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl ⟨hab, h⟩)
    · exact Or.inr (Or.inr h)

open Classical in
/-- **The fraction of degenerate quadruples** over `E`: at most `(19 · 2^24 + 31) / 2^192`. -/
theorem badP4_fraction_le (g : Fin 4 → E[X]) (hg : ∀ j, (g j).natDegree ≤ 2 ^ 22 + 2) :
    ((univ.filter fun x : E × E × E × E ↦ BadP4 I g x).card : ℝ≥0∞) / 2 ^ 768 ≤
      (19 * 2 ^ 24 + 31 : ℝ≥0∞) / 2 ^ 192 := by
  have h := card_badP4_le I g hg
  rw [LeanVM.Protocol.card_E] at h
  have h' : ((univ.filter fun x : E × E × E × E ↦ BadP4 I g x).card : ℝ≥0∞) ≤
      (19 * 2 ^ 24 + 31) * (2 ^ 192) ^ 3 := by exact_mod_cast h
  calc _ ≤ (19 * 2 ^ 24 + 31) * (2 ^ 192) ^ 3 / 2 ^ 768 := ENNReal.div_le_div_right h' _
    _ = (19 * 2 ^ 24 + 31 : ℝ≥0∞) / 2 ^ 192 := by
        rw [show (2 : ℝ≥0∞) ^ 768 = 2 ^ 192 * (2 ^ 192) ^ 3 by rw [← pow_mul, ← pow_add],
          ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

/-- The number, below `2^-163`. -/
theorem bad4_bound_lt : (19 * 2 ^ 24 + 31 : ℝ≥0∞) / 2 ^ 192 < 2⁻¹ ^ 163 := by
  have h1 : (19 * 2 ^ 24 + 31 : ℝ≥0∞) / 2 ^ 192 < 2 ^ 29 / 2 ^ 192 :=
    ENNReal.div_lt_div_right (by simp) (by simp) (by norm_num)
  have h2 : (2 ^ 29 : ℝ≥0∞) / 2 ^ 192 = 2⁻¹ ^ 163 := by
    have e : (2 : ℝ≥0∞) ^ 29 / 2 ^ 192 = (2 ^ 29 * 1) / (2 ^ 29 * 2 ^ 163) := by norm_num
    rw [e, ENNReal.mul_div_mul_left _ _ (by simp) (by simp), one_div, ENNReal.inv_pow]
  exact h2 ▸ h1

end E2ECompleteness.Pcs
