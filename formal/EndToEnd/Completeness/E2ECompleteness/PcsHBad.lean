-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this directory's previous `PcsBad.lean` (`card_quad_le`) to the deployed protocol's degenerate
-- challenges. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the field `E` of `2^192` elements.
import E2ECompleteness.PcsHHonest
import Completeness.Reduction

/-!
# The degenerate challenges are rare

`badSet w coins` (`PcsHHonest.lean`) is contained in the quadruples `(α, β, t, ρ)` where

* `(α, β)` is bad (`ABad`): `β = 0`, or a cell's copy denominator vanishes (at most `2 · 2^24` values of `α` for
  each `β`), or `γ(α, β) = (E /ₘ Z)(0)` vanishes with `β ≠ 0`: `γ = α β s + r(β)` with `s = σ̂_{n−2} ≠ 0` (the
  evaluated check `WiringCheck`), so one `α` for each `β`;
* or `t` is a root of `tPoly α β` (the product of `claimsAt`'s denominators at `t`, a nonzero polynomial of degree
  at most `5 · 2^24` at a good pair);
* or `ρ` is the one root of the conic's denominator at `t`.

**`card_badSet_le`**: at most `(7 · 2^24 + 3) q³` quadruples; **`badSet_density`**: a fraction at most
`(7 · 2^24 + 3) / 2^192`.

**`WiringCheck`** is the only hypothesis: the circuit's wiring table has entry `2^24 − 1` zero and entry `2^24 − 2`
nonzero, an evaluated check on the deployed circuit's constant table.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity
open scoped ENNReal

attribute [local irreducible] PcsQuotient.membership PcsQuotient.membershipBuilder

namespace E2ECompleteness.Pcs.H

/-! ## Counting quadruples -/

theorem card_quad_le {F : Type} [Fintype F] [DecidableEq F] [Field F] [CharP F 2] [SampleableType F] (AB : F → F → Prop) [∀ a b, Decidable (AB a b)]
    (P : F → F → F[X]) (R : F → F → Prop) [∀ a b, Decidable (R a b)] (A D : ℕ)
    (hAB : (univ.filter fun p : F × F => AB p.1 p.2).card ≤ A * Fintype.card F)
    (hP : ∀ a b, ¬ AB a b → P a b ≠ 0 ∧ (P a b).natDegree ≤ D)
    (hR : ∀ t, (univ.filter fun ρ => R t ρ).card ≤ 1) :
    (univ.filter fun x : F × F × F × F => AB x.1 x.2.1 ∨ (¬ AB x.1 x.2.1 ∧ (P x.1 x.2.1).eval x.2.2.1 = 0) ∨
        R x.2.2.1 x.2.2.2).card ≤ (A + D + 1) * Fintype.card F ^ 3 := by
  set q := Fintype.card F
  set S₁ := univ.filter fun x : F × F × F × F => AB x.1 x.2.1
  set S₂ := univ.filter fun x : F × F × F × F => ¬ AB x.1 x.2.1 ∧ (P x.1 x.2.1).eval x.2.2.1 = 0
  set S₃ := univ.filter fun x : F × F × F × F => R x.2.2.1 x.2.2.2
  have hsub : (univ.filter fun x : F × F × F × F => AB x.1 x.2.1 ∨ (¬ AB x.1 x.2.1 ∧ (P x.1 x.2.1).eval x.2.2.1 = 0) ∨
      R x.2.2.1 x.2.2.2) ⊆ S₁ ∪ S₂ ∪ S₃ := by
    intro x hx
    obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
    simp only [S₁, S₂, S₃, mem_union, Finset.mem_filter, mem_univ, true_and]
    rcases hx with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have h₁ : S₁.card ≤ A * q * (q * q) := by
    have hs : S₁ ⊆ ((univ.filter fun p : F × F => AB p.1 p.2) ×ˢ (univ : Finset (F × F))).image
        fun p ↦ (p.1.1, p.1.2, p.2.1, p.2.2) := by
      intro x hx
      obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_image.mpr ⟨((x.1, x.2.1), (x.2.2.1, x.2.2.2)),
        Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, hx⟩, mem_univ _⟩, rfl⟩
    refine (card_le_card hs).trans (card_image_le.trans ?_)
    rw [card_product, card_univ, Fintype.card_prod]
    exact Nat.mul_le_mul_right _ hAB
  have h₂ : S₂.card ≤ q * q * (D * q) := by
    let Rs : F × F → Finset (F × F × F × F) := fun p ↦
      if AB p.1 p.2 then ∅ else
        ((univ.filter fun t : F ↦ (P p.1 p.2).eval t = 0) ×ˢ (univ : Finset F)).image
          fun tr ↦ (p.1, p.2, tr.1, tr.2)
    have hs : S₂ ⊆ (univ : Finset (F × F)).biUnion Rs := by
      intro x hx
      obtain ⟨-, hab, hx⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_biUnion.mpr ⟨(x.1, x.2.1), mem_univ _, ?_⟩
      simp only [Rs, hab, ↓reduceIte]
      exact Finset.mem_image.mpr ⟨(x.2.2.1, x.2.2.2),
        Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, hx⟩, mem_univ _⟩, rfl⟩
    have hRs : ∀ p, (Rs p).card ≤ D * q := fun p ↦ by
      simp only [Rs]
      split_ifs with hb
      · simp
      · refine card_image_le.trans ?_
        rw [card_product, card_univ]
        exact Nat.mul_le_mul_right _ (Completeness.card_filter_eval_eq_zero_le _ (hP _ _ hb).1
          (hP _ _ hb).2)
    refine (card_le_card hs).trans (card_biUnion_le.trans ((sum_le_sum fun p _ ↦ hRs p).trans
      (le_of_eq ?_)))
    rw [sum_const, card_univ, Fintype.card_prod, smul_eq_mul]
  have h₃ : S₃.card ≤ q * q * (q * 1) := by
    have hs : S₃ ⊆ ((univ : Finset (F × F × F))).biUnion fun p =>
        (univ.filter fun ρ => R p.2.2 ρ).image fun ρ => (p.1, p.2.1, p.2.2, ρ) := by
      intro x hx
      obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_biUnion.mpr ⟨(x.1, x.2.1, x.2.2.1), mem_univ _,
        Finset.mem_image.mpr ⟨x.2.2.2, Finset.mem_filter.mpr ⟨mem_univ _, hx⟩, rfl⟩⟩
    refine (card_le_card hs).trans (card_biUnion_le.trans ((sum_le_sum fun p _ =>
      card_image_le.trans (hR p.2.2)).trans (le_of_eq ?_)))
    rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_prod, smul_eq_mul]
    ring
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add
    ((card_union_le _ _).trans (add_le_add h₁ h₂)) h₃) |>.trans (le_of_eq ?_))
  ring

/-! ## The novel basis's coefficients -/

theorem nov_coeff (k : ℕ) (f : ℕ → E) {j : ℕ} (hj : j < 2 ^ k) (hz : ∀ i, j < i → i < 2 ^ k → f i = 0) :
    (Novel.nov 0 k f).coeff j = f j := by
  unfold Novel.nov
  rw [finset_sum_coeff, Finset.sum_eq_single j]
  · have h1 : (Novel.basisAt (F := E) 0 k j).coeff j = 1 := by
      have := (Novel.basisAt_monic (F := E) k j).coeff_natDegree
      rwa [Novel.natDegree_basisAt (F := E) k j hj] at this
    rw [coeff_C_mul, h1, mul_one]
  · intro i hi hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by rw [Novel.natDegree_basisAt (F := E) k i (Finset.mem_range.mp hi)]; exact h),
        mul_zero]
    · rw [hz i h (Finset.mem_range.mp hi), C_0, zero_mul, coeff_zero]
  · intro h; exact absurd (Finset.mem_range.mpr hj) h

/-! ## `(f /ₘ Z)(0)` is linear -/

theorem phi_add (Z : E[X]) (hZ : Z.Monic) (f g : E[X]) : ((f + g) /ₘ Z).eval 0 = (f /ₘ Z).eval 0 + (g /ₘ Z).eval 0 := by
  rw [Novel.divByMonic_add hZ, Polynomial.eval_add]

theorem phi_C_mul (Z : E[X]) (hZ : Z.Monic) (a : E) (f : E[X]) : ((C a * f) /ₘ Z).eval 0 = a * (f /ₘ Z).eval 0 := by
  rw [Novel.divByMonic_C_mul hZ, Polynomial.eval_mul, Polynomial.eval_C]

/-! ## The conic's denominator vanishes at one `ρ` at most -/

theorem conic_card_gen (c θ : E) :
    (univ.filter fun ρ : E => c * (1 + ρ) + ρ + θ * (1 + ρ) = 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have ha' := ha
  have hb' := hb
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  by_contra hab
  have hsub : (a + b) * (c + θ + 1) = 0 := by linear_combination (norm := char2_norm) ha' + hb'
  rcases mul_eq_zero.mp hsub with h | h
  · exact hab (CharTwo.add_eq_zero.mp h)
  · have h1 : (1 : E) = 0 := by linear_combination (norm := char2_norm) ha' - (1 + a) * h
    exact one_ne_zero h1

theorem conic_card_le (t : E) :
    (univ.filter fun ρ : E => (witnessConic t (QuotientSecurity.sq t) ρ).1 + (witnessConic t (QuotientSecurity.sq t) ρ).2 = 0).card
      ≤ 1 :=
  conic_card_gen (t + QuotientSecurity.sq t * ofK (betaAt 1)) (ofK (betaAt 1))

end E2ECompleteness.Pcs.H
