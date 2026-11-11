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

/-- `card_quad_le` for a set of quadruples each degenerate, counted by `Nat.card`. -/
theorem card_quad_le' {F : Type} [Fintype F] [DecidableEq F] [Field F] [CharP F 2] [SampleableType F] (AB : F → F → Prop)
    (P : F → F → F[X]) (R : F → F → Prop) (A D : ℕ) (S : Finset (F × F × F × F))
    (hS : ∀ x ∈ S, AB x.1 x.2.1 ∨ (¬ AB x.1 x.2.1 ∧ (P x.1 x.2.1).eval x.2.2.1 = 0) ∨ R x.2.2.1 x.2.2.2)
    (hAB : ∀ T : Finset (F × F), (∀ p ∈ T, AB p.1 p.2) → T.card ≤ A * Nat.card F)
    (hP : ∀ a b, ¬ AB a b → P a b ≠ 0 ∧ (P a b).natDegree ≤ D)
    (hR : ∀ t (T : Finset F), (∀ ρ ∈ T, R t ρ) → T.card ≤ 1) :
    S.card ≤ (A + D + 1) * Nat.card F ^ 3 := by
  classical
  rw [Nat.card_eq_fintype_card] at hAB ⊢
  refine (card_le_card fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS x hx⟩).trans
    (card_quad_le AB P R A D (hAB _ fun p hp => (Finset.mem_filter.mp hp).2) hP
      fun t => hR t _ fun ρ hρ => (Finset.mem_filter.mp hρ).2)

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

theorem conic_card_gen' (c θ : E) (T : Finset E) (hT : ∀ ρ ∈ T, c * (1 + ρ) + ρ + θ * (1 + ρ) = 0) :
    T.card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  have ha' := hT a ha
  have hb' := hT b hb
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

/-! ## `γ` is affine in `α` -/

section Gen

variable (P : _root_.Kc3.Params E) (c : (Fin 24 → Bool) → E)

/-- `s = ((X² + X)(X + σ) /ₘ Z)(0)`, the coefficient of `α β` in `γ`. -/
noncomputable def sCoef : E := (((X ^ 2 + X) * (X + P.sigmaPoly)) /ₘ P.vCells).eval 0

/-- `r(β)`, the part of `γ` without `α`. -/
noncomputable def rCoef (β : E) : E :=
  (((X ^ 2 + X) * (P.cellPoly (witnessOfTable (k := 22) c) 0 + C β * X) *
    (P.cellPoly (witnessOfTable (k := 22) c) 0 + C β * P.sigmaPoly)) /ₘ P.vCells).eval 0

theorem Epoly_split (α β : E) :
    Epoly P α β c = C α * C α * (X ^ 2 + X) + C α * C β * ((X ^ 2 + X) * (X + P.sigmaPoly)) +
      (X ^ 2 + X) * (P.cellPoly (witnessOfTable (k := 22) c) 0 + C β * X) *
        (P.cellPoly (witnessOfTable (k := 22) c) 0 + C β * P.sigmaPoly) := by
  rw [Epoly_eq]
  unfold _root_.Kc3.Params.dPoly _root_.Kc3.Params.dNextPoly
  have h2 : (2 : E[X]) = 0 := CharTwo.two_eq_zero
  linear_combination ((X ^ 2 + X) * C α * P.cellPoly (witnessOfTable (k := 22) c) 0) * h2

/-- **`γ = α β s + r(β)`.** -/
theorem gamma_split (hZ : P.vCells = digitPoly 24) (α β : E) :
    (Epoly P α β c /ₘ P.vCells).eval 0 = α * β * sCoef P + rCoef P c β := by
  have hmon : P.vCells.Monic := by rw [hZ]; exact Novel.digit_monic 24
  have hw : ((X ^ 2 + X : E[X]) /ₘ P.vCells) = 0 := by
    refine Novel.divByMonic_of_lt hmon ?_
    rw [hZ, Novel.digit_natDegree]
    exact lt_of_le_of_lt (natDegree_add_le_of_degree_le (natDegree_X_pow_le 2) (natDegree_X_le.trans (by norm_num)))
      (by norm_num)
  rw [Epoly_split, phi_add _ hmon, phi_add _ hmon, mul_assoc (C α) (C α), phi_C_mul _ hmon, phi_C_mul _ hmon,
    hw, mul_assoc (C α) (C β), phi_C_mul _ hmon, phi_C_mul _ hmon, sCoef, rCoef, eval_zero]
  ring

/-- **At most one `α` makes `γ` vanish** for `β ≠ 0` when `s ≠ 0`. -/
theorem gamma_root_unique (hZ : P.vCells = digitPoly 24) (hs : sCoef P ≠ 0) {β : E} (hβ : β ≠ 0) {α α' : E}
    (h : (Epoly P α β c /ₘ P.vCells).eval 0 = 0) (h' : (Epoly P α' β c /ₘ P.vCells).eval 0 = 0) : α = α' := by
  rw [gamma_split P c hZ] at h h'
  have : (α - α') * (β * sCoef P) = 0 := by linear_combination h - h'
  rcases mul_eq_zero.mp this with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 (mul_ne_zero hβ hs)

/-- **`s` is the wiring table's entry `2^24 − 2`** when its entry `2^24 − 1` is zero. -/
theorem sCoef_eq (hZ : P.vCells = digitPoly 24) (wt : Array K) (hS : P.sigmaPoly = Novel.nov 0 24 fun j => ofK (wt.getD j 0))
    (htop : wt.getD (2 ^ 24 - 1) 0 = 0) : sCoef P = ofK (wt.getD (2 ^ 24 - 2) 0) := by
  have hmon : P.vCells.Monic := by rw [hZ]; exact Novel.digit_monic 24
  have hR : (P.vCells - X ^ (2 ^ 24)).natDegree ≤ 2 ^ 24 - 2 := by
    rw [hZ]; exact (Novel.digitPoly_sub_le 24).trans (by norm_num)
  have hSd : P.sigmaPoly.natDegree ≤ 2 ^ 24 - 1 := by
    rw [hS]; have := Novel.natDegree_nov_lt 24 (fun j => ofK (wt.getD j 0)); omega
  have hf : ((X ^ 2 + X) * (X + P.sigmaPoly)).natDegree ≤ 2 ^ 24 + 1 := by
    refine natDegree_mul_le_of_le (m := 2) (n := 2 ^ 24 - 1)
      (natDegree_add_le_of_degree_le (natDegree_X_pow_le 2) (natDegree_X_le.trans (by norm_num)))
      (natDegree_add_le_of_degree_le (natDegree_X_le.trans (by norm_num)) hSd) |>.trans (by norm_num)
  rw [sCoef, Novel.divByMonic_eval_zero (2 ^ 24) (by norm_num) _ hmon hR _ hf]
  have e : (X ^ 2 + X) * (X + P.sigmaPoly) = X ^ 3 + X ^ 2 + X ^ 2 * P.sigmaPoly + X * P.sigmaPoly := by ring
  have hc1 : P.sigmaPoly.coeff (2 ^ 24 - 1) = 0 := by
    rw [hS, nov_coeff 24 _ (by norm_num) (fun i h1 h2 => by omega), htop, Compose.Reduce.ofK_zero]
  have hc2 : P.sigmaPoly.coeff (2 ^ 24 - 2) = ofK (wt.getD (2 ^ 24 - 2) 0) := by
    rw [hS, nov_coeff 24 _ (by norm_num) (fun i h1 h2 => by
      rw [show i = 2 ^ 24 - 1 by omega, htop, Compose.Reduce.ofK_zero])]
  rw [e, coeff_add, coeff_add, coeff_add, coeff_X_pow, coeff_X_pow, if_neg (by norm_num), if_neg (by norm_num),
    coeff_X_pow_mul', if_pos (by norm_num), show 2 ^ 24 = (2 ^ 24 - 1) + 1 from by norm_num, coeff_X_mul,
    show 2 ^ 24 - 1 + 1 - 2 = 2 ^ 24 - 2 from by norm_num, hc1, hc2]
  ring

end Gen

/-! ## `claimsAt`'s denominators at `t`, as one polynomial -/

section TPoly

variable (P : _root_.Kc3.Params E) (g : Fin 4 → E[X])

/-- The product of `claimsAt`'s denominators at `t` (but the conic's). -/
noncomputable def tPoly (α β : E) : E[X] :=
  (∏ k ∈ range 24, (1 + digitPoly k)) * (1 + digitPoly 24 * X) *
    (digitPoly 24 * X + P.dPoly g α β * P.dNextPoly g α β) * P.vRows *
    ∏ k ∈ range 11, (X + C (PcsBridge.Kc3.pinE k))

theorem one_add_digit_ne (k : ℕ) : (1 + digitPoly k : E[X]) ≠ 0 := by
  intro h
  have := congrArg (fun p : E[X] => p.eval 0) h
  simp only [Polynomial.eval_add, eval_one, Novel.digitPoly_eval_zero, add_zero, eval_zero] at this
  exact one_ne_zero this

theorem X_add_C_ne (a : E) : (X + C a : E[X]) ≠ 0 := X_add_C_ne_zero a

theorem tPoly_ne_zero (hZ : P.vCells = digitPoly 24) (α β : E) (i₀ : P.T × Fin 4)
    (h₀ : α + P.cells g i₀ + β * P.pt i₀ ≠ 0 ∧ α + P.cells g i₀ + β * P.pt (P.σ i₀) ≠ 0) :
    tPoly P g α β ≠ 0 := by
  unfold tPoly
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
  · exact Finset.prod_ne_zero_iff.mpr fun k _ => one_add_digit_ne k
  · intro h
    have := congrArg (fun p : E[X] => p.eval 0) h
    simp only [Polynomial.eval_add, Polynomial.eval_mul, eval_one, Novel.digitPoly_eval_zero, zero_mul, add_zero,
      eval_zero] at this
    exact one_ne_zero this
  · intro h
    have := congrArg (fun p : E[X] => p.eval (P.pt i₀)) h
    simp only [Polynomial.eval_add, Polynomial.eval_mul, eval_zero] at this
    rw [← hZ, P.vCells_eval_pt, zero_mul, zero_add, P.dPoly_eval_pt, P.dNextPoly_eval_pt] at this
    exact mul_ne_zero h₀.1 h₀.2 this
  · unfold _root_.Kc3.Params.vRows
    exact (monic_prod_of_monic _ _ fun x _ => monic_X_sub_C _).ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun k _ => X_add_C_ne _

theorem tPoly_natDegree_le (hcard : P.T.card = 2 ^ 22) (gm : P.Msg₁) (hg : gm.1 = g) (α β : E) :
    (tPoly P g α β).natDegree ≤ 5 * 2 ^ 24 := by
  have hn : P.nCells = 2 ^ 24 := by rw [_root_.Kc3.Params.nCells_eq, hcard]; norm_num
  have hd := Kc3.Honest.natDegree_d_le P gm α β
  have hd' := Kc3.Honest.natDegree_d'_le P gm α β
  rw [hg, hn] at hd hd'
  have h1 : (∏ k ∈ range 24, (1 + digitPoly k : E[X])).natDegree ≤ 2 ^ 24 := by
    refine (natDegree_prod_le _ _).trans ?_
    have : ∀ k ∈ range 24, (1 + digitPoly k : E[X]).natDegree ≤ 2 ^ k := fun k _ =>
      natDegree_add_le_of_degree_le (natDegree_one.le.trans (Nat.zero_le _)) (Novel.digit_natDegree k).le
    refine (Finset.sum_le_sum this).trans ?_
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have h2 : (1 + digitPoly 24 * X : E[X]).natDegree ≤ 2 ^ 24 + 1 :=
    natDegree_add_le_of_degree_le (natDegree_one.le.trans (Nat.zero_le _))
      (natDegree_mul_le_of_le (Novel.digit_natDegree 24).le natDegree_X_le)
  have h3 : (digitPoly 24 * X + P.dPoly g α β * P.dNextPoly g α β : E[X]).natDegree ≤ 2 ^ 25 :=
    natDegree_add_le_of_degree_le ((natDegree_mul_le_of_le (Novel.digit_natDegree 24).le natDegree_X_le).trans
      (by norm_num)) ((natDegree_mul_le_of_le hd hd').trans (by norm_num))
  have h4 : P.vRows.natDegree ≤ 2 ^ 22 := by
    unfold _root_.Kc3.Params.vRows
    refine (natDegree_prod_le _ _).trans ?_
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_coe, hcard,
      le_refl]
  have h5 : (∏ k ∈ range 11, (X + C (PcsBridge.Kc3.pinE k))).natDegree ≤ 11 := by
    refine (natDegree_prod_le _ _).trans ?_
    simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, le_refl]
  unfold tPoly
  refine (natDegree_mul_le_of_le (natDegree_mul_le_of_le (natDegree_mul_le_of_le (natDegree_mul_le_of_le h1 h2) h3)
    h4) h5).trans (by norm_num)

end TPoly

/-! ## The good challenges -/

section Good

variable (P : _root_.Kc3.Params E) (hM : PcsBridge.Kc3.Matches P s₀) (w : Secret) (coins : Coins)

/-- `(α, β)` is degenerate. -/
def ABad (α β : E) : Prop :=
  β = 0 ∨ ¬ (∀ i : P.T × Fin 4, α + P.cells (gH w coins) i + β * P.pt i ≠ 0 ∧
    α + P.cells (gH w coins) i + β * P.pt (P.σ i) ≠ 0) ∨
    (Epoly P α β (cW w coins) /ₘ P.vCells).eval 0 = 0

/-- The conic's denominator vanishes. -/
def RBad (t ρ : E) : Prop :=
  (witnessConic t (QuotientSecurity.sq t) ρ).1 + (witnessConic t (QuotientSecurity.sq t) ρ).2 = 0

include hM

/-- **Off the degenerate challenges, no denominator vanishes.** -/
theorem goodAt_of (α β t ρ : E) (hab : ¬ ABad P w coins α β) (ht : (tPoly P (gH w coins) α β).eval t ≠ 0)
    (hρ : ¬ RBad t ρ) : GoodAt w coins P α β t ρ := by
  simp only [ABad, not_or, not_not] at hab
  obtain ⟨-, hcells, hγ⟩ := hab
  unfold tPoly at ht
  simp only [Polynomial.eval_mul, Polynomial.eval_prod] at ht
  obtain ⟨h1234, h5⟩ := mul_ne_zero_iff.mp ht
  obtain ⟨h123, h4⟩ := mul_ne_zero_iff.mp h1234
  obtain ⟨h12, h3⟩ := mul_ne_zero_iff.mp h123
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h12
  have hv0 : P.rowValues (_root_.Kc3.Params.opened (gH w coins) t) t 0 = (P.cellPoly (gH w coins) 0).eval t := by
    show P.cellAt (_root_.Kc3.Params.opened (gH w coins) t) t 0 = _
    exact P.cellAt_opened _ t 0
  refine ⟨hcells, hγ, ⟨fun k hk => ?_, ?_, ?_, ?_, fun k hk => ?_, hρ⟩⟩
  · have := Finset.prod_ne_zero_iff.mp h1 k (Finset.mem_range.mpr hk)
    simpa only [Polynomial.eval_add, eval_one, digitPoly_eval] using this
  · simpa only [Polynomial.eval_add, Polynomial.eval_mul, eval_one, digitPoly_eval, eval_X] using h2
  · rw [hv0]
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, digitPoly_eval, eval_X, _root_.Kc3.Params.dPoly,
      _root_.Kc3.Params.dNextPoly, eval_C] using h3
  · rw [← hM.vRows t]; exact h4
  · have := Finset.prod_ne_zero_iff.mp h5 k (Finset.mem_range.mpr hk)
    simpa only [Polynomial.eval_add, eval_X, eval_C] using this

omit hM in
/-- **The degenerate pairs**: at most `(2 n + 2) q`, `n` the cells. -/
theorem card_ABad_le [DecidablePred fun p : E × E => ABad P w coins p.1 p.2] [DecidableEq (E × E)]
    (hZ : P.vCells = digitPoly 24) (hs : sCoef P ≠ 0) :
    (univ.filter fun p : E × E => ABad P w coins p.1 p.2).card ≤ (2 * P.nCells + 2) * Fintype.card E := by
  set q := Fintype.card E
  classical
  let γz : E → E := fun β => if h : ∃ α, (Epoly P α β (cW w coins) /ₘ P.vCells).eval 0 = 0 then h.choose else 0
  have hsub : (univ.filter fun p : E × E => ABad P w coins p.1 p.2) ⊆
      ((univ : Finset E).image fun a => (a, (0 : E))) ∪
      ((univ : Finset (P.T × Fin 4)).biUnion fun i =>
        ((univ : Finset E).image fun b => (P.cells (gH w coins) i + b * P.pt i, b)) ∪
        ((univ : Finset E).image fun b => (P.cells (gH w coins) i + b * P.pt (P.σ i), b))) ∪
      ((univ : Finset E).image fun b => (γz b, b)) := by
    intro x hx
    have hx' : ABad P w coins x.1 x.2 := by
      rw [Finset.mem_filter] at hx
      exact hx.2
    unfold ABad at hx'
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion]
    rcases hx' with h | h | h
    · exact Or.inl (Or.inl ⟨x.1, by rw [← h]⟩)
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      refine Or.inl (Or.inr ⟨i, ?_⟩)
      by_cases h0 : x.1 + P.cells (gH w coins) i + x.2 * P.pt i = 0
      · exact Or.inl ⟨x.2, Prod.ext (by linear_combination (norm := char2_norm) h0) rfl⟩
      · exact Or.inr ⟨x.2, Prod.ext (by linear_combination (norm := char2_norm) hi h0) rfl⟩
    · by_cases hβ : x.2 = 0
      · exact Or.inl (Or.inl ⟨x.1, by rw [← hβ]⟩)
      · refine Or.inr ⟨x.2, Prod.ext ?_ rfl⟩
        have hex : ∃ α, (Epoly P α x.2 (cW w coins) /ₘ P.vCells).eval 0 = 0 := ⟨x.1, h⟩
        simp only [γz, dif_pos hex]
        exact gamma_root_unique P (cW w coins) hZ hs hβ hex.choose_spec h
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  refine (add_le_add ((card_union_le _ _).trans (add_le_add card_image_le
    (card_biUnion_le.trans (Finset.sum_le_sum fun i _ => (card_union_le _ _).trans
      (add_le_add card_image_le card_image_le))))) card_image_le).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Finset.card_univ, smul_eq_mul]
  show q + Fintype.card (P.T × Fin 4) * (q + q) + q = (2 * P.nCells + 2) * q
  ring

omit hM in
/-- **The degenerate pairs**: at most `(2 n + 2) q`, `n` the cells. -/
theorem card_ABad_le' (hZ : P.vCells = digitPoly 24) (hs : sCoef P ≠ 0) (T : Finset (E × E))
    (hT : ∀ p ∈ T, ABad P w coins p.1 p.2) : T.card ≤ (2 * P.nCells + 2) * Nat.card E := by
  rw [Nat.card_eq_fintype_card]
  set q := Fintype.card E
  classical
  let γz : E → E := fun β => if h : ∃ α, (Epoly P α β (cW w coins) /ₘ P.vCells).eval 0 = 0 then h.choose else 0
  have hsub : T ⊆
      ((univ : Finset E).image fun a => (a, (0 : E))) ∪
      ((univ : Finset (P.T × Fin 4)).biUnion fun i =>
        ((univ : Finset E).image fun b => (P.cells (gH w coins) i + b * P.pt i, b)) ∪
        ((univ : Finset E).image fun b => (P.cells (gH w coins) i + b * P.pt (P.σ i), b))) ∪
      ((univ : Finset E).image fun b => (γz b, b)) := by
    intro x hx
    have hx' : ABad P w coins x.1 x.2 := hT x hx
    unfold ABad at hx'
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion]
    rcases hx' with h | h | h
    · exact Or.inl (Or.inl ⟨x.1, by rw [← h]⟩)
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      refine Or.inl (Or.inr ⟨i, ?_⟩)
      by_cases h0 : x.1 + P.cells (gH w coins) i + x.2 * P.pt i = 0
      · exact Or.inl ⟨x.2, Prod.ext (by linear_combination (norm := char2_norm) h0) rfl⟩
      · exact Or.inr ⟨x.2, Prod.ext (by linear_combination (norm := char2_norm) hi h0) rfl⟩
    · by_cases hβ : x.2 = 0
      · exact Or.inl (Or.inl ⟨x.1, by rw [← hβ]⟩)
      · refine Or.inr ⟨x.2, Prod.ext ?_ rfl⟩
        have hex : ∃ α, (Epoly P α x.2 (cW w coins) /ₘ P.vCells).eval 0 = 0 := ⟨x.1, h⟩
        simp only [γz, dif_pos hex]
        exact gamma_root_unique P (cW w coins) hZ hs hβ hex.choose_spec h
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  refine (add_le_add ((card_union_le _ _).trans (add_le_add card_image_le
    (card_biUnion_le.trans (Finset.sum_le_sum fun i _ => (card_union_le _ _).trans
      (add_le_add card_image_le card_image_le))))) card_image_le).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Finset.card_univ, smul_eq_mul]
  show q + Fintype.card (P.T × Fin 4) * (q + q) + q = (2 * P.nCells + 2) * q
  ring

end Good

theorem conic_card_le' (t : E) (T : Finset E) (hT : ∀ ρ ∈ T, RBad t ρ) : T.card ≤ 1 :=
  conic_card_gen' (t + QuotientSecurity.sq t * ofK (betaAt 1)) (ofK (betaAt 1)) T hT

/-! ## The deployed circuit -/

/-- **The evaluated check on the circuit's wiring table** (`crates/membership/quotient`'s wiring is fixed by the
circuit): its entry `2^24 − 1` (the top coefficient, the sum of the cells' σ-points) is zero, and its entry
`2^24 − 2` (the coefficient `s` of `α β` in `γ`) is not. -/
def WiringCheck : Prop :=
  (membership logRows).wiringTable.getD (2 ^ 24 - 1) 0 = 0 ∧ (membership logRows).wiringTable.getD (2 ^ 24 - 2) 0 ≠ 0

theorem sigmaPoly_P0 : P0.sigmaPoly = Novel.nov 0 24 fun j => ofK ((membership logRows).wiringTable.getD j 0) := by
  rw [sigmaPoly_P0_table]
  exact tablePoly_idx 24 (fun j => ofK ((membership logRows).wiringTable.getD j 0))

theorem sCoef_P0 (hW : WiringCheck) : sCoef P0 ≠ 0 := by
  rw [sCoef_eq P0 vCells_eq _ sigmaPoly_P0 hW.1]
  intro h
  exact hW.2 (ofK_injective (h.trans Compose.Reduce.ofK_zero.symm))

/-- **The degenerate challenges**: at most `(7 · 2^24 + 3) q³`. -/
theorem card_badSet_le (hW : WiringCheck) (w : Secret) (coins : Coins) :
    (badSet w coins).card ≤ (7 * 2 ^ 24 + 3) * Nat.card E ^ 3 := by
  refine (card_quad_le' (ABad P0 w coins) (tPoly P0 (gH w coins)) RBad (2 ^ 25 + 2) (5 * 2 ^ 24) _ ?_ ?_ ?_
    fun t T hT => conic_card_le' t T hT).trans (by norm_num)
  · intro x hx
    have hx2 : ¬ GoodAt w coins P0 x.1 x.2.1 x.2.2.1 x.2.2.2 := mem_badSet.mp hx
    rcases em (ABad P0 w coins x.1 x.2.1) with h1 | h1
    · exact Or.inl h1
    rcases em ((tPoly P0 (gH w coins) x.1 x.2.1).eval x.2.2.1 = 0) with h2 | h2
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    rcases em (RBad x.2.2.1 x.2.2.2) with h3 | h3
    · exact Or.inr (Or.inr h3)
    exact absurd (goodAt_of P0 P0_matches w coins _ _ _ _ h1 h2 h3) hx2
  · intro T hT
    have := card_ABad_le' P0 w coins vCells_eq (sCoef_P0 hW) T hT
    rw [nCells_P0] at this
    exact this.trans (by norm_num)
  · intro a b hab
    have hc : ∀ i : P0.T × Fin 4, a + P0.cells (gH w coins) i + b * P0.pt i ≠ 0 ∧
        a + P0.cells (gH w coins) i + b * P0.pt (P0.σ i) ≠ 0 := by
      by_contra hn
      exact hab (Or.inr (Or.inl hn))
    obtain ⟨gm, hgm⟩ : ∃ gm : P0.Msg₁, gm.1 = gH w coins :=
      ⟨⟨gH w coins, fun j => by rw [card_T_P0]; exact PcsBridge.Kc3.natDegree_witnessOfTable_lt _ j⟩, rfl⟩
    exact ⟨tPoly_ne_zero P0 (gH w coins) vCells_eq a b (P0.pins 0, 0) (hc _),
      tPoly_natDegree_le P0 (gH w coins) card_T_P0 gm hgm a b⟩

/-- **The fraction of degenerate challenges** over `E`: at most `(7 · 2^24 + 3) / 2^192`. -/
theorem badSet_density (hW : WiringCheck) (w : Secret) (coins : Coins) :
    ((badSet w coins).card : ℝ≥0∞) / 2 ^ 768 ≤ (7 * 2 ^ 24 + 3 : ℝ≥0∞) / 2 ^ 192 := by
  have h := card_badSet_le hW w coins
  have hq : Nat.card E = 2 ^ 192 := BF64.nat_card_ext3
  rw [hq] at h
  have h' : ((badSet w coins).card : ℝ≥0∞) ≤ (7 * 2 ^ 24 + 3) * (2 ^ 192) ^ 3 := by exact_mod_cast h
  calc _ ≤ (7 * 2 ^ 24 + 3) * (2 ^ 192) ^ 3 / 2 ^ 768 := ENNReal.div_le_div_right h' _
    _ = (7 * 2 ^ 24 + 3 : ℝ≥0∞) / 2 ^ 192 := by
        rw [show (2 : ℝ≥0∞) ^ 768 = 2 ^ 192 * (2 ^ 192) ^ 3 by rw [← pow_mul, ← pow_add],
          ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

/-- The number, below `2^-165`. -/
theorem bad_bound_lt : (7 * 2 ^ 24 + 3 : ℝ≥0∞) / 2 ^ 192 < 2⁻¹ ^ 165 := by
  have h1 : (7 * 2 ^ 24 + 3 : ℝ≥0∞) / 2 ^ 192 < 2 ^ 27 / 2 ^ 192 :=
    ENNReal.div_lt_div_right (by simp) (by simp) (by norm_num)
  have h2 : (2 ^ 27 : ℝ≥0∞) / 2 ^ 192 = 2⁻¹ ^ 165 := by
    have e : (2 : ℝ≥0∞) ^ 27 / 2 ^ 192 = (2 ^ 27 * 1) / (2 ^ 27 * 2 ^ 165) := by norm_num
    rw [e, ENNReal.mul_div_mul_left _ _ (by simp) (by simp), one_div, ENNReal.inv_pow]
  exact h2 ▸ h1

end E2ECompleteness.Pcs.H
