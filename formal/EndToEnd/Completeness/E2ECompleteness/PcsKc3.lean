-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the honest second message of the deployed reduction (`formal/Kc3`), for completeness.
import Kc3.RoundThree

/-!
# The honest second message is consistent, and accepted

For any parameters `P` of the reduction (`formal/Kc3`), cells satisfying the relation (`Sat`), and challenges at
which no cell's denominator vanishes:

* `errAt_eq_zero_of_sat`: no error at any cell, so `Z g` vanishes on the cells;
* `vCells_dvd_numer`: `Z` divides `N = d d' (h + Z ε) + d + d' + μ Z g` for the copy argument's sum `h` (the
  logarithmic derivatives on the cells) and any blinding `ε`; the quotient is `q` (`Z q = N`);
* **`consistent_honest`**: when `q`'s high part `q /ₘ Z` vanishes at `0` (what the prover's `b₂` ensures), the
  second message `(q %ₘ Z, (q /ₘ Z) /ₘ X, X h, ε)` is consistent: `q = A₀ + Z X A₁`, `x h = B₀ + Z X B₁`, and the
  identity is `X (Z q + N) = 0`;
* **`accepts_of_consistent`**: a consistent second message, with the row's true values and `next`, is accepted at
  every `t`, `ρ` where the verifier's denominators do not vanish.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Kc3.Honest

open Kc3.Params QuotientSecurity
open QuotientSecurity.Params (Witness)

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] (P : Kc3.Params F)

/-- **No error at any cell** when the cells satisfy the relation. -/
theorem errAt_eq_zero_of_sat (stmt : Stmt F) (g : Witness F) (hs : P.Sat stmt (P.cells g))
    (i : P.T × Fin 4) : P.errAt stmt g i = 0 := by
  obtain ⟨x, c⟩ := i
  by_cases h0 : c = 0
  · subst h0
    rw [errAt_row, hs.1 x, mul_zero]
  · by_cases hp : ∃ k, (x, c) = P.pinCell k
    · obtain ⟨k, hk⟩ := hp
      rw [hk, errAt_pin, hs.2.2 k, CharTwo.add_self_eq_zero, mul_zero]
    · push_neg at hp
      exact P.errAt_other stmt g (x, c) h0 hp

/-- **The numerator** `N = d d' (h + Z ε) + d + d' + μ Z g`. -/
noncomputable def numer (stmt : Stmt F) (g : Witness F) (α β μ : F) (h ε : F[X]) : F[X] :=
  P.dPoly g α β * P.dNextPoly g α β * (h + P.vCells * ε) + P.dPoly g α β + P.dNextPoly g α β +
    C μ * P.zgPoly stmt g

/-- On a cell, the numerator vanishes when `h` is the logarithmic derivatives there. -/
theorem numer_eval_pt (stmt : Stmt F) (g : Witness F) (hs : P.Sat stmt (P.cells g)) (α β μ : F) (h ε : F[X])
    (i : P.T × Fin 4) (hd : α + P.cells g i + β * P.pt i ≠ 0) (hd' : α + P.cells g i + β * P.pt (P.σ i) ≠ 0)
    (hh : h.eval (P.pt i) = (α + P.cells g i + β * P.pt i)⁻¹ + (α + P.cells g i + β * P.pt (P.σ i))⁻¹) :
    (numer P stmt g α β μ h ε).eval (P.pt i) = 0 := by
  have he : (P.zgPoly stmt g).eval (P.pt i) = 0 := errAt_eq_zero_of_sat P stmt g hs i
  simp only [numer, eval_add, eval_mul, eval_C, P.vCells_eval_pt, zero_mul, add_zero, dPoly_eval_pt,
    dNextPoly_eval_pt, he, mul_zero, hh]
  field_simp
  linear_combination (norm := char2_norm) (0 : F)

/-- **`Z` divides the numerator**: it vanishes on every cell, and `Z` is the product of the cells' distinct
linear factors. -/
theorem vCells_dvd_numer (stmt : Stmt F) (g : Witness F) (hs : P.Sat stmt (P.cells g)) (α β μ : F) (h ε : F[X])
    (hd : ∀ i, α + P.cells g i + β * P.pt i ≠ 0) (hd' : ∀ i, α + P.cells g i + β * P.pt (P.σ i) ≠ 0)
    (hh : ∀ i, h.eval (P.pt i) = (α + P.cells g i + β * P.pt i)⁻¹ + (α + P.cells g i + β * P.pt (P.σ i))⁻¹) :
    P.vCells ∣ numer P stmt g α β μ h ε := by
  unfold vCells
  refine Finset.prod_dvd_of_coprime ?_ fun i _ => ?_
  · exact fun i _ j _ hij => Polynomial.pairwise_coprime_X_sub_C P.pt_injective hij
  · rw [dvd_iff_isRoot]
    exact numer_eval_pt P stmt g hs α β μ h ε i (hd i) (hd' i) (hh i)

/-- The honest second message from `q`, `h` and `ε`. -/
noncomputable def honestMsg (q h ε : F[X]) : TMsg F :=
  ⟨q %ₘ P.vCells, (q /ₘ P.vCells) /ₘ X, X * h, ε⟩

theorem qPoly_honestMsg (q h ε : F[X]) (hq0 : (q /ₘ P.vCells).eval 0 = 0) :
    P.qPoly (honestMsg P q h ε) = q := by
  have hX : X * ((q /ₘ P.vCells) /ₘ X) = q /ₘ P.vCells := by
    have := (mul_divByMonic_eq_iff_isRoot (p := q /ₘ P.vCells) (a := 0)).mpr hq0
    simpa using this
  simp only [qPoly, honestMsg, zeta]
  rw [mul_assoc, hX]
  exact modByMonic_add_div q P.vCells

/-- **The honest second message is consistent.** -/
theorem consistent_honest (stmt : Stmt F) (g : Witness F) (α β μ : F) (q h ε : F[X])
    (hq : P.vCells * q = numer P stmt g α β μ h ε) (hq0 : (q /ₘ P.vCells).eval 0 = 0) :
    P.Consistent stmt g (honestMsg P q h ε) α β μ := by
  unfold Consistent identity
  rw [qPoly_honestMsg P q h ε hq0]
  have hN : P.vCells * q + numer P stmt g α β μ h ε = 0 := by
    rw [hq]; exact CharTwo.add_self_eq_zero _
  simp only [xhPoly, honestMsg, zeta, rhsPoly]
  unfold numer at hN
  linear_combination (norm := ring_nf) X * hN

set_option maxRecDepth 100000 in
/-- **A consistent second message is accepted** with the row's true values and the true `next`, at every `t`, `ρ`
where the verifier's denominators do not vanish. -/
theorem accepts_of_consistent (stmt : Stmt F) (g : Witness F) (R : TMsg F) (α β μ t ρ : F)
    (h : P.Consistent stmt g R α β μ)
    (hD : conicDen P.θ t ρ ≠ 0)
    (hC : P.vCells.eval t * t + (α + (P.cellPoly g 0).eval t + β * t) *
      (α + (P.cellPoly g 0).eval t + β * P.sigmaPoly.eval t) ≠ 0)
    (hR : P.vRows.eval t ≠ 0) (hPn : P.vPins.eval t ≠ 0) :
    P.Accepts stmt g R α β μ t (P.rowValues (opened g t) t) (P.sigmaPoly.eval t) ρ := by
  have hI : (P.identity stmt g R α β μ).eval t = 0 := by rw [h]; exact eval_zero
  have hv : ∀ c, P.cellAt (opened g t) t c = (P.cellPoly g c).eval t := P.cellAt_opened g t
  refine ⟨?_, rfl, hD, ?_, hR, hPn, ?_⟩
  · -- The witness claim: the conic's identity.
    have := conic_identity P.θ t ρ (opened g t) hD
    rw [P.rowValues_eq]
    exact this
  · simpa [rowValues, hv] using hC
  · simp only [rowValues, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, hv]
    set X0 := (P.cellPoly g 0).eval t
    set d := α + X0 + β * t
    set d' := α + X0 + β * P.sigmaPoly.eval t
    set z := P.vCells.eval t
    set D := z * t + d * d'
    set qv := (P.qPoly R).eval t
    set Pv := (P.xhPoly R).eval t
    have hzg : z * (gate X0 0 ((P.cellPoly g 2).eval t) ((P.cellPoly g 3).eval t + (P.cellPoly g 1).eval t) /
        P.vRows.eval t + (X0 + (P.pinPoly stmt).eval t) / P.vPins.eval t) = (P.zgPoly stmt g).eval t := by
      have e1 : z = P.vRows.eval t * P.cofRows.eval t := by rw [← eval_mul, P.vRows_mul_cofRows]
      have e2 : z = P.vPins.eval t * P.cofPins.eval t := by rw [← eval_mul, P.vPins_mul_cofPins]
      simp only [zgPoly, gatePoly, eval_add, eval_mul, gate_eval]
      rw [mul_add]
      congr 1
      · rw [e1, mul_div_assoc', mul_comm (P.vRows.eval t), mul_assoc, mul_div_assoc, mul_div_cancel_left₀ _ hR]
        simp only [gate]
        ring
      · rw [e2, mul_comm (P.vPins.eval t), mul_assoc, mul_div_cancel₀ _ hPn]
    rw [mul_assoc μ z, hzg]
    have e3 : (P.dPoly g α β).eval t = α + (P.cellPoly g 0).eval t + β * t := by simp [dPoly]
    have e4 : (P.dNextPoly g α β).eval t = α + (P.cellPoly g 0).eval t + β * P.sigmaPoly.eval t := by
      simp [dNextPoly]
    have hcl : z * t * qv + d * d' * Pv = t * (d + d' + μ * (P.zgPoly stmt g).eval t) := by
      unfold identity at hI
      simp only [rhsPoly, eval_add, eval_mul, eval_X, eval_C, e3, e4] at hI
      simp only [d, d', z, qv, Pv, X0]
      linear_combination (norm := char2_norm) hI
    rw [eq_div_iff hC, ← hcl]
    have hκ : d * d' / D * D = d * d' := div_mul_cancel₀ _ hC
    rw [show ((1 + d * d' / D) * qv + d * d' / D * Pv) * D =
      qv * D + qv * (d * d' / D * D) + Pv * (d * d' / D * D) by ring, hκ]
    simp only [D]
    linear_combination (norm := char2_norm) (0 : F)

end Kc3.Honest
