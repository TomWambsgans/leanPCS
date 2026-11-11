-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The third challenge, in the style of `formal/QuotientSecurity/RoundThree.lean` (adapted from leanVM, branch
-- PCS-openings-aggregation, commit 651453c6).
import Kc3.RoundTwo
import Kc3.Conic

/-!
# The third challenge

If the identity does not hold at `t`, the verifier's claims hold for at most three `ρ` whatever the prover sends
(`card_round3_le`): with the row's true values and the true `next`, the copy claim **is** the identity at `t`
(`consistentAt_of_accepts`), so it fails for every `ρ`; with another `next` the wiring claim fails; with other
values the witness claim, on the row polynomials' conic, passes for at most two `ρ` (`Conic.lean`).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Kc3

open QuotientSecurity QuotientSecurity.Params

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] (P : Params F)

namespace Params

/-- `Z = Z_R · (Z / Z_R)`. -/
theorem vRows_mul_cofRows : P.vRows * P.cofRows = P.vCells := by
  have hmap : (univ.filter fun i : P.T × Fin 4 => i.2 = 0) =
      univ.map ⟨fun x : P.T => (x, (0 : Fin 4)), fun x y h => by simpa using h⟩ := by
    ext ⟨x, c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro h; exact ⟨x, by rw [h]; rfl⟩
    · rintro ⟨y, hy⟩; exact (congrArg Prod.snd hy).symm
  have h1 : P.vRows = ∏ i ∈ univ.filter (fun i : P.T × Fin 4 => i.2 = 0), (X - C (P.pt i)) := by
    rw [hmap, Finset.prod_map, vRows]
    refine Finset.prod_congr rfl fun x _ => ?_
    show X - C (x : F) = X - C (P.pt (x, 0))
    rw [P.pt_row]
  rw [vCells, ← Finset.prod_filter_mul_prod_filter_not univ (fun i : P.T × Fin 4 => i.2 = 0), h1]
  rfl

/-- `Z = Z_P · (Z / Z_P)`. -/
theorem vPins_mul_cofPins : P.vPins * P.cofPins = P.vCells := by
  rw [vCells, ← Finset.prod_filter_mul_prod_filter_not univ (fun i : P.T × Fin 4 => ∃ k, i = P.pinCell k)]
  have hmap : (univ.filter fun i : P.T × Fin 4 => ∃ k, i = P.pinCell k) =
      univ.map ⟨P.pinCell, fun k l h => P.pins.injective (congrArg Prod.fst h)⟩ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩
  rw [hmap, Finset.prod_map, vPins, cofPins]
  congr 1
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists]

/-- The four values an honest prover's row polynomials take at `t`. -/
noncomputable def opened (g : Witness F) (t : F) : Fin 4 → F := fun j => ((g j).comp rowPoly).eval t

theorem cellAt_opened (g : Witness F) (t : F) (c : Fin 4) :
    P.cellAt (opened g t) t c = (P.cellPoly g c).eval t := by
  simp only [cellAt, opened, cellPoly, eval_finsetSum, eval_mul, eval_comp, eval_add, eval_X, eval_C]

/-- The verifier's three values of a row are `rowVals`' linear forms (`θ² + θ + 1 = 0`). -/
theorem rowValues_eq (a : Fin 4 → F) (t : F) : P.rowValues a t = rowVals P.θ t a := by
  have hθ := P.hθ
  funext k
  fin_cases k
  · simp only [rowValues, rowVals, cellAt, Fin.sum_univ_four, digit, shift, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val, eval_one, eval_X, eval_add, eval_mul, eval_pow, Fin.zero_eta, Fin.isValue, add_zero]
    ring
  · simp only [rowValues, rowVals, cellAt, Fin.sum_univ_four, digit, shift, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val, eval_one, eval_X, eval_add, eval_mul, eval_pow, Fin.mk_one, Fin.isValue]
    linear_combination (norm := char2_norm) (a 2 + (t + P.θ) * a 3) * hθ
  · simp only [rowValues, rowVals, cellAt, Fin.sum_univ_four, digit, shift, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val, eval_one, eval_X, eval_add, eval_mul, eval_pow, Fin.reduceFinMk, Fin.isValue]
    linear_combination (norm := char2_norm) (a 2 + (t + P.θ + 1) * a 3) * hθ

set_option maxRecDepth 100000 in
/-- **With the true values, the copy claim is the identity at `t`.** -/
theorem consistentAt_of_accepts (stmt : Stmt F) (g : Witness F) (R : TMsg F) (α β μ t ρ : F)
    (h : P.Accepts stmt g R α β μ t (P.rowValues (opened g t) t) (P.sigmaPoly.eval t) ρ) :
    P.ConsistentAt stmt g R α β μ t := by
  obtain ⟨-, -, -, hD, hR, hPn, hcopy⟩ := h
  have hv : ∀ c, P.cellAt (opened g t) t c = (P.cellPoly g c).eval t := P.cellAt_opened g t
  simp only [rowValues, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, hv] at hcopy hD
  set X0 := (P.cellPoly g 0).eval t
  set d := α + X0 + β * t
  set d' := α + X0 + β * P.sigmaPoly.eval t
  set z := P.vCells.eval t
  set D := z * t + d * d'
  set qv := (P.qPoly R).eval t
  set Pv := (P.xhPoly R).eval t
  -- `Z g` at `t` from the values.
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
  rw [mul_assoc μ z, hzg] at hcopy
  -- Clearing the denominator `ζ + d d'`: `ζ q + d d' P = t R`.
  have hκD : d * d' / D * D = d * d' := div_mul_cancel₀ _ hD
  have hcl : z * t * qv + d * d' * Pv = t * (d + d' + μ * (P.zgPoly stmt g).eval t) := by
    have e := congrArg (· * D) hcopy
    simp only [div_mul_cancel₀ _ hD] at e
    rw [← e]
    calc z * t * qv + d * d' * Pv = qv * (z * t + d * d') + qv * (d * d') + Pv * (d * d') := by
          linear_combination (norm := char2_norm) (0 : F)
      _ = qv * D + qv * (d * d' / D * D) + Pv * (d * d' / D * D) := by rw [hκD]
      _ = ((1 + d * d' / D) * qv + d * d' / D * Pv) * D := by ring
  have e3 : (P.dPoly g α β).eval t = α + (P.cellPoly g 0).eval t + β * t := by simp [dPoly]
  have e4 : (P.dNextPoly g α β).eval t = α + (P.cellPoly g 0).eval t + β * P.sigmaPoly.eval t := by
    simp [dNextPoly]
  unfold ConsistentAt identity
  simp only [rhsPoly, eval_add, eval_mul, eval_X, eval_C, e3, e4]
  simp only [d, d', z, qv, Pv, X0] at hcl
  linear_combination (norm := char2_norm) hcl

variable [Fintype F]

open Classical in
/-- **The third challenge.** If the identity does not hold at `t`, the verifier's claims hold for at most three
`ρ`, whatever values the prover sends. -/
theorem card_round3_le (stmt : Stmt F) (g : P.Msg₁) (R : P.Msg₂) (α β μ t : F)
    (h : ¬ P.ConsistentAt stmt g.1 R.1 α β μ t) (v : Fin 3 → F) (s : F) :
    (univ.filter fun ρ : F => P.Accepts stmt g.1 R.1 α β μ t v s ρ).card ≤ 3 := by
  by_cases hs : P.sigmaPoly.eval t = s
  · by_cases hv : v = P.rowValues (opened g.1 t) t
    · subst hv hs
      have : (univ.filter fun ρ : F => P.Accepts stmt g.1 R.1 α β μ t
          (P.rowValues (opened g.1 t) t) (P.sigmaPoly.eval t) ρ) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun ρ _ hρ => h (P.consistentAt_of_accepts stmt g.1 R.1 α β μ t ρ hρ)
      rw [this]; simp
    · rw [P.rowValues_eq] at hv
      refine (Finset.card_le_card fun ρ hρ => ?_).trans ((card_conic_le P.hθ t (opened g.1 t) v hv).trans
        (by norm_num))
      rw [Finset.mem_filter] at hρ ⊢
      obtain ⟨-, hw, -, hD, -⟩ := hρ
      exact ⟨Finset.mem_univ _, hD, hw⟩
  · have : (univ.filter fun ρ : F => P.Accepts stmt g.1 R.1 α β μ t v s ρ) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun ρ _ hρ => hs hρ.2.1
    rw [this]; simp

end Params

end Kc3
