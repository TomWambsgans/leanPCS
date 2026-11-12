-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/QuotientSecurity/Cells.lean` (itself from leanVM, branch PCS-openings-aggregation, commit
-- 651453c6) to `Kc3.Params`.
import Kc3.Protocol

/-!
# The polynomials on the cells

`Kc3`'s polynomials read on the cells: a row is the same at its four cells (`rowPoly_eval_shift`), so the cells'
polynomial at a cell is that cell's value (`cellPoly_zero_eval_pt`); the denominators there; the two cofactors
`Z / Z_R` and `Z / Z_P` vanish on every cell but a row's first, resp. a pinned one; the pins' interpolant takes the
statement at the pins; and so `Z g` at a cell (`errAt`) is a nonzero multiple of the gate's error at a row's first
cell, of the pin's error at a pinned cell, and zero elsewhere.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Kc3

open QuotientSecurity QuotientSecurity.Params

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] (P : Params F)

namespace Params

theorem theta_pow_four : P.θ ^ 4 = P.θ := by
  have h := P.hθ
  have h2 : P.θ * P.θ = P.θ + 1 := by
    have : P.θ * P.θ + (P.θ + 1) = 0 := by rw [← h]; ring
    exact CharTwo.add_eq_zero.mp this
  have h4 : P.θ ^ 4 = (P.θ * P.θ) * (P.θ * P.θ) := by ring
  rw [h4, h2]
  have : (P.θ + 1) * (P.θ + 1) = P.θ * P.θ + 1 + (P.θ + P.θ) := by ring
  rw [this, CharTwo.add_self_eq_zero, add_zero, h2, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem shift_pow_four (c : Fin 4) : shift P.θ c ^ 4 = shift P.θ c := by
  fin_cases c
  · simp [shift]
  · simp [shift]
  · simpa [shift] using P.theta_pow_four
  · simp only [shift]
    show (P.θ + 1) ^ 4 = P.θ + 1
    have : (P.θ + 1) ^ 4 = P.θ ^ 4 + 1 := by
      have h := add_pow_char_pow (R := F) (p := 2) (n := 2) P.θ 1
      simpa using h
    rw [this, P.theta_pow_four]

/-- A row is the same at its four cells. -/
theorem rowPoly_eval_shift (x : F) (c : Fin 4) :
    (rowPoly : F[X]).eval (x + shift P.θ c) = (rowPoly : F[X]).eval x := by
  have h := add_pow_char_pow (R := F) (p := 2) (n := 2) x (shift P.θ c)
  simp only [rowPoly, eval_add, eval_pow, eval_X]
  have h' : (x + shift P.θ c) ^ 4 = x ^ 4 + shift P.θ c ^ 4 := by simpa using h
  rw [h', P.shift_pow_four]
  have : shift P.θ c + shift P.θ c = 0 := CharTwo.add_self_eq_zero _
  linear_combination this

/-- The polynomial of the `X` role, at any cell, is that cell's value. -/
theorem cellPoly_zero_eval_pt (g : Witness F) (i : P.T × Fin 4) :
    (P.cellPoly g 0).eval (P.pt i) = P.cells g i := by
  simp only [cellPoly, cells, pt, eval_finsetSum, eval_mul, eval_comp, eval_add, eval_X, eval_C]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [P.rowPoly_eval_shift]
  simp [shift]

theorem pt_row (x : P.T) : P.pt (x, 0) = x := by simp [pt, shift]

theorem dPoly_eval_pt (g : Witness F) (α β : F) (i : P.T × Fin 4) :
    (P.dPoly g α β).eval (P.pt i) = α + P.cells g i + β * P.pt i := by
  simp [dPoly, cellPoly_zero_eval_pt]

theorem dNextPoly_eval_pt (g : Witness F) (α β : F) (i : P.T × Fin 4) :
    (P.dNextPoly g α β).eval (P.pt i) = α + P.cells g i + β * P.pt (P.σ i) := by
  simp only [dNextPoly, eval_add, eval_mul, eval_C, cellPoly_zero_eval_pt]
  rw [show P.sigmaPoly.eval (P.pt i) = P.pt (P.σ i) from P.hσ i]

theorem nCells_eq : P.nCells = 4 * P.T.card := by
  simp [nCells, Fintype.card_prod, mul_comm]

theorem vCells_eval_pt (i : P.T × Fin 4) : P.vCells.eval (P.pt i) = 0 := by
  rw [vCells, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem vCells_monic : P.vCells.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _

theorem natDegree_vCells : P.vCells.natDegree = P.nCells := by
  rw [vCells, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
  simp [nCells]

theorem vCells_ne_zero : P.vCells ≠ 0 := P.vCells_monic.ne_zero

/-- `Z / Z_R` at a row's first cell is not zero. -/
theorem cofRows_eval_row (i : P.T × Fin 4) (hi : i.2 = 0) : P.cofRows.eval (P.pt i) ≠ 0 := by
  rw [cofRows, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [Finset.mem_filter] at hj
  simp only [eval_sub, eval_X, eval_C]
  intro h
  have := P.pt_injective (sub_eq_zero.mp h)
  rw [this] at hi
  exact hj.2 hi

/-- `Z / Z_R` vanishes on every other cell. -/
theorem cofRows_eval_other (i : P.T × Fin 4) (hi : i.2 ≠ 0) : P.cofRows.eval (P.pt i) = 0 := by
  rw [cofRows, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) (by simp)

/-- `Z / Z_P` at a pinned cell is not zero. -/
theorem cofPins_eval_pin (k : Fin pinCount) : P.cofPins.eval (P.pt (P.pinCell k)) ≠ 0 := by
  rw [cofPins, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [Finset.mem_filter] at hj
  simp only [eval_sub, eval_X, eval_C]
  intro h
  have := P.pt_injective (sub_eq_zero.mp h)
  exact hj.2 k this.symm

/-- `Z / Z_P` vanishes on every other cell. -/
theorem cofPins_eval_other (i : P.T × Fin 4) (hi : ∀ k, i ≠ P.pinCell k) : P.cofPins.eval (P.pt i) = 0 := by
  rw [cofPins, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) (by simp)

theorem pinCell_role (k : Fin pinCount) : (P.pinCell k).2 = 2 := rfl

theorem pinPt_injective : Function.Injective P.pinPt := by
  intro k l h
  have := P.pt_injective h
  exact P.pins.injective (congrArg Prod.fst this)

/-- The pins' interpolant takes the statement at the pins. -/
theorem pinPoly_eval_pin (stmt : Stmt F) (k : Fin pinCount) : (P.pinPoly stmt).eval (P.pinPt k) = stmt k :=
  Lagrange.eval_interpolate_at_node _ P.pinPt_injective.injOn (Finset.mem_univ k)

/-- **`Z g` at a cell**, the error the identity reads there. -/
noncomputable def errAt (stmt : Stmt F) (g : Witness F) (i : P.T × Fin 4) : F :=
  (P.zgPoly stmt g).eval (P.pt i)

/-- At a row's first cell, the error is `Z / Z_R` (nonzero) times the gate's. -/
theorem errAt_row (stmt : Stmt F) (g : Witness F) (x : P.T) :
    P.errAt stmt g (x, 0) = P.cofRows.eval (P.pt (x, 0)) *
      gate (P.cells g (x, 0)) (P.cells g (x, 1)) (P.cells g (x, 2)) (P.cells g (x, 3)) := by
  have hpin : ∀ k, (x, (0 : Fin 4)) ≠ P.pinCell k := fun k h => by
    have := congrArg Prod.snd h
    simp [pinCell] at this
  simp only [errAt, zgPoly, eval_add, eval_mul, P.cofPins_eval_other _ hpin, zero_mul, add_zero]
  congr 1
  rw [P.pt_row x, gatePoly, gate_eval]
  rfl

/-- At a pinned cell, the error is `Z / Z_P` (nonzero) times the pin's. -/
theorem errAt_pin (stmt : Stmt F) (g : Witness F) (k : Fin pinCount) :
    P.errAt stmt g (P.pinCell k) = P.cofPins.eval (P.pt (P.pinCell k)) * (P.cells g (P.pinCell k) + stmt k) := by
  have h2 : (P.pinCell k).2 ≠ 0 := by simp [pinCell]
  have hp : (P.pinPoly stmt).eval (P.pt (P.pinCell k)) = stmt k := P.pinPoly_eval_pin stmt k
  simp only [errAt, zgPoly, eval_add, eval_mul, P.cofRows_eval_other _ h2, zero_mul, zero_add,
    cellPoly_zero_eval_pt, hp]

/-- Elsewhere, no error. -/
theorem errAt_other (stmt : Stmt F) (g : Witness F) (i : P.T × Fin 4) (h0 : i.2 ≠ 0)
    (hp : ∀ k, i ≠ P.pinCell k) : P.errAt stmt g i = 0 := by
  simp only [errAt, zgPoly, eval_add, eval_mul, P.cofRows_eval_other _ h0, P.cofPins_eval_other _ hp, zero_mul,
    add_zero]

/-- An error sits on an error cell. -/
theorem errorCell_of_errAt (stmt : Stmt F) (g : Witness F) (i : P.T × Fin 4) (h : P.errAt stmt g i ≠ 0) :
    P.ErrorCell i := by
  by_contra hn
  simp only [ErrorCell, not_or, not_exists] at hn
  exact h (P.errAt_other stmt g i hn.1 fun k hk => hn.2.1 k hk)

/-- No error anywhere: every gate and every pin holds. -/
theorem gates_pins_of_errAt (stmt : Stmt F) (g : Witness F) (h : ∀ i, P.errAt stmt g i = 0) :
    (∀ x : P.T, gate (P.cells g (x, 0)) (P.cells g (x, 1)) (P.cells g (x, 2)) (P.cells g (x, 3)) = 0) ∧
      ∀ k, P.cells g (P.pinCell k) = stmt k := by
  refine ⟨fun x => ?_, fun k => ?_⟩
  · have := h (x, 0)
    rw [errAt_row] at this
    exact (mul_eq_zero.mp this).resolve_left (P.cofRows_eval_row (x, 0) rfl)
  · have := h (P.pinCell k)
    rw [errAt_pin] at this
    exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (P.cofPins_eval_pin k))

end Params

end Kc3
