-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The first challenge of `docs/membership/PROTOCOL.md` ("Soundness"), in the style of
-- `formal/QuotientSecurity/RoundOne.lean` (adapted from leanVM, branch PCS-openings-aggregation, commit 651453c6).
import Kc3.Cells
import Kc3.Pole

/-!
# The first challenge

If the cells of the first message do not satisfy the relation, few triples `(α, β, μ)` admit a consistent
second message: at most `E1 q² = 8 n q²` (`card_round1_le`).

**The sum, by the layout** (`consistent_sum`). Where the identity `X Z q + d d' P + X R` vanishes, at `x = 0` it
reads `d d'(0) P(0) = 0`; outside the `2 q²` triples where `d d'(0)` vanishes, `P(0) = 0`, so `B₀(0) = 0` and
`h = P / X = B₀ / X + Z B₁` is a polynomial whose part `B₀ / X` has degree at most `n − 2`: it sums to zero over the
cells (`Params.hSum`), and `Z B₁` vanishes there. Dividing by `X`, `Z q + d d' h = R`, so on a cell where no
denominator vanishes `h = 1/d + 1/d' + μ e / (d d')`, `e` the error `Z g` there (`Cells.lean`'s `errAt`). Hence
`L(α, β) + μ B(α, β) = 0`, `L` the copy argument's sum of logarithmic derivatives.

**The count.** Outside the `2 n q²` triples where a cell's denominator vanishes and the `2 q²` above:
* if some error is not zero, it sits on an error cell, and the pole condition gives one whose predecessor on its
  cycle has none (or a lone one): the pole lemma, `(4 n + 1) q²` (`Pole.lean`);
* otherwise every gate and pin holds, so a copy fails: the copy argument, `(4 n − 2) q²`
  (`QuotientSecurity.card_copy_triple_le`, target zero).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Kc3

open QuotientSecurity QuotientSecurity.Params

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] (P : Params F)

namespace Params

/-- The anchors are rows: there are rows. -/
theorem card_T_pos : 0 < P.T.card := Finset.card_pos.mpr ⟨(P.pins 0).1, (P.pins 0).2⟩

/-- **The sum, by the layout.** A consistent second message whose `B₀` is below `n`, at a triple where `d d'(0)`
and no cell's denominator vanishes: the copy argument's sum plus `μ` times the errors' sum is zero. -/
theorem consistent_sum (stmt : Stmt F) (g : Witness F) (R : TMsg F) (hB : R.B₀.natDegree < P.nCells)
    (α β μ : F) (h : P.Consistent stmt g R α β μ)
    (h0 : (P.dPoly g α β).eval 0 * (P.dNextPoly g α β).eval 0 ≠ 0)
    (hd : ∀ i, α + P.cells g i + β * P.pt i ≠ 0) (hd' : ∀ i, α + P.cells g i + β * P.pt (P.σ i) ≠ 0) :
    logSum P.pt P.σ (P.cells g) α β +
      μ * ∑ i, P.errAt stmt g i * ((α + P.cells g i + β * P.pt i) * (α + P.cells g i + β * P.pt (P.σ i)))⁻¹
        = 0 := by
  unfold Consistent identity at h
  -- At `x = 0`: `d d'(0) P(0) = 0`, so `B₀(0) = 0`.
  have e0 := congrArg (fun p : F[X] => p.eval 0) h
  simp only [eval_add, eval_mul, eval_X, zero_mul, zero_add, add_zero, eval_zero] at e0
  have hP0 : (P.xhPoly R).eval 0 = 0 := (mul_eq_zero.mp e0).resolve_left h0
  have hB0 : R.B₀.eval 0 = 0 := by
    simp only [xhPoly, zeta, eval_add, eval_mul, eval_X, mul_zero, zero_mul, add_zero] at hP0
    exact hP0
  obtain ⟨b, hb⟩ : X ∣ R.B₀ := X_dvd_iff.mpr (by rw [coeff_zero_eq_eval_zero]; exact hB0)
  -- Dividing by `X`: `Z q + d d' h + R = 0`, `h = b + Z B₁`.
  set inner := P.vCells * P.qPoly R + P.dPoly g α β * P.dNextPoly g α β * (b + P.vCells * R.B₁) +
    P.rhsPoly stmt g α β μ with hinner
  have hI : X * inner = 0 := by
    rw [← h, hinner, xhPoly, zeta, hb]
    ring
  have hin : inner = 0 := (mul_eq_zero.mp hI).resolve_left X_ne_zero
  -- On a cell: `h = 1/d + 1/d' + μ e / (d d')`.
  have hpt : ∀ i, b.eval (P.pt i) = (α + P.cells g i + β * P.pt i)⁻¹ +
      (α + P.cells g i + β * P.pt (P.σ i))⁻¹ + μ * (P.errAt stmt g i *
        ((α + P.cells g i + β * P.pt i) * (α + P.cells g i + β * P.pt (P.σ i)))⁻¹) := by
    intro i
    have e := congrArg (fun p : F[X] => p.eval (P.pt i)) hin
    simp only [hinner, rhsPoly, eval_add, eval_mul, eval_C, P.vCells_eval_pt, zero_mul, mul_zero, add_zero,
      zero_add, eval_zero, dPoly_eval_pt, dNextPoly_eval_pt] at e
    rw [show (P.zgPoly stmt g).eval (P.pt i) = P.errAt stmt g i from rfl] at e
    have hdi := hd i
    have hdi' := hd' i
    set d := α + P.cells g i + β * P.pt i
    set d' := α + P.cells g i + β * P.pt (P.σ i)
    have e' : d * d' * b.eval (P.pt i) = d + d' + μ * P.errAt stmt g i := CharTwo.add_eq_zero.mp e
    field_simp
    linear_combination e'
  -- `b` has degree at most `n − 2`: it sums to zero over the cells.
  have hdeg : b.natDegree + 2 ≤ 4 * P.T.card := by
    rw [← P.nCells_eq]
    by_cases hb0 : b = 0
    · rw [hb0, natDegree_zero, P.nCells_eq]
      have := P.card_T_pos
      omega
    · have : R.B₀.natDegree = b.natDegree + 1 := by
        rw [hb, natDegree_mul X_ne_zero hb0, natDegree_X]; ring
      omega
  have hsum := P.hSum b hdeg
  rw [show (∑ i : P.T × Fin 4, b.eval (i.1.1 + shift P.θ i.2)) = ∑ i, b.eval (P.pt i) from rfl,
    Finset.sum_congr rfl fun i _ => hpt i, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  exact hsum

variable [Fintype F]

open Classical in
/-- **The first challenge.** If the cells of the first message do not satisfy the relation, at most `E1 q²` of
the `q³` triples `(α, β, μ)` admit a consistent second message. -/
theorem card_round1_le (hpole : P.PoleCondition) (stmt : Stmt F) (g : P.Msg₁)
    (hsat : ¬ P.Sat stmt (P.cells g.1)) :
    (univ.filter fun c : F × F × F => ∃ R : P.Msg₂, P.Consistent stmt g.1 R.1 c.1 c.2.1 c.2.2).card
      ≤ P.E1 * Fintype.card F ^ 2 := by
  have hn : P.E1 = 8 * (4 * P.T.card) := by rw [E1, P.nCells_eq]
  have hcard : Fintype.card (P.T × Fin 4) = 4 * P.T.card := P.nCells_eq
  rw [hn, ← hcard]
  refine card_round1_core P.pt P.pt_injective P.σ (P.cells g.1) (P.errAt stmt g.1) _
    (univ.filter fun p : F × F × F =>
      (P.dPoly g.1 p.1 p.2.1).eval 0 * (P.dNextPoly g.1 p.1 p.2.1).eval 0 = 0) ?_ ?_ ?_ (E := P.ErrorCell) ?_ ?_ ?_
  · -- `d d'(0)` vanishes at `2 q²` triples.
    let f : Bool × F × F → F × F × F := fun r =>
      ((P.cellPoly g.1 0).eval 0 + (if r.1 then 0 else r.2.1 * P.sigmaPoly.eval 0), r.2.1, r.2.2)
    have hsub : (univ.filter fun p : F × F × F =>
        (P.dPoly g.1 p.1 p.2.1).eval 0 * (P.dNextPoly g.1 p.1 p.2.1).eval 0 = 0) ⊆ univ.image f := by
      rintro ⟨α, β, μ⟩ hp
      rw [Finset.mem_filter] at hp
      simp only [dPoly, dNextPoly, eval_add, eval_mul, eval_C, eval_X, mul_zero, add_zero] at hp
      rcases mul_eq_zero.mp hp.2 with h | h
      · refine Finset.mem_image.mpr ⟨(true, β, μ), Finset.mem_univ _, ?_⟩
        simp only [f, if_true, add_zero, Prod.mk.injEq, and_true]
        exact (CharTwo.add_eq_zero.mp h).symm
      · refine Finset.mem_image.mpr ⟨(false, β, μ), Finset.mem_univ _, ?_⟩
        simp only [f, Bool.false_eq_true, if_false, Prod.mk.injEq, and_true]
        have h' : α + ((P.cellPoly g.1 0).eval 0 + β * P.sigmaPoly.eval 0) = 0 := by
          rw [← add_assoc]; exact h
        exact (CharTwo.add_eq_zero.mp h').symm
    refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
    exact le_of_eq (by ring)
  · -- Elsewhere, the sum.
    intro p hp h0 h1
    rw [Finset.mem_filter] at hp
    obtain ⟨-, R, hR⟩ := hp
    rw [Finset.mem_filter, not_and, not_exists] at h0
    have h0' := h0 (Finset.mem_univ _)
    rw [Finset.mem_filter, not_and] at h1
    have hd : ∀ i, p.1 + P.cells g.1 i + p.2.1 * P.pt i ≠ 0 := fun i h => h0' i (Or.inl h)
    have hd' : ∀ i, p.1 + P.cells g.1 i + p.2.1 * P.pt (P.σ i) ≠ 0 := fun i h => h0' i (Or.inr h)
    exact ⟨fun i => ⟨hd i, hd' i⟩,
      P.consistent_sum stmt g.1 R.1 R.2.2.2.1 _ _ _ hR (h1 (Finset.mem_univ _)) hd hd'⟩
  · -- No error: every gate and pin holds, so a copy fails.
    intro he hc
    obtain ⟨hgates, hpins⟩ := P.gates_pins_of_errAt stmt g.1 he
    exact hsat ⟨hgates, hc, hpins⟩
  · -- An error sits on an error cell.
    intro i hi
    exact P.errorCell_of_errAt stmt g.1 i hi
  · exact hpole
  · rw [hcard]; have := P.card_T_pos; omega

end Params

end Kc3
