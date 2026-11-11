-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here, after `formal/Kc3/RoundTwo.lean`'s `natDegree_identity_le`: the degrees of the honest numerator and of
-- `(X² + X) d d'`.
import E2ECompleteness.PcsKc3

/-!
# The degrees of the honest numerator

For F1's parameters with `N` cells and a first message of row polynomials of degree below `N / 4`:
`numer … h ε` (`PcsKc3.lean`) has degree below `3 N` when `deg h < N` and `deg ε ≤ 1` (`natDegree_numer_lt`);
`(X² + X) d d'` has degree at most `2 N` (`natDegree_Epoly_le`).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Kc3.Honest

open Kc3.Params QuotientSecurity

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] (P : Kc3.Params F)

theorem natDegree_d_le (g : P.Msg₁) (α β : F) : (P.dPoly g.1 α β).natDegree ≤ P.nCells - 1 := by
  have hn : 44 ≤ P.nCells := by rw [P.nCells_eq]; have := P.eleven_le_card_T; omega
  have hc0 := P.natDegree_cellPoly_le g 0
  have h1 := natDegree_mul_le_of_le (natDegree_C (R := F) β).le (natDegree_X_le (R := F))
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ hc0) ?_
  · exact (natDegree_C (R := F) α).le.trans (by omega)
  · exact h1.trans (by omega)

theorem natDegree_d'_le (g : P.Msg₁) (α β : F) : (P.dNextPoly g.1 α β).natDegree ≤ P.nCells - 1 := by
  have hn : 44 ≤ P.nCells := by rw [P.nCells_eq]; have := P.eleven_le_card_T; omega
  have hc0 := P.natDegree_cellPoly_le g 0
  have hσ : P.sigmaPoly.natDegree < P.nCells := by rw [P.nCells_eq]; exact P.hσdeg
  have h1 := natDegree_mul_le_of_le (natDegree_C (R := F) β).le (le_refl P.sigmaPoly.natDegree)
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ hc0) ?_
  · exact (natDegree_C (R := F) α).le.trans (by omega)
  · exact h1.trans (by omega)

theorem natDegree_zg_le (stmt : Stmt F) (g : P.Msg₁) : (P.zgPoly stmt g.1).natDegree ≤ 3 * P.nCells - 2 := by
  have hn : 44 ≤ P.nCells := by rw [P.nCells_eq]; have := P.eleven_le_card_T; omega
  have hc0 := P.natDegree_cellPoly_le g 0
  have hc1 := P.natDegree_cellPoly_le g 1
  have hc2 := P.natDegree_cellPoly_le g 2
  have hc3 := P.natDegree_cellPoly_le g 3
  have hcr := P.natDegree_cofRows_le
  have hcp := P.natDegree_cofPins_le
  have hpin := P.natDegree_pinPoly_le stmt
  have hgate : (P.gatePoly g.1).natDegree ≤ 2 * P.nCells - 2 := by
    unfold gatePoly gate
    have h1 := natDegree_mul_le_of_le hc0 hc2
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_) ?_
    · exact hc3.trans (by omega)
    · exact hc1.trans (by omega)
    · exact hc2.trans (by omega)
    · exact h1.trans (by omega)
  unfold zgPoly
  have h1 := natDegree_mul_le_of_le hcr hgate
  have h3 : (P.cellPoly g.1 0 + P.pinPoly stmt).natDegree ≤ P.nCells - 1 := by
    refine natDegree_add_le_of_degree_le hc0 ?_
    exact hpin.trans (by omega)
  have h2 := natDegree_mul_le_of_le hcp h3
  refine natDegree_add_le_of_degree_le ?_ ?_
  · exact h1.trans (by omega)
  · exact h2.trans (by omega)

/-- **The honest numerator has degree below `3 N`.** -/
theorem natDegree_numer_lt (stmt : Stmt F) (g : P.Msg₁) (α β μ : F) (h ε : F[X]) (hh : h.natDegree < P.nCells)
    (hε : ε.natDegree ≤ 1) : (numer P stmt g.1 α β μ h ε).natDegree < 3 * P.nCells := by
  have hn : 44 ≤ P.nCells := by rw [P.nCells_eq]; have := P.eleven_le_card_T; omega
  have hd := natDegree_d_le P g α β
  have hd' := natDegree_d'_le P g α β
  have hzg := natDegree_zg_le P stmt g
  have hZ : P.vCells.natDegree ≤ P.nCells := P.natDegree_vCells.le
  have hhZ : (h + P.vCells * ε).natDegree ≤ P.nCells + 1 := by
    refine natDegree_add_le_of_degree_le (hh.le.trans (by omega)) ?_
    exact natDegree_mul_le_of_le hZ hε
  have t1 := natDegree_mul_le_of_le (natDegree_mul_le_of_le hd hd') hhZ
  have t3 := natDegree_mul_le_of_le (natDegree_C (R := F) μ).le hzg
  unfold numer
  have e1 : (P.dPoly g.1 α β * P.dNextPoly g.1 α β * (h + P.vCells * ε)).natDegree ≤ 3 * P.nCells - 1 :=
    t1.trans (by omega)
  have e2 : (P.dPoly g.1 α β * P.dNextPoly g.1 α β * (h + P.vCells * ε) + P.dPoly g.1 α β).natDegree ≤
      3 * P.nCells - 1 := natDegree_add_le_of_degree_le e1 (hd.trans (by omega))
  have e3 : (P.dPoly g.1 α β * P.dNextPoly g.1 α β * (h + P.vCells * ε) + P.dPoly g.1 α β +
      P.dNextPoly g.1 α β).natDegree ≤ 3 * P.nCells - 1 := natDegree_add_le_of_degree_le e2 (hd'.trans (by omega))
  have t3' : (C μ * P.zgPoly stmt g.1).natDegree ≤ 3 * P.nCells - 1 := t3.trans (by omega)
  have e4 := natDegree_add_le_of_degree_le e3 t3'
  omega

/-- **`(X² + X) d d'` has degree at most `2 N`.** -/
theorem natDegree_Epoly_le (g : P.Msg₁) (α β : F) :
    ((X ^ 2 + X) * P.dPoly g.1 α β * P.dNextPoly g.1 α β).natDegree ≤ 2 * P.nCells := by
  have hn : 44 ≤ P.nCells := by rw [P.nCells_eq]; have := P.eleven_le_card_T; omega
  have hd := natDegree_d_le P g α β
  have hd' := natDegree_d'_le P g α β
  have hw : (X ^ 2 + X : F[X]).natDegree ≤ 2 :=
    natDegree_add_le_of_degree_le (natDegree_X_pow_le 2) (natDegree_X_le.trans (by norm_num))
  exact (natDegree_mul_le_of_le (natDegree_mul_le_of_le hw hd) hd').trans (by omega)

end Kc3.Honest
