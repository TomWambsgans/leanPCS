-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The second challenge, in the style of `formal/QuotientSecurity/RoundTwo.lean` and `Degrees.lean` (adapted from
-- leanVM, branch PCS-openings-aggregation, commit 651453c6).
import Kc3.RoundOne

/-!
# The second challenge

If the second message is not consistent with the first, the identity, a nonzero polynomial of degree at most
`4 n − 1`, vanishes at fewer than `D2 = 4 n` points `t` (`card_round2_le`). The degrees: the cells' polynomials
below `n` (row polynomials below `n / 4`), `d`, `d'` below `n`, `q` and `x h` at most `2 n`, `Z g` at most
`3 n − 2`; so `X Z q` at most `3 n + 1`, `d d' P` at most `4 n − 2`, `X R` at most `3 n − 1`.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Kc3

open QuotientSecurity QuotientSecurity.Params

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] (P : Params F)

namespace Params

/-- Eleven anchor rows: at least eleven rows. -/
theorem eleven_le_card_T : 11 ≤ P.T.card := by
  have h := Fintype.card_le_of_embedding P.pins
  rw [Fintype.card_fin, Fintype.card_coe] at h
  exact h

theorem natDegree_digit_le (j : Fin 4) : (digit j : F[X]).natDegree ≤ 3 := by
  fin_cases j <;> simp only [digit, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
    Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;> compute_degree <;> norm_num

theorem natDegree_rowPoly : (rowPoly : F[X]).natDegree = 4 := by
  unfold rowPoly; compute_degree!

/-- The cells' polynomials are below `n`. -/
theorem natDegree_cellPoly_le (g : P.Msg₁) (c : Fin 4) :
    (P.cellPoly g.1 c).natDegree ≤ P.nCells - 1 := by
  rw [P.nCells_eq]
  have hN := P.card_T_pos
  unfold cellPoly
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine (natDegree_mul_le_of_le (m := 3) (n := 4 * (P.T.card - 1)) ?_ ?_).trans (by omega)
  · rw [natDegree_comp, natDegree_X_add_C, mul_one]; exact natDegree_digit_le j
  · rw [natDegree_comp, natDegree_rowPoly]
    have := g.2 j
    have : (g.1 j).natDegree ≤ P.T.card - 1 := by omega
    calc (g.1 j).natDegree * 4 ≤ (P.T.card - 1) * 4 := Nat.mul_le_mul_right _ this
      _ = 4 * (P.T.card - 1) := by ring

theorem natDegree_prod_sub_C_le {ι : Type*} (s : Finset ι) (a : ι → F) :
    (∏ i ∈ s, (X - C (a i))).natDegree ≤ s.card := by
  refine (natDegree_prod_le _ _).trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl fun i _ => natDegree_X_sub_C (a i)]
  simp

theorem natDegree_cofRows_le : P.cofRows.natDegree ≤ P.nCells :=
  (natDegree_prod_sub_C_le _ _).trans ((Finset.card_le_univ _).trans le_rfl)

theorem natDegree_cofPins_le : P.cofPins.natDegree ≤ P.nCells :=
  (natDegree_prod_sub_C_le _ _).trans ((Finset.card_le_univ _).trans le_rfl)

theorem natDegree_pinPoly_le (stmt : Stmt F) : (P.pinPoly stmt).natDegree ≤ 10 := by
  by_cases h : P.pinPoly stmt = 0
  · rw [h, natDegree_zero]; omega
  · have hd := Lagrange.degree_interpolate_lt (s := (univ : Finset (Fin pinCount))) (v := P.pinPt) stmt
      P.pinPt_injective.injOn
    rw [Finset.card_univ, Fintype.card_fin] at hd
    have := (natDegree_lt_iff_degree_lt h).mpr hd
    have h11 : pinCount = 11 := rfl
    omega

set_option maxHeartbeats 1000000 in
/-- **The identity's degree**: at most `4 n − 1`. -/
theorem natDegree_identity_le (stmt : Stmt F) (g : P.Msg₁) (R : P.Msg₂) (α β μ : F) :
    (P.identity stmt g.1 R.1 α β μ).natDegree ≤ 4 * P.nCells - 1 := by
  have hn : 44 ≤ P.nCells := by rw [P.nCells_eq]; have := P.eleven_le_card_T; omega
  have hc0 := P.natDegree_cellPoly_le g 0
  have hc1 := P.natDegree_cellPoly_le g 1
  have hc2 := P.natDegree_cellPoly_le g 2
  have hc3 := P.natDegree_cellPoly_le g 3
  obtain ⟨⟨A₀, A₁, B₀, B₁⟩, hA0, hA1, hB0, hB1⟩ := R
  simp only at hA0 hA1 hB0 hB1
  have hσ : P.sigmaPoly.natDegree < P.nCells := by rw [P.nCells_eq]; exact P.hσdeg
  have hZ : P.vCells.natDegree ≤ P.nCells := P.natDegree_vCells.le
  have hcr := P.natDegree_cofRows_le
  have hcp := P.natDegree_cofPins_le
  have hpin := P.natDegree_pinPoly_le stmt
  have hX : (X : F[X]).natDegree ≤ 1 := natDegree_X_le
  have hCα := (natDegree_C (R := F) α).le
  have hCβ := (natDegree_C (R := F) β).le
  have hCμ := (natDegree_C (R := F) μ).le
  generalize P.nCells = N at hn hc0 hc1 hc2 hc3 hA0 hA1 hB0 hB1 hσ hZ hcr hcp ⊢
  have hzeta : P.zeta.natDegree ≤ N + 1 := natDegree_mul_le_of_le hZ hX
  have hq : (P.qPoly ⟨A₀, A₁, B₀, B₁⟩).natDegree ≤ 2 * N := by
    have h1 := natDegree_mul_le_of_le hzeta (Nat.le_refl A₁.natDegree)
    refine natDegree_add_le_of_degree_le ?_ ?_
    · show A₀.natDegree ≤ 2 * N; omega
    · exact h1.trans (by omega)
  have hP : (P.xhPoly ⟨A₀, A₁, B₀, B₁⟩).natDegree ≤ 2 * N := by
    have h1 := natDegree_mul_le_of_le hzeta (Nat.le_refl B₁.natDegree)
    refine natDegree_add_le_of_degree_le ?_ ?_
    · show B₀.natDegree ≤ 2 * N; omega
    · exact h1.trans (by omega)
  have hd : (P.dPoly g.1 α β).natDegree ≤ N - 1 := by
    have h1 := natDegree_mul_le_of_le hCβ hX
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ hc0) ?_
    · exact hCα.trans (by omega)
    · exact h1.trans (by omega)
  have hd' : (P.dNextPoly g.1 α β).natDegree ≤ N - 1 := by
    have h1 := natDegree_mul_le_of_le hCβ (le_refl P.sigmaPoly.natDegree)
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ hc0) ?_
    · exact hCα.trans (by omega)
    · exact h1.trans (by omega)
  have hgate : (P.gatePoly g.1).natDegree ≤ 2 * N - 2 := by
    unfold gatePoly gate
    have h1 := natDegree_mul_le_of_le hc0 hc2
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_) ?_
    · exact hc3.trans (by omega)
    · exact hc1.trans (by omega)
    · exact hc2.trans (by omega)
    · exact h1.trans (by omega)
  have hzg : (P.zgPoly stmt g.1).natDegree ≤ 3 * N - 2 := by
    unfold zgPoly
    have h1 := natDegree_mul_le_of_le hcr hgate
    have h3 : (P.cellPoly g.1 0 + P.pinPoly stmt).natDegree ≤ N - 1 := by
      refine natDegree_add_le_of_degree_le hc0 ?_
      exact hpin.trans (by omega)
    have h2 := natDegree_mul_le_of_le hcp h3
    refine natDegree_add_le_of_degree_le ?_ ?_
    · exact h1.trans (by omega)
    · exact h2.trans (by omega)
  have hR : (P.rhsPoly stmt g.1 α β μ).natDegree ≤ 3 * N - 2 := by
    unfold rhsPoly
    have h1 := natDegree_mul_le_of_le hCμ hzg
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
    · exact hd.trans (by omega)
    · exact hd'.trans (by omega)
    · exact h1.trans (by omega)
  unfold identity
  have t1 := natDegree_mul_le_of_le (natDegree_mul_le_of_le hX hZ) hq
  have t2 := natDegree_mul_le_of_le (natDegree_mul_le_of_le hd hd') hP
  have t3 := natDegree_mul_le_of_le hX hR
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
  · exact t1.trans (by omega)
  · exact t2.trans (by omega)
  · exact t3.trans (by omega)

variable [Fintype F]

open Classical in
/-- **The second challenge.** If the second message is not consistent, the identity holds at fewer than `D2`
points. -/
theorem card_round2_le (stmt : Stmt F) (g : P.Msg₁) (R : P.Msg₂) (α β μ : F)
    (h : ¬ P.Consistent stmt g.1 R.1 α β μ) :
    (univ.filter fun t : F => P.ConsistentAt stmt g.1 R.1 α β μ t).card ≤ P.D2 := by
  have h0 : P.identity stmt g.1 R.1 α β μ ≠ 0 := h
  calc (univ.filter fun t : F => P.ConsistentAt stmt g.1 R.1 α β μ t).card
      ≤ (P.identity stmt g.1 R.1 α β μ).roots.toFinset.card := Finset.card_le_card fun t ht => by
        rw [Finset.mem_filter] at ht
        rw [Multiset.mem_toFinset, mem_roots h0, IsRoot.def]
        exact ht.2
    _ ≤ Multiset.card (P.identity stmt g.1 R.1 α β μ).roots := Multiset.toFinset_card_le _
    _ ≤ (P.identity stmt g.1 R.1 α β μ).natDegree := card_roots' _
    _ ≤ 4 * P.nCells - 1 := P.natDegree_identity_le stmt g R α β μ
    _ ≤ P.D2 := by unfold D2; omega

end Params

end Kc3
