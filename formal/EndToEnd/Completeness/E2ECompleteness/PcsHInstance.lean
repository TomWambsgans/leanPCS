-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: F1's (`formal/Kc3`) parameters for the deployed circuit, on the Statement's basis, for completeness.
import E2ECompleteness.PcsHBasis
import E2ECompleteness.PcsKc3
import E2ECompleteness.PcsKc3Claims
import E2ECompleteness.PcsSizes
import Kc3.Cantor
import Completeness.Tables
import Kc3Circuit.Transport
import PcsBridge.Kc3Deployed

/-!
# F1's parameters for the deployed circuit

`P0` is F0's instance of the deployed circuit (`Kc3Deployed.deployedParams`) on the Statement's basis `BE`: cell
`i` is the cell numbered `idxE i`, at the point `B(idxE i)` (`pt_idx`). **`P0_matches`**: it matches the
statement's constants (`PcsBridge.Kc3.Matches`) with the circuit's wiring table `s₀`; `vCells_eq`: its cells'
vanishing polynomial is `w₂₄`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

-- The membership circuit is a closed term of `2^22` rows: never evaluate it.
attribute [local irreducible] PcsQuotient.membership PcsQuotient.membershipBuilder

namespace E2ECompleteness.Pcs.H

theorem hm28 : 22 + 2 ≤ 28 := by norm_num

/-- The circuit's wiring, by index. -/
def sig (c : ℕ) : ℕ := (membership logRows).sigma.getD c 0

theorem sig_eq_sigC (c : ℕ) : sig c = Kc3Closed.sigC c := by
  rw [Kc3Closed.sigC_def]; rfl

/-- **The polynomial of a table by index** is the novel-basis polynomial of its entries. -/
theorem tablePoly_idx {F : Type} [Field F] [CharP F 2] (m : ℕ) (f : ℕ → F) :
    tablePoly (fun b : Fin m → Bool => f (Completeness.idx b)) = Novel.nov 0 m f := by
  unfold tablePoly Novel.nov Novel.basisAt
  refine Finset.sum_bij' (fun b _ ↦ Completeness.idx b) (fun j _ ↦ Completeness.bitsOf m j)
    (fun b _ ↦ Finset.mem_range.mpr (Completeness.idx_lt b)) (fun _ _ ↦ Finset.mem_univ _)
    (fun b _ ↦ Completeness.bitsOf_idx b) (fun j hj ↦ Completeness.idx_bitsOf m j (Finset.mem_range.mp hj))
    (fun b _ ↦ ?_)
  congr 1
  rw [← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Completeness.testBit_idx, zero_add]

/-! ## The deployed instance (F0's `Kc3Deployed.deployedParams`) on the Statement's basis -/

/-- **F1's parameters for the deployed circuit**, on `BE`. -/
noncomputable def P0 : _root_.Kc3.Params E := Kc3Deployed.deployedParams BE hm28

theorem bitsNum_eq_idx {m : ℕ} (x : Fin m → Bool) : (Kc3Deployed.bitsNum x : ℕ) = Completeness.idx x := by
  rw [Kc3Deployed.bitsNum_val, Completeness.idx]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem idxE_eq (i : cantorT BE 22 × Fin 4) :
    (Kc3Deployed.idxE BE hm28 i : ℕ) = Completeness.idx ((cantorCells BE hm28).symm i) := by
  rw [Kc3Deployed.idxE, Equiv.trans_apply, bitsNum_eq_idx]

/-- **A cell's point is the point of its number.** -/
theorem pt_idx (i : P0.T × Fin 4) : P0.pt i = ofK (point (Kc3Deployed.idxE BE hm28 i)) := by
  have h1 : P0.pt i = BE.point ((cantorCells BE hm28).symm i) := cantorCells_symm_point BE hm28 i
  have h2 := ofK_point (m := 24) (by norm_num) (Completeness.idx_lt ((cantorCells BE hm28).symm i))
  rw [Completeness.bitsOf_idx] at h2
  exact h1.trans (h2.symm.trans (congrArg (fun n => ofK (point n)) (idxE_eq i).symm))

/-! ## The match -/

/-- The circuit's wiring table, in `E`. -/
noncomputable def s₀ : (Fin 24 → Bool) → E :=
  fun b => ofK ((membership logRows).wiringTable.getD (Completeness.idx b) 0)

theorem membership_logRows' : (membership logRows).logRows = 22 := by
  unfold membership finish; rfl

theorem sigma_map_size : ((membership logRows).sigma.map point).size = 2 ^ 24 := by
  rw [Array.size_map]; exact E2ECompleteness.Pcs.membership_sigma_size

/-- **The wiring polynomial at a cell** is the point σ sends it to. -/
theorem s₀_eval_point {c : ℕ} (hc : c < 2 ^ 24) :
    (tablePoly s₀).eval (ofK (point c)) = ofK (point (sig c)) := by
  have h := nov_coefficients_K (m := 24) (by norm_num) 0 _ sigma_map_size hc
  rw [zero_add] at h
  rw [show s₀ = fun b => ofK ((membership logRows).wiringTable.getD (Completeness.idx b) 0) from rfl,
    tablePoly_idx 24 (fun j => ofK ((membership logRows).wiringTable.getD j 0))]
  have hw : (membership logRows).wiringTable = coefficients 24 0 ((membership logRows).sigma.map point) := by
    rw [Circuit.wiringTable, membership_logRows']
  rw [hw, h]
  have hs : c < (membership logRows).sigma.size := by rw [E2ECompleteness.Pcs.membership_sigma_size]; exact hc
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hs, Option.map_some,
    Option.getD_some, sig, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, Option.getD_some]

theorem vCells_eq : P0.vCells = digitPoly 24 := by
  symm
  refine eq_prod_of_monic_of_roots (Novel.digit_monic 24) ?_ P0.pt_injective fun i => ?_
  · rw [Novel.digit_natDegree]
    exact (_root_.Kc3.ofCantor_nCells BE hm28 _ _ _).symm
  · have e : P0.pt i = BE.point ((cantorCells BE hm28).symm i) := cantorCells_symm_point BE hm28 i
    rw [e, digitPoly_eval]
    exact BE.iterate_point (by norm_num) _

theorem pinPt_eq (k : Fin _root_.Kc3.pinCount) : P0.pinPt k = PcsBridge.Kc3.pinE k := by
  have hk := k.2
  simp only [_root_.Kc3.pinCount] at hk
  have h := pt_idx ((P0.pins k, 2) : P0.T × Fin 4)
  have e : (Kc3Deployed.idxE BE hm28 (P0.pins k, 2) : ℕ) = 4 * k + 2 :=
    Kc3Deployed.cell_of_row BE hm28 k (by omega) 2
  exact h.trans (congrArg (fun n => ofK (point n)) e)

theorem sigma_carries (i : P0.T × Fin 4) :
    (tablePoly s₀).eval (P0.pt i) = P0.pt (P0.σ i) := by
  have h1 := pt_idx i
  have h2 := pt_idx (P0.σ i)
  have h3 : (Kc3Deployed.idxE BE hm28 (P0.σ i) : ℕ) = Kc3Closed.sigC (Kc3Deployed.idxE BE hm28 i) :=
    Kc3Deployed.idx_sigma BE hm28 i
  have hl : (Kc3Deployed.idxE BE hm28 i : ℕ) < 2 ^ 24 := by have := Kc3Deployed.idx_lt BE hm28 i; omega
  rw [h1, h2]
  refine (s₀_eval_point hl).trans (congrArg (fun n => ofK (point n)) ?_)
  rw [h3, sig_eq_sigC]

/-- **F1's parameters match the statement's constants**, with the circuit's wiring table. -/
theorem P0_matches : PcsBridge.Kc3.Matches P0 s₀ :=
  PcsBridge.Kc3.matches_ofCantor BE hm28 _ _ _ (fun k _ => rfl) s₀ pinPt_eq sigma_carries

end E2ECompleteness.Pcs.H
