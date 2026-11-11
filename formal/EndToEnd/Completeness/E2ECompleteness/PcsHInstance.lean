-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: F1's (`formal/Kc3`) parameters for the deployed circuit, on the Statement's basis, for completeness.
import E2ECompleteness.PcsHBasis
import E2ECompleteness.PcsKc3
import E2ECompleteness.PcsKc3Claims
import E2ECompleteness.PcsSizes
import Kc3.Cantor
import Completeness.Tables

/-!
# F1's parameters for the deployed circuit

Given that the circuit's wiring is a permutation of the `2^24` cells (`SigmaPerm`, F0's `sigma_lt` and
`sigma_inj`), `deployedP` is F1's instance on the Statement's basis (`Kc3.Params.ofCantor` of `BE`, `2^22` rows):
cell `i` is the cell of `i`'s bits (`cellAt`, role `i mod 4` of row `i / 4`), σ the circuit's, the pins the rows
`k < 11`. **`deployedP_matches`**: it matches the statement's constants (`PcsBridge.Kc3.Matches`) with the
circuit's wiring table; **`sat_deployedP`**: cells given as `v` by index that satisfy the gates, the copies and
the pins by index (F0's `GatesIdx`, `CopiesIdx`, `PinsIdx`) satisfy F1's relation, for the first message of a
witness table whose polynomial takes the value `v i` at `B(i)` (`cells_witnessOfTable`).
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

/-- **The wiring permutes the cells** (F0's `sigma_lt`, `sigma_inj`). -/
def SigmaPerm : Prop :=
  (∀ c < 2 ^ 24, sig c < 2 ^ 24) ∧ ∀ c < 2 ^ 24, ∀ d < 2 ^ 24, sig c = sig d → c = d

/-! ## Bits -/

theorem bitsOf_inj {m a b : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ m) (h : Completeness.bitsOf m a = Completeness.bitsOf m b) :
    a = b := by
  rw [← Completeness.idx_bitsOf m a ha, ← Completeness.idx_bitsOf m b hb, h]

/-- The bits of cell `4 r + c`: its role's two, then its row's. -/
theorem bitsOf_cell (r : ℕ) (c : Fin 4) :
    Completeness.bitsOf 24 (4 * r + c) = cellBits (Completeness.bitsOf 22 r, c) := by
  have hc := c.2
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
  · show (4 * r + c).testBit 0 = roleBit0 c
    rw [Nat.testBit_zero, show (4 * r + (c : ℕ)) % 2 = (c : ℕ) % 2 by omega]
    fin_cases c <;> rfl
  · show (4 * r + c).testBit 1 = roleBit1 c
    rw [Nat.testBit_succ, Nat.testBit_zero, show (4 * r + (c : ℕ)) / 2 % 2 = (c : ℕ) / 2 by omega]
    fin_cases c <;> rfl
  · show (4 * r + c).testBit (k + 1 + 1) = r.testBit k
    rw [Nat.testBit_succ, Nat.testBit_succ, show (4 * r + (c : ℕ)) / 2 / 2 = r by omega]

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

/-! ## The cells -/

/-- The cell of index `i` (its bits). -/
noncomputable def cellAt (i : ℕ) : cantorT BE 22 × Fin 4 := cantorCells BE hm28 (Completeness.bitsOf 24 i)

/-- The row of index `r`. -/
noncomputable def rowOf (r : ℕ) : cantorT BE 22 := cantorRows BE hm28 (Completeness.bitsOf 22 r)

theorem cellAt_cell (r : ℕ) (c : Fin 4) : cellAt (4 * r + c) = (rowOf r, c) := by
  unfold cellAt cantorCells
  rw [bitsOf_cell, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem rowOf_injective {r r' : ℕ} (hr : r < 2 ^ 22) (hr' : r' < 2 ^ 22) (h : rowOf r = rowOf r') : r = r' :=
  bitsOf_inj hr hr' ((cantorRows BE hm28).injective h)

theorem cellAt_idx (x : Fin 24 → Bool) : cellAt (Completeness.idx x) = cantorCells BE hm28 x := by
  rw [cellAt, Completeness.bitsOf_idx]

/-- Every row is a row of index below `2^22`. -/
theorem exists_rowOf (x : cantorT BE 22) : ∃ r < 2 ^ 22, rowOf r = x :=
  ⟨Completeness.idx ((cantorRows BE hm28).symm x), Completeness.idx_lt _, by
    rw [rowOf, Completeness.bitsOf_idx, Equiv.apply_symm_apply]⟩

/-- Every cell is a cell of index below `2^24`. -/
theorem exists_cellAt (i : cantorT BE 22 × Fin 4) : ∃ c < 2 ^ 24, cellAt c = i :=
  ⟨Completeness.idx ((cantorCells BE hm28).symm i), Completeness.idx_lt _, by
    rw [cellAt_idx, Equiv.apply_symm_apply]⟩

/-! ## The wiring, the pins -/

/-- The wiring on bits. -/
noncomputable def sigBits (x : Fin 24 → Bool) : Fin 24 → Bool :=
  Completeness.bitsOf 24 (sig (Completeness.idx x))

theorem sigBits_injective (hσ : SigmaPerm) : Function.Injective sigBits := by
  intro x y h
  have h1 := bitsOf_inj (hσ.1 _ (Completeness.idx_lt x)) (hσ.1 _ (Completeness.idx_lt y)) h
  have h2 := hσ.2 _ (Completeness.idx_lt x) _ (Completeness.idx_lt y) h1
  rw [← Completeness.bitsOf_idx x, ← Completeness.bitsOf_idx y, h2]

/-- The wiring as a permutation of the cells. -/
noncomputable def sigmaP (hσ : SigmaPerm) : Equiv.Perm (cantorT BE 22 × Fin 4) :=
  ((cantorCells BE hm28).symm.trans
    (Equiv.ofBijective sigBits (Finite.injective_iff_bijective.mp (sigBits_injective hσ)))).trans
    (cantorCells BE hm28)

theorem sigmaP_cellAt (hσ : SigmaPerm) {c : ℕ} (hc : c < 2 ^ 24) :
    sigmaP hσ (cellAt c) = cellAt (sig c) := by
  simp only [sigmaP, cellAt, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.ofBijective_apply, sigBits,
    Completeness.idx_bitsOf 24 c hc]

/-- The pins: rows `0 … 10`. -/
noncomputable def pinsP : Fin _root_.Kc3.pinCount ↪ cantorT BE 22 :=
  ⟨fun k => rowOf k, fun k k' h => Fin.ext (rowOf_injective (by have := k.2; simp only [_root_.Kc3.pinCount] at this; omega)
    (by have := k'.2; simp only [_root_.Kc3.pinCount] at this; omega) h)⟩

/-- **F1's parameters for the deployed circuit.** -/
noncomputable def deployedP (hσ : SigmaPerm) : _root_.Kc3.Params E :=
  _root_.Kc3.Params.ofCantor BE hm28 (sigmaP hσ) pinsP ∅

variable (hσ : SigmaPerm)

theorem deployedP_pt (i : cantorT BE 22 × Fin 4) :
    (deployedP hσ).pt i = BE.point ((cantorCells BE hm28).symm i) :=
  cantorCells_symm_point BE hm28 i

theorem deployedP_pt_cellAt {c : ℕ} (hc : c < 2 ^ 24) : (deployedP hσ).pt (cellAt c) = ofK (point c) := by
  rw [deployedP_pt, cellAt, Equiv.symm_apply_apply, ofK_point (by norm_num) hc]

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

/-- The rows' polynomial, as the verifier evaluates it. -/
noncomputable def rowsPolyE : E[X] := ∑ k ∈ range 23, C (ofK ((rowVanishing 24).getD k 0)) * digitPoly k

theorem rowsPolyE_monic : rowsPolyE.Monic ∧ rowsPolyE.natDegree = 2 ^ 22 := by
  have hlow : (∑ k ∈ range 22, C (ofK ((rowVanishing 24).getD k 0)) * digitPoly k : E[X]).natDegree
      < (digitPoly 22 : E[X]).natDegree := by
    rw [Novel.digit_natDegree]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := 2 ^ 21) fun k hk => ?_) (by norm_num)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [Novel.digit_natDegree]
    exact Nat.pow_le_pow_right (by norm_num) (by simp at hk; omega)
  have e : rowsPolyE =
      ∑ k ∈ range 22, C (ofK ((rowVanishing 24).getD k 0)) * digitPoly k + digitPoly 22 := by
    rw [rowsPolyE, Finset.sum_range_succ, rowVanishing_last, Compose.Reduce.ofK_one, C_1, one_mul]
  rw [e]
  exact ⟨(Novel.digit_monic 22).add_of_right (degree_lt_degree hlow),
    by rw [natDegree_add_eq_right_of_natDegree_lt hlow, Novel.digit_natDegree]⟩

theorem rowsPolyE_eval (t : E) : rowsPolyE.eval t = PcsBridge.Kc3.rowsAt t := by
  simp only [rowsPolyE, eval_finsetSum, Polynomial.eval_mul, eval_C, digitPoly_eval, PcsBridge.Kc3.rowsAt]

theorem rowsPolyE_eval_sum {ι : Type*} (s : Finset ι) (f : ι → E) :
    rowsPolyE.eval (∑ i ∈ s, f i) = ∑ i ∈ s, rowsPolyE.eval (f i) := by
  simp only [rowsPolyE_eval, PcsBridge.Kc3.rowsAt, sq_iterate_sum, Finset.mul_sum]
  exact Finset.sum_comm

/-- The rows' polynomial vanishes at `β_j`, `2 ≤ j < 24`. -/
theorem rowsPolyE_beta {j : ℕ} (hj2 : 2 ≤ j) (hj : j < 24) : rowsPolyE.eval (BE.β j) = 0 := by
  have h := congrArg ofK (rowPolyAt_beta hj2 hj)
  rw [rowPolyAt_eq_sum', ofK_sum, Compose.Reduce.ofK_zero] at h
  rw [← h, rowsPolyE_eval, PcsBridge.Kc3.rowsAt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Compose.Reduce.ofK_mul, ofK_S_iterate, BE_β]

theorem vCells_eq : (deployedP hσ).vCells = digitPoly 24 := by
  symm
  refine eq_prod_of_monic_of_roots (Novel.digit_monic 24) ?_ (deployedP hσ).pt_injective fun i => ?_
  · rw [Novel.digit_natDegree]
    exact (_root_.Kc3.ofCantor_nCells BE hm28 (sigmaP hσ) pinsP ∅).symm
  · have e := deployedP_pt hσ i
    rw [e, digitPoly_eval]
    exact BE.iterate_point (by norm_num) _

theorem vRows_eq : (deployedP hσ).vRows = rowsPolyE := by
  symm
  refine eq_prod_of_monic_of_roots rowsPolyE_monic.1 ?_ Subtype.val_injective fun x => ?_
  · rw [rowsPolyE_monic.2, Fintype.card_coe]
    exact (_root_.Kc3.card_cantorT BE hm28).symm
  · obtain ⟨y, -, hy⟩ := Finset.mem_image.mp x.2
    show rowsPolyE.eval (x : E) = 0
    rw [← hy, CantorBasis.point, rowsPolyE_eval_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hj
    · have h2 : 2 ≤ (j : ℕ) := by
        by_contra h
        have : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
        rcases this with h0 | h1
        · have : j = 0 := Fin.ext h0
          subst this
          simp [cellBits, roleBit0] at hj
        · have : j = Fin.succ 0 := Fin.ext h1
          subst this
          simp [cellBits, roleBit1] at hj
      exact rowsPolyE_beta h2 j.2
    · rw [rowsPolyE_eval, PcsBridge.Kc3.rowsAt]
      simp [sq_iterate_zero]

theorem pinPt_eq (k : Fin _root_.Kc3.pinCount) : (deployedP hσ).pinPt k = PcsBridge.Kc3.pinE k := by
  have hc : cellAt (4 * k + 2) = (rowOf k, 2) := cellAt_cell k 2
  have hk := k.2
  simp only [_root_.Kc3.pinCount] at hk
  have e := deployedP_pt_cellAt hσ (c := 4 * k + 2) (by omega)
  rw [hc] at e
  exact e

theorem sigmaPoly_eq : (deployedP hσ).sigmaPoly = tablePoly s₀ := by
  symm
  refine Lagrange.eq_interpolate_of_eval_eq _ (deployedP hσ).pt_injective.injOn ?_ fun i _ => ?_
  · rw [Finset.card_univ]
    have h1 : Fintype.card (cantorT BE 22 × Fin 4) = 2 ^ 24 :=
      _root_.Kc3.ofCantor_nCells BE hm28 (sigmaP hσ) pinsP ∅
    rw [h1]
    by_cases h0 : tablePoly s₀ = 0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree h0]
      exact_mod_cast natDegree_tablePoly_lt s₀
  · obtain ⟨c, hc, rfl⟩ := exists_cellAt i
    have e1 := deployedP_pt_cellAt hσ hc
    have e2 := deployedP_pt_cellAt hσ (hσ.1 c hc)
    rw [← sigmaP_cellAt hσ hc] at e2
    show (tablePoly s₀).eval ((deployedP hσ).pt (cellAt c)) = (deployedP hσ).pt (sigmaP hσ (cellAt c))
    rw [e1, e2, s₀_eval_point hc]

/-- **F1's parameters match the statement's constants**, with the circuit's wiring table. -/
theorem deployedP_matches : PcsBridge.Kc3.Matches (deployedP hσ) s₀ where
  theta := rfl
  card := _root_.Kc3.card_cantorT BE hm28
  vCells t := by rw [vCells_eq, digitPoly_eval]
  vRows t := by rw [vRows_eq, rowsPolyE_eval]
  pins := pinPt_eq hσ
  sigma t := by rw [sigmaPoly_eq]

end E2ECompleteness.Pcs.H
