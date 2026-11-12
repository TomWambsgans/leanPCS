-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here; `hcar_deployed` follows this repository's `formal/EndToEnd/Soundness/PcsSetup.lean` (`wcol_carries`, at
-- commit 784bd6d8) on F0's deployed instance (`formal/Kc3Circuit/Kc3Circuit/Transport.lean`).
import Soundness.PcsMatch
import PcsBridge.Kc3Deployed
import Kc3Circuit.Transport

/-!
# The deployed instance

F0's instance `Kc3Deployed.deployedParams B hm` on the statement's basis in `E` (`B = basisE`, `β_k = beta()[k]`,
`24` vectors): the circuit's σ, its anchor rows as pins, its last `16` rows random.

* `sigmaSize`: the Statement's σ has `2^24` entries (F0's joins' invariant);
* `pt_deployed`: the cell numbered `c` (`idxE`) is the point `B(c)` (`Domain.point c`);
* `matches_deployed`: the instance matches the statement's constants, the Statement's wiring table carrying σ
  (`Bridge.Ntt.tablePoly_coefficients_cantor`);
* `stackRel_deployed`: a satisfied witness table spells a secret (`Kc3Deployed.relation_of_sat_deployed`, the
  cells being the table's polynomial at the cells' points, which `inputBitsOfStack` computes).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace PcsKS.Deployed

open QuotientRpm QuotientSecurity Compose LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain
open PcsBridge.Kc3 Kc3Deployed Kc3Closed Kc3Wiring SoundPcs WhirBridge LeanVM.Protocol

attribute [local irreducible] PcsQuotient.membershipBuilder Kc3Circuit.membershipBuild PcsQuotient.membership

/-- The statement's basis in `E`. -/
noncomputable abbrev B : CantorBasis E (22 + 2) := basisE Bridge.statementConsts Bridge.isCantor_statementConsts

theorem hm : 22 + 2 ≤ 22 + 2 := le_rfl

/-- The deployed instance. -/
noncomputable abbrev P : _root_.Kc3.Params E := deployedParams B hm

theorem hB : Bridge.Ntt.CantorUpTo 24 := ⟨Bridge.isCantor_statementConsts.1, Bridge.isCantor_statementConsts.2⟩

theorem hβ : ∀ k < 22 + 2, B.β k = ofK (betaAt k) := fun _ _ => rfl

/-! ## σ's size -/

/-- **The Statement's σ has `2^24` entries.** -/
theorem sigmaSize : SigmaSize := by
  unfold SigmaSize
  rw [show PcsQuotient.logRows = 22 from rfl, Kc3Closed.sigma_eq,
    wiring_eq_joins 22 _ rows_size slots_lt, (joins_inv _ _ cell_slots_lt).sigma_size, rows_size]
  norm_num

/-! ## The points -/

theorem idxE_val (i : cantorT B 22 × Fin 4) :
    (idxE B hm i : ℕ) = Completeness.idx ((cantorCells B hm).symm i) := by
  unfold idxE
  rw [Equiv.trans_apply, bitsNum_val, Completeness.idx]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem point_B (x : Fin (22 + 2) → Bool) : B.point x = ofK ((Bridge.Ntt.cantorOf hB).point x) := by
  rw [point_basisE]
  rfl

/-- **The cell numbered `c` is the point `B(c)`.** -/
theorem pt_deployed (i : cantorT B 22 × Fin 4) : P.pt i = ofK (point (idxE B hm i)) := by
  rw [show P.pt i = B.point ((cantorCells B hm).symm i) from pt_ofCantor B hm _ _ _ i, point_B, idxE_val,
    Bridge.Ntt.point_eq_cantor hB (by decide) (Completeness.idx_lt _), Completeness.bitsOf_idx]

theorem pt_deployed' (i : P.T × Fin 4) : P.pt i = ofK (point (idxE B hm i)) := pt_deployed i

/-! ## The match -/

theorem getD_map_point (s : Array ℕ) {i : ℕ} (hi : i < s.size) :
    (s.map PcsQuotient.Domain.point).getD i 0 = PcsQuotient.Domain.point (s.getD i 0) := by
  simp [Array.getD_eq_getD_getElem?, hi]

/-- **The Statement's wiring table carries σ** on the instance's cells. -/
theorem hcar_deployed (i : cantorT B 22 × Fin 4) :
    (tablePoly (colFn wcol)).eval (P.pt i) = P.pt (deployedSigma B hm i) := by
  have hσ := sigmaSize
  have hvsz : ((membership PcsQuotient.logRows).sigma.map PcsQuotient.Domain.point).size = 2 ^ 24 := by
    rw [Array.size_map, hσ]
  have hfn : colFn wcol = fun b => ofK ((PcsQuotient.Domain.coefficients 24 0
      ((membership PcsQuotient.logRows).sigma.map PcsQuotient.Domain.point)).getD (Completeness.idx b) 0) := by
    funext b
    rw [colFn_wcol, wiringTable_eq]
  set x := (cantorCells B hm).symm i with hx
  have hL := Bridge.Ntt.tablePoly_coefficients_cantor hB (by decide) _ hvsz x
  have hxlt : Completeness.idx x < (membership PcsQuotient.logRows).sigma.size := by
    rw [hσ]; exact Completeness.idx_lt x
  rw [getD_map_point _ hxlt] at hL
  rw [pt_deployed, pt_deployed, idx_sigma, sigC_def, idxE_val, ← hx, hfn, ← map_tablePoly,
    show (ofK (point (Completeness.idx x)) : E) = algebraMap K E (point (Completeness.idx x)) from rfl,
    Polynomial.eval_map, Polynomial.eval₂_at_apply,
    Bridge.Ntt.point_eq_cantor hB (by decide) (Completeness.idx_lt _), Completeness.bitsOf_idx, hL]
  rfl

theorem hpins_deployed (k : Fin 11) : P.pinPt k = pinE k := by
  refine (pt_deployed ((deployedPins B hm k : cantorT B 22), (2 : Fin 4))).trans ?_
  have h : (idxE B hm (deployedPins B hm k, 2) : ℕ) = 4 * k + 2 :=
    cell_of_row B hm k (by have := k.2; omega) 2
  rw [h]
  rfl

/-- **The deployed instance matches the statement's constants.** -/
theorem matches_deployed : Matches P (colFn wcol) :=
  matches_ofCantor B hm _ _ _ hβ (colFn wcol) hpins_deployed hcar_deployed

/-! ## The relation -/

theorem colFn_mk (st : Vector K (2 ^ 24)) (b : Fin 24 → Bool) :
    colFn (⟨st⟩ : Column 24) b = ofK (st.toArray.getD (Completeness.idx b) 0) := by
  have h1 : Whir.bitsEquiv 24 b = ⟨Completeness.idx b, Completeness.idx_lt b⟩ :=
    Fin.ext (by rw [Whir.bitsEquiv_val, bitsToNat_eq_idx])
  have hl : Completeness.idx b < 16777216 := Completeness.idx_lt b
  unfold colFn
  simp [tabFn, h1, hl, Array.getD_eq_getD_getElem?, Vector.getElem?_eq_getElem hl]

/-- The stack's first `2^24` entries, as `inputBitsOfStack` reads them. -/
def wHatOf (st : Vector K (2 ^ 24)) : Array K := Array.ofFn (n := 2 ^ 24) fun j => st.toArray.getD j.val 0

/-- **The cells of the stack's quarters are the values `inputBitsOfStack` computes.** -/
theorem cells_stack (st : Vector K (2 ^ 24)) (i : cantorT B 22 × Fin 4) :
    P.cells (witnessOfTable (k := 22) (colFn (⟨st⟩ : Column 24))) i =
      ofK ((values 24 0 (wHatOf st)).getD (idxE B hm i) 0) := by
  have hsz : (wHatOf st).size = 2 ^ 24 := by simp [wHatOf]
  have hlt : (idxE B hm i : ℕ) < 2 ^ 24 := (idxE B hm i).isLt
  have hfn : colFn (⟨st⟩ : Column 24) = fun b => ofK ((wHatOf st).getD (Completeness.idx b) 0) := by
    funext b
    have hl : Completeness.idx b < 16777216 := Completeness.idx_lt b
    rw [colFn_mk]
    simp [wHatOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hl, Vector.getElem?_eq_getElem hl]
  refine (cells_witnessOfTable P _ i).trans ?_
  rw [pt_deployed, Bridge.Ntt.values_getD_tablePoly hB (by decide) 0 _ hsz hlt, zero_add,
    hfn, ← map_tablePoly,
    show (ofK (point (idxE B hm i)) : E) = algebraMap K E (point (idxE B hm i)) from rfl,
    Polynomial.eval_map, Polynomial.eval₂_at_apply]
  rfl

theorem ofK_eq_one_iff (a : K) : ofK a = 1 ↔ a = 1 := by
  rw [← Compose.Reduce.ofK_one]
  exact (algebraMap K E).injective.eq_iff

theorem membership_logRows_eq : (membership PcsQuotient.logRows).logRows = 22 := by
  unfold membership finish
  rfl

/-- **A satisfied witness table spells a secret** at the deployed instance. -/
theorem stackRel_deployed : StackRel P (readWK P matches_deployed.card) := by
  intro stmt st h
  rw [readWK_fst] at h
  have hs : stmtVals (stmt.y ++ stmt.root) = Kc3Deployed.stmtOf stmt := by
    funext k
    simp only [stmtVals, Kc3Deployed.stmtOf, stmtOf_bytes]
  rw [hs] at h
  have hr := relation_of_sat_deployed B hm stmt _ h
  have e : inputBitsOfStack (membership PcsQuotient.logRows) st =
      inputBits B hm (P.cells (witnessOfTable (k := 22) (colFn (⟨st⟩ : Column 24)))) := by
    unfold inputBitsOfStack inputBits
    rw [membership_logRows_eq]
    refine List.map_congr_left fun r _ => ?_
    by_cases hc : 4 * r + 3 < 4 * 2 ^ 22
    · have hw : wIdx B hm (P.cells (witnessOfTable (k := 22) (colFn (⟨st⟩ : Column 24)))) (4 * r + 3) =
          ofK ((values 24 0 (wHatOf st)).getD (4 * r + 3) 0) := by
        unfold wIdx
        rw [dif_pos hc, cells_stack, idx_cellOf]
      rw [hw]
      simp only [ofK_eq_one_iff]
      rfl
    · have hw : wIdx B hm (P.cells (witnessOfTable (k := 22) (colFn (⟨st⟩ : Column 24)))) (4 * r + 3) = 0 := by
        unfold wIdx
        rw [dif_neg hc]
      have hv : (values (PcsQuotient.cellVars 22) 0 (Array.ofFn (n := 2 ^ PcsQuotient.cellVars 22) fun i =>
          st.toArray.getD i.val 0)).getD (4 * r + 3) 0 = 0 := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none]
        · rfl
        · rw [Bridge.Ntt.values_size, Array.size_ofFn]
          show 2 ^ 24 ≤ 4 * r + 3
          omega
      rw [hw, hv]
      simp
  unfold secretOfStack
  rw [e]
  exact hr

end PcsKS.Deployed

namespace Soundness

open PcsKS.Deployed

/-- **Knowledge soundness of the deployed membership proof in the random-permutation model**, for the Statement's
extractor and experiment, with no hypothesis: an adversary of at most `Q` calls of `π`, `π⁻¹` makes the verifier
accept while the extractor (reading the setup's tree and the adversary's transcript) outputs no secret of the
statement with probability at most `ksBound Q`. -/
theorem knowledgeSoundness : PcsQuotient.KnowledgeSoundness ksBound :=
  knowledgeSoundness_of_matches P (Kc3Deployed.poleCondition_deployed B hm) matches_deployed stackRel_deployed
    sigmaSize

end Soundness
