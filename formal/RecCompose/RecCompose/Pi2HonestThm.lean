-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The tables' model is `Tables.lean`'s (`pi2Model`,
-- `pi2Tables`' claims, read backwards), the verifier's arithmetic `formal/RecStatement`'s (`checks_claims_iff_post2`),
-- the rounds' states `formal/RecPiop`'s (`Post2`, `qClaim_of_eval`).
import RecCompose.Pi2HonestMain

/-!
# π2's honest prover: the claims hold and the check passes

* **`pi2_honest_post2`**: off `BadCopy` and `BadT`, the honest stacks reach `RecPiop.Post2` (the identity and `P`'s
  definition are zero, `Σ_V h = 0`, `ξ` is the setup's value, `s = P(t)`, the fold values are `W`'s true ones);
* **`claims_of_model`**: the verifier's check and the model's values give π2's five claims on the stacks (the tables'
  layer, `pi2Tables`' `claims`, read backwards);
* **`pi2_honest`**: off `BadCopy` and `BadT`, `all ≠ 0` and `Pi2ClaimsHold` at the honest inputs.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Finset Polynomial

variable {D : RecDeployment} {C : Pi2Circuits D} (Fa : Pi2Facts D C) (hcol : Pi2SetupColumns D C)
  (roots : RecSetupRoots)

theorem length_foldValues (m r : ℕ) (T : Array K) (t : E) : (foldValues m r T t).length = 2 ^ r := by
  simp [foldValues]

/-- The coset is off `V_m`: `w_m` is nonzero there. -/
theorem sq_coset_ne {G : RecPiop.Circuit E} (hm : G.logN + 1 < 28) {p : ℕ} (hp : p < 2 ^ (G.logN + 1)) :
    QuotientSecurity.sq^[G.logN] (cosetPoint G.logN p) ≠ 0 := by
  rw [← RecPiop.Circuit.zV_eval_eq G UniComplete.Domain.basisE (by omega)]
  exact zV_coset_ne hm hp

/-- **The honest stacks reach the state after `ρ`**, off `BadCopy` and `BadT`. -/
theorem pi2_honest_post2 (w : ℕ → K) (scalars : List E) (α β γ t ρ : E)
    (hw : (C.G roots).Satisfies (Fa.pubOf roots scalars) (RecCircuit.emb w))
    (hbad : ¬ BadCopy (C.G roots) w (Fa.pubOf roots scalars) α β γ) (ht : ¬ BadT (C.G roots) w α β γ t) :
    RecPiop.Post2 (C.G roots) pi2Omega (pi2Model Fa roots hcol) (fun _ : Unit ↦ Fa.pubOf roots scalars) ()
      (honestW (C.G roots) w) [α, β, γ]
      (honestQ (C.G roots) (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ) [t]
      ((honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ).a ++
        [(honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ).ξ,
          (honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ).s]) [ρ] := by
  have hpts := RecPiop.Points.ofCantor UniComplete.Domain.basisE
  have hW := modelW_eq Fa hcol roots w
  have hσ := modelSigma_eq Fa hcol roots
  have hκ := modelKappa_eq Fa hcol roots
  have hH := modelH_eq Fa hcol roots (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ
  have hQ := modelQ_eq Fa hcol roots (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ
  have hP := modelP_eq Fa hcol roots (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ
  have hQP := modelQP_eq Fa hcol roots (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ
  have hphi_eq : (pi2Model Fa roots hcol).phi (Fa.pubOf roots scalars) γ =
      RecStatement.phiPoly (C.G roots) UniComplete.Domain.basisE (Fa.pubOf roots scalars) γ := rfl
  set G := C.G roots with hG
  set S := (Spec.of (D.circuitAt roots.pi1).circuit).core with hSdef
  set Mo := pi2Model Fa roots hcol with hMo
  set pub := Fa.pubOf roots scalars with hpub
  set cW := honestW G w with hcW
  set cQ := honestQ G S scalars w α β γ with hcQ
  set inp := honestInputs G (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ with hinp
  have hV : G.Valid := Fa.valid roots
  have hK : KCircuit G := kCircuit_toPiop _
  have h24 : G.logN = 24 := logN_G Fa roots
  have h4 : G.logW = 4 := Fa.logW roots
  have hm : G.logN + 1 < 28 := by omega
  have hpull : ∀ i < G.N, ¬ G.IsHole i → RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i ≠ 0 :=
    fun i hi hh h0 ↦ hbad (Or.inl ⟨i, hi, hh, h0⟩)
  have hpush : ∀ i < G.N, ¬ G.IsHole i → G.dPushV pi2Omega (RecCircuit.emb w) α β i ≠ 0 :=
    fun i hi hh h0 ↦ hbad (Or.inr ⟨i, hi, hh, h0⟩)
  have hHP : HonestPolys G w α β Mo.setup (Mo.wP cW) (Mo.hP cQ) (Mo.pP cQ) := by
    rw [hW, hH, hP]
    exact honestPolys G w α β Mo.setup hσ hκ
  have hwv : ∀ j < G.N, (Mo.wP cW).eval (pi2Omega j) = RecCircuit.emb w j :=
    fun j hj ↦ by rw [hW]; exact witnessPoly_omega G w (by omega) hj
  have hhv : ∀ i < G.N, (Mo.hP cQ).eval (pi2Omega i) = (hValues G w α β).getD i 0 :=
    fun i hi ↦ by rw [hH]; exact hNovel_omega G w α β (by omega) hi
  have hpv : ∀ i < G.N, (Mo.pP cQ).eval (pi2Omega i) = pvValue G w i :=
    fun i hi ↦ by rw [hP]; exact pushPolyH_omega G hK w hw (by omega) hi
  have hΦ : ∀ j < G.nP, (RecStatement.phiPoly G UniComplete.Domain.basisE pub γ (G.port j % G.W)).eval
      (pi2Omega (G.port j)) = G.pubFp γ pub j :=
    fun j hj ↦ RecStatement.phiPoly_eval_port hV (by omega) pub γ hj
  have hqp : Mo.qPP cQ = qpHonest (Mo.wP cW) (Mo.pP cQ) γ (G := G) := by
    rw [hQP]
    exact novP_qpNovel hK hV hm w α β γ Mo.setup _ _ _ hHP hwv hpv
  have hdef : G.defPoly pi2Omega (Mo.wP cW) (Mo.pP cQ) (Mo.qPP cQ) γ = 0 := by
    rw [hqp]
    exact defPoly_qpHonest hV (by omega) w hwv γ hpv
  have hq : Mo.qP cQ = numPoly Mo.setup (RecStatement.phiPoly G UniComplete.Domain.basisE pub γ) (Mo.wP cW)
      (Mo.hP cQ) (Mo.pP cQ) α β γ /ₘ G.zV pi2Omega := by
    rw [hQ]
    refine novP_qNovel hV hm w α β γ _ _ (RecStatement.natDegree_phiPoly_lt hV pub γ) hΦ (fun p hp k ↦ ?_)
      Mo.setup _ _ _ _ hHP hdef hw hwv hhv hpull hpush
    exact RecStatement.phiAt_eq (Fa.spec roots) hV scalars γ (sq_coset_ne hm hp) k
  have hid : G.idPoly pi2Omega Mo.setup (RecStatement.phiPoly G UniComplete.Domain.basisE pub γ) (Mo.wP cW)
      (Mo.hP cQ) (Mo.qP cQ) (Mo.pP cQ) α β γ = 0 := by
    rw [hq]
    exact idPoly_qHonest hV (by omega) _ w hwv α β γ hΦ hdef hw hhv hpull hpush
  have hla : inp.a.length = 2 ^ G.logW := length_foldValues _ _ _ _
  have hfv : ∀ k < 2 ^ G.logW, RecPiop.foldVals (inp.a ++ [inp.ξ, inp.s]) k = Mo.fold cW t k := by
    intro k hk
    unfold RecPiop.foldVals
    rw [List.getD_append _ _ _ _ (by rw [hla]; exact hk)]
    exact foldValues_eq Fa hcol roots w t hk
  have hxi : RecPiop.xiOf G.logW (inp.a ++ [inp.ξ, inp.s]) = Mo.setup.κP.eval t + β * Mo.setup.σP.eval t := by
    unfold RecPiop.xiOf
    rw [List.getD_append_right _ _ _ _ (by rw [hla]), hla, Nat.sub_self, List.getD_cons_zero]
    exact xiOf_eq Fa hcol roots β t
  have hsv : RecPiop.sOf G.logW (inp.a ++ [inp.ξ, inp.s]) = (Mo.pP cQ).eval t := by
    unfold RecPiop.sOf
    rw [List.getD_append_right _ _ _ _ (by rw [hla]; omega), hla, Nat.add_sub_cancel_left, List.getD_cons_succ,
      List.getD_cons_zero, hP]
    exact sOf_eq G w t
  have hcells : ∀ x < G.W, RecPiop.cellsOf G.logW pi2Omega (RecPiop.foldVals (inp.a ++ [inp.ξ, inp.s])) t x =
      (Mo.wP cW).eval (t + pi2Omega x) := fun x hx ↦ by
    rw [RecPiop.cellsOf_congr _ _ hfv t x]
    exact Mo.cells_fold _ t x hx
  -- the nonzero denominators, off `BadT`
  have hT : QuotientSecurity.sq^[G.logN + 1] t ≠ 0 := fun h ↦ ht (Or.inl h)
  have hcq : (G.zV pi2Omega).eval t ≠ 0 := by
    rw [RecPiop.Circuit.zV_eval_eq G UniComplete.Domain.basisE (by omega)]
    exact wm_ne_zero hT
  have hpullAt : RecPiop.dPullAt (RecPiop.cellsOf G.logW pi2Omega (RecPiop.foldVals (inp.a ++ [inp.ξ, inp.s])) t)
      α β t = (RecPiop.dPullP (witnessPoly G w) α β).eval t := by
    unfold RecPiop.dPullAt RecPiop.dPullP
    rw [hcells 0 (Nat.two_pow_pos _), pi2Omega_zero, add_zero, hW]
    simp
    try rfl
  have hch_eq : RecPiop.chAt (RecPiop.cellsOf G.logW pi2Omega (RecPiop.foldVals (inp.a ++ [inp.ξ, inp.s])) t)
      (RecPiop.xiOf G.logW (inp.a ++ [inp.ξ, inp.s])) (RecPiop.sOf G.logW (inp.a ++ [inp.ξ, inp.s])) α β t =
      (RecPiop.dPullP (witnessPoly G w) α β * dPushH G w α β).eval t := by
    unfold RecPiop.chAt RecPiop.dPushAt dPushH
    rw [hpullAt, hxi, hsv, hP, hκ, hσ, Polynomial.eval_mul]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  have hch : RecPiop.chAt (RecPiop.cellsOf G.logW pi2Omega (RecPiop.foldVals (inp.a ++ [inp.ξ, inp.s])) t)
      (RecPiop.xiOf G.logW (inp.a ++ [inp.ξ, inp.s])) (RecPiop.sOf G.logW (inp.a ++ [inp.ξ, inp.s])) α β t ≠ 0 := by
    rw [hch_eq]
    exact fun h ↦ ht (Or.inr (Or.inl h))
  have hy : RecPiop.chAt (RecPiop.cellsOf G.logW pi2Omega (RecPiop.foldVals (inp.a ++ [inp.ξ, inp.s])) t)
      (RecPiop.xiOf G.logW (inp.a ++ [inp.ξ, inp.s])) (RecPiop.sOf G.logW (inp.a ++ [inp.ξ, inp.s])) α β t +
        (G.zV pi2Omega).eval t ≠ 0 := by
    rw [hch_eq, ← Polynomial.eval_add]
    exact fun h ↦ ht (Or.inr (Or.inr (Or.inl h)))
  unfold RecPiop.Post2 RecPiop.SumOK RecPiop.abc
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  refine ⟨?_, hxi, ?_, ?_⟩
  · rw [Finset.sum_congr rfl fun i hi ↦ hhv i (mem_range.mp hi)]
    exact sum_hValues hV w hw α β
  · rw [hphi_eq]
    exact RecPiop.Circuit.qClaim_of_eval hV hpts Mo.setup _ Mo.idC (Mo.wP cW) (Mo.hP cQ) (Mo.qP cQ) (Mo.pP cQ)
      (Mo.qPP cQ) α β γ t _ _ ρ hcells hxi hsv (by rw [hid, Polynomial.eval_zero])
      (by rw [hdef, Polynomial.eval_zero]) hcq hch hy
  · unfold RecPiop.foldAt
    exact Finset.sum_congr rfl fun k hk ↦ by rw [hfv k (mem_range.mp hk)]

/-- **The verifier's check and the model's values give π2's five claims** on the stacks (`pi2Tables`' `claims`, read
backwards). -/
theorem claims_of_model (inp : Inputs E) (cW cQ : Stk)
    (hall : ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).all ≠ 0)
    (hid : idEq ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp)
      (c3Of (Spec.of (D.circuitAt roots.pi1).circuit).core)
      ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).rhoQ (((pi2Model Fa roots hcol).hP cQ).eval inp.t)
      (((pi2Model Fa roots hcol).qP cQ).eval inp.t) (((pi2Model Fa roots hcol).pP cQ).eval inp.t)
      (((pi2Model Fa roots hcol).qPP cQ).eval inp.t) (QuotientSecurity.sq^[(C.G roots).logN] inp.t) inp.s)
    (hpe : pushEq ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp) inp.ρ
      (((pi2Model Fa roots hcol).pP cQ).eval inp.t) (((pi2Model Fa roots hcol).qPP cQ).eval inp.t)
      (QuotientSecurity.sq^[(C.G roots).logN] inp.t) inp.s)
    (hsum : ∑ i ∈ range (C.G roots).N, ((pi2Model Fa roots hcol).hP cQ).eval (pi2Omega i) = 0)
    (hξ : inp.ξ = (pi2Model Fa roots hcol).setup.κP.eval inp.t + inp.β * (pi2Model Fa roots hcol).setup.σP.eval inp.t)
    (hf : ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).fold =
      RecPiop.foldAt (C.G roots).logW ((pi2Model Fa roots hcol).fold cW inp.t) inp.ρ) :
    Pi2ClaimsHold D roots inp cW cQ := by
  have hS := Fa.spec roots
  have hm := view_logN Fa roots
  have hm24 := view_logN24 Fa roots
  have hr4 := view_logRow4 Fa roots
  set m := (D.circuitAt roots.pi1).circuit.logN with hmdef
  set S := (Spec.of (D.circuitAt roots.pi1).circuit).core with hSdef
  have hSm : S.logN = m := spec_core_logN _
  have hSr : S.logRow = (D.circuitAt roots.pi1).circuit.logRow := spec_core_logRow _
  have hm20 : 20 ≤ m := by omega
  have hqv : (stackVars m).2.1 = m + 4 := by simp only [stackVars, hm20, ite_true]; omega
  have hT : QuotientSecurity.sq^[(C.G roots).logN + 1] inp.t ≠ 0 := by
    have h := hall
    rw [run_all hS inp] at h
    exact right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  rw [← hm] at hT
  have hw : ∀ l < m + 1, 1 + QuotientSecurity.sq^[l] inp.t ≠ 0 := fun l hl ↦ one_add_digit_ne_zero hT hl
  have huw : ∀ l < m + 1, (S.run inp).uList.getD l 0 =
      QuotientSecurity.sq^[l] inp.t / (1 + QuotientSecurity.sq^[l] inp.t) := fun l hl ↦
    run_u hS inp hall (by rw [← hm]; exact hl)
  have hu : (S.run inp).uList.length = m + 1 := by rw [run_uList_length, hSm]
  have hu' : ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).uList.length = m + 1 := hu
  have hDne : ∏ l ∈ range (m + 1), (1 + QuotientSecurity.sq^[l] inp.t)⁻¹ ≠ 0 :=
    prod_inv_ne_zero_gen (F := E) (n := m + 1) (f := fun l ↦ 1 + QuotientSecurity.sq^[l] inp.t) hw
  have hv : (layoutsOf m).2.1.vars = m + 4 := rfl
  have hqval := run_quotientValue hS inp hall
  have hpval := run_pushesValue hS inp hall
  rw [← hm] at hqval hpval
  have hscale : S.scale = extension.2 := spec_core_scale _
  have hc3 : c3Of S = extension.1.1 * extension.1.2 * extension.2⁻¹ := by
    unfold c3Of
    rw [spec_core_y0, spec_core_y1, extension_L0]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `W`'s claim
    unfold ClaimOn
    have hv1 : (layoutsOf m).1.vars = m := rfl
    have hwv : (stackVars m).1 = m := by simp only [stackVars, hm20, ite_true]; omega
    rw [hv1, run_witnessPoint, hSm, hSr, hwv, padded_eq (by simp [digitsList]; omega),
      claim_wFold (by omega) _ inp.t inp.ρ, hf]
    have e : (C.G roots).logW = (D.circuitAt roots.pi1).circuit.logRow := (view_logRow Fa roots).symm
    exact congrArg (fun r ↦ RecPiop.foldAt r (wFold m (D.circuitAt roots.pi1).circuit.logRow
      (wTab D roots cW) inp.t) inp.ρ) e.symm
  · -- `Q`'s identity claim
    unfold ClaimOn
    dsimp only
    rw [hv, run_quotientPoint, hSm, hqv, padded_eq (by simp [hu']), spec_core_y0, spec_core_y1]
    have hc := claim_quotient (qZero hm20 cQ) hu hw huw (S.run inp).rhoQ
    unfold qTable at hc
    rw [hc, hqval, hscale]
    unfold idEq at hid
    have hid' := hid
    change _ = (1 + (S.run inp).rhoQ) * (hPoly (qTable m cQ) m).eval inp.t +
        (S.run inp).rhoQ * (qPoly (qTable m cQ) m).eval inp.t + c3Of S * ((1 + (S.run inp).rhoQ) *
          QuotientSecurity.sq^[(C.G roots).logN] inp.t * (pPoly (qTable m cQ) m).eval inp.t +
          (S.run inp).rhoQ * (qpPoly (qTable m cQ) m).eval inp.t) at hid'
    unfold hPoly qPoly pPoly qpPoly qTable at hid'
    rw [novP_eval_sq, novP_eval_sq, novP_eval_sq, novP_eval_sq, ← hm] at hid'
    rw [hid', hc3]
    have hs := extension_scale_ne_zero
    field_simp
  · -- `Q`'s pushes' claim
    unfold ClaimOn
    dsimp only
    rw [hv, run_pushesPoint, hSm, hqv, padded_eq (by simp [hu'])]
    have hc := claim_pushes (qZero hm20 cQ) hu hw huw inp.ρ
    unfold qTable at hc
    rw [hc, hpval, hscale, spec_core_y0, spec_core_y1, extension_L0, mul_inv_cancel₀ extension_scale_ne_zero,
      one_mul]
    unfold pushEq at hpe
    have hpe' := hpe
    change _ = (1 + inp.ρ) * QuotientSecurity.sq^[(C.G roots).logN] inp.t * (pPoly (qTable m cQ) m).eval inp.t +
        inp.ρ * (qpPoly (qTable m cQ) m).eval inp.t at hpe'
    unfold pPoly qpPoly qTable at hpe'
    rw [novP_eval_sq, novP_eval_sq, ← hm] at hpe'
    rw [hpe']
    ring
  · -- `Q`'s sum claim
    unfold ClaimOn
    dsimp only
    rw [hv, run_sumPoint, run_sumValue, spec_core_y0, spec_core_y1, hSm, hqv, padded_eq (by simp)]
    have hc := claim_sum (qZero hm20 cQ)
    unfold qTable at hc
    rw [hc]
    have h2 : qCoef ((layoutsOf m).2.1.readEntry cQ) m 0 (2 ^ m - 1) = 0 := by
      have h := hsum
      change ∑ i ∈ range (C.G roots).N, (hPoly (qTable m cQ) m).eval (pi2Omega i) = 0 at h
      rw [← pow_view_N Fa roots] at h
      unfold hPoly at h
      rw [sum_novP_omega (by omega)] at h
      exact h
    rw [h2, mul_zero]
  · -- the setup's claim
    unfold ClaimOn
    have hv2 : (layoutsOf m).2.2.vars = m + 1 := rfl
    have hsv : (stackVars m).2.2 = m + 1 := by simp only [stackVars, hm20, ite_true]; omega
    rw [hv2, run_setupPoint, hSm, hsv, padded_eq (by simp [digitsList]; omega), claim_setup]
    have hlane : max (m + 1) 24 - PcsQuotient.laneFold ≤ m := by
      simp only [PcsQuotient.laneFold]; omega
    have hT0 : ∀ k < 2 ^ m, (layoutsOf m).2.2.readEntry (fun j ↦ (D.circuitAt roots.pi1).setupStack.getD j 0) k =
        (kappaB D roots).getD k 0 := fun k hk ↦ by
      rw [setupLayout_eq hm20, readEntry_ofChunks_two hlane _ (by rw [pow_succ]; omega)]
      exact (setupStack_getD _ hk).1
    have hT1 : ∀ k < 2 ^ m, (layoutsOf m).2.2.readEntry (fun j ↦ (D.circuitAt roots.pi1).setupStack.getD j 0) k +
        (layoutsOf m).2.2.readEntry (fun j ↦ (D.circuitAt roots.pi1).setupStack.getD j 0) (k + 2 ^ m) =
        (sigmaB D roots).getD k 0 := fun k hk ↦ by
      rw [hT0 k hk, setupLayout_eq hm20, readEntry_ofChunks_two hlane _ (by rw [pow_succ]; omega),
        (setupStack_getD _ hk).2]
      show (kappaB D roots).getD k 0 + ((kappaB D roots).getD k 0 + (sigmaB D roots).getD k 0) = _
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [wPoly_congr hT0, wPoly_congr hT1]
    exact hξ.symm

include hcol in
/-- **π2's honest prover: the verifier's check passes and its five claims hold**, off the bad challenges. -/
theorem pi2_honest (w : ℕ → K) (scalars : List E) (α β γ t ρ : E)
    (hw : (C.G roots).Satisfies (Fa.pubOf roots scalars) (RecCircuit.emb w))
    (hbad : ¬ BadCopy (C.G roots) w (Fa.pubOf roots scalars) α β γ) (ht : ¬ BadT (C.G roots) w α β γ t) :
    ((Spec.of (D.circuitAt roots.pi1).circuit).core.run
        (honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ)).all ≠ 0 ∧
      Pi2ClaimsHold D roots (honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ)
        (honestW (C.G roots) w) (honestQ (C.G roots) (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ) := by
  have hpost := pi2_honest_post2 Fa hcol roots w scalars α β γ t ρ hw hbad ht
  have hW := modelW_eq Fa hcol roots w
  have hσ := modelSigma_eq Fa hcol roots
  have hκ := modelKappa_eq Fa hcol roots
  have hV := Fa.valid roots
  have hpts := RecPiop.Points.ofCantor UniComplete.Domain.basisE
  set inp := honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ with hinp
  have ha : inp.a.length = 2 ^ (C.G roots).logW := length_foldValues _ _ _ _
  have hT : QuotientSecurity.sq^[(C.G roots).logN + 1] inp.t ≠ 0 := fun h ↦ ht (Or.inl h)
  have hcells : ∀ x < (C.G roots).W, RecPiop.cellsOf (C.G roots).logW pi2Omega (fun k ↦ inp.a.getD k 0) inp.t x =
      ((pi2Model Fa roots hcol).wP (honestW (C.G roots) w)).eval (inp.t + pi2Omega x) := fun x hx ↦ by
    rw [RecPiop.cellsOf_congr _ _ (a := fun k ↦ inp.a.getD k 0)
      (a' := (pi2Model Fa roots hcol).fold (honestW (C.G roots) w) t)
      (fun k hk ↦ foldValues_eq Fa hcol roots w t hk) inp.t x]
    exact (pi2Model Fa roots hcol).cells_fold _ t x hx
  have hξ := xiOf_eq Fa hcol roots β t
  have hpvt : inp.α + (C.G roots).pvAt pi2Omega (RecPiop.cellsOf (C.G roots).logW pi2Omega
      (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t + inp.ξ ≠ 0 := by
    intro h0
    apply ht
    right; right; right
    rw [← hW, ← hκ, ← hσ]
    have e := RecPiop.Circuit.pvAt_eq hV hpts _ inp.γ inp.t hcells
    change inp.α + (C.G roots).pvAt (Heap.omega UniComplete.Domain.basisE) _ inp.γ inp.t + inp.ξ = 0 at h0
    rw [e] at h0
    change α + Polynomial.eval t ((C.G roots).pushPolyV pi2Omega
      ((pi2Model Fa roots hcol).wP (honestW (C.G roots) w)) γ) +
        xiOf (C.G roots).logN (D.circuitAt roots.pi1).setupStack β t = 0 at h0
    rw [hξ] at h0
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [← h0]
    ring
  obtain ⟨hall, hid, hpe, hsum, hξ', hf⟩ := (checks_claims_iff_post2 (Fa.spec roots) hV inp (pi2Model Fa roots hcol)
    (fun _ _ ↦ rfl) rfl (fun _ : Unit ↦ Fa.pubOf roots scalars) () rfl (honestW (C.G roots) w)
    (honestQ (C.G roots) (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ) ha).mpr ⟨hT, hpvt, hpost⟩
  exact ⟨hall, claims_of_model Fa hcol roots inp _ _ hall hid hpe hsum hξ' hf⟩

end RecCompose

/-- info: 'RecCompose.pi2_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2_honest
