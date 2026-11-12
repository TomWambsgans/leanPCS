-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The tables' model is `Tables.lean`'s (`pi2Model`,
-- `pi2Tables`' claims, read backwards), the verifier's arithmetic `formal/RecStatement`'s (`checks_claims_iff_post2`),
-- the rounds' states `formal/RecPiop`'s (`Post2`, `qClaim_of_eval`).
import RecCompose.Pi2HonestMain

/-!
# π2's honest prover: the claims hold and the check passes (π2v4)

* **`pi2_honest_post2`**: off `BadCopy`, `BadT` and `BadRho`, the honest stacks reach `RecPiop.Post2`: `ξ` is the setup's
  value, `Q`'s two claims hold (`RecPiop.Circuit.qClaim_of_eval`: `I = D² H + x Z_V D A + x² Z_V³ G + x D R` is zero at
  `H = x h`, `A = q`, `G = 0`, `iPoly_honest`, `H = x h` because `Σ_V h = 0`, `hxPoly_eq`; `P`'s definition is zero; `S = 0`;
  `Z_V(t)`, `c_h`, `Y_1`, `Y_2`, `Y_3` nonzero), the fold values are `W`'s true ones;
* **`claims_of_model`**: the verifier's check and the model's values give π2's four claims on the stacks (the tables'
  layer, `pi2Tables`' `claims`, read backwards);
* **`pi2_honest`**: off `BadCopy`, `BadT` and `BadRho`, `all ≠ 0` and `Pi2ClaimsHold` at the honest inputs.
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

/-- **The honest stacks reach the state after `ρ`**, off `BadCopy`, `BadT` and `BadRho`. -/
theorem pi2_honest_post2 (w : ℕ → K) (scalars : List E) (α β γ t ρ : E)
    (hw : (C.G roots).Satisfies (Fa.pubOf roots scalars) (RecCircuit.emb w))
    (hbad : ¬ BadCopy (C.G roots) w (Fa.pubOf roots scalars) α β γ) (ht : ¬ BadT (C.G roots) w α β γ t)
    (hρ : ¬ BadRho (C.G roots) t ρ) :
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
  have hG0 := modelG_eq Fa hcol roots (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ
  have hQ := modelQ_eq Fa hcol roots (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ
  have hP := modelP_eq Fa hcol roots (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ
  have hQP := modelQP_eq Fa hcol roots (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ
  have hS0 := modelS_eq Fa hcol roots (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ
  have hphi_eq : (pi2Model Fa roots hcol).phi (Fa.pubOf roots scalars) γ =
      RecStatement.phiPoly (C.G roots) UniComplete.Domain.basisE (Fa.pubOf roots scalars) γ := rfl
  set G := C.G roots with hG
  set S := (Spec.of (D.circuitAt roots.pi1).circuit).core with hSdef
  set Mo := pi2Model Fa roots hcol with hMo
  set pub := Fa.pubOf roots scalars with hpub
  set cW := honestW G w with hcW
  set cQ := honestQ G S scalars w α β γ with hcQ
  set inp := honestInputs G (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ with hinp
  set hnov := UniKeccakComplete.AlgC.novP G.logN fun j ↦ (hNovel G w α β).getD j 0 with hnovdef
  have hV : G.Valid := Fa.valid roots
  have hK : KCircuit G := kCircuit_toPiop _
  have h24 : G.logN = 24 := logN_G Fa roots
  have hm : G.logN + 1 < 28 := by omega
  have hpull : ∀ i < G.N, ¬ G.IsHole i → RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i ≠ 0 :=
    fun i hi hh h0 ↦ hbad (Or.inl ⟨i, hi, hh, h0⟩)
  have hpush : ∀ i < G.N, ¬ G.IsHole i → G.dPushV pi2Omega (RecCircuit.emb w) α β i ≠ 0 :=
    fun i hi hh h0 ↦ hbad (Or.inr ⟨i, hi, hh, h0⟩)
  have hHP : HonestPolys G w α β Mo.setup (Mo.wP cW) hnov (Mo.pP cQ) := by
    rw [hW, hP]
    exact honestPolys G w α β Mo.setup hσ hκ
  have hwv : ∀ j < G.N, (Mo.wP cW).eval (pi2Omega j) = RecCircuit.emb w j :=
    fun j hj ↦ by rw [hW]; exact witnessPoly_omega G w (by omega) hj
  have hhv : ∀ i < G.N, hnov.eval (pi2Omega i) = (hValues G w α β).getD i 0 :=
    fun i hi ↦ hNovel_omega G w α β (by omega) hi
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
      hnov (Mo.pP cQ) α β γ /ₘ G.zV pi2Omega := by
    rw [hQ]
    refine novP_qNovel hV hm w α β γ _ _ (RecStatement.natDegree_phiPoly_lt hV pub γ) hΦ (fun p hp k ↦ ?_)
      Mo.setup _ _ _ _ hHP hdef hw hwv hhv hpull hpush
    exact RecStatement.phiAt_eq (Fa.spec roots) hV scalars γ (sq_coset_ne hm hp) k
  have hid : G.idPoly pi2Omega Mo.setup (RecStatement.phiPoly G UniComplete.Domain.basisE pub γ) (Mo.wP cW)
      hnov (Mo.qP cQ) (Mo.pP cQ) α β γ = 0 := by
    rw [hq]
    exact idPoly_qHonest hV (by omega) _ w hwv α β γ hΦ hdef hw hhv hpull hpush
  have hHx : Mo.hP cQ = X * hnov := by
    rw [hH]
    exact hxPoly_eq G w α β (by omega) (sum_hValues hV w hw α β)
  have hI : G.iPoly pi2Omega Mo.setup (RecStatement.phiPoly G UniComplete.Domain.basisE pub γ) (Mo.wP cW)
      (Mo.hP cQ) (Mo.qP cQ) (Mo.gP cQ) (Mo.pP cQ) α β γ = 0 := by
    rw [hHx, hG0]
    exact iPoly_honest G Mo.setup _ _ _ _ _ α β γ hid
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
  -- the nonzero values, off `BadT` and `BadRho`
  have hT : QuotientSecurity.sq^[G.logN] t ≠ 0 := fun h ↦ ht (Or.inl h)
  have hzt : (G.zV pi2Omega).eval t = QuotientSecurity.sq^[G.logN] t :=
    RecPiop.Circuit.zV_eval_eq G UniComplete.Domain.basisE (by omega) t
  have hcq : (G.zV pi2Omega).eval t ≠ 0 := by rw [hzt]; exact hT
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
  have hy1 : RecPiop.chAt (RecPiop.cellsOf G.logW pi2Omega (RecPiop.foldVals (inp.a ++ [inp.ξ, inp.s])) t)
      (RecPiop.xiOf G.logW (inp.a ++ [inp.ξ, inp.s])) (RecPiop.sOf G.logW (inp.a ++ [inp.ξ, inp.s])) α β t +
        t * (G.zV pi2Omega).eval t ≠ 0 := by
    rw [hch_eq]
    intro h
    apply ht
    refine Or.inr (Or.inr (Or.inl ?_))
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at h ⊢
    linear_combination h
  have hy2 : RecPiop.chAt (RecPiop.cellsOf G.logW pi2Omega (RecPiop.foldVals (inp.a ++ [inp.ξ, inp.s])) t)
      (RecPiop.xiOf G.logW (inp.a ++ [inp.ξ, inp.s])) (RecPiop.sOf G.logW (inp.a ++ [inp.ξ, inp.s])) α β t +
        t * (G.zV pi2Omega).eval t * (G.zV pi2Omega).eval t ≠ 0 := by
    rw [hch_eq]
    intro h
    apply ht
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow] at h ⊢
    linear_combination h
  unfold RecPiop.Post2 RecPiop.abc
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  refine ⟨hxi, ?_, ?_⟩
  · rw [hphi_eq]
    exact RecPiop.Circuit.qClaim_of_eval hV hpts Mo.setup _ Mo.idC (Mo.wP cW) (Mo.hP cQ) (Mo.qP cQ) (Mo.gP cQ)
      (Mo.pP cQ) (Mo.qPP cQ) (Mo.sP cQ) α β γ t _ _ ρ hcells hxi hsv (by rw [hI, Polynomial.eval_zero])
      (by rw [hdef, Polynomial.eval_zero]) (by rw [hS0, Polynomial.eval_zero]) hcq hch hy1 hy2 hρ
  · unfold RecPiop.foldAt
    exact Finset.sum_congr rfl fun k hk ↦ by rw [hfv k (mem_range.mp hk)]

/-- **The verifier's check and the model's values give π2's four claims** on the stacks (`pi2Tables`' `claims`, read
backwards). -/
theorem claims_of_model (inp : Inputs E) (cW cQ : Stk)
    (hall : ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).all ≠ 0)
    (hid : idEq ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp) (Spec.of (D.circuitAt roots.pi1).circuit).core.scale
      (Spec.of (D.circuitAt roots.pi1).circuit).core.yCube inp.t (QuotientSecurity.sq^[(C.G roots).logN] inp.t)
      ((hPoly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t) ((q0Poly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t)
      ((q1Poly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t) ((gPoly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t)
      ((pPoly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t) ((qp0Poly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t)
      ((qp1Poly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t) ((sPoly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t))
    (hpe : pushEq ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp) inp.t
      (QuotientSecurity.sq^[(C.G roots).logN] inp.t) inp.ρ
      ((pPoly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t) ((qp0Poly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t)
      ((qp1Poly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t) ((sPoly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t))
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
  have hT : QuotientSecurity.sq^[(C.G roots).logN] inp.t ≠ 0 :=
    ((all_ne_zero_iff hS (Fa.valid roots) inp).mp hall).1
  rw [← hm] at hT
  have hw : ∀ l < m, 1 + QuotientSecurity.sq^[l] inp.t ≠ 0 := fun l hl ↦ one_add_digit_ne_zero hT hl
  have huw : ∀ l < m, (S.run inp).uList.getD l 0 =
      QuotientSecurity.sq^[l] inp.t / (1 + QuotientSecurity.sq^[l] inp.t) := fun l hl ↦
    run_u hS inp hall (by rw [← hm]; exact hl)
  have hu : (S.run inp).uList.length = m := by rw [run_uList_length, hSm]
  have hu' : ((Spec.of (D.circuitAt roots.pi1).circuit).core.run inp).uList.length = m := hu
  have hscale : inp.t * (QuotientSecurity.sq^[m] inp.t)⁻¹ =
      ∏ l ∈ range m, (1 + QuotientSecurity.sq^[l] inp.t)⁻¹ := digitsScale_eq hT
  have hsc : S.scale = extension.2 := spec_core_scale _
  have hyc : S.yCube = yCubeE := spec_core_yCube _
  have hwm : QuotientSecurity.sq^[(C.G roots).logN] inp.t = QuotientSecurity.sq^[m] inp.t := by rw [hm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `W`'s claim
    unfold ClaimOn
    have hwv : (stackVars m).1 = m := by simp only [stackVars, hm20, ite_true]; omega
    rw [run_witnessPoint, hSm, hSr, hwv, padded_eq (by simp [digitsList]; omega),
      mleStk_eq _ (by simp [digitsList]; omega), claim_wFold (by omega) _ inp.t inp.ρ, hf]
    have e : (C.G roots).logW = (D.circuitAt roots.pi1).circuit.logRow := (view_logRow Fa roots).symm
    exact congrArg (fun r ↦ RecPiop.foldAt r (wFold m (D.circuitAt roots.pi1).circuit.logRow
      (wTab D roots cW) inp.t) inp.ρ) e.symm
  · -- `Q`'s identity claim
    unfold ClaimOn
    dsimp only
    rw [run_quotientPoint, hSm, hqv, padded_eq (by simp [hu']), spec_core_y0, spec_core_y1,
      mleStk_eq _ (by simp [hu']), claim_quotient (T := cQ) hu hw huw]
    unfold idEq at hid
    rw [hid, hwm, hscale, hsc, hyc]
    unfold hPoly q0Poly q1Poly gPoly pPoly qp0Poly qp1Poly sPoly
    rw [limb_eval, limb_eval, limb_eval, limb_eval, slot_eval, slot_eval, slot_eval, slot_eval]
    ring
  · -- `Q`'s pushes' claim
    unfold ClaimOn
    dsimp only
    rw [run_pushesPoint, hSm, hqv, padded_eq (by simp [hu']), mleStk_eq _ (by simp [hu']),
      claim_pushes (T := cQ) hu hw huw]
    unfold pushEq at hpe
    rw [hpe, hwm, hscale]
    unfold pPoly qp0Poly qp1Poly sPoly
    rw [slot_eval, slot_eval, slot_eval, slot_eval]
  · -- the setup's claim
    unfold ClaimOn
    have hsv : (stackVars m).2.2 = m + 1 := by simp only [stackVars, hm20, ite_true]; omega
    rw [run_setupPoint, hSm, hsv, padded_eq (by simp [digitsList]),
      mleStk_eq _ (by simp [digitsList]), claim_setup]
    have hT0 : ∀ k < 2 ^ m, (D.circuitAt roots.pi1).setupStack.getD k 0 = (kappaB D roots).getD k 0 :=
      fun k hk ↦ (setupStack_getD _ hk).1
    have hT1 : ∀ k < 2 ^ m, (D.circuitAt roots.pi1).setupStack.getD k 0 +
        (D.circuitAt roots.pi1).setupStack.getD (k + 2 ^ m) 0 = (sigmaB D roots).getD k 0 := fun k hk ↦ by
      rw [hT0 k hk, (setupStack_getD _ hk).2]
      show (kappaB D roots).getD k 0 + ((kappaB D roots).getD k 0 + (sigmaB D roots).getD k 0) = _
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [wPoly_congr hT0, wPoly_congr hT1]
    exact hξ.symm

include hcol in
/-- **π2's honest prover: the verifier's check passes and its four claims hold**, off the bad challenges. -/
theorem pi2_honest (w : ℕ → K) (scalars : List E) (α β γ t ρ : E)
    (hw : (C.G roots).Satisfies (Fa.pubOf roots scalars) (RecCircuit.emb w))
    (hbad : ¬ BadCopy (C.G roots) w (Fa.pubOf roots scalars) α β γ) (ht : ¬ BadT (C.G roots) w α β γ t)
    (hρ : ¬ BadRho (C.G roots) t ρ) :
    ((Spec.of (D.circuitAt roots.pi1).circuit).core.run
        (honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ)).all ≠ 0 ∧
      Pi2ClaimsHold D roots (honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ)
        (honestW (C.G roots) w) (honestQ (C.G roots) (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ) := by
  have hpost := pi2_honest_post2 Fa hcol roots w scalars α β γ t ρ hw hbad ht hρ
  have hW := modelW_eq Fa hcol roots w
  have hσ := modelSigma_eq Fa hcol roots
  have hκ := modelKappa_eq Fa hcol roots
  have hV := Fa.valid roots
  have hpts := RecPiop.Points.ofCantor UniComplete.Domain.basisE
  have hm := view_logN Fa roots
  set inp := honestInputs (C.G roots) (D.circuitAt roots.pi1).setupStack w scalars α β γ t ρ with hinp
  set cQ := honestQ (C.G roots) (Spec.of (D.circuitAt roots.pi1).circuit).core scalars w α β γ with hcQ
  have ha : inp.a.length = 2 ^ (C.G roots).logW := length_foldValues _ _ _ _
  have hT : QuotientSecurity.sq^[(C.G roots).logN] inp.t ≠ 0 := fun h ↦ ht (Or.inl h)
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
    right; right; right; right
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
  have hq : ((pi2Model Fa roots hcol).qP cQ).eval inp.t =
      (q0Poly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t +
        QuotientSecurity.sq^[(C.G roots).logN] inp.t * (q1Poly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t := by
    show (qPoly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t = _
    rw [← hm]
    exact twoDigits_eval _ _ _ inp.t
  have hqp : ((pi2Model Fa roots hcol).qPP cQ).eval inp.t =
      (qp0Poly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t +
        QuotientSecurity.sq^[(C.G roots).logN] inp.t * (qp1Poly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t := by
    show (qpPoly cQ (D.circuitAt roots.pi1).circuit.logN).eval inp.t = _
    rw [← hm]
    exact twoDigits_eval _ _ _ inp.t
  obtain ⟨hall, hid, hpe, hξ', hf⟩ := (checks_claims_iff_post2 (Fa.spec roots) hV inp extension_scale_ne_zero
    (pi2Model Fa roots hcol) (fun _ _ ↦ rfl) rfl (fun _ : Unit ↦ Fa.pubOf roots scalars) () rfl (honestW (C.G roots) w)
    cQ ha _ _ _ _ hq hqp).mpr ⟨hT, hpvt, hpost⟩
  exact ⟨hall, claims_of_model Fa hcol roots inp _ _ hall hid hpe hξ' hf⟩

end RecCompose

/-- info: 'RecCompose.pi2_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2_honest
