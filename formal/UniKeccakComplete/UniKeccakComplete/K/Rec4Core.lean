-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's honest proof is accepted: `Rec3Core.lean`'s
-- `accepts_of_trace3`, `front_challenges3`, `coreAccepts3_reference` and `Rec3CoreBatch.lean`'s `batchHolds3_front`
-- for π1-rec4's verifier (`KDeployment.verifierWith4H`) and prover (`Rec4Prover.lean`).
import UniKeccakComplete.K.Rec4SyncVerifier
import UniKeccakComplete.K.Rec4CoreRun
import UniKeccakComplete.K.Rec3Core

/-!
# π1-rec4's honest proof is accepted (`CoreAccepts4`)

* **`verifyWithKH4_of_calls`**: π1-rec4's whole verifier accepts when its run accepts with three point claims on
  `C1`, `C2`, the setup, in order, and their three openings accept (`VerifierAccept.lean`'s, for `verifyWithKH4`).
* **`batchHolds4_front`**: at the reference shape, for an honest trace, the prover's state when the batch starts
  (`frontOf4`) satisfies `BatchHolds` unless `BadFp` (at `α, β`) or `BadT` (at Flock's point and `t`): π1-rec3's
  `batchHolds3_of` with Flock's output `flockOut4 fl map` (its ring identity at the late map,
  `FlockP.flockRingSum4`; its point's length, `FlockP.flock4_point_length_trace`).
* **`accepts_of_trace4`**: a proof `proveRec4With` returns is accepted by `KDeployment.verifierWith4H` (the run on the
  prover's stream, `runWithKH4_syncs4`, `runWithKH4_accepts4`; the claims' values, `streamValues4`; WHIR's three
  honest openings at `27, 26, 23` variables, `Core.pcsOpenKH_of`).
* **`front_challenges4`**: the staged challenges (`proverChallenges4`, `proverTChallenge4`) are the prover's front
  state's.
* **`coreAccepts4_reference`**: `CoreAccepts4 D` at the reference shape.
-/

open UniStatement UniKeccak LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace UniKeccakComplete.Rec4

open UniComplete UniKeccakComplete.Rec3

open ProverRun
open UniKeccakSound (keccakRefShape)
open UniKeccakComplete.Core (claims_shape commitReal_tree commitReal_halves rootRead_rootHalves pcsOpenKH_of
  setupRoots_eq)
open UniKeccakComplete.Prob (tInput firstInput prefixStream oodOf)

-- The heavy definitions stay folded in the defeq checks against the prover's state (`frontOf4`).
attribute [local irreducible] flockProve4 atTOf c2DataOf c1Stack setupStackOf

/-! ## When the whole verifier accepts -/

/-- **π1-rec4's verifier accepts** when its run does, with the three point claims and no matrices' claim, and the
three openings accept. -/
theorem verifyWithKH4_of_calls (H : List UInt8 → Digest) (W : List UInt8 → RateB) (F : KeccakState → KeccakState)
    (shape : UniStatement.Shape) (v : KeccakVariant) (iv : List UInt8) (roots : SetupRootsK)
    (input : Vector UInt8 32) (π : KeccakProof) (o : UniStatement.Outcome) (r : Reduced) (p1 p2 p3 : List E)
    (v1 v2 v3 : E)
    (hrun : runWithKH4 (m := Id) (fun b ↦ pure (H b)) (fun b ↦ pure (W b)) shape iv input.toList π.stream v .point = o)
    (hacc : o.accepts = true) (hres : o.result = .ok r)
    (hop : r.openings = [(.c1, .point p1 v1 none), (.c2, .point p2 v2 none), (.setup, .point p3 v3 none)])
    (hmat : r.matrices = none)
    (h1 : pcsOpenKH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (stackVarsK shape .c1) (rootOf r.roots.1) r.oods.1 p1 v1 π.c1 = true)
    (h2 : pcsOpenKH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (stackVarsK shape .c2) (rootOf r.roots.2) r.oods.2 p2 v2 π.c2 = true)
    (h3 : pcsOpenKH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s))
      (stackVarsK shape .setup) roots.f roots.fOod p3 v3 π.setup = true) :
    verifyWithKH4 (m := Id) (fun b ↦ pure (H b)) (fun b ↦ pure (W b)) (fun s ↦ pure (F s)) shape v iv roots input π =
      true := by
  unfold verifyWithKH4
  simp only [hrun]
  simp only [bind, pure] at h1 h2 h3 ⊢
  simp only [hacc, hres, hop, hmat, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp [commitments, commitOfK, KeccakProof.openingOf, h1, h2, h3]
  rfl

/-! ## The honest batch's hypothesis at the prover's state -/

theorem wideXs_getD (W : List UInt8 → RateB) (count : ℕ) (w : Wr) {i : ℕ} (hi : i < count) :
    (wideXs W count w).getD i 0 = challengeAt (W (tInput w)).toList i := by
  simp [wideXs, List.getD_eq_getElem?_getD, hi]

theorem wideXs_length (W : List UInt8 → RateB) (count : ℕ) (w : Wr) : (wideXs W count w).length = count := by
  simp [wideXs]

/-- **The honest batch's hypothesis at π1-rec4's prover's state**, unless `BadFp` or `BadT`. -/
theorem batchHolds4_front (H : List UInt8 → Digest) (W : List UInt8 → RateB)
    (commit : Commitment → ℕ → Array K → Id Committed) (tr : Trace) (hon : TraceHonest tr)
    (href : tr.shape = keccakRefShape) (seed : Digest)
    (hbad : ¬ BadFp tr (frontOf4 H W commit tr (Wr.start seed)).1.alphas
      (frontOf4 H W commit tr (Wr.start seed)).1.beta)
    (hbadT : ∀ out, (frontOf4 H W commit tr (Wr.start seed)).1.flockOut = some out →
      ¬ Prob.BadT keccakRefShape out.point (frontOf4 H W commit tr (Wr.start seed)).1.t) :
    BatchHoldsAt4 H W commit tr seed := by
  unfold BatchHoldsAt4
  simp only [frontOf4, FrontOut.stackOf] at hbad hbadT ⊢
  refine batchHolds3_of tr hon href (squaresLen_coreBatch _ 4) _ _ _ _ (flockOut4 _ _) rfl ?_
    (FlockP.flockRingSum4 (Pure.pure ∘ H) _ keccakRec4 _ tr.qflock _ _ ?_)
    (FlockP.flock4_point_length_trace H tr keccakRec4 (by decide) _ _) hbad (hbadT _ rfl)
  all_goals simp [wideXs]

/-! ## The honest proof is accepted -/

set_option maxHeartbeats 1000000 in
/-- **π1-rec4's honest proof is accepted**, for an honest trace at the reference shape (its setup the deployment's)
whose batch's hypothesis holds at the prover's state. -/
theorem accepts_of_trace4 (D : KDeployment) (H : List UInt8 → Digest) (W : List UInt8 → RateB)
    (F : KeccakState → KeccakState) (input : Vector UInt8 32) (tr : Trace) (π : KeccakProof) (hon : TraceHonest tr)
    (href : tr.shape = keccakRefShape) (hshape : tr.shape = D.shape) (hpi : tr.publicInput = input.toList)
    (hsetup : setupStackOf tr = setupStackK D.prog D.shape)
    (hbatch : BatchHoldsAt4 H W (commitReal (m := Id) H) tr (proverSeed4 H D.programIv tr))
    (hπ : proveRec4With (m := Id) H W F PcsQuotient.nonceFuel D.programIv tr = some π) :
    KDeployment.verifierWith4H (m := Id) H W F D (D.setupRoots (setupTreeKWithH (m := Id) H F D)) input
      π = true := by
  have hF := FlockP.flockHolds_of_traceHonest tr hon
  have htree : setupTreeKWithH (m := Id) H F D = setupTreeOf (m := Id) H tr := by
    unfold setupTreeKWithH setupTreeOf
    rw [hsetup, hshape]
  have hroots := setupRoots_eq D tr (setupTreeOf (m := Id) H tr) hshape hsetup
  have hiv : KDeployment.ivWithH (m := Id) H D keccakRec4 (D.setupRoots (setupTreeOf (m := Id) H tr)) =
      contractIvOf (m := Id) H tr.shape keccakRec4 D.programIv
        (setupRootsOf tr (setupTreeOf (m := Id) H tr)) := by
    rw [hroots, hshape]; rfl
  have hC2 := c2ColumnsHonest_of_traceHonest hon
  -- The prover's proof.
  obtain ⟨p1, p2, p3, h1, h2, h3, rfl⟩ := (proveRec4With_eq_some H W F _ _ _ π).mp hπ
  -- The verifier's run on the prover's stream.
  obtain ⟨R, hrunR, hopR, hmatR, hrootR, hoodR⟩ := runWithKH4_syncs4 H W (commitReal (m := Id) H) tr
    (contractIvOf (m := Id) H tr.shape keccakRec4 D.programIv
      (setupRootsOf tr (setupTreeOf (m := Id) H tr))) hon.valid hon.rowsFit hF _
      (batchSyncsAt4_of_holds H W _ tr _ hbatch)
  have hacc := runWithKH4_accepts4 H W (commitReal (m := Id) H) tr
    (contractIvOf (m := Id) H tr.shape keccakRec4 D.programIv
      (setupRootsOf tr (setupTreeOf (m := Id) H tr))) hon.valid hon.rowsFit hF hbatch
  have hrun_eq : proverRun4 H W (commitReal (m := Id) H) tr
      (contractIvOf (m := Id) H tr.shape keccakRec4 D.programIv
        (setupRootsOf tr (setupTreeOf (m := Id) H tr))) =
      streamRun4 H W D.programIv tr := rfl
  rw [hrun_eq] at hrunR hopR hrootR hoodR hacc
  have hf : StreamFacts3 (commitReal (m := Id) H) tr (streamRun4 H W D.programIv tr).1 :=
    streamRun4_facts H W (commitReal (m := Id) H) tr _
  have hv : StreamValues3 tr (streamRun4 H W D.programIv tr).1 :=
    streamValues4 H W (commitReal (m := Id) H) tr _
  generalize (streamRun4 H W D.programIv tr).1 = out at hf hv h1 h2 h3 hopR hrootR hoodR hrunR hacc ⊢
  -- The claims.
  obtain ⟨pt1, v1, pt2, v2, pt3, v3, hcl⟩ := claims_shape _ hf.claims_fst
  have hmem : ∀ x ∈ [(Commitment.c1, pt1, v1), (.c2, pt2, v2), (.setup, pt3, v3)], x ∈ out.claims := by
    rw [hcl]; exact fun _ h ↦ h
  have hpts := hf.points hC2
  rw [href, ref_rounds] at hpts
  have hl1 : pt1.length = 27 := by simpa [ref_layoutIn_c1] using hpts _ (hmem (.c1, pt1, v1) (by simp))
  have hl2 : pt2.length = 26 := by simpa [ref_layoutIn_c2] using hpts _ (hmem (.c2, pt2, v2) (by simp))
  have hl3 : pt3.length = 23 := by simpa [ref_layoutIn_setup] using hpts _ (hmem (.setup, pt3, v3) (by simp))
  have hv1 : v1 = stackEval (c1Stack tr) pt1 := by
    have := hv.values _ (hmem (.c1, pt1, v1) (by simp)); rw [hf.c1] at this; exact this
  have hv2 : v2 = stackEval out.c2.1 pt2 := hv.values _ (hmem (.c2, pt2, v2) (by simp))
  have hv3 : v3 = stackEval (setupStackOf tr) pt3 := by
    have := hv.values _ (hmem (.setup, pt3, v3) (by simp)); rw [hf.setup] at this; exact this
  obtain ⟨α2, β2, γ2, hc2s⟩ := hv.c2stack
  have hs1 : (c1Stack tr).size = 2 ^ 27 := Core.c1Stack_size tr href
  have hs2' : out.c2.1.size = 2 ^ 26 := by rw [hc2s]; exact Core.c2Stack_size tr href _ β2 γ2
  have hs3 : (setupStackOf tr).size = 2 ^ 23 := Core.setupStackOf_size tr href
  -- The openings the prover made.
  have hfind : ∀ c, out.claims.find? (·.1 == c) =
      [(Commitment.c1, pt1, v1), (.c2, pt2, v2), (.setup, pt3, v3)].find? (·.1 == c) := by
    intro c; rw [hcl]
  obtain ⟨c1', q1, w1, hf1, ho1⟩ := (claimProof_eq_some H F _ _ _ _ _ _).mp h1
  obtain ⟨c2', q2, w2, hf2, ho2⟩ := (claimProof_eq_some H F _ _ _ _ _ _).mp h2
  obtain ⟨c3', q3, w3, hf3, ho3⟩ := (claimProof_eq_some H F _ _ _ _ _ _).mp h3
  have e1 : some (Commitment.c1, pt1, v1) = some (c1', q1, w1) := ((hfind .c1).trans rfl).symm.trans hf1
  have e2 : some (Commitment.c2, pt2, v2) = some (c2', q2, w2) := ((hfind .c2).trans rfl).symm.trans hf2
  have e3 : some (Commitment.setup, pt3, v3) = some (c3', q3, w3) := ((hfind .setup).trans rfl).symm.trans hf3
  simp only [Option.some.injEq, Prod.mk.injEq] at e1 e2 e3
  rw [← e1.2.1, ← e1.2.2] at ho1
  rw [← e2.2.1, ← e2.2.2] at ho2
  rw [← e3.2.1, ← e3.2.2] at ho3
  have ho1' : pcsProveH (m := Id) H F PcsQuotient.nonceFuel 27
      (E2ECompleteness.commitWithH (m := Id) H 27 (c1Stack tr)) (c1Stack tr) pt1 (stackEval (c1Stack tr) pt1) =
      some p1 := by
    have : pcsProveH (m := Id) H F PcsQuotient.nonceFuel (stackVarsK tr.shape .c1) out.c1.2.tree out.c1.1 pt1 v1 =
        some p1 := ho1
    simp only [hf.c1, commitReal_tree, href, reference_stackVars_c1, ref_c1Layout, hv1] at this
    exact this
  have ho2' : pcsProveH (m := Id) H F PcsQuotient.nonceFuel 26
      (E2ECompleteness.commitWithH (m := Id) H 26 out.c2.1) out.c2.1 pt2 (stackEval out.c2.1 pt2) = some p2 := by
    have : pcsProveH (m := Id) H F PcsQuotient.nonceFuel (stackVarsK tr.shape .c2) out.c2.2.tree out.c2.1 pt2 v2 =
        some p2 := ho2
    simp only [hf.c2, commitReal_tree, href, reference_stackVars_c2, ref_c2Layout, hv2] at this
    exact this
  have ho3' : pcsProveH (m := Id) H F PcsQuotient.nonceFuel 23
      (E2ECompleteness.commitWithH (m := Id) H 23 (setupStackOf tr)) (setupStackOf tr) pt3
      (stackEval (setupStackOf tr) pt3) = some p3 := by
    have : pcsProveH (m := Id) H F PcsQuotient.nonceFuel (stackVarsK tr.shape .setup)
        (E2ECompleteness.commitWithH (m := Id) H (setupLayout tr.shape).vars (setupStackOf tr)) out.setup
        pt3 v3 = some p3 := ho3
    simp only [hf.setup, href, reference_stackVars_setup, ref_setupLayout, hv3] at this
    exact this
  -- The claims' openings accept each.
  have a1 := pcsOpenKH_of H F _ (n := 27) (by norm_num) (by norm_num) _ hs1 pt1 hl1 ho1'
  have a2 := pcsOpenKH_of H F _ (n := 26) (by norm_num) (by norm_num) _ hs2' pt2 hl2 ho2'
  have a3 := pcsOpenKH_of H F _ (n := 23) (by norm_num) (by norm_num) _ hs3 pt3 hl3 ho3'
  -- The verifier.
  show verifyWithKH4 (m := Id) H W F D.shape keccakRec4
    (KDeployment.ivWithH (m := Id) H D keccakRec4 (D.setupRoots (setupTreeKWithH (m := Id) H F D)))
    (D.setupRoots (setupTreeKWithH (m := Id) H F D)) input _ = true
  rw [htree, hiv]
  have hD : D.shape = keccakRefShape := hshape.symm.trans href
  refine verifyWithKH4_of_calls H W F D.shape keccakRec4 _ _ input _ _ R pt1 pt2 pt3 v1 v2 v3 ?_ hacc ?_ ?_ hmatR
    ?_ ?_ ?_
  · rw [← hshape, ← hpi]; rfl
  · rw [hrunR]
  · rw [hopR, hcl]; rfl
  · simp only [hrootR, hoodR, hf.c1, commitReal_halves, rootRead_rootHalves, rootOf_rootHalves,
      hD, reference_stackVars_c1, href, ref_c1Layout, hv1]
    exact a1
  · simp only [hrootR, hoodR, hf.c2, commitReal_halves, rootRead_rootHalves, rootOf_rootHalves,
      hD, reference_stackVars_c2, href, ref_c2Layout, hv2]
    exact a2
  · rw [hroots]
    simp only [setupRootsOf, hD, reference_stackVars_setup, hv3, setupTree_eq, href, ref_setupLayout]
    exact a3

/-! ## The honest run's openings -/

set_option maxHeartbeats 1000000 in
/-- **The openings of π1-rec4's verifier's run on an honest proof**, at every pure Keccak-256 rate `W` and permutation
`F` (any challenges, no bad event excluded), at the reference shape: the run returns `.ok R` whose openings are three
point claims on `C1`, `C2`, the setup, in this order, at points of `27`, `26`, `23` coordinates (`stackVarsK` of the
reference shape, `reference_stackVars_c1` …), no bit-slice claim. -/
theorem honest_openings4 (D : KDeployment) (hD : D.shape = keccakRefShape) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) (W : List UInt8 → RateB)
    (F : KeccakState → KeccakState) (π : KeccakProof)
    (hπ : uniProverRec4With (m := Id) (hOf W) W F D input rows q = some π) :
    ∃ (R : Reduced) (c : Chan) (pt1 pt2 pt3 : List E) (v1 v2 v3 : E),
      runWithKH4 (m := Id) (Pure.pure ∘ hOf W) (Pure.pure ∘ W) D.shape
          (KDeployment.ivWithH (m := Id) (hOf W) D keccakRec4
            (D.setupRoots (setupTreeKWithH (m := Id) (hOf W) F D)))
          input.toList π.stream keccakRec4 .point = ⟨.ok R, c⟩ ∧
      R.openings = [(.c1, .point pt1 v1 none), (.c2, .point pt2 v2 none), (.setup, .point pt3 v3 none)] ∧
      pt1.length = 27 ∧ pt2.length = 26 ∧ pt3.length = 23 := by
  set H := hOf W
  set tr := honestTrace D input rows q
  have hon : TraceHonest tr := Mapping.honestTrace_honest D input rows q hfit hrel
  have href : tr.shape = keccakRefShape := hD
  have hshape : tr.shape = D.shape := rfl
  have hsetup : setupStackOf tr = setupStackK D.prog D.shape := setupStackOf_honestTrace D input rows q
  have hpi : tr.publicInput = input.toList := rfl
  have hF := FlockP.flockHolds_of_traceHonest tr hon
  have htree : setupTreeKWithH (m := Id) H F D = setupTreeOf (m := Id) H tr := by
    unfold setupTreeKWithH setupTreeOf
    rw [hsetup, hshape]
  have hroots := setupRoots_eq D tr (setupTreeOf (m := Id) H tr) hshape hsetup
  have hiv : KDeployment.ivWithH (m := Id) H D keccakRec4 (D.setupRoots (setupTreeOf (m := Id) H tr)) =
      contractIvOf (m := Id) H tr.shape keccakRec4 D.programIv
        (setupRootsOf tr (setupTreeOf (m := Id) H tr)) := by
    rw [hroots, hshape]; rfl
  have hC2 := c2ColumnsHonest_of_traceHonest hon
  obtain ⟨p1, p2, p3, -, -, -, rfl⟩ := (proveRec4With_eq_some H W F _ _ _ π).mp hπ
  obtain ⟨R, hrunR, hopR, -, -, -⟩ := runWithKH4_syncs4 H W (commitReal (m := Id) H) tr
    (contractIvOf (m := Id) H tr.shape keccakRec4 D.programIv
      (setupRootsOf tr (setupTreeOf (m := Id) H tr))) hon.valid hon.rowsFit hF _
      (batchSyncsAt4_any H W _ tr _)
  have hrun_eq : proverRun4 H W (commitReal (m := Id) H) tr
      (contractIvOf (m := Id) H tr.shape keccakRec4 D.programIv
        (setupRootsOf tr (setupTreeOf (m := Id) H tr))) =
      streamRun4 H W D.programIv tr := rfl
  rw [hrun_eq] at hrunR hopR
  have hf : StreamFacts3 (commitReal (m := Id) H) tr (streamRun4 H W D.programIv tr).1 :=
    streamRun4_facts H W (commitReal (m := Id) H) tr _
  rw [htree, hiv, ← hshape, ← hpi]
  generalize (streamRun4 H W D.programIv tr).1 = out at hf hopR hrunR ⊢
  obtain ⟨pt1, v1, pt2, v2, pt3, v3, hcl⟩ := claims_shape _ hf.claims_fst
  have hmem : ∀ x ∈ [(Commitment.c1, pt1, v1), (.c2, pt2, v2), (.setup, pt3, v3)], x ∈ out.claims := by
    rw [hcl]; exact fun _ h ↦ h
  have hpts := hf.points hC2
  rw [href, ref_rounds] at hpts
  have hl1 : pt1.length = 27 := by simpa [ref_layoutIn_c1] using hpts _ (hmem (.c1, pt1, v1) (by simp))
  have hl2 : pt2.length = 26 := by simpa [ref_layoutIn_c2] using hpts _ (hmem (.c2, pt2, v2) (by simp))
  have hl3 : pt3.length = 23 := by simpa [ref_layoutIn_setup] using hpts _ (hmem (.setup, pt3, v3) (by simp))
  refine ⟨R, _, pt1, pt2, pt3, v1, v2, v3, hrunR, ?_, hl1, hl2, hl3⟩
  rw [hopR, hcl]
  rfl

/-! ## The staged challenges are the prover's -/

/-- **The staged challenges are π1-rec4's prover's front state's**: `α`, `β` (the bus draw's), Flock's point, `t` (the
point draw's first). -/
theorem front_challenges4 (D : KDeployment) (W : List UInt8 → RateB) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) :
    (frontOf4 (hOf W) W (commitReal (m := Id) (hOf W)) (honestTrace D input rows q)
        (Wr.start (proverSeed4 (hOf W) D.programIv (honestTrace D input rows q)))).1.alphas =
        (proverChallenges4 D W input rows q).1 ∧
      (frontOf4 (hOf W) W (commitReal (m := Id) (hOf W)) (honestTrace D input rows q)
        (Wr.start (proverSeed4 (hOf W) D.programIv (honestTrace D input rows q)))).1.beta =
        (proverChallenges4 D W input rows q).2 ∧
      (frontOf4 (hOf W) W (commitReal (m := Id) (hOf W)) (honestTrace D input rows q)
          (Wr.start (proverSeed4 (hOf W) D.programIv (honestTrace D input rows q)))).1.flockOut.map
          (·.point) = some (proverTChallenge4 D W input rows q).1 ∧
      (frontOf4 (hOf W) W (commitReal (m := Id) (hOf W)) (honestTrace D input rows q)
        (Wr.start (proverSeed4 (hOf W) D.programIv (honestTrace D input rows q)))).1.t =
        (proverTChallenge4 D W input rows q).2 := by
  set tr := honestTrace D input rows q
  set a := proverA4 (m := Id) (hOf W) D input rows q with ha
  set seed := proverSeed4 (hOf W) D.programIv tr
  have hw2 : (((Wr.start seed).append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
      (rootWord (commitReal (m := Id) (hOf W) .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves)).append
      (scalarWire (pcsOod (c1LayoutK tr.shape).vars (c1Stack tr)
        (rootOf (commitReal (m := Id) (hOf W) .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves))) =
      ⟨prefixStream rows a.c1 a.ood, 0, seed, #[]⟩ := rfl
  have hin : tInput ⟨prefixStream rows a.c1 a.ood, 0, seed, #[]⟩ = firstInput rows a := rfl
  have h3 : wideWr ⟨prefixStream rows a.c1 a.ood, 0, seed, #[]⟩ (W (firstInput rows a)) 4 =
      writerAfter4 rows a.c1 a.ood (W (firstInput rows a)) := by
    simp [wideWr, writerAfter4, busOf]
  unfold frontOf4
  simp only []
  rw [hw2]
  simp only [wideXs_getD W 4 _ (show 0 < 4 by norm_num), wideXs_getD W 4 _ (show 1 < 4 by norm_num),
    wideXs_getD W 5 _ (show 0 < 5 by norm_num), hin, h3]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The core fact of the probability layer -/

/-- **`CoreAccepts4`** at the reference shape. -/
theorem coreAccepts4_reference (D : KDeployment) (hD : D.shape = keccakRefShape) : CoreAccepts4 D := by
  intro input rows q hfit hrel W F π hπ hbad hbadT
  have hon : TraceHonest (honestTrace D input rows q) := Mapping.honestTrace_honest D input rows q hfit hrel
  have href : (honestTrace D input rows q).shape = keccakRefShape := hD
  obtain ⟨hα, hβ, hpt, ht⟩ := front_challenges4 D W input rows q
  refine accepts_of_trace4 D (hOf W) W F input (honestTrace D input rows q) π hon href rfl rfl
    (setupStackOf_honestTrace D input rows q) ?_ hπ
  refine batchHolds4_front (hOf W) W _ _ hon href _ ?_ ?_
  · rw [hα, hβ]
    exact hbad
  · intro out hout
    rw [hout, Option.map_some, Option.some.injEq] at hpt
    rw [hpt, ht]
    have h := hbadT
    rw [hD] at h
    exact h

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.accepts_of_trace4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.accepts_of_trace4

/-- info: 'UniKeccakComplete.Rec4.coreAccepts4_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.coreAccepts4_reference
