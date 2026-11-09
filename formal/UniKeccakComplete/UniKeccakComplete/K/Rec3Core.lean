-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec3's honest proof is accepted: `Core.lean`'s
-- `accepts_of_trace`, `coreAccepts_reference` for π1-rec3's verifier (`KDeployment.verifierWithH` at `keccakRec3`,
-- three `PCS_OPEN` calls) and prover (`Rec3Prover.lean`).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/Rec3Core.lean`.
import UniKeccakComplete.K.Rec3CoreBatch
import UniKeccakComplete.K.Rec3CoreRun
import UniKeccakComplete.K.Core

/-!
# π1-rec3's honest proof is accepted (Keccak VM)

* **`accepts_of_trace3`**: for an honest trace at the reference shape (`keccakRefShape`, its setup the deployment's),
  whose paired batch synchronises at a zero terminal (`BatchSyncsAt3 … (fun _ ↦ 0)`), a proof `proveRec3With` (Flock's
  honest prover on the Keccak-f block, at `keccakRec3`) returns is accepted by `KDeployment.verifierWithH` at
  `keccakRec3`: the run on the prover's stream accepts (`runWithKH_syncs3`, `runWithKH_accepts3`; Flock's collected
  value zero, `FlockP.flockSyncs_trace … keccakRec3`), its claims are the prover's (`streamRun3_facts`,
  `streamValues3`), and WHIR's three honest openings are accepted (`pcsOpen_honest_k`, at `27, 26, 23` variables);
  `verifyWithKH_of_calls` assembles them.
* **`front_challenges3`**: the staged challenges (`proverChallenges3`, `proverTChallenge3`) are the prover's front
  state's (`α`, `β`, Flock's point, `t`).
* **`coreAccepts3_reference`**: `CoreAccepts3 D flockProveH` at the reference shape, the paired batch's hypothesis
  from `Rec3CoreBatch.batchSyncsAt3_front` (Flock's ring identity `FlockP.flockRingSum` and point length
  `FlockP.flock_point_length_trace` at `keccakRec3`), the bad events moved to the prover's front state by
  `front_challenges3`. `coreFailsOnlyAtPow3` (every shape, every Flock prover) is in `Rec3CoreRun.lean`.
-/

open UniStatement UniKeccak LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace UniKeccakComplete.Rec3

open UniComplete

open ProverRun
open UniKeccakSound (keccakRefShape)
open UniKeccakComplete.Core (claims_shape ref_word_c1 ref_word_c2 ref_word_setup commitReal_tree commitReal_halves
  rootRead_digestScalars)

/-! ## The honest proof is accepted -/

set_option maxHeartbeats 1000000 in
/-- **π1-rec3's honest proof is accepted**, for an honest trace at the reference shape (its setup the deployment's)
whose paired batch synchronises at a zero terminal. -/
theorem accepts_of_trace3 (D : KDeployment) (H : List UInt8 → Digest) (F : KeccakState → KeccakState)
    (input : Vector UInt8 32) (tr : Trace) (π : KeccakProof) (hon : TraceHonest tr)
    (href : tr.shape = keccakRefShape) (hshape : tr.shape = D.shape) (hpi : tr.publicInput = input.toList)
    (hsetup : setupStackOf tr = setupStackK D.prog D.shape)
    (hbatch : BatchSyncsAt3 H (commitReal (m := Id) H) (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr
      (proverSeed3 H D.programIv tr) (fun _ ↦ 0))
    (hπ : proveRec3With (m := Id) H F PcsQuotient.nonceFuel (FlockP.flockProve (m := Id) (Pure.pure ∘ H))
      D.programIv tr = some π) :
    KDeployment.verifierWithH (m := Id) H F D keccakRec3 (D.setupRoots (setupTreeKWithH (m := Id) H F D)) input
      π = true := by
  have hflock := FlockP.flockSyncs_trace H tr hon keccakRec3 (by decide)
  have htree : setupTreeKWithH (m := Id) H F D = setupTreeOf (m := Id) H tr := by
    unfold setupTreeKWithH setupTreeOf
    rw [hsetup, hshape]
  have hiv : KDeployment.ivWithH (m := Id) H D keccakRec3 (D.setupRoots (setupTreeOf (m := Id) H tr)) =
      contractIvOf (m := Id) H tr.shape keccakRec3 D.programIv
        ⟨(setupTreeOf (m := Id) H tr).root⟩ := by
    rw [hshape]; rfl
  have hC2 := c2ColumnsHonest_of_traceHonest hon
  -- The prover's proof.
  obtain ⟨p1, p2, p3, h1, h2, h3, rfl⟩ := (proveRec3With_eq_some H F _ _ _ _ _ _ π).mp hπ
  -- The verifier's run on the prover's stream.
  obtain ⟨R, hrunR, hopR, hmatR, hrootR⟩ := runWithKH_syncs3 H (commitReal (m := Id) H)
    (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr
    (contractIvOf (m := Id) H tr.shape keccakRec3 D.programIv
      ⟨(setupTreeOf (m := Id) H tr).root⟩) hon.valid hon.rowsFit (fun _ ↦ 0) hflock
    (fun _ ↦ 0) hbatch
  have hacc := runWithKH_accepts3 H (commitReal (m := Id) H) (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr
    (contractIvOf (m := Id) H tr.shape keccakRec3 D.programIv
      ⟨(setupTreeOf (m := Id) H tr).root⟩) hon.valid hon.rowsFit (fun _ ↦ 0) hflock
    (fun _ ↦ 0) hbatch rfl rfl
  have hrun_eq : proverRun3 H (commitReal (m := Id) H) (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr
      (contractIvOf (m := Id) H tr.shape keccakRec3 D.programIv
        ⟨(setupTreeOf (m := Id) H tr).root⟩) =
      streamRun3 H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) D.programIv tr := rfl
  rw [hrun_eq] at hrunR hopR hrootR hacc
  have hf : StreamFacts3 (commitReal (m := Id) H) tr
      (streamRun3 H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) D.programIv tr).1 :=
    streamRun3_facts H (commitReal (m := Id) H) _ tr _
  have hv : StreamValues3 tr
      (streamRun3 H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) D.programIv tr).1 :=
    streamValues3 H (commitReal (m := Id) H) _ tr _
  generalize (streamRun3 H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) D.programIv tr).1 = out
    at hf hv h1 h2 h3 hopR hrootR hrunR hacc ⊢
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
  have ho1' : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel (plainLayout 27)
      (E2ECompleteness.commitWithH (m := Id) H 27 (c1Stack tr)) (c1Stack tr) [⟨pt1, stackEval (c1Stack tr) pt1⟩] =
      some p1 := by
    have : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel
        (plainLayout (layoutWordVars ((layoutWordsK tr.shape).getD 0 []))) out.c1.2.tree out.c1.1 [⟨pt1, v1⟩] =
        some p1 := ho1
    simp only [hf.c1, commitReal_tree, href, ref_word_c1, ref_c1Layout, hv1] at this
    exact this
  have ho2' : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel (plainLayout 26)
      (E2ECompleteness.commitWithH (m := Id) H 26 out.c2.1) out.c2.1 [⟨pt2, stackEval out.c2.1 pt2⟩] =
      some p2 := by
    have : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel
        (plainLayout (layoutWordVars ((layoutWordsK tr.shape).getD 1 []))) out.c2.2.tree out.c2.1 [⟨pt2, v2⟩] =
        some p2 := ho2
    simp only [hf.c2, commitReal_tree, href, ref_word_c2, ref_c2Layout, hv2] at this
    exact this
  have ho3' : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel (plainLayout 23)
      (E2ECompleteness.commitWithH (m := Id) H 23 (setupStackOf tr)) (setupStackOf tr)
      [⟨pt3, stackEval (setupStackOf tr) pt3⟩] = some p3 := by
    have : E2ECompleteness.proveOpeningWithH (m := Id) H F PcsQuotient.nonceFuel
        (plainLayout (layoutWordVars ((layoutWordsK tr.shape).getD 2 [])))
        (E2ECompleteness.commitWithH (m := Id) H (setupLayout tr.shape).vars (setupStackOf tr)) out.setup
        [⟨pt3, v3⟩] = some p3 := ho3
    simp only [hf.setup, href, ref_word_setup, ref_setupLayout, hv3] at this
    exact this
  -- WHIR accepts each.
  have a1 := pcsOpen_honest_k H F _ (vars := 27) (by norm_num) (by norm_num) _ hs1 pt1 hl1 ho1'
  have a2 := pcsOpen_honest_k H F _ (vars := 26) (by norm_num) (by norm_num) _ hs2' pt2 hl2 ho2'
  have a3 := pcsOpen_honest_k H F _ (vars := 23) (by norm_num) (by norm_num) _ hs3 pt3 hl3 ho3'
  -- The verifier.
  show verifyWithKH (m := Id) H F D.shape keccakRec3
    (KDeployment.ivWithH (m := Id) H D keccakRec3 (D.setupRoots (setupTreeKWithH (m := Id) H F D)))
    (D.setupRoots (setupTreeKWithH (m := Id) H F D)) input _ = true
  rw [htree, hiv]
  have hD : D.shape = keccakRefShape := hshape.symm.trans href
  refine verifyWithKH_of_calls H F D.shape keccakRec3 _ _ input _ _ R pt1 pt2 pt3 v1 v2 v3 ?_ hacc ?_ ?_ hmatR
    ?_ ?_ ?_
  · rw [← hshape, ← hpi]; rfl
  · rw [hrunR]
  · rw [hopR, hcl]; rfl
  · simp only [hrootR, hf.c1, commitReal_halves, rootRead_digestScalars, rootOf_digestScalars, hD, ref_word_c1,
      href, ref_c1Layout, hv1]
    exact a1
  · simp only [hrootR, hf.c2, commitReal_halves, rootRead_digestScalars, rootOf_digestScalars, hD, ref_word_c2,
      href, ref_c2Layout, hv2]
    exact a2
  · simp only [hD, ref_word_setup, hv3, KDeployment.setupRoots, setupTree_eq, href, ref_setupLayout]
    exact a3

/-! ## The staged challenges are the prover's -/

/-- **The staged challenges are π1-rec3's prover's front state's**: `α`, `β`, Flock's point, `t`. -/
theorem front_challenges3 (H : List UInt8 → Digest) (flock : FlockProver Id) (D : KDeployment)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    (frontOf3 H (commitReal (m := Id) H) flock (honestTrace D input rows q)
        (Wr.start (proverSeed3 H D.programIv (honestTrace D input rows q)))).1.alphas =
        (proverChallenges3 H D input rows q).1 ∧
      (frontOf3 H (commitReal (m := Id) H) flock (honestTrace D input rows q)
        (Wr.start (proverSeed3 H D.programIv (honestTrace D input rows q)))).1.beta =
        (proverChallenges3 H D input rows q).2 ∧
      (frontOf3 H (commitReal (m := Id) H) flock (honestTrace D input rows q)
          (Wr.start (proverSeed3 H D.programIv (honestTrace D input rows q)))).1.flockOut.map
          (·.point) = some (proverTChallenge3 H flock D input rows q).1 ∧
      (frontOf3 H (commitReal (m := Id) H) flock (honestTrace D input rows q)
        (Wr.start (proverSeed3 H D.programIv (honestTrace D input rows q)))).1.t =
        (proverTChallenge3 H flock D input rows q).2 := by
  set tr := honestTrace D input rows q
  set c1 := E2ECompleteness.commitWithH (m := Id) H (c1LayoutK tr.shape).vars (c1Stack tr)
  set seed := proverSeed3 H D.programIv tr
  have hw2 : ((Wr.start seed).append (tr.rows.flatMap fun n ↦ integerWire n 4)).append
      (rootWord (commitReal (m := Id) H .c1 (c1LayoutK tr.shape).vars (c1Stack tr)).halves) =
      ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩ := rfl
  set s₁ := H (digestBytes seed ++ ((Prob.prefixStream rows c1).extract 0 (Prob.prefixStream rows c1).size).toList)
  have h1 : Wr.sampled H ⟨Prob.prefixStream rows c1, 0, seed, #[]⟩ =
      (Prob.chal s₁, ⟨Prob.prefixStream rows c1, (Prob.prefixStream rows c1).size, s₁, #[Prob.chal s₁]⟩) := rfl
  have h2 : Wr.sampled H ⟨Prob.prefixStream rows c1, (Prob.prefixStream rows c1).size, s₁, #[Prob.chal s₁]⟩ =
      (Prob.chal (H (digestBytes s₁)), writerAfter3 rows c1 s₁ (H (digestBytes s₁))) := by
    simp only [Wr.sampled, Prob.extract_size_toList, List.append_nil]
    rfl
  unfold frontOf3
  simp only []
  rw [hw2, h1, h2]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The core fact of the probability layer -/

/-- **`CoreAccepts3` for Flock's honest prover** at the reference shape. -/
theorem coreAccepts3_reference (D : KDeployment) (hD : D.shape = keccakRefShape) :
    CoreAccepts3 D flockProveH := by
  intro input rows q hfit hrel H F π hπ hbad hbadT
  have hon : TraceHonest (honestTrace D input rows q) := Mapping.honestTrace_honest D input rows q hfit hrel
  have href : (honestTrace D input rows q).shape = keccakRefShape := hD
  obtain ⟨hα, hβ, hpt, ht⟩ := front_challenges3 H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) D input rows q
  refine accepts_of_trace3 D H F input (honestTrace D input rows q) π hon href rfl rfl
    (setupStackOf_honestTrace D input rows q) ?_ hπ
  refine batchSyncsAt3_front H _ _ _ hon href _
    (fun w ↦ FlockP.flockRingSum (Pure.pure ∘ H) _ keccakRec3 _ w)
    (fun w ↦ FlockP.flock_point_length_trace H _ keccakRec3 (by decide) w) ?_ ?_
  · rw [hα, hβ]
    exact hbad
  · intro out hout
    rw [hout, Option.map_some, Option.some.injEq] at hpt
    rw [hpt, ht]
    have h := hbadT
    rw [hD] at h
    exact h

end UniKeccakComplete.Rec3

/-- info: 'UniKeccakComplete.Rec3.accepts_of_trace3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.accepts_of_trace3

/-- info: 'UniKeccakComplete.Rec3.coreAccepts3_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.coreAccepts3_reference

/-- info: 'UniKeccakComplete.Rec3.coreFailsOnlyAtPow3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.coreFailsOnlyAtPow3
