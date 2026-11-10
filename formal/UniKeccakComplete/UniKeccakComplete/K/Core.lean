-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/Core.lean`.
import UniKeccakComplete.K.CoreRun
import UniKeccakComplete.K.CoreBatch
import UniKeccakComplete.K.FlockCommutes
import UniKeccakComplete.K.VerifierAccept
import UniKeccakComplete.K.Setup
import UniKeccakComplete.K.Mapping

/-!
# The honest prover's proof is accepted (Keccak VM, main line)

The core of completeness at a pure hash and permutation (`Prob.CoreAccepts`, `Prob.CoreFailsOnlyAtPow`), for
Flock's honest prover on the Keccak-f block (`flockProveH`) at the reference shape (`keccakRefShape`):

* **`accepts_of_trace`**: for an honest trace (`TraceHonest`) at the reference shape, its setup the deployment's,
  whose batching sumcheck synchronises with a zero terminal (`BatchSyncsAt … (fun _ ↦ 0)`), a proof `proveWith`
  returns is accepted by `KDeployment.verifierWithH` at `keccakMain`: the verifier's run on the prover's stream
  accepts (`runWithKH_syncs`, `runWithKH_accepts`: the counts' checks, Flock's collected value — zero for the honest
  Keccak-f prover, `FlockP.flockSyncs_trace` — and the batch's terminal are zero) with the prover's three point
  claims and no matrices' claim, and the three PCS claims' checks accept the honest openings (`pcsOpenKH_of`, at
  `27, 26, 23` variables, `reference_stackVars_c1`: each claim's value is its stack's extension at its point,
  `streamValues`; each point has its stack's variables, `StreamFacts.points`; the stacks' sizes, `c1Stack_size`,
  `c2Stack_size`, `setupStackOf_size`; each root is the committed tree's, `rootRead_rootHalves`, `rootOf_rootHalves`,
  each out-of-domain answer the prover's, the setup's commitment the deployment's, `setupRoots_eq`,
  `setupStackOf_honestTrace`); `verifyWithKH_of_calls` assembles them;
* **`coreAccepts_reference`**: `CoreAccepts D flockProveH` at the reference shape, the batch's hypothesis at the
  prover's state from `CoreBatch.lean`'s `batchSyncsAt_front`, the bad events moved from the staged challenges to the
  prover's state by `front_challenges`;
* **`coreFailsOnlyAtPow`**: `proveWith` fails only at a PCS opening whose point has its variables
  (`proveWith_eq_none`, every commitment has a claim, `claims_complete`, `claim_length`), at every shape.
-/

open UniStatement UniKeccak LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace UniKeccakComplete.Core

open UniComplete

open ProverRun
open UniKeccakSound (keccakRefShape)

/-- A root's halves are read back as they are (`digestScalars` leaves the top limbs zero). -/
theorem rootRead_digestScalars (d : Digest) : rootRead (digestScalars d) = digestScalars d := by
  have h := digestOfScalars_digestScalars d
  unfold digestOfScalars at h
  split at h
  · rename_i hc
    exact rootRead_of hc.1 hc.2
  · exact absurd h (by simp)

theorem commitReal_tree (H : List UInt8 → Digest) (c : Commitment) (vars : ℕ) (stack : Array K) :
    (commitReal (m := Id) H c vars stack).tree = E2ECompleteness.commitWithH (m := Id) H vars stack := rfl

theorem commitReal_halves (H : List UInt8 → Digest) (c : Commitment) (vars : ℕ) (stack : Array K) :
    (commitReal (m := Id) H c vars stack).halves =
      rootHalves (E2ECompleteness.commitWithH (m := Id) H vars stack).root := rfl

/-- A root's halves as the prover sends them are read back as they are (no top limbs). -/
theorem rootRead_rootHalves (d : Digest) : rootRead (rootHalves d) = rootHalves d := by
  simp only [rootRead, rootHalves, (UniSound.limb_eNew_lane _ _ _).1, (UniSound.limb_eNew_lane _ _ _).2]

/-- **The honest PCS opening is accepted by the verifier's claim check** (`pcsOpenKH`), at `23 ≤ n ≤ 28`. -/
theorem pcsOpenKH_of (H : List UInt8 → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {n : ℕ}
    (h1 : 23 ≤ n) (h2 : n ≤ 28) (stack : Array K) (hs : stack.size = 2 ^ n) (pt : List E) (hpt : pt.length = n)
    {π : Compile.Proof}
    (hπ : pcsProveH (m := Id) H F fuel n (E2ECompleteness.commitWithH (m := Id) H n stack) stack pt
      (stackEval stack pt) = some π) :
    pcsOpenKH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s)) n
      (E2ECompleteness.commitWithH (m := Id) H n stack).root
      (pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root) pt (stackEval stack pt) π = true := by
  unfold pcsOpenKH
  simp only [hpt, ↓reduceDIte]
  exact pcsVerify_pcsProveH H F fuel h1 h2 stack hs pt hpt hπ

/-- **The setup's commitment the verifier holds is the prover's**, its stack the deployment's. -/
theorem setupRoots_eq (D : KDeployment) (tr : Trace) (tree : LeanVM.Prover.Tree) (hshape : tr.shape = D.shape)
    (hsetup : setupStackOf tr = setupStackK D.prog D.shape) : D.setupRoots tree = setupRootsOf tr tree := by
  simp only [KDeployment.setupRoots, setupRootsOf, setupOodK, pcsOod, stackEval, pcsZ, hsetup]
  rw [hshape]

/-- Three claims on `C1`, `C2`, the setup, in order. -/
theorem claims_shape (l : List (Commitment × List E × E)) (h : l.map (·.1) = [.c1, .c2, .setup]) :
    ∃ pt1 v1 pt2 v2 pt3 v3, l = [(.c1, pt1, v1), (.c2, pt2, v2), (.setup, pt3, v3)] := by
  rcases l with _ | ⟨⟨a, pt1, v1⟩, _ | ⟨⟨b, pt2, v2⟩, _ | ⟨⟨c, pt3, v3⟩, _ | _⟩⟩⟩ <;> simp at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨_, _, _, _, _, _, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **The honest proof is accepted**, for an honest trace at the reference shape (its setup the deployment's) whose
batching sumcheck synchronises with a zero terminal. -/
theorem accepts_of_trace (D : KDeployment) (H : List UInt8 → Digest) (F : KeccakState → KeccakState)
    (input : Vector UInt8 32) (tr : Trace) (π : KeccakProof) (hon : TraceHonest tr)
    (href : tr.shape = keccakRefShape) (hshape : tr.shape = D.shape) (hpi : tr.publicInput = input.toList)
    (hsetup : setupStackOf tr = setupStackK D.prog D.shape)
    (hbatch : BatchSyncsAt H (commitReal (m := Id) H) (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr
      (proverSeed H D.programIv tr) (fun _ ↦ 0))
    (hπ : proveWith (m := Id) H F PcsQuotient.nonceFuel (FlockP.flockProve (m := Id) (Pure.pure ∘ H))
      D.programIv tr = some π) :
    KDeployment.verifierWithH (m := Id) H F D keccakMain (D.setupRoots (setupTreeKWithH (m := Id) H F D)) input
      π = true := by
  have hflock := FlockP.flockSyncs_trace H tr hon keccakMain (by decide)
  have htree : setupTreeKWithH (m := Id) H F D = setupTreeOf (m := Id) H tr := by
    unfold setupTreeKWithH setupTreeOf
    rw [hsetup, hshape]
  have hroots := setupRoots_eq D tr (setupTreeOf (m := Id) H tr) hshape hsetup
  have hiv : KDeployment.ivWithH (m := Id) H D keccakMain (D.setupRoots (setupTreeOf (m := Id) H tr)) =
      contractIvOf (m := Id) H tr.shape keccakMain D.programIv
        (setupRootsOf tr (setupTreeOf (m := Id) H tr)) := by
    rw [hroots, hshape]; rfl
  have hC2 := c2ColumnsHonest_of_traceHonest hon
  -- The prover's proof.
  obtain ⟨p1, p2, p3, h1, h2, h3, rfl⟩ := (proveWith_eq_some H F _ _ _ _ π).mp hπ
  -- The verifier's run on the prover's stream.
  obtain ⟨R, hrunR, hopR, hmatR, hrootR, hoodR⟩ := runWithKH_syncs H (commitReal (m := Id) H)
    (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr
    (contractIvOf (m := Id) H tr.shape keccakMain D.programIv
      (setupRootsOf tr (setupTreeOf (m := Id) H tr))) hon.valid hon.rowsFit (fun _ ↦ 0) hflock
    (fun _ ↦ 0) hbatch
  have hacc := runWithKH_accepts H (commitReal (m := Id) H) (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr
    (contractIvOf (m := Id) H tr.shape keccakMain D.programIv
      (setupRootsOf tr (setupTreeOf (m := Id) H tr))) hon.valid hon.rowsFit (fun _ ↦ 0) hflock
    (fun _ ↦ 0) hbatch rfl rfl
  have hrun_eq : proverRun H (commitReal (m := Id) H) (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr
      (contractIvOf (m := Id) H tr.shape keccakMain D.programIv
        (setupRootsOf tr (setupTreeOf (m := Id) H tr))) =
      streamRun H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) D.programIv tr := rfl
  rw [hrun_eq] at hrunR hopR hrootR hoodR hacc
  have hf : StreamFacts (commitReal (m := Id) H) tr
      (streamRun H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) D.programIv tr).1 :=
    streamRun_facts H (commitReal (m := Id) H) _ tr _
  have hv : StreamValues tr
      (streamRun H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) D.programIv tr).1 :=
    streamValues H (commitReal (m := Id) H) _ tr _
  generalize (streamRun H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) D.programIv tr).1 = out
    at hf hv h1 h2 h3 hopR hrootR hoodR hrunR hacc ⊢
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
  have hs1 : (c1Stack tr).size = 2 ^ 27 := c1Stack_size tr href
  have hs2' : out.c2.1.size = 2 ^ 26 := by rw [hc2s]; exact c2Stack_size tr href _ β2 γ2
  have hs3 : (setupStackOf tr).size = 2 ^ 23 := setupStackOf_size tr href
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
  show verifyWithKH (m := Id) H F D.shape keccakMain
    (KDeployment.ivWithH (m := Id) H D keccakMain (D.setupRoots (setupTreeKWithH (m := Id) H F D)))
    (D.setupRoots (setupTreeKWithH (m := Id) H F D)) input _ = true
  rw [htree, hiv]
  have hD : D.shape = keccakRefShape := hshape.symm.trans href
  refine verifyWithKH_of_calls H F D.shape keccakMain _ _ input _ _ R pt1 pt2 pt3 v1 v2 v3 ?_ hacc ?_ ?_ hmatR
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

/-! ## The core facts of `ProbHyp.lean` -/

/-- **`CoreAccepts` for Flock's honest prover** at the reference shape. -/
theorem coreAccepts_reference (D : KDeployment) (hD : D.shape = keccakRefShape) :
    Prob.CoreAccepts D flockProveH := by
  intro input rows q hfit hrel H F π hπ hbad hbadT
  have hon : TraceHonest (honestTrace D input rows q) := Mapping.honestTrace_honest D input rows q hfit hrel
  have href : (honestTrace D input rows q).shape = keccakRefShape := hD
  obtain ⟨hα, hβ, hpt, ht⟩ := front_challenges H (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) D input rows q
  refine accepts_of_trace D H F input (honestTrace D input rows q) π hon href rfl rfl
    (setupStackOf_honestTrace D input rows q) ?_ hπ
  refine batchSyncsAt_front H _ _ hon href _ ?_ ?_
  · rw [hα, hβ]
    exact hbad
  · intro out hout
    rw [hout, Option.map_some, Option.some.injEq] at hpt
    rw [hpt, ht]
    have h := hbadT
    rw [hD] at h
    exact h

/-- **`proveWith` fails only at an opening**: if it returns `none`, one of the three WHIR openings returned `none`
(every commitment has a claim, `claims_complete`). -/
theorem fails_only_at_opening (H : List UInt8 → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
    (flock : FlockProver Id) (programIv : List UInt8) (tr : Trace) (hon : TraceHonest tr)
    (hnone : proveWith (m := Id) H F fuel flock programIv tr = none) :
    ∃ (n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E), pt.length = n ∧
      pcsProveH (m := Id) H F fuel n tree stack pt v = none := by
  have hf : StreamFacts (commitReal (m := Id) H) tr (streamRun H flock programIv tr).1 :=
    streamRun_facts H (commitReal (m := Id) H) _ tr _
  have hC2 := c2ColumnsHonest_of_traceHonest hon
  rcases proveWith_eq_none H F _ _ _ _ hnone with hmiss | ⟨_, pt, v, hfd, h⟩ | ⟨_, pt, v, hfd, h⟩ |
      ⟨_, pt, v, hfd, h⟩
  · exfalso
    obtain ⟨c, hc, hn⟩ := hmiss
    have hc' : c ∈ (streamRun H flock programIv tr).1.claims.map (·.1) := by
      rw [hf.claims_fst]; exact hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc'
    exact absurd (by simp : (x.1 == x.1) = true) (List.find?_eq_none.mp hn x hx)
  all_goals exact ⟨_, _, _, pt, v, claim_length hf hC2 hfd, h⟩

/-- **The honest prover fails only at an opening** (`Prob.CoreFailsOnlyAtPow`), every shape. -/
theorem coreFailsOnlyAtPow (D : KDeployment) : Prob.CoreFailsOnlyAtPow D flockProveH :=
  fun input rows q hfit hrel H F _ _ hnone ↦ fails_only_at_opening H F _ _ _ _
    (Mapping.honestTrace_honest D input rows q hfit hrel) hnone

end UniKeccakComplete.Core

/-- info: 'UniKeccakComplete.Core.accepts_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Core.accepts_of_trace

/-- info: 'UniKeccakComplete.Core.coreAccepts_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Core.coreAccepts_reference

/-- info: 'UniKeccakComplete.Core.coreFailsOnlyAtPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Core.coreFailsOnlyAtPow
