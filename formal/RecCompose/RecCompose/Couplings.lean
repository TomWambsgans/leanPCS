-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Part1
import RecCompose.Part2
import RecCompose.Rpm

/-!
# The soundness couplings

* `experimentsAgree`: the end-to-end experiment is π2's, the calls dropped (the monad laws).
* `hazardCoupling`: the hazard adversary built from π2's (`hazardAdversary`) makes `A`'s queries, and its transcript,
  logged, is `A`'s (`Rpm.logged_post`); for every fixed permutation (`Rpm.prEvent_le_of_perm`) the two games agree up to
  the contract, which the hazard event does not read.
* `pi1Coupling`: the π1 adversary built from π2's (`pi1Adversary`) likewise; for every fixed permutation and every
  prefix (the setup, `A`'s output and transcript) on which π2's extractor outputs a stream `s` accepted with the
  contract's π1 openings `ops` off the hazard, the contract accepts at most as often as its three π1 openings do
  (`contract_le_openSeq`: the contract's acceptance needs all eight; `loop_le`), and those are π1-rec3's verifier at
  Keccak-f[1600] with its openings over `π` (**`Pi1OpeningsAgree`**, named below); `CallsPure` makes the contract's π1
  openings the calldata's `pi1OpsOf`.
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-- **The end-to-end experiment is π2's, the calls dropped.** -/
theorem experimentsAgree (D : RecDeployment) : ExperimentsAgree D := by
  intro A
  unfold recSoundnessExperiment recSoundnessExperiment2
  rw [Rpm.runWithRandomPermutation_map]
  congr 1
  simp only [map_bind, RecDeployment.verifierWith, bind_assoc]
  refine bind_congr fun trees ↦ bind_congr fun p ↦ ?_
  obtain ⟨z, T⟩ := p
  refine bind_congr fun r ↦ ?_
  simp

/-- The derived adversaries' continuation after `A`. -/
theorem hazardAdversary_eq (D : RecDeployment) (A : RecAdversary) (roots : RecSetupRoots)
    (evals : List (List UInt8 × Digest)) :
    hazardAdversary D A roots evals = (simulateQ loggedOracles (A roots)).run [] >>= fun p ↦
      pure (p.1.1, (recExtractor2 D roots p.1.1 evals p.2 p.1.2).getD #[]) := by
  unfold hazardAdversary
  refine bind_congr fun p ↦ ?_
  obtain ⟨z, T⟩ := p
  rfl

/-- **The hazard coupling.** -/
theorem hazardCoupling (D : RecDeployment) : HazardCoupling D := by
  intro A Q hQ
  refine ⟨fun roots evals ↦ ?_, ?_⟩
  · rw [hazardAdversary_eq]
    exact Rpm.queryCost_post _ _ _ (fun _ ↦ rfl) Q (hQ roots)
  unfold recSoundnessExperiment2 pi1HazardExperiment
  refine Rpm.prEvent_le_of_perm _ _ _ _ fun π ↦ ?_
  simp only [simulateQ_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun trees ↦ ?_
  rw [hazardAdversary_eq, Rpm.logged_post _ _ _ (fun _ ↦ rfl), simulateQ_map, bind_map_left]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p ↦ ?_
  obtain ⟨z, T⟩ := p
  simp only [simulateQ_pure]
  refine prEvent_bind_le_of_forall_le _ _ _ fun r ↦ ?_
  obtain ⟨acc, calls⟩ := r
  simp only
  refine Rpm.prEvent_pure_le _ _ _ _ fun h1 ↦ ?_
  obtain ⟨s, hs, hz⟩ := h1
  simp only at hs ⊢
  rw [hs]
  exact hz

/-! ## π1-rec3's coupling -/

/-- **A π1 opening as the block opens the contract's claim**: `UniKeccak.pcsOpenK` on the point's length
(`pcsOpenWords` on the claim's words, decoded). -/
def openAt {m : Type → Type} [Monad m] (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (o : Pi1Opening) (p : Compile.Proof) : m Bool :=
  UniKeccak.pcsOpenK F o.2.2.1.length o.1 o.2.1 o.2.2.1 o.2.2.2 p

/-- **The contract's three π1 openings** `ops`, with the recursive proof's three π1 opening proofs. -/
def openSeq {m : Type → Type} [Monad m] (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState)
    (ops : List Pi1Opening) (proof : RecProof) : m Bool := do
  let b1 ← openAt F (ops.getD 0 default) proof.c1
  let b2 ← openAt F (ops.getD 1 default) proof.c2
  let b3 ← openAt F (ops.getD 2 default) proof.f
  return b1 && b2 && b3

/-- **Named hypothesis: π1-rec3's verifier at Keccak-f[1600] is the contract's three π1 openings**, on a stream `s`
π1-rec3's graph accepts with the contract's π1 openings `ops` (read off the calldata) off the merge hazard, the graph
being π1-rec3's verifier there: `pi1KeccakVerifierWith` (π1's run over Keccak-f[1600], then `C1`, `C2`, the setup opened
over `π` at their stacks' variables `stackVarsK`) on π1's proof of `s` with the recursive proof's three π1 opening
proofs is, as a computation, the contract's three π1 claims opened, `openSeq` of `ops` (each at its point's length).

Why it holds (`OpeningsAgree.lean`, `pi1OpeningsAgree`): off the hazard `Pi1GraphIsVerifierK` makes the graph's
outputs `RecGraphKeccak.verifierOutputsWithK`'s at the reference shape (`D.pi1.shape = keccak128`), so the Keccak run
accepts and the graph's claims are `UniKeccak.pcsClaimWordsK`' words; their decoding (`decodePi1Call`, which
`Pi1GraphAccepts` compares with `ops`) gives back the verifier's openings (`elementOfWord ∘ elementWord`,
`digestOfBytes32 ∘ digestBytes`, the roots `rootOf`'s bytes); `F`'s commitment is the deployment's
(`pi1CallsWith`); the verifier's openings at π1-rec3 are three point claims in `commitments` order, no matrix call;
and the contract's points have `stackVarsK` coordinates (`Pi1CallsShape`: the calls' word counts). -/
def Pi1OpeningsAgree (D : RecDeployment) : Prop :=
  RecGraphKeccak.Pi1GraphIsVerifierK →
    ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) (s : Array UInt8)
      (ops : List Pi1Opening),
      pi1OpsOf D roots input proof.stream = some ops →
      Pi1GraphAccepts (D.pi1IvAt roots.pi1) input s ops →
      ¬ RecGraphKeccak.MergeHazardK LeanVM.Semantics.keccakF1600 (D.pi1IvAt roots.pi1) input.toList s →
        pi1KeccakVerifierWith queryPermutation D.pi1 roots.pi1 input (proof.pi1Proof s) =
          openSeq queryPermutation ops proof

/-- A claim that decodes is opened as its decoded opening. -/
theorem pcsOpenWords_eq {m : Type → Type} [Monad m]
    (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState) (w : List (List UInt8)) (p : Compile.Proof)
    (x : Pi1Opening) (h : claimOfWords w = some x) : pcsOpenWords F w p = openAt F x p := by
  unfold pcsOpenWords openAt
  rw [h]

/-- **The contract's eight openings accept at most as often as its three π1 openings**, over any oracle answers. -/
theorem loop_le (I : QueryImpl RandomPermutationOracles ProbComp)
    (calls : List (List (List UInt8))) (hlen : calls.length = 8) (proof : RecProof) (ops : List Pi1Opening)
    (hops : contractPi1Openings calls = some ops) :
    Pr{let x ← simulateQ I (do
        let s ← forIn (calls.zip proof.openings) true fun x s ↦ do
          let b ← pcsOpenWords queryPermutation x.1 x.2
          pure (ForInStep.yield (s && b))
        pure (s, calls))}[x.1 = true ∧ contractPi1Openings x.2 = some ops] ≤
      Pr{let b ← simulateQ I (openSeq queryPermutation ops proof)}[b = true] := by
  match calls, hlen with
  | [w0, w1, w2, w3, w4, w5, w6, w7], _ =>
    simp only [contractPi1Openings, List.take, List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hops
    obtain ⟨x0, h0, _, ⟨x1, h1, _, ⟨x2, h2, _, rfl, rfl⟩, rfl⟩, rfl⟩ := hops

    simp only [RecProof.openings, List.zip_cons_cons, List.zip_nil_left, List.forIn_cons, List.forIn_nil,
      bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, pcsOpenWords_eq _ _ _ _ h0, pcsOpenWords_eq _ _ _ _ h1,
      pcsOpenWords_eq _ _ _ _ h2, openSeq, List.getD_cons_zero, List.getD_cons_succ]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun b0 ↦ ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun b1 ↦ ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun b2 ↦ ?_
    refine prEvent_bind_le_of_forall_le _ _ _ fun b3 ↦ ?_
    refine prEvent_bind_le_of_forall_le _ _ _ fun b4 ↦ ?_
    refine prEvent_bind_le_of_forall_le _ _ _ fun b5 ↦ ?_
    refine prEvent_bind_le_of_forall_le _ _ _ fun b6 ↦ ?_
    refine prEvent_bind_le_of_forall_le _ _ _ fun b7 ↦ ?_
    refine Rpm.prEvent_pure_le _ _ _ _ fun h ↦ ?_
    simp only [Bool.and_eq_true] at h ⊢
    tauto

/-- A pure event that fails has probability at most anything. -/
theorem prEvent_pure_le_of_not {α : Type} (a : α) (p : α → Prop) (h : ¬ p a) (x : ℝ≥0∞) :
    Pr{let y ← (pure a : ProbComp α)}[p y] ≤ x := by
  classical
  rw [prEvent_pure]
  simp [h]

/-- **The contract accepts with π1 openings `ops` at most as often as those openings accept**, over any oracle
answers. -/
theorem contract_le_openSeq (I : QueryImpl RandomPermutationOracles ProbComp) (D : RecDeployment)
    (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) (ops : List Pi1Opening) :
    Pr{let x ← simulateQ I (D.contractWith queryPermutation roots input proof)}[
      x.1 = true ∧ contractPi1Openings x.2 = some ops] ≤
    Pr{let b ← simulateQ I (openSeq queryPermutation ops proof)}[b = true] := by
  unfold RecDeployment.contractWith
  simp only [simulateQ_bind]
  refine prEvent_bind_le_of_forall_le _ _ _ fun iv ↦ ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun o ↦ ?_
  split
  · rw [simulateQ_pure]
    exact prEvent_pure_le_of_not _ _ (fun h ↦ Bool.false_ne_true h.1) _
  · rename_i r hr
    split_ifs with h1 h2
    · rw [simulateQ_pure]
      exact prEvent_pure_le_of_not _ _ (fun h ↦ Bool.false_ne_true h.1) _
    · rw [simulateQ_pure]
      exact prEvent_pure_le_of_not _ _ (fun h ↦ Bool.false_ne_true h.1) _
    · rcases Classical.em (contractPi1Openings (pcsCalls (D.circuitAt roots.pi1).circuit
          (pi1CallsWith D.pi1Calls roots.pi1) (digestBytes roots.pi2) roots.pi2Ood proof.stream r) = some ops)
        with hops | hops
      · exact loop_le I _ (not_not.mp h2) proof ops hops
      · rw [simulateQ_bind]
        refine prEvent_bind_le_of_forall_le _ _ _ fun b ↦ ?_
        rw [simulateQ_pure]
        exact prEvent_pure_le_of_not _ _ (fun h ↦ hops h.2) _

/-- The π1 adversary's continuation after `A`. -/
theorem pi1Adversary_eq (D : RecDeployment) (A : RecAdversary) (roots : RecSetupRoots)
    (evals : List (List UInt8 × Digest)) :
    pi1Adversary D A roots evals = (simulateQ loggedOracles (A roots)).run [] >>= fun p ↦
      pure (p.1.1, p.1.2.pi1Proof ((recExtractor2 D roots p.1.1 evals p.2 p.1.2).getD #[])) := by
  unfold pi1Adversary
  refine bind_congr fun p ↦ ?_
  obtain ⟨z, T⟩ := p
  rfl

/-- The contract's π1 openings are the calldata's, on the outcome. -/
def CallsGood (D : RecDeployment) (z : RecOutcome2) : Prop :=
  acc z = true → ∃ ops, pi1OpsOf D (rts z) (inp z) (prf z).stream = some ops ∧
    contractPi1Openings (cls z) = some ops

/-- **π1-rec3's coupling.** -/
theorem pi1Coupling (D : RecDeployment) (hpure : CallsPure D) (hagree : Pi1OpeningsAgree D) : Pi1Coupling D := by
  intro hgv A Q hQ
  refine ⟨fun roots evals ↦ ?_, ?_⟩
  · rw [pi1Adversary_eq]
    exact Rpm.queryCost_post _ _ _ (fun _ ↦ rfl) Q (hQ roots)
  refine (prEvent_mono_of_support _ _ (fun z ↦ Pi1Event D z ∧ CallsGood D z)
    fun z hz h ↦ ⟨h, fun ha ↦ hpure A z hz ha⟩).trans ?_
  unfold recSoundnessExperiment2 pi1KeccakSoundnessExperiment
  refine Rpm.prEvent_le_of_perm _ _ _ _ fun π ↦ ?_
  simp only [simulateQ_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun trees ↦ ?_
  rw [pi1Adversary_eq, Rpm.logged_post _ _ _ (fun _ ↦ rfl), simulateQ_map, bind_map_left]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p ↦ ?_
  obtain ⟨z, T⟩ := p
  simp only
  rcases Classical.em (∃ s ops, recExtractor2 D trees.roots z.1 trees.evaluations T z.2 = some s ∧
      pi1OpsOf D trees.roots z.1 z.2.stream = some ops ∧
      Pi1GraphAccepts (D.pi1IvAt trees.roots.pi1) z.1 s ops ∧
      ¬ RecGraphKeccak.MergeHazardK LeanVM.Semantics.keccakF1600 (D.pi1IvAt trees.roots.pi1) z.1.toList s ∧
      ¬ ∃ q, UniKeccak.uniExtractorK D.flock D.pi1 z.1 trees.evaluations T (z.2.pi1Proof s) = some q ∧
        D.pi1.Relation D.flock (z.2.pi1Proof s).rows z.1 q) with hC | hC
  · obtain ⟨s, ops, hs, hops, hga, hz, hno⟩ := hC
    have hV := hagree hgv trees.roots z.1 z.2 s ops hops hga hz
    rw [hs, Option.getD_some]
    simp only [simulateQ_pure, bind_pure_comp, prEvent_map]
    refine (prEvent_mono _ _ _ ?_).trans ((contract_le_openSeq _ D trees.roots z.1 z.2 ops).trans ?_)
    · rintro x ⟨⟨ha, -⟩, hg⟩
      obtain ⟨ops', hops', hcon'⟩ := hg ha
      refine ⟨ha, ?_⟩
      have e : ops' = ops := by
        change pi1OpsOf D trees.roots z.1 z.2.stream = some ops' at hops'
        rw [hops] at hops'
        exact (Option.some.inj hops').symm
      subst e
      exact hcon'
    · rw [← hV]
      exact prEvent_mono _ _ _ fun b hb ↦ ⟨hb, hno⟩
  · refine prEvent_bind_le_of_forall_le _ _ _ fun r ↦ ?_
    obtain ⟨acc, calls⟩ := r
    refine prEvent_pure_le_of_not _ _ ?_ _
    rintro ⟨⟨ha, s, ops, hs, hops, hga, hz, hno⟩, hg⟩
    obtain ⟨ops', hops', hcon'⟩ := hg ha
    have : ops' = ops := by
      simp only at hops hcon'
      rw [hops] at hcon'
      exact (Option.some.inj hcon').symm
    subst this
    exact hC ⟨s, ops', hs, hops', hga, hz, hno⟩

end RecCompose

/-- info: 'RecCompose.experimentsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.experimentsAgree

/-- info: 'RecCompose.hazardCoupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.hazardCoupling

/-- info: 'RecCompose.pi1Coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi1Coupling
