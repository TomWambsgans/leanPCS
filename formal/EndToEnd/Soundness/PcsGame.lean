-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Soundness/Final.lean` (at commit abe22812: `soundnessExperiment_eq`,
-- `rpmGame_eq`, the experiments' coupling) to the EIP's PCS claims.
import Soundness.PcsSetup
import E2ECompleteness.PcsExperiment
import E2ECompleteness.PcsDuplex
import E2ECompleteness.PcsCost
import E2ECompleteness.PcsHashLen

/-!
# The Statement's experiment is the transfer game's

The Statement's knowledge-soundness experiment (`PcsQuotient.soundnessExperiment`) runs the setup (`setupWith`), the
adversary on the setup's commitment and the verifier, all over `π`. Its setup and verifier are the two-call
computations `setupWithH callKeccak256` and `verifyWithH callKeccak256 callKeccakF1600` answered over `π`
(`E2ECompleteness/PcsWithHash.lean`), so it is a function of `PcsRpm.lean`'s game `rpmGameG` of those
(**`soundnessExperiment_eq`**), and it breaks only where the game's event `EvK` holds of the setup's log and the
adversary's evaluations (**`prEvent_soundness_le`**): on the game's support the setup's log is its tree's evaluations
then the out-of-domain point's `46`-byte entries (`setupLog`), and the Statement's extractor finds a secret where the
extraction succeeds on that log (`extractor_of_extracts`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace PcsKS

open QuotientRpm QuotientSecurity Compose ComposePcs LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

/-! ## Supports -/

/-- Simulating a computation by computations shrinks its support. -/
theorem support_simulateQ_subset' {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α : Type}
    (impl : QueryImpl spec (OracleComp spec')) (oa : OracleComp spec α) :
    support (simulateQ impl oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    intro x hx
    simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at hx
    obtain ⟨u, -, hx⟩ := hx
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, ih u hx⟩

/-- **The log of a computation whose every Keccak-256 input satisfies `P`**: the starting log, then entries
satisfying `P`. -/
theorem log_support (P : List UInt8 → Prop) {α : Type} (X : OracleComp KeccakCalls α)
    (hX : E2ECompleteness.HashOK P X) :
    ∀ (l : Transcript), ∀ p ∈ support ((simulateQ logImplKC X).run l),
      ∃ L : Transcript, p.2 = l ++ L ∧ ∀ e ∈ L, P e.1 := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro l p hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨[], by simp, by simp⟩
  | query_bind t k ih =>
    intro l p hp
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 hX
    rw [loggedKC_run_query_bind, mem_support_bind_iff] at hp
    obtain ⟨u, -, hp⟩ := hp
    obtain ⟨L, hL, hP⟩ := ih u (hk u) _ p hp
    refine ⟨(inlEntry ⟨t, u⟩).toList ++ L, by rw [hL, List.append_assoc], fun e he => ?_⟩
    rcases List.mem_append.mp he with he | he
    · rcases t with x | s
      · simp only [inlEntry, Option.toList_some, List.mem_singleton] at he
        subst he
        exact ht
      · simp [inlEntry] at he
    · exact hP e he

/-! ## The setup -/

/-- The Statement's setup with Keccak-256 a call. -/
noncomputable abbrev setupS : OracleComp KeccakCalls (LeanVM.Prover.Tree × PcsQuotient.Commitment) :=
  E2ECompleteness.Pcs.setupWithH callKeccak256

theorem hashOK_ood (n : ℕ) (root : Digest) :
    E2ECompleteness.HashOK (fun x => x.length = 46)
      (E2ECompleteness.Pcs.oodPointWithH callKeccak256 n root) := by
  unfold E2ECompleteness.Pcs.oodPointWithH
  refine E2ECompleteness.Pcs.HashOK.mapM _ (fun j ↦ ?_) _
  exact E2ECompleteness.HashOK.bind
    (E2ECompleteness.hashOK_callKeccak256 (E2ECompleteness.Pcs.length_oodInput _ _ _))
    fun _ ↦ E2ECompleteness.HashOK.pure _ _

/-- **The setup's log** is its tree's evaluations, then the out-of-domain point's `46`-byte inputs. -/
theorem setupLog {s : (LeanVM.Prover.Tree × PcsQuotient.Commitment) × Transcript}
    (hs : s ∈ support (loggedKC setupS)) :
    ∃ L : Transcript, s.2 = Soundness.treeTr s.1.1 ++ L ∧ ∀ e ∈ L, e.1.length = 46 := by
  unfold setupS E2ECompleteness.Pcs.setupWithH E2ECompleteness.Pcs.commitmentWithH at hs
  unfold loggedKC at hs
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hs
  obtain ⟨tl, htl, hs⟩ := hs
  have hb : (simulateQ logImplKC (E2ECompleteness.Pcs.commitWithH callKeccak256
      (PcsQuotient.cellVars PcsQuotient.logRows)
      (PcsQuotient.membership PcsQuotient.logRows).wiringTable)).run [] =
      (fun t => (t, Soundness.treeTr t)) <$> E2ECompleteness.Pcs.commitWithH callKeccak256
        (PcsQuotient.cellVars PcsQuotient.logRows) (PcsQuotient.membership PcsQuotient.logRows).wiringTable :=
    Soundness.loggedKC_buildTree _ _
  rw [hb, support_map] at htl
  obtain ⟨t, -, rfl⟩ := htl
  have hm : (E2ECompleteness.Pcs.oodPointWithH callKeccak256 (PcsQuotient.cellVars PcsQuotient.logRows) t.root >>=
      fun z => (pure (t, (⟨t.root, PcsQuotient.tableEval (PcsQuotient.membership PcsQuotient.logRows).wiringTable z⟩ :
        PcsQuotient.Commitment)) : OracleComp KeccakCalls _)) =
      (fun z => (t, (⟨t.root, PcsQuotient.tableEval (PcsQuotient.membership PcsQuotient.logRows).wiringTable z⟩ :
        PcsQuotient.Commitment))) <$>
        E2ECompleteness.Pcs.oodPointWithH callKeccak256 (PcsQuotient.cellVars PcsQuotient.logRows) t.root := by
    rw [map_eq_bind_pure_comp]
    rfl
  simp only at hs
  rw [hm, simulateQ_map, StateT.run_map, support_map] at hs
  obtain ⟨p, hp, rfl⟩ := hs
  obtain ⟨L, hL, hP⟩ := log_support (fun x => x.length = 46) _ (hashOK_ood _ _) _ p hp
  exact ⟨L, hL, hP⟩

/-! ## The experiment -/

/-- The adversary on the setup's output: given its commitment. -/
def advS (A : PcsQuotient.Adversary) :
    LeanVM.Prover.Tree × PcsQuotient.Commitment →
      OracleComp Common.RandomPermutationOracles (PcsQuotient.Statement × PcsQuotient.Proof) :=
  fun s => A s.2

/-- The Statement's verifier with the two calls, on the setup's commitment. -/
def verV (s : LeanVM.Prover.Tree × PcsQuotient.Commitment) (a : PcsQuotient.Statement × PcsQuotient.Proof) :
    OracleComp KeccakCalls Bool :=
  E2ECompleteness.Pcs.verifyWithH callKeccak256 callKeccakF1600 22 s.2 a.1 a.2

/-- The Statement's outcome of an outcome of the game. -/
def outS (z : (((LeanVM.Prover.Tree × PcsQuotient.Commitment) × (PcsQuotient.Statement × PcsQuotient.Proof)) ×
    Bool) × Transcript × Common.OracleQueryLog) : PcsQuotient.Outcome :=
  ((z.1.1.2, z.1.2), PcsQuotient.Tree.evaluations z.1.1.1.1, z.2.2)

theorem setupWith_qp : PcsQuotient.setupWith Common.queryPermutation =
    Prod.fst <$> simulateQ keccakCallsOverQueryPermutation (loggedKC setupS) := by
  rw [E2ECompleteness.Pcs.setupWith_eqH, ← E2ECompleteness.Pcs.implH_keccakCallsOverQueryPermutation,
    ← E2ECompleteness.Pcs.simulateQ_setupWithH, ← simulateQ_map, loggedKC, fst_loggedKC_run]

theorem verifier_qp (s : LeanVM.Prover.Tree × PcsQuotient.Commitment) (stmt : PcsQuotient.Statement)
    (proof : PcsQuotient.Proof) :
    PcsQuotient.verifier Common.queryPermutation s.2 stmt proof =
      simulateQ keccakCallsOverQueryPermutation (verV s (stmt, proof)) := by
  rw [verV, E2ECompleteness.Pcs.simulateQ_verifyWithH,
    E2ECompleteness.Pcs.implH_keccakCallsOverQueryPermutation,
    E2ECompleteness.Pcs.implF_keccakCallsOverQueryPermutation, PcsQuotient.verifier,
    E2ECompleteness.Pcs.verifyWith_eqH]
  rfl

/-- **The Statement's experiment is a function of the game.** -/
theorem soundnessExperiment_eq (A : PcsQuotient.Adversary) :
    PcsQuotient.soundnessExperiment A =
      outS <$> Common.runWithRandomPermutation (rpmGameG setupS (advS A) verV) := by
  have h : (do
      let (tree, index) ← PcsQuotient.setupWith Common.queryPermutation
      let (z, transcript) ← (simulateQ Common.loggedOracles (A index)).run []
      let accepted ← PcsQuotient.verifier Common.queryPermutation index z.1 z.2
      return (((z, accepted), PcsQuotient.Tree.evaluations tree, transcript) : PcsQuotient.Outcome)) =
      outS <$> rpmGameG setupS (advS A) verV := by
    rw [setupWith_qp, bind_map_left, rpmGameG, map_bind]
    refine bind_congr fun s => ?_
    obtain ⟨⟨t, i⟩, l⟩ := s
    simp only [map_bind, map_pure, advS]
    refine bind_congr fun p => ?_
    obtain ⟨⟨stmt, proof⟩, T⟩ := p
    rw [verifier_qp (t, i) stmt proof]
    rfl
  rw [PcsQuotient.soundnessExperiment, h, Common.runWithRandomPermutation,
    Common.runWithRandomPermutation, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map,
    Functor.map_map, Functor.map_map]

/-- **The Statement's experiment breaks only where the game's event holds.** -/
theorem prEvent_soundness_le (A : PcsQuotient.Adversary) :
    Pr{let z ← PcsQuotient.soundnessExperiment A}[PcsQuotient.BreaksKnowledgeSoundness z] ≤
      Pr{let z ← Common.runWithRandomPermutation (rpmGameG setupS (advS A) verV)}[BreaksG EvK z] := by
  rw [soundnessExperiment_eq, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun z hz hb => ?_
  have hz' := support_simulateQ_run'_subset _ _ _ hz
  simp only [rpmGameG, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz'
  obtain ⟨s, hs, p, -, v, -, rfl⟩ := hz'
  obtain ⟨L, hL, hP⟩ := setupLog (support_simulateQ_subset' _ _ hs)
  refine ⟨hb.1, fun hx => hb.2 ?_⟩
  rw [hL] at hx
  exact extractor_of_extracts s.1.1 L hP p.2 p.1 hx

end PcsKS
