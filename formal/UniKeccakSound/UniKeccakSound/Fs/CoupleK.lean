-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `UniSound/FsCouple.lean` (after
-- `formal/EndToEnd/Soundness/Final.lean`: `prEvent_le_of_continuations`, `step_le`) for the Keccak experiment
-- (`formal/UniKeccak`'s `keccakSoundnessExperiment`: one setup tree, the Keccak contract's IV, `verifyWithK`).
import UniKeccakSound.Fs.GameK
import Soundness.Final

/-!
# The Keccak experiment and the composed game, coupled

**`uniGameLeVK_of`**: the coupling `UniGameLeVK` (`GameK.lean`) from three bridge facts, as `UniSound`'s:

* **`UniSetupBridgeK`** (the setup): the composed setup over `π`, logged (`uSetupK`: one tree, `stackSetupS` of the
  setup's stack at its plain shape), is the Keccak experiment's `setupTreeKWith` over `π`, its root as bytes and its
  log the tree's evaluations (`Soundness.treeTr`);
* **`UniVerifierBridgeK`** (the verifier): from any state of the lazily sampled permutation, `verifyWithK` (the run on
  the stream, its early stops, the three claims' openings) accepts at most as often as the composed verifier (the
  chain over the univariate encoding and the three openings) satisfies `uniCheckK` with all three openings
  accepting;
* **`UniExtractBridgeK`** (the extractor's reading): a candidate of `C1`'s root that the composed extractor reads off
  the setup's log and the adversary's permutation transcript, and that satisfies the Keccak VM's relation (`RelK`),
  makes `uniExtractorK` find a stack satisfying it.

The proof is `UniSound.uniGameLeV_of`'s: both experiments are the setup's tree and the adversary given its roots
(`D.setupRoots`), its queries logged (`prefixUK`), then their verifiers on the same state of the permutation; both
first compute the Keccak contract's IV, the same Keccak-256 call (`ivWithK_eq`), then (`step_leK`) the Keccak event
is impossible if its extractor finds a stack, and otherwise follows from the verifier's acceptance.
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.layoutWordsK UniKeccak.setupStackK

/-! ## The bridge facts -/

/-- **SETUP**: the composed setup over `π`, logged, is `setupTreeKWith` over `π`, its root as bytes, its log the
tree's evaluations. -/
def UniSetupBridgeK (D : KDeployment) (hs : UniShapesK D) : Prop :=
  simulateQ keccakCallsOverQueryPermutation (loggedKC (uSetupK D hs)) =
    (fun t : LeanVM.Prover.Tree => (toB t.root, Soundness.treeTr t)) <$>
      setupTreeKWith Common.queryPermutation D

section Bridges

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain) (nV V : ℕ)
  (C : UniCodeK D Fl nV V) (hs : UniShapesK D)

/-- **VERIFIER**: from any state of the lazily sampled permutation, `verifyWithK` on a proof (its IV, roots, input
and Keccak proof `kpOf π`) accepts at most as often as the composed verifier on it passes `uniCheckK` with every
opening accepting. -/
def UniVerifierBridgeK : Prop :=
  ∀ (π : UPf) (s : Common.PermutationEdges KeccakState),
    Pr{let b ← (simulateQ Common.lazyRandomPermutationOracles
        (verifyWithK Common.queryPermutation D.shape keccakMain π.iv.toList π.roots π.input (kpOf π))).run' s}[
        b = true] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
          (simulateQ keccakCallsOverQueryPermutation (verU (uSpecK Fl nV V) (uView (uRoundsK Fl nV V))
            (opsRun (uView (uRoundsK Fl nV V)) (uOpsK D Fl nV V C hs)) π))).run' s}[
        uniCheckK D Fl nV V C π v.1 ∧ ∀ k < (uOpsK D Fl nV V C hs).length, v.2.getD k false = true]

/-- **EXTRACTOR READING**: a candidate stack of `C1`'s root that the composed extractor reads off the setup's log and
a permutation transcript, satisfying the Keccak VM's relation at the proof's statement, makes `uniExtractorK`, on the
setup's evaluations and that transcript, find a stack satisfying it. -/
def UniExtractBridgeK : Prop :=
  ∀ (t : LeanVM.Prover.Tree) (T : Common.OracleQueryLog) (z : UPf × (List (List E) × List Bool)) (q : Stk),
    some q ∈ extractorK (fun i => (uniTcK hs i).commit) (uView (uRoundsK Fl nV V))
        (z, Soundness.treeTr t ++ evalTr (permutationQueries T)) →
      RelK F D (uStK Fl nV V z.1) q →
        ∃ q', uniExtractorK F D z.1.input (PcsQuotient.Tree.evaluations t) T (kpOf z.1) = some q' ∧
          D.Relation F (kpOf z.1).rows z.1.input q'

end Bridges

/-! ## The experiments, a common prefix then the verifiers -/

theorem rootsK_toB (D : KDeployment) (t : LeanVM.Prover.Tree) : rootsK D (toB t.root) = D.setupRoots t := by
  simp only [rootsK, KDeployment.setupRoots, Soundness.ofB_toB_root]

/-- The proof the composed game's verifier reads, from the setup's tree and the adversary's output. -/
def piOfK (D : KDeployment) (a : LeanVM.Prover.Tree × ((Vector UInt8 32 × KeccakProof) × Common.OracleQueryLog)) :
    UPf :=
  ⟨a.2.1.1, upOf a.2.1.2, Vector.replicate 32 0, D.setupRoots a.1⟩

/-- **The common prefix**: the setup's tree over `π`, then the adversary given its roots, its queries logged. -/
noncomputable def prefixUK (D : KDeployment) (A : KAdversary) :
    OracleComp Common.RandomPermutationOracles
      (LeanVM.Prover.Tree × ((Vector UInt8 32 × KeccakProof) × Common.OracleQueryLog)) :=
  setupTreeKWith Common.queryPermutation D >>= fun t =>
    (simulateQ Common.loggedOracles (A (D.setupRoots t))).run [] >>= fun p => pure (t, p)

theorem keccakSoundnessExperiment_eq (D : KDeployment) (A : KAdversary) :
    keccakSoundnessExperiment D keccakMain A = Common.runWithRandomPermutation (prefixUK D A >>= fun a =>
      D.verifierWith Common.queryPermutation keccakMain (D.setupRoots a.1) a.2.1.1 a.2.1.2 >>= fun acc =>
        pure (((a.2.1, acc), PcsQuotient.Tree.evaluations a.1, a.2.2) : KOutcome)) := by
  unfold keccakSoundnessExperiment prefixUK
  simp only [bind_assoc, pure_bind]

theorem run_logged_uAdvK (D : KDeployment) (A : KAdversary) (s : Bytes32) :
    (simulateQ Common.loggedOracles (uAdvK D A s)).run [] =
      (fun p => ((⟨p.1.1, upOf p.1.2, Vector.replicate 32 0, rootsK D s⟩ : UPf), p.2)) <$>
        (simulateQ Common.loggedOracles (A (rootsK D s))).run [] := by
  rw [uAdvK, simulateQ_map, StateT.run_map]

theorem uFixK_toB (D : KDeployment) (t : LeanVM.Prover.Tree) (π : UPf) :
    uFixK D (toB t.root) π = { π with roots := D.setupRoots t } := by
  rw [← rootsK_toB D t]
  rfl

theorem run'_map_lazyK {α β : Type} (f : α → β) (X : OracleComp Common.RandomPermutationOracles α)
    (s : Common.PermutationEdges KeccakState) :
    (simulateQ Common.lazyRandomPermutationOracles (f <$> X)).run' s =
      f <$> (simulateQ Common.lazyRandomPermutationOracles X).run' s := by
  rw [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, StateT.run'_eq,
    Functor.map_map]

theorem rpmGameS_eqK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (nV V : ℕ) (C : UniCodeK D Fl nV V) (hs : UniShapesK D) (hS : UniSetupBridgeK D hs) (A : KAdversary) :
    Common.runWithRandomPermutation
        (rpmGameS (uSetupK D hs) (uFixK D) (uAdvK D A) (uVerIvK D Fl nV V C hs)) =
      Common.runWithRandomPermutation (prefixUK D A >>= fun a =>
        simulateQ keccakCallsOverQueryPermutation (uVerIvK D Fl nV V C hs (piOfK D a)) >>= fun v =>
          pure ((piOfK D a, v), Soundness.treeTr a.1, a.2.2)) := by
  unfold rpmGameS prefixUK
  rw [hS]
  simp only [bind_map_left, bind_assoc, pure_bind, run_logged_uAdvK, rootsK_toB, uFixK_toB]
  rfl

/-! ## The verifiers, outcome by outcome -/

section Step

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain) (nV V : ℕ)
  (C : UniCodeK D Fl nV V) (hs : UniShapesK D)

/-- **One outcome of the setup and the adversary**: the Keccak event after the Keccak verifier is at most as likely
as the composed event after the composed verifier, from any state of the permutation. -/
theorem step_leK (hV : UniVerifierBridgeK D Fl nV V C hs) (hX : UniExtractBridgeK D Fl nV V hs)
    (a : LeanVM.Prover.Tree × ((Vector UInt8 32 × KeccakProof) × Common.OracleQueryLog))
    (s : Common.PermutationEdges KeccakState) :
    Pr{let acc ← (simulateQ Common.lazyRandomPermutationOracles
        (D.verifierWith Common.queryPermutation keccakMain (D.setupRoots a.1) a.2.1.1 a.2.1.2)).run' s}[
        KBreaksKnowledgeSoundness F D (uniExtractorK F D)
          (((a.2.1, acc), PcsQuotient.Tree.evaluations a.1, a.2.2))] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
          (simulateQ keccakCallsOverQueryPermutation (uVerIvK D Fl nV V C hs (piOfK D a)))).run' s}[
        UniBreaksRelK D Fl nV V C hs
          (ivOut (piOfK D a, v), Soundness.treeTr a.1 ++ evalTr (permutationQueries a.2.2))] := by
  -- both verifiers first compute the contract's IV
  have hL : D.verifierWith Common.queryPermutation keccakMain (D.setupRoots a.1) a.2.1.1 a.2.1.2 =
      simulateQ keccakCallsOverQueryPermutation (hash256 (ivInputK D (D.setupRoots a.1))) >>= fun iv =>
        verifyWithK Common.queryPermutation D.shape keccakMain iv.toList (D.setupRoots a.1) a.2.1.1 a.2.1.2 := by
    rw [KDeployment.verifierWith, ivWithK_eq, bind_map_left]
  have hR : simulateQ keccakCallsOverQueryPermutation (uVerIvK D Fl nV V C hs (piOfK D a)) =
      simulateQ keccakCallsOverQueryPermutation (hash256 (ivInputK D (D.setupRoots a.1))) >>= fun iv =>
        (fun v => (iv, v)) <$> simulateQ keccakCallsOverQueryPermutation
          (verU (uSpecK Fl nV V) (uView (uRoundsK Fl nV V))
            (opsRun (uView (uRoundsK Fl nV V)) (uOpsK D Fl nV V C hs)) (setIv iv (piOfK D a))) := by
    rw [uVerIvK, simulateQ_bind]
    simp only [simulateQ_map]
    rfl
  rw [hL, hR]
  refine Soundness.mono_bind Common.lazyRandomPermutationOracles _ _ _ _ _ (fun iv s' => ?_) s
  -- the Keccak extractor finds a stack: no break
  by_cases hext : ∃ q, uniExtractorK F D a.2.1.1 (PcsQuotient.Tree.evaluations a.1) a.2.2 a.2.1.2 = some q ∧
      D.Relation F a.2.1.2.rows a.2.1.1 q
  · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ ?_)) zero_le
    intro acc _ hb
    exact hb.2 hext
  -- otherwise no candidate of the composed extractor satisfies the relation
  have hnone : ∀ (v : List (List E) × List Bool), ∀ c ∈ extractorK (fun i => (uniTcK hs i).commit)
      (uView (uRoundsK Fl nV V))
      ((setIv iv (piOfK D a), v), Soundness.treeTr a.1 ++ evalTr (permutationQueries a.2.2)),
      ∀ q, c = some q → ¬ RelK F D (uStK Fl nV V (setIv iv (piOfK D a))) q := by
    intro v c hc q hq hrel
    subst hq
    exact hext (hX a.1 a.2.2 (setIv iv (piOfK D a), v) q hc hrel)
  have hacc := hV (setIv iv (piOfK D a)) s'
  calc _ ≤ Pr{let b ← (simulateQ Common.lazyRandomPermutationOracles
          (verifyWithK Common.queryPermutation D.shape keccakMain iv.toList (D.setupRoots a.1) a.2.1.1
            a.2.1.2)).run' s'}[b = true] := prEvent_mono _ _ _ fun b hb => hb.1
    _ ≤ _ := hacc
    _ ≤ _ := by
      rw [run'_map_lazyK, prEvent_map]
      exact prEvent_mono _ _ _ fun v hv => ⟨hv.1, hv.2, hnone v⟩

end Step

/-! ## The coupling -/

/-- **The coupling from the bridge facts**: the setup bridge, the verifier bridge and the extractor's reading make
the Keccak experiment's break at most as likely as the composed game's. -/
theorem uniGameLeVK_of (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (nV V : ℕ) (C : UniCodeK D Fl nV V) (hs : UniShapesK D) (hS : UniSetupBridgeK D hs)
    (hV : UniVerifierBridgeK D Fl nV V C hs) (hX : UniExtractBridgeK D Fl nV V hs) :
    UniGameLeVK D Fl nV V C hs := by
  intro A
  rw [keccakSoundnessExperiment_eq D A, rpmGameS_eqK D Fl nV V C hs hS A]
  exact Soundness.prEvent_le_of_continuations (prefixUK D A)
    (fun a => D.verifierWith Common.queryPermutation keccakMain (D.setupRoots a.1) a.2.1.1 a.2.1.2)
    (fun a => simulateQ keccakCallsOverQueryPermutation (uVerIvK D Fl nV V C hs (piOfK D a)))
    (fun a acc => (((a.2.1, acc), PcsQuotient.Tree.evaluations a.1, a.2.2) : KOutcome))
    (fun a v => ((piOfK D a, v), Soundness.treeTr a.1, a.2.2))
    (KBreaksKnowledgeSoundness F D (uniExtractorK F D))
    (fun z => UniBreaksRelK D Fl nV V C hs (ivOut z.1, z.2.1 ++ evalTr (permutationQueries z.2.2)))
    fun a s => step_leK D Fl nV V C hs hV hX a s

end UniKeccakSound

/-- info: 'UniKeccakSound.uniGameLeVK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniGameLeVK_of
