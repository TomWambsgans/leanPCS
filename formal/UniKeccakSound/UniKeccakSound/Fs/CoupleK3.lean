-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The Keccak main line's `Fs/CoupleK.lean` at π1-rec3's
-- shape, as `UniSound/Rec3/FsCouple3.lean` is the main line's `FsCouple.lean`.
import UniKeccakSound.Fs.GameK3
import UniKeccakSound.Fs.CoupleK

/-!
# The Keccak experiment at π1-rec3's shape and the composed game, coupled

**`uniGameLeVK3_of`**: the coupling `UniGameLeVK3` from the setup bridge (`UniSetupBridgeK`, the main line's: the
setup does not depend on the variant), the verifier bridge at `keccakRec3` (`UniVerifierBridgeK3`) and the
extractor's reading at π1-rec3's rounds (`UniExtractBridgeK3`), as `CoupleK.lean`'s `uniGameLeVK_of`, with the main
line's prefix (`prefixUK`, `piOfK`, `run_logged_uAdvK`, `uFixK_toB`, `run'_map_lazyK`).
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.setupStackK UniKeccak.setupOodK

/-! ## The bridge facts -/

section Bridges

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ)
  (C : UniCodeK3 D F3 nV np) (hs : UniShapesK D)

/-- **VERIFIER**: from any state of the lazily sampled permutation, `verifyWithK` on a proof (its IV, roots, input
and Keccak proof `kpOf π`) accepts at most as often as the composed verifier on it passes `uniCheckK3` with every
opening accepting. -/
def UniVerifierBridgeK3 : Prop :=
  ∀ (π : UPf) (s : Common.PermutationEdges KeccakState),
    Pr{let b ← (simulateQ Common.lazyRandomPermutationOracles
        (verifyWithK Common.queryPermutation D.shape keccakRec3 π.iv.toList π.roots π.input (kpOf π))).run' s}[
        b = true] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
          (simulateQ keccakCallsOverQueryPermutation (verU (uSpecK3 F3 nV np) (uView (uRoundsK3 F3 nV np))
            (opsRun (uView (uRoundsK3 F3 nV np)) (uOpsK3 D F3 nV np C hs)) π))).run' s}[
        uniCheckK3 D F3 nV np C π v.1 ∧ ∀ k < (uOpsK3 D F3 nV np C hs).length, v.2.getD k false = true]

/-- **EXTRACTOR READING**: a candidate stack of `C1`'s root that the composed extractor reads off the setup's log and
a permutation transcript, satisfying the Keccak VM's relation at the proof's statement, makes `uniExtractorK`, on the
setup's evaluations and that transcript, find a stack satisfying it. -/
def UniExtractBridgeK3 : Prop :=
  ∀ (t : LeanVM.Prover.Tree) (T : Common.OracleQueryLog) (z : UPf × (List (List E) × List Bool)) (q : Stk),
    some q ∈ extractorK (fun i => (uniTcK hs i).commit) (uView (uRoundsK3 F3 nV np))
        (z, Soundness.treeTr t ++ evalTr (permutationQueries T)) →
      RelK F D (uStK3 F3 nV np z.1) q →
        ∃ q', uniExtractorK F D z.1.input (PcsQuotient.Tree.evaluations t) T (kpOf z.1) = some q' ∧
          D.Relation F (kpOf z.1).rows z.1.input q'

end Bridges

/-! ## The experiments, a common prefix then the verifiers -/

theorem keccakSoundnessExperiment_eq3 (D : KDeployment) (A : KAdversary) :
    keccakSoundnessExperiment D keccakRec3 A = Common.runWithRandomPermutation (prefixUK D A >>= fun a =>
      D.verifierWith Common.queryPermutation keccakRec3 (D.setupRoots a.1) a.2.1.1 a.2.1.2 >>= fun acc =>
        pure (((a.2.1, acc), PcsQuotient.Tree.evaluations a.1, a.2.2) : KOutcome)) := by
  unfold keccakSoundnessExperiment prefixUK
  simp only [bind_assoc, pure_bind]

theorem rpmGameS_eqK3 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (nV np : ℕ) (C : UniCodeK3 D F3 nV np) (hs : UniShapesK D) (hS : UniSetupBridgeK D hs) (A : KAdversary) :
    Common.runWithRandomPermutation
        (rpmGameS (uSetupK D hs) (uFixK D) (uAdvK D A) (uVerIvK3 D F3 nV np C hs)) =
      Common.runWithRandomPermutation (prefixUK D A >>= fun a =>
        simulateQ keccakCallsOverQueryPermutation (uVerIvK3 D F3 nV np C hs (piOfK D a)) >>= fun v =>
          pure ((piOfK D a, v), Soundness.treeTr a.1, a.2.2)) := by
  unfold rpmGameS prefixUK
  rw [hS]
  simp only [bind_map_left, bind_assoc, pure_bind, run_logged_uAdvK, rootsK_toB, uFixK_toB]
  rfl

/-! ## The verifiers, outcome by outcome -/

section Step

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ)
  (C : UniCodeK3 D F3 nV np) (hs : UniShapesK D)

/-- **One outcome of the setup and the adversary**: the Keccak event after the Keccak verifier is at most as likely
as the composed event after the composed verifier, from any state of the permutation. -/
theorem step_leK3 (hV : UniVerifierBridgeK3 D F3 nV np C hs) (hX : UniExtractBridgeK3 D F3 nV np hs)
    (a : LeanVM.Prover.Tree × ((Vector UInt8 32 × KeccakProof) × Common.OracleQueryLog))
    (s : Common.PermutationEdges KeccakState) :
    Pr{let acc ← (simulateQ Common.lazyRandomPermutationOracles
        (D.verifierWith Common.queryPermutation keccakRec3 (D.setupRoots a.1) a.2.1.1 a.2.1.2)).run' s}[
        KBreaksKnowledgeSoundness F D (uniExtractorK F D)
          (((a.2.1, acc), PcsQuotient.Tree.evaluations a.1, a.2.2))] ≤
      Pr{let v ← (simulateQ Common.lazyRandomPermutationOracles
          (simulateQ keccakCallsOverQueryPermutation (uVerIvK3 D F3 nV np C hs (piOfK D a)))).run' s}[
        UniBreaksRelK3 D F3 nV np C hs
          (ivOut (piOfK D a, v), Soundness.treeTr a.1 ++ evalTr (permutationQueries a.2.2))] := by
  -- both verifiers first compute the contract's IV
  have hL : D.verifierWith Common.queryPermutation keccakRec3 (D.setupRoots a.1) a.2.1.1 a.2.1.2 =
      simulateQ keccakCallsOverQueryPermutation (hash256 (ivInputK3 D (D.setupRoots a.1))) >>= fun iv =>
        verifyWithK Common.queryPermutation D.shape keccakRec3 iv.toList (D.setupRoots a.1) a.2.1.1 a.2.1.2 := by
    rw [KDeployment.verifierWith, ivWithK_eq3, bind_map_left]
  have hR : simulateQ keccakCallsOverQueryPermutation (uVerIvK3 D F3 nV np C hs (piOfK D a)) =
      simulateQ keccakCallsOverQueryPermutation (hash256 (ivInputK3 D (D.setupRoots a.1))) >>= fun iv =>
        (fun v => (iv, v)) <$> simulateQ keccakCallsOverQueryPermutation
          (verU (uSpecK3 F3 nV np) (uView (uRoundsK3 F3 nV np))
            (opsRun (uView (uRoundsK3 F3 nV np)) (uOpsK3 D F3 nV np C hs)) (setIv iv (piOfK D a))) := by
    rw [uVerIvK3, simulateQ_bind]
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
      (uView (uRoundsK3 F3 nV np))
      ((setIv iv (piOfK D a), v), Soundness.treeTr a.1 ++ evalTr (permutationQueries a.2.2)),
      ∀ q, c = some q → ¬ RelK F D (uStK3 F3 nV np (setIv iv (piOfK D a))) q := by
    intro v c hc q hq hrel
    subst hq
    exact hext (hX a.1 a.2.2 (setIv iv (piOfK D a), v) q hc hrel)
  have hacc := hV (setIv iv (piOfK D a)) s'
  calc _ ≤ Pr{let b ← (simulateQ Common.lazyRandomPermutationOracles
          (verifyWithK Common.queryPermutation D.shape keccakRec3 iv.toList (D.setupRoots a.1) a.2.1.1
            a.2.1.2)).run' s'}[b = true] := prEvent_mono _ _ _ fun b hb => hb.1
    _ ≤ _ := hacc
    _ ≤ _ := by
      rw [run'_map_lazyK, prEvent_map]
      exact prEvent_mono _ _ _ fun v hv => ⟨hv.1, hv.2, hnone v⟩

end Step

/-! ## The coupling -/

/-- **The coupling from the bridge facts**: the setup bridge, the verifier bridge and the extractor's reading make
the Keccak experiment's break at most as likely as the composed game's. -/
theorem uniGameLeVK3_of (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3)
    (nV np : ℕ) (C : UniCodeK3 D F3 nV np) (hs : UniShapesK D) (hS : UniSetupBridgeK D hs)
    (hV : UniVerifierBridgeK3 D F3 nV np C hs) (hX : UniExtractBridgeK3 D F3 nV np hs) :
    UniGameLeVK3 D F3 nV np C hs := by
  intro A
  rw [keccakSoundnessExperiment_eq3 D A, rpmGameS_eqK3 D F3 nV np C hs hS A]
  exact Soundness.prEvent_le_of_continuations (prefixUK D A)
    (fun a => D.verifierWith Common.queryPermutation keccakRec3 (D.setupRoots a.1) a.2.1.1 a.2.1.2)
    (fun a => simulateQ keccakCallsOverQueryPermutation (uVerIvK3 D F3 nV np C hs (piOfK D a)))
    (fun a acc => (((a.2.1, acc), PcsQuotient.Tree.evaluations a.1, a.2.2) : KOutcome))
    (fun a v => ((piOfK D a, v), Soundness.treeTr a.1, a.2.2))
    (KBreaksKnowledgeSoundness F D (uniExtractorK F D))
    (fun z => UniBreaksRelK3 D F3 nV np C hs (ivOut z.1, z.2.1 ++ evalTr (permutationQueries z.2.2)))
    fun a s => step_leK3 D F3 nV np C hs hV hX a s

end UniKeccakSound

/-- info: 'UniKeccakSound.uniGameLeVK3_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniGameLeVK3_of
