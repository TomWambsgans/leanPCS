-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Soundness/{Final,RpmV}.lean` (at commit abe22812: the end theorem
-- from the random-permutation transfer and the composition) to the EIP's PCS claims (`formal/SoundPcs`).
import Soundness.PcsGame
import Bridge.Claims.Constants

/-!
# Knowledge soundness of the deployed membership proof (the EIP's PCS claims)

**`Soundness.knowledgeSoundness : PcsQuotient.KnowledgeSoundness Soundness.ksBound`**, with no hypothesis:

1. the Statement's experiment breaks only where the transfer game's event holds (`prEvent_soundness_le`,
   `PcsGame.lean`);
2. the game moves to mumbai's two-oracle model, against one deterministic adversary `A'` of at most
   `2^20 + 24 + Q` queries, less `(setupPermCalls + Q + verifierPermCalls)² / 2^508` (`rpm_le_romG`, `PcsRpm.lean`);
3. there it is bounded by `SoundPcs`'s deployed run of the converted adversary (`le_dExp`, `PcsDExp.lean`): outcome
   by outcome, the Statement's verifier is the deployed run's chain and six openings (`verifyWithH_eq_contD`) or
   rejects (`verifyWithH_reject`), and `SoundPcs`'s extractor list holds a witness only where the extraction succeeds
   (`extracts_of_mem`) (`hcmpK`);
4. the deployed run breaks with probability at most `SoundPcs.deployedBound` (`knowledgeSoundness_deployed_pcsM`,
   at the Statement's wiring table `wcol`, `claimsMatchK`), at the constants the bridges prove: `beta()` is a Cantor
   basis (`Bridge.isCantor_statementConsts`), `tau` solves `row_vanishing`'s system
   (`E2ECompleteness.Pcs.rowVanishing_stmt`), the wire reads the statement as its halves (`pcsWire`).

`ksBound Q = deployedBound (2^20 + 24 + Q) + (setupPermCalls + Q + verifierPermCalls)² / 2^508`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace PcsKS

open QuotientRpm QuotientSecurity Compose ComposePcs LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge.Pcs SoundPcs

variable (hc : IsCantor PcsBridge.statementConsts.beta)

/-- The deployed wire at the deployed instance. -/
noncomputable abbrev WK : Wire (instR hc).params (instR hc).bounds := pcsWire (instR hc)

/-- The setup's commitment as `SoundPcs` reads it: its root's bytes and its out-of-domain answer. -/
def phiS (x : LeanVM.Prover.Tree × PcsQuotient.Commitment) : QuotientRpm.Bytes32 × E := (toB x.2.root, x.2.ood)

theorem run'_map {α β : Type} (f : α → β) (X : OracleComp KeccakCalls α) (c : KeccakCalls.QueryCache) :
    (simulateQ randomOracle (f <$> X)).run' c = f <$> (simulateQ randomOracle X).run' c := by
  rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]

theorem support_contD {P : Params E} {B : P.Bounds} (W : Wire P B) (O : OpenSpec) (po : RootProof4 E × Rest)
    (tA : Transcript) {z : S0 × Bool} (hz : z ∈ support (contD W O po tA)) :
    z.1.π = po.1 ∧ z.1.tA = tA := by
  unfold contD at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨ch, -, hz⟩ := hz
  rw [support_map] at hz
  obtain ⟨ok, -, rfl⟩ := hz
  exact ⟨rfl, rfl⟩

/-- **The comparison, outcome by outcome**: from any cache and any transcript of it, the Statement's verifier's
event is at most as likely as `BreaksD`'s after the chain and the six openings on the converted proof. -/
theorem hcmpK (x : LeanVM.Prover.Tree × PcsQuotient.Commitment) (a : PcsQuotient.Statement × PcsQuotient.Proof)
    (c : KeccakCalls.QueryCache) (tA : Transcript) (_ : Consistent tA c) :
    Pr{let v ← (simulateQ randomOracle (verV x a)).run' c}[EvK x a v tA] ≤
      Pr{let z ← (simulateQ randomOracle (contD (WK hc) pcsOpen (setc (phiS x) (conv0 a)) tA)).run' c}[
        BreaksDP (WK hc) (cWK hc) z] := by
  by_cases hr : RootsOK a.2.reduction
  · obtain ⟨hW, hH, hQ, hG⟩ := hr
    obtain ⟨rW, hW'⟩ := Option.isSome_iff_exists.mp hW
    obtain ⟨rH, hH'⟩ := Option.isSome_iff_exists.mp hH
    obtain ⟨rQ, hQ'⟩ := Option.isSome_iff_exists.mp hQ
    obtain ⟨rG, hG'⟩ := Option.isSome_iff_exists.mp hG
    have hv : verV x a = Prod.snd <$> contD (WK hc) pcsOpen (rootProofOf4 x.2 a.1 a.2.reduction, restOf a.2) tA :=
      verifyWithH_eq_contD (instR hc) x.2 a.1 a.2 rW rH rQ rG hW' hH' hQ' hG' tA
    rw [hv, run'_map, prEvent_map]
    show _ ≤ Pr{let z ← (simulateQ randomOracle (contD (WK hc) pcsOpen
      (rootProofOf4 x.2 a.1 a.2.reduction, restOf a.2) tA)).run' c}[BreaksDP (WK hc) (cWK hc) z]
    refine prEvent_mono_of_support _ _ _ fun z hz hev => ?_
    obtain ⟨hπ, htA⟩ := support_contD _ _ _ _ (support_simulateQ_run'_subset _ _ _ hz)
    refine ⟨hev.1, fun g hg hs => hev.2 ?_⟩
    rw [htA, hπ] at hg
    rw [hπ] at hs
    exact extracts_of_mem hc a x.2 tA rW hW' g hg hs
  · have h0 : Pr{let v ← (simulateQ randomOracle (verV x a)).run' c}[EvK x a v tA] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ fun v hv hev => by
        have := verifyWithH_reject x.2 a.1 a.2 hr v (support_simulateQ_run'_subset _ _ _ hv)
        rw [this] at hev
        exact Bool.false_ne_true hev.1
    rw [h0]
    exact bot_le

end PcsKS

namespace Soundness

open QuotientRpm QuotientSecurity Compose ComposePcs LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge.Pcs SoundPcs PcsKS

/-- The setup's Keccak-256 queries: the tree's `2^20` and the out-of-domain point's `24`. -/
def setupQueries : ℕ := 2 ^ 20 + 24

/-- The setup's calls of `π` (`E2ECompleteness.Pcs.Cost.comCost 24`: `5 · 2^19` for the tree, `24` for the point). -/
def setupPermCalls : ℕ := E2ECompleteness.Pcs.Cost.comCost 24

/-- The verifier's calls of `π`: the reduction's `10`, each opening's `vOpen`. -/
def verifierPermCalls : ℕ := 10 + 6 * E2ECompleteness.Pcs.Cost.vOpen

/-- **The knowledge-soundness error** for an adversary of `Q` calls of `π`, `π⁻¹`: `SoundPcs`'s bound for the
deterministic adversary of the transfer (`2^20 + 24 + Q` queries: it recomputes the public setup), and the
transfer's term. -/
noncomputable def ksBound (Q : ℕ) : ℝ≥0∞ :=
  deployedBound (setupQueries + Q) + ((setupPermCalls + Q + verifierPermCalls : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508

/-- **Knowledge soundness of the deployed membership proof in the random-permutation model**, for the Statement's
extractor and experiment, with no hypothesis: an adversary of at most `Q` calls of `π`, `π⁻¹` makes the verifier
accept while the extractor (reading the setup's tree and the adversary's transcript) outputs no secret of the
statement with probability at most `ksBound Q`. -/
theorem knowledgeSoundness : PcsQuotient.KnowledgeSoundness ksBound := by
  intro A Q hQ
  have hc : IsCantor PcsBridge.statementConsts.beta := Bridge.isCantor_statementConsts
  have hτ : Reduce.RowVanishing PcsBridge.statementConsts 22 :=
    E2ECompleteness.Pcs.rowVanishing_stmt E2ECompleteness.Pcs.constants
  have hSQ : IsTotalQueryBound setupS setupQueries := by
    have h := setupPcs_queryBound wcol
    rw [setupPcs_eq] at h
    exact (isQueryBound_map_iff _ _ _ _ _).mp h
  have hSπ : Common.QueryCostAtMost setupS LeanVM.Rpm.hashBlocks setupPermCalls :=
    E2ECompleteness.Pcs.Cost.qc_commitmentWithH 24 _
  obtain ⟨A', hA', hle⟩ := rpm_le_romG EvK lookInv_EvK setupS E2ECompleteness.Pcs.hOnly_setupWithH
    setupQueries setupPermCalls hSQ hSπ (advS A) Q (fun s => hQ s.2) verV
    (fun s a => (LeanVM.Rpm.duplexVm_iff_duplexP _ _).mpr
      (E2ECompleteness.Pcs.disc_verifyWithH 22 s.2 a.1 a.2 []))
    verifierPermCalls (fun s a => E2ECompleteness.Pcs.Cost.cost_verifyWithH 22 s.2 a.1 a.2)
  refine (prEvent_soundness_le A).trans (hle.trans (add_le_add ?_ le_rfl))
  refine (le_dExp (WK hc) pcsOpen (cWK hc) setupS phiS wcol setupPcs_eq conv0 A' verV EvK
    (hcmpK hc)).trans ?_
  exact knowledgeSoundness_deployed_pcsM hc deployedSigma (WK hc) wcol
    (claimsMatchK hc (WK hc) (fun _ => rfl) hτ) (fun _ => conv0 <$> A') (setupQueries + Q)
    (fun _ => (isQueryBound_map_iff _ _ _ _ _).mpr hA')

end Soundness

/-- info: 'Soundness.knowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.knowledgeSoundness
