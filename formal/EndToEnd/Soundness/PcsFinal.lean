-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Soundness/{Final,RpmV}.lean` (at commit abe22812: the end theorem
-- from the random-permutation transfer and the composition) to the EIP's PCS claims (`formal/SoundPcs`).
import Soundness.PcsGame

/-!
# Knowledge soundness of the deployed membership proof, for any F1 parameters that match the claims

**`Soundness.knowledgeSoundness_of`**: for F1's parameters `P` (`Kc3.Params`) whose three rounds are sound
(`RoundsSound P`, from the pole condition: `roundsSound_of`) at round error at most `2^-164`, a match `M` of the
Statement's claims with `P`'s verifier at the Statement's wiring table `wcol` (`ClaimsMatch (pcsWire2 P) wcol`), and
`P`'s satisfied witness tables, read by `M.readW`, spelling a secret (`StackRel P M.readW`), the Statement's
extractor and experiment have error at most `ksBound Q`:

1. the Statement's experiment breaks only where the transfer game's event holds (`prEvent_soundness_le`,
   `PcsGame.lean`);
2. the game moves to mumbai's two-oracle model, against one deterministic adversary `A'` of at most
   `2^20 + 24 + Q` queries, less `(setupPermCalls + Q + verifierPermCalls)² / 2^508` (`rpm_le_romG`, `PcsRpm.lean`);
3. there it is bounded by `SoundPcs`'s deployed run of the converted adversary (`le_dExp`, `PcsDExp.lean`): outcome
   by outcome, the Statement's verifier is the deployed run's chain and three openings (`verifyWithH_eq_contD`) or
   rejects (`verifyWithH_reject`), and `SoundPcs`'s extractor list holds a witness only where the extraction succeeds
   (`extracts_of_mem`) (`hcmpK`);
4. the deployed run breaks with probability at most `SoundPcs.deployedBound`
   (`SoundPcs.knowledgeSoundness_deployed_pcs_of` at `wcol`, whose setup is the Statement's: `setupPcs_eq`).

`ksBound Q = deployedBound (2^20 + 24 + Q) + (setupPermCalls + Q + verifierPermCalls)² / 2^508`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace PcsKS

open QuotientRpm QuotientSecurity Compose ComposePcs LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge.Pcs SoundPcs

/-- The setup's commitment as `SoundPcs` reads it: its root's bytes and its out-of-domain answer. -/
def phiS (x : LeanVM.Prover.Tree × PcsQuotient.Commitment) : QuotientRpm.Bytes32 × E := (toB x.2.root, x.2.ood)

theorem run'_map {α β : Type} (f : α → β) (X : OracleComp KeccakCalls α) (c : KeccakCalls.QueryCache) :
    (simulateQ randomOracle (f <$> X)).run' c = f <$> (simulateQ randomOracle X).run' c := by
  rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]

theorem support_contD {P : Kc3.Params E} (W : Wire2 P) (O : OpenSpec) (po : RootProof2 E × Rest)
    (tA : Transcript) {z : S0 × Bool} (hz : z ∈ support (contD W O po tA)) :
    z.1.π = po.1 ∧ z.1.tA = tA := by
  unfold contD at hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨ch, -, hz⟩ := hz
  rw [support_map] at hz
  obtain ⟨ok, -, rfl⟩ := hz
  exact ⟨rfl, rfl⟩

variable (P : Kc3.Params E) (readW : Column 24 → P.Msg₁) (hrel : StackRel P readW)

include hrel in
/-- **The comparison, outcome by outcome**: from any cache and any transcript of it, the Statement's verifier's
event is at most as likely as `BreaksD`'s after the chain and the three openings on the converted proof. -/
theorem hcmpK (x : LeanVM.Prover.Tree × PcsQuotient.Commitment) (a : PcsQuotient.Statement × PcsQuotient.Proof)
    (c : KeccakCalls.QueryCache) (tA : Transcript) (_ : Consistent tA c) :
    Pr{let v ← (simulateQ randomOracle (verV x a)).run' c}[EvK x a v tA] ≤
      Pr{let z ← (simulateQ randomOracle (contD (pcsWire2 P) pcsOpen (setc (phiS x) (conv0 a)) tA)).run' c}[
        BreaksDP (pcsWire2 P) (cWK readW) z] := by
  by_cases hr : RootsOK a.2.reduction
  · obtain ⟨hW, hT⟩ := hr
    obtain ⟨rW, hW'⟩ := Option.isSome_iff_exists.mp hW
    obtain ⟨rT, hT'⟩ := Option.isSome_iff_exists.mp hT
    have hv : verV x a = Prod.snd <$> contD (pcsWire2 P) pcsOpen
        (rootProofOf2 x.2 a.1 a.2.reduction, restOf a.2) tA :=
      verifyWithH_eq_contD P x.2 a.1 a.2 rW rT hW' hT' tA
    rw [hv, run'_map, prEvent_map]
    show _ ≤ Pr{let z ← (simulateQ randomOracle (contD (pcsWire2 P) pcsOpen
      (rootProofOf2 x.2 a.1 a.2.reduction, restOf a.2) tA)).run' c}[BreaksDP (pcsWire2 P) (cWK readW) z]
    refine prEvent_mono_of_support _ _ _ fun z hz hev => ?_
    obtain ⟨hπ, htA⟩ := support_contD _ _ _ _ (support_simulateQ_run'_subset _ _ _ hz)
    refine ⟨hev.1, fun g hg hs => hev.2 ?_⟩
    rw [htA, hπ] at hg
    rw [hπ] at hs
    exact extracts_of_mem readW hrel a x.2 tA rW hW' g hg hs
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

/-- The setup's calls of `π` (`VH.Cost.comCost 24`: `5 · 2^19` for the tree, `24` for the point). -/
def setupPermCalls : ℕ := VH.Cost.comCost 24

/-- The verifier's calls of `π`: the reduction's `8`, each of the three openings' `vOpen`. -/
def verifierPermCalls : ℕ := 8 + 3 * VH.Cost.vOpen

/-- **The knowledge-soundness error** for an adversary of `Q` calls of `π`, `π⁻¹`: `SoundPcs`'s bound for the
deterministic adversary of the transfer (`2^20 + 24 + Q` queries: it recomputes the public setup), and the
transfer's term. -/
noncomputable def ksBound (Q : ℕ) : ℝ≥0∞ :=
  deployedBound (setupQueries + Q) + ((setupPermCalls + Q + verifierPermCalls : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508

/-- **Knowledge soundness of the deployed membership proof in the random-permutation model, for any F1 parameters
that match the claims**: an adversary of at most `Q` calls of `π`, `π⁻¹` makes the verifier accept while the
extractor (reading the setup's tree and the adversary's transcript) outputs no secret of the statement with
probability at most `ksBound Q`. -/
theorem knowledgeSoundness_of (P : Kc3.Params E) (hR : RoundsSound P)
    (hre : P.roundError ≤ ((1 / 2 ^ 164 : ℝ≥0) : ℝ≥0∞)) (M : ClaimsMatch (pcsWire2 P) wcol)
    (hrel : StackRel P M.readW) (hσ : SigmaSize) : PcsQuotient.KnowledgeSoundness ksBound := by
  intro A Q hQ
  have hSQ : IsTotalQueryBound setupS setupQueries := by
    have h := setupPcs_queryBound wcol
    rw [setupPcs_eq hσ] at h
    exact (isQueryBound_map_iff _ _ _ _ _).mp h
  have hSπ : Common.QueryCostAtMost setupS LeanVM.Rpm.hashBlocks setupPermCalls :=
    VH.Cost.qc_commitmentWithH 24 _
  obtain ⟨A', hA', hle⟩ := rpm_le_romG EvK lookInv_EvK setupS VH.hOnly_setupWithH
    setupQueries setupPermCalls hSQ hSπ (advS A) Q (fun s => hQ s.2) verV
    (fun s a => (LeanVM.Rpm.duplexVm_iff_duplexP _ _).mpr
      (VH.disc_verifyWithH 22 s.2 a.1 a.2 []))
    verifierPermCalls (fun s a => VH.Cost.cost_verifyWithH 22 s.2 a.1 a.2)
  refine (prEvent_soundness_le A).trans (hle.trans (add_le_add ?_ le_rfl))
  refine (le_dExp (pcsWire2 P) pcsOpen (cWK M.readW) setupS phiS wcol (setupPcs_eq hσ) conv0 A' verV EvK
    (hcmpK P M.readW hrel)).trans ?_
  exact knowledgeSoundness_deployed_pcs_of (pcsWire2 P) hR hre wcol M (fun _ => conv0 <$> A')
    (setupQueries + Q) (fun _ => (isQueryBound_map_iff _ _ _ _ _).mpr hA')

end Soundness

/-- info: 'Soundness.knowledgeSoundness_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.knowledgeSoundness_of
