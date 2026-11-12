-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The grinding for π2's staged run (`Pi2ProbStaged`'s
-- `rejectGood_of_pot`, `pot_of_rejects`) with the staged run at pure functions (`Pi2SimAt`) and `Pi2Accepts.pi2_accepts`;
-- uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the
-- logged random oracle, mumbai's proof-of-work potential.
import RecCompose.Pi2SimAt

/-!
# The core at pure functions (π2v4)

* **`rejects_at_good`**: at pure `(Ht, Ft)`, on a staged run whose graph accepts and whose contract rejects at good
  challenges (`GoodRej`: the triple off `badSet2`, `t` off `badT2`, `ρ` off `badR2`), one of π2's four openings fails
  its proof of work: `stagedAt`'s facts (`runAt_staged`, `cAt_fst`, `stagedAt_good`) put the honest prover's challenges
  in the event, and `pi2_accepts` (the witness by `Pi2WitnessExists`, π1's claims by `Pi2Pi1Openings`) says its proof,
  if any, is accepted. For every π1 prover `P1k`.
* **`rejectGood_pi2`**: the grinding (`Holds3.rejectGood`): `GoodRej` with probability at most
  `N · (1 − 2^-17)^nonceFuel`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open E2ECompleteness (ro runAt)
open Pi2S Pi2K Pi2P Pi2E Pi2G
open scoped ENNReal

open Classical in
/-- **The core at pure `(Ht, Ft)`**, for any π1 prover: on a staged run whose graph accepts and whose contract
rejects at good challenges, one of π2's openings fails its proof of work. -/
theorem rejects_at_good {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hwc : Pi2WitnessExists D C Fa) (hpo : Pi2Pi1Openings D)
    (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) (input : Vector UInt8 32)
    (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) (z : Z2)
    (hz : runAt Ht Ft (pi2Staged D C Fa P1k input).run = z) (hev : GoodRej C.G z) :
    PcsFails Ht Ft PcsQuotient.nonceFuel := by
  rw [runAt_staged] at hz
  obtain ⟨ha1, ha2, hB, hT, hR⟩ := hev
  cases hp1 : runAt Ht Ft P1k with
  | none =>
    rw [hp1] at hz
    subst hz
    have hf : (stagedAt Ht Ft D C Fa input none).1.1.1 = false := rfl
    rw [hf] at ha1
    cases ha1
  | some p1 =>
    rw [hp1] at hz
    have hgr : Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Ht) Ft D (rootsH D Ht Ft).pi1 input p1) =
        true := by
      rw [← hz] at ha1
      exact (cAt_fst Ht Ft D C input _ _ p1 rfl).symm.trans ha1
    have hgood := pi2Choice_good (hwc _ _ _ (graphChecks_of_verifierH hgr))
    obtain ⟨h1, hz2, hzt, hzp, hzr⟩ := stagedAt_good Ht Ft D C Fa input p1 hD hgood
    rw [hz] at h1 hz2 hzt hzp hzr
    rw [h1, expW2_some] at ha2
    cases hpr : Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Ht) Ft D C.G Fa.pubOf PcsQuotient.nonceFuel input p1) with
    | none => exact pi2Prover_none Fa Ht Ft _ input p1 hpr
    | some proof =>
      exfalso
      rw [hpr] at ha2
      dsimp only at ha2
      rw [hzp, hz2, hzt] at hT
      rw [hz2] at hB
      rw [hzr] at hR
      have hbad : ¬ BadCopy (C.G (rootsH D Ht Ft)) (vwH D C Fa Ht Ft input p1).2
          (Fa.pubOf (rootsH D Ht Ft) (publicScalarsOf input.toList (vwH D C Fa Ht Ft input p1).1))
          (outAt Ht Ft D C Fa input p1).inputs.α (outAt Ht Ft D C Fa input p1).inputs.β
          (outAt Ht Ft D C Fa input p1).inputs.γ :=
        fun hb ↦ hB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
      have ht : ¬ BadT (C.G (rootsH D Ht Ft)) (vwH D C Fa Ht Ft input p1).2 (outAt Ht Ft D C Fa input p1).inputs.α
          (outAt Ht Ft D C Fa input p1).inputs.β (outAt Ht Ft D C Fa input p1).inputs.γ
          (outAt Ht Ft D C Fa input p1).inputs.t :=
        fun hb ↦ hT ⟨hgood.2.1, hbad, hb⟩
      obtain ⟨h3, o1, o2, o3⟩ := hpo Ht Ft input p1 hgr
      have hacc := pi2_accepts D hD C Fa Ft Ht PcsQuotient.nonceFuel input p1 hgood h3 (logN_G Fa _)
        (by rw [Fa.logW]; rfl) proof hpr hroots hbad ht hR ⟨o1, o2, o3⟩
      exact absurd (hacc.symm.trans ha2) (by decide)

/-- **The grinding for π2** (`Holds3.rejectGood`): the staged run rejected at good challenges (`GoodRej`), the graph
accepting, with probability at most `N · (1 − 2^-17)^nonceFuel`. -/
theorem rejectGood_pi2 {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hwc : Pi2WitnessExists D C Fa) (hpo : Pi2Pi1Openings D)
    (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) (input : Vector UInt8 32) {N : ℕ}
    (hcost : Common.QueryCostAtMost (pi2Staged D C Fa P1k input).run hashBlocks N) :
    Pr{let z ← (simulateQ ro (pi2Staged D C Fa P1k input).run).run' ∅}[GoodRej C.G z] ≤
      (N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel :=
  rejectGood_of_pot _ _ hcost fun ℓ z hz hev ↦
    pot_of_rejects _ (GoodRej C.G)
      (fun Ht Ft hev' ↦ rejects_at_good hD C Fa hroots hwc hpo P1k input Ht Ft _ rfl hev') ℓ z hz hev

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.rejectGood_pi2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.rejectGood_pi2
