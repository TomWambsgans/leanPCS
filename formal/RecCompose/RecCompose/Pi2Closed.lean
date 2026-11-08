-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's completeness (`formal/RecStatement`'s
-- `RecCompleteness2`, `RecCompletenessWith`) at π1-rec3's prover (`Pi2P1`), the witness's completeness closed.
import RecCompose.Pi2SimEnd
import RecCompose.Pi2Witness

/-!
# π2's completeness, closed

`Pi2SimEnd`'s end theorems with the compiled circuit's completeness proved (`Pi2W.pi2WitnessComplete`, from the
compiler's completeness checks): **`recCompleteness2_pi2_rec3_final`**, **`recCompleteness_pi2_rec3_final_fs`**. The
inputs left: the run-checked `Pi2Circuits D`, `hroots`, `GraphsAgree`, `Pi2ViewChecked C`; π1-rec3's prover's named
facts (`Pi1ProverFacts D P1 P1k`, `Pi2P1`); `Pi2AlphaFresh εα` (`α`'s input not hashed before its query but with
probability `εα`; proved at `alphaBound` in `Pi2AlphaEnd`); and for the end-to-end form the Fiat–Shamir-heuristic
premises `Pi1CompletenessKeccak`, `Pi1HazardKeccakHonest`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open Pi2S Pi2K Pi2P Pi2E Pi2G
open scoped ENNReal

/-- **π2's completeness at π1-rec3's prover**: from the run-checked inputs, π1's prover's named facts and `α`'s
freshness only. -/
theorem recCompleteness2_pi2_rec3_final {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree)
    {P1 : Pi1Prover D} {P1k : Pi1ProverK D} (hP1 : Pi1ProverFacts D P1 P1k) {εα : ℝ≥0∞}
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα) :
    RecCompleteness2 D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' Cost2.pi2RunN εα (tFreshBound2 Cost2.pi2RunN εα)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_pi2_rec3_closed hD C hchk hroots hg hP1 hal (Pi2W.pi2WitnessComplete hD C hchk)

/-- **The recursive verifier's completeness end to end** at π1-rec3's prover. -/
theorem recCompleteness_pi2_rec3_final_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree)
    {P1 : Pi1Prover D} {P1k : Pi1ProverK D} (hP1 : Pi1ProverFacts D P1 P1k) {εα : ℝ≥0∞}
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα)
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D P1 δ1) (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' Cost2.pi2RunN εα (tFreshBound2 Cost2.pi2RunN εα)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_pi2_rec3_closed_fs hD C hchk hroots hg hP1 hal (Pi2W.pi2WitnessComplete hD C hchk) δ1 δh h1 hh

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.recCompleteness2_pi2_rec3_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness2_pi2_rec3_final

/-- info: 'RecCompose.Pi2Sim.recCompleteness_pi2_rec3_final_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness_pi2_rec3_final_fs
