-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's completeness (`formal/RecStatement`'s
-- `RecCompleteness2`, `RecCompletenessWith`) at π2v4 over π1-rec4's prover (`Pi2P1`'s abstract program and named
-- facts): `Pi2ProbEnd`'s end theorem with its named facts proved (`Pi2SimExp`, `Pi2RunDuplex`, `Pi2RunCost`,
-- `Pi2AlphaFresh`, `Pi2AlphaG`), `CompleteCouplings`' end-to-end composition.
import RecCompose.Pi2ProbEnd
import RecCompose.Pi2SimExp
import RecCompose.Pi2RunDuplex
import RecCompose.Pi2AlphaFresh
import RecCompose.Pi2AlphaG
import RecCompose.CompleteCouplings

/-!
# π2's completeness (π2v4), closed but for the other helpers' inputs

* **`recCompleteness2_pi2_closed`**: `RecCompleteness2 D P1 (pi2Prover D C.G Fa.pubOf nonceFuel) delta2Closed` at the
  real deployment (`hD`), for π1-rec4's prover `P1` with its two-call program `P1k` (`Pi1ProverFacts`: `P1` is `P1k`
  over `π`, `P1k` disciplined, of at most `2^47` block calls, hashing inputs shorter than `2^26` bytes), from
  `Pi2Pi1Openings D` (π1's three claims, as π1-rec4's graph makes them, open in the contract), `Pi2WitnessExists D C Fa`
  (the circuit compiler's completeness) and a non-hole position of π2's circuit (`t`'s count). The staged run's
  experiment (`Pi2SimExp.pi2ExperimentLe_of`), duplex shape (`pi2RunDuplex_of`), block count (`pi2RunCost_of`,
  `pi2RunN ≤ 2^50`), `α`'s freshness (`alphaFresh_of`, `alphaBound ≤ 2^-204`) and `t`'s (`pi2TFresh_ofG`,
  `tFreshBound2 ≤ 2^-200`) are proved.
* **`delta2Closed_le`**: `delta2Closed ≤ 2^-164` (about `2^-164.4`: `t`'s bad set `(10 · 2^24 + 1) / 2^192` and the copy
  argument's `2^25 / 2^192` dominate).
* **`recCompleteness_pi2_closed_fs`**: the recursive verifier's completeness end to end (`recCompleteness_end_fs`), with
  the Fiat–Shamir premises `Pi1CompletenessKeccak D P1 δ1`, `Pi1HazardKeccakHonest D P1 δh`: error `δ1 + δh +
  delta2Closed`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open UniKeccakComplete.Prob.TFresh (hc_of_qc)
open Pi2S Pi2K Pi2P Pi2E Pi2G
open scoped ENNReal

/-- **π2's completeness error** (π2v4): `delta2V4` at the staged run's block count `pi2RunN`, `α`'s bound `alphaBound`
and `t`'s `tFreshBound2 pi2RunN alphaBound`. -/
noncomputable def delta2Closed : ℝ≥0∞ :=
  delta2V4 Cost2.pi2RunN alphaBound (tFreshBound2 Cost2.pi2RunN alphaBound)

/-- **`α`'s freshness where the graph accepted**, at π1-rec4's prover. -/
theorem pi2AlphaFreshG_of {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    {P1 : Pi1Prover D} {P1k : Pi1ProverK D} (hP1 : Pi1ProverFacts D P1 P1k) :
    Pi2AlphaFreshG D C Fa P1k alphaBound := fun input rows q hfit hrel ↦
  alphaFresh_of hD C Fa (P1k input rows q) input (hP1.hashShort input rows q hfit hrel)
    (hc_of_qc (hP1.cost input rows q hfit hrel))

/-- **`t`'s freshness where the graph accepted**, at π1-rec4's prover. -/
theorem pi2TFreshG_of {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    {P1 : Pi1Prover D} {P1k : Pi1ProverK D} (hP1 : Pi1ProverFacts D P1 P1k) :
    Pi2TFreshG D C Fa P1k (tFreshBound2 Cost2.pi2RunN alphaBound) := fun input rows q hfit hrel ↦
  pi2TFresh_ofG C Fa (P1k input rows q) input (pi2RunCost_of hD C Fa hP1.cost input rows q hfit hrel) GAccA
    (pi2AlphaFreshG_of hD C Fa hP1 input rows q hfit hrel)

/-- **π2's completeness at π1-rec4's prover** (π2v4), the staged run's analysis proved: from π1's prover's named
facts, π1's claims' openings, the witness's existence and a non-hole position. -/
theorem recCompleteness2_pi2_closed {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) {P1 : Pi1Prover D} {P1k : Pi1ProverK D}
    (hP1 : Pi1ProverFacts D P1 P1k) (hpo : Pi2Pi1Openings D) (hwc : Pi2WitnessExists D C Fa)
    (hnh : ∀ roots, ∃ i < (C.G roots).N, ¬ (C.G roots).IsHole i) :
    RecCompleteness2 D P1 (pi2Prover D C.G Fa.pubOf PcsQuotient.nonceFuel) delta2Closed :=
  recCompleteness2_pi2_v4 C Fa hD hroots P1 P1k (pi2ExperimentLe_of hD C Fa hwc hP1.overPerm)
    (pi2RunDuplex_of D C Fa hP1.disc) (pi2RunCost_of hD C Fa hP1.cost) (pi2AlphaFreshG_of hD C Fa hP1)
    (pi2TFreshG_of hD C Fa hP1) hpo hwc hnh

/-- **`δ2` in bits**: below `2^-164`. -/
theorem delta2Closed_le : delta2Closed ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 :=
  delta2V4_le Cost2.pi2RunN_le (alphaBound_le.trans (E2ECompleteness.inv_pow_le_inv_pow (by norm_num)))
    ((tFreshBound2_le Cost2.pi2RunN_le alphaBound_le201).trans (E2ECompleteness.inv_pow_le_inv_pow (by norm_num)))

/-- **The recursive verifier's completeness end to end** at π1-rec4's prover (π2v4): error `δ1 + δh + delta2Closed`,
`delta2Closed ≤ 2^-164`. -/
theorem recCompleteness_pi2_closed_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) {P1 : Pi1Prover D} {P1k : Pi1ProverK D}
    (hP1 : Pi1ProverFacts D P1 P1k) (hpo : Pi2Pi1Openings D) (hwc : Pi2WitnessExists D C Fa)
    (hnh : ∀ roots, ∃ i < (C.G roots).N, ¬ (C.G roots).IsHole i)
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D P1 δ1) (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 (pi2Prover D C.G Fa.pubOf PcsQuotient.nonceFuel))
      (δ1 + δh + delta2Closed) :=
  recCompleteness_end_fs D hD P1 _ _ (recCompleteness2_pi2_closed hD C Fa hroots hP1 hpo hwc hnh) δ1 δh h1 hh

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.recCompleteness2_pi2_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness2_pi2_closed

/-- info: 'RecCompose.Pi2Sim.delta2Closed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.delta2Closed_le

/-- info: 'RecCompose.Pi2Sim.recCompleteness_pi2_closed_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness_pi2_closed_fs
