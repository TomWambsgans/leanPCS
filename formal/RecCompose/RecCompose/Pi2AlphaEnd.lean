-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's completeness (`formal/RecStatement`'s
-- `RecCompleteness2`, `RecCompletenessWith`) at π1-rec3's prover (`Pi2P1`'s abstract program and named facts) with
-- `α`'s freshness proved: `Pi2AlphaG` (`Holds3`, the staged bounds conditioned on the graph's acceptance),
-- `Pi2AlphaFresh` (`alphaFresh_of`), `Pi2AlphaSupport` (`accA_pi2`, `accB_pi2`), and `Pi2SimEnd`'s, `Pi2Closed`'s
-- ingredients.
import RecCompose.Pi2AlphaFresh
import RecCompose.Pi2AlphaG
import RecCompose.Pi2Closed

/-!
# π2's completeness, closed but for the run-checked inputs and π1's prover's named facts

`Pi2AlphaFresh εα` (`Pi2TFreshPi2`) asks `α`'s input to be fresh on every outcome of stage A. Off π1-rec3's graph
accepting (π1's prover returning none, or a proof whose public values do not match the reads), `pi2Staged`'s `α` input
is `fixLen`'s `608` zeros, which nothing here shows π1-rec3's prover does not hash. Those outcomes are rejected (the
verdict's first component is the graph's), so `α`'s and `t`'s freshness are asked only where the graph accepted
(`Pi2AlphaG.Holds3`, `GAcc`), and there they are proved:

* **`holds3_pi2_of`**: `Holds3` of `pi2Staged … (P1k input rows q)` at `G = GAcc`, `εα = alphaBound` (`alphaFresh_of`),
  `εt = tFreshBound2 pi2RunN alphaBound` (`pi2TFresh_ofG`), from `Pi1ProverFacts D P1 P1k`;
* **`recCompleteness2_pi2_rec3_closed`**: `RecCompleteness2 D P1 (pi2Prover …) δ2` from `Pi2Circuits D`, `hroots`,
  `GraphsAgree`, `Pi2ViewChecked C` and `Pi1ProverFacts D P1 P1k` only, `δ2 = delta2' pi2RunN alphaBound
  (tFreshBound2 pi2RunN alphaBound) (pi2RunN · missProb 17 ^ nonceFuel) ≤ 2^-164` (**`delta2_alpha_le`**; about
  `2^-164.7`: the copy argument's `2^-166`, `t`'s `2^-165` dominate);
* **`recCompleteness_pi2_rec3_closed_fs`**: the recursive verifier's completeness end to end (`recCompleteness_end_fs`
  at the real deployment), with the Fiat–Shamir premises `Pi1CompletenessKeccak D P1 δ1`, `Pi1HazardKeccakHonest D P1 δh`.

These are the headline completeness theorems for the Keccak VM's recursion. π1-rec3's prover enters only through
`Pi1ProverFacts` (`Pi2P1`): a Lean transcription of the Keccak π1-rec3 prover discharges them by its commutation with
simulation, its duplex discipline, its block count (`≤ 2^47`) and its hash census (inputs `< 2^26` bytes). A prover
whose Fiat–Shamir is the pure `keccak256` (as π1-rec3's graph hashes, so that `Pi1CompletenessKeccak` is the honest
prover's Fiat–Shamir heuristic) is one such `P1k`: its Fiat–Shamir hashes are no queries.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Alpha

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open Pi2S Pi2K Pi2P Pi2E Pi2G Pi2O
open scoped ENNReal

/-- **The staged run's `Holds3`** at π1-rec3's prover, `α`'s and `t`'s freshness where the graph accepted. -/
theorem holds3_pi2_of {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree) {P1 : Pi1Prover D} {P1k : Pi1ProverK D}
    (hP1 : Pi1ProverFacts D P1 P1k) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) (hfit : D.pi1.shape.RowsFit rows) (hrel : D.pi1.HonestRelation D.flock rows input q) :
    (pi2Staged D C (pi2Facts hD C hchk) (P1k input rows q) input).Holds3 D P1
      (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel) input rows q 608 (badSet2 C.G) (badT2 C.G)
      Pi2Sim.GAcc (fun b : StB ↦ Pi2Sim.GAcc b.a) (2 ^ 25 + 36) (9 * 2 ^ 24) Cost2.pi2RunN Pi2Sim.alphaBound
      (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
      ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) where
  experiment := Pi2Sim.pi2ExperimentLe_of hD C (pi2Facts hD C hchk) (Pi2W.pi2WitnessComplete hD C hchk) hP1.overPerm
    input rows q hfit hrel
  duplex := pi2RunDuplex_of D C _ hP1.disc input rows q hfit hrel
  cost := pi2RunCost_of hD hg C _ hP1.cost input rows q hfit hrel
  L_ne := by norm_num
  inp_length _ := fixLen_length 608 _
  alphaFresh := Pi2Sim.alphaFresh_of hD hg C hchk hP1.cost hP1.hashShort input rows q hfit hrel
  accA := fun a ha s₁ s₂ s₃ c z hz ↦ Pi2Sim.accA_pi2 C (pi2Facts hD C hchk) input (P1k input rows q) a ha s₁ s₂ s₃ c z hz
  accB := fun b hb st c z hz ↦ Pi2Sim.accB_pi2 C input b hb st c z hz
  badCard p := card_badCopy_pi2 (pi2Facts hD C hchk) p.1 p.2.1 p.2.2
  badTCard fp := card_badT_pi2 (pi2Facts hD C hchk) fp.1.1 fp.1.2.1 fp.1.2.2 fp.2.1 fp.2.2.1 fp.2.2.2
    (nonHole_pi2 C hchk (pi2Facts hD C hchk) fp.1.1)
  tFresh := pi2TFresh_ofG C (pi2Facts hD C hchk) (P1k input rows q) input
    (pi2RunCost_of hD hg C _ hP1.cost input rows q hfit hrel) Pi2Sim.GAcc
    (Pi2Sim.alphaFresh_of hD hg C hchk hP1.cost hP1.hashShort input rows q hfit hrel)
  rejectGood := Pi2Sim.rejectGood_pi2_good hD C (pi2Facts hD C hchk) hroots (Pi2W.pi2WitnessComplete hD C hchk)
    (pi2Pi1Openings hD C hchk hroots hg) (P1k input rows q) input
    (pi2RunCost_of hD hg C _ hP1.cost input rows q hfit hrel)

/-- **π2's completeness at π1-rec3's prover**, from the run-checked inputs (`Pi2Circuits D`, `hroots`, `GraphsAgree`,
`Pi2ViewChecked C`) and π1's prover's named facts (`Pi1ProverFacts D P1 P1k`) only. -/
theorem recCompleteness2_pi2_rec3_closed {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree)
    {P1 : Pi1Prover D} {P1k : Pi1ProverK D} (hP1 : Pi1ProverFacts D P1 P1k) :
    RecCompleteness2 D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_of_staged3 fun input rows q hfit hrel ↦
    ⟨_, _, _, _, _, holds3_pi2_of hD C hchk hroots hg hP1 input rows q hfit hrel⟩

/-- **δ2 in bits**: below `2^-164` (`alphaBound ≤ 2^-204`). -/
theorem delta2_alpha_le :
    delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
      ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 :=
  Pi2Sim.delta2_rec3_le Pi2Sim.alphaBound_le201

/-- **The recursive verifier's completeness end to end** at π1-rec3's prover, from the run-checked inputs, π1's
prover's named facts and the Fiat–Shamir premises (`Pi1CompletenessKeccak D P1 δ1`, `Pi1HazardKeccakHonest D P1 δh`):
error `δ1 + δh + δ2`, `δ2 ≤ 2^-164`. -/
theorem recCompleteness_pi2_rec3_closed_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree)
    {P1 : Pi1Prover D} {P1k : Pi1ProverK D} (hP1 : Pi1ProverFacts D P1 P1k)
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D P1 δ1) (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_end_fs D hD P1 _ _ (recCompleteness2_pi2_rec3_closed hD C hchk hroots hg hP1) δ1 δh h1 hh

end RecCompose.Pi2Alpha

/-- info: 'RecCompose.Pi2Alpha.recCompleteness2_pi2_rec3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Alpha.recCompleteness2_pi2_rec3_closed

/-- info: 'RecCompose.Pi2Alpha.delta2_alpha_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Alpha.delta2_alpha_le

/-- info: 'RecCompose.Pi2Alpha.recCompleteness_pi2_rec3_closed_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Alpha.recCompleteness_pi2_rec3_closed_fs
