-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's completeness (`formal/RecStatement`'s
-- `RecCompleteness2`, `RecCompletenessWith`) at π1-rec3's prover (`Pi2P1`'s abstract program and named facts),
-- assembled from `Pi2SimExp` (`Pi2ExperimentLe`), `Pi2SimCore` (the grinding without `Pi2RunAt`), `Pi2Chain` and
-- `Pi2TFreshPi2` (`Holds2`, `Pi2TFresh` from `Pi2AlphaFresh`), `Pi2CallsOpen` (`Pi2Pi1Openings`).
import RecCompose.Pi2SimCore
import RecCompose.Pi2TFreshPi2
import RecCompose.Pi2CallsOpen
import RecCompose.Pi2RunCost
import RecCompose.Pi2RunDuplex

/-!
# π2's completeness at π1-rec3's prover, the staged run's experiment and analysis proved

`P1 : Pi1Prover D` is π1-rec3's prover over the random permutation and `P1k : Pi1ProverK D` its two-call program, with
`Pi2P1`'s named facts (`Pi1ProverFacts D P1 P1k`: `P1` is `P1k` over `π`, `P1k` disciplined, of at most `2^47` block
calls, hashing short inputs). `Pi2ExperimentLe` is proved from `Pi1OverPerm` (`pi2ExperimentLe_of`), `Pi2RunAt` is not
needed (`rejectGood_pi2_good`), `Pi2Pi1Openings` is proved (`pi2Pi1Openings`), `Pi2TFresh` is proved from `Pi2RunCost`
and `Pi2AlphaFresh` (`pi2TFresh_of`), `Pi2HashBeforeAlpha` is replaced by `Pi2AlphaFresh`.

* **`holds2_pi2_of`**: `Pi2Staged.Holds2` of `pi2Staged … (P1k input rows q)` from `Pi1OverPerm`, `Pi2RunDuplex`,
  `Pi2RunCost N`, `Pi2AlphaFresh εα` and `Pi2WitnessComplete`;
* **`recCompleteness2_pi2_rec3`**: `RecCompleteness2 D P1 (pi2Prover …) (delta2' N εα (tFreshBound2 N εα)
  (N · missProb 17 ^ nonceFuel))`, below `2^-164` at `N ≤ 2^50`, `εα ≤ 2^-201` (`delta2_pi2_le2`);
* **`recCompleteness2_pi2_rec3_closed`**: the same with the duplex shape (`pi2RunDuplex_of`, from `Pi1Disc`) and the
  block count (`pi2RunCost_of`, from `Pi1Cost`, `N = pi2RunN ≤ 2^50`) proved; **`delta2_rec3_le`**: below `2^-164`;
* **`recCompleteness_pi2_rec3_fs`**, **`recCompleteness_pi2_rec3_closed_fs`**: the recursive verifier's completeness end
  to end.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open Pi2S Pi2K Pi2P Pi2E Pi2G Pi2O
open scoped ENNReal

/-- **The staged run's `Holds2`** at π1-rec3's prover. -/
theorem holds2_pi2_of {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree) {P1 : Pi1Prover D} {P1k : Pi1ProverK D}
    {N : ℕ} {εα : ℝ≥0∞} (hP : Pi1OverPerm D P1 P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) (hfit : D.pi1.shape.RowsFit rows)
    (hrel : D.pi1.HonestRelation D.flock rows input q) :
    (pi2Staged D C (pi2Facts hD C hchk) (P1k input rows q) input).Holds2 D P1
      (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel) input rows q 536 (badSet2 C.G) (badT2 C.G)
      (2 ^ 25 + 36) (2 ^ 27) N εα (tFreshBound2 N εα)
      ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) where
  experiment := pi2ExperimentLe_of hD C (pi2Facts hD C hchk) hwc hP input rows q hfit hrel
  duplex := hdup input rows q hfit hrel
  cost := hcost input rows q hfit hrel
  L_ne := by norm_num
  inp_length _ := fixLen_length 536 _
  alphaFresh := hal input rows q hfit hrel
  badCard p := card_badCopy_pi2 (pi2Facts hD C hchk) p.1 p.2.1 p.2.2
  badTCard fp := card_badT_pi2 (pi2Facts hD C hchk) fp.1.1 fp.1.2.1 fp.1.2.2 fp.2.1 fp.2.2.1 fp.2.2.2
    (nonHole_pi2 C hchk (pi2Facts hD C hchk) fp.1.1)
  tFresh := pi2TFresh_of C (pi2Facts hD C hchk) P1k hcost hal input rows q hfit hrel
  rejectGood := rejectGood_pi2_good hD C (pi2Facts hD C hchk) hroots hwc (pi2Pi1Openings hD C hchk hroots hg)
    (P1k input rows q) input (hcost input rows q hfit hrel)

/-- **π2's completeness at π1-rec3's prover**, from `Pi1OverPerm`, the duplex shape, the cost, `α`'s freshness and the
witness's completeness. -/
theorem recCompleteness2_pi2_rec3 {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree) {P1 : Pi1Prover D} {P1k : Pi1ProverK D}
    {N : ℕ} {εα : ℝ≥0∞} (hP : Pi1OverPerm D P1 P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk)) :
    RecCompleteness2 D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' N εα (tFreshBound2 N εα) ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_of_staged2 fun input rows q hfit hrel ↦
    ⟨_, _, _, holds2_pi2_of hD C hchk hroots hg hP hdup hcost hal hwc input rows q hfit hrel⟩

/-- **The recursive verifier's completeness end to end** at π1-rec3's prover. -/
theorem recCompleteness_pi2_rec3_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree) {P1 : Pi1Prover D} {P1k : Pi1ProverK D}
    {N : ℕ} {εα : ℝ≥0∞} (hP : Pi1OverPerm D P1 P1k)
    (hdup : Pi2RunDuplex D C (pi2Facts hD C hchk) P1k) (hcost : Pi2RunCost D C (pi2Facts hD C hchk) P1k N)
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D P1 δ1) (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' N εα (tFreshBound2 N εα)
        ((N : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_end_fs D hD P1 _ _
    (recCompleteness2_pi2_rec3 hD C hchk hroots hg hP hdup hcost hal hwc) δ1 δh h1 hh

/-! ## The duplex shape and the cost proved -/

/-- **π2's completeness at π1-rec3's prover**, the staged run's duplex shape (`pi2RunDuplex_of`) and block count
(`pi2RunCost_of`, `N = pi2RunN ≤ 2^50`) proved from `Pi1ProverFacts`: from `α`'s freshness and the witness's
completeness. -/
theorem recCompleteness2_pi2_rec3_closed {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree)
    {P1 : Pi1Prover D} {P1k : Pi1ProverK D} (hP1 : Pi1ProverFacts D P1 P1k) {εα : ℝ≥0∞}
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk)) :
    RecCompleteness2 D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' Cost2.pi2RunN εα (tFreshBound2 Cost2.pi2RunN εα)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness2_pi2_rec3 hD C hchk hroots hg hP1.overPerm (pi2RunDuplex_of D C _ hP1.disc)
    (pi2RunCost_of hD hg C _ hP1.cost) hal hwc

/-- **δ2 in bits**: below `2^-164` at `εα ≤ 2^-201`. -/
theorem delta2_rec3_le {εα : ℝ≥0∞} (ha : εα ≤ (2 : ℝ≥0∞)⁻¹ ^ 201) :
    delta2' Cost2.pi2RunN εα (tFreshBound2 Cost2.pi2RunN εα)
      ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 :=
  delta2_pi2_le2 Cost2.pi2RunN_le ha

/-- **The recursive verifier's completeness end to end** at π1-rec3's prover, the duplex shape and the cost proved. -/
theorem recCompleteness_pi2_rec3_closed_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree)
    {P1 : Pi1Prover D} {P1k : Pi1ProverK D} (hP1 : Pi1ProverFacts D P1 P1k) {εα : ℝ≥0∞}
    (hal : Pi2AlphaFresh D C (pi2Facts hD C hchk) P1k εα) (hwc : Pi2WitnessComplete D C (pi2Facts hD C hchk))
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D P1 δ1) (hh : Pi1HazardKeccakHonest D P1 δh) :
    RecCompletenessWith D (composeProver D P1 (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' Cost2.pi2RunN εα (tFreshBound2 Cost2.pi2RunN εα)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_end_fs D hD P1 _ _ (recCompleteness2_pi2_rec3_closed hD C hchk hroots hg hP1 hal hwc) δ1 δh h1 hh

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.recCompleteness2_pi2_rec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness2_pi2_rec3

/-- info: 'RecCompose.Pi2Sim.recCompleteness_pi2_rec3_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness_pi2_rec3_fs

/-- info: 'RecCompose.Pi2Sim.recCompleteness2_pi2_rec3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness2_pi2_rec3_closed

/-- info: 'RecCompose.Pi2Sim.delta2_rec3_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.delta2_rec3_le

/-- info: 'RecCompose.Pi2Sim.recCompleteness_pi2_rec3_closed_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.recCompleteness_pi2_rec3_closed_fs
