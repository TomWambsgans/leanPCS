-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's completeness (`formal/RecStatement`'s
-- `RecCompleteness2`, `RecCompletenessWith`) at the recursion's concrete π1-rec3 prover (`Pi1KeccakProver`'s
-- `pi1Rec3ProverK`, `formal/UniKeccakComplete`'s prover with its Fiat–Shamir over Keccak-f[1600]): `Pi2AlphaEnd`'s
-- theorems with `Pi2P1.Pi1ProverFacts` discharged (`Pi1KeccakTransfer`, `Pi1KeccakCensus`).
import RecCompose.Pi1KeccakCensus
import RecCompose.Pi1KeccakRpm
import RecCompose.Pi2AlphaEnd
import RecCompose.RealDeployment

/-!
# The recursive verifier's completeness at the concrete π1-rec3 prover

`Pi2Alpha.recCompleteness2_pi2_rec3_closed` and `recCompleteness_pi2_rec3_closed_fs` take an abstract π1-rec3 prover
`P1` with its two-call program `P1k` and the four named facts `Pi1ProverFacts D P1 P1k`. Here `P1` is the recursion's
Lean prover `pi1Rec3ProverK D` (`UniKeccakComplete.Rec3`'s π1-rec3 prover with Flock's honest prover, its Fiat–Shamir
the pure `keccak256`, the graph's; its trees and WHIR openings over `π`) and `P1k = p1kK D`, and the facts are proved:

* **`pi1ProverFactsK`**: `Pi1ProverFacts D (pi1Rec3ProverK D) (p1kK D)` at the real deployment (`D.Real`):
  `Pi1OverPerm` (`pi1Rec3ProverK_eq`), `Pi1Disc` (`disc_p1kK`), `Pi1Cost` (`qc_p1kK`, at most `2^47` blocks),
  `Pi1HashShort` (`hashShort_p1kK`), each transferred from UniKeccakComplete's two-call prover (`Pi1KeccakTransfer`);
* **`recCompleteness2_pi2_rec3_K`**: `RecCompleteness2 D (pi1Rec3ProverK D) (pi2Prover …) δ2` from the run-checked
  inputs only (`Pi2Circuits D`, `hroots`, `GraphsAgree`, `Pi2ViewChecked C`), `δ2 ≤ 2^-164`
  (`Pi2Alpha.delta2_alpha_le`);
* **`recCompleteness_pi2_rec3_K_fs`**: the recursive verifier's completeness end to end at `composeProver D
  (pi1Rec3ProverK D) (pi2Prover …)`, error `δ1 + δh + δ2`, with exactly two named premises, both about π1-rec3 at the
  **real Keccak-f[1600]**: `Pi1CompletenessKeccak D (pi1Rec3ProverK D) δ1` and `Pi1HazardKeccakHonest D
  (pi1Rec3ProverK D) δh`;
* **`recCompleteness_real_K_fs`**: the same at `realDeployment prog hprog`, its `Real` and its circuits from the
  evaluated checks (`GraphsAgree`, `DigestChecked`, `SetupRootChecked`, `IvChecked`); **`recCompleteness_real_K_fs_bits`**
  with `δ2` replaced by its bound `2^-164`.

**The two premises.** Neither is provable here, and both are honest-prover statements (no adversary grinds):

* `Pi1CompletenessKeccak D (pi1Rec3ProverK D) δ1` is `Pi1CompletenessFs D (pure ∘ keccakF1600) δ1`
  (`pi1CompletenessKeccak_iff`). Its random-permutation reading, `Pi1CompletenessFs D π deltaK`, **is proved**
  (`pi1CompletenessFs_rpm`, from `UniKeccakComplete.uniCompletenessKeccakRec3_closed`): `deltaK < 2^-169`. The premise
  is the Fiat–Shamir heuristic for this one fixed honest prover: Keccak-f[1600] behaves as the random permutation on
  its run.
* `Pi1HazardKeccakHonest D (pi1Rec3ProverK D) δh`: the honest proof's run at Keccak-f[1600] avoids the merge hazard
  (`RecGraphKeccak.MergeHazardK`: `t` a root of `Z_bad(p_0)`), motivated by `RecGraphKeccak.hazard_probK`
  (`≤ 2^16/|E| = 2^-176` for a uniform `t`), a count, not a game: its random-permutation reading is not proved.

At the real Keccak-f[1600] a fixed honest prover is not ground by anyone, so the premises are the weakest form of the
Fiat–Shamir heuristic; but the model gap remains: no Lean theorem passes from the random permutation to the fixed
function π2's circuit computes.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi1K

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM LeanVM.Rpm
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open Pi2S Pi2K Pi2P Pi2E Pi2G Pi2O
open scoped ENNReal

/-- **The four named facts about π1-rec3's prover, discharged** for the recursion's prover at the real deployment. -/
theorem pi1ProverFactsK {D : RecDeployment} (hD : D.Real) : Pi1ProverFacts D (pi1Rec3ProverK D) (p1kK D) where
  overPerm input rows q _ _ := pi1Rec3ProverK_eq D input rows q
  disc input rows q _ _ := disc_p1kK D input rows q
  cost input rows q hfit hrel :=
    qc_p1kK D (real_shape hD) (real_programIv hD) input rows q hfit (real_honest hD hrel)
  hashShort input rows q hfit _ := hashShort_p1kK hD input rows q hfit

/-- **π2's completeness at the recursion's π1-rec3 prover**, from the run-checked inputs only (`Pi2Circuits D`,
`hroots`, `GraphsAgree`, `Pi2ViewChecked C`); `δ2 ≤ 2^-164` (`Pi2Alpha.delta2_alpha_le`). -/
theorem recCompleteness2_pi2_rec3_K {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree) :
    RecCompleteness2 D (pi1Rec3ProverK D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel)
      (delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  Pi2Alpha.recCompleteness2_pi2_rec3_closed hD C hchk hroots hg (pi1ProverFactsK hD)

/-- **The recursive verifier's completeness end to end at the recursion's π1-rec3 prover**: error `δ1 + δh + δ2`,
`δ2 ≤ 2^-164`, from the run-checked inputs and the two named premises about π1-rec3 at the real Keccak-f[1600]
(`Pi1CompletenessKeccak`, whose random-permutation reading is `pi1CompletenessFs_rpm` at `deltaK < 2^-169`;
`Pi1HazardKeccakHonest`). -/
theorem recCompleteness_pi2_rec3_K_fs {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hchk : Pi2ViewChecked C) (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree)
    (δ1 δh : ℝ≥0∞) (h1 : Pi1CompletenessKeccak D (pi1Rec3ProverK D) δ1)
    (hh : Pi1HazardKeccakHonest D (pi1Rec3ProverK D) δh) :
    RecCompletenessWith D
      (composeProver D (pi1Rec3ProverK D) (pi2Prover D C (pi2Facts hD C hchk) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  Pi2Alpha.recCompleteness_pi2_rec3_closed_fs hD C hchk hroots hg (pi1ProverFactsK hD) δ1 δh h1 hh

/-- **The same at the real deployment** `realDeployment prog hprog`: its `Real` from `GraphsAgree`, `DigestChecked`,
`SetupRootChecked`; its circuits and view check from `GraphsAgree`, `IvChecked`. -/
theorem recCompleteness_real_K_fs (prog : KeccakVm.Program)
    (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize) (hg : GraphsAgree) (hd : DigestChecked)
    (hs : SetupRootChecked) (hiv : IvChecked) (δ1 δh : ℝ≥0∞)
    (h1 : Pi1CompletenessKeccak (realDeployment prog hprog) (pi1Rec3ProverK (realDeployment prog hprog)) δ1)
    (hh : Pi1HazardKeccakHonest (realDeployment prog hprog) (pi1Rec3ProverK (realDeployment prog hprog)) δh) :
    RecCompletenessWith (realDeployment prog hprog)
      (composeProver (realDeployment prog hprog) (pi1Rec3ProverK (realDeployment prog hprog))
        (pi2Prover (realDeployment prog hprog) (pi2Circuits_real prog hprog hg hiv)
          (pi2Facts (realDeployment_real prog hprog hg hd hs) (pi2Circuits_real prog hprog hg hiv)
            (pi2ViewChecked_real prog hprog hg hiv)) PcsQuotient.nonceFuel))
      (δ1 + δh + delta2' Cost2.pi2RunN Pi2Sim.alphaBound (tFreshBound2 Cost2.pi2RunN Pi2Sim.alphaBound)
        ((Cost2.pi2RunN : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel)) :=
  recCompleteness_pi2_rec3_K_fs (realDeployment_real prog hprog hg hd hs) (pi2Circuits_real prog hprog hg hiv)
    (pi2ViewChecked_real prog hprog hg hiv) rfl hg δ1 δh h1 hh

/-- **The headline, in bits**: at the real deployment, the recursive verifier rejects the composed honest proof with
probability at most `δ1 + δh + 2^-164`, `δ1`, `δh` the two named premises' errors (`Pi1CompletenessKeccak`, whose
random-permutation reading holds at `deltaK < 2^-169`, `pi1CompletenessFs_rpm`; `Pi1HazardKeccakHonest`). -/
theorem recCompleteness_real_K_fs_bits (prog : KeccakVm.Program)
    (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize) (hg : GraphsAgree) (hd : DigestChecked)
    (hs : SetupRootChecked) (hiv : IvChecked) (δ1 δh : ℝ≥0∞)
    (h1 : Pi1CompletenessKeccak (realDeployment prog hprog) (pi1Rec3ProverK (realDeployment prog hprog)) δ1)
    (hh : Pi1HazardKeccakHonest (realDeployment prog hprog) (pi1Rec3ProverK (realDeployment prog hprog)) δh) :
    RecCompletenessWith (realDeployment prog hprog)
      (composeProver (realDeployment prog hprog) (pi1Rec3ProverK (realDeployment prog hprog))
        (pi2Prover (realDeployment prog hprog) (pi2Circuits_real prog hprog hg hiv)
          (pi2Facts (realDeployment_real prog hprog hg hd hs) (pi2Circuits_real prog hprog hg hiv)
            (pi2ViewChecked_real prog hprog hg hiv)) PcsQuotient.nonceFuel))
      (δ1 + δh + (2 : ℝ≥0∞)⁻¹ ^ 164) := fun input rows q hfit hrel ↦
  (recCompleteness_real_K_fs prog hprog hg hd hs hiv δ1 δh h1 hh input rows q hfit hrel).trans
    (by gcongr; exact Pi2Alpha.delta2_alpha_le)

end RecCompose.Pi1K

/-- info: 'RecCompose.Pi1K.pi1ProverFactsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1ProverFactsK

/-- info: 'RecCompose.Pi1K.recCompleteness2_pi2_rec3_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.recCompleteness2_pi2_rec3_K

/-- info: 'RecCompose.Pi1K.recCompleteness_pi2_rec3_K_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.recCompleteness_pi2_rec3_K_fs

/-- info: 'RecCompose.Pi1K.recCompleteness_real_K_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.recCompleteness_real_K_fs

/-- info: 'RecCompose.Pi1K.recCompleteness_real_K_fs_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.recCompleteness_real_K_fs_bits
