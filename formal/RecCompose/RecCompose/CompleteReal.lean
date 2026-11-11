-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's completeness (`formal/RecStatement`'s
-- `RecCompleteness2`, `RecCompletenessWith`) at the recursion's concrete π1-rec4 prover (`Pi1Rec4Prover`'s
-- `pi1Rec4ProverK`, `formal/UniKeccakComplete`'s prover with its Fiat–Shamir over Keccak-f[1600]) and the real
-- deployment (`RealDeployment`, `RealCircuit`): `Pi2Closed`'s theorems with `Pi2P1.Pi1ProverFacts` discharged
-- (`Pi1Rec4Transfer`, `Pi1Rec4Census`), π1's openings and the witness's existence from `Pi2Witness`.
import RecCompose.Pi1Rec4Rpm
import RecCompose.Pi1Rec4Census
import RecCompose.Pi2Closed
import RecCompose.Pi2Witness
import RecCompose.RealCircuit

/-!
# The recursive verifier's completeness at the real deployment

`Pi2Sim.recCompleteness2_pi2_closed` and `recCompleteness_pi2_closed_fs` take an abstract π1-rec4 prover `P1` with its
two-call program `P1k` and the four named facts `Pi1ProverFacts D P1 P1k`, π1's openings in the contract
(`Pi2Pi1Openings`), the circuit compiler's completeness (`Pi2WitnessExists`) and a non-hole position. Here `P1` is the
recursion's Lean prover `pi1Rec4ProverK D` (`UniKeccakComplete.Rec4`'s π1-rec4 prover, its Fiat–Shamir the pure
`keccak256` and its rate, the graph's; its trees and WHIR openings over `π`), `P1k = p1kK4 D`, and every input is
proved or evaluated:

* **`pi1ProverFactsK4`**: `Pi1ProverFacts D (pi1Rec4ProverK D) (p1kK4 D)` at any `D.Real`: `Pi1OverPerm`
  (`pi1Rec4ProverK_eq`), `Pi1Disc` (`disc_p1kK4`), `Pi1Cost` (`qc_p1kK4`, at most `2^47` blocks), `Pi1HashShort`
  (`hashShort_p1kK4`);
* **`pi2Pi1Openings_real`** (from `Pi2W.pi1Openings_of_verifierH`), **`Pi2W.pi2WitnessExists_real`**,
  **`Pi2W.nonhole_real`**, from the evaluated checks;
* **`recCompleteness2_real`**: `RecCompleteness2 (realDeployment prog hprog) (pi1Rec4ProverK _) (realPi2Prover …)
  delta2Closed`, `delta2Closed ≤ 2^-164` (`Pi2Sim.delta2Closed_le`), from the evaluated checks only;
* **`recCompleteness_real`**: the recursive verifier's completeness end to end at the real deployment, for the composed
  Lean prover `composeProver (pi1Rec4ProverK D) (realPi2Prover …)`, error `δ1 + δh + 2^-164`, with the evaluated checks
  (`GraphsAgreeK4`, `DigestChecked`, `SetupRootChecked`, `IvChecked`) and exactly two named premises, both about
  π1-rec4's honest run at the **real Keccak-f[1600]**: `Pi1CompletenessKeccak D (pi1Rec4ProverK D) δ1` and
  `Pi1HazardKeccakHonest D (pi1Rec4ProverK D) δh`.

**The two premises.** Neither is provable here, and both are honest-prover statements (no adversary grinds):

* `Pi1CompletenessKeccak D (pi1Rec4ProverK D) δ1` is `Pi1CompletenessFs4 D (pure ∘ keccakF1600) δ1`
  (`pi1CompletenessKeccak_iff4`). Its random-permutation reading, `Pi1CompletenessFs4 D π deltaK`, **is proved**
  (`pi1CompletenessFs4_rpm`, from `UniKeccakComplete.uniCompletenessKeccakRec4_closed`): `deltaK < 2^-169`. The
  premise is the Fiat–Shamir heuristic for this one fixed honest prover.
* `Pi1HazardKeccakHonest D (pi1Rec4ProverK D) δh`: the honest proof's run at Keccak-f[1600] avoids the merge hazard
  (`RecGraphKeccak.MergeHazardK4`: `t` a root of `Z_bad(p_0)`), motivated by `RecGraphKeccak.hazard_probK`
  (`≤ 2^16/|E| = 2^-176` for a uniform `t`), a count, not a game.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi1K

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open Pi2G
open scoped ENNReal

variable (prog : KeccakVm.Program) (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize)
  (hg : RecGraphKeccak.GraphsAgreeK4) (hd : DigestChecked) (hs : SetupRootChecked) (hiv : IvChecked)

/-- **π2's Lean prover at the real deployment**: `Pi2E.pi2Prover` on the compiled circuits and their public values,
`nonceFuel` nonces a proof of work. -/
noncomputable abbrev realPi2Prover : Pi2Prover :=
  Pi2E.pi2Prover (realDeployment prog hprog) (pi2Circuits_real prog hprog hg hiv).G
    (pi2Facts_real prog hprog hg hd hs hiv).pubOf PcsQuotient.nonceFuel

/-- **π1's openings in the contract at the real deployment** (`Pi2Pi1Openings`), from π1-rec4's graph verifier. -/
theorem pi2Pi1Openings_real : Pi2Pi1Openings (realDeployment prog hprog) := fun Ht Ft input p1 h ↦
  Pi2W.pi1Openings_of_verifierH (realDeployment_real prog hprog hg hd hs).2.2.1 Ht Ft _ input p1 h

/-- **π2's completeness at the real deployment and the recursion's π1-rec4 prover**, from the evaluated checks only;
`delta2Closed ≤ 2^-164` (`Pi2Sim.delta2Closed_le`). -/
theorem recCompleteness2_real :
    RecCompleteness2 (realDeployment prog hprog) (pi1Rec4ProverK _) (realPi2Prover prog hprog hg hd hs hiv)
      Pi2Sim.delta2Closed :=
  Pi2Sim.recCompleteness2_pi2_closed (realDeployment_real prog hprog hg hd hs) (pi2Circuits_real prog hprog hg hiv)
    (pi2Facts_real prog hprog hg hd hs hiv) rfl (pi1ProverFactsK4 (realDeployment_real prog hprog hg hd hs))
    (pi2Pi1Openings_real prog hprog hg hd hs) (Pi2W.pi2WitnessExists_real prog hprog hg hd hs hiv)
    (Pi2W.nonhole_real prog hprog hg hd hs hiv)

/-- **The recursive verifier's completeness at the real deployment**: the composed Lean prover (π1-rec4's
`pi1Rec4ProverK`, then π2's `realPi2Prover`) is rejected with probability at most `δ1 + δh + 2^-164`, for every Keccak
VM program of the reference shape, every input, row counts that fit and `KvHonest` witness, given the evaluated checks
and the two named premises about π1-rec4's honest run at Keccak-f[1600] (`Pi1CompletenessKeccak δ1`, whose
random-permutation reading holds at `deltaK < 2^-169`, `pi1CompletenessFs4_rpm`; `Pi1HazardKeccakHonest δh`). -/
theorem recCompleteness_real (δ1 δh : ℝ≥0∞)
    (h1 : Pi1CompletenessKeccak (realDeployment prog hprog) (pi1Rec4ProverK _) δ1)
    (hh : Pi1HazardKeccakHonest (realDeployment prog hprog) (pi1Rec4ProverK _) δh) :
    RecCompletenessWith (realDeployment prog hprog)
      (composeProver (realDeployment prog hprog) (pi1Rec4ProverK _) (realPi2Prover prog hprog hg hd hs hiv))
      (δ1 + δh + (2 : ℝ≥0∞)⁻¹ ^ 164) := fun input rows q hfit hrel ↦
  (Pi2Sim.recCompleteness_pi2_closed_fs (realDeployment_real prog hprog hg hd hs)
    (pi2Circuits_real prog hprog hg hiv) (pi2Facts_real prog hprog hg hd hs hiv) rfl
    (pi1ProverFactsK4 (realDeployment_real prog hprog hg hd hs)) (pi2Pi1Openings_real prog hprog hg hd hs)
    (Pi2W.pi2WitnessExists_real prog hprog hg hd hs hiv) (Pi2W.nonhole_real prog hprog hg hd hs hiv) δ1 δh h1 hh
    input rows q hfit hrel).trans (by gcongr; exact Pi2Sim.delta2Closed_le)

end RecCompose.Pi1K

/-- info: 'RecCompose.Pi1K.recCompleteness2_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.recCompleteness2_real

/-- info: 'RecCompose.Pi1K.recCompleteness_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.recCompleteness_real
