-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Tables
import RecCompose.Real
import RecCompose.FsClosed
import RecCompose.End

/-!
# The end theorems, from the named inputs left

The end statements at a deployment `D` with `D.Real` (π2v4 over the Keccak VM's π1-rec4 at the 128-signature reference
shape), every proved layer in place, their hypotheses the inputs left:

* π2's Fiat–Shamir layer `Pi2FsLayer D` (proved at every real deployment: `pi2FsLayer_real`, `FsClosed.lean`);
* the setup's columns, proved from `RecDeployment.Real` (`SetupFromCompiler`: σ, κ the compiled circuit's at every π1
  setup commitment), so `Pi2SetupColumns D C` is `pi2SetupColumns_of_real` and the tables' layer is `pi2Tables`;
* the compiled circuit `C : Pi2Circuits D` (the Lean compiler on π1-rec4's graph at every π1 setup commitment) at the
  emitted graph's roots (`hroots`), its facts `Fa : Pi2Facts D C` and the circuit's corollary
  `Pi2CircuitAccepts C Fa` (a satisfied circuit carries a π1 stream π1-rec4's graph accepts, its claims hashing to the
  declared ones); at the real deployment all three are built from the evaluated checks (`RealEnd.lean`);
* the Lean recording of π1-rec4's verifier is the emitted graph (`RecGraphKeccak.GraphsAgreeK4`, **evaluated**).
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol
open scoped ENNReal

/-- π2's layers from the named inputs. -/
noncomputable def pi2LayersFinal (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hcirc : Pi2CircuitAccepts C Fa) :
    Pi2Layers D pi2Bound :=
  pi2Layers_of_fs C Fa (pi2SetupColumns_of_real hD C hroots) (pi2FsLayer_real D hD) hcirc

/-- **π2's part**: `RecKnowledgeSoundness2 D pi2Bound`, and `pi2Bound Q ≤ 2^-64` for `Q ≤ 2^64`. -/
theorem recKnowledgeSoundness2_final (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hcirc : Pi2CircuitAccepts C Fa) :
    RecKnowledgeSoundness2 D pi2Bound ∧ ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  ⟨recKnowledgeSoundness2_of_real D (pi2LayersFinal D hD C Fa hroots hcirc), pi2Bound_le_bits⟩

/-- **End to end, against the Keccak VM's `KvHolds`, as an explicit reduction**:
`RecKnowledgeSoundnessReduction D pi2Bound` (π2's bound plus π1-rec4's, the merge hazard's and a Keccak-256
collision's experiments for the explicit derived adversaries). -/
theorem recKnowledgeSoundnessReduction_final (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D)
    (Fa : Pi2Facts D C) (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hcirc : Pi2CircuitAccepts C Fa)
    (hg : RecGraphKeccak.GraphsAgreeK4) : RecKnowledgeSoundnessReduction D pi2Bound :=
  recKnowledgeSoundnessReduction_end D hD.2.2.1 hg (pi2LayersFinal D hD C Fa hroots hcirc)

/-- **End to end, the Prop-premise form**: `RecKnowledgeSoundness D pi2Bound ε1 εh εc` for every `ε1`, `εh`, `εc`. -/
theorem recKnowledgeSoundness_final (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hcirc : Pi2CircuitAccepts C Fa)
    (hg : RecGraphKeccak.GraphsAgreeK4) (ε1 εh εc : ℕ → ℝ≥0∞) : RecKnowledgeSoundness D pi2Bound ε1 εh εc :=
  recKnowledgeSoundness_end D hD.2.2.1 hg (pi2LayersFinal D hD C Fa hroots hcirc) ε1 εh εc

end RecCompose

/-- info: 'RecCompose.recKnowledgeSoundness2_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness2_final

/-- info: 'RecCompose.recKnowledgeSoundnessReduction_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundnessReduction_final

/-- info: 'RecCompose.recKnowledgeSoundness_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_final
