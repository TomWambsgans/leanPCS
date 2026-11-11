-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Final
import RecCompose.RealEnd
import RecCompose.RealCircuit
import RecCompose.IvUniform
import RecCompose.Layouts
import RecCompose.Pi2AcceptsReal
import RecCompose.Pi1Rec4Rpm
import RecCompose.CompleteReal

/-!
# RecCompose: the recursive verifier's end theorems

π2v4 over π1-rec4 at the real deployment (`RealDeployment.lean`): knowledge soundness as an explicit reduction
(`RealEnd.lean`), completeness for the composed Lean prover (`CompleteReal.lean`). See `formal/RecCompose/README.md`.
The build fails if a headline theorem's axioms grow beyond Lean's three standard ones.
-/

/-- info: 'RecCompose.recKnowledgeSoundness_reduction_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_reduction_real

/-- info: 'RecCompose.recKnowledgeSoundnessReduction_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundnessReduction_final

/-- info: 'RecCompose.recKnowledgeSoundness2_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness2_final

/-- info: 'RecCompose.recKnowledgeSoundness_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_final

/-- info: 'RecCompose.pi2Bound_le_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Bound_le_bits

/-- info: 'RecCompose.realDeployment_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.realDeployment_real

/-- info: 'RecCompose.pi2CircuitAccepts_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2CircuitAccepts_real

/-- info: 'RecCompose.pi2FsLayer_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2FsLayer_real

/-- info: 'RecCompose.ivChecked_of_patchChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.ivChecked_of_patchChecked

/-- info: 'RecCompose.recCompleteness_end_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recCompleteness_end_fs

/-- info: 'RecCompose.Pi2E.pi2_accepts_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.pi2_accepts_real

/-- info: 'RecCompose.Pi1K.pi1Rec4ProverK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1Rec4ProverK_eq

/-- info: 'RecCompose.Pi1K.pi1CompletenessFs4_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1CompletenessFs4_rpm

/-- info: 'RecCompose.Pi1K.pi1CompletenessKeccak_iff4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1CompletenessKeccak_iff4

/-- info: 'RecCompose.Pi1K.pi1ProverFactsK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1ProverFactsK4

/-- info: 'RecCompose.Pi2Sim.delta2Closed_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.delta2Closed_le

/-- info: 'RecCompose.Pi1K.recCompleteness2_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.recCompleteness2_real

/-- info: 'RecCompose.Pi1K.recCompleteness_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.recCompleteness_real
