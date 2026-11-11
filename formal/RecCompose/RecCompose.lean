-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Basic
import RecCompose.Part1
import RecCompose.Part2
import RecCompose.Complete
import RecCompose.RpmC
import RecCompose.Pi1Decode
import RecCompose.CompleteCouplings
import RecCompose.Numbers
import RecCompose.End
import RecCompose.Circuit
import RecCompose.Layers
import RecCompose.Holds
import RecCompose.Chan
import RecCompose.Pi2Run
import RecCompose.CallsPure
import RecCompose.Rpm
import RecCompose.Couplings
import RecCompose.RunShape
import RecCompose.RunOpenings
import RecCompose.OpeningsAgree
import RecCompose.Bridge
import RecCompose.Final
import RecCompose.Tables
import RecCompose.Real
import RecCompose.FsClosed
import RecCompose.Pi2Prover
import RecCompose.Pi2ProverRun
import RecCompose.Pi2CompleteEnd
import RecCompose.Pi2ProbStaged
import RecCompose.Pi2CallsOpen
import RecCompose.ViewDefs
import RecCompose.View
import RecCompose.Valid
import RecCompose.FactsAlg
import RecCompose.FactsSpec
import RecCompose.FactsSpecOf
import RecCompose.Facts
import RecCompose.Meanings
import RecCompose.Layouts
import RecCompose.IvLength
import RecCompose.RealDeployment
import RecCompose.IvUniform
import RecCompose.Pi2AlphaEnd
import RecCompose.Pi2Closed
import RecCompose.CompleteKeccakEnd
import RecCompose.RealCircuit
import RecCompose.RealEnd

/-!
# RecCompose: the recursive verifier's end theorems

See `formal/RecCompose/README.md`. The build fails if a headline theorem's axioms grow beyond Lean's three standard
ones.
-/

/-- info: 'RecCompose.recKnowledgeSoundness_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_reduction

/-- info: 'RecCompose.recKnowledgeSoundness2_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness2_closed

/-- info: 'RecCompose.recKnowledgeSoundness_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_closed

/-- info: 'RecCompose.recKnowledgeSoundness_closed_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_closed_fs

/-- info: 'RecCompose.recCompleteness_end_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recCompleteness_end_fs

/-- info: 'RecCompose.pi2Bound_le_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2Bound_le_bits

/-- info: 'RecCompose.realDeployment_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.realDeployment_real

/-- info: 'RecCompose.Pi2Alpha.recCompleteness2_pi2_rec3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Alpha.recCompleteness2_pi2_rec3_closed

/-- info: 'RecCompose.Pi2Alpha.recCompleteness_pi2_rec3_closed_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Alpha.recCompleteness_pi2_rec3_closed_fs

/-- info: 'RecCompose.Pi2Alpha.delta2_alpha_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Alpha.delta2_alpha_le

/-- info: 'RecCompose.Pi1K.pi1ProverFactsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1ProverFactsK

/-- info: 'RecCompose.Pi1K.recCompleteness2_pi2_rec3_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.recCompleteness2_pi2_rec3_K

/-- info: 'RecCompose.Pi1K.recCompleteness_real_K_fs_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.recCompleteness_real_K_fs_bits

/-- info: 'RecCompose.recKnowledgeSoundness_reduction_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_reduction_real
