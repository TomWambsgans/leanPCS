-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import SoundPcs.Final

/-! The axioms of `SoundPcs`'s results: `propext`, `Classical.choice` and `Quot.sound` only. -/

/-- info: 'SoundPcs.knowledgeSoundness_deployed_pcs_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SoundPcs.knowledgeSoundness_deployed_pcs_of

/-- info: 'SoundPcs.trace_dExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SoundPcs.trace_dExp

/-- info: 'SoundPcs.prEvent_EBn_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SoundPcs.prEvent_EBn_le

/-- info: 'ComposePcs.prob_advBad2P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ComposePcs.prob_advBad2P

/-- info: 'ComposePcs.trace_core2P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ComposePcs.trace_core2P
