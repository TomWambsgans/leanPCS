-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import ZK.PcsFSClosed
import ZK.PcsSlack
import ZK.PcsSpan
import ZK.PcsIdeal

/-! # The axioms of the zero-knowledge theorem (PCS claims) -/

/-- info: 'PcsQuotient.EndToEnd.zeroKnowledge_pcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_pcs

/-- info: 'PcsQuotient.EndToEnd.hybrid_run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.hybrid_run_eq

/-- info: 'PcsQuotient.EndToEnd.RProg.trace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.RProg.trace_le

/-- info: 'PcsQuotient.EndToEnd.RProg.trace_le_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.RProg.trace_le_approx

/-- info: 'PcsQuotient.EndToEnd.ideal_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.ideal_joint

/-- info: 'PcsQuotient.EndToEnd.rootOfHalves_rootHalves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.rootOfHalves_rootHalves

/-- info: 'PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed

/-- info: 'PcsQuotient.EndToEnd.fiatShamirUniform_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.fiatShamirUniform_closed

/-- info: 'PcsQuotient.EndToEnd.εfs₀_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.εfs₀_le

/-- info: 'PcsQuotient.EndToEnd.revealedUniform_of_group1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.revealedUniform_of_group1

/-- info: 'PcsQuotient.EndToEnd.zeroKnowledge_pcs_group1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_pcs_group1

/-- info: 'PcsQuotient.EndToEnd.spanFail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.spanFail_le

/-- info: 'PcsQuotient.EndToEnd.εslack_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.εslack_le

/-- info: 'PcsQuotient.EndToEnd.revealedUniform_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.revealedUniform_slack

/-- info: 'PcsQuotient.EndToEnd.zeroKnowledge_pcs_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.zeroKnowledge_pcs_slack

/-- info: 'PcsQuotient.EndToEnd.PcsParam.pcsExperiment_idealOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.PcsParam.pcsExperiment_idealOf

/-- info: 'PcsQuotient.EndToEnd.PcsParam.pcsZeroKnowledge_idealOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.PcsParam.pcsZeroKnowledge_idealOf

/-- info: 'PcsQuotient.EndToEnd.PcsParam.zeroKnowledge_idealOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PcsQuotient.EndToEnd.PcsParam.zeroKnowledge_idealOf
