-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import ZK.PcsFSClosed
import ZK.PcsSlack

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
