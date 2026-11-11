-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Completeness.Reduction
import Completeness.Circuit
import Completeness.Tables
import Completeness.Honest
import Completeness.HiddenFill
import Completeness.Read
import Completeness.Opening

/-!
# Completeness layers shared with the leanVM line

The previous membership protocol's completeness layers, pruned to what the leanVM line imports
(`Reduction`, `Circuit`, `Tables`, `Honest`, `HiddenFill`, `Read`, `Opening`); the previous protocol's own end
theorems (`completeness_deployed_*`, `HiddenOpenings.lean`) were removed (git history). The deployed membership
protocol's completeness is `formal/EndToEnd/Completeness` (`E2ECompleteness.completeness_end`). Every declaration
below depends on `propext`, `Classical.choice` and `Quot.sound` only.
-/

/-- info: 'Completeness.Reduction.honest_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.Reduction.honest_accepts

/-- info: 'Completeness.Reduction.bad_fraction_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.Reduction.bad_fraction_le

/-- info: 'Completeness.Reduction.bad_bound_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.Reduction.bad_bound_lt

/-- info: 'Completeness.honest_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.honest_relation

/-- info: 'Completeness.exists_table_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.exists_table_support

/-- info: 'Completeness.qGate_mem_lifts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.qGate_mem_lifts

/-- info: 'Completeness.accepts_table_of_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.accepts_table_of_honest

/-- info: 'Completeness.mle_eq_tableEvalN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.mle_eq_tableEvalN

/-- info: 'Completeness.quotient_inChunks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.quotient_inChunks

/-- info: 'Completeness.readNew_fillNew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.readNew_fillNew

/-- info: 'Completeness.witness_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.witness_read

/-- info: 'Completeness.quotient_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.quotient_read

/-- info: 'Completeness.gadgetWeight_sum_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.gadgetWeight_sum_zero

/-- info: 'Completeness.deployed_newHiddenOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.deployed_newHiddenOK

/-- info: 'Completeness.openingVerify_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.openingVerify_honest

/-- info: 'Completeness.ours_romComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Completeness.ours_romComplete

/-- info: 'Completeness.honest_relation_random' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Completeness.honest_relation_random

/-- info: 'Completeness.relation_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Completeness.relation_vals

/-- info: 'Completeness.cellsRandomized_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Completeness.cellsRandomized_eq

