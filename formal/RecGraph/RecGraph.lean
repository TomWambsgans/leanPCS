-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecGraph.Node
import RecGraph.Semantics
import RecGraph.Record
import RecGraph.Commute
import RecGraph.Values
import RecGraph.Pi1.Main
import RecGraph.Sim.Compose
import RecGraph.Sim.Calls
import RecGraph.Sim.Flock
import RecGraph.Sim.Shape
import RecGraph.Sim.Wide

/-!
# RecGraph: recorded verifier graphs, their meaning, and the recorder

The recursion's outer proof π2 proves a circuit compiled from the **recorded operation graph** of the inner proof π1's
verifier (`crates/leanvm/rec`, π1-rec3: `FsShape::Rec3`). This library is the design-independent half of "compiler
correctness" (`README.md` here): the graph (`Node`, `Graph`), its meaning over any permutation (`evalGraph`), the
Lean recorder (`Record.lean`) with "recording commutes with evaluation" (`Commute.lean`, `Values.lean`); and the verifier's shared pieces as recorder programs
(`Pi1/`) with their simulation framework (`Sim/`), from which the Keccak VM's π1-rec3 (`formal/RecGraphKeccak`) is
built and proved.

The build fails if a definition or theorem below uses an axiom beyond Lean's three standard ones.
-/

/-- info: 'RecGraph.evalGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.evalGraph


/-- info: 'RecGraph.run_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.run_vals

/-- info: 'RecGraph.record_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.record_eval

/-- info: 'RecGraph.new_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.new_val

/-- info: 'RecGraph.constant_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.constant_val

/-- info: 'RecGraph.add_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.add_val

/-- info: 'RecGraph.mul_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.mul_val

/-- info: 'RecGraph.new_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.new_inv

/-- info: 'RecGraph.add_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.add_inv

/-- info: 'RecGraph.mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.mul_inv

/-- info: 'RecGraph.start_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.start_inv

/-- info: 'RecGraph.op_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.op_val

/-- info: 'RecGraph.op_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.op_inv

/-- info: 'RecGraph.op_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.op_lt

/-- info: 'RecGraph.record_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.record_inv

/-- info: 'RecGraph.sample_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.sample_val

/-- info: 'RecGraph.input_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.input_val

/-- info: 'RecGraph.ringWeight_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.ringWeight_val

/-- info: 'RecGraph.bits_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.bits_val

/-- info: 'RecGraph.Pi1.evalGraph_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Pi1.evalGraph_recorded
