-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraphKeccak.Emitted
import RecGraphKeccak.Pi1.Verifier
import RecGraphKeccak.Main
import RecGraphKeccak.Sim.End
import RecGraphKeccak.Sim.Final

/-!
# RecGraphKeccak: the Keccak VM's π1-rec3 recorded graph, and graph = verifier

The Keccak VM's π1-rec3 recorded verifier graph (`Emitted.lean`, written by `crates/leanvm_rec/tests/
lean_graph_keccak.rs`, data only), the verifier as a `RecGraph.Prog` program (`Pi1/`; its Lean recording `pi1GraphK`
equals the emitted graph node for node: `RecGraphKeccakTest/Pi1Check.lean`), and graph = verifier against `UniKeccak`'s
`runWithK` at `keccakRec3` (`Main.lean`: `Pi1GraphIsVerifierK`), from the simulation's parts (`Sim/`): Flock with the
structured terminal is proved (`flockSpecK`), the composition is proved (`pi1GraphIsVerifierK_of_parts`), the tables' parts, `Q_W`'s identity and
degree and the heap's relations are proved; the tail and the relations' shape off the hazard are the named
`KeccakTailShape` (`pi1GraphIsVerifierK_of_tailShape`). See `README.md`.

The build fails if a definition or theorem below uses an axiom beyond Lean's three standard ones.
-/

/-- info: 'RecGraphKeccak.Pi1.pi1Rec3K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Pi1.pi1Rec3K

/-- info: 'RecGraphKeccak.Pi1GraphIsVerifierK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Pi1GraphIsVerifierK

/-- info: 'RecGraphKeccak.TerminalE.structuredTerminal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.TerminalE.structuredTerminal_eq

/-- info: 'RecGraphKeccak.Sim.structuredTerminal_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.structuredTerminal_ph

/-- info: 'RecGraphKeccak.Sim.flockSpecK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.flockSpecK

/-- info: 'RecGraphKeccak.Sim.reduce_simQK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.reduce_simQK

/-- info: 'RecGraphKeccak.Sim.pi1SimK_of_reduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.pi1SimK_of_reduce

/-- info: 'RecGraphKeccak.Sim.pi1GraphIsVerifierK_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.pi1GraphIsVerifierK_of_parts

/-- info: 'RecGraphKeccak.Sim.pi1GraphIsVerifierK_of_simParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.pi1GraphIsVerifierK_of_simParts

/-- info: 'RecGraphKeccak.Sim.tableSpecK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.tableSpecK

/-- info: 'RecGraphKeccak.Sim.degreeSpecK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.degreeSpecK

/-- info: 'RecGraphKeccak.Sim.constraintSpecK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.constraintSpecK

/-- info: 'RecGraphKeccak.Sim.heapSpecK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.heapSpecK

/-- info: 'RecGraphKeccak.Sim.pi1GraphIsVerifierK_of_tailShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.pi1GraphIsVerifierK_of_tailShape

/-- info: 'RecGraphKeccak.Sim.keccakSimParts_of_tailShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.keccakSimParts_of_tailShape
