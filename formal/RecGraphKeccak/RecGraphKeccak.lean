-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecGraphKeccak.Emitted
import RecGraphKeccak.Pi1.Verifier
import RecGraphKeccak.Main
import RecGraphKeccak.Sim.End
import RecGraphKeccak.Sim.Final
import RecGraphKeccak.Hazard
import RecGraphKeccak.Main4
import RecGraphKeccak.Sim.Final4
import RecGraphKeccak.Sim.AtSetup4

/-!
# RecGraphKeccak: the Keccak VM's π1-rec4 recorded graph, and graph = verifier

The Keccak VM's π1-rec4 recorded verifier graph (`Emitted.lean`, written by `crates/leanvm/rec/tests/
lean_graph_keccak.rs`, data only), the verifier as a `RecGraph.Prog` program (`Pi1/Verifier4.lean`; its Lean recording
`pi1GraphK4` equals the emitted graph node for node: `RecGraphKeccakTest/Pi1Check.lean`), and graph = verifier against
`UniKeccak`'s `runWithK4` at `keccakRec4` (`Main4.lean`: `Pi1GraphIsVerifierK4`), proved from the simulation's parts
(`Sim/`): **`Sim.pi1GraphIsVerifierK4 : Pi1GraphIsVerifierK4`**, with no hypothesis. π1-rec3's program and its theorem
`Sim.pi1GraphIsVerifierK` are kept. `Circuit.lean` (`pi1rec3K_end`) is not imported: `formal/RecCircuit` does not yet
compile π1-rec4's `wide` nodes. See `README.md`.

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

/-- info: 'RecGraphKeccak.Sim.tailSpecK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.tailSpecK

/-- info: 'RecGraphKeccak.Sim.shapeSpecK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.shapeSpecK

/-- info: 'RecGraphKeccak.Sim.keccakTailShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.keccakTailShape

/-- info: 'RecGraphKeccak.Sim.pi1GraphIsVerifierK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.pi1GraphIsVerifierK

/-- info: 'RecGraphKeccak.functionalsCorrect15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.functionalsCorrect15

/-- info: 'RecGraphKeccak.hazard_cardK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.hazard_cardK

/-- info: 'RecGraphKeccak.hazard_probK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.hazard_probK

/-- info: 'RecGraphKeccak.Pi1.pi1Rec4K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Pi1.pi1Rec4K

/-- info: 'RecGraphKeccak.Pi1GraphIsVerifierK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Pi1GraphIsVerifierK4

/-- info: 'RecGraphKeccak.GraphsAgreeK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.GraphsAgreeK4

/-- info: 'RecGraphKeccak.emitted_isVerifierK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.emitted_isVerifierK4

/-- info: 'RecGraph.Sim.sim_sampleWide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraph.Sim.sim_sampleWide

/-- info: 'RecGraphKeccak.Sim.verifyWalkedK4_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.verifyWalkedK4_sim

/-- info: 'RecGraphKeccak.Sim.tailSpecK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.tailSpecK4

/-- info: 'RecGraphKeccak.Sim.reduce_simQK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.reduce_simQK4

/-- info: 'RecGraphKeccak.Sim.pi1GraphIsVerifierK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.pi1GraphIsVerifierK4

/-- info: 'RecGraphKeccak.graphAtSetup_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.graphAtSetup_recorded

/-- info: 'RecGraphKeccak.Sim.pi1GraphIsVerifierK4At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.pi1GraphIsVerifierK4At

/-- info: 'RecGraphKeccak.Sim.emitted_isVerifierK4At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecGraphKeccak.Sim.emitted_isVerifierK4At
