-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecGraphKeccak.Sim.End
import RecGraphKeccak.Sim.Constraint
import RecGraphKeccak.Sim.Heap
import RecGraphKeccak.Sim.ShapeK

/-!
# Graph = verifier for the Keccak VM's π1-rec3: what is left after the proved parts

Flock (`flockSpecK`), the tables' parts (`tableSpecK`), `Q_W`'s identity (`constraintSpecK`) and degree
(`degreeSpecK`) and the heap's relations (`heapSpecK`) are proved, at the representations `partRK`, `tableShapeK`,
`constraintShapeK`, `heapShapeK`. `KeccakTailShape`: a condition `OK` on the relations and `C2`'s columns, with byte
and challenge counts, under which the tail simulates `UniKeccak`'s (`TailSpecK`), and which `reduceWithK`'s relations
satisfy off the merge hazard (`ShapeSpecK`); proved at `TailOKK` (`keccakTailShape`: `Sim/BatchK.lean`,
`Sim/ShapeK.lean`). So **`pi1GraphIsVerifierK : Pi1GraphIsVerifierK`**, with no hypothesis.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters UniStatement RecGraph RecGraph.Sim RecGraphKeccak

/-- **What is left of graph = verifier for the Keccak π1-rec3**: the tail (`TailSpecK`) and the relations' shape off
the hazard (`ShapeSpecK`), for one condition `OK`. -/
def KeccakTailShape : Prop :=
  ∃ (OK : List Relation → List (Column × Nat × Bool) → Prop) (nB chB : List Relation → List (Column × Nat × Bool) → Nat),
    TailSpecK OK nB chB ∧ ShapeSpecK tableShapeK constraintShapeK heapShapeK OK

/-- **Graph = verifier for the Keccak π1-rec3, from `KeccakTailShape`** (every other part proved). -/
theorem pi1GraphIsVerifierK_of_tailShape (h : KeccakTailShape) : Pi1GraphIsVerifierK := by
  obtain ⟨OK, nB, chB, hTail, hS⟩ := h
  exact pi1GraphIsVerifierK_of_parts partRK partRK_grows tableSpecK constraintSpecK degreeSpecK heapSpecK hTail hS

/-- `KeccakTailShape` gives `KeccakSimParts`. -/
theorem keccakSimParts_of_tailShape (h : KeccakTailShape) : KeccakSimParts := by
  obtain ⟨OK, nB, chB, hTail, hS⟩ := h
  exact ⟨partRK, tableShapeK, constraintShapeK, heapShapeK, OK, tableBytesK, nB, chB, partRK_grows, tableSpecK,
    constraintSpecK, degreeSpecK, heapSpecK, hTail, hS⟩

/-- **The tail and the shape, proved** (`tailSpecK`, `shapeSpecK`, at `TailOKK`). -/
theorem keccakTailShape : KeccakTailShape := ⟨TailOKK, tailBytesK, tailChK, tailSpecK, shapeSpecK⟩

/-- **Graph = verifier for the Keccak VM's π1-rec3, off the merge hazard**: no hypothesis. -/
theorem pi1GraphIsVerifierK : Pi1GraphIsVerifierK := pi1GraphIsVerifierK_of_tailShape keccakTailShape

end RecGraphKeccak.Sim
