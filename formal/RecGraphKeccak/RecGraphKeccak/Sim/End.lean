-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraphKeccak.Sim.Top

/-!
# Graph = verifier for the Keccak VM's π1-rec3, from the parts

`pi1GraphIsVerifierK_of_parts`: from the parts' interface (`Sim/ComposeSpec.lean`; Flock is proved, `flockSpecK`),
`Pi1GraphIsVerifierK` (`Main.lean`), through `reduce_simQK` (`Sim/Compose.lean`), `pi1SimK_of_reduce` (`Sim/Top.lean`)
and `pi1GraphIsVerifierK_of_sim`. `KeccakSimParts` names what is left: representations of the tables' parts, of the
relations' shapes and of the tail's condition, with the five parts' statements for them.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph RecGraph.Sim RecGraphKeccak

/-- **Graph = verifier for the Keccak VM's π1-rec3, from the parts** (for any representations satisfying them). -/
theorem pi1GraphIsVerifierK_of_parts (PR : PartRep) (hPR : PartRepGrows PR)
    {TS : Table → List E → TablePart × List Relation → Prop} {CS : List E → E → Relation → Prop}
    {HS : List E → List Relation × List (Column × Nat × Bool) → Prop}
    {OK : List Relation → List (Column × Nat × Bool) → Prop} {nT : Table → Nat}
    {nB chB : List Relation → List (Column × Nat × Bool) → Nat}
    (hT : TableSpecK PR TS nT) (hC : ConstraintSpecK PR CS) (hD : DegreeSpecK) (hH : HeapSpecK PR HS)
    (hTail : TailSpecK OK nB chB) (hS : ShapeSpecK TS CS HS OK) : Pi1GraphIsVerifierK :=
  pi1GraphIsVerifierK_of_sim (pi1SimK_of_reduce fun _ _ _ _ st words wordsE hg hseed hcur hch hw hwl ↦
    reduce_simQK PR hPR hT hC hD hH hTail hS st words wordsE hg hseed hcur hch hw hwl)

/-- **What is left of graph = verifier for the Keccak π1-rec3** (Flock is proved): representations of the tables'
parts (`PR`, growing with the recorder's state), of the tables', the constraint quotient's and the heap's relations'
shapes (`TS`, `CS`, `HS`) and of the tail's condition (`OK`), with byte counts, for which the tables' parts, the
constraint quotient's relation, its degree, the heap's relations and the tail simulate `UniKeccak`'s, and the
relations satisfy `OK` off the merge hazard. -/
def KeccakSimParts : Prop :=
  ∃ (PR : PartRep) (TS : Table → List E → TablePart × List Relation → Prop) (CS : List E → E → Relation → Prop)
    (HS : List E → List Relation × List (Column × Nat × Bool) → Prop)
    (OK : List Relation → List (Column × Nat × Bool) → Prop) (nT : Table → Nat)
    (nB chB : List Relation → List (Column × Nat × Bool) → Nat),
    PartRepGrows PR ∧ TableSpecK PR TS nT ∧ ConstraintSpecK PR CS ∧ DegreeSpecK ∧ HeapSpecK PR HS ∧
      TailSpecK OK nB chB ∧ ShapeSpecK TS CS HS OK

/-- **Graph = verifier for the Keccak π1-rec3, from `KeccakSimParts`.** -/
theorem pi1GraphIsVerifierK_of_simParts (h : KeccakSimParts) : Pi1GraphIsVerifierK := by
  obtain ⟨PR, _, _, _, _, _, _, _, hPR, hT, hC, hD, hH, hTail, hS⟩ := h
  exact pi1GraphIsVerifierK_of_parts PR hPR hT hC hD hH hTail hS

end RecGraphKeccak.Sim
