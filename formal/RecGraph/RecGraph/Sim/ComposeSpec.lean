-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.ComposeBase

/-!
# The composition's interface: the shared representations

The parts' representation (`PartRep`, `PartRepGrows`), the openings' (`OpeningsR`), a table's relations (`tabRels`)
and the roots' (`RootR`), which the Keccak VM's interface (`RecGraphKeccak.Sim.ComposeSpec`) states its parts with.
-/

-- The judgment is `RecGraph.Sim.Sim`.
set_option linter.dupNamespace false

namespace RecGraph.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph.Pi1

/-- A table part's representation. -/
abbrev PartRep : Type :=
  (KeccakState → KeccakState) → List UInt8 → List UInt8 → Array UInt8 → RecState → TablePartS → TablePart → Prop

/-- The representation grows with the state. -/
def PartRepGrows (PR : PartRep) : Prop :=
  ∀ π iv publicInput stream (st st' : RecState) p u, KInv st → Grows st st' →
    PR π iv publicInput stream st p u → PR π iv publicInput stream st' p u

/-- **The openings, represented**: one point claim per commitment, its point and value represented. -/
def OpeningsR (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)
    (st : RecState) (a : List (Commitment × List Nat × Nat)) (b : List (Commitment × Opening)) : Prop :=
  List.Forall₂ (fun x y ↦ ∃ ptE vE, y = (x.1, .point ptE vE none) ∧ RpL π iv publicInput stream st x.2.1 ptE ∧
    Rp π iv publicInput stream st x.2.2 vE) a b

/-- The tables' relations, as `reduceWithFs` concatenates them. -/
def tabRels (outs : List (TablePart × List Relation)) : Array Relation :=
  outs.foldl (fun acc o ↦ acc ++ o.2.toArray) #[]

/-- A root's halves, represented, at their stream offsets. -/
def RootR (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
    (a : Sym × Sym) (x : E × E) (off : Nat) : Prop :=
  Rp π iv publicInput stream st a.1 x.1 ∧ Rp π iv publicInput stream st a.2 x.2 ∧
    st.nodes[a.1]? = some (.input off 16) ∧ st.nodes[a.2]? = some (.input (off + 16) 16)

end RecGraph.Sim
