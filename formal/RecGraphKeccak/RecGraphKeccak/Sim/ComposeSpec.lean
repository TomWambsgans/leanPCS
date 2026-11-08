-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecGraph.Sim.Compose
import RecGraphKeccak.Sim.Flock
import RecGraphKeccak.Main

/-!
# The Keccak composition's interface: what each part of the Keccak π1-rec3 verifier is to satisfy

As `RecGraph.Sim.ComposeSpec` for the BLAKE2s VM, at `keccak128` and against `UniKeccak.reduceWithK`'s parts:

* Flock: `FlockSpecK` (`Sim/Flock.lean`, proved: `flockSpecK`);
* `TableSpecK PR TS nT`: a table's part (`tablePart`, on `tablesKeccak`, at `keccak128`'s heights);
* `ConstraintSpecK PR CS`: `Q_W`'s identity (`constraintRelationK`, the `SHA3` lanes' copies and `END_BIT`);
* `DegreeSpecK`: its degree is `Shape.constraintDegreeK keccak128`;
* `HeapSpecK PR HS`: the heap's relations (`heapRelations` at `keccak128`);
* `TailSpecK OK nB chB`: the tail after `ρ` (`tailPK`: one claim per commitment, then `batchK` with `weightAtK`) against
  `UniKeccak.batchK`, for relations satisfying `OK`;
* `ShapeSpecK TS CS HS OK`: `reduceWithK`'s relations satisfy `OK` off the hazard.

Every part is stated for every permutation, IV, public input and stream.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph RecGraph.Pi1
  RecGraph.Sim RecGraphKeccak.Pi1

/-- The digits' count at the Keccak shape (`max h (r_W + 4) + 2 = 26`). -/
abbrev wLenK : Nat := max keccak128.heap.h (keccak128.constraintVars + 4) + 2

/-- **A table's part** (`table_part`) on the Keccak VM: `nT t` bytes, no challenge. -/
def TableSpecK (PR : PartRep) (TS : Table → List E → TablePart × List Relation → Prop) (nT : Table → Nat) :
    Prop :=
  ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
    (t : Table), t ∈ tablesKeccak →
    ∀ (weights : Array Nat) (weightsE : Array E) (beta : Nat) (betaE : E) (w : List Nat) (wE : List E),
    st.nodes[0]? = some Node.seed → RpL π iv publicInput stream st weights.toList weightsE.toList →
    weightsE.size = 16 → Rp π iv publicInput stream st beta betaE → RpL π iv publicInput stream st w wE →
    wE.length = wLenK →
    Sim π iv publicInput stream st (RecGraph.Pi1.tablePart t (keccak128.heights.getD t.opcode 0) weights beta w)
      (UniStatement.tablePart (m := Id) t (keccak128.heights.getD t.opcode 0) weightsE betaE wE) (nT t) 0
      (fun st' a b ↦ PR π iv publicInput stream st' a.1 b.1 ∧ RpRels π iv publicInput stream st' a.2 b.2 ∧
        TS t wE b)

/-- **The constraint quotient's relation** on the Keccak VM (`constraintRelationK`, pure). -/
def ConstraintSpecK (PR : PartRep) (CS : List E → E → Relation → Prop) : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
    (parts : List TablePartS) (partsE : List TablePart) (pw : List Nat) (pwE : List E) (gamma t cv : Nat)
    (gammaE tE cvE : E) (w : List Nat) (wE : List E),
    Good st → st.nodes[0]? = some Node.seed → List.Forall₂ (PR π iv publicInput stream st) parts partsE →
    RpL π iv publicInput stream st pw pwE → pwE.length = 4 → Rp π iv publicInput stream st gamma gammaE →
    Rp π iv publicInput stream st t tE → Rp π iv publicInput stream st cv cvE → RpL π iv publicInput stream st w wE →
    wE = digits tE wLenK →
    PSim st (Pi1.constraintRelationK keccak128 parts pw gamma t cv w)
      (UniKeccak.constraintRelationK keccak128 partsE pwE gammaE tE cvE wE).1
      (fun st' a b ↦ RpRel π iv publicInput stream st' a b ∧ CS wE tE b)

/-- **The constraint quotient's degree** is the Keccak shape's (`Shape.constraintDegreeK`). -/
def DegreeSpecK : Prop :=
  ∀ (partsE : List TablePart) (pwE : List E) (gammaE tE cvE : E) (wE : List E), partsE.length = 6 →
    (UniKeccak.constraintRelationK keccak128 partsE pwE gammaE tE cvE wE).2 = UniKeccak.Shape.constraintDegreeK keccak128

/-- **The heap's relations** at the Keccak shape (`heapRelations`, pure), and the leaf quotients' columns. -/
def HeapSpecK (PR : PartRep) (HS : List E → List Relation × List (Column × Nat × Bool) → Prop) : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
    (active : List Nat) (activeE : List E) (parts : List TablePartS) (partsE : List TablePart)
    (weights : Array Nat) (weightsE : Array E) (beta hv cv mpl mps bpl bps : Nat)
    (betaE hvE cvE mplE mpsE bplE bpsE : E) (w : List Nat) (wE : List E),
    Good st → st.nodes[0]? = some Node.seed → RpL π iv publicInput stream st active activeE → activeE.length = 6 →
    List.Forall₂ (PR π iv publicInput stream st) parts partsE → partsE.length = 6 →
    RpL π iv publicInput stream st weights.toList weightsE.toList → weightsE.size = 16 →
    Rp π iv publicInput stream st beta betaE → Rp π iv publicInput stream st hv hvE →
    Rp π iv publicInput stream st cv cvE → Rp π iv publicInput stream st mpl mplE →
    Rp π iv publicInput stream st mps mpsE → Rp π iv publicInput stream st bpl bplE →
    Rp π iv publicInput stream st bps bpsE → RpL π iv publicInput stream st w wE → wE.length = wLenK →
    PSim st
      (RecGraph.Pi1.heapRelations keccak128 active parts weights beta hv cv mpl mps bpl bps w
        (chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1)))
      (UniStatement.heapRelations keccak128 activeE partsE weightsE betaE hvE cvE mplE mpsE bplE bpsE wE
        (chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1)))
      (fun st' a b ↦ RpRels π iv publicInput stream st' a.1 b.1 ∧ a.2 = b.2 ∧ HS wE b)

/-- **The Keccak verifier after `ρ`** (`reduceK`'s tail, literally): one claim per commitment, then the batch. -/
def tailPK (relations : List RelationS) (rho : Sym) (c2Columns : List (Column × Nat × Bool)) (map : List Sym) :
    Prog (List (Commitment × List Sym × Sym)) := do
  let mut combined : Array (Commitment × CombinedS) := #[]
  for c in commitments do
    if let some claim ← RecGraph.Pi1.combine relations c rho then
      combined := combined.push (c, claim)
  let _ ← one
  let stackLayouts := UniKeccak.layoutsK keccak128 c2Columns
  Pi1.batchK combined.toList stackLayouts (some map)

/-- `UniKeccak`'s tail after `ρ`, as `reduceWithK` has it at the point-claim ABI. -/
def tailUK (π : KeccakState → KeccakState) (relations : List Relation) (rho : E)
    (c2Columns : List (Column × Nat × Bool)) (map : List E) : ChanM Id (List (Commitment × Opening)) :=
  UniKeccak.batchK (Fp π) .rec3
    (commitments.filterMap fun c ↦ (UniStatement.combine relations c rho).map (c, ·))
    (UniKeccak.layoutsK keccak128 c2Columns) (some map)

/-- **The tail**: for relations satisfying `OK`, `nB` bytes and `chB` challenges, the openings represented. -/
def TailSpecK (OK : List Relation → List (Column × Nat × Bool) → Prop)
    (nB chB : List Relation → List (Column × Nat × Bool) → Nat) : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
    (relsS : List RelationS) (rels : List Relation) (rhoS : Nat) (ρ : E) (c2 : List (Column × Nat × Bool))
    (mapS : List Nat) (mapE : List E),
    Good st → 0 < st.nodes.size → RpRels π iv publicInput stream st relsS rels →
    Rp π iv publicInput stream st rhoS ρ → RpL π iv publicInput stream st mapS mapE → OK rels c2 →
    Sim π iv publicInput stream st (tailPK relsS rhoS c2 mapS) (tailUK π rels ρ c2 mapE) (nB rels c2) (chB rels c2)
      (fun st' a b ↦ OpeningsR π iv publicInput stream st' a b)

/-- **The relations `reduceWithK` states at the point-claim ABI**, from its intermediate values (step 4 to 7). -/
def relsUniK (outs : List (TablePart × List Relation)) (wE alphasE : List E) (betaE mfc addr mpl bfc bpl : E)
    (constraint : Relation) (heapRels : List Relation) (flockPt : List E) (target : E) : List Relation :=
  ((((((((tabRels outs).push (Relation.equal (.memory 3) (wE.take keccak128.logMemory) mfc)).push
    (Relation.equal .address (wE.take keccak128.logMemory) addr)).push
    { terms := (List.range 3).map fun k ↦
        term (.memory k) (wE.take keccak128.logMemory) ((UniStatement.eqKernel alphasE).getD (3 + k) 0),
      value := mpl + betaE + (UniStatement.eqKernel alphasE).getD 0 0 * sepMem +
        (UniStatement.eqKernel alphasE).getD 1 0 * addr + (UniStatement.eqKernel alphasE).getD 2 0 * mfc }).push
    (Relation.equal .bytecodeFinal (wE.take keccak128.logBytecode) bfc)).push
    (Relation.equal .bytecodeTuple (alphasE ++ wE.take keccak128.logBytecode)
      (bpl + betaE + (UniStatement.eqKernel alphasE).getD 2 0 * bfc))).push constraint ++ heapRels.toArray).push
    { terms := [{ column := .qflock, point := flockPt, twist := ringTwist, coefficient := 1 }],
      value := target }).toList

/-- **`C2`'s columns at the Keccak shape**: the heap, the tree quotient, the constraint quotient's chunks, the
leaves'. -/
def c2UniK (leaf : List (Column × Nat × Bool)) : List (Column × Nat × Bool) :=
  [(.heap, keccak128.heap.h, true), (.treeQuotient 0, keccak128.heap.h, true), (.treeQuotient 1, 0, true)] ++
    List.map (fun x ↦ (Column.constraintQuotient x.2, x.1, true))
      ((chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1)).zip
        (List.range (chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1)).length)) ++
    leaf

/-- **Off the hazard, `reduceWithK`'s relations satisfy `OK`**, from the parts' shapes. -/
def ShapeSpecK (TS : Table → List E → TablePart × List Relation → Prop) (CS : List E → E → Relation → Prop)
    (HS : List E → List Relation × List (Column × Nat × Bool) → Prop)
    (OK : List Relation → List (Column × Nat × Bool) → Prop) : Prop :=
  ∀ (tE : E) (alphasE : List E) (betaE : E) (flockPt : List E) (target : E) (outs : List (TablePart × List Relation))
    (mfc addr mpl bfc bpl : E) (constraint : Relation) (heapOut : List Relation × List (Column × Nat × Bool)),
    alphasE.length = 4 → flockPt.length = 26 → List.Forall₂ (fun t o ↦ TS t (digits tE wLenK) o) tablesKeccak outs →
    CS (digits tE wLenK) tE constraint → HS (digits tE wLenK) heapOut → ¬ HazardK (flockPt.headD 0) tE →
    OK (relsUniK outs (digits tE wLenK) alphasE betaE mfc addr mpl bfc bpl constraint heapOut.1 flockPt target)
      (c2UniK heapOut.2)

/-- No hazard at a channel's challenges `45` (`p_0`) and `52` (`t`), `t` drawn: `MergeHazardK`'s condition. -/
def NoHazardAtK (c : Chan) : Prop :=
  ¬ (53 ≤ c.challenges.size ∧ HazardK (c.challenges.getD 45 0) (c.challenges.getD 52 0))

/-- **What `reduceK` leaves, represented**: the roots (at `24` and `3752`), the openings, no pending matrices. -/
def RedRK (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState)
    (red : ReducedS) (r : Reduced) : Prop :=
  RootR π iv publicInput stream st red.root1 r.roots.1 24 ∧ RootR π iv publicInput stream st red.root2 r.roots.2 3752 ∧
    OpeningsR π iv publicInput stream st red.openings r.openings ∧ r.matrices = none

end RecGraphKeccak.Sim
