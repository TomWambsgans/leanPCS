-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The two transcriptions are `UniSound/Ids/Rels.lean`'s
-- reading (`tablePartOf`, `tablesPart`, a value at a time) and the Keccak code-level link's `mainRelsK`,
-- `flockClaimK` (`Code/Shape.lean`); the proofs are `UniSound/Ids/Align.lean`'s on the Keccak tables.
import UniSound.Ids.Align
import UniSound.Ids.Eval
import UniKeccakSound.Ids.Build

/-!
# The Keccak relations at `t`, read a value at a time

The Keccak identity model's relations at `t` (`relsAtK`) are the code-level link's (`mainRelsK`: each Keccak table's
part reads its `tableReads` values as one chunk, `consumeFold`). **`relsAtK_eq`**: for round `0`'s challenges of
length at least four, they are `relsOfK` of the relations' input (`relInputK`, `UniSound.Ids.RelInput`): the tables'
parts read a value at a time (`tablesPart` on `tablesKeccak`, `UniSound/Ids/Rels.lean`), then the memory's, the
bytecode's, the constraint quotient's (`constraintRelationK`), the heap's (`heapRelations`) and Flock's ring term
(`RelInput.ringRels`), in the code's order. The tables' alignment is `UniSound.Ids.tablesPart_eq` (any list of tables).

Round `0`'s challenges must have four entries: `relsAtK` reads `α` as `ch.take 4`, the identities (`polysK`) as
`alphasOf ch` (padded with zeros); they agree exactly then (`UniSound.Ids.Align.alphasOf_eq`).
-/

namespace UniKeccakSound.IdsEval

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak UniKeccakSound.Ids

/-! ## The relations from their input, on the Keccak tables -/

section Inp

variable (inp : RelInput)

/-- The Keccak tables' parts, read a value at a time. -/
def tpK : List TablePart × List Relation × List E :=
  tablesPart inp.shape inp.weights inp.beta inp.w tablesKeccak inp.vals

/-- The values after the Keccak tables'. -/
def restK : List E := (tpK inp).2.2

def mfcK : E := (restK inp).getD 0 0
def addrK : E := (restK inp).getD 1 0
def mpullK : E := (restK inp).getD 2 0
def mpushK : E := mpullK inp + inp.weights.getD 2 0 * (1 + mfcK inp)
def bfcK : E := (restK inp).getD 3 0
def bpullK : E := (restK inp).getD 4 0
def bpushK : E := bpullK inp + inp.weights.getD 2 0 * (1 + bfcK inp)
def hvK : E := (restK inp).getD 5 0
def cvK : E := (restK inp).getD 6 0

/-- The memory's three relations. -/
def memRelsK : List Relation :=
  [Relation.equal (.memory 3) (inp.w.take inp.shape.logMemory) (mfcK inp),
    Relation.equal .address (inp.w.take inp.shape.logMemory) (addrK inp),
    ⟨(List.range 3).map (fun k ↦ term (.memory k) (inp.w.take inp.shape.logMemory) (inp.weights.getD (3 + k) 0)),
      mpullK inp + inp.beta + inp.weights.getD 0 0 * sepMem + inp.weights.getD 1 0 * addrK inp +
        inp.weights.getD 2 0 * mfcK inp⟩]

/-- The bytecode's two relations. -/
def bcRelsK : List Relation :=
  [Relation.equal .bytecodeFinal (inp.w.take inp.shape.logBytecode) (bfcK inp),
    Relation.equal .bytecodeTuple (inp.alphas ++ inp.w.take inp.shape.logBytecode)
      (bpullK inp + inp.beta + inp.weights.getD 2 0 * bfcK inp)]

/-- The constraint quotient's relation and degree on the Keccak VM (step 5). -/
def constraintK : Relation × ℕ :=
  constraintRelationK inp.shape (tpK inp).1 inp.publicWords inp.gamma inp.t (cvK inp) inp.w

/-- The heap's relations (step 6). -/
def heapK : List Relation × List (Column × ℕ × Bool) :=
  heapRelations inp.shape inp.active (tpK inp).1 inp.weights inp.beta (hvK inp) (cvK inp) (mpullK inp)
    (mpushK inp) (bpullK inp) (bpushK inp) inp.w (chunks ((constraintK inp).2 + 1))

/-- **The Keccak verifier's relations at `t`**, in its order (steps 4–7 of `reduceWithK`, point claims). -/
def relsOfK : List Relation :=
  (tpK inp).2.1 ++ memRelsK inp ++ bcRelsK inp ++ [(constraintK inp).1] ++ (heapK inp).1 ++ inp.ringRels

end Inp

/-- **The relations' input** at a statement, round `0`'s challenges, Flock's result, `t` and the values. -/
def relInputK (D : KDeployment) (s : USt) (ch : List E) (fl : List E × Flock.End) (t : E) (vals : List E) :
    RelInput :=
  ⟨D.shape, publicWordsOf s.1.toList, countsOf D.shape s.2, alphasOf ch, betaOf ch, gammaOf ch, fl.1, some fl.2,
    t, vals⟩

/-! ## `mainRelsK` read a value at a time -/

open Align

/-- The Keccak tables' relations and parts as `mainRelsK` reads them. -/
def stOfK (shape : Shape) (alphas : List E) (beta t : E) (vals : List E) : Array Relation × Array TablePart :=
  consumeFold tableReads (tablesStep shape.heights (eqKernel alphas) beta (wOf shape t)) tablesKeccak (#[], #[])
    (vals.take tablesReadsK)

/-- The constraint quotient's relation as `mainRelsK` states it. -/
def crOfAK (shape : Shape) (pw : List E) (alphas : List E) (beta gamma t : E) (vals : List E) : Relation × ℕ :=
  constraintRelationK shape (stOfK shape alphas beta t vals).2.toList pw gamma t
    (vals.getD (tablesReadsK + 6) 0) (wOf shape t)

/-- The heap's relations as `mainRelsK` states them. -/
def hrOfK (shape : Shape) (pw : List E) (counts : List (List E)) (alphas : List E) (beta gamma t : E)
    (vals : List E) : List Relation × List (Column × ℕ × Bool) :=
  heapRelations shape ((counts.zip shape.heights).map fun x => activeVanishingFromBits (wOf shape t) x.1 x.2)
    (stOfK shape alphas beta t vals).2.toList (eqKernel alphas) beta (vals.getD (tablesReadsK + 5) 0)
    (vals.getD (tablesReadsK + 6) 0) (vals.getD (tablesReadsK + 2) 0)
    (vals.getD (tablesReadsK + 2) 0 + (eqKernel alphas).getD 2 0 * (1 + vals.getD tablesReadsK 0))
    (vals.getD (tablesReadsK + 4) 0)
    (vals.getD (tablesReadsK + 4) 0 + (eqKernel alphas).getD 2 0 * (1 + vals.getD (tablesReadsK + 3) 0))
    (wOf shape t) (chunks ((crOfAK shape pw alphas beta gamma t vals).2 + 1))

/-- **`mainRelsK`' relations**, as a list. -/
theorem mainRelsK_fst (shape : Shape) (pw : List E) (counts : List (List E)) (alphas : List E)
    (beta gamma t : E) (vals : List E) :
    (mainRelsK shape pw counts alphas beta gamma t vals).1.toList =
      (stOfK shape alphas beta t vals).1.toList ++
        [Relation.equal (.memory 3) ((wOf shape t).take shape.logMemory) (vals.getD tablesReadsK 0),
          Relation.equal .address ((wOf shape t).take shape.logMemory) (vals.getD (tablesReadsK + 1) 0),
          ⟨(List.range 3).map (fun k => term (.memory k) ((wOf shape t).take shape.logMemory)
              ((eqKernel alphas).getD (3 + k) 0)),
            vals.getD (tablesReadsK + 2) 0 + beta + (eqKernel alphas).getD 0 0 * sepMem +
              (eqKernel alphas).getD 1 0 * vals.getD (tablesReadsK + 1) 0 +
              (eqKernel alphas).getD 2 0 * vals.getD tablesReadsK 0⟩,
          Relation.equal .bytecodeFinal ((wOf shape t).take shape.logBytecode)
            (vals.getD (tablesReadsK + 3) 0),
          Relation.equal .bytecodeTuple (alphas ++ (wOf shape t).take shape.logBytecode)
            (vals.getD (tablesReadsK + 4) 0 + beta + (eqKernel alphas).getD 2 0 * vals.getD (tablesReadsK + 3) 0),
          (crOfAK shape pw alphas beta gamma t vals).1] ++
        (hrOfK shape pw counts alphas beta gamma t vals).1 := by
  unfold mainRelsK
  simp only [wOf, stOfK, crOfAK, hrOfK, Array.toList_append, Array.toList_push, List.append_assoc,
    List.cons_append, List.nil_append]

theorem stK_eq (inp : RelInput) :
    consumeFold tableReads (tablesStep inp.shape.heights (eqKernel inp.alphas) inp.beta (wOf inp.shape inp.t))
        tablesKeccak (#[], #[]) (inp.vals.take (tablesKeccak.map tableReads).sum) =
      stOfK inp.shape inp.alphas inp.beta inp.t inp.vals :=
  rfl

theorem tpK_eq (inp : RelInput) :
    tablesPart inp.shape (eqKernel inp.alphas) inp.beta (wOf inp.shape inp.t) tablesKeccak inp.vals = tpK inp :=
  rfl

/-- The Keccak tables' relations. -/
theorem tpK_fst (inp : RelInput) : (stOfK inp.shape inp.alphas inp.beta inp.t inp.vals).1.toList = (tpK inp).2.1 := by
  rw [← stK_eq, ← tpK_eq]
  exact tablesPart_fst _ _ _ _ tablesKeccak _

/-- The Keccak tables' parts. -/
theorem tpK_snd (inp : RelInput) : (stOfK inp.shape inp.alphas inp.beta inp.t inp.vals).2.toList = (tpK inp).1 := by
  rw [← stK_eq, ← tpK_eq]
  exact tablesPart_snd _ _ _ _ tablesKeccak _

/-- The values after the Keccak tables'. -/
theorem restK_getD (inp : RelInput) (k : ℕ) : (restK inp).getD k 0 = inp.vals.getD (tablesReadsK + k) 0 := by
  have h3 := (tablesPart_eq inp.shape (eqKernel inp.alphas) inp.beta (wOf inp.shape inp.t) tablesKeccak
    #[] #[] inp.vals).2.2
  rw [tpK_eq] at h3
  have e : restK inp = (tpK inp).2.2 := rfl
  rw [e, h3]
  exact getD_drop _ _ _

/-- The constraint quotient's relation. -/
theorem constraintK_eq (inp : RelInput) :
    constraintK inp = crOfAK inp.shape inp.publicWords inp.alphas inp.beta inp.gamma inp.t inp.vals := by
  have e : constraintK inp = constraintRelationK inp.shape (tpK inp).1 inp.publicWords inp.gamma inp.t
    ((restK inp).getD 6 0) (wOf inp.shape inp.t) := rfl
  rw [e, ← tpK_snd, restK_getD]
  rfl

/-- The heap's relations. -/
theorem heapK_eq (inp : RelInput) :
    heapK inp = hrOfK inp.shape inp.publicWords inp.counts inp.alphas inp.beta inp.gamma inp.t inp.vals := by
  have e : heapK inp = heapRelations inp.shape
      ((inp.counts.zip inp.shape.heights).map fun p ↦ activeVanishingFromBits (wOf inp.shape inp.t) p.1 p.2)
      (tpK inp).1 (eqKernel inp.alphas) inp.beta ((restK inp).getD 5 0) ((restK inp).getD 6 0)
      ((restK inp).getD 2 0)
      ((restK inp).getD 2 0 + (eqKernel inp.alphas).getD 2 0 * (1 + (restK inp).getD 0 0)) ((restK inp).getD 4 0)
      ((restK inp).getD 4 0 + (eqKernel inp.alphas).getD 2 0 * (1 + (restK inp).getD 3 0)) (wOf inp.shape inp.t)
      (chunks ((constraintK inp).2 + 1)) := rfl
  rw [e, constraintK_eq, ← tpK_snd]
  simp only [restK_getD, Nat.add_zero]
  rfl

/-- **The relations but Flock's are `mainRelsK`'**. -/
theorem relsOfK_fst (inp : RelInput) :
    (tpK inp).2.1 ++ memRelsK inp ++ bcRelsK inp ++ [(constraintK inp).1] ++ (heapK inp).1 =
      (mainRelsK inp.shape inp.publicWords inp.counts inp.alphas inp.beta inp.gamma inp.t inp.vals).1.toList := by
  rw [mainRelsK_fst, ← tpK_fst, constraintK_eq, heapK_eq]
  simp only [memRelsK, bcRelsK, mfcK, addrK, mpullK, bfcK, bpullK, RelInput.w, RelInput.weights, wOf,
    restK_getD, Nat.add_zero, List.append_assoc, List.cons_append, List.nil_append]

/-- **The relations are the Keccak code-level link's**, Flock's ring term (`ringRels`) the one `flockClaimK`
adds. -/
theorem relsOfK_eq (inp : RelInput) (fl : List E × Flock.End) (h1 : fl.1 = inp.flockPoint)
    (h2 : some fl.2 = inp.flockEnd) :
    relsOfK inp = (flockClaimK (mainRelsK inp.shape inp.publicWords inp.counts inp.alphas inp.beta inp.gamma
      inp.t inp.vals).1 fl).1.toList := by
  rw [show relsOfK inp = ((tpK inp).2.1 ++ memRelsK inp ++ bcRelsK inp ++ [(constraintK inp).1] ++
    (heapK inp).1) ++ inp.ringRels from rfl, relsOfK_fst]
  obtain ⟨p, e⟩ := fl
  simp only at h1 h2
  subst h1
  unfold flockClaimK RelInput.ringRels
  rw [← h2]
  rcases e with ⟨map, target⟩ | ⟨ws, value⟩ <;> simp

/-- **The Keccak identity model's relations at `t` are `relsOfK`'s**, for at least four challenges in round `0`. -/
theorem relsAtK_eq (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) (hch : 4 ≤ ch.length) :
    relsAtK D Fl s ch fd t vals = relsOfK (relInputK D s ch (Fl.prog.out fd []) t vals) := by
  rw [relsOfK_eq _ (Fl.prog.out fd []) rfl rfl]
  unfold relsAtK
  rw [show (relInputK D s ch (Fl.prog.out fd []) t vals).alphas = ch.take 4 from alphasOf_eq ch hch]
  rfl

end UniKeccakSound.IdsEval
