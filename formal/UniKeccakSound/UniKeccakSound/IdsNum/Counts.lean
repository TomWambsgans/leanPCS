-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The counts are `UniSound/Ids/Counts.lean`'s
-- (`relCount_reference`, `ncvOf_eq`) on the Keccak verifier's relations (`Code/Shape.lean`'s `mainRelsK`,
-- `flockClaimK`) and constraints (`Ids/Model.lean`'s `constraintsPK`).
import UniSound.Ids.Counts
import UniSound.Ids.Degrees
import UniKeccakSound.IdsNum.Deployed
import UniKeccakSound.Ids.BusCount

/-!
# The Keccak relations' number, the constraints' number, the bus bound

* **`relCountK_of`** (`RelCountK D Fl (177 + |blocks|)`, every shape): `relsAtK` is the tables' parts (each its sent
  values, then at most two relations a flush: `tablePartPure_rels_len`; `166` for the six Keccak tables, which the
  kernel counts from their sent columns and flushes, no coefficient: `tablesK_rels`), the memory's three, the
  bytecode's two, the constraint quotient's, the heap's `3 + |blocks| + 1` (`UniSound.Ids.Eval.heapRelations_fst`)
  and at most one ring end (`flockClaimK`); **`relCountK_ref`**: `187` at the reference shape (`10` heap blocks).
* **`ncvK_le`**: at most `98` constraint vectors' entries at every shape (`JUMP`'s two, six counters, at most one
  copy a `SHA3` column, three public lines, plus one; `keccakSlot` is not evaluated, so the `SHA3` table's `86`
  columns bound its `50` lanes).
* **`busBoundK_ref`**: the bus bound `3,227,649` at the reference shape.
-/

namespace UniKeccakSound.IdsNum

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.Eval UniKeccak UniKeccakSound
  UniKeccakSound.Ids

/-! ## Loops of fixed reads, counted -/

/-- **A measure grows by at most `c x` a step** of a loop of fixed reads, so by `Σ c x` over the loop. -/
theorem consumeFold_le {α β : Type} (k : α → ℕ) (g : α → β → List E → β) (f : β → ℕ) (c : α → ℕ)
    (h : ∀ x b vs, f (g x b vs) ≤ f b + c x) :
    ∀ (l : List α) (b : β) (vs : List E), f (consumeFold k g l b vs) ≤ f b + (l.map c).sum
  | [], b, _ => by simp [consumeFold]
  | x :: xs, b, vs => by
    simp only [consumeFold, List.map_cons, List.sum_cons]
    have h1 := consumeFold_le k g f c h xs (g x b (vs.take (k x))) (vs.drop (k x))
    have h2 := h x b (vs.take (k x))
    omega

theorem sum_map_const {α : Type} (l : List α) (c : ℕ) : (l.map fun _ ↦ c).sum = c * l.length := by
  induction l with
  | nil => simp
  | cons _ l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

/-! ## The tables' relations -/

theorem flushStep_size (t : Table) (pt : List E) (weights : Array E) (beta : E) (sent : Array (Option E))
    (x : List Form × List Form) (s : Array Relation × E × E × ℕ × ℕ) (vs : List E) :
    (UniSound.flushStep t pt weights beta sent x s vs).1.size ≤ s.1.size + 2 := by
  unfold UniSound.flushStep
  dsimp only
  split_ifs <;> simp

/-- **A table's part's relations**: its sent values', at most two a flush (`tabRels`). -/
theorem tablePartPure_rels_len (t : Table) (lh : ℕ) (weights : Array E) (beta : E) (w vs : List E) :
    (tablePartPure t lh weights beta w vs).2.length ≤ tabRels t := by
  unfold tablePartPure tabRels
  dsimp only
  rw [Array.length_toList]
  generalize hs1 : consumeFold (fun _ ↦ 1) (UniSound.sentStep t (w.take lh)) (sentColumns t)
    (Array.replicate t.width none, #[]) (vs.take (sentColumns t).length) = s1
  have h1 : s1.2.size ≤ (sentColumns t).length := by
    have := consumeFold_le (fun _ ↦ 1) (UniSound.sentStep t (w.take lh)) (fun s ↦ s.2.size) (fun _ ↦ 1)
      (fun x b vs ↦ by simp [UniSound.sentStep]) (sentColumns t) (Array.replicate t.width none, #[])
      (vs.take (sentColumns t).length)
    rw [hs1, sum_map_const] at this
    simpa using this
  have h2 := consumeFold_le (flushReads weights s1.1) (UniSound.flushStep t (w.take lh) weights beta s1.1)
    (fun s ↦ s.1.size) (fun _ ↦ 2) (fun x b vs ↦ flushStep_size _ _ _ _ _ x b vs)
    (t.flushes.pull.zip t.flushes.push) (s1.2, 1, 1, 1, 0) (vs.drop (sentColumns t).length)
  rw [sum_map_const] at h2
  dsimp only at h2
  omega

set_option maxRecDepth 100000 in
/-- **The six Keccak tables' relations**: `166` (the kernel counts their sent columns and flushes). -/
theorem tablesK_rels : (tablesKeccak.map tabRels).sum = 166 := by
  decide +kernel

/-- The tables' loop (step 4): at most `166` relations. -/
theorem tablesK_rels_size (heights : List ℕ) (weights : Array E) (beta : E) (w vs : List E) :
    (consumeFold tableReads (tablesStep heights weights beta w) tablesKeccak (#[], #[]) vs).1.size ≤ 166 := by
  have h := consumeFold_le tableReads (tablesStep heights weights beta w) (fun s ↦ s.1.size) tabRels
    (fun x b vs ↦ by
      simp only [tablesStep, Array.size_append, List.size_toArray]
      exact Nat.add_le_add_left (tablePartPure_rels_len _ _ _ _ _ _) _) tablesKeccak (#[], #[]) vs
  rw [tablesK_rels] at h
  simpa using h

/-! ## The relations at `t` -/

theorem flockClaimK_size (rels : Array Relation) (fl : List E × Flock.End) :
    (flockClaimK rels fl).1.size ≤ rels.size + 1 := by
  unfold flockClaimK
  split <;> simp

/-- **The relations before Flock's claim**: at most `176 + |blocks|`. -/
theorem mainRelsK_size (S : Shape) (pw : List E) (counts : List (List E)) (alphas : List E)
    (beta gamma t : E) (vals : List E) :
    (mainRelsK S pw counts alphas beta gamma t vals).1.size ≤ 176 + S.heap.blocks.length := by
  unfold mainRelsK
  dsimp only
  simp only [Array.size_append, List.size_toArray, heapRelations_fst, Array.size_push, List.length_append,
    List.length_cons, List.length_nil, List.length_map, List.length_zip, List.length_range, min_self]
  have h := tablesK_rels_size S.heights (eqKernel alphas) beta
    (digits t (max S.heap.h (S.constraintVars + 4) + 2)) (vals.take tablesReadsK)
  omega

/-- **At most `177 + |blocks|` relations**, at every Keccak deployment. -/
theorem relCountK_of (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) : RelCountK D Fl (177 + D.shape.heap.blocks.length) := by
  intro s ch fd t vals
  unfold relsAtK
  rw [Array.length_toList]
  have h1 := flockClaimK_size (mainRelsK D.shape (publicWordsOf s.1.toList) (countsBits D.shape.heights s.2)
    (ch.take 4) (ch.getD 4 0) (ch.getD 5 0) t vals).1 (Fl.prog.out fd [])
  have h2 := mainRelsK_size D.shape (publicWordsOf s.1.toList) (countsBits D.shape.heights s.2)
    (ch.take 4) (ch.getD 4 0) (ch.getD 5 0) t vals
  omega

/-- **At most `187` relations** at the reference Keccak shape (`10` heap blocks). -/
theorem relCountK_ref (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (hD : D.shape = keccakRefShape) : RelCountK D Fl 187 := by
  have h := relCountK_of D Fl
  rw [hD, heapK_blocks_ref] at h
  exact h

/-! ## The constraints' number -/

/-- A Keccak table's constraints' number, bounded: `JUMP`'s two, the counters', one a `SHA3` column. -/
def tabConsK (tab : Table) : ℕ :=
  (if tab.opcode = opJump then 2 else 0) + 1 + if tab.opcode = opBlake2s then tab.width else 0

theorem tableConstraintsPK_len (S : Shape) (c : Stk) (tab : Table) :
    (tableConstraintsPK S c tab).length ≤ tabConsK tab := by
  unfold tableConstraintsPK tabConsK
  dsimp only
  simp only [List.length_append, List.length_singleton]
  refine Nat.add_le_add (Nat.add_le_add ?_ le_rfl) ?_
  · split_ifs <;> simp
  · split_ifs
    · exact (List.length_filterMap_le _ _).trans_eq List.length_range
    · simp

set_option maxRecDepth 100000 in
theorem tablesK_cons : (tablesKeccak.map tabConsK).sum = 94 := by
  decide +kernel

/-- **At most `98` constraint vectors' entries** on the Keccak VM, at every shape. -/
theorem ncvK_le (S : Shape) : ncvK S ≤ 98 := by
  unfold ncvK constraintsPK linesPK
  simp only [List.length_append, List.length_flatMap, List.length_map, List.length_zip, linesOf,
    List.length_cons, List.length_nil, List.length_range]
  have h := list_sum_map_le tablesKeccak (fun tab ↦ (tableConstraintsPK S (fun _ ↦ 0) tab).length) tabConsK
    fun tab _ ↦ tableConstraintsPK_len S _ tab
  rw [tablesK_cons] at h
  omega

/-! ## The bus bound -/

set_option maxRecDepth 100000 in
/-- **The bus bound at the reference Keccak shape**: `3,227,649`. -/
theorem busBoundK_ref : busBoundK keccakRefShape = 3227649 := by
  rw [keccakRef_eq]
  decide +kernel

end UniKeccakSound.IdsNum

/-- info: 'UniKeccakSound.IdsNum.relCountK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.relCountK_of

/-- info: 'UniKeccakSound.IdsNum.relCountK_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.relCountK_ref

/-- info: 'UniKeccakSound.IdsNum.ncvK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.ncvK_le
