-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The programs are `formal/UniKeccak`'s
-- (`Verifier.lean`: `constraintRelationK`, `Shape.c2ColumnsK`, `layoutsK`) and `formal/UniStatement`'s
-- (`heapRelations`, `tablePart`); the proofs are `formal/UniSound/UniSound/CodeShape.lean`'s on the Keccak tables.
import UniSound.CodeLink
import UniKeccakSound.FsK

/-!
# The Keccak verifier's `C2` columns are the shape's

The Keccak verifier (`reduceWithK`) computes `C2`'s columns during the run (`constraintRelationK`'s quotient degree,
`heapRelations`' leaf quotients' chunks from the tables' parts); they are the shape's (`Shape.c2ColumnsK`, which
`layoutsOfK` and the batch's variables are built from), whatever the values read:

* `constraintRelationK_snd`: the constraint quotient's degree is `Shape.constraintDegreeK`;
* `tablesK_parts_degrees`: the parts of `tablesKeccak` have the tables' degrees (`tableDegrees`), whatever the values;
* `c2ColumnsK_run`: `C2`'s columns in the run are `Shape.c2ColumnsK`.

Also the values at `t` (`tablesReadsK`, `valsCountK`), the relations before Flock's claim (`mainRelsK`, `reduceWithK`'s
steps 4–6 as a function of what was read and drawn), and that every commitment has a relation
(`mainCombinedK_length`). The generic lemmas (`forIn_id_proj`, `heapRelations_snd`, `heap_blocks_tables`,
`consumeFold_proj`, `tablePartPure_degrees`, `combined_length`) are `UniSound`'s.
-/

namespace UniKeccakSound

open UniStatement UniSound UniKeccak LeanVM.Parameters

/-! ## The Keccak tables -/

theorem tablesKeccak_length : tablesKeccak.length = 6 := rfl

/-! ## The constraint quotient's degree -/

theorem constraintDegreeK_eq (shape : Shape) :
    Shape.constraintDegreeK shape = max (tablesKeccak.foldl (cdStep shape) 0) (degree (2 ^ shape.logMemory) 3) :=
  rfl

/-- **The constraint quotient's degree is the shape's** on the Keccak VM, for parts of every table. -/
theorem constraintRelationK_snd (shape : Shape) (parts : List TablePart) (pw : List E) (g t cv : E)
    (w : List E) (h : tablesKeccak.length ≤ parts.length) :
    (constraintRelationK shape parts pw g t cv w).2 = Shape.constraintDegreeK shape := by
  unfold constraintRelationK
  simp only [Id.run_bind, Id.run_pure]
  rw [constraintDegreeK_eq]
  refine (congrArg (fun d => max d (degree (2 ^ shape.logMemory) 3))
    (forIn_id_proj (fun s : E × Array Term × E × ℕ => s.2.2.2) (fun d x => cdStep shape d x.1) _ ?_
      _ _)).trans ?_
  · intro x s
    have hjb : opJump ≠ opBlake2s := by decide
    have hbj : opBlake2s ≠ opJump := by decide
    by_cases h1 : x.1.opcode = opJump <;> by_cases h2 : x.1.opcode = opBlake2s <;>
      simp only [h1, h2, ite_true, ite_false] <;>
      exact ⟨_, rfl, by simp [cdStep, h1, h2, hjb, hbj]⟩
  · simp only [foldl_zip_fst _ _ _ _ h]

/-! ## The tables' parts -/

/-- **The parts of a list of tables have the tables' degrees**, whatever the values. -/
theorem parts_degrees_of (ts : List Table) (heights : List ℕ) (weights : Array E) (beta : E)
    (w vs : List E) :
    (consumeFold tableReads (tablesStep heights weights beta w) ts (#[], #[]) vs).2.toList.map
        (fun p => (p.pullDegree, p.pushDegree)) = ts.map tableDegrees := by
  rw [consumeFold_proj tableReads (tablesStep heights weights beta w)
    (fun s : Array Relation × Array TablePart => s.2.toList.map fun p => (p.pullDegree, p.pushDegree))
    (fun c table => c ++ [tableDegrees table]) ?_ ts (#[], #[]) vs]
  · rw [foldl_append_map]
    rfl
  · intro x s vs
    simp only [tablesStep, Array.toList_push, List.map_append, List.map_cons, List.map_nil,
      tablePartPure_degrees]

/-- **The Keccak tables' parts have the tables' degrees.** -/
theorem tablesK_parts_degrees (heights : List ℕ) (weights : Array E) (beta : E) (w vs : List E) :
    (consumeFold tableReads (tablesStep heights weights beta w) tablesKeccak (#[], #[]) vs).2.toList.map
        (fun p => (p.pullDegree, p.pushDegree)) = tablesKeccak.map tableDegrees :=
  parts_degrees_of tablesKeccak heights weights beta w vs

theorem leafDegreeRunK_eq (parts : List TablePart)
    (hparts : parts.map (fun p => (p.pullDegree, p.pushDegree)) = tablesKeccak.map tableDegrees) (b : Block)
    (hb : ∀ t, b.leaves = .table t → t < tablesKeccak.length) :
    leafDegreeRun parts b = Shape.leafDegreeK b := by
  unfold leafDegreeRun Shape.leafDegreeK
  cases hl : b.leaves with
  | unused => rfl
  | memory => rfl
  | bytecode => rfl
  | table t =>
    have ht := hb t hl
    have hlen : parts.length = tablesKeccak.length := by
      simpa using congrArg List.length hparts
    have h1 := congrArg (fun l => l.getD t (0, 0)) hparts
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map] at h1
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem ht] at h1
    simp only [Option.map_some, Option.getD_some] at h1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : t < parts.length),
      List.getElem?_eq_getElem ht, Option.getD_some]
    rw [← h1]

/-- **`C2`'s columns in the Keccak verifier's run are the shape's.** -/
theorem c2ColumnsK_run (shape : Shape) (hlen : shape.heights.length = tablesKeccak.length)
    (parts : List TablePart)
    (hparts : parts.map (fun p => (p.pullDegree, p.pushDegree)) = tablesKeccak.map tableDegrees)
    (active pw : List E) (g t cv : E) (weights : Array E) (beta hv mp mpu bp bpu : E) (w : List E) :
    [(Column.heap, shape.heap.h, true), (Column.treeQuotient 0, shape.heap.h, true),
        (Column.treeQuotient 1, 0, true)] ++
      List.map (fun x => (Column.constraintQuotient x.2, x.1, true))
        ((chunks ((constraintRelationK shape parts pw g t cv w).2 + 1)).zip
          (List.range (chunks ((constraintRelationK shape parts pw g t cv w).2 + 1)).length)) ++
      (heapRelations shape active parts weights beta hv cv mp mpu bp bpu w
        (chunks ((constraintRelationK shape parts pw g t cv w).2 + 1))).2 = Shape.c2ColumnsK shape := by
  have hpl : tablesKeccak.length ≤ parts.length := by
    have := congrArg List.length hparts
    simp at this
    omega
  rw [constraintRelationK_snd _ _ _ _ _ _ _ hpl, heapRelations_snd]
  unfold Shape.c2ColumnsK
  congr 1
  refine flatMap_congr_mem _ _ _ fun x hx => ?_
  have hb := List.of_mem_zip hx
  rw [leafDegreeRunK_eq parts hparts x.1 (fun t ht => by
    have := heap_blocks_tables shape.logMemory shape.logBytecode shape.heights x.1 hb.1 t ht
    omega)]
  rfl

/-! ## The values at `t` and the relations -/

/-- The Keccak tables' values at `t`. -/
def tablesReadsK : ℕ := (tablesKeccak.map tableReads).sum

/-- **The values at `t`** on the Keccak VM: the tables', the memory's final counts, address and pull fingerprint,
the bytecode's final counts and pull fingerprint, `T(t)` and `Q_W(t)` (`valsCount` on `tablesKeccak`). -/
def valsCountK : ℕ := tablesReadsK + 7

/-- **The relations at `t` before Flock's claim (steps 4–6 of `reduceWithK`), and `C2`'s columns**, from the row
counts' bits, `α`, `β`, `γ`, `t` and the values. -/
def mainRelsK (shape : Shape) (pw : List E) (counts : List (List E)) (alphas : List E)
    (beta gamma t : E) (vals : List E) : Array Relation × List (Column × ℕ × Bool) :=
  let w := digits t (max shape.heap.h (shape.constraintVars + 4) + 2)
  let weights := eqKernel alphas
  let st := consumeFold tableReads (tablesStep shape.heights weights beta w) tablesKeccak (#[], #[])
    (vals.take tablesReadsK)
  let memoryFinalCount := vals.getD tablesReadsK 0
  let address := vals.getD (tablesReadsK + 1) 0
  let memoryPull := vals.getD (tablesReadsK + 2) 0
  let bytecodeFinalCount := vals.getD (tablesReadsK + 3) 0
  let bytecodePull := vals.getD (tablesReadsK + 4) 0
  let heapValue := vals.getD (tablesReadsK + 5) 0
  let constraintValue := vals.getD (tablesReadsK + 6) 0
  let cr := constraintRelationK shape st.2.toList pw gamma t constraintValue w
  let hr := heapRelations shape ((counts.zip shape.heights).map fun x => activeVanishingFromBits w x.1 x.2)
    st.2.toList weights beta heapValue constraintValue memoryPull
    (memoryPull + weights.getD 2 0 * (1 + memoryFinalCount)) bytecodePull
    (bytecodePull + weights.getD 2 0 * (1 + bytecodeFinalCount)) w (chunks (cr.2 + 1))
  let r1 := st.1.push (Relation.equal (.memory 3) (w.take shape.logMemory) memoryFinalCount)
  let r2 := r1.push (Relation.equal .address (w.take shape.logMemory) address)
  let r3 := r2.push ⟨(List.range 3).map (fun k => term (.memory k) (w.take shape.logMemory)
      (weights.getD (3 + k) 0)),
    memoryPull + beta + weights.getD 0 0 * sepMem + weights.getD 1 0 * address +
      weights.getD 2 0 * memoryFinalCount⟩
  let r4 := r3.push (Relation.equal .bytecodeFinal (w.take shape.logBytecode) bytecodeFinalCount)
  let r5 := r4.push (Relation.equal .bytecodeTuple (alphas ++ w.take shape.logBytecode)
    (bytecodePull + beta + weights.getD 2 0 * bytecodeFinalCount))
  (r5.push cr.1 ++ hr.1.toArray,
    [(.heap, shape.heap.h, true), (.treeQuotient 0, shape.heap.h, true), (.treeQuotient 1, 0, true)] ++
      List.map (fun x => (Column.constraintQuotient x.2, x.1, true))
        ((chunks (cr.2 + 1)).zip (List.range (chunks (cr.2 + 1)).length)) ++ hr.2)

/-- **Flock's claim on `q_flock`** (step 7, point claims: the ring switch's one term) and the ring map; a combination
end adds nothing. -/
def flockClaimK (rels : Array Relation) (fl : List E × Flock.End) : Array Relation × Option (List E) :=
  match fl.2 with
  | .ring map target => (rels.push ⟨[⟨.qflock, fl.1, ringTwist, 1⟩], target⟩, some map)
  | .combination _ _ => (rels, none)

/-- **`C2`'s columns in the run are the shape's** (whatever the values). -/
theorem mainRelsK_c2 (shape : Shape) (hlen : shape.heights.length = 6) (pw : List E) (counts : List (List E))
    (alphas : List E) (beta gamma t : E) (vals : List E) :
    (mainRelsK shape pw counts alphas beta gamma t vals).2 = Shape.c2ColumnsK shape := by
  unfold mainRelsK
  simp only []
  exact c2ColumnsK_run shape hlen _ (tablesK_parts_degrees _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _

theorem flockClaimK_mem (rels : Array Relation) (fl : List E × Flock.End) (r : Relation)
    (h : r ∈ rels.toList) : r ∈ (flockClaimK rels fl).1.toList := by
  unfold flockClaimK
  split <;> simp [h]

/-- **One claim per commitment in the run.** -/
theorem mainCombinedK_length (shape : Shape) (pw : List E) (counts : List (List E)) (alphas : List E)
    (beta gamma t : E) (vals : List E) (fl : List E × Flock.End) (rho : E) :
    (commitments.filterMap fun c =>
      (combine (flockClaimK (mainRelsK shape pw counts alphas beta gamma t vals).1 fl).1.toList c rho).map
        fun x => (c, x)).length = 3 := by
  apply combined_length
  · refine ⟨Relation.equal (.memory 3) ((digits t (max shape.heap.h (shape.constraintVars + 4) + 2)).take
      shape.logMemory) (vals.getD tablesReadsK 0), flockClaimK_mem _ fl _ ?_, rfl⟩
    unfold mainRelsK
    simp
  · refine ⟨Relation.equal .heap ((digits t (max shape.heap.h (shape.constraintVars + 4) + 2)).take
      shape.heap.h) (vals.getD (tablesReadsK + 5) 0), flockClaimK_mem _ fl _ ?_, rfl⟩
    unfold mainRelsK
    simp only [Array.toList_append, List.mem_append]
    exact Or.inr (heapRelations_mem _ _ _ _ _ _ _ _ _ _ _ _ _)
  · refine ⟨Relation.equal .address ((digits t (max shape.heap.h (shape.constraintVars + 4) + 2)).take
      shape.logMemory) (vals.getD (tablesReadsK + 1) 0), flockClaimK_mem _ fl _ ?_, rfl⟩
    unfold mainRelsK
    simp

end UniKeccakSound
