-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The technique (the `Id.run do` loops as folds) is
-- `formal/UniSound`'s (`UniSound.Ids.Eval.constraintRelation_eq`, `crOf_deg`).
import RecGraphKeccak.Sim.Tables
import UniSound.Ids.Eval

/-!
# `Q_W`'s identity on the Keccak VM, as folds, and its degree

`UniKeccak.constraintRelationK` is an `Id.run do` block with two loops; here as folds (`crOfK`: a table's step
`crStepK`, the `SHA3` lanes' copies `copyStepK` with `END_BIT`'s known part, the public lines `UniSound`'s
`lineStep`), `constraintRelationK_eq`, and its degree: **`degreeSpecK : DegreeSpecK`**, the degree is
`Shape.constraintDegreeK keccak128` (any shape, with a part per table: `crOfK_deg`).
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph RecGraph.Pi1 RecGraph.Sim
  RecGraphKeccak.Pi1 UniSound.Ids.Eval

/-- One lane's step of the `SHA3` copies' loop, on (known, terms, power). -/
def copyStepK (o r : ℕ) (columns : List String) (w y : List E) (lift gamma : E) (s : E × Array Term × E)
    (c : ℕ) : E × Array Term × E :=
  match keccakSlot (columns.getD c "") with
  | some slot =>
    ((if keccakSlotOffset (columns.getD c "") != 0 then
        s.1 + s.2.2 * lift * eK (keccakSlotOffset (columns.getD c "")) else s.1),
      (s.2.1.push (term (.table o c) (w.take r) (s.2.2 * lift))).push (term (.qflockSlot slot) y (s.2.2 * lift)),
      s.2.2 * gamma)
  | none => s

/-- One table's step of `constraintRelationK`'s loop, on (known, terms, power, degree). -/
def crStepK (shape : UniStatement.Shape) (gamma t : E) (w : List E) (s : E × Array Term × E × ℕ)
    (x : Table × TablePart) : E × Array Term × E × ℕ :=
  let r := shape.heights.getD x.1.opcode 0
  let n := 2 ^ r
  let lift := vanishingRatio w r shape.constraintVars
  let s1 : E × Array Term × E × ℕ := if x.1.opcode = opJump then
      (s.1 + s.2.2.1 * lift * (x.2.sent.getD (colIdx x.1.columns "b") none).getD 0 +
          s.2.2.1 * gamma * lift * (x.2.sent.getD (colIdx x.1.columns "v_cond") none).getD 0 *
            ((x.2.sent.getD (colIdx x.1.columns "b") none).getD 0 + 1),
        s.2.1.push (term (.table x.1.opcode (colIdx x.1.columns "w")) (w.take r)
          (s.2.2.1 * lift * (x.2.sent.getD (colIdx x.1.columns "v_cond") none).getD 0)),
        s.2.2.1 * gamma * gamma, max s.2.2.2 (degree n 2))
    else s
  let s2 : E × Array Term × E × ℕ := (s1.1 + s1.2.2.1 * lift,
    s1.2.1.push (term (.inverse x.1.opcode) (w.take r)
      (s1.2.2.1 * lift * x.1.countColumns.foldl (fun acc c ↦ acc * (x.2.sent.getD c none).getD 0) 1)),
    s1.2.2.1 * gamma, max s1.2.2.2 (degree ((n - 1) * (1 + x.1.countColumns.length)) n))
  if x.1.opcode = opSha3 then
    let inner := (List.range x.1.width).foldl
      (copyStepK x.1.opcode r x.1.columns w (coordinatesAt t (coordinateFunctionals r)) lift gamma)
      (s2.1, s2.2.1, s2.2.2.1)
    (inner.1, inner.2.1, inner.2.2, max s2.2.2.2 (degree (r * (n / 2)) n))
  else s2

/-- **`constraintRelationK`, as folds.** -/
def crOfK (shape : UniStatement.Shape) (parts : List TablePart) (publicWords : List E) (gamma t constraintValue : E)
    (w : List E) : Relation × ℕ :=
  let s := (tablesKeccak.zip parts).foldl (crStepK shape gamma t w) (0, #[], 1, 0)
  let s' := ((UniSound.Ids.linesOf publicWords).zip (List.range 3)).foldl (lineStep shape gamma t w)
    (s.1, s.2.1, s.2.2.1)
  (⟨s'.2.1.toList, constraintValue * w.getD shape.constraintVars 0 + s'.1⟩,
    max s.2.2.2 (degree (2 ^ shape.logMemory) 3))

/-- **`constraintRelationK` is its folds.** -/
theorem constraintRelationK_eq (shape : UniStatement.Shape) (parts : List TablePart) (publicWords : List E)
    (gamma t constraintValue : E) (w : List E) :
    UniKeccak.constraintRelationK shape parts publicWords gamma t constraintValue w =
      crOfK shape parts publicWords gamma t constraintValue w := by
  unfold UniKeccak.constraintRelationK crOfK
  simp only [Id.run]
  rw [forIn_id_eq_foldl' _ _ _ (crStepK shape gamma t w)]
  · simp only [pure_bind, List.forIn_pure_yield_eq_foldl]
    rfl
  · intro x s
    by_cases hj : x.1.opcode = opJump
    · have hb : ¬ x.1.opcode = opSha3 := by rw [hj]; decide
      simp only [crStepK, ite_eq_left hj, ite_eq_right hb]
    · by_cases hb : x.1.opcode = opSha3
      · simp only [crStepK, ite_eq_right hj, ite_eq_left hb]
        rw [forIn_id_eq_foldl' _ _ _ (copyStepK x.1.opcode (shape.heights.getD x.1.opcode 0) x.1.columns w
          (coordinatesAt t (coordinateFunctionals (shape.heights.getD x.1.opcode 0)))
          (vanishingRatio w (shape.heights.getD x.1.opcode 0) shape.constraintVars) gamma)]
        · rfl
        · intro c s'
          unfold copyStepK
          rcases keccakSlot (x.1.columns.getD c "") with _ | slot
          · rfl
          · by_cases ho : (keccakSlotOffset (x.1.columns.getD c "") != 0) = true
            · simp only [ho, ↓reduceIte]
            · simp only [ho, Bool.false_eq_true, ↓reduceIte]
      · simp only [crStepK, ite_eq_right hj, ite_eq_right hb]

/-! ## The degree -/

/-- A table's step of `Shape.constraintDegreeK`'s fold. -/
def cdStepK (shape : UniStatement.Shape) (d : ℕ) (table : Table) : ℕ :=
  let r := shape.heights.getD table.opcode 0
  let n := 2 ^ r
  let d := if table.opcode = opJump then max d (degree n 2) else d
  let d := max d (degree ((n - 1) * (1 + table.countColumns.length)) n)
  if table.opcode = opSha3 then max d (degree (r * (n / 2)) n) else d

theorem crFoldK_deg (S : UniStatement.Shape) (gamma t : E) (w : List E) : ∀ (L : List (Table × TablePart))
    (s : E × Array Term × E × ℕ), (L.foldl (crStepK S gamma t w) s).2.2.2 =
      (L.map Prod.fst).foldl (cdStepK S) s.2.2.2
  | [], _ => rfl
  | x :: L, s => by
    rw [List.foldl_cons, crFoldK_deg S gamma t w L, List.map_cons, List.foldl_cons]
    congr 1
    unfold crStepK cdStepK
    dsimp only
    by_cases hj : x.1.opcode = opJump
    · have hb : ¬ x.1.opcode = opSha3 := by rw [hj]; decide
      simp only [ite_eq_left hj, ite_eq_right hb]
    · by_cases hb : x.1.opcode = opSha3
      · simp only [ite_eq_right hj, ite_eq_left hb]
      · simp only [ite_eq_right hj, ite_eq_right hb]

/-- **The constraint relation's degree is the shape's** (`constraintDegreeK`), with a part per table. -/
theorem crOfK_deg (S : UniStatement.Shape) (parts : List TablePart) (pw : List E) (gamma t cv : E) (w : List E)
    (hlen : tablesKeccak.length ≤ parts.length) :
    (crOfK S parts pw gamma t cv w).2 = UniKeccak.Shape.constraintDegreeK S := by
  unfold crOfK UniKeccak.Shape.constraintDegreeK
  dsimp only
  rw [crFoldK_deg, List.map_fst_zip hlen]
  rfl

/-- **`DegreeSpecK`**: `Q_W`'s degree at `keccak128` is `Shape.constraintDegreeK keccak128`. -/
theorem degreeSpecK : DegreeSpecK := by
  intro partsE pwE gammaE tE cvE wE hl
  rw [constraintRelationK_eq]
  exact crOfK_deg _ _ _ _ _ _ _ (by rw [hl]; decide)

end RecGraphKeccak.Sim
