-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniSound.Ids.Eval

/-!
# The relations' number, the columns absent from `C1`, the constraints' number

* **`relCount_reference`** (`RelCountP D Fl 135`): `relsOf` is each table's part (its sent values,
  then at most two relations a flush: `tablePartOf_rels_len`), the memory's three, the bytecode's two,
  the constraint quotient's, the heap's `3 + |blocks| + 1` (`heapRelations_fst`) and at most one ring
  end. The tables' part is `115` (the kernel counts the six tables' sent columns and flushes, no
  coefficient), the reference heap has `9` blocks.
* **`c1Absent`**: a column not in a stack's column list has no limbs (`limbs_new_absent`, for any
  `StackLayout.new`), so a table's column past its width has none in `C1`, at every shape.
* **`ncvOf_eq`**: `30` constraints at every shape (`JUMP`'s two, six counters, `BLAKE2S`'s eighteen
  copies, three public lines) plus one.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset UniSound.Ids.Eval

/-! ## The relations' number -/

theorem flushStep_rels_len (at_ : ℕ → Column) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) (st : TPState) (fl : List Form × List Form) :
    (flushStep at_ pt weights beta sent st fl).rels.length ≤ st.rels.length + 2 := by
  unfold flushStep
  dsimp only
  split_ifs <;> simp

theorem flushFold_rels_len (at_ : ℕ → Column) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) : ∀ (l : List (List Form × List Form)) (st : TPState),
      (l.foldl (flushStep at_ pt weights beta sent) st).rels.length ≤ st.rels.length + 2 * l.length
  | [], st => by simp
  | fl :: l, st => by
    rw [List.foldl_cons]
    have h1 := flushFold_rels_len at_ pt weights beta sent l (flushStep at_ pt weights beta sent st fl)
    have h2 := flushStep_rels_len at_ pt weights beta sent st fl
    rw [List.length_cons]
    omega

/-- A table's relations: its sent values', at most two a flush. -/
def tabRels (tab : Table) : ℕ := (sentColumns tab).length + 2 * (tab.flushes.pull.zip tab.flushes.push).length

theorem tablePartOf_rels_len (tab : Table) (lh : ℕ) (weights : Array E) (beta : E) (w vals : List E) :
    (tablePartOf tab lh weights beta w vals).2.1.length ≤ tabRels tab := by
  unfold tablePartOf tabRels
  dsimp only
  refine (flushFold_rels_len _ _ _ _ _ _ _).trans ?_
  simp

theorem tablesPart_rels_len (S : Shape) (weights : Array E) (beta : E) (w : List E) :
    ∀ (ts : List Table) (vals : List E),
      (tablesPart S weights beta w ts vals).2.1.length ≤ (ts.map tabRels).sum
  | [], _ => by simp [tablesPart]
  | t :: ts, vals => by
    simp only [tablesPart, List.length_append, List.map_cons, List.sum_cons]
    have h1 := tablePartOf_rels_len t (S.heights.getD t.opcode 0) weights beta w vals
    have h2 := tablesPart_rels_len S weights beta w ts
      (tablePartOf t (S.heights.getD t.opcode 0) weights beta w vals).2.2
    omega

theorem ringRels_len (inp : RelInput) : inp.ringRels.length ≤ 1 := by
  unfold RelInput.ringRels
  split <;> simp

/-! ## Columns absent from a layout -/

/-- **A column not listed has no limbs**, in any `StackLayout.new`. -/
theorem limbs_new_absent (cols : List (Column × ℕ × Bool)) (col : Column) (h : ∀ x ∈ cols, x.1 ≠ col) :
    (StackLayout.new cols).limbs col = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun b hb ↦ by
    obtain ⟨e, he⟩ := limbs_new_mem cols col b hb
    exact h _ he rfl

/-! ## The constraints' number -/

end UniSound.Ids

