-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proofs are `UniSound/Ids/Deployed.lean`'s
-- (`c1Limbs`, `setupLimbs`, `layoutAligned_new`) and `UniSound/Ids/Eval.lean`'s (`c1_limbs`, `c2_limbs`,
-- `c2Columns_vars`) on the Keccak VM's layouts (`formal/UniKeccak`'s `layoutsK`, `Shape.c2ColumnsK`).
import UniSound.Ids.Deployed
import UniSound.Ids.Eval
import UniKeccakSound.Ids.Model

/-!
# The Keccak VM's stack layouts: limbs, variables, alignment

The Keccak verifier's three stacks (`layoutsOfK`, read through `UniKeccakSound.Ids.layoutOfK`) are
`StackLayout.new` of explicit column lists: `C1`'s (`c1ColsK`: `q_flock` at `h_SHA3 + 11` variables, every Keccak
table's columns and `z_T` at its height, the memory's four columns, the bytecode's final counts), `C2`'s
(`Shape.c2ColumnsK`), the setup's (`UniSound.Ids.setupCols`, the same as BLAKE2s's). At every shape:

* **`layoutAlignedK`**: each stack's blocks are aligned (`UniSound.Ids.layoutAligned_new`, for any columns);
* **`c1LimbsK`** (`C1LimbsK`): `C1`'s columns are one limb each (each named once in `c1NamesK`, checked by the
  kernel; `UniSound.Ids.limbs_new_single`), **`setupLimbsK`** (`SetupLimbsK`) the setup's two;
* **`c1_limbsK`**, **`c2_limbsK`**, **`setup_limbsK`**: every limb of a column sits at its column's variables
  (`c1VarsK`, `c2VarsK`; the setup's `lb + 4` and `lm`), by `UniSound.Ids.limbs_new_mem` (no evaluation of the
  sort).
-/

namespace UniKeccakSound.IdsNum

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.Eval UniKeccak UniKeccakSound.Ids

/-! ## The column lists -/

/-- `C1`'s columns at a shape on the Keccak VM (`layoutsK`'s `c1`). -/
def c1ColsK (S : Shape) : List (Column × ℕ × Bool) :=
  [(.qflock, S.heights.getD opBlake2s 0 + qflockRowBits, false)] ++
    tablesKeccak.flatMap (fun t ↦
      (List.range t.width).map (fun c ↦ (Column.table t.opcode c, S.heights.getD t.opcode 0, false)) ++
        [(.inverse t.opcode, S.heights.getD t.opcode 0, false)]) ++
    (List.range 4).map (fun k ↦ (Column.memory k, S.logMemory, false)) ++
    [(.bytecodeFinal, S.logBytecode, false)]

theorem layoutOfK_c1 (S : Shape) : layoutOfK S .c1 = StackLayout.new (c1ColsK S) := rfl

theorem c1LayoutK_eq (S : Shape) : c1LayoutK S = StackLayout.new (c1ColsK S) := rfl

theorem layoutOfK_c2 (S : Shape) : layoutOfK S .c2 = StackLayout.new (Shape.c2ColumnsK S) := rfl

theorem layoutOfK_setup (S : Shape) : layoutOfK S .setup = StackLayout.new (setupCols S) := rfl

theorem setupLayout_eq (S : Shape) : setupLayout S = StackLayout.new (setupCols S) := rfl

/-- **The Keccak stacks are aligned**, at every shape. -/
theorem layoutAlignedK (S : Shape) (c : Commitment) : LayoutAligned (layoutOfK S c) := by
  cases c
  · rw [layoutOfK_c1]; exact layoutAligned_new _
  · rw [layoutOfK_c2]; exact layoutAligned_new _
  · rw [layoutOfK_setup]; exact layoutAligned_new _

/-! ## `C1`'s columns: names and variables -/

/-- `C1`'s column names on the Keccak VM (no shape). -/
def c1NamesK : List Column :=
  [.qflock] ++ tablesKeccak.flatMap (fun t ↦
      (List.range t.width).map (fun c ↦ Column.table t.opcode c) ++ [.inverse t.opcode]) ++
    (List.range 4).map Column.memory ++ [.bytecodeFinal]

/-- A Keccak `C1` column's variables at a shape. -/
def c1VarsK (S : Shape) : Column → ℕ
  | .qflock => S.heights.getD opBlake2s 0 + qflockRowBits
  | .table o _ => S.heights.getD o 0
  | .inverse o => S.heights.getD o 0
  | .memory _ => S.logMemory
  | .bytecodeFinal => S.logBytecode
  | _ => 0

theorem c1ColsK_eq (S : Shape) : c1ColsK S = c1NamesK.map fun c ↦ (c, c1VarsK S c, false) := by
  simp only [c1ColsK, c1NamesK, List.map_append, List.map_flatMap, List.map_cons, List.map_nil,
    List.map_map]
  rfl

/-- A column named once in `C1`'s list is listed once, at its variables. -/
theorem c1ColsK_filter (S : Shape) (col : Column) (h : c1NamesK.filter (· == col) = [col]) :
    (c1ColsK S).filter (fun x ↦ x.1 == col) = [(col, c1VarsK S col, false)] := by
  rw [c1ColsK_eq, List.filter_map]
  have e : ((fun x : Column × ℕ × Bool ↦ x.1 == col) ∘ fun c ↦ (c, c1VarsK S c, false)) = (· == col) := rfl
  rw [e, h]
  rfl

section Kernel

set_option maxRecDepth 100000

theorem c1NamesK_table : ∀ o < 6, ∀ i < (tablesKeccak.getD o default).width,
    c1NamesK.filter (· == Column.table o i) = [.table o i] := by decide +kernel

theorem c1NamesK_inverse : ∀ o < 6, c1NamesK.filter (· == Column.inverse o) = [.inverse o] := by
  decide +kernel

theorem c1NamesK_memory : ∀ k < 4, c1NamesK.filter (· == Column.memory k) = [.memory k] := by
  decide +kernel

theorem c1NamesK_bytecodeFinal : c1NamesK.filter (· == Column.bytecodeFinal) = [.bytecodeFinal] := by
  decide +kernel

theorem c1NamesK_qflock : c1NamesK.filter (· == Column.qflock) = [.qflock] := by decide +kernel

/-- The Keccak tables' opcodes are their places. -/
theorem tablesKeccak_opcode : ∀ o < 6, (tablesKeccak.getD o default).opcode = o := by decide +kernel

end Kernel

/-! ## One limb each -/

/-- **`C1`'s columns are one limb each** on the Keccak VM, at their tables' heights (the tables' columns and
`z_T`), the memory's, the bytecode's, `q_flock`'s `h_SHA3 + 11`. -/
def C1LimbsK (S : Shape) : Prop :=
  (∀ o < 6, ∀ i < (tablesKeccak.getD o default).width, ∃ off,
      (layoutOfK S .c1).limbs (.table o i) = [(0, S.heights.getD o 0, off)]) ∧
    (∀ o < 6, ∃ off, (layoutOfK S .c1).limbs (.inverse o) = [(0, S.heights.getD o 0, off)]) ∧
    (∀ k < 4, ∃ off, (layoutOfK S .c1).limbs (.memory k) = [(0, S.logMemory, off)]) ∧
    (∃ off, (layoutOfK S .c1).limbs .bytecodeFinal = [(0, S.logBytecode, off)]) ∧
    (∃ off, (layoutOfK S .c1).limbs .qflock = [(0, S.heights.getD opBlake2s 0 + qflockRowBits, off)])

/-- **The setup's two columns are one limb each** on the Keccak VM. -/
def SetupLimbsK (S : Shape) : Prop :=
  (∃ off, (layoutOfK S .setup).limbs .address = [(0, S.logMemory, off)]) ∧
    ∃ off, (layoutOfK S .setup).limbs .bytecodeTuple = [(0, S.logBytecode + 4, off)]

/-- **`C1`'s columns are one limb each** on the Keccak VM, at every shape. -/
theorem c1LimbsK (S : Shape) : C1LimbsK S := by
  refine ⟨fun o ho i hi ↦ ?_, fun o ho ↦ ?_, fun k hk ↦ ?_, ?_, ?_⟩ <;> rw [layoutOfK_c1]
  · exact limbs_new_single _ _ _ (c1ColsK_filter S _ (c1NamesK_table o ho i hi))
  · exact limbs_new_single _ _ _ (c1ColsK_filter S _ (c1NamesK_inverse o ho))
  · exact limbs_new_single _ _ _ (c1ColsK_filter S _ (c1NamesK_memory k hk))
  · exact limbs_new_single _ _ _ (c1ColsK_filter S _ c1NamesK_bytecodeFinal)
  · exact limbs_new_single _ _ _ (c1ColsK_filter S _ c1NamesK_qflock)

/-- **The setup's two columns are one limb each** on the Keccak VM, at every shape. -/
theorem setupLimbsK (S : Shape) : SetupLimbsK S := by
  refine ⟨?_, ?_⟩ <;> rw [layoutOfK_setup] <;> exact limbs_new_single _ _ _ (by simp [setupCols])

/-! ## Every limb at its column's variables -/

/-- **`C1`'s limbs** on the Keccak VM: each at its column's variables (`c1VarsK`). -/
theorem c1_limbsK (S : Shape) (col : Column) (b : ℕ × ℕ × ℕ) (hb : b ∈ (layoutOfK S .c1).limbs col) :
    b.2.1 = c1VarsK S col := by
  rw [layoutOfK_c1] at hb
  obtain ⟨e, he⟩ := limbs_new_mem _ col b hb
  rw [c1ColsK_eq] at he
  obtain ⟨c, _, hc⟩ := List.mem_map.mp he
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, h2, -⟩ := hc
  exact h2.symm

/-- The setup's limbs: the bytecode's tuples at `lb + 4`, the addresses at `lm`. -/
theorem setup_limbsK (S : Shape) (col : Column) (b : ℕ × ℕ × ℕ) (hb : b ∈ (layoutOfK S .setup).limbs col) :
    (col = .bytecodeTuple → b.2.1 = S.logBytecode + 4) ∧ (col = .address → b.2.1 = S.logMemory) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  all_goals
    rw [layoutOfK_setup] at hb
    obtain ⟨e, he⟩ := limbs_new_mem _ col b hb
    subst h
    simp [setupCols] at he
    exact he.1

/-- **`C2`'s columns' variables** on the Keccak VM: the heap's and the tree quotient's first chunk `h`, its
second `0`, each quotient's chunk its size (`Shape.constraintDegreeK`, `Shape.leafDegreeK`). -/
def c2VarsK (S : Shape) : Column → ℕ
  | .heap => S.heap.h
  | .treeQuotient 0 => S.heap.h
  | .treeQuotient _ => 0
  | .constraintQuotient c => (chunks (Shape.constraintDegreeK S + 1)).getD c 0
  | .leafQuotient i c => match Shape.leafDegreeK (S.heap.blocks.getD i default) with
    | some d => (chunks (d + 1)).getD c 0
    | none => 0
  | _ => 0

theorem c2ColumnsK_vars (S : Shape) (col : Column) (v : ℕ) (e : Bool) (h : (col, v, e) ∈ Shape.c2ColumnsK S) :
    v = c2VarsK S col := by
  unfold Shape.c2ColumnsK at h
  dsimp only at h
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with ((h | h | h) | h) | h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    rfl
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    rfl
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    rfl
  · obtain ⟨p, hp, he⟩ := List.mem_map.mp h
    obtain ⟨-, hget⟩ := mem_zip_range_iff _ 0 p hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    simp only [c2VarsK, hget]
  · obtain ⟨⟨blk, idx⟩, hp, hx⟩ := List.mem_flatMap.mp h
    obtain ⟨-, hget⟩ := mem_zip_range_iff _ default _ hp
    dsimp only at hget hx
    rcases hd : Shape.leafDegreeK blk with _ | d
    · rw [hd] at hx
      simp at hx
    · rw [hd] at hx
      obtain ⟨p, hp', he⟩ := List.mem_map.mp hx
      obtain ⟨-, hget'⟩ := mem_zip_range_iff _ 0 p hp'
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, -⟩ := he
      simp only [c2VarsK, hget, hd]
      exact hget'.symm

/-- **`C2`'s limbs** on the Keccak VM: each at its column's variables (`c2VarsK`). -/
theorem c2_limbsK (S : Shape) (col : Column) (b : ℕ × ℕ × ℕ) (hb : b ∈ (layoutOfK S .c2).limbs col) :
    b.2.1 = c2VarsK S col := by
  rw [layoutOfK_c2] at hb
  obtain ⟨e, he⟩ := limbs_new_mem _ col b hb
  exact c2ColumnsK_vars S col _ e he

end UniKeccakSound.IdsNum

/-- info: 'UniKeccakSound.IdsNum.c1LimbsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.c1LimbsK

/-- info: 'UniKeccakSound.IdsNum.setupLimbsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.setupLimbsK

/-- info: 'UniKeccakSound.IdsNum.c2_limbsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.c2_limbsK
