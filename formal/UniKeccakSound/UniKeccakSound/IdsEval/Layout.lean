-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The layouts are `formal/UniKeccak`'s `layoutsK`,
-- `layoutsOfK`, `Shape.c2ColumnsK`; the proofs are `UniSound/Ids/Eval.lean`'s (`c1_limbs`, `c2_limbs`,
-- `setup_limbs`) on the Keccak VM's columns.
import UniKeccakSound.Ids.FlockReg
import UniSound.Ids.Eval

/-!
# The Keccak layouts' columns

Each column of the Keccak VM's three stacks is laid at its variables (`StackLayout.new`), within the batch's:

* **`c1_limbsK`**: `C1`'s at `c1VarsK` (`q_flock` at `h_SHA3 + 11`, a table's columns and `z_T` at its height, the
  memory's at `lm`, the bytecode's final counts at `lb`);
* **`c2_limbsK`**: `C2`'s at `c2VarsK` (the quotients' chunks from `constraintDegreeK`, `leafDegreeK`);
* **`setup_limbsK`**: the setup's (the bytecode's tuples at `lb + 4`, the addresses at `lm`);
* **`qvOf_c1K`**: `weightAtK`'s `q_flock` variables, `h_SHA3 + 11`.
-/

namespace UniKeccakSound.IdsEval

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.Eval UniKeccak UniKeccakSound.Ids

theorem layoutsOfK_eq (S : Shape) :
    layoutsOfK S = [(.c1, layoutOfK S .c1), (.c2, layoutOfK S .c2), (.setup, layoutOfK S .setup)] := rfl

theorem layoutOfK_c1' (S : Shape) : layoutOfK S .c1 = StackLayout.new (c1ColsK S) := rfl

theorem layoutOfK_c2 (S : Shape) : layoutOfK S .c2 = StackLayout.new (UniKeccak.Shape.c2ColumnsK S) := rfl

theorem layoutOfK_setup (S : Shape) : layoutOfK S .setup = StackLayout.new (setupCols S) := rfl

theorem vars_le_batchK (S : Shape) (c : Commitment) : (layoutOfK S c).vars ≤ batchVarsK S := by
  unfold batchVarsK varsOf
  rw [layoutsOfK_eq]
  refine le_foldl_max _ 0 _ (Or.inl ?_)
  cases c <;> simp

theorem limb_le_batchK (S : Shape) (c : Commitment) (hL : LayoutAligned (layoutOfK S c)) {col : Column}
    {b : ℕ × ℕ × ℕ} (hb : b ∈ (layoutOfK S c).limbs col) : b.2.1 ≤ batchVarsK S :=
  (limb_le_vars hL hb).trans (vars_le_batchK S c)

/-! ## `C1` -/

/-- `C1`'s column names on the Keccak VM (no shape). -/
def c1NamesK : List Column :=
  [.qflock] ++ tablesKeccak.flatMap (fun t ↦
      (List.range t.width).map (fun c ↦ Column.table t.opcode c) ++ [.inverse t.opcode]) ++
    (List.range 4).map Column.memory ++ [.bytecodeFinal]

/-- A `C1` column's variables at a shape on the Keccak VM. -/
def c1VarsK (S : Shape) : Column → ℕ
  | .qflock => S.heights.getD opSha3 0 + qflockRowBits
  | .table o _ => S.heights.getD o 0
  | .inverse o => S.heights.getD o 0
  | .memory _ => S.logMemory
  | .bytecodeFinal => S.logBytecode
  | _ => 0

theorem c1ColsK_eq (S : Shape) : c1ColsK S = c1NamesK.map fun c ↦ (c, c1VarsK S c, false) := by
  simp only [c1ColsK, c1NamesK, List.map_append, List.map_flatMap, List.map_cons, List.map_nil, List.map_map]
  rfl

/-- **`C1`'s limbs** on the Keccak VM: each at its column's variables (`c1VarsK`), within the batch's. -/
theorem c1_limbsK (S : Shape) (col : Column) (b : ℕ × ℕ × ℕ) (hb : b ∈ (layoutOfK S .c1).limbs col) :
    b.2.1 = c1VarsK S col ∧ b.2.1 ≤ batchVarsK S := by
  refine ⟨?_, limb_le_batchK S .c1 (by rw [layoutOfK_c1']; exact layoutAligned_new _) hb⟩
  rw [layoutOfK_c1'] at hb
  obtain ⟨e, he⟩ := limbs_new_mem _ col b hb
  rw [c1ColsK_eq] at he
  obtain ⟨c, _, hc⟩ := List.mem_map.mp he
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, h2, -⟩ := hc
  exact h2.symm

/-- **`weightAtK`'s `q_flock` variables** in `C1`'s layout: `h_SHA3 + 11`. -/
theorem qvOf_c1K (S : Shape) : qvOf (layoutOfK S .c1) = S.heights.getD opSha3 0 + qflockRowBits := by
  obtain ⟨off, hoff⟩ := c1LayoutK_qflock S
  unfold qvOf
  rw [show layoutOfK S .c1 = c1LayoutK S from rfl, hoff]
  rfl

/-! ## `C2` -/

/-- **`C2`'s columns' variables** on the Keccak VM. -/
def c2VarsK (S : Shape) : Column → ℕ
  | .heap => S.heap.h
  | .treeQuotient 0 => S.heap.h
  | .treeQuotient _ => 0
  | .constraintQuotient c => (chunks (UniKeccak.Shape.constraintDegreeK S + 1)).getD c 0
  | .leafQuotient i c => match UniKeccak.Shape.leafDegreeK (S.heap.blocks.getD i default) with
    | some d => (chunks (d + 1)).getD c 0
    | none => 0
  | _ => 0

theorem c2ColumnsK_vars (S : Shape) (col : Column) (v : ℕ) (e : Bool)
    (h : (col, v, e) ∈ UniKeccak.Shape.c2ColumnsK S) : v = c2VarsK S col := by
  unfold UniKeccak.Shape.c2ColumnsK at h
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
    rcases hd : UniKeccak.Shape.leafDegreeK blk with _ | d
    · rw [hd] at hx
      simp at hx
    · rw [hd] at hx
      obtain ⟨p, hp', he⟩ := List.mem_map.mp hx
      obtain ⟨-, hget'⟩ := mem_zip_range_iff _ 0 p hp'
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, -⟩ := he
      simp only [c2VarsK, hget, hd]
      exact hget'.symm

/-- **`C2`'s limbs** on the Keccak VM: each at its column's variables, within the batch's. -/
theorem c2_limbsK (S : Shape) (col : Column) (b : ℕ × ℕ × ℕ) (hb : b ∈ (layoutOfK S .c2).limbs col) :
    b.2.1 = c2VarsK S col ∧ b.2.1 ≤ batchVarsK S := by
  refine ⟨?_, limb_le_batchK S .c2 (by rw [layoutOfK_c2]; exact layoutAligned_new _) hb⟩
  rw [layoutOfK_c2] at hb
  obtain ⟨e, he⟩ := limbs_new_mem _ col b hb
  exact c2ColumnsK_vars S col _ e he

/-! ## The setup -/

/-- The setup's limbs: the bytecode's tuples at `lb + 4`, the addresses at `lm`. -/
theorem setup_limbsK (S : Shape) (col : Column) (b : ℕ × ℕ × ℕ) (hb : b ∈ (layoutOfK S .setup).limbs col) :
    (col = .bytecodeTuple → b.2.1 = S.logBytecode + 4) ∧ (col = .address → b.2.1 = S.logMemory) ∧
      b.2.1 ≤ batchVarsK S := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_,
    limb_le_batchK S .setup (by rw [layoutOfK_setup]; exact layoutAligned_new _) hb⟩
  all_goals
    rw [layoutOfK_setup] at hb
    obtain ⟨e, he⟩ := limbs_new_mem _ col b hb
    subst h
    simp [setupCols] at he
    exact he.1

end UniKeccakSound.IdsEval
