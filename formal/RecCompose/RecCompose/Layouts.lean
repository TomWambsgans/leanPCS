-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md and AGENTS.md.
import UniComplete.Reference
import RecCompose.Bridge

/-!
# π1's calls' layout words are the Keccak π1-rec3's

**`pi1CallsLayouts_of_real`**: `Pi1CallsLayouts D` at the real deployment. π1's calls are `Data.pi1Calls`, and their
layout words (word 1 of each, constants the Rust wrote) are the Keccak π1-rec3's at the 128-signature reference shape
(`w1 i`, `UniKeccak.layoutWordsK RecGraphKeccak.Pi1.keccak128`). `layoutWordsK` sorts (`StackLayout.new`'s
`List.mergeSort`, well-founded: the kernel does not reduce it), so the two numbers a word holds are taken off the sort
first (UniComplete's generic `stackLayout_vars`, `pieceWords`, `heapLayout_h`, `heapLayout_blocks_sum`, for any
column list and any heap):

* `stackLayout_words`: the words a stack's blocks fill are its pieces' (`UniComplete.pieceWords`), in any order;
* `c2_pieceWordsK`: `C2`'s words on the Keccak VM (`UniKeccak.Shape.c2ColumnsK`) as the heap's, the tree and
  constraint quotients' and the blocks' leaf quotients' (`leafWordsK`, `Shape.leafDegreeK`), from the heap's
  unsorted blocks;

then the kernel evaluates the three stacks' words (`0x49fc000`, `0x28ce003`, `0x500000`) and variables (`27`, `26`,
`23`), and compares the three 32-byte words with `Data.pi1Calls`' (`data_layout0`, `1`, `2`: the only decisions that read
`Data`, at its three layout words, which the setup roots do not change).
-/

namespace RecCompose

open UniStatement UniComplete

/-- A fold that adds `g x` is a sum. -/
theorem foldl_add_eq {β : Type} (g : β → ℕ) (f : ℕ → β → ℕ) (hf : ∀ a x, f a x = a + g x) :
    ∀ (L : List β) (a : ℕ), L.foldl f a = a + (L.map g).sum
  | [], a => by simp
  | x :: L, a => by
    rw [List.foldl_cons, hf, foldl_add_eq g f hf L, List.map_cons, List.sum_cons]
    omega

theorem stackFold_fst (L : List (Column × ℕ × ℕ)) (acc : Array (Column × ℕ × ℕ × ℕ) × ℕ) :
    ((L.foldl (fun (acc : Array (Column × ℕ × ℕ × ℕ) × ℕ) (x : Column × ℕ × ℕ) ↦
      (acc.1.push (x.1, x.2.1, x.2.2, acc.2), acc.2 + 2 ^ x.2.2)) acc).1.toList.map fun b ↦ 2 ^ b.2.2.1) =
      (acc.1.toList.map fun b ↦ 2 ^ b.2.2.1) ++ L.map fun p ↦ 2 ^ p.2.2 := by
  induction L generalizing acc with
  | nil => simp
  | cons p L ih =>
    rw [List.foldl_cons, ih]
    simp

/-- **A stack's words are its pieces' words**, the sort aside. -/
theorem stackLayout_words (cols : List (Column × ℕ × Bool)) : (StackLayout.new cols).words = pieceWords cols := by
  unfold StackLayout.new StackLayout.words
  dsimp only
  rw [foldl_add_eq (fun b : Column × ℕ × ℕ × ℕ ↦ 2 ^ b.2.2.1) _ (fun a x ↦ by obtain ⟨_, _, _, _⟩ := x; rfl),
    stackFold_fst]
  simp only [List.map_nil, List.nil_append, zero_add]
  rw [sum_map_mergeSort, pieces_words]

/-! ## The Keccak VM's stacks -/

/-- `C1`'s columns on the Keccak VM (`UniKeccak.layoutsK`' `c1`). -/
def c1ColumnsK (shape : Shape) : List (Column × ℕ × Bool) :=
  let heights := shape.heights
  [(.qflock, heights.getD opBlake2s 0 + UniKeccak.qflockRowBits, false)] ++
    tablesKeccak.flatMap (fun t ↦
      let h := heights.getD t.opcode 0
      (List.range t.width).map (fun c ↦ (Column.table t.opcode c, h, false)) ++
        [(.inverse t.opcode, h, false)]) ++
    (List.range 4).map (fun k ↦ (Column.memory k, shape.logMemory, false)) ++
    [(.bytecodeFinal, shape.logBytecode, false)]

theorem layoutsOfK_eq (s : Shape) :
    UniKeccak.layoutsOfK s = [(.c1, StackLayout.new (c1ColumnsK s)), (.c2, StackLayout.new (UniKeccak.Shape.c2ColumnsK s)),
      (.setup, StackLayout.new (setupColumns s))] := rfl

/-- **A heap block's leaf quotient's words** in the Keccak VM's `C2`: its `leafDegreeK`'s chunks, `E`-valued; none for
an unused block. -/
def leafWordsK (b : Block) : ℕ :=
  match UniKeccak.Shape.leafDegreeK b with
  | none => 0
  | some d => ((chunks (d + 1)).map fun e ↦ 3 * 2 ^ e).sum

theorem leafWordsK_position (l : Leaves) (r p p' : ℕ) : leafWordsK ⟨l, r, p⟩ = leafWordsK ⟨l, r, p'⟩ := rfl

/-- **`C2`'s words on the Keccak VM**: the heap's and the tree quotient's (`E`-valued, `h`, `h`, `0` variables), the
constraint quotient's chunks, and the heap blocks' leaf quotients. -/
theorem c2_pieceWordsK (s : Shape) :
    pieceWords (UniKeccak.Shape.c2ColumnsK s) =
      3 * 2 ^ s.heap.h + 3 * 2 ^ s.heap.h + 3 * 2 ^ 0 +
        ((chunks (UniKeccak.Shape.constraintDegreeK s + 1)).map fun e ↦ 3 * 2 ^ e).sum +
          (s.heap.blocks.map leafWordsK).sum := by
  unfold UniKeccak.Shape.c2ColumnsK
  dsimp only
  rw [pieceWords_append, pieceWords_append]
  congr 1
  · simp only [pieceWords, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_map,
      Function.comp_def, ite_true]
    rw [sum_zip_range_fst (chunks (UniKeccak.Shape.constraintDegreeK s + 1)) fun e ↦ 3 * 2 ^ e]
    omega
  · rw [pieceWords, sum_map_flatMap, ← sum_zip_range_fst s.heap.blocks leafWordsK]
    congr 1
    refine List.map_congr_left fun x _ ↦ ?_
    unfold leafWordsK
    cases h : UniKeccak.Shape.leafDegreeK x.1 with
    | none => rfl
    | some d =>
      simp only [List.map_map, Function.comp_def, ite_true]
      exact sum_zip_range_fst _ fun e ↦ 3 * 2 ^ e

/-! ## The reference shape's three words (`RecGraphKeccak.Pi1.keccak128`, 128 signatures) -/

open RecGraphKeccak.Pi1 (keccak128)

/-- `C2`'s words at the reference shape, from the heap's unsorted blocks (no sort left). -/
def c2WordsK : ℕ :=
  3 * 2 ^ (log2Ceil (heapTotal keccak128.logMemory keccak128.logBytecode keccak128.heights) + 1) +
    3 * 2 ^ (log2Ceil (heapTotal keccak128.logMemory keccak128.logBytecode keccak128.heights) + 1) + 3 * 2 ^ 0 +
    ((chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1)).map fun e ↦ 3 * 2 ^ e).sum +
    (((heapUsed keccak128.logMemory keccak128.logBytecode keccak128.heights).map fun x ↦
        leafWordsK ⟨x.1, x.2, 0⟩).sum +
      ((unusedBlocks (2 ^ log2Ceil (heapTotal keccak128.logMemory keccak128.logBytecode keccak128.heights))
        (heapTotal keccak128.logMemory keccak128.logBytecode keccak128.heights)).map leafWordsK).sum)

theorem keccak128_c2Pieces : pieceWords (UniKeccak.Shape.c2ColumnsK keccak128) = c2WordsK := by
  rw [c2_pieceWordsK, Shape.heap, heapLayout_h,
    heapLayout_blocks_sum leafWordsK (fun l r p p' ↦ leafWordsK_position l r p p')]
  rfl

/-- `C1`'s words: `77,578,240`. -/
theorem keccak128_c1Words : pieceWords (c1ColumnsK keccak128) = 0x49fc000 := by decide +kernel

/-- `C2`'s words: `42,786,819`. -/
theorem keccak128_c2Words : c2WordsK = 0x28ce003 := by decide +kernel

/-- The setup's words: `5,242,880`. -/
theorem keccak128_setupWords : pieceWords (setupColumns keccak128) = 0x500000 := by decide +kernel

/-- `C1`'s `27` variables. -/
theorem keccak128_c1Vars : (StackLayout.new (c1ColumnsK keccak128)).vars = 27 := by
  rw [stackLayout_vars, keccak128_c1Words]
  decide +kernel

/-- `C2`'s `26` variables. -/
theorem keccak128_c2Vars : (StackLayout.new (UniKeccak.Shape.c2ColumnsK keccak128)).vars = 26 := by
  rw [stackLayout_vars, keccak128_c2Pieces, keccak128_c2Words]
  decide +kernel

/-- The setup's `23` variables. -/
theorem keccak128_setupVars : (StackLayout.new (setupColumns keccak128)).vars = 23 := by
  rw [stackLayout_vars, keccak128_setupWords]
  decide +kernel

/-- **The Keccak π1-rec3's three layout words at the reference shape**, their numbers off the sort. -/
theorem w1_eq :
    w1 0 = layoutWord keccak128 0x5501 27 0x49fc000 ∧
    w1 1 = layoutWord keccak128 0x5502 26 0x28ce003 ∧
    w1 2 = layoutWord keccak128 0x5503 23 0x500000 := by
  refine ⟨?_, ?_, ?_⟩
  · show layoutWord keccak128 0x5501 (StackLayout.new (c1ColumnsK keccak128)).vars
      (StackLayout.new (c1ColumnsK keccak128)).words = _
    rw [keccak128_c1Vars, stackLayout_words, keccak128_c1Words]
  · show layoutWord keccak128 0x5502 (StackLayout.new (UniKeccak.Shape.c2ColumnsK keccak128)).vars
      (StackLayout.new (UniKeccak.Shape.c2ColumnsK keccak128)).words = _
    rw [keccak128_c2Vars, stackLayout_words, keccak128_c2Pieces, keccak128_c2Words]
  · show layoutWord keccak128 0x5503 (StackLayout.new (setupColumns keccak128)).vars
      (StackLayout.new (setupColumns keccak128)).words = _
    rw [keccak128_setupVars, stackLayout_words, keccak128_setupWords]

/-! ## `Data.pi1Calls`' layout words (the only decisions here that read `Data`) -/

theorem data_layout0 : (RecStatement.Data.pi1Calls.getD 0 []).getD 1 default =
    RecStatement.CallWord.const (layoutWord keccak128 0x5501 27 0x49fc000) := by decide +kernel

theorem data_layout1 : (RecStatement.Data.pi1Calls.getD 1 []).getD 1 default =
    RecStatement.CallWord.const (layoutWord keccak128 0x5502 26 0x28ce003) := by decide +kernel

theorem data_layout2 : (RecStatement.Data.pi1Calls.getD 2 []).getD 1 default =
    RecStatement.CallWord.const (layoutWord keccak128 0x5503 23 0x500000) := by decide +kernel

/-- `Data.pi1Calls`' layout words are the Keccak π1-rec3's at the reference shape. -/
theorem data_pi1Calls_layouts : ∀ ci < 3, (RecStatement.Data.pi1Calls.getD ci []).getD 1 default =
    RecStatement.CallWord.const (w1 ci) := by
  obtain ⟨h0, h1, h2⟩ := w1_eq
  intro ci hci
  interval_cases ci
  · rw [h0]; exact data_layout0
  · rw [h1]; exact data_layout1
  · rw [h2]; exact data_layout2

/-- **π1's calls' layout words are the Keccak π1-rec3's**, at the real deployment. -/
theorem pi1CallsLayouts_of_real {D : RecStatement.RecDeployment} (hD : D.Real) : Pi1CallsLayouts D := by
  intro ci hci
  rw [hD.2.1]
  exact data_pi1Calls_layouts ci hci

end RecCompose

/-- info: 'RecCompose.pi1CallsLayouts_of_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi1CallsLayouts_of_real
