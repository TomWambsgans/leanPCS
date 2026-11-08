-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The method is `UniSound/Ids/Deployed.lean`'s
-- (`heapGood_reference`) and `UniKeccakSound/Fs/LayerK.lean`'s (`c1Vars_ref`, `c2Vars_ref`, `setupVars_ref`) at
-- the reference Keccak shape.
import UniKeccakSound.IdsNum.Layouts
import UniKeccakSound.IdsNum.Functionals15
import UniKeccakSound.Ids.Final
import UniKeccakSound.Fs.LayerK

/-!
# The deployment's constants at the reference Keccak shape

The reference Keccak shape `keccakShapeOf 721598 [24260, 36229, 24626, 35812, 15509, 17712]` (`keccakRefShape`,
also `UniKeccakSound.keccakRef` and `keccak128`, by `rfl`; 128 signatures) is `⟨20, 18, [15, 16, 15, 16, 14, 15]⟩`
(`keccakRef_eq`). There:

* **`heapGoodK_ref`** (`HeapGood`): `HeapLayout.new`'s sort replaced by its result (`Fs/LayerK.lean`'s `heapRefL`,
  by `mergeSort_eq_of`: a permutation, sorted, the order antisymmetric on it), the kernel lays the blocks out
  (`heapBlocksK`: `2^22` positions, eight used blocks from leaf `2^21`, two unused), and they fill the leaves end to
  end, aligned;
* **`functionalsK_ref`** (`FunctionalsCorrect (h_SHA3)`, `h_SHA3 = 15`: `functionalsCorrect15`) and
  **`height2K_ref`** (`2 ≤ h_SHA3`);
* **`layoutVarsSmall3K_ref`** (`LayoutVarsSmall3K`): `C1` `27` variables, `C2` `26`, the setup `23`
  (`c1Vars_ref`, `c2Vars_ref`, `setupVars_ref`).

The basis (`BetaCantor`, `UniSound.Ids.betaCantor`) and the layouts' alignment and limbs (`Layouts.lean`) hold at
every shape.
-/

namespace UniKeccakSound.IdsNum

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak UniKeccakSound UniKeccakSound.Ids

/-! ## The reference shape -/

/-- **The reference Keccak shape**: `2^20` memory cells, `2^18` instructions, the heights. -/
theorem keccakRef_eq : keccakRefShape = ⟨20, 18, [15, 16, 15, 16, 14, 15]⟩ := by
  show keccakShapeOf 721598 [24260, 36229, 24626, 35812, 15509, 17712] = _
  unfold keccakShapeOf shapeWith
  congr 1

theorem keccak128_eq_refShape : keccak128 = keccakRefShape := rfl

/-- `SHA3`'s height at the reference shape: `15`. -/
theorem hSha3_ref : keccakRefShape.heights.getD opBlake2s 0 = 15 := by
  rw [keccakRef_eq]; rfl

/-! ## The heap (`HeapGood`) -/

/-- **The reference shape's used blocks, sorted** (no evaluation of `mergeSort`). -/
theorem heapSortedK :
    ([(Leaves.memory, 20), (.bytecode, 18)] ++ (List.range [15, 16, 15, 16, 14, 15].length).map
        fun t ↦ (Leaves.table t, [15, 16, 15, 16, 14, 15].getD t 0)).mergeSort
      (fun a b ↦ b.2 < a.2 || (a.2 == b.2 && a.1.order ≤ b.1.order)) = heapRefL :=
  mergeSort_eq_of UniKeccakSound.heapLe UniKeccakSound.heapLe_trans UniKeccakSound.heapLe_total
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The reference heap's blocks: the eight used (largest first, from leaf `2^21`), then two unused blocks of
`2^14` and `2^19` leaves. -/
def heapBlocksK : List (Leaves × ℕ × ℕ) :=
  [(.memory, 20, 2097152), (.bytecode, 18, 3145728), (.table 1, 16, 3407872), (.table 3, 16, 3473408),
    (.table 0, 15, 3538944), (.table 2, 15, 3571712), (.table 5, 15, 3604480), (.table 4, 14, 3637248),
    (.unused, 14, 3653632), (.unused, 19, 3670016)]

/-- **The reference heap**: `2^22` positions, its blocks. -/
theorem heapK_ref : keccakRefShape.heap.h = 22 ∧ keccakRefShape.heap.blocks.map Block.toTuple = heapBlocksK := by
  rw [keccakRef_eq]
  unfold Shape.heap HeapLayout.new
  dsimp only
  rw [heapSortedK]
  simp only [unusedBlocks, Std.Legacy.Range.forIn_eq_forIn_range']
  decide +kernel

theorem heapK_blocks_ref : keccakRefShape.heap.blocks = heapBlocksK.map Block.ofTuple := by
  rw [← heapK_ref.2, List.map_map]
  conv_lhs => rw [← List.map_id keccakRefShape.heap.blocks]
  exact List.map_congr_left fun b _ ↦ by cases b; rfl

/-- **The heap's blocks at the reference Keccak shape** fill the leaves end to end, aligned. -/
theorem heapGoodK_ref : HeapGood keccakRefShape := by
  unfold HeapGood
  rw [heapK_ref.1, heapK_blocks_ref]
  refine ⟨by norm_num, by norm_num, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  rw [keccakRef_eq]
  simp [heapBlocksK, Block.ofTuple]

/-! ## The coordinate functionals and `SHA3`'s height -/

/-- **The coordinate functionals at `SHA3`'s height** (`15`) invert the Moore matrix, at the reference shape. -/
theorem functionalsK_ref (D : KDeployment) (hD : D.shape = keccakRefShape) :
    FunctionalsCorrect (D.shape.heights.getD opBlake2s 0) := by
  rw [hD, hSha3_ref]
  exact functionalsCorrect15

/-- **`2 ≤ h_SHA3`** at the reference shape. -/
theorem height2K_ref (D : KDeployment) (hD : D.shape = keccakRefShape) : 2 ≤ D.shape.heights.getD opBlake2s 0 := by
  rw [hD, hSha3_ref]
  norm_num

/-! ## The stacks' variables (`LayoutVarsSmall3K`) -/

theorem layoutOfK_c1_vars_ref : (layoutOfK keccakRefShape .c1).vars = 27 := c1Vars_ref

theorem layoutOfK_c2_vars_ref : (layoutOfK keccakRefShape .c2).vars = 26 := c2Vars_ref

theorem layoutOfK_setup_vars_ref : (layoutOfK keccakRefShape .setup).vars = 23 := setupVars_ref

/-- **The three stacks have fewer than `256` variables** at the reference shape: `27`, `26`, `23`. -/
theorem layoutVarsSmall3K_ref (D : KDeployment) (hD : D.shape = keccakRefShape) : LayoutVarsSmall3K D := by
  intro c
  rw [hD]
  cases c
  · rw [layoutOfK_c1_vars_ref]; norm_num
  · rw [layoutOfK_c2_vars_ref]; norm_num
  · rw [layoutOfK_setup_vars_ref]; norm_num

end UniKeccakSound.IdsNum

/-- info: 'UniKeccakSound.IdsNum.heapGoodK_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.heapGoodK_ref

/-- info: 'UniKeccakSound.IdsNum.functionalsK_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.functionalsK_ref

/-- info: 'UniKeccakSound.IdsNum.layoutVarsSmall3K_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.layoutVarsSmall3K_ref
