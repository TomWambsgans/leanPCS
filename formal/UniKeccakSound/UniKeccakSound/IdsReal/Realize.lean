-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The argument is `UniSound/Ids/LvRealize.lean`'s
-- (`lvRealizes`), for `formal/KeccakVm`'s instance and `formal/UniKeccak`'s `kvStack`; the boundary lemmas follow
-- `Lv42/Protocol/LeanIsa/Bus.lean`'s (`boundaryTuples_push`, `boundaryTuples_pull`), `flushTuples_eq_opcode`
-- `Heap/LeanIsa.lean`'s.
import UniSound.Ids.LvRealize
import UniSound.Ids.Deployed
import UniKeccakSound.Ids.FlockReg
import UniKeccakSound.IdsReal.Forms

/-!
# The heap read off `C1` realizes the Keccak VM's bus (`KvRealizesK`)

**`kvRealizesK`**: for a Keccak deployment `D` whose heap is well formed (`HeapGood`, of which only the memory's
and the bytecode's heights at most `24` are used, for `basisValueInv`), wherever the copies hold (`CopiesK`; only
its counts in range are used), the heap the verifier reads off `C1` (`hdK`) realizes the bus of `C1`'s Keccak VM
stack (`Heap.Realizes`, `kvStack`): its push and its pull tuples are permutations of `(D.inst rows).tuples q side`.

`UniSound.Ids.lvRealizes`' argument, for `KeccakVm.keccakIsaInstance`:

1. **The forms are the Keccak VM's flushes** (`IdsReal.rowTuplesK_eq`, `Forms.lean`).
2. **The rows** (`LvR.map_rowPosition`, `LvR.activePositions_perm`, shape-generic).
3. **The values** (`rowK_eq`): the Keccak VM's row `x` of opcode table `j` is `C1`'s row `rowPosition x`, every
   column (the lanes included) being committed and read back as `kvColumn` (`column_kvStack`): no copy is needed
   (unlike Lv42's `BLAKE2S` limbs, read off `q_flock`). A table's block holds its flushes (`tableBlockK_side`).
4. **The boundary** (`memTupleKK_eq`, `bcTupleKK_eq`, `finKK_eq`, `kv_boundaryTuples_push`/`_pull`): the memory's
   and the bytecode's pairs and the state boundary are the instance's six boundary blocks; the setup's address
   column is `g^x` (`suValK_address`) and its bytecode slots are `tupleSlotK` (`slotValK_eq`), by
   `basisValueInv`.
5. **The heap** (`blocks_sideK`, `LvR.heap_flatMap`): `HeapLayout.new`'s blocks are the memory's, the
   bytecode's, the six tables' and unused ones; assembled as `LvR.realizes` is.
-/

namespace UniKeccakSound.IdsReal

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.LvR UniKeccak UniKeccakSound.Ids
open Lv42.Protocol
open Lv42.Protocol.LeanIsa (opIdx Sizes tupleOf)
open KeccakVm.KeccakIsa (Col kappa keccakIsaμ memCol bfcntCol)

/-! ## The values: the Keccak VM's rows are `C1`'s -/

section Rows

variable (D : KDeployment) (rows : List ℕ) (c : Stk)

/-- **The Keccak VM's row `x` of opcode table `j` is `C1`'s row `rowPosition x`**, every column committed. -/
theorem rowK_eq (j : Fin 6) (x : Fin (2 ^ (D.inst rows).τ (opIdx j))) :
    (D.inst rows).row (kvStack D.prog (D.sizes rows) D.shape c) (opIdx j) x =
      fun i ↦ c1RowK D c j (rowPosition (rows.getD j 0) (D.shape.heights.getD j 0) x.val) i.val := by
  funext i
  exact (column_kvStack D.prog (D.sizes rows) D.shape c ⟨opIdx j, i⟩ x).trans (Vector.get_ofFn _ _)

/-- **A table's block holds the Keccak VM's executed rows' flushes**, on one side. -/
theorem table_side_permK (j : Fin 6) (r : ℕ) (hr : r = D.shape.heights.getD j 0)
    (hcount : rows.getD j 0 ≤ 2 ^ r) (side : Side) :
    ((List.range (2 ^ r)).flatMap fun x ↦ if isActive x (rows.getD j 0) r then
      (if side = .push then (tablesKeccak.getD j default).flushes.push
        else (tablesKeccak.getD j default).flushes.pull).map (fun tup ↦ tupleK tup (c1RowK D c j x)) else []).Perm
      (Heap.tableTuples (D.inst rows) (kvStack D.prog (D.sizes rows) D.shape c) (opIdx j) side) := by
  subst hr
  rw [flatMap_ite_filter]
  refine ((activePositions_perm _ _).symm.flatMap_right _).trans ?_
  rw [← map_rowPosition hcount, List.flatMap_map]
  refine List.Perm.trans (List.Perm.of_eq (List.flatMap_congr fun x hx ↦ ?_))
    (Heap.rows_perm_tableTuples (D.inst rows) (kvStack D.prog (D.sizes rows) D.shape c) (opIdx j) side)
  have hxc : x < rows.getD j 0 := List.mem_range.mp hx
  have hx' : x < 2 ^ (D.inst rows).τ (opIdx j) :=
    lt_of_lt_of_le hxc ((D.inst rows).rows_le (opIdx j))
  exact (rowTuplesK_eq _ _ _ j side x hx' _ (rowK_eq D rows c j ⟨x, hx'⟩)).symm

/-- **A table's block's tuples of a side** are the Keccak VM's table's. -/
theorem tableBlockK_side (j : Fin 6) (b : Block) (hr : b.r = D.shape.heights.getD j 0)
    (hcount : rows.getD j 0 ≤ 2 ^ b.r) (side : Side) :
    (lbSide (tableBlockKK D c rows b j) side).Perm
      (Heap.tableTuples (D.inst rows) (kvStack D.prog (D.sizes rows) D.shape c) (opIdx j) side) := by
  cases side
  · exact table_side_permK D rows c j b.r hr hcount .push
  · exact table_side_permK D rows c j b.r hr hcount .pull

end Rows

/-! ## The heap's blocks -/

theorem blockKK_key (D : KDeployment) (c : Stk) (rows : List ℕ) (b : Block) :
    blockKK D c rows b = blockKK D c rows ⟨b.leaves, b.r, 0⟩ := by
  obtain ⟨l, r, p⟩ := b
  cases l <;> rfl

theorem blockKK_unused (D : KDeployment) (c : Stk) (rows : List ℕ) (r : ℕ) (side : Side) :
    lbSide (blockKK D c rows ⟨.unused, r, 0⟩) side = [] := by
  cases side
  · exact Heap.LeafBlock.pushes_unused r
  · exact Heap.LeafBlock.pulls_unused r

/-- **The heap's blocks, side by side**: the memory's, the bytecode's, the six tables'. -/
theorem blocks_sideK (D : KDeployment) (c : Stk) (rows : List ℕ) (side : Side) :
    ((D.shape.heap.blocks.map (blockKK D c rows)).flatMap (lbSide · side)).Perm
      (lbSide (blockKK D c rows ⟨.memory, D.shape.logMemory, 0⟩) side ++
        lbSide (blockKK D c rows ⟨.bytecode, D.shape.logBytecode, 0⟩) side ++
          (List.range 6).flatMap fun t ↦
            lbSide (blockKK D c rows ⟨.table t, D.shape.heights.getD t 0, 0⟩) side) := by
  have h := heap_flatMap D.shape (fun k ↦ lbSide (blockKK D c rows ⟨k.1, k.2, 0⟩) side)
    (fun r ↦ blockKK_unused D c rows r side)
  rw [List.flatMap_map] at h
  rw [List.flatMap_map]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_map,
    D.valid.1] at h
  refine List.Perm.trans (List.Perm.of_eq ?_) h
  exact List.flatMap_congr fun b _ ↦ by rw [blockKK_key]; rfl

/-- The memory and bytecode blocks' heights fit `BasisValueInv`'s (`LvR.heights_le`, for a shape). -/
theorem heights_leS (S : UniStatement.Shape) (hHG : HeapGood S) : S.logMemory ≤ 24 ∧ S.logBytecode ≤ 24 := by
  obtain ⟨_, hh, hsum, -⟩ := hHG
  have hk := heap_flatMap S (fun k : Leaves × ℕ ↦ if k.1 = .unused then [] else [2 ^ k.2])
    (fun r ↦ by simp)
  have hmem : ∀ k ∈ [(Leaves.memory, S.logMemory), (Leaves.bytecode, S.logBytecode)],
      2 ^ k.2 ≤ 2 ^ (S.heap.h - 1) := by
    intro k hk'
    have hin : 2 ^ k.2 ∈ (S.heap.blocks.map blockKey).flatMap
        (fun k : Leaves × ℕ ↦ if k.1 = .unused then [] else [2 ^ k.2]) := by
      refine hk.symm.subset (List.mem_flatMap.mpr ⟨k, List.mem_append_left _ hk', ?_⟩)
      rcases List.mem_cons.mp hk' with rfl | hk'
      · simp
      · rw [List.mem_singleton] at hk'
        subst hk'
        simp
    obtain ⟨k', hk'', hin'⟩ := List.mem_flatMap.mp hin
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk''
    rw [← hsum]
    have : 2 ^ k.2 = 2 ^ b.r := by
      by_cases hu : b.leaves = .unused
      · simp [blockKey, hu] at hin'
      · simpa [blockKey, hu] using hin'
    rw [this]
    exact le_sum_of_mem' (List.mem_map.mpr ⟨b, hb, rfl⟩)
  have h1 := hmem _ (List.mem_cons_self ..)
  have h2 := hmem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  simp only at *
  omega

/-! ## The setup (`setupStackK`) -/

theorem setupStkK_eq (D : KDeployment) (w : ℕ) (tOff aOff : ℕ)
    (ht : (setupLayout D.shape).limbs .bytecodeTuple = [(0, D.shape.logBytecode + 4, tOff)])
    (ha : (setupLayout D.shape).limbs .address = [(0, D.shape.logMemory, aOff)])
    (hw : w < 2 ^ (setupLayout D.shape).vars) :
    setupStkK D w = if tOff ≤ w ∧ w < tOff + 2 ^ (D.shape.logBytecode + 4) then
        ((Array.ofFn (n := 16) fun s ↦ bCoefficients D.prog.logSize
          (Array.ofFn (n := 2 ^ D.prog.logSize) fun i ↦ tupleSlotK D.prog i s.val)).getD ((w - tOff) % 16)
            #[]).getD ((w - tOff) / 16) 0
      else if aOff ≤ w ∧ w < aOff + 2 ^ D.shape.logMemory then
        (bCoefficients D.shape.logMemory (Array.ofFn (n := 2 ^ D.shape.logMemory) fun i ↦
          LeanVM.Parameters.gpow i.val)).getD (w - aOff) 0
      else 0 := by
  simp only [setupStkK, setupStackK, ht, ha, List.headD_cons]
  simp [Array.getD_eq_getD_getElem?, hw]

/-- **The setup's address column is `g^x`** (`basisValueInv`). -/
theorem suValK_address (D : KDeployment) (hlm : D.shape.logMemory ≤ 24) (x : ℕ)
    (hx : x < 2 ^ D.shape.logMemory) : suValK D .address D.shape.logMemory x = LeanVM.Parameters.gpow x := by
  obtain ⟨tOff, aOff, ht, ha, hdis, htv, hav⟩ := setup_facts D.shape
  have hblock : c1Block (setupLayout D.shape) (setupStkK D) .address = bCoefficients D.shape.logMemory
      (Array.ofFn (n := 2 ^ D.shape.logMemory) fun i ↦ LeanVM.Parameters.gpow i.val) := by
    simp only [c1Block, ha]
    apply Array.ext
    · simp [bCoefficients_size]
    · intro i h1 h2
      simp only [Array.getElem_ofFn]
      rw [Array.size_ofFn] at h1
      rw [setupStkK_eq D _ tOff aOff ht ha (by omega), ite_neg_of (by omega), ite_pos_of (by omega)]
      simp [Array.getD_eq_getD_getElem?, h2]
  rw [suValK, hblock, basisValueInv _ hlm _ (by simp) x hx]
  simp [Array.getD_eq_getD_getElem?, hx]

/-- **The setup's bytecode slot `s` is `tupleSlotK`** (`basisValueInv`). -/
theorem slotValK_eq (D : KDeployment) (hlb : D.shape.logBytecode ≤ 24) (s : ℕ)
    (hs : s < 16) (x : Fin (2 ^ D.prog.logSize)) : slotValK D s x.val = tupleSlotK D.prog x s := by
  obtain ⟨tOff, aOff, ht, ha, hdis, htv, hav⟩ := setup_facts D.shape
  have hlbe := D.logBytecode_eq
  have hoff : tupleOffK D = tOff := by simp [tupleOffK, ht]
  have harr : (Array.ofFn (n := 2 ^ D.shape.logBytecode) fun k ↦ setupStkK D (tupleOffK D + s + 16 * k.val)) =
      bCoefficients D.prog.logSize (Array.ofFn (n := 2 ^ D.prog.logSize) fun i ↦ tupleSlotK D.prog i s) := by
    apply Array.ext
    · simp [bCoefficients_size, hlbe]
    · intro k h1 h2
      simp only [Array.getElem_ofFn]
      rw [Array.size_ofFn] at h1
      have hk16 : s + 16 * k < 2 ^ (D.shape.logBytecode + 4) := by
        rw [pow_add]; norm_num; omega
      rw [hoff, setupStkK_eq D _ tOff aOff ht ha (by omega), ite_pos_of (by omega)]
      have e1 : (tOff + s + 16 * k - tOff) % 16 = s := by omega
      have e2 : (tOff + s + 16 * k - tOff) / 16 = k := by omega
      rw [e1, e2]
      simp [Array.getD_eq_getD_getElem?, hs, h2]
  rw [slotValK, harr, hlbe, basisValueInv _ (hlbe ▸ hlb) _ (by simp) x.val x.isLt]
  simp [Array.getD_eq_getD_getElem?]

/-! ## The Keccak VM's boundary (`Lv42`'s, with the Keccak VM's entries) -/

section Boundary

variable (prog : KeccakVm.Program) (s : Sizes) (q : LeanVM.Protocol.Column (keccakIsaμ prog s))

/-- A cell of a column of the Keccak VM's instance. -/
abbrev kcell (col : Col) (x : Fin (2 ^ kappa prog s col)) : K :=
  ((KeccakVm.keccakIsaInstance prog s).column q col).values.get x

/-- The memory columns' cells of row `x`: the three limbs. -/
abbrev kMemLimbs (x : Fin (2 ^ s.logMem)) : List K :=
  [kcell prog s q (memCol 0) x, kcell prog s q (memCol 1) x, kcell prog s q (memCol 2) x]

/-- The program's entry at slot `i`, its eight coordinates (`KeccakVm.entry`). -/
abbrev kEntryList (i : Fin (2 ^ prog.logSize)) : List K :=
  (List.finRange 8).map fun k ↦ (KeccakVm.entry (prog.code i))[k]

/-- A boundary block's coordinates, the separator first, are the tuple of the rest (`Lv42`'s
`coords_coordCell`, for the Keccak VM's `coords`). -/
theorem coords_coordCellK (I : M3Instance) {κ : ℕ} (σ : K) (rest : List (Coord I.toShape κ))
    (q : LeanVM.Protocol.Column I.μ) (x : Fin (2 ^ κ)) :
    (KeccakVm.KeccakIsa.coords (.const σ :: rest)).map (fun co ↦ I.coordCell q co x) =
      tupleOf σ (rest.map fun co ↦ I.coordCell q co x).toArray := by
  apply Vector.ext
  intro k hk
  simp only [KeccakVm.KeccakIsa.coords, tupleOf, Vector.getElem_map, Vector.getElem_ofFn]
  rcases k with _ | k
  · rfl
  · simp only [List.getD_cons_succ, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
      List.getElem?_toArray, List.getElem?_map]
    by_cases hr : k < rest.length
    · rw [List.getD_eq_getElem _ _ hr, List.getElem?_eq_getElem hr]
      rfl
    · rw [List.getD_eq_default _ _ (by omega), List.getElem?_eq_none (by omega)]
      rfl

/-- The push side's boundary tuples: the initial state, the memory seed, the bytecode seed. -/
theorem kv_boundaryTuples_push :
    (KeccakVm.keccakIsaInstance prog s).boundaryTuples q .push =
      [tupleOf (LeanVM.Parameters.gpow 0) #[1, 1]] ++
      ((List.finRange (2 ^ s.logMem)).map fun x : Fin (2 ^ s.logMem) ↦
        tupleOf (LeanVM.Parameters.gpow 1) (#[LeanVM.Parameters.gpow x, 1] ++ (kMemLimbs prog s q x).toArray)) ++
      ((List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        tupleOf (LeanVM.Parameters.gpow 2) (#[LeanVM.Parameters.gpow i, 1] ++ (kEntryList prog i).toArray)) := by
  simp only [M3Instance.boundaryTuples, KeccakVm.KeccakIsa.boundary, List.filter_cons, List.filter_nil,
    reduceCtorEq, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  refine congrArg₂ (fun a b : List (Vector K 16) ↦ a ++ b) ?_
    (congrArg₂ (fun a b : List (Vector K 16) ↦ a ++ b) ?_ ?_)
  · rw [show List.finRange (2 ^ 0) = [0] from rfl, List.map_singleton]
    refine congrArg (· :: []) ((coords_coordCellK (KeccakVm.keccakIsaInstance prog s) _ _ q 0).trans ?_)
    rfl
  · refine List.map_congr_left fun x _ ↦ (coords_coordCellK (KeccakVm.keccakIsaInstance prog s) _ _ q
        x).trans ?_
    simp [M3Instance.coordCell, idxColumn, LeanVM.Protocol.powersTable, Vector.get_ofFn]
    rfl
  · refine List.map_congr_left fun i _ ↦ (coords_coordCellK (KeccakVm.keccakIsaInstance prog s) _ _ q
        i).trans ?_
    have hl : ((Coord.known (idxColumn prog.logSize) :: Coord.const 1 ::
        (List.finRange 8).map fun k ↦ (Coord.known (KeccakVm.KeccakIsa.entryColumn prog k) :
          Coord (KeccakVm.KeccakIsa.shape prog s) prog.logSize)).map
        fun co ↦ (KeccakVm.keccakIsaInstance prog s).coordCell q co i) =
          LeanVM.Parameters.gpow i :: 1 :: kEntryList prog i := by
      simp only [List.map_cons, List.map_map]
      refine congrArg₂ _ (Vector.get_ofFn _ _) (congrArg₂ _ rfl (List.map_congr_left fun k _ ↦ ?_))
      exact Vector.get_ofFn _ _
    exact (congrArg (fun l : List K ↦ tupleOf (LeanVM.Parameters.gpow 2) l.toArray) hl).trans rfl

/-- The pull side's boundary tuples: the final state, the memory finalize, the bytecode finalize. -/
theorem kv_boundaryTuples_pull :
    (KeccakVm.keccakIsaInstance prog s).boundaryTuples q .pull =
      [tupleOf (LeanVM.Parameters.gpow 0) #[prog.finalPc, 1]] ++
      ((List.finRange (2 ^ s.logMem)).map fun x : Fin (2 ^ s.logMem) ↦
        tupleOf (LeanVM.Parameters.gpow 1)
          (#[LeanVM.Parameters.gpow x, kcell prog s q (memCol 3) x] ++ (kMemLimbs prog s q x).toArray)) ++
      ((List.finRange (2 ^ prog.logSize)).map fun i : Fin (2 ^ prog.logSize) ↦
        tupleOf (LeanVM.Parameters.gpow 2)
          (#[LeanVM.Parameters.gpow i, kcell prog s q bfcntCol i] ++ (kEntryList prog i).toArray)) := by
  simp only [M3Instance.boundaryTuples, KeccakVm.KeccakIsa.boundary, List.filter_cons, List.filter_nil,
    reduceCtorEq, decide_true, decide_false, ite_true, Bool.false_eq_true, ite_false,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  refine congrArg₂ (fun a b : List (Vector K 16) ↦ a ++ b) ?_
    (congrArg₂ (fun a b : List (Vector K 16) ↦ a ++ b) ?_ ?_)
  · rw [show List.finRange (2 ^ 0) = [0] from rfl, List.map_singleton]
    refine congrArg (· :: []) ((coords_coordCellK (KeccakVm.keccakIsaInstance prog s) _ _ q 0).trans ?_)
    rfl
  · refine List.map_congr_left fun x _ ↦ (coords_coordCellK (KeccakVm.keccakIsaInstance prog s) _ _ q
        x).trans ?_
    simp [M3Instance.coordCell, idxColumn, LeanVM.Protocol.powersTable, Vector.get_ofFn]
    rfl
  · refine List.map_congr_left fun i _ ↦ (coords_coordCellK (KeccakVm.keccakIsaInstance prog s) _ _ q
        i).trans ?_
    have hl : ((Coord.known (idxColumn prog.logSize) :: Coord.committed bfcntCol rfl ::
        (List.finRange 8).map fun k ↦ (Coord.known (KeccakVm.KeccakIsa.entryColumn prog k) :
          Coord (KeccakVm.KeccakIsa.shape prog s) prog.logSize)).map
        fun co ↦ (KeccakVm.keccakIsaInstance prog s).coordCell q co i) =
          LeanVM.Parameters.gpow i :: kcell prog s q bfcntCol i :: kEntryList prog i := by
      simp only [List.map_cons, List.map_map]
      refine congrArg₂ _ (Vector.get_ofFn _ _) (congrArg₂ _ rfl (List.map_congr_left fun k _ ↦ ?_))
      exact Vector.get_ofFn _ _
    exact (congrArg (fun l : List K ↦ tupleOf (LeanVM.Parameters.gpow 2) l.toArray) hl).trans rfl

/-- The column groups (tables `0, 1, 2`) flush nothing. -/
theorem kv_tableTuples_nil (side : Side) (j : Fin 9) (hj : decide (3 ≤ j.val) = false) :
    Heap.tableTuples (KeccakVm.keccakIsaInstance prog s) q j side = [] := by
  obtain ⟨_ | _ | _ | k, hk⟩ := j
  · rfl
  · rfl
  · rfl
  · simp at hj

/-- `flushTuples` is the opcode tables'. -/
theorem kv_flushTuples_eq_opcode (side : Side) :
    (KeccakVm.keccakIsaInstance prog s).flushTuples q side =
      (List.finRange 6).flatMap fun j ↦
        Heap.tableTuples (KeccakVm.keccakIsaInstance prog s) q (opIdx j) side := by
  rw [Heap.flushTuples_eq]
  show (List.finRange 9).flatMap
    (fun j : Fin 9 ↦ Heap.tableTuples (KeccakVm.keccakIsaInstance prog s) q j side) = _
  rw [← Heap.LeanIsa.flatMap_filter_of_nil (fun j : Fin 9 ↦ decide (3 ≤ j.val)) _ _
    fun j _ hj ↦ kv_tableTuples_nil prog s q side j hj]
  exact (congrArg (fun l ↦ List.flatMap _ l) Heap.LeanIsa.finRange_filter).trans (List.flatMap_map ..)

end Boundary

/-! ## The boundary read off `C1` -/

section BoundaryC1

variable (D : KDeployment) (rows : List ℕ) (c : Stk)

theorem kcell_mem (i : Fin 4) (x : Fin (2 ^ (D.sizes rows).logMem)) :
    kcell D.prog (D.sizes rows) (kvStack D.prog (D.sizes rows) D.shape c) (memCol i) x =
      c1ValK D c (.memory i.val) D.shape.logMemory x.val :=
  (column_kvStack D.prog (D.sizes rows) D.shape c (memCol i) x).trans (Vector.get_ofFn _ _)

theorem kcell_bfcnt (x : Fin (2 ^ D.prog.logSize)) :
    kcell D.prog (D.sizes rows) (kvStack D.prog (D.sizes rows) D.shape c) bfcntCol x =
      c1ValK D c .bytecodeFinal D.shape.logBytecode x.val := by
  refine (column_kvStack D.prog (D.sizes rows) D.shape c bfcntCol x).trans ((Vector.get_ofFn _ _).trans ?_)
  rw [D.logBytecode_eq]
  rfl

/-- **The memory's tuple of cell `x`** is the Keccak VM's memory boundary tuple. -/
theorem memTupleKK_eq (hlm : D.shape.logMemory ≤ 24) (cnt : K) (x : Fin (2 ^ (D.sizes rows).logMem)) :
    memTupleKK D c cnt x.val = tupleOf (LeanVM.Parameters.gpow 1)
      (#[LeanVM.Parameters.gpow x.val, cnt] ++
        (kMemLimbs D.prog (D.sizes rows) (kvStack D.prog (D.sizes rows) D.shape c) x).toArray) := by
  have hsu := suValK_address D hlm x.val x.isLt
  apply Vector.ext
  intro k hk
  simp only [memTupleKK, tupleOf, Vector.getElem_ofFn, kMemLimbs, kcell_mem D rows c]
  interval_cases k <;> simp [hsu, toK_sepMem]

/-- **The bytecode's tuple of instruction `i`** is the Keccak VM's bytecode boundary tuple. -/
theorem bcTupleKK_eq (hlb : D.shape.logBytecode ≤ 24) (cnt : K) (i : Fin (2 ^ D.prog.logSize)) :
    bcTupleKK D cnt i.val = tupleOf (LeanVM.Parameters.gpow 2)
      (#[LeanVM.Parameters.gpow i.val, cnt] ++ (kEntryList D.prog i).toArray) := by
  apply Vector.ext
  intro k hk
  simp only [bcTupleKK, tupleOf, Vector.getElem_ofFn, slotValK_eq D hlb k hk i, tupleSlotK, kEntryList]
  interval_cases k <;> simp [ofBits_four]

/-- The state boundary's pull is the Keccak VM's. -/
theorem finKK_eq : finKK D = tupleOf (LeanVM.Parameters.gpow 0) #[D.prog.finalPc, 1] := by
  apply Vector.ext
  intro k hk
  simp only [finKK, tupleOf, Vector.getElem_ofFn]
  interval_cases k <;> simp [toK_gpow, KeccakVm.Program.finalPc, D.logBytecode_eq]

end BoundaryC1

/-! ## The heap realizes the Keccak VM's bus -/

/-- **The heap read off `C1` realizes the Keccak VM's bus** wherever the counts are in range, for memory and
bytecode heights at most `24`. -/
theorem realizesK (D : KDeployment) (hlm : D.shape.logMemory ≤ 24) (hlb : D.shape.logBytecode ≤ 24)
    (s : USt) (c : Stk) (hfit : CountsFit D.shape s.2) :
    Heap.Realizes (I := D.inst s.2) (kvStack D.prog (D.sizes s.2) D.shape c) (hdK D c s) := by
  obtain ⟨-, hfit⟩ := hfit
  set rows := s.2 with hrows
  set q := kvStack D.prog (D.sizes rows) D.shape c with hq
  have htab : ∀ side : Side, ((List.range 6).flatMap fun t ↦
      lbSide (blockKK D c rows ⟨.table t, D.shape.heights.getD t 0, 0⟩) side).Perm
        ((List.finRange 6).flatMap fun j ↦ Heap.tableTuples (D.inst rows) q (opIdx j) side) := by
    intro side
    rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
    exact List.Perm.flatMap_left _ fun j _ ↦
      tableBlockK_side D rows c j ⟨.table j.val, _, 0⟩ rfl (hfit j j.isLt) side
  have hrange : List.range (2 ^ D.shape.logBytecode) = List.range (2 ^ D.prog.logSize) := by
    rw [D.logBytecode_eq]
  constructor
  · -- push
    have hmem : lbSide (blockKK D c rows ⟨.memory, D.shape.logMemory, 0⟩) .push =
        (List.finRange (2 ^ (D.sizes rows).logMem)).map fun x ↦ tupleOf (LeanVM.Parameters.gpow 1)
          (#[LeanVM.Parameters.gpow x.val, 1] ++ (kMemLimbs D.prog (D.sizes rows) q x).toArray) := by
      refine (Heap.LeafBlock.pushes_pair _ _ _).trans ?_
      exact map_range_eq_finRange _ _ _ fun x ↦ memTupleKK_eq D rows c hlm 1 x
    have hbc : lbSide (blockKK D c rows ⟨.bytecode, D.shape.logBytecode, 0⟩) .push =
        (List.finRange (2 ^ D.prog.logSize)).map fun i ↦ tupleOf (LeanVM.Parameters.gpow 2)
          (#[LeanVM.Parameters.gpow i.val, 1] ++ (kEntryList D.prog i).toArray) := by
      refine (Heap.LeafBlock.pushes_pair _ _ _).trans ?_
      rw [hrange]
      exact map_range_eq_finRange _ _ _ fun i ↦ bcTupleKK_eq D hlb 1 i
    have hb := blocks_sideK D c rows .push
    rw [hmem, hbc] at hb
    show ((D.shape.heap.blocks.map (blockKK D c rows)).flatMap (lbSide · .push) ++ [initK]).Perm
      ((D.inst rows).flushTuples q .push ++ (D.inst rows).boundaryTuples q .push)
    rw [kv_flushTuples_eq_opcode, kv_boundaryTuples_push, initK_eq]
    refine (hb.append_right _).trans ?_
    refine (((htab .push).append_left _).append_right _).trans ?_
    exact perm_shuffle _ _ _ _
  · -- pull
    have hmem : lbSide (blockKK D c rows ⟨.memory, D.shape.logMemory, 0⟩) .pull =
        (List.finRange (2 ^ (D.sizes rows).logMem)).map fun x ↦ tupleOf (LeanVM.Parameters.gpow 1)
          (#[LeanVM.Parameters.gpow x.val, kcell D.prog (D.sizes rows) q (memCol 3) x] ++
            (kMemLimbs D.prog (D.sizes rows) q x).toArray) := by
      refine (Heap.LeafBlock.pulls_pair _ _ _).trans ?_
      refine map_range_eq_finRange _ _ _ fun x ↦ ?_
      rw [kcell_mem D rows c 3 x]
      exact memTupleKK_eq D rows c hlm _ x
    have hbc : lbSide (blockKK D c rows ⟨.bytecode, D.shape.logBytecode, 0⟩) .pull =
        (List.finRange (2 ^ D.prog.logSize)).map fun i ↦ tupleOf (LeanVM.Parameters.gpow 2)
          (#[LeanVM.Parameters.gpow i.val, kcell D.prog (D.sizes rows) q bfcntCol i] ++
            (kEntryList D.prog i).toArray) := by
      refine (Heap.LeafBlock.pulls_pair _ _ _).trans ?_
      rw [hrange]
      refine map_range_eq_finRange _ _ _ fun i ↦ ?_
      rw [kcell_bfcnt D rows c i]
      exact bcTupleKK_eq D hlb _ i
    have hb := blocks_sideK D c rows .pull
    rw [hmem, hbc] at hb
    show ((D.shape.heap.blocks.map (blockKK D c rows)).flatMap (lbSide · .pull) ++ [finKK D]).Perm
      ((D.inst rows).flushTuples q .pull ++ (D.inst rows).boundaryTuples q .pull)
    rw [kv_flushTuples_eq_opcode, kv_boundaryTuples_pull, finKK_eq]
    refine (hb.append_right _).trans ?_
    refine (((htab .pull).append_left _).append_right _).trans ?_
    exact perm_shuffle _ _ _ _

/-- **The heap read off `C1` realizes the Keccak VM's bus** wherever the copies hold (`KvRealizesK`), for a
deployment whose heap is well formed (`HeapGood`: the memory's and the bytecode's heights at most `24`). -/
theorem kvRealizesK (D : KDeployment) (hHG : HeapGood D.shape) : KvRealizesK D := by
  intro s c hcp
  obtain ⟨hlm, hlb⟩ := heights_leS D.shape hHG
  exact realizesK D hlm hlb s c hcp.1

end UniKeccakSound.IdsReal

/-- info: 'UniKeccakSound.IdsReal.kvRealizesK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsReal.kvRealizesK
