-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `formal/Lv42`'s `Protocol/LeanIsa/Complete.lean`,
-- `Protocol/LeanIsa/Read.lean` and the stack of a witness of `Protocol/LeanIsa.lean` (leanerVM `mumbai` f0393df4,
-- MIT OR Apache-2.0), for the Keccak VM's instance, all of whose columns are committed.
module

public import KeccakArith.CTheorem

/-!
# Completeness of the Keccak VM's relation

`stackOf F prog s w`: the stack of a witness `w` of `kEnsemble prog` at the sizes `s`: every column at its block (Lv42's
`stackOf`), the opcode tables' and the two blocks' cells, and as the Flock column `QFLOCK` the honest column
`F.gen` of the states the executed `SHA3` rows step (`sha3States`: the input lanes, `END_BIT` XORed into lane 16).

`kvHonest_stackOf`: a witness satisfying the Keccak VM's constraint statement stacks, at the sizes it carries
(`witnessSizes`), into a column satisfying `KvHonest`: `M3Holds` from the equivalences of `ARelation` on the executed rows
and the zero padding rows on the others (`M3Honest`'s padding clause), and `KeccakAux` from `F.holds_gen` (the region),
`F.in_gen` (the input copies, `END_BIT` cancelling in characteristic two) and `F.step_of_holds` with the Keccak relation
of the rows (the output copies).

`kvCompleteness`: a valid execution of the Keccak VM with at most `2^32` rows of every opcode has a stack satisfying
`KvHonest` at the sizes its run carries.
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Arithmetization KeccakVm KeccakVm.KeccakIsa
open LeanVM.Protocol (Column M3Table toM3_constraints_iff boolVec boolIndex boolVec_cast)
open Lv42.Protocol (M3Instance Side M3Holds M3Honest)
open Lv42.Protocol.LeanIsa (Sizes sideOf counted)
open Lv42.Semantics (Regs MemImage PublicInput)
open Lv42.Parameters (minLogMem maxLogMem maxLogRows)
open Air.Flat (Component EnsembleWitness)

/-! ## Reading a committed column -/

/-- Cell `x` of a column is the stack's cell `x` past its block's offset. -/
theorem column_committed (prog : KeccakVm.Program) (s : Sizes) (q : Column (keccakIsaμ prog s)) (c : Col)
    (x : Fin (2 ^ kappa prog s c)) :
    ((keccakIsaInstance prog s).column q c).values.get x =
      q.values[x.val + (blocks prog s).offset (blockOf c)]'(by
        have := (blocks prog s).offset_add_pow_le_total (blockOf (prog := prog) (s := s) c)
        have := blocks_fits prog s
        have h1 := x.isLt
        have h2 : 2 ^ kappa prog s c = 2 ^ (blocks prog s).size (blockOf c) := by rw [size_blockOf]
        omega) := by
  have h0 : ((keccakIsaInstance prog s).column q c).values.get x =
      q.values.get (boolIndex ((layout prog s).extend c (boolVec x))) := by
    simp only [M3Instance.column, Lv42.Protocol.Layout.read, Lv42.Protocol.Layout.readWith]
    exact Vector.get_ofFn _ _
  refine h0.trans ?_
  show q.values.get (boolIndex ((blocks prog s).extendPoint (blocks_fits prog s) (blockOf c)
    (Vector.cast (size_blockOf prog s c).symm (boolVec x)))) = _
  rw [boolVec_cast]
  exact (blocks prog s).get_extendPoint (blocks_fits prog s) q (blockOf c) (Fin.cast (by rw [size_blockOf]) x)

/-! ## The stack of a witness -/

section StackOf

variable (F : KeccakFlockSpec) (prog : KeccakVm.Program) (s : Sizes)

/-- The memory block's cell of memory column `i`: the limbs at `2, 3, 4`, `MFCNT` at `1`. -/
def memRowCell : Fin 4 → ℕ := ![2, 3, 4, 1]

/-- The state an executed `SHA3` row's block carries at its input port: the row's input lanes, `END_BIT` XORed into
lane 16 (`laneOffset`); `0` on a padding row. -/
def sha3States (w : EnsembleWitness (kEnsemble prog)) : Vector KState (2 ^ s.τ 5) :=
  Vector.ofFn fun x ↦ if x.val < s.rows 5 then
    Vector.ofFn fun l : Fin 25 ↦ (cellOf (tableAt w 5) x (Sha3Table.inLane l) + laneOffset l).lane
  else Vector.replicate 25 0

/-- The column `c` a witness carries. -/
def witnessColumn (w : EnsembleWitness (kEnsemble prog)) : (c : Col) → Vector K (2 ^ kappa prog s c)
  | ⟨⟨0, _⟩, i⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w 6) x (memRowCell i)
  | ⟨⟨1, _⟩, _⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w 7) x 1
  | ⟨⟨2, _⟩, _⟩ => (F.gen (sha3States prog s w)).values
  | ⟨⟨j + 3, h⟩, i⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w ⟨j, by omega⟩) x i

/-- The stack of a witness at the sizes `s`: its columns at their blocks, zero past the last. -/
def stackOf (w : EnsembleWitness (kEnsemble prog)) : Column (keccakIsaμ prog s) :=
  (blocks prog s).stackColumn (fun b ↦ witnessColumn F prog s w (stackOrder prog s)[b]) (keccakIsaμ prog s)

variable (w : EnsembleWitness (kEnsemble prog))

private theorem stackColumn_get (t : (blocks prog s).Tables K) (b : Fin (blocks prog s).n)
    (x : Fin (2 ^ (blocks prog s).size b)) :
    ((blocks prog s).stackColumn t (keccakIsaμ prog s)).values[x.val + (blocks prog s).offset b]'(by
      have := (blocks prog s).offset_add_pow_le_total b
      have := blocks_fits prog s
      have := x.isLt
      omega) = (t b)[x] := by
  rw [← (blocks prog s).unstack_getElem (blocks_fits prog s) _ b x.isLt]
  exact congrArg (·[x]) ((blocks prog s).unstack_stackAt t (blocks_fits prog s) 0 b)

private theorem witnessColumn_congr {c c' : Col} (h : c' = c) (x : Fin (2 ^ kappa prog s c')) :
    (witnessColumn F prog s w c')[x] =
      (witnessColumn F prog s w c)[(Fin.cast (by rw [h]) x : Fin (2 ^ kappa prog s c))] := by
  subst h
  rfl

/-- A column of the stack of a witness is the witness's column. -/
theorem column_stackOf (c : Col) (x : Fin (2 ^ kappa prog s c)) :
    ((keccakIsaInstance prog s).column (stackOf F prog s w) c).values.get x = (witnessColumn F prog s w c)[x] := by
  refine (column_committed prog s _ c x).trans ?_
  have hsz := size_blockOf prog s c
  have hx : x.val < 2 ^ (blocks prog s).size (blockOf c) := by rw [hsz]; exact x.isLt
  refine (stackColumn_get prog s _ (blockOf c) ⟨x.val, hx⟩).trans ?_
  exact witnessColumn_congr F prog s w (List.getElem_idxOf _) _

end StackOf

/-! ## Rows of the two blocks -/

private theorem memRow_cells (idx cnt : K) (m : Vector K 3) :
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[1]?.getD 0 = cnt ∧
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[2]?.getD 0 = m[0] ∧
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[3]?.getD 0 = m[1] ∧
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[4]?.getD 0 = m[2] := by
  simp [explicit_provable_type, ProvableStruct.componentsToElements, ProvableStruct.toComponents,
    toComponents, circuit_norm]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Vector.getElem_append] <;> simp <;>
    rw [Vector.getElem_append] <;> simp

private theorem memRow_cell (idx cnt : K) (m : Vector K 3) (k : Fin 4) :
    (toElements (⟨idx, cnt, m⟩ : MemRow K)).toArray[memRowCell k]?.getD 0 =
      ![m[0], m[1], m[2], cnt] k := by
  obtain ⟨c1, c2, c3, c4⟩ := memRow_cells idx cnt m
  fin_cases k
  exacts [c2, c3, c4, c1]

private theorem bytecodeRow_cell (prog : KeccakVm.Program) (i : Fin (2 ^ prog.logSize)) (c : K) :
    (toElements (kBytecodeRowOf prog i c)).toArray[1]?.getD 0 = c := by
  simp [kBytecodeRowOf, explicit_provable_type, ProvableStruct.componentsToElements,
    ProvableStruct.toComponents, toComponents, circuit_norm]
  rw [Vector.getElem_append]
  simp
  rw [Vector.getElem_append]
  simp

/-! ## The sizes of a witness -/

/-- The sizes a witness carries: its memory size and its tables' row counts. -/
def witnessSizes {prog : KeccakVm.Program} (w : EnsembleWitness (kEnsemble prog)) (h : 0 < (imageOf w.data).1) :
    Sizes :=
  ⟨(imageOf w.data).1, h, fun j ↦ (opTable w j).table.length⟩

/-! ## The stack of a witness agrees with it -/

section Agree

variable {F : KeccakFlockSpec} {prog : KeccakVm.Program} {w : EnsembleWitness (kEnsemble prog)}

private theorem cellOf_eq (t : Air.Flat.Table K) {x : ℕ} (hx : x < t.table.length) (i : ℕ) :
    cellOf t x i = (t.table[x]'hx)[i]?.getD 0 := by
  rw [cellOf, List.getElem?_eq_getElem hx]
  rfl

private theorem cells_stackOf (hp : 0 < (imageOf w.data).1) (j : Fin 6)
    (x : Fin ((keccakIsaInstance prog (witnessSizes w hp)).rows (opIdx j)))
    (i : Fin ((keccakIsaInstance prog (witnessSizes w hp)).width (opIdx j))) :
    cellOf (opTable w j) x i =
      (keccakIsaInstance prog (witnessSizes w hp)).row (stackOf F prog (witnessSizes w hp) w) (opIdx j)
          (Fin.castLE ((keccakIsaInstance prog (witnessSizes w hp)).rows_le _) x) i := by
  refine Eq.symm ((column_stackOf F prog _ w ⟨opIdx j, i⟩ _).trans ?_)
  exact Vector.getElem_ofFn _

private theorem memRows_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) :
    memBlockRows w = memBlockRowsOf prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) := by
  obtain ⟨idx, cnt, hrows⟩ := h.seed_rows
  have hlen : (memBlockRows w).length = 2 ^ (imageOf w.data).1 := by
    rw [hrows, List.length_ofFn]
  have hrow : ∀ x : Fin (2 ^ (imageOf w.data).1),
      (memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt) =
        (toElements (⟨idx x, cnt x, #v[((imageOf w.data).2 x).limb 0,
          ((imageOf w.data).2 x).limb 1, ((imageOf w.data).2 x).limb 2]⟩ : MemRow K)).toArray :=
    fun x ↦ by simp only [hrows, List.getElem_ofFn]
  have hidx : ∀ x : Fin (2 ^ (imageOf w.data).1), idx x = gpow x := fun x ↦ by
    have := h.index_columns x.val (by rw [hlen]; exact x.isLt)
    rw [hrow, memRowAt_toElements] at this
    exact this
  have hcell : ∀ (k : Fin 4) (x : Fin (2 ^ (imageOf w.data).1)),
      cell prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) (memCol k) x =
        ((memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt))[memRowCell k]?.getD 0 :=
    fun k x ↦ (column_stackOf F prog (witnessSizes w hp) w (memCol k) x).trans
        ((Vector.getElem_ofFn _).trans (cellOf_eq _ _ _))
  rw [hrows, memBlockRowsOf]
  refine congrArg List.ofFn (funext fun x ↦ ?_)
  simp only [hcell, hrow x, hidx x, memRow_cell]
  rfl

private theorem bytecodeRows_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) :
    bytecodeBlockRows w =
      bytecodeBlockRowsOf prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) := by
  obtain ⟨cntFin, hrows⟩ := h.bytecode_rows
  have hlen : (bytecodeBlockRows w).length = 2 ^ prog.logSize := by
    rw [hrows, List.length_ofFn]
  have hrow : ∀ i : Fin (2 ^ prog.logSize),
      (bytecodeBlockRows w)[i.val]'(by rw [hlen]; exact i.isLt) =
        (toElements (kBytecodeRowOf prog i (cntFin i))).toArray :=
    fun i ↦ by simp only [hrows, List.getElem_ofFn]
  have hcell : ∀ i : Fin (2 ^ prog.logSize),
      cell prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) bfcntCol i =
        ((bytecodeBlockRows w)[i.val]'(by rw [hlen]; exact i.isLt))[1]?.getD 0 :=
    fun i ↦ (column_stackOf F prog (witnessSizes w hp) w bfcntCol i).trans
      ((Vector.getElem_ofFn _).trans (cellOf_eq _ _ _))
  rw [hrows, bytecodeBlockRowsOf]
  refine congrArg List.ofFn (funext fun i ↦ ?_)
  simp only [hcell, hrow i, bytecodeRow_cell]

/-- The stack of a witness satisfying the constraint statement agrees with it. -/
theorem agrees_stackOf {input : PublicInput} (h : SatisfiedBy prog input w) (hp : 0 < (imageOf w.data).1) :
    Agrees (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) w :=
  ⟨fun _ ↦ rfl, cells_stackOf hp, memRows_stackOf h hp, bytecodeRows_stackOf h hp⟩

private theorem memLimb_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) (k : Fin 3) (x : Fin (2 ^ (imageOf w.data).1)) :
    cell prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) (memCol k.castSucc) x =
      ((imageOf w.data).2 x).limb k := by
  obtain ⟨idx, cnt, hrows⟩ := h.seed_rows
  have hlen : (memBlockRows w).length = 2 ^ (imageOf w.data).1 := by
    rw [hrows, List.length_ofFn]
  refine (column_stackOf F prog (witnessSizes w hp) w (memCol k.castSucc) x).trans
      ((Vector.getElem_ofFn _).trans ((cellOf_eq _ (by rw [hlen]; exact x.isLt) _).trans ?_))
  have hrow : (memBlockRows w)[x.val]'(by rw [hlen]; exact x.isLt) =
      (toElements (⟨idx x, cnt x, #v[((imageOf w.data).2 x).limb 0,
        ((imageOf w.data).2 x).limb 1, ((imageOf w.data).2 x).limb 2]⟩ : MemRow K)).toArray := by
    simp only [hrows, List.getElem_ofFn]
  simp only [hrow, memRow_cell]
  fin_cases k <;> rfl

private theorem image_words {input : PublicInput} (h : SatisfiedBy prog input w)
    (h0 : 0 < 2 ^ (imageOf w.data).1) (h1 : 1 < 2 ^ (imageOf w.data).1) :
    (imageOf w.data).2 ⟨0, h0⟩ = input.word0 ∧ (imageOf w.data).2 ⟨1, h1⟩ = input.word1 := by
  have hκ : (imageOf w.data).1 < 64 := lt_of_le_of_lt h.caps.le_maxLogMem (by decide)
  have e0 := (Lv42.Semantics.MemImage.read_gpow hκ (imageOf w.data).2 ⟨0, h0⟩).symm.trans h.word0_eq
  have e1 := (Lv42.Semantics.MemImage.read_gpow hκ (imageOf w.data).2 ⟨1, h1⟩).symm.trans h.word1_eq
  exact ⟨Option.some.inj e0, Option.some.inj e1⟩

private theorem publicLinesHold_stackOf {input : PublicInput} (h : SatisfiedBy prog input w)
    (hp : 0 < (imageOf w.data).1) :
    (keccakIsaInstance prog (witnessSizes w hp)).PublicLinesHold input (stackOf F prog (witnessSizes w hp) w) := by
  have h0 : 0 < 2 ^ (imageOf w.data).1 := Nat.two_pow_pos _
  have h1 : 1 < 2 ^ (imageOf w.data).1 := Nat.one_lt_two_pow hp.ne'
  obtain ⟨w0, w1⟩ := image_words h h0 h1
  have hl : ∀ k : Fin 3,
      cell prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) (memCol k.castSucc)
        ⟨0, h0⟩ = input.word0.limb k ∧
      cell prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) (memCol k.castSucc)
        ⟨1, h1⟩ = input.word1.limb k := fun k ↦
    ⟨(memLimb_stackOf h hp k _).trans (congrArg (·.limb k) w0),
      (memLimb_stackOf h hp k _).trans (congrArg (·.limb k) w1)⟩
  intro l hl'
  have hls : (publicLines prog (witnessSizes w hp) input).toList =
      [⟨memCol 0, input.lanes 0, input.lanes 2, false, hp⟩,
        ⟨memCol 1, input.lanes 1, input.lanes 3, false, hp⟩, ⟨memCol 2, 0, 0, false, hp⟩] := rfl
  change l ∈ (publicLines prog (witnessSizes w hp) input).toList at hl'
  rw [hls] at hl'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl | rfl
  · exact ⟨(hl 0).1.trans (by simp [PublicInput.word0]),
      (hl 0).2.trans (by simp [PublicInput.word1])⟩
  · exact ⟨(hl 1).1.trans (by simp [PublicInput.word0]),
      (hl 1).2.trans (by simp [PublicInput.word1])⟩
  · exact ⟨(hl 2).1.trans (by simp [PublicInput.word0]),
      (hl 2).2.trans (by simp [PublicInput.word1])⟩

/-! ## Honest padding -/

/-- **The padding is honest**: past a table's rows, the stack of a witness holds zeros, the public padding row. -/
theorem paddingHonest_stackOf (hp : 0 < (imageOf w.data).1) :
    (keccakIsaInstance prog (witnessSizes w hp)).PaddingHonest (stackOf F prog (witnessSizes w hp) w) := by
  rintro ⟨j, hj⟩ x hx
  funext i
  have h9 : j < 9 := hj
  match j, hj, h9, x, hx, i with
  | 0, _, _, x, hx, _ => exact absurd (lt_of_lt_of_le x.isLt hx) (lt_irrefl _)
  | 1, _, _, x, hx, _ => exact absurd (lt_of_lt_of_le x.isLt hx) (lt_irrefl _)
  | 2, _, _, x, hx, _ => exact absurd (lt_of_lt_of_le x.isLt hx) (lt_irrefl _)
  | j + 3, hj, h9, x, hx, i =>
    have hrows : (opTable w ⟨j, by omega⟩).table.length ≤ x.val := hx
    refine (column_stackOf F prog (witnessSizes w hp) w ⟨⟨j + 3, hj⟩, i⟩ x).trans ?_
    refine (Vector.getElem_ofFn _).trans ?_
    simp [cellOf, List.getElem?_eq_none hrows]

/-! ## The constraints at the zero row -/

/-- The constraint polynomials of the opcode tables but `JUMP` are none. -/
theorem opcode_constraints_nil : ∀ j : Fin 6, j ≠ 4 → (kOpTable j).constraints.length = 0 := by
  decide +kernel

private def jumpZeroRow : JumpRow K := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private theorem jumpRaw_zero : jumpRaw jumpZeroRow 0 0 = Array.replicate 14 0 := by
  simp [jumpRaw, rawRow, jumpZeroRow, explicit_provable_type,
    ProvableStruct.componentsToElements, ProvableStruct.toComponents, toComponents, circuit_norm]
  rfl

private theorem width_jump : (kOpComponent 4).width = 14 := by decide +kernel

/-- `JUMP`'s constraint polynomials vanish at the zero row. -/
theorem jump_constraints_zero : ∀ C ∈ (kOpTable 4).constraints, C.eval (fun _ ↦ (0 : K)) = 0 := by
  have hl : (kOpComponent 4).rowOperations.lookups = [] := by decide +kernel
  refine (toM3_constraints_iff (kOpComponent 4) channelSep channelDir counted hl (fun _ ↦ 0)
    (fun _ _ ↦ #[])).mpr ?_
  have he : (Array.ofFn fun _ : Fin (kOpComponent 4).width ↦ (0 : K)) = jumpRaw jumpZeroRow 0 0 := by
    rw [jumpRaw_zero]
    exact Array.ext (by simp [width_jump]) (fun i _ _ ↦ by simp)
  rw [he]
  exact jumpRaw_constraints jumpZeroRow 0 0 (by simp [jumpZeroRow]) (by simp [jumpZeroRow]) _

/-- Every opcode table's constraints vanish at the zero row. -/
theorem zero_constraints (j : Fin 6) : ∀ C ∈ (kOpTable j).constraints, C.eval (fun _ ↦ (0 : K)) = 0 := by
  by_cases h4 : j = 4
  · subst h4
    exact jump_constraints_zero
  · intro C hC
    exact absurd (List.length_pos_of_mem hC) (by rw [opcode_constraints_nil j h4]; omega)

/-! ## The relation of the stack -/

/-- **`M3Honest` of the stack of a witness.** -/
theorem m3Honest_stackOf {input : PublicInput} (h : SatisfiedBy prog input w) (hp : 0 < (imageOf w.data).1) :
    M3Honest (keccakIsaInstance prog (witnessSizes w hp)) input (stackOf F prog (witnessSizes w hp) w) := by
  have hA := agrees_stackOf (F := F) h hp
  have hP := paddingHonest_stackOf (F := F) (w := w) hp
  refine ⟨⟨?_, (balanced_iff_pairs hA).mpr fun k ↦ ?_, (countsNonzero_iff hA).mp h.counts_nonzero,
    publicLinesHold_stackOf h hp, ?_⟩, hP⟩
  · intro j' C hC x
    rcases j' with ⟨_ | _ | _ | j, hj⟩
    · exact absurd hC List.not_mem_nil
    · exact absurd hC List.not_mem_nil
    · exact absurd hC List.not_mem_nil
    · have h9 : (keccakIsaInstance prog (witnessSizes w hp)).ntab = 9 := rfl
      by_cases hx : x.val < (witnessSizes w hp).rows ⟨j, by omega⟩
      · have hmem : opTable w ⟨j, by omega⟩ ∈ w.allTables :=
          EnsembleWitness.mem_allTables_of_mem_tables _ (mem_tables_iff.mpr ⟨⟨j, by omega⟩, rfl⟩)
        have hc := (opcode_constraints_iff hA ⟨j, by omega⟩).mp (h.constraints _ hmem) ⟨x.val, hx⟩
        exact (inst_constraints_iff prog (witnessSizes w hp) ⟨j, by omega⟩ _).mpr hc C hC
      · have hz : (keccakIsaInstance prog (witnessSizes w hp)).padRow ⟨j + 3, hj⟩ = fun _ ↦ 0 := rfl
        rw [hP ⟨j + 3, hj⟩ x (Nat.not_lt.mp hx), hz]
        have h0 := (inst_constraints_iff prog (witnessSizes w hp) ⟨j, by omega⟩ (fun _ ↦ 0)).mpr
          (zero_constraints ⟨j, by omega⟩)
        exact h0 C hC
  · fin_cases k
    exacts [h.state_balanced, h.mem_balanced, h.bytecode_balanced]
  · intro r hr
    exact absurd hr (by simp)

end Agree

/-! ## The Keccak-f region of the stack -/

section Aux

variable {F : KeccakFlockSpec} {prog : KeccakVm.Program} {w : EnsembleWitness (kEnsemble prog)}

/-- The Flock column of the stack of a witness is the honest column of its `SHA3` rows' states. -/
theorem flockColumn_stackOf (s : Sizes) :
    flockColumn prog s (stackOf F prog s w) = F.gen (sha3States prog s w) := by
  suffices hv : (flockColumn prog s (stackOf F prog s w)).values = (F.gen (sha3States prog s w)).values by
    revert hv
    generalize F.gen (sha3States prog s w) = c
    intro hv
    cases c
    exact congrArg Column.mk hv
  refine Vector.ext fun y hy ↦ ?_
  exact column_stackOf F prog s w flockCol ⟨y, hy⟩

/-- A lane word with `END_BIT` XORed into lane 16 twice is itself (characteristic two). -/
private theorem laneOffset_add_self (l : Fin 25) (a : K) : a + laneOffset l + laneOffset l = a := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The input state of an executed row is the argument of its `sha3Step`. -/
private theorem inState_eq (f : ℕ → K) :
    (Vector.ofFn fun l : Fin 25 ↦ (f (Sha3Table.inLane l) + laneOffset l).lane) =
      (laneState (Vector.ofFn fun l : Fin 25 ↦ f (Sha3Table.inLane l))).setIfInBounds endLane
        (LeanVM.Semantics.Keccak.lane (laneState (Vector.ofFn fun l : Fin 25 ↦ f (Sha3Table.inLane l))) endLane
          ^^^ endBit) := by
  apply Vector.ext
  intro l hl
  rw [Vector.getElem_setIfInBounds]
  simp only [Vector.getElem_ofFn]
  unfold endLane
  split_ifs with h16
  · subst h16
    rw [lane_eq_getElem _ _ (by decide), laneState_getElem _ _ (by decide), laneOffset_endLane, lane_add]
    simp [K.lane, K.ofLane]
  · rw [laneState_getElem _ _ hl, laneOffset_ne _ (fun h ↦ h16 h.symm), add_zero]
    simp

/-- A raw row of at least 86 cells, read as the `SHA3` component reads it, is `rowOfCells` of its first 86 cells. -/
theorem valueFromOffset_eq_ofFn (row : Array K) (d : ProverData K) :
    valueFromOffset Sha3Row 0 (Environment.fromArray row d) = rowOfCells fun i : Fin 86 ↦ row[i.val]?.getD 0 := by
  refine Eq.trans ?_ (valueFromOffset_ofFn (fun i : Fin 86 ↦ row[i.val]?.getD 0) d)
  simp only [valueFromOffset]
  refine congrArg _ (Vector.ext fun i hi ↦ ?_)
  rw [Vector.getElem_mapRange, Vector.getElem_mapRange]
  have hi' : i < 86 := hi
  show (row[0 + i]?).getD 0 = ((Array.ofFn fun j : Fin 86 ↦ row[j.val]?.getD 0)[0 + i]?).getD 0
  rw [Nat.zero_add, Array.getElem?_ofFn, dite_eq_left hi', Option.getD_some]

/-- **`KeccakAux` of the stack of a witness satisfying the constraint statement.** -/
theorem keccakAux_stackOf {input : PublicInput} (h : SatisfiedBy prog input w) (hp : 0 < (imageOf w.data).1) :
    KeccakAux F prog (witnessSizes w hp) (stackOf F prog (witnessSizes w hp) w) := by
  set s := witnessSizes w hp with hs
  have hfl := flockColumn_stackOf (F := F) (w := w) s
  refine ⟨by rw [hfl]; exact F.holds_gen _, fun t ht l ↦ ?_⟩
  have hlen : t.val < (tableAt w 5).table.length := ht
  have hcell : ∀ (i : ℕ) (hi : i < Sha3Table.width), sha3Cell prog s (stackOf F prog s w) i hi t =
      cellOf (tableAt w 5) t i := fun i hi ↦
    (column_stackOf F prog s w (sha3Col i hi) t).trans (Vector.getElem_ofFn _)
  have hst : (sha3States prog s w)[t] =
      Vector.ofFn fun l : Fin 25 ↦ (cellOf (tableAt w 5) t (Sha3Table.inLane l) + laneOffset l).lane := by
    simp only [sha3States, Fin.getElem_fin, Vector.getElem_ofFn, ht, ↓reduceIte]
  have hin := F.in_gen (sha3States prog s w) t
  have hout := F.step_of_holds _ (F.holds_gen (sha3States prog s w)) t
  rw [hin, hst] at hout
  rw [hfl, hcell, hcell]
  refine ⟨?_, ?_⟩
  · -- the input copy
    have hl := congrArg (·[l]) hin
    simp only [kBlockState, Fin.getElem_fin, Vector.getElem_ofFn, hst] at hl
    have hk : kBlockCell (F.gen (sha3States prog s w)) t (F.inSlot l) =
        cellOf (tableAt w 5) t (Sha3Table.inLane l) + laneOffset l := by
      rw [← ofLane_lane (kBlockCell _ t _), hl, ofLane_lane]
    rw [hk, laneOffset_add_self]
  · -- the output copy, by the Keccak relation of the row
    have hv := h.sha3_valid _ (List.getElem_mem hlen)
    rw [sha3RowAt, valueFromOffset_eq_ofFn] at hv
    have hg : (fun i : Fin 86 ↦ ((tableAt w 5).table[t.val]'hlen)[i.val]?.getD 0) =
        fun i : Fin 86 ↦ cellOf (tableAt w 5) t i := funext fun i ↦ (cellOf_eq _ hlen _).symm
    rw [hg] at hv
    have e : kBlockState (F.gen (sha3States prog s w)) t F.outSlot =
        laneState (rowOfCells fun i : Fin 86 ↦ cellOf (tableAt w 5) t i).outLane := by
      rw [hout, inState_eq, hv]
      rfl
    have hl := congrArg (·[l]) e
    simp only [kBlockState, Fin.getElem_fin, Vector.getElem_ofFn, laneState_getElem _ _ l.isLt] at hl
    have hk : kBlockCell (F.gen (sha3States prog s w)) t (F.outSlot l) =
        cellOf (tableAt w 5) t (Sha3Table.outLane l) := by
      rw [← ofLane_lane (kBlockCell _ t _), hl, ofLane_lane]
      simp [rowOfCells, Sha3Table.outLane]
    exact hk.symm

end Aux

/-! ## The end theorems -/

/-- **The stack of a witness satisfying the Keccak VM's constraint statement satisfies `KvHonest`**, at the sizes the
witness carries. -/
theorem kvHonest_stackOf (F : KeccakFlockSpec) {prog : KeccakVm.Program} {input : PublicInput}
    {w : EnsembleWitness (kEnsemble prog)} (h : SatisfiedBy prog input w) (hp : 0 < (imageOf w.data).1) :
    KvHonest F prog (witnessSizes w hp) input (stackOf F prog (witnessSizes w hp) w) :=
  ⟨m3Honest_stackOf h hp, keccakAux_stackOf h hp⟩

/-- **Completeness of the Keccak VM's relation.** A valid execution `t` of `prog` on `input` that executes at most
`2^32` instructions of every opcode has a stack satisfying `KvHonest F prog s input q`, at the sizes `s` it carries:
the memory log-size is the execution's and opcode table `j` has the execution's number of instructions of its opcode
(`tableOpcode j`). -/
theorem kvCompleteness (F : KeccakFlockSpec) {prog : KeccakVm.Program} {input : PublicInput}
    {t : KeccakVm.Trace prog} (h : KeccakVm.ValidExecution prog input t)
    (hcount : ∀ op, t.count op ≤ 2 ^ maxLogRows) :
    ∃ (s : Sizes) (q : Column (keccakIsaμ prog s)), KvHonest F prog s input q ∧ s.logMem = t.κ ∧
      ∀ j : Fin 6, s.rows j = t.count (tableOpcode j) := by
  have hc : ∀ op, t.count op = runRows t op := count_eq_runRows h.2
  obtain ⟨w, hw, hrep, hlen⟩ := constraintCompleteness_rows h fun op ↦ hc op ▸ hcount op
  have hp : 0 < (imageOf w.data).1 := lt_of_lt_of_le (by decide) hw.caps.minLogMem_le
  refine ⟨witnessSizes w hp, stackOf F prog (witnessSizes w hp) w, kvHonest_stackOf F hw hp, hrep.κ_eq,
    fun j ↦ ?_⟩
  rw [hc]
  exact hlen j

end KeccakArith

end
