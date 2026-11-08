-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The witness read off a stack follows `formal/Lv42`'s
-- `Protocol/LeanIsa.lean` (`witnessOf`, leanerVM `mumbai` f0393df4, MIT OR Apache-2.0), for the Keccak VM's
-- instance, all of whose columns are committed.
module

public import KeccakArith.SStateWalk

/-!
# The witness read off a Keccak VM stack

`witnessOf prog s q`: the Keccak VM ensemble's witness a stack `q` of `keccakIsaInstance prog s` carries (Lv42's
`witnessOf`): the six opcode tables' executed rows, the memory and bytecode blocks from the memory columns, the
program and `BFCNT`, the image from the memory columns, the public input from the first two cells of `MEM_LO` and
`MEM_HI`.

The instance's opcode table `j` is `kOpComponent j` read as an M3 table (`kOpTable j`): its flushes, constraints and
count columns are the component's (`inst_flushes_eval`, `inst_constraints_iff`, `mem_inst_counts`), from Lv42's five
tables and `sha3M3_flushes`, `sha3M3_constraints`, `sha3M3_count`.
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Arithmetization KeccakVm KeccakVm.KeccakIsa
open LeanVM.Protocol (Column M3Table)
open Lv42.Protocol (M3Instance Side)
open Lv42.Protocol.LeanIsa (Sizes sideOf counted)
open Lv42.Semantics (Regs MemImage PublicInput)
open Lv42.Parameters (minLogMem maxLogMem maxLogRows)
open Air.Flat (Component EnsembleWitness)

/-! ## The opcode tables -/

/-- The six opcode tables of the Keccak VM, in the ensemble's order. -/
def kOpComponent : Fin 6 → Component K
  | 0 => ⟨xorTable⟩
  | 1 => ⟨mulTable⟩
  | 2 => ⟨setTable⟩
  | 3 => ⟨derefTable⟩
  | 4 => ⟨jumpTable⟩
  | 5 => ⟨sha3Table⟩

/-- Opcode table `j` as an M3 table. -/
def kOpTable (j : Fin 6) : M3Table K Lv42.Arithmetization.Direction :=
  (kOpComponent j).toM3 channelSep channelDir counted

/-- The index of opcode table `j` among the instance's tables. -/
def opIdx (j : Fin 6) : Fin 9 := ⟨j + 3, by omega⟩

/-- The instance's width of opcode table `j` is its component's. -/
theorem kw (prog : KeccakVm.Program) (s : Sizes) (j : Fin 6) :
    (keccakIsaInstance prog s).width (opIdx j) = (kOpComponent j).width := by
  fin_cases j <;> rfl

/-- The instance's log-height of opcode table `j` is the announced one. -/
theorem kτ (prog : KeccakVm.Program) (s : Sizes) (j : Fin 6) :
    (keccakIsaInstance prog s).τ (opIdx j) = s.τ j := by
  fin_cases j <;> rfl

/-- The instance's row count of opcode table `j` is the announced one. -/
theorem krows (prog : KeccakVm.Program) (s : Sizes) (j : Fin 6) :
    (keccakIsaInstance prog s).rows (opIdx j) = s.rows j := by
  fin_cases j <;> rfl

/-- A row of the instance's table `opIdx j`, read with its component's width. -/
def kRow {prog : KeccakVm.Program} {s : Sizes} {j : Fin 6}
    (r : Fin ((keccakIsaInstance prog s).width (opIdx j)) → K) : Fin (kOpComponent j).width → K :=
  fun i ↦ r (Fin.cast (kw prog s j).symm i)

/-- Filtering the sides of a mapped flush list. -/
theorem filter_sideOf_map {n : ℕ} (L : List (Lv42.Arithmetization.Direction × Vector (CPoly.CMvPolynomial n K) 16))
    (side : Side) (r : Fin n → K) :
    (((L.map fun f ↦ (sideOf f.1, f.2)).filter fun f ↦ decide (f.1 = side)).map fun f ↦ f.2.map (·.eval r)) =
      ((L.filter fun f ↦ decide (sideOf f.1 = side)).map fun f ↦ f.2.map (·.eval r)) := by
  rw [List.filter_map, List.map_map]
  rfl

/-- **The instance's flushes of opcode table `j`** on a row are its component's on that row. -/
theorem inst_flushes_eval (prog : KeccakVm.Program) (s : Sizes) (j : Fin 6) (side : Side)
    (r : Fin ((keccakIsaInstance prog s).width (opIdx j)) → K) :
    (((keccakIsaInstance prog s).flushes (opIdx j)).filter fun f ↦ decide (f.1 = side)).map
        (fun f ↦ f.2.map (·.eval r)) =
      ((kOpTable j).flushes.filter fun f ↦ decide (sideOf f.1 = side)).map
        fun f ↦ f.2.map (·.eval (kRow r)) := by
  fin_cases j
  · exact filter_sideOf_map _ side r
  · exact filter_sideOf_map _ side r
  · exact filter_sideOf_map _ side r
  · exact filter_sideOf_map _ side r
  · exact filter_sideOf_map _ side r
  · show ((Sha3Table.flushes.filter fun f ↦ decide (f.1 = side)).map fun f ↦ f.2.map (·.eval r)) = _
    rw [← sha3M3_flushes]
    exact filter_sideOf_map _ side r

/-- **The instance's constraints of opcode table `j`** vanish on a row exactly when its component's do. -/
theorem inst_constraints_iff (prog : KeccakVm.Program) (s : Sizes) (j : Fin 6)
    (r : Fin ((keccakIsaInstance prog s).width (opIdx j)) → K) :
    (∀ C ∈ (keccakIsaInstance prog s).constraints (opIdx j), C.eval r = 0) ↔
      ∀ C ∈ (kOpTable j).constraints, C.eval (kRow r) = 0 := by
  fin_cases j
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · show (∀ C ∈ ([] : List (CPoly.CMvPolynomial Sha3Table.width K)), C.eval r = 0) ↔ _
    show _ ↔ ∀ C ∈ sha3M3.constraints, C.eval (kRow r) = 0
    rw [sha3M3_constraints]
    simp

/-- **The instance's count columns of opcode table `j`** are its component's. -/
theorem mem_inst_counts (prog : KeccakVm.Program) (s : Sizes) (j : Fin 6)
    (k : Fin ((keccakIsaInstance prog s).width (opIdx j))) :
    k ∈ (keccakIsaInstance prog s).counts (opIdx j) ↔ Fin.cast (kw prog s j) k ∈ (kOpTable j).count := by
  fin_cases j
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · show k ∈ Sha3Table.counts ↔ _
    show _ ↔ _ ∈ sha3M3.count
    rw [sha3M3_count]
    exact Iff.rfl

/-- The announced sizes are admissible: the memory window, the row cap, the stacked size's cap. -/
def Admissible (prog : KeccakVm.Program) (s : Sizes) : Prop :=
  minLogMem ≤ s.logMem ∧ s.logMem ≤ maxLogMem ∧ (∀ j, s.rows j ≤ 2 ^ maxLogRows) ∧
    keccakIsaμ prog s ≤ Lv42.Protocol.LeanIsa.maxMu

/-! ## The witness read off a stack -/

section WitnessOf

variable (prog : KeccakVm.Program) (s : Sizes) (q : Column (keccakIsaμ prog s))

/-- Cell `x` of column `c`, read off the stack. -/
abbrev cell (c : Col) (x : Fin (2 ^ kappa prog s c)) : K :=
  ((keccakIsaInstance prog s).column q c).values.get x

/-- The executed rows of opcode table `j`, read off the stack. -/
def opcodeRows (j : Fin 6) : List (Array K) :=
  List.ofFn fun x : Fin ((keccakIsaInstance prog s).rows (opIdx j)) ↦
    Array.ofFn ((keccakIsaInstance prog s).row q (opIdx j)
      (Fin.castLE ((keccakIsaInstance prog s).rows_le (opIdx j)) x))

/-- The memory block's rows: the index `g^x`, the finalize count `MFCNT`, the three limbs. -/
def memBlockRowsOf : List (Array K) :=
  List.ofFn fun x : Fin (2 ^ s.logMem) ↦ (toElements (⟨gpow x, cell prog s q (memCol 3) x,
    #v[cell prog s q (memCol 0) x, cell prog s q (memCol 1) x,
      cell prog s q (memCol 2) x]⟩ : MemRow K)).toArray

/-- The bytecode block's rows: the program's, with the finalize counts `BFCNT`. -/
def bytecodeBlockRowsOf : List (Array K) :=
  List.ofFn fun i : Fin (2 ^ prog.logSize) ↦
    (toElements (kBytecodeRowOf prog i (cell prog s q bfcntCol i))).toArray

/-- The memory image: the three limb columns, word by word. -/
def imageRows : Array (Vector K 3) :=
  Array.ofFn fun x : Fin (2 ^ s.logMem) ↦
    #v[cell prog s q (memCol 0) x, cell prog s q (memCol 1) x, cell prog s q (memCol 2) x]

/-- Prover data whose one table is the memory image, `"mem"`. -/
def dataOf (mem : Array (Vector K 3)) : ProverData K := fun name n ↦
  if h : name = memDataName ∧ n = 3 then h.2 ▸ mem else #[]

/-- Cell `0` of a memory column. -/
def cell0 (i : Fin 4) : K := cell prog s q (memCol i) ⟨0, Nat.two_pow_pos _⟩

/-- Cell `1` of a memory column. -/
def cell1 (i : Fin 4) : K := cell prog s q (memCol i) ⟨1, Nat.one_lt_two_pow s.logMem_pos.ne'⟩

/-- The public input: cells `0` and `1` of `MEM_LO` and `MEM_HI`. -/
def publicInputOf : PublicIO K :=
  ⟨#v[cell0 prog s q 0, cell0 prog s q 1, cell1 prog s q 0, cell1 prog s q 1]⟩

/-- The memory block has five columns. -/
theorem width_memTable : (⟨memTable⟩ : Component K).width = 5 := by decide +kernel

/-- The bytecode block has ten columns. -/
theorem width_bytecodeTable : (⟨bytecodeTable⟩ : Component K).width = 10 := by decide +kernel

/-- A table of the witness: a component, its rows of its width, the data. -/
def tableOf (c : Component K) (rows : List (Array K)) (data : ProverData K)
    (h : ∀ r ∈ rows, r.size = c.width) : Air.Flat.Table K :=
  ⟨c, c.width, rows, data, h⟩

/-- **The witness a stack carries.** -/
def witnessOf : EnsembleWitness (kEnsemble prog) :=
  let data := dataOf (imageRows prog s q)
  let op (j : Fin 6) : Air.Flat.Table K :=
    tableOf (kOpComponent j) (opcodeRows prog s q j) data (by
      simp only [opcodeRows, List.mem_ofFn, forall_exists_index]
      rintro _ x rfl
      rw [Array.size_ofFn]
      exact kw prog s j)
  { tables := [op 0, op 1, op 2, op 3, op 4, op 5,
      tableOf ⟨memTable⟩ (memBlockRowsOf prog s q) data (by
        simp only [memBlockRowsOf, List.mem_ofFn, forall_exists_index]
        rintro _ x rfl
        rw [Vector.size_toArray, width_memTable]
        rfl),
      tableOf ⟨bytecodeTable⟩ (bytecodeBlockRowsOf prog s q) data (by
        simp only [bytecodeBlockRowsOf, List.mem_ofFn, forall_exists_index]
        rintro _ x rfl
        rw [Vector.size_toArray, width_bytecodeTable]
        rfl)]
    data := data
    publicInput := publicInputOf prog s q
    same_length := rfl
    same_circuits := fun i hi ↦ by
      change i < 8 at hi
      interval_cases i <;> rfl
    same_data := by simp [tableOf, op] }

end WitnessOf

end KeccakArith

end
