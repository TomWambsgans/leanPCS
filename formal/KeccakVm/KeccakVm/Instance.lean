-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The instance follows `formal/Lv42`'s
-- `Protocol/LeanIsa.lean` (leanerVM `mumbai` f0393df4, MIT OR Apache-2.0): its five opcode tables, its column groups,
-- its boundary blocks, public lines and stacking are reused or repeated; the `SHA3` table's flushes are
-- `crates/leanvm_flock_gas/src/layout.rs::flushes_sha3` (leanVM `9d50c92a3`'s `Sha3Table`).
module

public import KeccakVm.Isa
public import Lv42.Protocol.LeanIsaBase
public import Lv42.Protocol.Stack
public import Lv42.Protocol.FixedColumns

/-!
# The Keccak VM's relation

The relation the Keccak VM's univariate verifier proves knowledge of, in the form of leanVM 42422001's
(`Lv42.Protocol.M3Holds` of `leanIsaInstance`), with the Keccak-f block in place of BLAKE2s's.

**The instance** `keccakIsaInstance prog s`: nine tables, as Lv42's,
* the four memory columns `MEM_LO, MEM_HI, MEM_TOP, MFCNT`, the bytecode count `BFCNT`, and the Flock column
  `QFLOCK` of `2^(11 + τ_SHA3)` cells (`2^11` words a permutation, `keccakR1csLogSize = 17`);
* Lv42's five opcode tables (`XOR`, `MUL`, `SET`, `DEREF`, `JUMP`: `Lv42.Protocol.LeanIsa.baseTable`, Clean's
  polynomials), and the `SHA3` table (`Sha3Table`): 86 columns (`sha3Columns`), no constraint, its flushes the
  state step, the bytecode read of `(g^5, o_m₀, …, o_m₃, o_tail, o_cap, o_out)` and the 26 cell reads, each a
  memory pull `(g, addr, cnt, v₀, v₁, v₂)` and push `(g, addr, g · cnt, v₀, v₁, v₂)` (Lv42's `memRead`), the
  values the cell's lanes in `sha3CellLanes`' order and zero tops, the lone lane-16 cell's high limb zero. The
  27 `cnt` columns are the count columns.
* Every column is committed, the 50 lane columns included: unlike Lv42's `BLAKE2S` limbs they are not read off the
  Flock column, because `in_16` is its port word plus `END_BIT` (`KECCAK.md`, "leanVM's opcode exactly"), which a
  linear reading cannot express. They are tied to the Flock column by `KeccakAux`'s copy clause instead, as the
  univariate verifier's `Q_W` ties its copies.
* The boundary blocks, the public lines and the stacking are Lv42's, with the Keccak VM's bytecode entries
  (`KeccakVm.entry`). The padding rows are zero (`tables_keccak`: "A padding row is zero"; Lv42's five tables'
  padding rows are zero too). The instance has no `FlockRegion` (Lv42's is sized for BLAKE2s's `2^14`-bit blocks):
  the Keccak-f region is `KeccakAux`'s.

**The Keccak-f block** is a parameter, `KeccakFlockSpec` (as Lv42's instance takes a `FlockSpec`): an R1CS on blocks
of `2^17` bits, its constant position, the input and output port words of each lane, and the two directions
between the region predicate and Keccak-f (`step_of_holds`: every block of a column satisfying the predicate holds
Keccak-f[1600] of its input port at its output port; `gen`, `holds_gen`, `in_gen`: the honest column). Its
inhabitant is the Keccak-f block of `crates/lv42_flock/src/keccak.rs`, `formal/KeccakFlock`'s `keccakFlockSpec`.

**The relation** `KvHolds F prog s input q`: `M3Holds` of the instance (constraints, bus balance, counts nonzero,
public lines) and `KeccakAux F` (every block of `QFLOCK` satisfies the block R1CS with `1` at its constant
position, and on every executed `SHA3` row `t`, output lane `l` is block `t`'s output port word `l` and input lane
`l` its input port word `l`, plus `END_BIT` for `l = 16`). `KvHonest` is the same with `M3Honest`.
-/

@[expose] public section

namespace KeccakVm

open LeanVM.Parameters LeanVM.Protocol LeanVM.Semantics Lv42.Protocol Lv42.Arithmetization CompPoly CPoly
open CMlPolynomialEval
open Lv42.Parameters (Flock.kSkip)
open Lv42.Protocol.LeanIsa (Sizes baseComponent baseTable sideOf minMu maxMu)

/-! ## The `SHA3` table -/

namespace Sha3Table

/-- The `SHA3` table's width, `SHA3_COLUMNS.len()`. -/
def width : ℕ := 86

/-- The columns, in `SHA3_COLUMNS`' order: `pc, fp`, the operands, the lanes, the counts. -/
def pc : ℕ := 0
def fp : ℕ := 1
def om (i : ℕ) : ℕ := 2 + i
def otail : ℕ := 6
def ocap : ℕ := 7
def oout : ℕ := 8
def inLane (l : ℕ) : ℕ := 9 + l
def outLane (l : ℕ) : ℕ := 34 + l
def cnt (c : ℕ) : ℕ := 59 + c
def cntBc : ℕ := 85

/-- A column as an expression. -/
def x (i : ℕ) : Expression K := .var ⟨i⟩

/-- A constant as an expression. -/
def k (c : K) : Expression K := .const c

/-- The address of input cell `c`: `fp · o_m_c` (`c < 4`), `g^(c−4) · fp · o_tail` (`c < 8`),
`g^(c−8) · fp · o_cap`. -/
def inAddr (c : ℕ) : Expression K :=
  if c < 4 then x fp * x (om c)
  else if c < 8 then k (g ^ (c - 4)) * (x fp * x otail)
  else k (g ^ (c - 8)) * (x fp * x ocap)

/-- The address of output cell `c`: `g^c · fp · o_out`. -/
def outAddr (c : ℕ) : Expression K := k (g ^ c) * (x fp * x oout)

/-- The three limbs of state cell `c` read off the lane columns `lane`: its two lanes (`sha3CellLanes`), a missing
high lane zero, the top zero. -/
def cellVals (lane : ℕ → ℕ) (c : ℕ) : List (Expression K) :=
  [x (lane (sha3CellLanes c).1),
    match (sha3CellLanes c).2 with
    | some h => x (lane h)
    | none => k 0,
    k 0]

/-- A memory read (Lv42's `memRead`): pull `(g, addr, cnt, v)`, push `(g, addr, g · cnt, v)`. -/
def memRead (addr : Expression K) (count : ℕ) (vals : List (Expression K)) : List (Side × List (Expression K)) :=
  [(.pull, [k (gpow 1), addr, x count] ++ vals), (.push, [k (gpow 1), addr, k g * x count] ++ vals)]

/-- The seven operands, in the bytecode flush's order. -/
def operands : List (Expression K) := [x (om 0), x (om 1), x (om 2), x (om 3), x otail, x ocap, x oout]

/-- **The flushes** of a `SHA3` row (`flushes_sha3`): the state step `(pc, fp) → (g · pc, fp)`, the bytecode read,
the thirteen input cells (counts `cnt_0 … cnt_12`) and the thirteen output cells (`cnt_13 … cnt_25`). -/
def flushExprs : List (Side × List (Expression K)) :=
  [(.pull, [k (gpow 0), x pc, x fp]), (.push, [k (gpow 0), k g * x pc, x fp]),
    (.pull, [k (gpow 2), x pc, x cntBc, k Opcode.sha3.code] ++ operands),
    (.push, [k (gpow 2), x pc, k g * x cntBc, k Opcode.sha3.code] ++ operands)] ++
  (List.range 13).flatMap (fun c ↦ memRead (inAddr c) (cnt c) (cellVals inLane c)) ++
  (List.range 13).flatMap (fun c ↦ memRead (outAddr c) (cnt (13 + c)) (cellVals outLane c))

/-- A flush's sixteen coordinates as polynomials in the row's 86 columns, zeros past its end. -/
def tuple (l : List (Expression K)) : Vector (CMvPolynomial width K) 16 :=
  Vector.ofFn fun j ↦ (l.getD j (k 0)).toCMvPolynomial width

/-- The flushes as polynomials. -/
def flushes : List (Side × Vector (CMvPolynomial width K) 16) := flushExprs.map fun f ↦ (f.1, tuple f.2)

/-- Every coordinate of every flush has degree at most two. -/
theorem flushExprs_degreeBound : ∀ f ∈ flushExprs, ∀ e ∈ f.2, e.degreeBound ≤ 2 := by
  decide +kernel

/-- Every flush coordinate has total degree at most two. -/
theorem flushes_degree : ∀ f ∈ flushes, ∀ j, (f.2.get j).totalDegree ≤ 2 := by
  intro f hf j
  obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
  simp only [tuple, Vector.get_ofFn]
  refine (Expression.totalDegree_toCMvPolynomial_le _ _).trans ?_
  by_cases hj : j.val < f'.2.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact flushExprs_degreeBound f' hf' _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

/-- The count columns: `cnt_0 … cnt_25`, `cnt_bc`. -/
def counts : List (Fin width) := (List.finRange 27).map fun c ↦ ⟨cnt c.val, by unfold cnt width; omega⟩

end Sha3Table

/-! ## The instance -/

namespace KeccakIsa

/-- The widths: the four memory columns, `BFCNT`, `QFLOCK`, Lv42's five opcode tables, `SHA3`. -/
def width : Fin 9 → ℕ
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => (baseComponent 0).width
  | ⟨4, _⟩ => (baseComponent 1).width
  | ⟨5, _⟩ => (baseComponent 2).width
  | ⟨6, _⟩ => (baseComponent 3).width
  | ⟨7, _⟩ => (baseComponent 4).width
  | ⟨8, _⟩ => Sha3Table.width

variable (prog : Program) (s : Sizes)

/-- The log-heights: the memory's, the program's, the Flock column's `11 + τ_SHA3`, then the announced ones. -/
def height : Fin 9 → ℕ
  | ⟨0, _⟩ => s.logMem
  | ⟨1, _⟩ => prog.logSize
  | ⟨2, _⟩ => 11 + s.τ 5
  | ⟨j + 3, h⟩ => s.τ ⟨j, by omega⟩

/-- The tables of the instance. -/
def shape : Shape := ⟨9, height prog s, width⟩

/-- The row counts: every row of the column groups, then the announced ones. -/
def rows : Fin 9 → ℕ
  | ⟨0, _⟩ => 2 ^ s.logMem
  | ⟨1, _⟩ => 2 ^ prog.logSize
  | ⟨2, _⟩ => 2 ^ (11 + s.τ 5)
  | ⟨j + 3, h⟩ => s.rows ⟨j, by omega⟩

theorem rows_le : ∀ j, rows prog s j ≤ 2 ^ height prog s j
  | ⟨0, _⟩ => le_rfl
  | ⟨1, _⟩ => le_rfl
  | ⟨2, _⟩ => le_rfl
  | ⟨j + 3, h⟩ => s.rows_le ⟨j, by omega⟩

/-- The constraint polynomials: Lv42's opcode tables' (`JUMP`'s two); `SHA3` has none. -/
def constraints : (j : Fin 9) → List (CMvPolynomial (width j) K)
  | ⟨3, _⟩ => (baseTable 0).constraints
  | ⟨4, _⟩ => (baseTable 1).constraints
  | ⟨5, _⟩ => (baseTable 2).constraints
  | ⟨6, _⟩ => (baseTable 3).constraints
  | ⟨7, _⟩ => (baseTable 4).constraints
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => []
  | ⟨2, _⟩ => []
  | ⟨8, _⟩ => []

/-- The flushes: Lv42's opcode tables', each on its channel's side, and `SHA3`'s. -/
def flushes : (j : Fin 9) → List (Side × Vector (CMvPolynomial (width j) K) 16)
  | ⟨3, _⟩ => (baseTable 0).flushes.map fun f ↦ (sideOf f.1, f.2)
  | ⟨4, _⟩ => (baseTable 1).flushes.map fun f ↦ (sideOf f.1, f.2)
  | ⟨5, _⟩ => (baseTable 2).flushes.map fun f ↦ (sideOf f.1, f.2)
  | ⟨6, _⟩ => (baseTable 3).flushes.map fun f ↦ (sideOf f.1, f.2)
  | ⟨7, _⟩ => (baseTable 4).flushes.map fun f ↦ (sideOf f.1, f.2)
  | ⟨8, _⟩ => Sha3Table.flushes
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => []
  | ⟨2, _⟩ => []

/-- The count columns: Lv42's opcode tables', and `SHA3`'s 27. -/
def counts : (j : Fin 9) → List (Fin (width j))
  | ⟨3, _⟩ => (baseTable 0).count
  | ⟨4, _⟩ => (baseTable 1).count
  | ⟨5, _⟩ => (baseTable 2).count
  | ⟨6, _⟩ => (baseTable 3).count
  | ⟨7, _⟩ => (baseTable 4).count
  | ⟨8, _⟩ => Sha3Table.counts
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => []
  | ⟨2, _⟩ => []

/-- Every constraint has total degree at most two (Lv42's `constraints_degree`). -/
theorem constraints_degree : ∀ j, ∀ C ∈ constraints j, C.totalDegree ≤ 2
  | ⟨3, _⟩ => Lv42.Protocol.LeanIsa.baseTable_constraints_degree 0
  | ⟨4, _⟩ => Lv42.Protocol.LeanIsa.baseTable_constraints_degree 1
  | ⟨5, _⟩ => Lv42.Protocol.LeanIsa.baseTable_constraints_degree 2
  | ⟨6, _⟩ => Lv42.Protocol.LeanIsa.baseTable_constraints_degree 3
  | ⟨7, _⟩ => Lv42.Protocol.LeanIsa.baseTable_constraints_degree 4
  | ⟨0, _⟩ => by simp [constraints]
  | ⟨1, _⟩ => by simp [constraints]
  | ⟨2, _⟩ => by simp [constraints]
  | ⟨8, _⟩ => by simp [constraints]

/-- Every flush coordinate has total degree at most two (Lv42's `flushes_degree`, `Sha3Table.flushes_degree`). -/
theorem flushes_degree : ∀ j, ∀ f ∈ flushes j, ∀ i, (f.2.get i).totalDegree ≤ 2
  | ⟨3, _⟩ => fun f hf i ↦ by
    obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
    exact Lv42.Protocol.LeanIsa.baseTable_flushes_degree 0 f' hf' i
  | ⟨4, _⟩ => fun f hf i ↦ by
    obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
    exact Lv42.Protocol.LeanIsa.baseTable_flushes_degree 1 f' hf' i
  | ⟨5, _⟩ => fun f hf i ↦ by
    obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
    exact Lv42.Protocol.LeanIsa.baseTable_flushes_degree 2 f' hf' i
  | ⟨6, _⟩ => fun f hf i ↦ by
    obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
    exact Lv42.Protocol.LeanIsa.baseTable_flushes_degree 3 f' hf' i
  | ⟨7, _⟩ => fun f hf i ↦ by
    obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
    exact Lv42.Protocol.LeanIsa.baseTable_flushes_degree 4 f' hf' i
  | ⟨8, _⟩ => Sha3Table.flushes_degree
  | ⟨0, _⟩ => by simp [flushes]
  | ⟨1, _⟩ => by simp [flushes]
  | ⟨2, _⟩ => by simp [flushes]

/-! ### The columns and the stack -/

/-- A column of the instance: table `j`, column `i`. -/
abbrev Col : Type := Σ j : Fin 9, Fin (width j)

/-- Memory column `i`: `MEM_LO, MEM_HI, MEM_TOP, MFCNT`. -/
def memCol (i : Fin 4) : Col := ⟨⟨0, by decide⟩, i⟩

/-- The bytecode finalize count `BFCNT`. -/
def bfcntCol : Col := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩

/-- The Flock column `QFLOCK`. -/
def flockCol : Col := ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩

/-- Column `i` of the `SHA3` table. -/
def sha3Col (i : ℕ) (h : i < Sha3Table.width) : Col := ⟨⟨8, by decide⟩, ⟨i, h⟩⟩

/-- Every column, in global order: table by table, column by column. All are committed. -/
def columns : List Col := (List.finRange 9).flatMap fun j ↦ (List.finRange (width j)).map (⟨j, ·⟩)

theorem mem_columns (c : Col) : c ∈ columns := by
  simp only [columns, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨c.1, c.2, rfl⟩

/-- The log-height of a column: its table's. -/
abbrev kappa (c : Col) : ℕ := height prog s c.1

/-- The columns in stacking order: largest first, ties in global order (Lv42's `stackOrder`). -/
def stackOrder : List Col :=
  columns.mergeSort fun a b ↦ decide (kappa prog s b ≤ kappa prog s a)

theorem stackOrder_pairwise :
    (stackOrder prog s).Pairwise fun a b ↦ decide (kappa prog s b ≤ kappa prog s a) :=
  List.pairwise_mergeSort (fun _ _ _ h₁ h₂ ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _

/-- The columns as aligned blocks, in stacking order. -/
def blocks : Blocks where
  n := (stackOrder prog s).length
  size b := kappa prog s (stackOrder prog s)[b]
  descending a b hab := by
    rcases (Fin.le_iff_val_le_val.mp hab).eq_or_lt with h | h
    · rw [Fin.ext h]
    · have := List.pairwise_iff_getElem.mp (stackOrder_pairwise prog s) a b a.isLt b.isLt h
      simp only [decide_eq_true_eq] at this
      exact this

/-- The stack's number of variables: the blocks' total rounded up to a power of two, at least `2^15`. -/
def keccakIsaμ : ℕ := max (Nat.clog 2 (blocks prog s).total) minMu

theorem blocks_fits : (blocks prog s).total ≤ 2 ^ keccakIsaμ prog s :=
  (Nat.le_pow_clog (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

variable {prog s} in
/-- The block of a column. -/
def blockOf (c : Col) : Fin (blocks prog s).n :=
  ⟨(stackOrder prog s).idxOf c, List.idxOf_lt_length_of_mem (List.mem_mergeSort.mpr (mem_columns c))⟩

theorem size_blockOf (c : Col) : (blocks prog s).size (blockOf c) = kappa prog s c := by
  show kappa prog s (stackOrder prog s)[(blockOf (prog := prog) (s := s) c : ℕ)] = _
  rw [show (stackOrder prog s)[(blockOf (prog := prog) (s := s) c : ℕ)] = c from List.getElem_idxOf _]

/-- The layout of the stack: every column at its aligned block. -/
def layout : Layout (keccakIsaμ prog s) Col (kappa prog s) :=
  ((blocks prog s).layout (blocks_fits prog s)).comap blockOf (size_blockOf prog s)

/-! ### The bus boundary and the public lines (Lv42's, with the Keccak VM's entries) -/

/-- Sixteen coordinates: the given ones, then constant zeros. -/
def coords {S : Shape} {κ : ℕ} (cs : List (Coord S κ)) : Vector (Coord S κ) 16 :=
  Vector.ofFn fun k ↦ cs.getD k (.const 0)

/-- Column `k` of the program's entries: the entry's coordinate `k + 1` at every slot. -/
def entryColumn (k : Fin 8) : Column prog.logSize :=
  ⟨Vector.ofFn fun i ↦ (entry (prog.code i))[k]⟩

/-- The six boundary blocks (Lv42's): the state boundary, the memory seed and finalize, the bytecode seed and
finalize. -/
def boundary : List (BoundaryBlock (shape prog s)) :=
  let entries : List (Coord (shape prog s) prog.logSize) :=
    (List.finRange 8).map fun k ↦ .known (entryColumn prog k)
  [⟨0, .push, coords [.const (channelSep StatePush.toRaw), .const 1, .const 1]⟩,
    ⟨s.logMem, .push, coords [.const (channelSep MemPush.toRaw), .known (idxColumn s.logMem),
      .const 1, .committed (memCol 0) rfl, .committed (memCol 1) rfl, .committed (memCol 2) rfl]⟩,
    ⟨prog.logSize, .push, coords ([.const (channelSep BytecodePush.toRaw),
      .known (idxColumn prog.logSize), .const 1] ++ entries)⟩,
    ⟨0, .pull, coords [.const (channelSep StatePull.toRaw), .const prog.finalPc, .const 1]⟩,
    ⟨s.logMem, .pull, coords [.const (channelSep MemPull.toRaw), .known (idxColumn s.logMem),
      .committed (memCol 3) rfl, .committed (memCol 0) rfl, .committed (memCol 1) rfl,
      .committed (memCol 2) rfl]⟩,
    ⟨prog.logSize, .pull, coords ([.const (channelSep BytecodePull.toRaw),
      .known (idxColumn prog.logSize), .committed bfcntCol rfl] ++ entries)⟩]

/-- The three public lines (Lv42's): `MEM_LO` holds `input₀, input₂` at cells `0, 1`, `MEM_HI` holds `input₁,
input₃`, `MEM_TOP` holds `0, 0`. -/
def publicLines (input : Lv42.Semantics.PublicInput) : Vector (PublicLine (shape prog s)) 3 :=
  #v[⟨memCol 0, input.lanes 0, input.lanes 2, false, s.logMem_pos⟩,
    ⟨memCol 1, input.lanes 1, input.lanes 3, false, s.logMem_pos⟩,
    ⟨memCol 2, 0, 0, false, s.logMem_pos⟩]

end KeccakIsa

open KeccakIsa

/-- **The Keccak VM's instance** of the public program `prog` at the announced sizes `s`. -/
abbrev keccakIsaInstance (prog : Program) (s : Sizes) : M3Instance where
  toShape := shape prog s
  Stmt := Lv42.Semantics.PublicInput
  constraints := constraints
  flushes := flushes
  d := 2
  constraints_degree := constraints_degree
  flushes_degree := flushes_degree
  counts := counts
  rows := rows prog s
  rows_le := rows_le prog s
  padRow := fun _ _ ↦ 0
  boundary := boundary prog s
  μ := keccakIsaμ prog s
  layout := layout prog s
  nLines := 3
  publicLines := publicLines prog s
  flock := none

/-! ## The Keccak-f block -/

/-- Log-size of a Keccak-f block's words: `2^11` words of `64` bits, `2^17` positions (`keccakR1csLogSize`). -/
abbrev kWords : ℕ := 11

/-- Cell `w` of block `t` of a column of `2^κ` blocks of `2^11` cells: cell `w + 2^11 t`. -/
def kBlockCell {κ : ℕ} (c : Column (kWords + κ)) (t : Fin (2 ^ κ)) (w : Fin (2 ^ kWords)) : K :=
  c.values[cubeIndex (k := kWords) w t]

/-- The state a block carries at the words `slot l`. -/
def kBlockState {κ : ℕ} (c : Column (kWords + κ)) (t : Fin (2 ^ κ)) (slot : Fin 25 → Fin (2 ^ kWords)) :
    KeccakState :=
  Vector.ofFn fun l ↦ (kBlockCell c t (slot l)).lane

/-- **What the Keccak-f region means**: the block R1CS, its constant position, the port words of each lane, and the
two directions between the region predicate and Keccak-f[1600]. -/
structure KeccakFlockSpec where
  /-- The R1CS of one block of `2^17` positions (`C = I`). -/
  r1cs : BlockR1CS E (Flock.kSkip + kWords)
  /-- The constant wire. -/
  constPos : Fin (2 ^ (Flock.kSkip + kWords))
  /-- The input port word of lane `l`. -/
  inSlot : Fin 25 → Fin (2 ^ kWords)
  /-- The output port word of lane `l`. -/
  outSlot : Fin 25 → Fin (2 ^ kWords)
  /-- Soundness: every block of a column satisfying the predicate holds Keccak-f of its input port at its output
  port. -/
  step_of_holds : ∀ {κ : ℕ} (c : Column (kWords + κ)), BlockR1CS.BatchHolds r1cs constPos (bitTable c) →
    ∀ t, kBlockState c t outSlot = keccakF1600 (kBlockState c t inSlot)
  /-- The honest column of a batch of input states. -/
  gen : {κ : ℕ} → Vector KeccakState (2 ^ κ) → Column (kWords + κ)
  /-- Completeness: the honest column satisfies the predicate. -/
  holds_gen : ∀ {κ : ℕ} (states : Vector KeccakState (2 ^ κ)),
    BlockR1CS.BatchHolds r1cs constPos (bitTable (gen states))
  /-- The honest column's block `t` holds state `t` at its input port. -/
  in_gen : ∀ {κ : ℕ} (states : Vector KeccakState (2 ^ κ)) (t : Fin (2 ^ κ)),
    kBlockState (gen states) t inSlot = states[t]

/-- The constant a `SHA3` input lane differs from its port word by: `END_BIT` for lane 16 (`keccak_slot_offset`). -/
def laneOffset (l : Fin 25) : K := if l.val = endLane then K.ofLane endBit else 0

section Aux

variable (F : KeccakFlockSpec) (prog : Program) (s : Sizes)

/-- The Flock column read off a stack. -/
def flockColumn (q : Column (keccakIsaμ prog s)) : Column (kWords + s.τ 5) :=
  (keccakIsaInstance prog s).column q flockCol

/-- Cell `x` of `SHA3` column `i`, read off a stack. -/
def sha3Cell (q : Column (keccakIsaμ prog s)) (i : ℕ) (h : i < Sha3Table.width) (x : Fin (2 ^ s.τ 5)) : K :=
  ((keccakIsaInstance prog s).column q (sha3Col i h)).values.get x

/-- **The Keccak-f region and the lanes' copies**: every block of `QFLOCK` satisfies the block R1CS with `1` at its
constant position, and on every executed `SHA3` row `t` the output lanes are block `t`'s output port and the input
lanes its input port, plus `END_BIT` in lane 16. -/
def KeccakAux (q : Column (keccakIsaμ prog s)) : Prop :=
  BlockR1CS.BatchHolds F.r1cs F.constPos (bitTable (flockColumn prog s q)) ∧
    ∀ t : Fin (2 ^ s.τ 5), t.val < s.rows 5 → ∀ l : Fin 25,
      sha3Cell prog s q (Sha3Table.inLane l) (by unfold Sha3Table.inLane Sha3Table.width; omega) t =
          kBlockCell (flockColumn prog s q) t (F.inSlot l) + laneOffset l ∧
        sha3Cell prog s q (Sha3Table.outLane l) (by unfold Sha3Table.outLane Sha3Table.width; omega) t =
          kBlockCell (flockColumn prog s q) t (F.outSlot l)

/-- **The Keccak VM's relation**: `M3Holds` of the instance and the Keccak-f region with the lanes' copies. -/
def KvHolds (input : Lv42.Semantics.PublicInput) (q : Column (keccakIsaμ prog s)) : Prop :=
  M3Holds (keccakIsaInstance prog s) input q ∧ KeccakAux F prog s q

/-- **The relation completeness starts from**: `M3Honest` and the Keccak-f region with the lanes' copies. -/
def KvHonest (input : Lv42.Semantics.PublicInput) (q : Column (keccakIsaμ prog s)) : Prop :=
  M3Honest (keccakIsaInstance prog s) input q ∧ KeccakAux F prog s q

end Aux

end KeccakVm

end
