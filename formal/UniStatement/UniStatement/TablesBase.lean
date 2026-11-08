-- Part of this repository. Transcribed from `crates/leanvm/statement/src/layout.rs` (`Form`, `Flushes`, the six
-- tables' columns, flushes and counters, `BLAKE2S_SLOTS`), adapted there from leanVM
-- (https://github.com/leanEthereum/leanVM), commit 42422001, `crates/verifier/src/layout.rs`. MIT OR Apache-2.0;
-- see NOTICE.md.
module

public import UniStatement.Basic

/-!
# The instruction tables (`layout.rs`): the forms, the flushes, the five shared tables

leanVM 42422001's tables as the verifier reads them: their columns (by name), their bus flushes (each a
**pull** tuple and the **push** tuple it pairs with, coordinates as `Form`s: polynomials of degree at most
two in the row's columns with constant coefficients) and their counter columns (the names starting with
`cnt`). The flushes are built by the Rust's helpers (`state_step`, `bytecode`, `memory_cols`, …), here
`Flushes.*`, so the transcription is line by line.

**A `Form`** is the Rust's `BTreeMap<Vec<usize>, E>` as a list sorted by the monomial (lexicographic, a
prefix first, as `Vec`'s order), `[]` the constant, `[i]` the column `x_i`, `[i, j]` (`i ≤ j`) the product.
Its iteration order is the map's, which fixes the order in which the verifier states its terms; an entry
whose coefficient is zero stays in the map (as `add_scaled` leaves it), and every reader skips it.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters

/-- `Vec<usize>`'s order: lexicographic, a proper prefix first. -/
def monoLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && monoLt as bs)

/-- **A form**: monomial ↦ coefficient, sorted by the monomial (`Form`, `layout.rs`). -/
abbrev Form := List (List ℕ × E)

/-- `entry(monomial) += c`: insert in order, or add to the entry. -/
def Form.addAt (f : Form) (mono : List ℕ) (c : E) : Form :=
  match f with
  | [] => [(mono, c)]
  | (k, v) :: rest =>
    if k == mono then (k, v + c) :: rest
    else if monoLt mono k then (mono, c) :: (k, v) :: rest
    else (k, v) :: Form.addAt rest mono c

/-- `add_scaled(other, weight)`: `self += weight · other`, entry by entry in `other`'s order. -/
def Form.addScaled (f other : Form) (weight : E) : Form :=
  other.foldl (fun acc (mono, c) ↦ acc.addAt mono (weight * c)) f

/-- `Form::term(monomial, c)`. -/
def Form.term (mono : List ℕ) (c : E) : Form := [(mono, c)]

/-- `self + other` (`Add for Form`): `add_scaled(other, ONE)`. -/
def Form.add (f other : Form) : Form := f.addScaled other 1

/-- `Form::sum(forms)`: from the empty form. -/
def Form.sum (forms : List Form) : Form := forms.foldl Form.add []

/-- `constant(value)`. -/
def constant (value : E) : Form := Form.term [] value

/-- `col(index, exponent) = g^exponent · x_index`. -/
def col (index exponent : ℕ) : Form := Form.term [index] (gpow exponent)

/-- `prod(a, b, exponent) = g^exponent · x_a x_b`. -/
def prod (a b exponent : ℕ) : Form := Form.term [min a b, max a b] (gpow exponent)

/-- `SEP_STATE = 1`. -/
def sepState : E := 1
/-- `SEP_MEM = g`. -/
def sepMem : E := gen
/-- `SEP_BYTECODE = g^2`. -/
def sepBytecode : E := eK 4

/-- **The bus flushes of a table** (`Flushes`): its push tuples and its pull tuples, the `k`-th of each
paired. -/
structure Flushes where
  push : List (List Form)
  pull : List (List Form)
  deriving Inhabited

namespace Flushes

/-- `pair(push, pull)`. -/
def pair (f : Flushes) (push pull : List Form) : Flushes := ⟨f.push ++ [push], f.pull ++ [pull]⟩

/-- `state_derived(pc, fp, npc, nfp)`: push `(SEP_STATE, npc, nfp)`, pull `(SEP_STATE, pc, fp)`. -/
def stateDerived (f : Flushes) (pc fp : ℕ) (npc nfp : Form) : Flushes :=
  f.pair [constant sepState, npc, nfp] [constant sepState, col pc 0, col fp 0]

/-- `state_step(pc, fp)`: the next state is `(g·pc, fp)`. -/
def stateStep (f : Flushes) (pc fp : ℕ) : Flushes := f.stateDerived pc fp (col pc 1) (col fp 0)

/-- `counted(prefix, count, suffix)`: push with the counter `g·count`, pull with `count`. -/
def counted (f : Flushes) (pre : List Form) (count : ℕ) (suffix : List Form) : Flushes :=
  let side (counter : Form) : List Form := pre ++ [counter] ++ suffix
  f.pair (side (col count 1)) (side (col count 0))

/-- `bytecode(pc, count, opcode, operands)`: `(SEP_BYTECODE, pc, count, g^opcode, operands…)`. -/
def bytecode (f : Flushes) (pc count opcode : ℕ) (operands : List Form) : Flushes :=
  f.counted [constant sepBytecode, col pc 0] count ([constant (gpow opcode)] ++ operands)

/-- `memory(address, count, values)`: `(SEP_MEM, address, count, v₀, v₁, v₂)`. -/
def memory (f : Flushes) (address : Form) (count : ℕ) (values : List Form) : Flushes :=
  f.counted [constant sepMem, address] count values

/-- `memory_cols(address, count, columns)`: the cell's limbs the named columns, the missing top ones zero. -/
def memoryCols (f : Flushes) (address : Form) (count : ℕ) (columns : List ℕ) : Flushes :=
  f.memory address count ((List.range 3).map fun limb ↦
    match columns[limb]? with
    | some c => col c 0
    | none => constant 0)

end Flushes

/-- **One instruction's table** (`Table`): its opcode (its index), its column names, its flushes. -/
structure Table where
  opcode : ℕ
  columns : List String
  flushes : Flushes
  deriving Inhabited

/-- `Table::width`. -/
def Table.width (t : Table) : ℕ := t.columns.length

/-- `Table::count_columns`: the columns whose name starts with `cnt`, in order. -/
def Table.countColumns (t : Table) : List ℕ :=
  (List.range t.width).filter fun i ↦ (t.columns.getD i "").startsWith "cnt"

/-- The index of a column by name (`cols`, `column_index`). -/
def colIdx (columns : List String) (n : String) : ℕ := columns.idxOf n

/-- `OP_XOR … OP_BLAKE2S` and `N_TABLES`. -/
def opXor : ℕ := 0
def opMul : ℕ := 1
def opSet : ℕ := 2
def opDeref : ℕ := 3
def opJump : ℕ := 4
def nTables : ℕ := 6

/-- `ARITH_COLUMNS`. -/
def arithColumns : List String :=
  ["pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a", "cnt_b",
    "cnt_c", "cnt_bc"]
/-- `SET_COLUMNS`. -/
def setColumns : List String := ["pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc"]
/-- `DEREF_COLUMNS`. -/
def derefColumns : List String :=
  ["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "v3_2", "cnt_ptr", "cnt_target",
    "cnt_local", "cnt_bc"]
/-- `JUMP_COLUMNS`. -/
def jumpColumns : List String :=
  ["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f", "cnt_bc", "w", "b"]
/-- `flushes_arith(opcode, multiply)`: XOR (`multiply = false`, the result limbwise `va + vb`) and MUL (the
tower product's three lanes). -/
def flushesArith (opcode : ℕ) (multiply : Bool) : Flushes :=
  let c := colIdx arithColumns
  let (pc, fp, oA, oB, oC) := (c "pc", c "fp", c "o_a", c "o_b", c "o_c")
  let (cntA, cntB, cntC, cntBc) := (c "cnt_a", c "cnt_b", c "cnt_c", c "cnt_bc")
  let va := [c "va_0", c "va_1", c "va_2"]
  let vb := [c "vb_0", c "vb_1", c "vb_2"]
  let towerLanes : List (List (ℕ × ℕ)) :=
    [[(0, 0), (1, 2), (2, 1)], [(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)], [(0, 2), (1, 1), (2, 0), (2, 2)]]
  let result : List Form :=
    if multiply then
      towerLanes.map fun lane ↦ Form.sum (lane.map fun (j, k) ↦ prod (va.getD j 0) (vb.getD k 0) 0)
    else (List.range 3).map fun i ↦ (col (va.getD i 0) 0).add (col (vb.getD i 0) 0)
  let operands := [col oA 0, col oB 0, col oC 0, constant 0, constant 0]
  ((((({ push := [], pull := [] } : Flushes).stateStep pc fp).bytecode pc cntBc opcode operands).memoryCols
    (prod fp oA 0) cntA va).memoryCols (prod fp oB 0) cntB vb).memory (prod fp oC 0) cntC result

/-- `flushes_set()`. -/
def flushesSet : Flushes :=
  let c := colIdx setColumns
  let (pc, fp, o, cnt, cntBc) := (c "pc", c "fp", c "o", c "cnt", c "cnt_bc")
  let k := [c "k_0", c "k_1", c "k_2"]
  let operands := [col o 0, col (k.getD 0 0) 0, col (k.getD 1 0) 0, col (k.getD 2 0) 0, constant 0]
  ((({ push := [], pull := [] } : Flushes).stateStep pc fp).bytecode pc cntBc opSet operands).memoryCols
    (prod fp o 0) cnt k

/-- `flushes_deref()`: the stored value `v2 = (1 + f_pc + f_fp) v3 + f_pc·(g²·pc) + f_fp·fp`, lane-wise. -/
def flushesDeref : Flushes :=
  let c := colIdx derefColumns
  let (pc, fp, o1, o2, o3, fPc, fFp, ptr) :=
    (c "pc", c "fp", c "o1", c "o2", c "o3", c "f_pc", c "f_fp", c "ptr")
  let (cntPtr, cntTarget, cntLocal, cntBc) := (c "cnt_ptr", c "cnt_target", c "cnt_local", c "cnt_bc")
  let v3 := [c "v3_0", c "v3_1", c "v3_2"]
  let gated (lane : ℕ) : List Form := [col lane 0, prod fPc lane 0, prod fFp lane 0]
  let store : List Form :=
    [Form.sum (gated (v3.getD 0 0) ++ [prod fPc pc 2, prod fFp fp 0]), Form.sum (gated (v3.getD 1 0)),
      Form.sum (gated (v3.getD 2 0))]
  let operands := [col o1 0, col o2 0, col o3 0, col fPc 0, col fFp 0]
  (((({ push := [], pull := [] } : Flushes).stateStep pc fp).bytecode pc cntBc opDeref operands).memoryCols
    (prod fp o1 0) cntPtr [ptr] |>.memory (prod ptr o2 0) cntTarget store).memoryCols (prod fp o3 0) cntLocal v3

/-- `flushes_jump()`: `next_pc = b·dest + (b + 1)·g·pc`, `next_fp = b·frame + (b + 1)·fp`, both derived. -/
def flushesJump : Flushes :=
  let c := colIdx jumpColumns
  let (pc, fp, oC, oD, oF, cond, dest, frame, b) :=
    (c "pc", c "fp", c "o_c", c "o_d", c "o_f", c "v_cond", c "v_pc", c "v_fp", c "b")
  let (cntC, cntD, cntF, cntBc) := (c "cnt_c", c "cnt_d", c "cnt_f", c "cnt_bc")
  let npc := ((prod b dest 0).add (prod b pc 1)).add (col pc 1)
  let nfp := ((prod b frame 0).add (prod b fp 0)).add (col fp 0)
  let operands := [col oC 0, col oD 0, col oF 0, constant 0, constant 0]
  (((({ push := [], pull := [] } : Flushes).stateDerived pc fp npc nfp).bytecode pc cntBc opJump
    operands).memoryCols (prod fp oC 0) cntC [cond] |>.memoryCols (prod fp oD 0) cntD [dest]).memoryCols
    (prod fp oF 0) cntF [frame]

end UniStatement

end
