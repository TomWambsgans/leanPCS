-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The basis-B encoding is `crates/leanvm/univariate`'s
-- (SPEC.md §2); the novel-basis transform is this repository's `formal/Statement` (`PcsQuotient.Domain`); the
-- programs and sizes are `formal/Lv42`'s (leanerVM `mumbai` f0393df4's, MIT OR Apache-2.0).
module

public import UniStatement.Run
public import PcsQuotient.Domain
public import Lv42.Protocol.LeanIsaBase

/-!
# The univariate commitments' encodings

The verifier's `C1` and setup commitments hold the tables' columns as **coefficients** in the basis `B`
(SPEC.md §2) on their own stack (`layouts`). This file has the maps the statements read them by:

* `basisValue c r x`: the value at `ω_x` of the column whose `2^r` basis-`B` coefficients are `c`, the
  `K`-multilinear extension of `c` at the digits `w_l(ω_x) = ω_{x >> l}` (SPEC.md §2:
  `f(t) = ĉ(w_0(t), …, w_{r−1}(t))`);
* `bCoefficients r v`: the inverse, the basis-`B` coefficients of the column of values `v`: the novel-basis
  coefficients (`PcsQuotient.Domain.coefficients`), then `c_k = Σ_{S ⊆ k} d_S`, since `B_k = Σ_{S ⊇ k} X_S`;
* **the rows' order** (`rowPosition`, iteration 2, F1b): a table's executed rows are its first `count`; the
  univariate PIOP places them at the fixed cosets of the count's set bits (`activePositions`), padding rows at the
  other rows in order (the rows' order is not part of leanVM's statement: the bus is a multiset, the constraints
  hold on every row, padding rows are free);
* the public input the calldata's 32 bytes are (`publicInputOf`), a proof's sizes (`sizesOf`);
* the setup's tables (`setupStack`, `matrixStack`): the bytecode's 16 tuple slots and the memory's addresses (in
  basis `B`), and Flock's matrices `A0`, `B0` (`0`/`1` entries, row low).

The map from a `C1` stack to Lv42's stack is `UniKeccak.Mapping`'s.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters
open Lv42.Protocol.LeanIsa (Sizes)
open Lv42.Semantics (Program PublicInput)

/-- The `K`-multilinear extension of a table at a point of `K`, low coordinate first. -/
def mleK (table : Array K) (pt : List K) : K :=
  (pt.foldl (fun (cur : Array K) r ↦ Array.ofFn (n := cur.size / 2) fun i ↦
    let a := cur.getD (2 * i.val) 0
    let b := cur.getD (2 * i.val + 1) 0
    a + r * (a + b)) table).getD 0 0

/-- **The value at `ω_x`** of the column of `2^r` basis-`B` coefficients `c`: `ĉ(ω_x, ω_{x>>1}, …)`. -/
def basisValue (c : Array K) (r x : ℕ) : K := mleK c ((List.range r).map fun l ↦ point (x >>> l))

/-- `c_k = Σ_{S ⊆ k} d_S` (the subset-sum transform, its own inverse in characteristic two). -/
def subsetSums (r : ℕ) (d : Array K) : Array K :=
  (List.range r).foldl (fun a l ↦ Array.ofFn (n := a.size) fun k ↦
    if k.val.testBit l then a.getD k.val 0 + a.getD (k.val - 2 ^ l) 0 else a.getD k.val 0) d

/-- **The basis-`B` coefficients** of the column of values `v` on `V_r`. -/
def bCoefficients (r : ℕ) (v : Array K) : Array K := subsetSums r (PcsQuotient.Domain.coefficients r 0 v)

/-- The setup's layout at a shape (`setupStackColumns`: it does not depend on the tables). -/
def setupLayout (shape : UniStatement.Shape) : StackLayout := StackLayout.new (setupStackColumns shape)

/-- Column `column`'s block of a stack (its limb `0`): `2^vars` words from its offset. -/
def c1Block (layout : StackLayout) (stack : ℕ → K) (column : UniStatement.Column) : Array K :=
  match layout.limbs column with
  | (_, vars, offset) :: _ => Array.ofFn (n := 2 ^ vars) fun i ↦ stack (offset + i.val)
  | [] => #[]

/-- **Where Lv42's row `x` of a table sits in `C1`** (iteration 2, F1b): Lv42's executed rows are its first
`count` (`x < count`), the univariate PIOP's are at the fixed cosets of the count's set bits
(`activePositions`, in order); Lv42's padding rows `x ≥ count` are `C1`'s other rows, in increasing order (the
cosets of the unset bits below `r`, highest first, then the last row `2^r − 1`). A bijection of `[0, 2^r)` for
`count ≤ 2^r`; the identity for a full table. -/
def rowPosition (count r x : ℕ) : ℕ := Id.run do
  if count = 2 ^ r then return x
  let active := decide (x < count)
  let mut y := if active then x else x - count
  for i in [0:r] do
    let b := r - 1 - i
    if count.testBit b == active then
      if y < 2 ^ b then return 2 ^ r - 2 ^ (b + 1) + y
      y := y - 2 ^ b
  return 2 ^ r - 1

/-- **The public input** the calldata's 32 bytes are: four 64-bit big-endian words, `lanes k` the word `k`
(as `publicWordsOf`, the verifier's own reading). -/
def publicInputOf (bytes : List UInt8) : PublicInput :=
  ⟨fun k ↦ K.ofLane (beWordAt bytes.toArray (8 * k.val))⟩

/-- The sizes of a proof, as Lv42's `Sizes`: the shape's memory (its log-size must be positive) and the proof's
row counts. -/
def sizesOf (shape : UniStatement.Shape) (h : 0 < shape.logMemory) (rows : List ℕ) : Sizes :=
  ⟨shape.logMemory, h, fun j ↦ rows.getD j.val 0⟩

/-! ### The setup's tables -/

/-- Slot `s` of instruction `i`'s bytecode tuple (SPEC.md §3): `SEP_BYTECODE`, the pc `g^i`, a zero (the
count is the prover's), then the instruction's entry (`Lv42.Arithmetization.entry`, slots 3 to 10). -/
def tupleSlot (prog : Program) (i : Fin (2 ^ prog.logSize)) (s : ℕ) : K :=
  if s = 0 then K.ofBits 4
  else if s = 1 then LeanVM.Parameters.gpow i.val
  else if s = 2 then 0
  else if h : s - 3 < 8 then (Lv42.Arithmetization.entry (prog.code i))[s - 3]
  else 0

/-- **The setup stack** (`F`): the bytecode's 16 slots, slot `s` of coefficient `k` at word `s + 16 k`
(the slot is the low four coordinates: the claim's point is `(α, w(t))`), and the memory's addresses
`g^i`, both in basis `B`, at the setup layout's offsets; zero elsewhere. -/
def setupStack (prog : Program) (shape : UniStatement.Shape) : Array K :=
  let layout := setupLayout shape
  let slots : Array (Array K) := Array.ofFn (n := 16) fun s ↦
    bCoefficients prog.logSize (Array.ofFn (n := 2 ^ prog.logSize) fun i ↦ tupleSlot prog i s.val)
  let addresses := bCoefficients shape.logMemory (Array.ofFn (n := 2 ^ shape.logMemory) fun i ↦ LeanVM.Parameters.gpow i.val)
  let (_, _, tupleOffset) := (layout.limbs .bytecodeTuple).headD (0, 0, 0)
  let (_, _, addressOffset) := (layout.limbs .address).headD (0, 0, 0)
  Array.ofFn (n := 2 ^ layout.vars) fun w ↦
    let w := w.val
    if tupleOffset ≤ w ∧ w < tupleOffset + 2 ^ (shape.logBytecode + 4) then
      let j := w - tupleOffset
      (slots.getD (j % 16) #[]).getD (j / 16) 0
    else if addressOffset ≤ w ∧ w < addressOffset + 2 ^ shape.logMemory then
      addresses.getD (w - addressOffset) 0
    else 0

/-- **A matrix of Flock's R1CS as a stack** of `2^28` words: entry `(k, j)` (row `k`, column `j`) at word
`k + 2^14 j`, `1` or `0` (`matrix_values`: the row's 14 coordinates, then the column's). -/
def matrixStack (A : Fin (2 ^ 14) → Fin (2 ^ 14) → Bool) : Array K :=
  Array.ofFn (n := 2 ^ 28) fun w ↦
    if A ⟨w.val % 2 ^ 14, Nat.mod_lt _ (by decide)⟩ ⟨w.val / 2 ^ 14 % 2 ^ 14, Nat.mod_lt _ (by decide)⟩
    then 1 else 0

end UniStatement

end
