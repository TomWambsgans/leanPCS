-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The basis-B encoding is `crates/leanvm/univariate`'s
-- (SPEC.md §2), the map `UniStatement/Mapping.lean`'s; the relation and its stack are `formal/KeccakVm`'s
-- (`keccakIsaInstance`, after `formal/Lv42`'s `leanIsaInstance`).
module

public import UniKeccak.Opening
public import UniStatement.Mapping
public import KeccakVm.Instance

/-!
# The Keccak verifier's commitments against the Keccak VM's stack

`UniStatement/Mapping.lean`'s map for the Keccak VM: the verifier's `C1` holds the tables' columns as basis-`B`
coefficients on its own stack (`layoutsK`); `KeccakVm.KvHolds F prog s input q` is about one stack `q` of values in
`KeccakVm.keccakIsaInstance`'s layout (`KeccakIsa.layout`: every column committed, largest first).

**The correspondence** (column of `C1` ↦ column of `keccakIsaInstance`; `t` an opcode, `i` a column):

| `C1` (`UniStatement.Column`) | KeccakVm (`KeccakIsa.Col`) | encoding |
|---|---|---|
| `memory k`, `k < 3` (limbs), `memory 3` (final counts) | `memCol k` (`MEM_LO, MEM_HI, MEM_TOP, MFCNT`) | basis `B`, `2^logMem` |
| `bytecodeFinal` | `bfcntCol` (`BFCNT`) | basis `B`, `2^logBytecode` |
| `qflock` | `flockCol` (`QFLOCK`, `2^(11 + τ_SHA3)` cells) | values; block `x` of the Keccak VM is `C1`'s block `rowPosition x` |
| `table t i`, every `i` (the `SHA3` table's 86, its 50 lanes included) | `⟨t + 3, i⟩` | basis `B`, `2^h_t`; row `x` of the Keccak VM is `C1`'s row `rowPosition x` |
| `inverse t` (`z_T`) | none | `CountsNonzero` (`Q_W`) |
| `qflockSlot j` (a view of `qflock`) | `kBlockCell · · j` | `Q_W` ties the lanes to it (`KeccakAux`'s copy clause) |

Unlike Lv42's `BLAKE2S` limbs, no column of the Keccak VM is read off `QFLOCK`: the lanes are committed in both, and
`KeccakAux` states what `Q_W`'s copy identities check (`in_l = port + END_BIT·[l = 16]`, `out_l = port`). The column
index `i` of a table is the same on both sides (`layout.rs`'s order: `KeccakVm.Sha3Table`'s `inLane l = 9 + l`,
`outLane l = 34 + l`, `cnt c = 59 + c` are `sha3Columns`' positions).

**The setup's table** (`setupStackK`): `UniStatement.setupStack` with the Keccak VM's bytecode entries
(`KeccakVm.entry`: `SHA3`'s `(g^5, o_m₀, …, o_out)`). No `A0`, `B0` stacks: the Keccak verifier opens no matrix.
-/

@[expose] public section

namespace UniKeccak

open LeanVM.Parameters UniStatement
open KeccakVm.KeccakIsa (Col blocks stackOrder kappa keccakIsaμ)
open Lv42.Protocol.LeanIsa (Sizes)

/-- `C1`'s layout at a shape on the Keccak VM (`layoutsK`; it does not depend on `C2`'s columns). -/
def c1LayoutK (shape : Shape) : StackLayout := ((layoutsK shape []).lookup .c1).getD default

/-- **The Keccak VM's column `c`, read off a `C1` stack** (the correspondence above), as `KeccakIsa.layout` reads it
(`Vector K (2 ^ kappa prog s c)`): a table's row `x` at `C1`'s row `rowPosition` (its `s.rows` executed rows at their
fixed cosets, the contract's height `h` from the shape), read in basis `B` at `h` variables; `QFLOCK`'s cell
`w + 2^11 x` at `q_flock`'s word `w + 2^11 · rowPosition x` (its blocks sit with `SHA3`'s rows). -/
def kvColumn (prog : KeccakVm.Program) (s : Sizes) (shape : Shape) (stack : ℕ → K) :
    (c : Col) → Vector K (2 ^ kappa prog s c)
  | ⟨⟨0, _⟩, i⟩ =>
    let coeffs := c1Block (c1LayoutK shape) stack (.memory i.val)
    Vector.ofFn fun x ↦ basisValue coeffs s.logMem x.val
  | ⟨⟨1, _⟩, _⟩ =>
    let coeffs := c1Block (c1LayoutK shape) stack .bytecodeFinal
    Vector.ofFn fun x ↦ basisValue coeffs prog.logSize x.val
  | ⟨⟨2, _⟩, _⟩ =>
    let values := c1Block (c1LayoutK shape) stack .qflock
    let hB := shape.heights.getD 5 0
    Vector.ofFn fun x ↦
      values.getD (x.val % 2 ^ KeccakVm.kWords + 2 ^ KeccakVm.kWords *
        rowPosition (s.rows 5) hB (x.val / 2 ^ KeccakVm.kWords)) 0
  | ⟨⟨j + 3, h⟩, i⟩ =>
    let coeffs := c1Block (c1LayoutK shape) stack (.table j i.val)
    let height := shape.heights.getD j 0
    Vector.ofFn fun x ↦ basisValue coeffs height (rowPosition (s.rows ⟨j, by omega⟩) height x.val)

/-- **The Keccak VM's stack a `C1` stack carries**: every column of `keccakIsaInstance` (`stackOrder`, largest
first), each read off `C1` (`kvColumn`), stacked as `KeccakIsa.layout` places it (`Blocks.stackColumn`). -/
def kvStack (prog : KeccakVm.Program) (s : Sizes) (shape : Shape) (stack : ℕ → K) :
    LeanVM.Protocol.Column (keccakIsaμ prog s) :=
  (blocks prog s).stackColumn (fun b ↦ kvColumn prog s shape stack (stackOrder prog s)[b]) (keccakIsaμ prog s)

/-- Slot `s` of instruction `i`'s bytecode tuple on the Keccak VM: `SEP_BYTECODE`, the pc `g^i`, a zero (the count
is the prover's), then the instruction's entry (`KeccakVm.entry`, slots 3 to 10). -/
def tupleSlotK (prog : KeccakVm.Program) (i : Fin (2 ^ prog.logSize)) (s : ℕ) : K :=
  if s = 0 then K.ofBits 4
  else if s = 1 then LeanVM.Parameters.gpow i.val
  else if s = 2 then 0
  else if h : s - 3 < 8 then (KeccakVm.entry (prog.code i))[s - 3]
  else 0

/-- **The Keccak VM's setup stack** (`F`): the bytecode's 16 slots (slot `s` of coefficient `k` at word `s + 16 k`) and
the memory's addresses `g^i`, both in basis `B`, at the setup layout's offsets (`setupLayout`: the setup's layout does
not depend on the tables); zero elsewhere. -/
def setupStackK (prog : KeccakVm.Program) (shape : Shape) : Array K :=
  let layout := setupLayout shape
  let slots : Array (Array K) := Array.ofFn (n := 16) fun s ↦
    bCoefficients prog.logSize (Array.ofFn (n := 2 ^ prog.logSize) fun i ↦ tupleSlotK prog i s.val)
  let addresses := bCoefficients shape.logMemory
    (Array.ofFn (n := 2 ^ shape.logMemory) fun i ↦ LeanVM.Parameters.gpow i.val)
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

/-- **What the verifier fixes of the Keccak-f block** (`KeccakFlockSpec`'s fields the verifier reads): input lane `l` at
port word `4l + 2` and output lane `l` at port word `4l` (`keccakSlot`), the constant wire at position `64`
(`keccak_flock::CONSTANT_COLUMN`, the lincheck's pin). The block's R1CS itself is the one whose lincheck terminal
`structuredTerminal` computes (not stated here: no Lean R1CS of the block is in this library). -/
def KeccakFlockFits (F : KeccakVm.KeccakFlockSpec) : Prop :=
  (∀ l : Fin 25, (F.inSlot l).val = keccakStateWord (-1) l.val) ∧
    (∀ l : Fin 25, (F.outSlot l).val = keccakStateWord 23 l.val) ∧ F.constPos.val = constantColumn

end UniKeccak

end
