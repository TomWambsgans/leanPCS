-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The five instructions other than the hash are
-- `formal/Lv42`'s (leanerVM `mumbai` f0393df4, leanVM 42422001), reused; the `SHA3` instruction is leanVM
-- `9d50c92a3`'s (`crates/leanvm_core/src/cpu/isa.rs`, `cpu/execute.rs`, `tables.rs::sha3_cells`,
-- `hash_flock.rs::{CELL_LANES, state_of_cells, cells_of_state, step_cells}`, `crates/primitives/src/hash.rs::step`),
-- its Keccak-f[1600] leanerVM 6175f1a0's (`Statement/Keccak.lean`).
module

public import Lv42.Spec.Isa
public import Statement.Keccak

/-!
# The Keccak VM's leanISA

The Keccak VM (`crates/leanvm_univariate/KECCAK.md`) is leanVM 42422001 with its `BLAKE2S` instruction replaced by
leanVM `9d50c92a3`'s `SHA3`: one step of that leanVM's cell sponge.

* **`SHA3 m₀ m₁ m₂ m₃ tail cap out`** reads thirteen cells: `[o_m₀], …, [o_m₃]` (four independently addressed),
  `[g^k · o_tail]` (`k < 4`), `[g^k · o_cap]` (`k < 5`); and the thirteen cells `[g^k · o_out]` (`k < 13`). The
  thirteen cells hold the 25 lanes of a Keccak state in the order `sha3CellLanes` (`hash_flock::CELL_LANES`):
  cell `c < 8` lanes `(2c, 2c + 1)` in limbs `0, 1`; cell `8` lane `16` alone in limb `0`; cell `9 ≤ c < 13` lanes
  `(2c − 1, 2c)`. A read cell is canonical: its `y²` limb is zero, and the lone cell's `y` limb too (`execute.rs`:
  `NotCanonical`). The written cells are `cellsOfState (sha3Step s)` of the state `s` the read cells hold, where
  `sha3Step s = Keccak-f[1600](s ⊕ END_BIT · e₁₆)`, `END_BIT = 0x80 << 56` (`primitives::hash::step`: SHA3's last
  padding bit in rate lane 16).
* **The other five instructions** are Lv42's, executed by `Lv42.Semantics.executeWith` (`executeWith_base`), and the
  machine (registers, memory, programs, `run`, `ValidExecution`) is Lv42's with this instruction set: the same
  halting rule (at `finalPc`, `fp = 1` required), the same memory bounds and public boundary.
* **The bytecode entry** of `SHA3` is `(g^5, o_m₀, o_m₁, o_m₂, o_m₃, o_tail, o_cap, o_out)`, the order of the
  `SHA3` table's bytecode flush (`layout.rs::flushes_sha3`); the other entries are Lv42's.

`KeccakVmTest/Isa.lean` checks `sha3Step` against SHA3-256: a message of at most 128 bytes is hashed by one step (leanVM
`9d50c92a3`'s cell encoding is plain SHA3-256 there), so the step of `"abc" ‖ 0x06` in the rate's first lanes
gives SHA3-256(`"abc"`) in lanes `0..3`.
-/

@[expose] public section

namespace KeccakVm

open LeanVM.Parameters LeanVM.Semantics
open Lv42.Parameters (minLogMem maxLogMem maxLogBytecode)

/-! ## Opcodes and instructions -/

/-- The six instructions, in bus-code order: Lv42's five, then `SHA3` in `BLAKE2S`'s place. -/
inductive Opcode
  | xor
  | mulNative
  | setConstant
  | deref
  | jump
  | sha3
  deriving DecidableEq, Repr

/-- The bus code: `g^0, …, g^5` in constructor order (`SHA3` takes `BLAKE2S`'s, `OP_SHA3 = 5`). -/
def Opcode.code : Opcode → K
  | .xor => gpow 0
  | .mulNative => gpow 1
  | .setConstant => gpow 2
  | .deref => gpow 3
  | .jump => gpow 4
  | .sha3 => gpow 5

/-- The Keccak VM's instructions. -/
inductive Instr
  /-- `[o_C] = [o_A] + [o_B]`. -/
  | xor (oA oB oC : K)
  /-- `[o_C] = [o_A] · [o_B]`. -/
  | mulNative (oA oB oC : K)
  /-- `[o] = k`. -/
  | setConstant (o : K) (k : E)
  /-- Lv42's `DEREF`. -/
  | deref (o1 o2 o3 : K) (mode : Lv42.Semantics.DerefMode)
  /-- Lv42's `JUMP`. -/
  | jump (oc od of : K)
  /-- One step of the cell sponge: the thirteen cells `[o_m₀], …, [o_m₃]`, `[g^k · o_tail]` (`k < 4`),
  `[g^k · o_cap]` (`k < 5`) hold a state; the thirteen cells `[g^k · o_out]` (`k < 13`) hold its `sha3Step`
  (`Sha3Cells`). -/
  | sha3 (om : Fin 4 → K) (otail ocap oout : K)
  deriving DecidableEq

/-- The opcode of an instruction. -/
def Instr.opcode : Instr → Opcode
  | .xor .. => .xor
  | .mulNative .. => .mulNative
  | .setConstant .. => .setConstant
  | .deref .. => .deref
  | .jump .. => .jump
  | .sha3 .. => .sha3

/-- The instructions Lv42 has too, as Lv42's; `SHA3` has none. -/
def Instr.base? : Instr → Option Lv42.Semantics.Instr
  | .xor oA oB oC => some (.xor oA oB oC)
  | .mulNative oA oB oC => some (.mulNative oA oB oC)
  | .setConstant o k => some (.setConstant o k)
  | .deref o1 o2 o3 mode => some (.deref o1 o2 o3 mode)
  | .jump oc od of => some (.jump oc od of)
  | .sha3 .. => none

/-! ## `SHA3` -/

/-- `END_BIT = 0x80 << 56` (`primitives::hash::END_BIT`): SHA3's last padding bit, in rate lane `16`. -/
def endBit : UInt64 := (0x80 : UInt64) <<< 56

/-- The rate lane `END_BIT` lives in (`END_LANE = RATE_LANES − 1`). -/
def endLane : ℕ := 16

/-- **One step of the cell sponge** (`primitives::hash::step`): XOR `END_BIT` into lane `16` and permute. -/
def sha3Step (s : KeccakState) : KeccakState :=
  keccakF1600 (s.setIfInBounds endLane (Keccak.lane s endLane ^^^ endBit))

/-- The lanes state cell `c` holds, `(lo, hi)`, `none` a literal zero (`hash_flock::CELL_LANES`): lanes `0..16` two
to a cell, then lane `16` alone, then the capacity lanes `17..25`. -/
def sha3CellLanes (c : ℕ) : ℕ × Option ℕ :=
  if c < 8 then (2 * c, some (2 * c + 1))
  else if c = 8 then (16, none)
  else (2 * c - 1, some (2 * c))

/-- The cell and limb holding lane `l`: the inverse of `sha3CellLanes` (`laneCell_cellLanes`). -/
def laneCell (l : ℕ) : ℕ × Fin 2 :=
  if l < 16 then (l / 2, ⟨l % 2, Nat.mod_lt _ (by decide)⟩)
  else if l = 16 then (8, 0)
  else ((l + 1) / 2, ⟨(l + 1) % 2, Nat.mod_lt _ (by decide)⟩)

/-- `laneCell` inverts `sha3CellLanes`: every lane is held once, at the cell and limb `laneCell` names. -/
theorem laneCell_cellLanes :
    (∀ l < 25, (laneCell l).1 < 13 ∧
      (if (laneCell l).2 = 0 then (sha3CellLanes (laneCell l).1).1 = l
       else (sha3CellLanes (laneCell l).1).2 = some l)) ∧
    ∀ c < 13, laneCell (sha3CellLanes c).1 = (c, 0) ∧
      ∀ h, (sha3CellLanes c).2 = some h → laneCell h = (c, 1) := by
  decide

/-- The state thirteen cells hold (`hash_flock::state_of_cells`): lane `l` is the limb of the cell that holds it. -/
def stateOfCells (cells : Fin 13 → E) : KeccakState :=
  Vector.ofFn fun l : Fin 25 ↦
    let (c, limb) := laneCell l.val
    if h : c < 13 then ((cells ⟨c, h⟩).limb ⟨limb.val, by omega⟩).lane else 0

/-- The thirteen cells holding a state (`hash_flock::cells_of_state`): a missing high lane and the `y²` limb zero. -/
def cellsOfState (s : KeccakState) (c : Fin 13) : E :=
  E.ofLimbs (K.ofLane (Keccak.lane s (sha3CellLanes c).1))
    (match (sha3CellLanes c).2 with
     | some h => K.ofLane (Keccak.lane s h)
     | none => 0) 0

/-- A read cell is canonical (`execute.rs`, `NotCanonical`): its `y²` limb zero, and the lone lane-16 cell's `y`
limb zero too (the table reads it with `memory_k`). -/
def Sha3Canonical (c : Fin 13) (x : E) : Prop :=
  IsCanonical128 x ∧ ((sha3CellLanes c).2 = none → x.limb 1 = 0)

instance (c : Fin 13) (x : E) : Decidable (Sha3Canonical c x) := by
  unfold Sha3Canonical; infer_instance

/-- **What `SHA3` checks**: the thirteen read cells are canonical, and the thirteen written cells hold `sha3Step` of
the state the read cells hold. -/
def Sha3Cells (input output : Fin 13 → E) : Prop :=
  (∀ c, Sha3Canonical c (input c)) ∧ ∀ c, output c = cellsOfState (sha3Step (stateOfCells input)) c

instance (input output : Fin 13 → E) : Decidable (Sha3Cells input output) := by
  unfold Sha3Cells; infer_instance

/-- The address of read cell `c` relative to the frame (`tables.rs::sha3_cells`, `layout.rs::flushes_sha3`):
`o_m₀, …, o_m₃`, then `g^k · o_tail` (`k < 4`), then `g^k · o_cap` (`k < 5`). -/
def sha3InOffset (om : Fin 4 → K) (otail ocap : K) (c : Fin 13) : K :=
  if h : c.val < 4 then om ⟨c.val, h⟩
  else if c.val < 8 then g ^ (c.val - 4) * otail
  else g ^ (c.val - 8) * ocap

/-- The address of written cell `c` relative to the frame: `g^c · o_out`. -/
def sha3OutOffset (oout : K) (c : Fin 13) : K := g ^ c.val * oout

/-- Read the thirteen words at the frame-relative offsets `offset c`; `none` if any read fails. -/
def readCells (read : K → Option E) (fp : K) (offset : Fin 13 → K) : Option (Fin 13 → E) :=
  (List.finRange 13).foldr (fun c acc ↦ do
    let v ← read (fp * offset c)
    let rest ← acc
    pure fun c' ↦ if c' = c then v else rest c') (some fun _ ↦ 0)

/-! ## One step -/

/-- Execute an instruction with the memory reader `read`: Lv42's five through `Lv42.Semantics.executeWith`, and
`SHA3`: read its 26 cells, check `Sha3Cells`, go to the next instruction. -/
def executeWith (read : K → Option E) (r : Lv42.Semantics.Regs K) : Instr → Option (Lv42.Semantics.Regs K)
  | .xor oA oB oC => Lv42.Semantics.executeWith read r (.xor oA oB oC)
  | .mulNative oA oB oC => Lv42.Semantics.executeWith read r (.mulNative oA oB oC)
  | .setConstant o k => Lv42.Semantics.executeWith read r (.setConstant o k)
  | .deref o1 o2 o3 mode => Lv42.Semantics.executeWith read r (.deref o1 o2 o3 mode)
  | .jump oc od of => Lv42.Semantics.executeWith read r (.jump oc od of)
  | .sha3 om otail ocap oout => do
    let input ← readCells read r.fp (sha3InOffset om otail ocap)
    let output ← readCells read r.fp (sha3OutOffset oout)
    guard (Sha3Cells input output)
    pure r.next

/-- The five instructions Lv42 has execute as in Lv42. -/
theorem executeWith_base (read : K → Option E) (r : Lv42.Semantics.Regs K) (i : Instr)
    (b : Lv42.Semantics.Instr) (h : i.base? = some b) :
    executeWith read r i = Lv42.Semantics.executeWith read r b := by
  cases i <;> simp only [Instr.base?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-! ## Programs and valid executions (Lv42's, with this instruction set) -/

/-- A program: `2^logSize` instructions, instruction `i` at address `g^i`. -/
structure Program where
  logSize : ℕ
  logSize_le : logSize ≤ maxLogBytecode
  code : Fin (2 ^ logSize) → Instr

/-- The instruction at address `pc`. -/
noncomputable def Program.fetch (prog : Program) (pc : K) : Option Instr :=
  (Lv42.Semantics.gLog? prog.logSize pc).map prog.code

/-- Execute an instruction on the memory `L`. -/
noncomputable def execute {κ : ℕ} (L : Lv42.Semantics.MemImage κ) (r : Lv42.Semantics.Regs K) :
    Instr → Option (Lv42.Semantics.Regs K) :=
  executeWith L.read r

/-- One step: fetch the instruction at `pc` and execute it. -/
noncomputable def step {κ : ℕ} (prog : Program) (L : Lv42.Semantics.MemImage κ) (r : Lv42.Semantics.Regs K) :
    Option (Lv42.Semantics.Regs K) :=
  prog.fetch r.pc >>= execute L r

/-- The last bytecode slot, `g^(2^logSize − 1)`: reaching it halts the machine. -/
def Program.finalPc (prog : Program) : K := gpow (2 ^ prog.logSize - 1)

/-- The machine halts at `(finalPc, 1)`. -/
def finalRegs (prog : Program) : Lv42.Semantics.Regs K := ⟨prog.finalPc, 1⟩

/-- `n` steps from `r`, halting at `finalPc` (Lv42's `run`: leanVM's executor stops at the last slot, and a valid
execution asks `fp = 1` there). -/
noncomputable def run {κ : ℕ} (prog : Program) (L : Lv42.Semantics.MemImage κ) :
    ℕ → Lv42.Semantics.Regs K → Option (Lv42.Semantics.Regs K)
  | 0, r => some r
  | n + 1, r => if r.pc = prog.finalPc then none else step prog L r >>= run prog L n

/-- An execution: a memory of `2^κ` words and a number of steps. -/
structure Trace (prog : Program) where
  κ : ℕ
  image : Lv42.Semantics.MemImage κ
  steps : ℕ

/-- The memory has between `2^16` and `2^32` words and holds the public input in words `0`, `1` (Lv42's). -/
def HasPublicBoundary {prog : Program} (input : Lv42.Semantics.PublicInput) (t : Trace prog) : Prop :=
  minLogMem ≤ t.κ ∧ t.κ ≤ maxLogMem ∧
    t.image.read (gpow 0) = some input.word0 ∧ t.image.read (gpow 1) = some input.word1

/-- **A valid execution** of `prog` on `input`: the memory holds the public input, and `t.steps` steps from `(1, 1)`
halt at `(finalPc, 1)`. -/
def ValidExecution (prog : Program) (input : Lv42.Semantics.PublicInput) (t : Trace prog) : Prop :=
  HasPublicBoundary input t ∧ run prog t.image t.steps Lv42.Semantics.Regs.initial = some (finalRegs prog)

/-- The last instruction is not a `JUMP` (Lv42's `SentinelSafe`). -/
def SentinelSafe (prog : Program) : Prop :=
  (prog.code ⟨2 ^ prog.logSize - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩).opcode ≠ .jump

/-- The number of instructions of opcode `op` executed in `n` steps from `r`, stepping as `run` does. -/
noncomputable def runCount {κ : ℕ} (prog : Program) (L : Lv42.Semantics.MemImage κ) (op : Opcode) :
    ℕ → Lv42.Semantics.Regs K → ℕ
  | 0, _ => 0
  | n + 1, r =>
    match prog.fetch r.pc, step prog L r with
    | some ins, some r' => (if ins.opcode = op then 1 else 0) + runCount prog L op n r'
    | _, _ => 0

/-- The number of instructions of opcode `op` an execution executes. -/
noncomputable def Trace.count {prog : Program} (t : Trace prog) (op : Opcode) : ℕ :=
  runCount prog t.image op t.steps Lv42.Semantics.Regs.initial

/-! ## The bytecode encoding -/

/-- The bus entry of an instruction, `(opcode, op₁, …, op₇)`: Lv42's for its five, and `SHA3`'s seven operands in
its bytecode flush's order (`layout.rs::flushes_sha3`). -/
def entry : Instr → Vector K 8
  | .sha3 om otail ocap oout => #v[Opcode.sha3.code, om 0, om 1, om 2, om 3, otail, ocap, oout]
  | .xor oA oB oC => Lv42.Arithmetization.entry (.xor oA oB oC)
  | .mulNative oA oB oC => Lv42.Arithmetization.entry (.mulNative oA oB oC)
  | .setConstant o k => Lv42.Arithmetization.entry (.setConstant o k)
  | .deref o1 o2 o3 mode => Lv42.Arithmetization.entry (.deref o1 o2 o3 mode)
  | .jump oc od of => Lv42.Arithmetization.entry (.jump oc od of)

/-- The sixteen slots of an instruction: the entry at slots `3` to `10`, zero elsewhere (Lv42's layout). -/
def encodeSlots (i : Instr) : Vector K 16 :=
  let e := entry i
  #v[0, 0, 0, e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7], 0, 0, 0, 0, 0]

/-! ## A check against SHA3-256 -/

/-- The little-endian lane of eight bytes. -/
def leLane (b : List UInt8) : UInt64 :=
  (List.range 8).foldl (fun acc i ↦ acc ||| ((b.getD i 0).toUInt64 <<< (8 * i).toUInt64)) 0

/-- The state of a final block of at most 128 message bytes before its step: the message and SHA3's suffix `0x06`
in lanes `0..16`, the rest zero (`hash::final_block` without its last byte, which the step supplies). -/
def finalState (msg : List UInt8) : KeccakState :=
  let bytes := (msg ++ [0x06]) ++ List.replicate (128 - msg.length - 1) 0
  Vector.ofFn fun l : Fin 25 ↦ if l.val < 16 then leLane (bytes.drop (8 * l.val)) else 0

end KeccakVm

end
