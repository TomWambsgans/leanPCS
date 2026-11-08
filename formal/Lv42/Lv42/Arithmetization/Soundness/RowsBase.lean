/-
  Lv42.Arithmetization.Soundness.RowsBase

  Adapted from leanerVM (https://github.com/Verified-zkEVM/leanerVM), branch mumbai, commit
  f0393df4, file lean_vm/LeanVM/Arithmetization/Soundness/Rows.lean. MIT OR Apache-2.0; see
  AGENTS.md. `LeanVM` renamed `Lv42`.

  What an arbitrary row of each of the six opcode tables sends, in the shape every table shares,
  and what the table's soundness makes of it: under the guarantees of its pulls, the row is a step
  of the machine from its pulled state to its pushed state.

  This module is its instruction-set-independent part (shared by the Keccak VM), moved out with
  every name kept; the BLAKE2s-specific rest stays in the module without `Base`, which imports it.
-/

module

public import Lv42.Arithmetization.Completeness.RowsBase

@[expose] public section

/-!
# The rows of a satisfying witness

At leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d` and Clean pin `42fe4b26`. Specification
§7 (the six AIRs, `doc/leanvm/body/07-*`) and §6 (their bus interactions): the per-row soundness
of the six opcode tables, from the tables of `Arithmetization.Tables` and their Clean soundness
theorems; the bus is `Soundness.Bus`'s.

**The shape of a row** (`OpRow`). A raw row of a witness is an arbitrary array, read by its
component as the typed row `rowInput` (the first cells, a missing cell `0`). Whatever its cells,
the row circuit of each opcode table sends the messages `sendsOf pc fp next rbc e reads` of
`Completeness.Rows`: the state pull `(pc, fp)` and push `next`, the bytecode pull and push of the
eight coordinates `e` at `pc`, and per memory read a pull of `(addr, count, v)` and a push of
`(addr, g·count, v)`, at most nine reads (`BLAKE2S`). The memory and bytecode pairs need nothing
more of the rows than this shape (`Soundness.MemChannel`, `Soundness.BytecodeChannel`).

**The step** (also `OpRow`). Under the table's `Assumptions` (the compression, for `BLAKE2S`), its
constraints (the `JUMP` residuals), and the guarantees of its pulls (that the memory reads are the
image's words and the bytecode entry decodes, which `Soundness.MemChannel` and
`Soundness.BytecodeChannel` derive from the bus), Clean's instantiated soundness theorem
(`Component.weakSoundness`) gives the table's `Spec`: the row refines the table's relation, so some
instruction `ins` with `entry ins = e` executes from `(pc, fp)` to `next` (`execute`), and
to the fall-through `(g·pc, fp)` unless it is a `JUMP`. The pushed successor is the table's output,
which for `JUMP` reads the indicator, the row's second local witness (`jump_output_gen`).

**The guarantees** (`ChannelOk`). Of the six channels only the memory pull and the bytecode pull
carry a guarantee; every interaction a table emits is on one of the six (`*_channelOk`), so the
guarantees of a row are those of its memory and bytecode pulls.

**Without the compression** (`OpRow`'s last clause). Under its constraints and the guarantees
alone a row is a step of the Flock-blind semantics `blakeFree` (`Lv42.Spec.IsaWith`), whose
`BLAKE2S` asks only canonical cells: a `BLAKE2S` row is bound to the image by the table's circuit
without its assumption (`blake2sTableFree`), and its cells, two limbs each, are canonical
(`blake2s_free_exec`); every other table assumes nothing, and a deployed step is a Flock-blind one
(`executeWithB_free_of_executeWith`).

## Wrong readings excluded

* A row is not assumed to be a typed row written by an honest prover: the shape holds for every
  array, the step only under the guarantees, which the bus supplies.
* The table does not know which instruction the program holds at `pc`: `e = entry ins` names the
  instruction the row's own columns encode, and that it is the program's is the bytecode pair's
  (`Soundness.BytecodeChannel`).
* The `JUMP` successor is not read from the row's columns alone: it is the output, a function of
  the indicator, forced by the residuals (`flags_sound`) inside the table's soundness.
-/

namespace Lv42.Arithmetization

open Lv42.Parameters Lv42.Semantics LeanVM.Parameters
open Air.Flat (Component)

/-! ## The shape of a row -/

/-- The parameters of what an opcode-table row sends (`sendsOf`): the pulled state, the pushed
successor, the bytecode count and coordinates, and the memory reads. -/
structure RowRec where
  /-- The pulled program counter. -/
  pc : K
  /-- The pulled frame pointer. -/
  fp : K
  /-- The pushed successor. -/
  next : Regs K
  /-- The bytecode read count. -/
  rbc : K
  /-- The bytecode coordinates `(opcode, op₁, …, op₇)`. -/
  e : Vector K 8
  /-- The memory reads `(addr, count, limbs)`. -/
  reads : List (K × K × Vector K 3)

/-- A record exists. -/
instance : Inhabited RowRec := ⟨⟨0, 0, ⟨0, 0⟩, 0, 0, []⟩⟩

/-- What a row with these parameters sends. -/
def RowRec.sends (x : RowRec) : List (String × Array K) :=
  sendsOf x.pc x.fp x.next x.rbc x.e x.reads

/-- The pulled state of a record. -/
def RowRec.src (x : RowRec) : Regs K := ⟨x.pc, x.fp⟩

/-- The output of the `JUMP` row circuit at a row variable that evaluates to `r`: the successor
selected by the indicator `b`, the local witness at slot `n + 1`. -/
theorem jump_output_gen (x : Var JumpRow K) (env : Environment K) (n : ℕ) (r : JumpRow K)
    (hx : eval env x = r) (b : K) (hb : env.get (n + 1) = b) :
    eval env ((jumpTable.main x).output n) =
      (⟨b * r.vpc + b * (g * r.pc) + g * r.pc, b * r.vfp + b * r.fp + r.fp⟩ : Regs K) := by
  subst hx
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := x
  dsimp only [jumpTable]
  simp only [circuit_norm, memRead, bytecodeRead, hb, -BitVec.reduceNeg]

/-- A channel whose guarantee a row may need: the memory pull, the bytecode pull, or a channel
guaranteeing nothing. -/
def ChannelOk (ch : RawChannel K) : Prop :=
  ch = MemPull.toRaw ∨ ch = BytecodePull.toRaw ∨ ∀ mult msg data, ch.Guarantees mult msg data

-- Each of the six channels is `ChannelOk`: the two lookup pulls by name, the others since their
-- guarantee is `True` at every multiplicity.
private theorem channelOk_memPull : ChannelOk MemPull.toRaw := Or.inl rfl
private theorem channelOk_bytecodePull : ChannelOk BytecodePull.toRaw := Or.inr (Or.inl rfl)
private theorem channelOk_statePull : ChannelOk StatePull.toRaw :=
  Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
private theorem channelOk_statePush : ChannelOk StatePush.toRaw :=
  Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
private theorem channelOk_memPush : ChannelOk MemPush.toRaw :=
  Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
private theorem channelOk_bytecodePush : ChannelOk BytecodePush.toRaw :=
  Or.inr (Or.inr fun _ _ _ _ ↦ trivial)

/-- Every interaction of the `XOR` table is on one of the six channels. -/
theorem xor_channelOk : ∀ a ∈ (⟨xorTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, xorTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `MUL_NATIVE` table is on one of the six channels. -/
theorem mul_channelOk : ∀ a ∈ (⟨mulTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, mulTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `SET_CONSTANT` table is on one of the six channels. -/
theorem set_channelOk : ∀ a ∈ (⟨setTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, setTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `DEREF` table is on one of the six channels. -/
theorem deref_channelOk : ∀ a ∈ (⟨derefTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, derefTable, memRead, bytecodeRead,
    -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

/-- Every interaction of the `JUMP` table is on one of the six channels. -/
theorem jump_channelOk : ∀ a ∈ (⟨jumpTable⟩ : Component K).operations.interactions,
    ChannelOk a.channel := by
  rw [Component.interactions_eq]
  dsimp only [Component.rowOperations_mk, jumpTable]
  simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, channelOk_memPull,
    channelOk_bytecodePull, channelOk_statePull, channelOk_statePush, channelOk_memPush,
    channelOk_bytecodePush, and_self]

end Lv42.Arithmetization
