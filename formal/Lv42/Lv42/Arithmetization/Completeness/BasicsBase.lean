/-
  Lv42.Arithmetization.Completeness.BasicsBase

  Adapted from leanerVM (https://github.com/Verified-zkEVM/leanerVM), branch mumbai, commit
  f0393df4, file lean_vm/LeanVM/Arithmetization/Completeness/Basics.lean. MIT OR Apache-2.0; see
  AGENTS.md. `LeanVM` renamed `Lv42`.

  What the completeness witness and the hand-built `SatisfiedBy` witness share: a typed row as a
  raw row, a table's interactions read through its row circuit, and the constraints of the
  components that have none.

  This module is its instruction-set-independent part (shared by the Keccak VM), moved out with
  every name kept; the BLAKE2s-specific rest stays in the module without `Base`, which imports it.
-/

module

public import Lv42.Arithmetization.Boundary
public import Lv42.Arithmetization.Tables.Xor
public import Lv42.Arithmetization.Tables.MulNative
public import Lv42.Arithmetization.Tables.SetConstant
public import Lv42.Arithmetization.Tables.Deref
public import Lv42.Arithmetization.Tables.Jump
public import Clean.Air.FlatEnsemble

@[expose] public section

/-!
# Shared vocabulary of the completeness witness

These are the row-generic facts that the hand-built `SatisfiedBy` witness proves in
`tests/LeanVMTests/Arithmetization/Statement.lean`, moved here so that the construction of the
witness for an arbitrary trace and the hand-built one use the same proofs; the test file imports
them back and its proofs are unchanged.

* `rawRow` writes a typed row as the raw row Clean's tables hold (`toElements`).
* `table_interactions_eq` reads a table's interactions through its row circuit
  (`Component.rowOperations`): the form the kernel evaluates and the form this layer rewrites.
  `Component.operations` reaches them through `instantiate` and `toSubcircuit`, which the kernel
  does not unfold. `rowMessagesOn_eq` is the same for one row.
* `filter_eq_nil_of_rowOps`, `memTable_rowOps` and `bytecodeTable_rowOps`: a table whose row
  circuit has no interaction on a channel sends nothing on it, and the two blocks' interactions
  are their seed push and finalize pull on the row's variables.
* `xor_constraints` and its six siblings: the components with no constraint satisfy their
  constraints on every row, in every environment, since only the `JUMP` table asserts anything
  (`tables.rs:729-736`).

## Wrong readings excluded

* A raw row is the typed row's elements and nothing more: the `JUMP` table's two local
  witnesses are not part of it and are appended by the witness (`Completeness.Messages`).
* The constraints here hold in every environment: a wrong count never breaks them, it breaks
  the bus.
-/

namespace Lv42.Arithmetization

open Lv42.Parameters Lv42.Semantics LeanVM.Parameters
open Air.Flat (Component EnsembleWitness)

/-! ## Raw rows -/

/-- A typed row as a raw row: its elements, in column order. -/
def rawRow {Row : TypeMap} [ProvableType Row] (r : Row K) : Array K := (toElements r).toArray

/-- A raw row has the row type's width. -/
theorem rawRow_size {Row : TypeMap} [ProvableType Row] (r : Row K) :
    (rawRow r).size = size Row :=
  Vector.size_toArray _

/-- The raw rows of a list of typed rows all have the row type's width. -/
theorem rawRows_size {Row : TypeMap} [ProvableType Row] (rs : List (Row K)) :
    ∀ r ∈ rs.map rawRow, r.size = size Row := by
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨_, -, rfl⟩ := hr
  exact rawRow_size _

/-! ## A table's interactions through its row circuit -/

/-- A table's interactions through the row circuit (Clean's `Component.interactions_eq`): the
form the kernel evaluates, `Component.operations` reaching them through `instantiate` and
`toSubcircuit`, which it does not unfold. -/
theorem table_interactions_eq (t : Air.Flat.Table K) :
    t.interactions = t.table.flatMap fun row ↦
      t.component.rowOperations.interactions.map (·.eval (t.environment row)) := by
  simp only [Air.Flat.Table.interactions, Operations.interactionValues, Component.interactions_eq]

/-- The memory block's two interactions, on a row's variables. -/
theorem memTable_rowOps :
    (⟨memTable⟩ : Component K).rowOperations.interactions =
      [⟨MemPush.toRaw, 1, toElements (⟨var ⟨0⟩, 1, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ :
          MemMsg (Expression K)), false⟩,
       ⟨MemPull.toRaw, -1, toElements (⟨var ⟨0⟩, var ⟨1⟩, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ :
          MemMsg (Expression K)), true⟩] := by
  with_unfolding_all rfl

/-- The bytecode block's two interactions, on a row's variables. -/
theorem bytecodeTable_rowOps :
    (⟨bytecodeTable⟩ : Component K).rowOperations.interactions =
      [⟨BytecodePush.toRaw, 1, toElements (⟨var ⟨0⟩, 1, var ⟨2⟩,
          #v[var ⟨3⟩, var ⟨4⟩, var ⟨5⟩, var ⟨6⟩, var ⟨7⟩, var ⟨8⟩, var ⟨9⟩]⟩ :
          BytecodeMsg (Expression K)), false⟩,
       ⟨BytecodePull.toRaw, -1, toElements (⟨var ⟨0⟩, var ⟨1⟩, var ⟨2⟩,
          #v[var ⟨3⟩, var ⟨4⟩, var ⟨5⟩, var ⟨6⟩, var ⟨7⟩, var ⟨8⟩, var ⟨9⟩]⟩ :
          BytecodeMsg (Expression K)), true⟩] := by
  with_unfolding_all rfl

/-- A table whose row circuit interacts on no channel named `c` sends nothing on `c`, whatever
its rows. -/
theorem filter_eq_nil_of_rowOps (t : Air.Flat.Table K) (c : RawChannel K)
    (h : ∀ i ∈ t.component.rowOperations.interactions, i.channel.name ≠ c.name) :
    t.interactions.filter (·.channel.name = c.name) = [] := by
  rw [List.filter_eq_nil_iff, table_interactions_eq]
  intro i hi
  rw [List.mem_flatMap] at hi
  obtain ⟨r, -, hi⟩ := hi
  rw [List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  exact fun h' ↦ h j hj (of_decide_eq_true h')

/-! ## The components with no constraint -/

/-- The `XOR` table asserts nothing: its constraints hold in every environment. -/
theorem xor_constraints (env : Environment K) :
    (⟨xorTable⟩ : Component K).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, xorTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The `MUL_NATIVE` table asserts nothing. -/
theorem mul_constraints (env : Environment K) :
    (⟨mulTable⟩ : Component K).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, mulTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The `SET_CONSTANT` table asserts nothing. -/
theorem set_constraints (env : Environment K) :
    (⟨setTable⟩ : Component K).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, setTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The `DEREF` table asserts nothing. -/
theorem deref_constraints (env : Environment K) :
    (⟨derefTable⟩ : Component K).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, derefTable, memRead, bytecodeRead, -BitVec.reduceNeg]

/-- The memory block asserts nothing. -/
theorem mem_constraints (env : Environment K) :
    (⟨memTable⟩ : Component K).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, memTable, -BitVec.reduceNeg]

/-- The bytecode block asserts nothing. -/
theorem bytecode_constraints (env : Environment K) :
    (⟨bytecodeTable⟩ : Component K).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, bytecodeTable, -BitVec.reduceNeg]

/-- The verifier asserts nothing, for any program. -/
theorem verifier_constraints (prog : Program) (env : Environment K) :
    (⟨leanIsaVerifier prog⟩ : Component K).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, leanIsaVerifier, -BitVec.reduceNeg]

/-! ### Moved from `Completeness/Satisfied` (the shared `JUMP` table) -/

/-- The `JUMP` row circuit's constraints, generically: they are exactly the two residuals of the
local witnesses `w` and `b`, at slots `n` and `n + 1`. -/
theorem jump_constraints_iff (x : Var JumpRow K) (env : Environment K) (n : ℕ) (r : JumpRow K)
    (hx : eval env x = r) (w b : K) (hw : env.get n = w) (hb : env.get (n + 1) = b) :
    ((jumpTable.main x).operations n).ConstraintsHold env ↔
      b + r.vcond * w = 0 ∧ r.vcond * (b + 1) = 0 := by
  subst hx
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := x
  dsimp only [jumpTable]
  simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
  constructor
  · intro h
    have h1 := h _ (Or.inl rfl)
    have h2 := h _ (Or.inr rfl)
    simp only [Expression.eval, hw, hb] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ e (rfl | rfl)
    · simp only [Expression.eval, hw, hb, h1]
    · simp only [Expression.eval, hb, h2]

end Lv42.Arithmetization
