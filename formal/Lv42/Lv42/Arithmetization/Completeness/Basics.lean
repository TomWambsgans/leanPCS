/-
  Lv42.Arithmetization.Completeness.Basics

  Adapted from leanerVM (https://github.com/Verified-zkEVM/leanerVM), branch mumbai, commit
  f0393df4, file lean_vm/LeanVM/Arithmetization/Completeness/Basics.lean. MIT OR Apache-2.0; see
  AGENTS.md. `LeanVM` renamed `Lv42`.

  What the completeness witness and the hand-built `SatisfiedBy` witness share: a typed row as a
  raw row, a table's interactions read through its row circuit, and the constraints of the
  components that have none.
-/

module

public import Lv42.Arithmetization.Completeness.BasicsBase
public import Lv42.Arithmetization.Statement

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

/-- A row's messages on a channel, through the row circuit. -/
theorem rowMessagesOn_eq (t : Air.Flat.Table K) (r : Array K) (c : RawChannel K) :
    rowMessagesOn t r c =
      ((t.component.rowOperations.interactions.map (·.eval (t.environment r))).filter
        (·.channel.name = c.name)).map (·.msg) := by
  rw [rowMessagesOn, Operations.interactionValues, Component.interactions_eq]

/-- The `BLAKE2S` table asserts nothing: the compression is Flock's (`Blake2sRowsValid`). -/
theorem blake2s_constraints (env : Environment K) :
    (⟨blake2sTable⟩ : Component K).operations.ConstraintsHold env := by
  rw [Component.constraintsHold_iff]
  simp only [circuit_norm, blake2sTable, memRead, bytecodeRead, -BitVec.reduceNeg]

end Lv42.Arithmetization
