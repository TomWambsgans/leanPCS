-- Part of this repository. Transcribed from `crates/leanvm_flock_gas/src/layout.rs` (`Form`, `Flushes`, the six
-- tables' columns, flushes and counters, `BLAKE2S_SLOTS`), adapted there from leanVM
-- (https://github.com/leanEthereum/leanVM), commit 42422001, `crates/verifier/src/layout.rs`. MIT OR Apache-2.0;
-- see NOTICE.md.
module

public import UniStatement.TablesBase

/-!
# The six instruction tables (`layout.rs`)

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

/-- `OP_BLAKE2S`. -/
def opBlake2s : ℕ := 5

/-- `BLAKE2S_COLUMNS`: the eighteen value limbs are `q_flock`'s slots (and, here, committed again). -/
def blake2sColumns : List String :=
  ["pc", "fp", "o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md",
    "m0_lo", "m0_hi", "m1_lo", "m1_hi", "m2_lo", "m2_hi", "m3_lo", "m3_hi",
    "out0_lo", "out0_hi", "out1_lo", "out1_hi", "cv0_lo", "cv0_hi", "cv1_lo", "cv1_hi", "md_lo", "md_hi",
    "cnt_m0", "cnt_m1", "cnt_m2", "cnt_m3", "cnt_cv0", "cnt_cv1", "cnt_out0", "cnt_out1", "cnt_md", "cnt_bc"]

/-- `flushes_blake2s()`: the state step, the bytecode read, and the nine cells read, each two limbs and a
zero top: four addressed message chunks, the consecutive chaining-value and output pairs, the metadata. -/
def flushesBlake2s : Flushes :=
  let c := colIdx blake2sColumns
  let (pc, fp, cntBc) := (c "pc", c "fp", c "cnt_bc")
  let operands := ["o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md"].map fun n ↦ col (c n) 0
  let cells : List (String × String × ℕ) :=
    [("m0", "o_0", 0), ("m1", "o_1", 0), ("m2", "o_2", 0), ("m3", "o_3", 0), ("cv0", "o_v", 0),
      ("cv1", "o_v", 1), ("out0", "o_out", 0), ("out1", "o_out", 1), ("md", "o_md", 0)]
  cells.foldl (fun f (cell, operand, exponent) ↦
      f.memoryCols (prod fp (c operand) exponent) (c ("cnt_" ++ cell)) [c (cell ++ "_lo"), c (cell ++ "_hi")])
    ((({ push := [], pull := [] } : Flushes).stateStep pc fp).bytecode pc cntBc opBlake2s operands)

/-- **The six tables** (`tables()`), in opcode order. -/
def tables : List Table :=
  [⟨opXor, arithColumns, flushesArith opXor false⟩, ⟨opMul, arithColumns, flushesArith opMul true⟩,
    ⟨opSet, setColumns, flushesSet⟩, ⟨opDeref, derefColumns, flushesDeref⟩,
    ⟨opJump, jumpColumns, flushesJump⟩, ⟨opBlake2s, blake2sColumns, flushesBlake2s⟩]

/-- `BLAKE2S_SLOTS`: the `BLAKE2S` limb each `q_flock` slot carries; slots 8 and 9 carry none. -/
def blake2sSlots : List (Option String) :=
  [some "cv0_lo", some "cv0_hi", some "cv1_lo", some "cv1_hi", some "out0_lo", some "out0_hi",
    some "out1_lo", some "out1_hi", none, none,
    some "m0_lo", some "m0_hi", some "m1_lo", some "m1_hi", some "m2_lo", some "m2_hi",
    some "m3_lo", some "m3_hi", some "md_lo", some "md_hi"]

/-- `qflock_slot(name)` (`verifier.rs`): the slot of a `BLAKE2S` limb. -/
def qflockSlot (n : String) : Option ℕ := blake2sSlots.findIdx? (· == some n)

/-- `BLAKE2S_R1CS_LOG_SIZE`: one compression is an R1CS of `2^14` positions. -/
def blake2sR1csLogSize : ℕ := 14

end UniStatement

end
