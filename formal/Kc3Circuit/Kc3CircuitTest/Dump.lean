-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/Circuit/CircuitTest/Dump.lean` (commit `f96a7938`), for the deployed circuit.
import PcsQuotient.Circuit
import PcsQuotient.Relation
import PcsQuotient.Reduction

/-!
# The differential test of the deployed circuit against the Rust's

`lake exe kc3-dump-circuit OUT` writes `PcsQuotient.membership 22`, the circuit `Kc3Circuit` proves its theorems
about, in the format of `crates/membership/quotient/examples/dump_circuit.rs` (little-endian `u32`s: the number of
rows, the rows used, the number of inputs; each row's `X, Y, C` sources, `0` zero, `1` one, `2` three, `3` free,
`4 + r` row `r`; the input rows; σ), and prints the anchors' `C` cells that `Circuit.cells` computes for the Rust
example's secret next to the statement's words. The two files must have the same SHA-256, and the words must agree
with each other and with the Rust's. Not part of the proofs.
-/

open PcsQuotient

/-- Append a little-endian `u32`. -/
def pushU32 (b : ByteArray) (x : Nat) : ByteArray :=
  let x := x.toUInt32
  ((b.push x.toUInt8).push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8).push (x >>> 24).toUInt8

/-- A source as the Rust example codes it. -/
def srcCode : Src → Nat
  | .zero => 0
  | .one => 1
  | .three => 2
  | .free => 3
  | .row r => r + 4

/-- A number as `16` hexadecimal digits. -/
def hex16 (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: kc3-dump-circuit OUT")
  let c := membership 22
  IO.println s!"rows {c.rows.size} used {c.usedRows} inputs {c.inputs.size} sigma {c.sigma.size}"
  let mut buf := ByteArray.emptyWithCapacity (4 * (3 + 3 * c.rows.size + c.inputs.size + c.sigma.size))
  buf := pushU32 buf c.rows.size
  buf := pushU32 buf c.usedRows
  buf := pushU32 buf c.inputs.size
  for row in c.rows do
    buf := pushU32 (pushU32 (pushU32 buf (srcCode row.x)) (srcCode row.y)) (srcCode row.c)
  for r in c.inputs do
    buf := pushU32 buf r
  for s in c.sigma do
    buf := pushU32 buf s
  IO.FS.writeBinFile path buf
  -- The secret of the Rust example.
  let dirs : UInt32 := 0xA5C31E77
  let w : Secret := {
    x := Vector.ofFn fun i : Fin 32 => (i.val * 37 + 11).toUInt8
    siblings := Vector.ofFn fun l : Fin depth => Vector.ofFn fun i : Fin 32 => (l.val * 101 + i.val * 13 + 5).toUInt8
    directions := Vector.ofFn fun i : Fin depth => (dirs >>> i.val.toUInt32) &&& 1 = 1 }
  let cells := c.cells (membershipInputs w)
  let words := w.statement.words
  for k in List.range publicWords do
    IO.println s!"word {k}: circuit {hex16 (cells.getD (4 * k + 2) 0).lane.toNat} statement {hex16 (words.getD k 0).lane.toNat}"
