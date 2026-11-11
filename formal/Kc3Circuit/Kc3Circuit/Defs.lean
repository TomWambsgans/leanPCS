/-
Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
Adapted from this repository's `formal/Circuit/Circuit/Defs.lean` (F0b of commit `f96a7938`'s circuit, the gate
`V = X + C + Y·C`) to the deployed circuit (`docs/membership/PROTOCOL.md`: the gate `V = Y + C + X·C`, the constant
`3` and free cells as sources, `11` anchor rows). The Keccak constants, the statement (`PcsCircuit.Secret`, `H`) and
the bit layouts are `formal/Circuit`'s, imported (`PcsCircuit.Builder.piInv`, `PcsCircuit.rho`, `PcsCircuit.Secret`).
-/
import Circuit.Bytes

/-!
# The membership circuit's builder, in the form the proofs read

A second transcription of `quotient::circuit::Builder` (`crates/membership/quotient/src/circuit.rs`), next to the
Statement's (`formal/Statement/PcsQuotient/Circuit.lean`): the same rows in the same order, its loops written as
`mapM` over `List.range` (the Statement's as `for` loops filling arrays). `Sim.lean`, `Loops.lean`, `Keccak.lean`,
`Build.lean` prove the two make the same rows; `Semantics.lean`, `KeccakGadget.lean`, `Membership.lean` prove what
these rows compute.

The sources are the Statement's five (`zero`, `one`, `three`, `row r`, `free`); the builder before `finish` reads
only `zero`, `one` and rows. A row `(X, Y, C)` computes `Y ⊕ (C ∧ ¬X)` on bits: a NOT is `(0, 1, a)`, an XOR
`(0, a, b)`, a χ `a ⊕ (¬b ∧ c)` the row `(b, a, c)`. The builder starts with the `11` anchor rows, idle until
`finish`.
-/

namespace Kc3Circuit

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol

/-! ## Rows -/

/-- What a cell reads (`circuit::Src`): a constant, row `r`'s `V` cell, or nothing (a free cell). -/
inductive Src where
  | zero
  | one
  | three
  | row (r : Nat)
  | free
  deriving DecidableEq, Repr, Inhabited

/-- One gate, `V = Y + C + X·C`, by what its three input cells read (`circuit::Row`). -/
structure Row where
  x : Src
  y : Src
  c : Src
  deriving DecidableEq, Repr, Inhabited

/-- A row reading zeros (`IDLE`). -/
def Row.idle : Row := ⟨.zero, .zero, .zero⟩

/-- The anchor rows (`PUBLIC_ROWS`): the builder's first rows, idle until `finish`. -/
def publicRows : Nat := 11

/-- The gate on bits: `y ⊕ (c ∧ ¬x)` (`gate_bits`). -/
def gateBits (x y c : Bool) : Bool := y ^^ (c && !x)

/-! ## The builder -/

/-- The rows made so far, the `11` anchor rows first (idle until `finish`), and the rows that are free input
bits, in the order they were made (`circuit::Builder`). -/
structure Builder where
  rows : Array Row
  inputs : Array Nat

/-- `Builder::new`: the anchor rows, idle. -/
def Builder.new : Builder := { rows := Array.replicate publicRows Row.idle, inputs := #[] }

/-- The builder's monad: a state of rows. -/
abbrev BuildM := StateM Builder

namespace Builder

/-- `Builder::row`: a new row, read as its output. -/
def row (x y c : Src) : BuildM Src :=
  modifyGet fun b => (.row b.rows.size, { b with rows := b.rows.push ⟨x, y, c⟩ })

/-- `Builder::input`: a free bit, a row reading its own output three times. -/
def input : BuildM Src :=
  modifyGet fun b =>
    let here := Src.row b.rows.size
    (here, { rows := b.rows.push ⟨here, here, here⟩, inputs := b.inputs.push b.rows.size })

/-- `Builder::not`: `¬a`, folded on constants; otherwise the row `(0, 1, a)`. -/
def notG : Src → BuildM Src
  | .zero => pure .one
  | .one => pure .zero
  | a => row .zero .one a

/-- `Builder::xor`: `a ⊕ b`, folded when either is a constant; otherwise the row `(0, a, b)`. The match arms
are the Rust's, tried in the same order. -/
def xorG : Src → Src → BuildM Src
  | .zero, v => pure v
  | v, .zero => pure v
  | .one, v => notG v
  | v, .one => notG v
  | a, b => row .zero a b

/-- `Builder::chi`: `a ⊕ (¬b ∧ c)`, Keccak's χ, in one row `(b, a, c)` unless a constant makes it cheaper. -/
def chiG (a b c : Src) : BuildM Src :=
  match b, c with
  | .one, _ => pure a
  | _, .zero => pure a
  | .zero, _ => xorG a c
  | _, .one => do
    let notB ← notG b
    xorG a notB
  | _, _ => row b a c

/-! ## Keccak-f[1600] -/

/-- A Keccak state of wires: lane `i = x + 5y`, bit `z` at index `64 i + z`. -/
abbrev State := Array Src

/-- Bit `z` of lane `i`. -/
def State.get (a : State) (i z : Nat) : Src := a.getD (64 * i + z) .zero

/-- θ: the column parities (`c`, each a chain of four XORs), their mixes (`d`), then each lane XORed with its
column's mix; the loops in the Rust's order (`x`, then `z`, then `y`). -/
def theta (a : State) : BuildM State := do
  let c ← (List.range 320).mapM fun k =>
    [1, 2, 3, 4].foldlM (fun acc y => xorG acc (a.get (k / 64 + 5 * y) (k % 64))) (a.get (k / 64) (k % 64))
  let c := c.toArray
  let d ← (List.range 320).mapM fun k =>
    xorG (State.get c ((k / 64 + 4) % 5) (k % 64)) (State.get c ((k / 64 + 1) % 5) ((k % 64 + 63) % 64))
  let d := d.toArray
  let a ← (List.range 1600).mapM fun k => xorG (a.get (k / 64) (k % 64)) (State.get d (k / 64 % 5) (k % 64))
  pure a.toArray

/-- ρ and π, wiring only: lane `j` bit `z` reads lane `piInv j` bit `z - rho (piInv j)` (mod `64`). -/
def rhoPi (a : State) : State :=
  ((List.range 1600).map fun k =>
    a.get (PcsCircuit.Builder.piInv (k / 64)) ((k % 64 + 64 - PcsCircuit.Builder.rho (PcsCircuit.Builder.piInv (k / 64))) % 64)).toArray

/-- χ: one row a bit, in the Rust's order (`y`, then `x`, then `z`, that is `64 i + z`). -/
def chiStep (b : State) : BuildM State := do
  let a ← (List.range 1600).mapM fun k =>
    chiG (b.get (k / 64) (k % 64)) (b.get ((k / 64 % 5 + 1) % 5 + 5 * (k / 64 / 5)) (k % 64))
      (b.get ((k / 64 % 5 + 2) % 5 + 5 * (k / 64 / 5)) (k % 64))
  pure a.toArray

/-- ι: a NOT where the round constant has a one, lane `0` only. -/
def iota (a : State) (rc : UInt64) : BuildM State := do
  let lane ← (List.range 64).mapM fun z =>
    if rc.toNat.testBit z then notG (a.get 0 z) else pure (a.get 0 z)
  let lane := lane.toArray
  pure ((List.range 1600).map fun k => if k < 64 then lane.getD k .zero else a.getD k .zero).toArray

/-- One round: θ, ρ and π, χ, ι. -/
def round (a : State) (rc : UInt64) : BuildM State := do
  let a ← theta a
  let b := rhoPi a
  let a ← chiStep b
  iota a rc

/-- `Builder::keccak_f`: Keccak-f[1600], the `24` rounds of leanerVM's `keccakRC`. -/
def keccakF (a : State) : BuildM State := keccakRC.foldlM round a

/-- `Builder::keccak256_64`: Keccak-256 of a 64-byte block, its `512` bits in byte order and low bit first;
Keccak's padding of a 64-byte message in one block; the digest's `256` bits likewise. -/
def keccak256Block (message : Array Src) : BuildM (Array Src) := do
  let state : State := ((List.range 1600).map fun k =>
    if k < 512 then message.getD k .zero
    else if k = 64 * 8 then .one
    else if k = 64 * 16 + 63 then .one
    else .zero).toArray
  let out ← keccakF state
  pure ((List.range 256).map fun k => out.getD k .zero).toArray

/-- `n` free bits. -/
def freeBits (n : Nat) : BuildM (Array Src) := do
  let l ← (List.range n).mapM fun _ => input
  pure l.toArray

end Builder

/-! ## The membership statement -/

open Builder

/-- `constant_block`: `32` copies of a byte, as `256` constant wires, low bit first. -/
def constantBlock (byte : UInt8) : Array Src :=
  ((List.range 256).map fun i => if byte.toNat.testBit (i % 8) then Src.one else Src.zero).toArray

/-- One level of the path: the sibling's `256` bits and the direction bit as inputs, the ordered pair by a swap
(`keep = ¬direction`, `left = χ(node, keep, differ) = node ⊕ (direction ∧ differ)`, `right = left ⊕ differ`,
`differ = node ⊕ sibling`), then its hash. -/
def level (node : Array Src) : BuildM (Array Src) := do
  let sibling ← freeBits 256
  let direction ← input
  let keep ← notG direction
  let lr ← (List.range 256).mapM fun i => do
    let differ ← xorG (node.getD i .zero) (sibling.getD i .zero)
    let l ← chiG (node.getD i .zero) keep differ
    let r ← xorG l differ
    pure (l, r)
  keccak256Block ((lr.map Prod.fst).toArray ++ (lr.map Prod.snd).toArray)

/-- The rows of `membership` before `finish`: `x`, `y = H(x ‖ 0x11^32)`, the leaf `H(x ‖ 0x22^32)`, the `32`
levels; the result is `(y, root)`. -/
def membershipBuild : BuildM (Array Src × Array Src) := do
  let x ← freeBits 256
  let y ← keccak256Block (x ++ constantBlock PcsCircuit.yPad)
  let leaf ← keccak256Block (x ++ constantBlock PcsCircuit.leafPad)
  let root ← (List.range PcsCircuit.depth).foldlM (fun node _ => level node) leaf
  pure (y, root)

/-- Run a builder program from a builder: its result and the grown builder. -/
def runBuild {α : Type} (m : BuildM α) (b : Builder) : α × Builder := (m.run b).run

end Kc3Circuit
