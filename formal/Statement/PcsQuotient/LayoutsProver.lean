-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The previous protocol's opening prover (version 2, hidden layouts), kept for the leanVM line, whose PIOPs open
-- their tables with it; the membership prover no longer uses it. Transcribed from
-- `crates/membership/quotient/src/opening.rs` before the EIP's PCS claims. The WHIR opening's prover is leanerVM's
-- (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Prover/Whir.lean`'s `levelsA`, `roundA`,
-- `stackTableA`, `eqKernelA`, run by `Statement/Prover/Run.lean`'s `runFrom`).
module

public import PcsQuotient.Verifier
public import PcsQuotient.Circuit
public import Statement.Prover.Whir

/-!
# The previous opening's prover (layouts), kept for the leanVM line

Stacks of tables in their layouts (`Layout.stackOf`, with the hidden layouts' padding), a claim's weight on a stack
(`Layout.weightAt`), the weight table of an opening (`weightTable`), the WHIR opening as a script (`openingScript`)
and an opening proof (`proveOpeningWith`): the previous membership protocol's, which the leanVM line's PIOPs use
for their public layouts. The membership prover (`Prover.lean`) opens PCS claims instead.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient.Domain PcsQuotient.Transcript

/-! ### Tables as stacks -/

/-- **A table's padding**: for each lane `l`, the words of its randomness `pad l 0, pad l 1, …`, in the order a
hidden stack takes them (`Table::hidden`: the Rust draws them from the lane's generator, ChaCha12 keyed by
Keccak-256 of the table's seed and the lane; the honest prover of the statement takes them uniform). -/
abbrev Padding : Type := ℕ → ℕ → K


/-- **The gadget's entries cancelled** (`Table::hidden`, `opening.rs`): at each of the nine entries, the second
lane of a pair takes the first's value and the overflow lane's is zero, so the gadget weighs nothing on the
stack (characteristic two). The entries are first-piece entries: no claim weighs them. -/
def Layout.cancelGadget (L : Layout) (stack : Array K) : Array K :=
  let lane := 2 ^ L.logLane
  (List.range 3).foldl (fun st g ↦ (List.range 3).foldl (fun st i ↦
    let y := L.gadgetEntry g i
    match gadgetLanes g with
    | [a, b] => st.setIfInBounds (b * lane + y) (st.getD (a * lane + y) 0)
    | [a] => st.setIfInBounds (a * lane + y) 0
    | _ => st) st) stack

/-- **The stack of a table** whose entry `i` is `entry i` (`Table::new`, `Table::hidden`, `opening.rs`). Public
layout: lane `l` holds block `b` whole. Hidden layout, pieces of `2^s`: every lane's first piece is padding; a
block lane then holds its block's pieces `1, 2, …`; the overflow lane its held pieces, then padding (its stream
continuing); a random lane padding; and the gadget's entries are cancelled (`cancelGadget`). -/
def Layout.stackOf (L : Layout) (entry : ℕ → K) (pad : Padding) : Array K :=
  let lane := 2 ^ L.logLane
  let kinds := L.lanes.toArray
  match L.logPiece with
  | none => Array.ofFn (n := kinds.size * lane) fun p ↦
    match kinds.getD (p.val / lane) .random with
    | .block b => entry (b * lane + p.val % lane)
    | _ => 0
  | some s =>
    let piece := 2 ^ s
    let pieces := L.pieces.toArray
    let held := pieces.size
    L.cancelGadget <| Array.ofFn (n := kinds.size * lane) fun p ↦
      let (l, i) := (p.val / lane, p.val % lane)
      if i < piece then pad l i
      else
        match kinds.getD l .random with
        | .block b => entry (b * lane + i)
        | .overflow =>
          if i < (held + 1) * piece then entry (pieces.getD (i / piece - 1) 0 * piece + i % piece)
          else pad l (i - held * piece)
        | .random => pad l i

/-- A claim's weight on a stack, tabulated once (`Layout::tensors`, `opening.rs`): the layout's lanes and
piece (as arrays: one lookup a position), the claim's lane and piece scales (`Layout.scales`), and the `eq`
tables of its lane coordinates and of its coordinates below a piece. -/
structure ClaimWeights where
  kinds : Array Lane
  logPiece : Option ℕ
  lanes : Array E
  pieces : Array E
  low : Array E
  pieceLow : Array E

/-- The tables of a claim's weight on `L`. -/
def Layout.claimWeights (L : Layout) (c : Claim) : ClaimWeights :=
  ⟨L.lanes.toArray, L.logPiece, (L.scales c.point).1.toArray, (L.scales c.point).2.toArray,
    eqKernelA (c.point.take L.logLane), eqKernelA (c.point.take (L.logPiece.getD 0))⟩

/-- **A claim's weight at entry `y` of lane `l`** (`Layout::weight_at`, `opening.rs`), from its tables
(`Layout.claimWeights L c`): public layout, its lane scale times its `eq` at `y`; hidden layout, zero on a
first piece; on a block lane, its lane scale times its `eq` at `y`; on the overflow lane, the held piece's scale
times its `eq` below the piece; zero on a random lane. -/
def Layout.weightAt (_L : Layout) (w : ClaimWeights) (l y : ℕ) : E :=
  match w.logPiece with
  | none => w.lanes.getD l 0 * w.low.getD y 0
  | some s =>
    let piece := y >>> s
    if piece = 0 then 0
    else
      match w.kinds.getD l .random with
      | .block _ => w.lanes.getD l 0 * w.low.getD y 0
      | .overflow => w.pieces.getD (piece - 1) 0 * w.pieceLow.getD (y % 2 ^ s) 0
      | .random => 0

/-- **The gadget's weight at entry `y` of lane `l`** (`Layout::gadget_at`, `opening.rs`): `β_i` at entry `i`
of pattern `g` on its lanes, zero elsewhere and in a public layout. -/
def Layout.gadgetAt (L : Layout) (l y : ℕ) : E :=
  match L.logPiece with
  | none => 0
  | some s =>
    if 2 ^ s - gadgetSize ≤ y ∧ y < 2 ^ s ∧ (gadgetLanes ((y + gadgetSize - 2 ^ s) / 3)).contains l
    then gadgetBeta ((y + gadgetSize - 2 ^ s) % 3) else 0
/-- Limb `l` of an element of `E`. -/
def limbOf (x : E) (l : ℕ) : K := LeanVM.Prover.limbAt x l

/-! ### The WHIR opening -/


/-- **The weight table of the batched claims** in WHIR's variable order: entry `i` is the stack position
`⌊i / 64⌋ + 2^(logN−6)·(i mod 64)`, entry `⌊i / 64⌋` of lane `i mod 64`, where each claim weighs
`Layout.weightAt`, and in a hidden layout the gadget `Layout.gadgetAt` with the scale after the claims'
(`open`, `Layout::weight`, `opening.rs`). -/
def weightTable (L : Layout) (scales : List E) (claims : List Claim) : Array E :=
  let parts := (claims.zip scales).map fun (c, s) ↦ (L.claimWeights c, s)
  let gadgetScale := scales.getD claims.length 0
  Array.ofFn (n := 2 ^ L.logN) fun i ↦
    parts.foldl (fun acc (w, s) ↦ acc + s * L.weightAt w (i.val % 64) (i.val / 64))
      (gadgetScale * L.gadgetAt (i.val % 64) (i.val / 64))

/-- **The honest WHIR opening** of `claims` on the stack `stack`, as a script of the prover's moves
(mumbai's `openingFast` with this weight table): receive the batching challenge, then run the levels
from the batched claim (the claims, and the gadget of value zero in a hidden layout: `stackClaims`) with the
stack table and the weight table. -/
def openingScript (L : Layout) (stack : Array K) (claims : List Claim) : Script Unit := do
  let c ← Script.sampleE
  let scales := powers c (stackClaims L claims).length
  match Whir.ladder L.logN logInvRate with
  | none => return ()
  | some config =>
    let f₀ := stackTableA L.logN stack
    let W₀ := weightTable L scales claims
    let target := dot scales ((stackClaims L claims).map (·.2))
    let quad ← roundA target W₀ f₀
    levelsA L.logN 0 config ⟨quad, [], []⟩ W₀ f₀

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **An opening proof** of `claims` on the table committed by `tree` (its stack `stack`): the root's two
halves sent first (`ProverState::add_root`), then the script run against the verifier's program from the
opening's sponge, with the table's tree as commitment `0`; `none` if a proof of work finds no nonce below
`fuel`. -/
def proveOpeningWith (fuel : ℕ) (L : Layout) (tree : Tree) (stack : Array K) (claims : List Claim) :
    m (Option Compile.Proof) := do
  let (r0, r1) := digestScalars tree.root
  let sp ← openingSpongeWith F L claims
  let sp ← absorb F sp r0 dsObserve
  let sp ← absorb F sp r1 dsObserve
  let program := verifyStackedOpening L.logN logInvRate
    (stackClaims L claims)
  let r ← runFrom F fuel program (some (openingScript L stack claims)) sp [tree]
  return r.map fun t ↦ ⟨r0 :: r1 :: t.1, t.2⟩

end With

/-- The witness table's stack: the cells' coefficients `wHat`, then the masks, hidden with `pad`. -/
def witnessStack (logRows : ℕ) (wHat mask : Array K) (pad : Padding) : Array K :=
  let n := 2 ^ cellVars logRows
  (witnessLayout logRows).stackOf (fun i ↦ if i < n then wHat.getD i 0 else mask.getD (i - n) 0) pad

/-- **The quotient table's stack** (`prove`, `protocol.rs`), hidden with `pad`: chunk `c` of `2^m` entries
holds limb `⌊c / 16⌋` of `h` (`c mod 16 = 0`) or of `q` (`c mod 16 ∈ 4 … 7`, its digit `c mod 4`), or the
gate's quotient (`c ∈ {8, 9}`, its digit `c mod 4`). -/
def quotientStack (logRows : ℕ) (hHat qHat : Array E) (qGateHat : Array K) (pad : Padding) :
    Array K :=
  let n := 2 ^ cellVars logRows
  (quotientLayout logRows).stackOf (pad := pad) fun i ↦
    let c := i / n
    let src := c % 4 * n + i % n
    if c &&& 12 = 0 then limbOf (hHat.getD src 0) (c / 16)
    else if c &&& 12 = 4 then limbOf (qHat.getD src 0) (c / 16)
    else qGateHat.getD src 0

end PcsQuotient

end
