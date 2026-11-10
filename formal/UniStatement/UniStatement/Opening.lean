-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Claims are `crates/membership/evm/src/machine.rs`'s
-- (as `crates/leanvm/statement/src/evm/machine.rs` declares them), its layout words and the contract's IV
-- `crates/leanvm/univariate/src/contract.rs`'s (`layout_word`, `layout_words`, `shape_bytes`, `contract_iv`,
-- `SetupRoots`); its semantics is this repository's `formal/Statement` opening (`PcsQuotient.openingWith`:
-- leanerVM `mumbai` 6175f1a0's WHIR verifier, MIT OR Apache-2.0).
module

public import UniStatement.Run
public import PcsQuotient.Opening
public import Common.Lanes

/-!
# The claims' opening, the layout words and the contract's IV: the shared pieces

**A declared claim** (`machine.rs`'s encoding: a root, a layout word, `k` point claims, each `v` coordinates and a
value): "the block's openings hold exactly these claims on that commitment under that layout". As in
`formal/Statement` (`formal/EndToEnd/Evm`'s `pcsOpen`), its meaning here is **the Statement's opening**,
`PcsQuotient.openingWith` (leanVM's WHIR verifier, mumbai's `verifyStackedOpening`, seeded as
`opening.rs` seeds it), on the claim's opening proof, for the **plain layout** of a stack of `2^vars`
words (`plainLayout`: lane `l` holds block `l`, so a claim's weight on the stack is `eq(point, ·)`: a point
claim on the stack's multilinear extension), `vars` read from the claim's **layout word** (iteration 2, F2:
`layoutWord`, byte 24). The Rust has only a mock frame (`PcsFrame::declaring_all`): which WHIR instance
the block's proof runs is not specified there; this is the choice the statements are made under.

**The layout words** (iteration 2, F2; `contract::layout_word`): 32 bytes, the shape's 8 (`shapeBytes`: `log_memory`,
`log_bytecode`, the six heights), the opening's code (bytes 22..24: `0x5501` `C1`, `0x5502` `C2`, `0x5503` the
setup), the stack's `vars` (byte 24) and `placed` (bytes 25..32, the words its blocks fill, `StackLayout.words`).
**The contract's IV** (`contract_iv`) hashes the tag `ivTag`, the program's IV, the setup's root (`SetupRoots`), the
shape's bytes and the layout words: `UniKeccak.contractIvKWith`, with the Keccak VM's layout words and the variant's
bytes. The seed is then `keccak(name ‖ IV ‖ public input)`; the whole verifier is `UniKeccak.verifyWithK`.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **The plain layout** of a stack of `2^vars` words: one chunk, lane `l` its block `l`
(`PcsQuotient.Layout.ofChunks`); a claim's weight is `eq(point, ·)` on the stack. -/
def plainLayout (vars : ℕ) : PcsQuotient.Layout := PcsQuotient.Layout.ofChunks vars vars vars [(0, 2 ^ vars)]

/-- **The setup's root** (`SetupRoots`), a constant of the verifier: the commitment `F` of the bytecode's tuples and
the memory's addresses. -/
structure SetupRoots where
  bytecode : Digest

/-- The digest whose bytes (`digestBytes`, its words little-endian) are the 32 bytes `b`. -/
def digestOfBytes32 (b : List UInt8) : Digest :=
  Vector.ofFn fun j : Fin 4 ↦
    (List.range 8).foldl (fun acc k ↦ acc ||| ((b.getD (8 * j.val + k) 0).toUInt64 <<< (8 * k).toUInt64)) 0

/-- The bytes of a lowercase hex string (a constant's spelling). -/
def bytesOfHex (s : String) : List UInt8 :=
  let digit (c : Char) : ℕ := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i ↦ (16 * digit (cs.getD (2 * i) '0') + digit (cs.getD (2 * i + 1) '0')).toUInt8

/-- **`shape_bytes(shape)`** (iteration 2, F2): `log_memory`, `log_bytecode`, then the six heights, a byte each. -/
def shapeBytes (s : Shape) : List UInt8 :=
  [s.logMemory.toUInt8, s.logBytecode.toUInt8] ++ (List.range 6).map fun k ↦ (s.heights.getD k 0).toUInt8

/-- `layout_code(commitment)`: the opening's code in its layout word. -/
def layoutCode : Commitment → ℕ
  | .c1 => 0x5501
  | .c2 => 0x5502
  | .setup => 0x5503

/-- **`layout_word(shape, code, vars, placed)`**: the shape's bytes (bytes `0..8`), zeros, the opening's code
(bytes `22..24`, big-endian), the stack's variables (byte `24`) and the words its blocks fill (bytes `25..32`,
big-endian). -/
def layoutWord (s : Shape) (code vars placed : ℕ) : List UInt8 :=
  shapeBytes s ++ List.replicate 14 (0 : UInt8) ++ [(code >>> 8).toUInt8, code.toUInt8, vars.toUInt8] ++
    (List.range 7).map fun k ↦ (placed >>> (8 * (6 - k))).toUInt8

/-- The stack's variables a layout word names (byte `24`): what the opening reads it for. -/
def layoutWordVars (word : List UInt8) : ℕ := (word.getD 24 0).toNat

/-! ### The claims, word for word (`contract::calls`, `opening_words`, `combined_words`) -/

/-- The eight big-endian bytes of a 64-bit word. -/
def be64 (w : UInt64) : List UInt8 := (List.range 8).map fun k ↦ (w >>> (8 * (7 - k)).toUInt64).toUInt8

/-- `number(n)`: a 32-byte word, `n` big-endian in its last eight bytes. -/
def numberWord (n : ℕ) : List UInt8 := List.replicate 24 0 ++ be64 n.toUInt64

/-- `element_word(x)`: `x`'s limbs `c2, c1, c0` big-endian in the low 24 bytes of a 32-byte word. -/
def elementWord (x : E) : List UInt8 :=
  List.replicate 8 0 ++ be64 (x.limb 2).lane ++ be64 (x.limb 1).lane ++ be64 (x.limb 0).lane

/-- A commitment's root word, as the stream carries it (`next_root`'s two halves, each big-endian limbs `1, 0`). -/
def rootWord (halves : E × E) : List UInt8 :=
  be64 (halves.1.limb 1).lane ++ be64 (halves.1.limb 0).lane ++ be64 (halves.2.limb 1).lane ++
    be64 (halves.2.limb 0).lane

/-- **A commitment's root from the two halves the stream carries it as** (`next_root`): the digest whose bytes
are the stream's 32 bytes, as they are (`rootWord`: each half's limbs `1, 0` big-endian). Since the EIP's PCS
claims (`crates/pcs_claim`) the prover sends a root's bytes as they are (`prover::prove::halves`), the bytes a PCS
claim's root field holds; before them it sent the root's two scalars of WHIR's transcript
(`digestOfScalars`). Its four words are the little-endian words of the bytes (`LeanVM.Rpm.bytesLane`). -/
def rootOf (halves : E × E) : Digest :=
  let w := rootWord halves
  #v[LeanVM.Rpm.bytesLane w, LeanVM.Rpm.bytesLane (w.drop 8), LeanVM.Rpm.bytesLane (w.drop 16),
    LeanVM.Rpm.bytesLane (w.drop 24)]

/-- **A root's two halves as the prover sends them** (`prover::prove::halves`): the halves `next_root` reads from
the root's 32 bytes (`digestBytes`), so that `rootWord (rootHalves d) = digestBytes d` and `rootOf (rootHalves d) = d`
(`UniComplete.rootWord_rootHalves`, `UniComplete.rootOf_rootHalves`). -/
def rootHalves (d : Digest) : E × E :=
  let b := (digestBytes d).toArray
  (eNew (beWordAt b 8) (beWordAt b 0) 0, eNew (beWordAt b 24) (beWordAt b 16) 0)

/-- `combined_words(claim)`: its points (a count, then each its length and coordinates), its terms (a count, then
each `column | point << 32 | twist << 48` and its coefficient), its value. -/
def combinedWords (claim : Combined) : List UInt8 :=
  numberWord claim.points.length ++ claim.points.flatMap (fun p ↦ numberWord p.length ++ p.flatMap elementWord) ++
    numberWord claim.terms.length ++
    claim.terms.flatMap (fun (c, p, twist, k) ↦ numberWord (c.id ||| p <<< 32 ||| twist <<< 48) ++ elementWord k) ++
    elementWord claim.value

/-- `opening_words(root, layout, opening)`: a call's header (the root, the layout word, the number of claims),
then its claims: a weighted claim; or a point claim (its coordinates, its value), and the bit-slice claim. -/
def openingWords (root layout : List UInt8) : Opening → List UInt8
  | .weighted claim => root ++ layout ++ numberWord 1 ++ combinedWords claim
  | .point pt v bitSlice => root ++ layout ++ numberWord (if bitSlice.isSome then 2 else 1) ++
      pt.flatMap elementWord ++ elementWord v ++ (bitSlice.map combinedWords).getD []

/-- The contract IV's tag. -/
def ivTag : List UInt8 := "leanVM-univar-iv".toUTF8.toList

/-- **A proof**: the stream (calldata after the selector and the public input: the row counts, then the rest),
and the opening proof the block holds for each of the three claims (mumbai's format,
`Compile.Proof`). -/
structure UniProof where
  stream : Array UInt8
  c1 : Compile.Proof
  c2 : Compile.Proof
  setup : Compile.Proof

/-- **A proof's row counts** (iteration 2, F1): the six its stream announces (`rowsOf`). -/
def UniProof.rows (p : UniProof) : List ℕ := rowsOf p.stream

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **A declared claim's opening** over `F`: the claims on the stack of `2^vars` words committed as `root`,
against the claim's opening proof. -/
def pcsOpenWith (vars : ℕ) (root : Digest) (claims : List PcsQuotient.Claim) (proof : Compile.Proof) :
    m Bool :=
  PcsQuotient.openingWith F (plainLayout vars) root claims proof

end With

end UniStatement

end
