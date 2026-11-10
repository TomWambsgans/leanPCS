-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `crates/leanvm/rec/src/pi2/contract.rs`
-- (`read_indices`, `claim_words`, `expected_calls`), π2v3 on the EIP's PCS claims; π1's contract
-- IV is `formal/UniKeccak`'s (`contractIvKWith`, `variantBytesK`: `crates/leanvm/univariate/src/contract.rs`'s
-- `variant_bytes`, `contract_iv_for`). The claims' words are `contract::claim_words`' (`element_word`: an element's
-- limbs big-endian in the low 24 bytes of a 32-byte word).
import RecStatement.Verifier
import UniKeccak.Opening

/-!
# The eight claims, word for word

The contract checks eight claims declared, each the EIP draft's PCS claim (`crates/pcs_claim`, `docs/PCS_CLAIM.md`)
in its words (`contract::claim_words`: the root's 32 bytes, the out-of-domain answer, the point's coordinates, the
value, each element its 32-byte word `element_word`), in this order:

1. **π1's three** (`C1`, `C2`, π1's setup `F`), their words as the circuit names them (`CallWord`): constants (the
   setup's root, its 32 bytes, and its out-of-domain answer, which the deployment substitutes: `pi1CallsWith`), π1's
   roots `C1`, `C2` (the stream's 32 bytes at their reads), π1's claims' elements (public scalars, `element_word`: the
   out-of-domain answers and the values among them), and the coordinates `y_0(z_j), y_1(z_j)` of π1-rec3's pair
   challenges `z_j` (`pair_point`), which the contract derives;
2. **`W`'s** (its root the stream's 32 bytes, its answer the stream's), **the setup's** (root and answer constants),
   **`Q`'s three** (the identity's, the pushes', the sum, each on `Q`'s root and answer).

**π1's contract IV** (`contract_iv_for` at `KECCAK_REC3`, `UniKeccak.contractIvKWith`): the Keccak-256 of the tag,
the program IV, π1's setup commitment (`F`'s root and out-of-domain answer), the shape's bytes, then the variant's
bytes: `"keccak-vm"`, the skip `3` and the Fiat–Shamir shape's code `3` (`Rec3`).
-/

namespace RecStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- The stream offsets of the roots: π1's (at each `Read.root`), then `W`'s and `Q`'s, after the public data (each of
π2's commitments its root then its 24-byte out-of-domain answer). -/
def rootsAt (reads : List Read) : List ℕ :=
  let (roots, next) := reads.foldl (fun (acc : List ℕ × ℕ) rd ↦
    (if rd = .root then acc.1 ++ [acc.2] else acc.1, acc.2 + rd.bytes)) ([], 0)
  roots ++ [next, next + 56]

/-- **`read_indices`**: the public scalars' indices of π1's claims' elements (each `Read.scalar`), after the public
input's four words. -/
def elementIndices (reads : List Read) : List ℕ :=
  (reads.foldl (fun (acc : List ℕ × ℕ) rd ↦
    (if rd = .scalar then acc.1 ++ [acc.2] else acc.1, acc.2 + rd.scalars)) ([], 4)).1

/-- The number of π1's roots the stream carries. -/
def rootReads (reads : List Read) : ℕ := (reads.filter (· = .root)).length

/-- The stream's 32 bytes from `at`. -/
def streamWord (stream : Array UInt8) (at' : ℕ) : List UInt8 := (stream.extract at' (at' + 32)).toList

/-- A claim's words: its coordinates, then its value. -/
def claimWords (c : List E × E) : List (List UInt8) := (c.1 ++ [c.2]).map UniStatement.elementWord

/-- **A word of π1's calls** from the stream and the reduction. -/
def callWord (reads : List Read) (stream : Array UInt8) (r : Reduced) : CallWord → List UInt8
  | .const w => w
  | .root i => streamWord stream ((rootsAt reads).getD i 0)
  | .element i => UniStatement.elementWord (r.scalars.getD ((elementIndices reads).getD i 0) 0)
  | .pair e c =>
    let pp := r.pairPoints.getD ((elementIndices reads).getD e 0) (0, 0)
    UniStatement.elementWord (if c = 0 then pp.1 else pp.2)

/-- **`expected_calls`**: the eight claims' words, in order: π1's (`pi1`, the circuit's words), then `W`'s, the
setup's (its root's 32 bytes and its answer the deployment's), `Q`'s identity, pushes' and sum claims. -/
def pcsCalls (c : Circuit) (pi1 : List (List CallWord)) (setupRoot : List UInt8) (setupOod : E)
    (stream : Array UInt8) (r : Reduced) : List (List (List UInt8)) :=
  let at' := rootsAt c.reads
  let n := rootReads c.reads
  let wHead := [streamWord stream (at'.getD n 0), UniStatement.elementWord r.oods.1]
  let qHead := [streamWord stream (at'.getD (n + 1) 0), UniStatement.elementWord r.oods.2]
  pi1.map (·.map (callWord c.reads stream r)) ++
    [wHead ++ claimWords r.witness,
     [setupRoot, UniStatement.elementWord setupOod] ++ claimWords r.setup,
     qHead ++ claimWords r.quotient,
     qHead ++ claimWords r.pushes,
     qHead ++ claimWords r.sum]

/-- The stream's length: the public data, `W`'s and `Q`'s commitments (roots and out-of-domain answers), the
`2^r + 2` values. -/
def streamLen (c : Circuit) : ℕ := (c.reads.map (·.bytes)).sum + 64 + 48 + 24 * (2 ^ c.logRow + 2)

/-! ## π1's contract IV -/

/-- **`variant_bytes(KECCAK_REC3)`**: `"keccak-vm"`, the skip (`3`), the Fiat–Shamir shape's code
(`3`, `Rec3`) (`UniKeccak.variantBytesK`). -/
def rec3VariantBytes : List UInt8 := UniKeccak.variantBytesK UniKeccak.keccakRec3

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`contract_iv_for(shape, KECCAK_REC3, program_iv, roots)`** over `F`: the Keccak π1-rec3's
contract IV (`UniKeccak.contractIvKWith … keccakRec3`) at π1's setup commitment. -/
def pi1IvWith (s : UniStatement.Shape) (programIv : List UInt8) (roots : UniKeccak.SetupRootsK) :
    m (List UInt8) :=
  UniKeccak.contractIvKWith F s UniKeccak.keccakRec3 programIv roots

end With

/-- The Keccak π1-rec3's contract IV over Keccak-f[1600] (`UniKeccak.contractIvK … keccakRec3`). -/
def pi1Iv (s : UniStatement.Shape) (programIv : List UInt8) (roots : UniKeccak.SetupRootsK) : List UInt8 :=
  Id.run (pi1IvWith (m := Id) (fun x ↦ pure (keccakF1600 x)) s programIv roots)

end RecStatement
