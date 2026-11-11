-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `crates/leanvm/rec/src/pi2/contract.rs`
-- (`read_indices`, `frame_payloads`, `payloads`, `claim_words`), π2v4 on the EIP's PCS claims (main 7e6d353c); π1's contract
-- IV is `formal/UniKeccak`'s (`contractIvKWith`, `variantBytesK`: `crates/leanvm/univariate/src/contract.rs`'s
-- `variant_bytes`, `contract_iv_for`). The claims' words are `contract::claim_words`' (`element_word`: an element's
-- limbs big-endian in the low 24 bytes of a 32-byte word).
import RecStatement.Verifier
import UniKeccak.Opening
import UniKeccak.Verifier4

/-!
# The claims, word for word

The transaction's frame of PCS claims declares π1's claims (payloads `0, 1, …`), then π2's four, each the EIP
draft's PCS claim (`crates/pcs_claim`, `docs/PCS_CLAIM.md`): its words (`contract::claim_words`: the root's 32 bytes,
the out-of-domain answer, the point's coordinates, the value, each element its 32-byte word `element_word`).

1. **π1's claims π2's circuit hashes** (`Data.hashed`: all three at 128 and 400 signatures): the contract does not
   encode them; it reads their payloads (their Keccak-256s) from the frame (`Read.frame p`, `frameReads`) into the
   seed, and π2's circuit computes the same Keccak-256s from π1's run (`RecCircuit`'s `ClaimHash` ports).
2. **π1's claims the contract encodes** (none at 128 and 400 signatures), their words as the circuit names them
   (`CallWord`): constants (the setup's root and out-of-domain answer, which the deployment substitutes:
   `pi1CallsWith`), π1's roots (the stream's 32 bytes at their reads), π1's claims' elements (public scalars) and the
   coordinates of π1's pair challenges (`pair_point`);
3. **π2's four** (`pcsCalls`): `W`'s (its root the stream's 32 bytes, its answer the stream's), the setup's (root and
   answer constants), `Q`'s two (the identity's, the pushes', each on `Q`'s root and answer), at payloads
   `π1's count … + 3`.

**π1's contract IV** (`contract_iv_for` at π1's variant `pi1Variant`, `UniKeccak.contractIvKWith`): the Keccak-256 of
the tag, the program IV, π1's setup commitment (`F`'s root and out-of-domain answer), the shape's bytes, then the
variant's bytes: `"keccak-vm"`, the skip and the Fiat–Shamir shape's code.
-/

namespace RecStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- The stream offsets of the roots: π1's (at each `Read.root`), then `W`'s and `Q`'s, after the public data (each of
π2's commitments its root then its 24-byte out-of-domain answer). -/
def rootsAt (reads : List Read) : List ℕ :=
  let (roots, next) := reads.foldl (fun (acc : List ℕ × ℕ) rd ↦
    (if rd = .root then acc.1 ++ [acc.2] else acc.1, acc.2 + rd.bytes)) ([], 0)
  roots ++ [next, next + 56]

/-- **`read_indices`**: the public scalars' indices of π1's claims' elements (each `Read.scalar` or `Read.narrow`),
after the public input's four words. -/
def elementIndices (reads : List Read) : List ℕ :=
  (reads.foldl (fun (acc : List ℕ × ℕ) rd ↦
    (if rd = .scalar ∨ rd = .narrow then acc.1 ++ [acc.2] else acc.1, acc.2 + rd.scalars)) ([], 4)).1

/-- **`frame_payloads`**: the frame payloads the verifier reads as public words (`Read.frame p`), in order. -/
def frameReads (reads : List Read) : List ℕ :=
  reads.filterMap fun rd ↦ match rd with
    | .frame p => some p
    | _ => none

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

/-- **The claims the contract encodes**, word for word (`claim_words`), in order: π1's it encodes (`pi1`, the circuit's
words), then `W`'s, the setup's (its root's 32 bytes and its answer the deployment's), `Q`'s identity and pushes'
claims. -/
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
     qHead ++ claimWords r.pushes]

/-- The stream's length: the public data, `W`'s and `Q`'s commitments (roots and out-of-domain answers), the
`2^r + 2` values. -/
def streamLen (c : Circuit) : ℕ := (c.reads.map (·.bytes)).sum + 64 + 48 + 24 * (2 ^ c.logRow + 2)

/-! ## π1's contract IV -/

/-- **π1's variant under the recursion** (`leanvm_rec::PI1`). -/
def pi1Variant : UniKeccak.KeccakVariant := UniKeccak.keccakRec4

/-- **`variant_bytes(PI1)`**: `"keccak-vm"`, the skip, the Fiat–Shamir shape's code (`UniKeccak.variantBytesK`). -/
def pi1VariantBytes : List UInt8 := UniKeccak.variantBytesK pi1Variant

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`contract_iv_for(shape, PI1, program_iv, roots)`** over `F`: π1's contract IV
(`UniKeccak.contractIvKWith … pi1Variant`) at π1's setup commitment. -/
def pi1IvWith (s : UniStatement.Shape) (programIv : List UInt8) (roots : UniKeccak.SetupRootsK) :
    m (List UInt8) :=
  UniKeccak.contractIvKWith F s pi1Variant programIv roots

end With

/-- π1's contract IV over Keccak-f[1600] (`UniKeccak.contractIvK … pi1Variant`). -/
def pi1Iv (s : UniStatement.Shape) (programIv : List UInt8) (roots : UniKeccak.SetupRootsK) : List UInt8 :=
  Id.run (pi1IvWith (m := Id) (fun x ↦ pure (keccakF1600 x)) s programIv roots)

end RecStatement
