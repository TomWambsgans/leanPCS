-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Transcribed from `crates/membership/quotient/src/protocol.rs` (`verify`, `verify_openings`, `Openings`). The
-- opening proofs are leanerVM's format (`Statement/LeanVmVerifier.lean`, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0).
module

public import PcsQuotient.PcsOpening

/-!
# The verifier

**The proof** (`Proof`): the reduction's proof (four commitments and seven elements of `E`,
`Reduction.lean`) and six PCS openings, one per claim (`Openings`, `protocol.rs`), each in mumbai's format
(`Opening.lean`).

**The verifier** (`verifyWith`), over a permutation `F` in any monad, Keccak-256 the sponge over `F`: the
reduction down to the four commitments and the six claims, then each claim's opening against its commitment,
in the Rust's order (`Claims::all`): the witness claim against `W`, the wiring claim against the circuit's
commitment `index`, then `H`'s, `Q`'s, `G`'s claims, then the sum claim against `H` (`verify_openings`,
`protocol.rs`). It accepts when all six openings hold. Each opening binds its commitment's root to the one
table of the root's list with the commitment's out-of-domain answer, so the two claims on `H` are opened
separately. In the model `F` is the random permutation; deployed, Keccak-f[1600] (`verify`), at
`logRows = 22` and the membership circuit's commitment (`Circuit.lean`, `Security.lean`).

The EVM contract (`crates/membership/evm`) is the reduction, recorded from the same Rust code
(`crates/membership/evm/src/record.rs`); it declares the six claims (the EIP's PCS claims) and leaves them to the
block's proof; this verifier checks them with WHIR directly.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **The openings** of a proof's six claims, in the order of `Claims::all` (`Openings`, `protocol.rs`). -/
structure Openings where
  witness : Compile.Proof
  wiring : Compile.Proof
  h : Compile.Proof
  q : Compile.Proof
  g : Compile.Proof
  sum : Compile.Proof

/-- **A proof**: the reduction's proof and the six openings. -/
structure Proof where
  reduction : ReductionProof
  openings : Openings

/-- **The six claims with their commitments and openings**, in the order of `Claims::all`. -/
def Reduced.checks (index : Commitment) (r : Reduced) (o : Openings) :
    List (Commitment × Claim × Compile.Proof) :=
  [(r.commitments.witness, r.claims.witness, o.witness), (index, r.claims.wiring, o.wiring),
    (r.commitments.h, r.claims.h, o.h), (r.commitments.q, r.claims.q, o.q),
    (r.commitments.g, r.claims.g, o.g), (r.commitments.h, r.claims.sum, o.sum)]

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- Check the openings in order, stopping at the first that fails (`verify_openings`). -/
def checkAllWith : List (Commitment × Claim × Compile.Proof) → m Bool
  | [] => return true
  | (c, claim, proof) :: rest => do
    if !(← pcsOpeningWith F c claim proof) then return false
    checkAllWith rest

/-- **The verifier** over the permutation `F`, on a circuit of `2^logRows` rows committed as `index`: the
claims of the reduction (`reduceWith`), then the six openings, in the Rust's order, stopping at the first that
fails. -/
def verifyWith (logRows : ℕ) (index : Commitment) (stmt : Statement) (proof : Proof) : m Bool := do
  match ← reduceWith F logRows index stmt proof.reduction with
  | none => return false
  | some r => checkAllWith F (r.checks index proof.openings)

end With

/-- The reduction over Keccak-f[1600] (`protocol::verify`): the commitments and claims, or `none`. -/
def reduce (logRows : ℕ) (index : Commitment) (stmt : Statement) (p : ReductionProof) :
    Option Reduced :=
  Id.run (reduceWith (m := Id) (fun s ↦ pure (keccakF1600 s)) logRows index stmt p)

/-- An opening check over Keccak-f[1600] (`opening::verify`, `pcs_claim::verify_claim`). -/
def pcsOpening (c : Commitment) (claim : Claim) (proof : Compile.Proof) : Bool :=
  Id.run (pcsOpeningWith (m := Id) (fun s ↦ pure (keccakF1600 s)) c claim proof)

/-- A layout opening check over Keccak-f[1600] (the previous protocol's `opening::verify`, kept for the leanVM
line). -/
def opening (L : Layout) (root : Digest) (claims : List Claim) (proof : Compile.Proof) : Bool :=
  Id.run (openingWith (m := Id) (fun s ↦ pure (keccakF1600 s)) L root claims proof)

/-- **The deployed verifier**, over Keccak-f[1600], on a circuit of `2^logRows` rows committed as `index`. -/
def verify (logRows : ℕ) (index : Commitment) (stmt : Statement) (proof : Proof) : Bool :=
  Id.run (verifyWith (m := Id) (fun s ↦ pure (keccakF1600 s)) logRows index stmt proof)

end PcsQuotient

end
