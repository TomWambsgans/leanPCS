-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `crates/leanvm/univariate/src/contract.rs`
-- (`claims_with`, `rust_verifier_with`: the claims of the run, the EIP's PCS claims) and
-- `crates/leanvm/univariate/src/prover/opening.rs`; a claim's opening is `formal/WhirBridge`'s transcription of
-- `crates/pcs_claim`'s `verify_claim` (`WhirBridge.Pcs.pcsVerifyWithHash`). A non-module file: `WhirBridge` is not
-- a module.
import UniKeccak.Opening
import WhirBridge.Pcs

/-!
# The Keccak contract's PCS claims and the whole Keccak verifier

* **The commitments** (`commitOfK`): `C1`'s and `C2`'s roots and out-of-domain answers as the run read them (each
  answer right after its root), the setup's the contract's constants (`SetupRootsK`).
* **The claims** (`pcsClaimK`, `pcsClaimsK`): one per commitment, the EIP draft's PCS claim (`crates/pcs_claim`,
  `docs/PCS_CLAIM.md`) of its point claim: `version ‖ n ‖ root ‖ ood ‖ point ‖ value`, `n` the point's length
  (`WhirBridge.Pcs.claimBytes`); its Keccak-256 is a payload of the transaction's frame of PCS claims.
* **The whole verifier** (`verifyWithK`): the run (`runWithK`, point claims), its verdict, then each claim's
  opening, `WhirBridge.Pcs.pcsVerifyWithHash` over `F` (Keccak-256 the sponge over `F`), the out-of-domain point
  `WhirBridge.Pcs.oodPoint n` of the claim's root (the deployed Keccak-256: a function of the root the verifier fixes,
  as `formal/WhirBridge`'s soundness theorems take it; they hold for every such function). A proof is the stream and
  three opening proofs (`KeccakProof`).

**Deviation, changing no verdict**: the Lean verifier requires each claim's point to have its commitment's stack
variables (`stackVarsK`: `C1`'s, `C2`'s, the setup's `vars`, from the shape); the Rust takes `n` from the point,
which the batch makes `r.take vars` of the batch's point `r` of `max vars` coordinates, so the two never differ.
-/

namespace UniKeccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

/-- A commitment's stack variables at a shape (`layouts_for(shape, Keccak)`'s `vars`). -/
def stackVarsK (shape : UniStatement.Shape) (c : Commitment) : ℕ := (((layoutsOfK shape).lookup c).getD default).vars

/-- **A commitment of the run**: `C1`'s and `C2`'s root (from the stream's halves) and out-of-domain answer (read
after it), the setup's the contract's constants. -/
def commitOfK (roots : SetupRootsK) (r : Reduced) : Commitment → Digest × E
  | .c1 => (rootOf r.roots.1, r.oods.1)
  | .c2 => (rootOf r.roots.2, r.oods.2)
  | .setup => (roots.f, roots.fOod)

/-- **The PCS claim of a point claim** on a commitment `(root, ood)`, on `n = point.length` variables. -/
def pcsClaimK (root : Digest) (ood : E) (pt : List E) (v : E) : WhirBridge.Pcs.Claim1 pt.length :=
  ⟨root, ood, pt, v, rfl⟩

/-- **`claims_with`**: the claims the contract checks declared, in order, one per commitment, each the EIP's PCS
claim's bytes (`PcsClaim::encode`); a weighted claim is no PCS claim (nothing). -/
def pcsClaimsK (roots : SetupRootsK) (r : Reduced) : List (List UInt8) :=
  r.openings.map fun (c, o) ↦ match o with
    | .point pt v _ => WhirBridge.Pcs.claimBytes (pcsClaimK (commitOfK roots r c).1 (commitOfK roots r c).2 pt v)
    | .weighted _ => []

/-- A commitment's root as the contract holds it: `C1`'s and `C2`'s the stream's 32 bytes (`rootWord`), the setup's
the constant's. -/
def rootBytesK (roots : SetupRootsK) (r : Reduced) : Commitment → List UInt8
  | .c1 => rootWord r.roots.1
  | .c2 => rootWord r.roots.2
  | .setup => digestBytes roots.f

/-- **The claims' words** as the contract holds them, in order (what `contract::claims` hands the frame check and
π2's circuit carries): each point claim's root (its 32 bytes), its out-of-domain answer, its point's coordinates
and its value, each element its word (`elementWord`); a weighted claim none. -/
def pcsClaimWordsK (roots : SetupRootsK) (r : Reduced) : List (List UInt8) :=
  r.openings.map fun (c, o) ↦ match o with
    | .point pt v _ => rootBytesK roots r c ++ elementWord (commitOfK roots r c).2 ++ pt.flatMap elementWord ++
        elementWord v
    | .weighted _ => []

/-- **A Keccak proof**: the stream (the row counts, then the rest) and the opening proof of each of the three
claims (`crates/pcs_claim`'s, mumbai's format). -/
structure KeccakProof where
  stream : Array UInt8
  c1 : Compile.Proof
  c2 : Compile.Proof
  setup : Compile.Proof

/-- A proof's row counts: the six its stream announces (`rowsOf`). -/
def KeccakProof.rows (p : KeccakProof) : List ℕ := rowsOf p.stream

/-- A commitment's opening proof. -/
def KeccakProof.openingOf (p : KeccakProof) : Commitment → Compile.Proof
  | .c1 => p.c1
  | .c2 => p.c2
  | .setup => p.setup

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **A claim's opening** over `F` (`pcs_claim::verify_claim`): the point claim `(pt, v)` on the commitment
`(root, ood)` of a stack of `n` variables, its point required to have `n` coordinates. -/
def pcsOpenK (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) : m Bool :=
  if h : pt.length = n then
    WhirBridge.Pcs.pcsVerifyWithHash (keccak256With F) F (WhirBridge.Pcs.oodPoint n) ⟨root, ood, pt, v, h⟩ p
  else pure false

/-- **The Keccak verifier** over `F`: the run on the stream (point claims; its row counts read and range-checked
there), its verdict, the three claims' openings (`C1`, `C2`, the setup). -/
def verifyWithK (shape : UniStatement.Shape) (v : KeccakVariant) (iv : List UInt8) (roots : SetupRootsK)
    (publicInput : Vector UInt8 32) (proof : KeccakProof) : m Bool := do
  let o ← runWithK F shape iv publicInput.toList proof.stream v .point
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    -- C1, C2, the setup: one point claim each.
    let mut ok := r.openings.map (·.1) == commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        ok := ok && (← pcsOpenK F (stackVarsK shape c) (commitOfK roots r c).1 (commitOfK roots r c).2 pt value
          (proof.openingOf c))
      | _ => ok := false
    -- No matrices' claims.
    if r.matrices.isSome then ok := false
    return ok

end With

end UniKeccak
