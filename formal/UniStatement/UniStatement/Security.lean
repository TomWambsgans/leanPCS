-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The model and the experiments' shape are this
-- repository's `formal/Statement` (`PcsQuotient.Security`, after leanerVM `mumbai` 6175f1a0's `Statement/LeanVm.lean`,
-- MIT OR Apache-2.0); the Merkle inversion is its (`PcsQuotient.Extractor`, `Replay`).
module

public import UniStatement.Opening
public import UniStatement.Mapping
public import PcsQuotient.Extractor
public import Lv42.Protocol.LeanIsaBase
public import VCVio.EvalDist.ProbabilityNotation

/-!
# The deployment, the setup and the experiments' pieces

The pieces the univariate verifier's statements share (`UniKeccak.Security` states the Keccak VM's with them). The
model is `formal/Statement`'s (leanerVM `mumbai`'s): one uniformly random permutation `π` of the Keccak-f[1600]
state, which every party queries forward and inverse; every hash of the protocol is Keccak-256 over `π`.

* **The deployment** (`Deployment`): a program, the shape (its heights, valid: `Shape.validate` with Flock, F5),
  leanVM's program IV; a proof's sizes (`Deployment.sizes`: the shape's memory, the proof's row counts, the
  stream's first 24 bytes). **The IV binds the setup** (`Deployment.ivWith`, the contract's IV: the Keccak-256 of
  a tag, leanVM's program IV, the setup's roots, the shape's bytes and the five layout words, `contractIvWith`);
  the deployed verifier is `Deployment.verifierWith`.
* **The setup's trees** (`SetupTrees`): the WHIR commitments of the setup stack and of Flock's matrices `A0`,
  `B0`; their roots are the verifier's constants, their evaluations what an extractor reads.
* **`C1`'s root and word** (`c1RootOf`, `c1Word`): the root the stream names and the leaves the unique preimages
  commit to under it.
* The adversary's and the outcome's types (`UniAdversary`, `UniOutcome`).

(The statements against leanVM 42422001's relation, with its `BLAKE2S` table and Flock's BLAKE2s circuit, were
here; they are removed with `BLAKE2S`.)
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics (KeccakState)
open LeanVM.Extraction
open OracleComp OracleSpec Common
open Lv42.Protocol.LeanIsa (Sizes)
open Lv42.Semantics (Program PublicInput)
open scoped ENNReal

/-- **The deployment**: the program, the shape (its heights; valid), leanVM's program IV. -/
structure Deployment where
  prog : Program
  shape : Shape
  programIv : List UInt8
  valid : shape.Valid
  logBytecode_eq : shape.logBytecode = prog.logSize

/-- The memory has at least two cells. -/
theorem Deployment.logMemory_pos (D : Deployment) : 0 < D.shape.logMemory := by
  have h := D.valid.2
  unfold Shape.validate at h
  by_contra hc
  have hlt : D.shape.logMemory < 1 := by omega
  simp [hlt] at h

/-- A proof's sizes, as Lv42's: the shape's memory, the proof's row counts. -/
def Deployment.sizes (D : Deployment) (rows : List ℕ) : Sizes := sizesOf D.shape D.logMemory_pos rows

/-! ### The setup -/

/-- **The setup's trees**: the WHIR commitments of the setup stack and of `A0`, `B0`. -/
structure SetupTrees where
  bytecode : LeanVM.Prover.Tree
  a0 : LeanVM.Prover.Tree
  b0 : LeanVM.Prover.Tree

/-- The verifier's constants: the trees' roots. -/
def SetupTrees.roots (t : SetupTrees) : SetupRoots := ⟨t.bytecode.root, t.a0.root, t.b0.root⟩

/-- The setup's Keccak-256 evaluations (each tree's, `Tree.evaluations`), which the extractor reads. -/
def SetupTrees.evaluations (t : SetupTrees) : List (List UInt8 × Digest) :=
  PcsQuotient.Tree.evaluations t.bytecode ++ PcsQuotient.Tree.evaluations t.a0 ++
    PcsQuotient.Tree.evaluations t.b0

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The transcript's IV** over `F` (iteration 2, F2: `contract::contract_iv`): the Keccak-256 of the tag,
leanVM's program IV, the setup's three roots, the shape's bytes and the five layout words
(`contractIvWith`). -/
def Deployment.ivWith (D : Deployment) (roots : SetupRoots) : m (List UInt8) :=
  contractIvWith F D.shape D.programIv roots

/-- **The deployed verifier** over `F` on the setup's roots: its IV (`ivWith`), then `verifyWith` at the
deployment's shape. -/
def Deployment.verifierWith (D : Deployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (proof : UniProof) : m Bool := do
  verifyWith F D.shape (← D.ivWith F roots) roots input proof

end With

/-! ### The extractor -/

/-- `C1`'s root as the stream names it: its 32 bytes after the six row counts (iteration 2, F1: bytes
`24..56`), two 16-byte halves (`next_root`). -/
def c1RootOf (proof : UniProof) : Digest :=
  let b := proof.stream
  let half (o : ℕ) : E := eNew (beWordAt b (o + 8)) (beWordAt b o) 0
  rootOf (half 24, half 40)

/-- **`C1`'s committed word**: under the root the stream names, the leaves the unique preimages `pre`
commit to (`Replay.leavesUnder`, mumbai's `committedLeaves`): `2^(μ − 6 + 1)` leaves of `64` words. -/
def c1Word (D : Deployment) (pre : Digest → ℕ → Option (List UInt8)) (proof : UniProof) : ℕ → List K :=
  let height := (c1Layout D.shape).vars - 6 + 1
  leafAt (PcsQuotient.Replay.leavesUnder pre 64 height (c1RootOf proof)) height 64

/-! ### Knowledge soundness -/

/-- An adversary: given the setup's roots, a public input and a proof, with coins, `π` and `π⁻¹`. -/
abbrev UniAdversary : Type := SetupRoots → OracleComp RandomPermutationOracles (Vector UInt8 32 × UniProof)

/-- An outcome: the statement and the proof, the verdict, the setup's evaluations, the transcript. -/
abbrev UniOutcome : Type :=
  ((Vector UInt8 32 × UniProof) × Bool) × List (List UInt8 × Digest) × OracleQueryLog

/-! ### Completeness -/

end UniStatement

end
