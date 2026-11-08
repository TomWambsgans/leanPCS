-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The model, the experiments' shape and the form of the
-- statements are this repository's `formal/Statement` (`PcsQuotient.Security`, after leanerVM `mumbai` 6175f1a0's
-- `Statement/LeanVm.lean`, MIT OR Apache-2.0); the extractor's replay, Merkle inversion and decoders are its
-- (`PcsQuotient.Extractor`, `Replay`, `Decoder`) and mumbai's (`Statement/Extractor.lean`); the relation is Lv42's
-- (`formal/Lv42`, leanerVM `mumbai` f0393df4's `M3Holds`).
module

public import UniStatement.Opening
public import UniStatement.Mapping
public import PcsQuotient.Extractor
public import Lv42.Protocol.LeanIsaBase
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Knowledge soundness and completeness, against leanVM 42422001's relation

Statements only, no proof. The model is `formal/Statement`'s (leanerVM `mumbai`'s): one uniformly random
permutation `π` of the Keccak-f[1600] state, which every party queries forward and inverse; every hash of
the protocol is Keccak-256 over `π` (the transcript, the WHIR commitments and openings), the setup's
commitments computed over `π` before the adversary runs.

**The deployment** (`Deployment`): the program `prog` (leanISA with `BLAKE2S`, `2^logBytecode`
instructions), the shape (its heights, one contract per shape class, valid: `Shape.validate` with Flock, F5),
leanVM's program IV. **The row counts are the proof's** (iteration 2, F1): the stream's first 24 bytes
(`UniProof.rows`, `rowsOf`), absorbed with `C1`'s root, each range-checked by the run (`c ≤ 2^h`). **The IV
binds the setup** (iteration 2, F2): `Deployment.ivWith` is the contract's IV, the Keccak-256 of a tag, leanVM's
program IV, the setup's roots, the shape's bytes and the five layout words (`contractIvWith`); each opening's
stack size is its layout word's (`layoutWordVars`), and the Statement's opening hashes the plain layout's
identifier, which encodes it. **The relation** is
Lv42's, for leanVM 42422001's statement: `M3Holds (leanIsaInstance blake2sFlockSpec prog s) input q`
(`= ConstraintsVanish ∧ Balanced ∧ CountsNonzero ∧ PublicLinesHold ∧ aux`, the last `FlockRegion.Holds` of
`q_flock`), at the proof's sizes `s` (`sizesOf`: the shape's memory, the proof's row counts), the public
input the calldata's 32 bytes (`publicInputOf`: big-endian words, as the contract reads them at `ad49e74`,
a documented convention, not changed: a caller reverses leanVM's little-endian words), `q` a stack of
Lv42's layout. Under `Sizes.Admissible`, Lv42 proves `M3Holds` equivalent to `SatisfiedBy prog input
(witnessOf …)` (`satisfiedBy_witnessOf`) and, from a satisfying witness, `M3Honest` of its stack
(`m3Honest_stackOf`).

**The setup** (`setupTreesWith`): the WHIR commitments (`PcsQuotient.commitWith`, rate `1/2`) of the
setup stack `F` (the bytecode's tuples and the memory's addresses, `setupStack`) and of Flock's matrices
`A0`, `B0` (`matrixStack` of `blake2sFlockSpec`'s R1CS). Their roots are the verifier's constants; the
extractor reads their trees (public).

**The extractor** (`uniExtractor`) is explicit and computable, as `formal/Statement`'s: from the
adversary's transcript and the setup's trees, the Keccak-256 evaluations replayed (`Replay`); `C1`'s
Merkle tree inverted under the root the stream names (`c1Word`); its candidate stacks, by the fast path,
the unique decoder, then the list decoder (mumbai's and the Statement's, at `C1`'s `2^μ`, rate `1/2`);
each candidate read as Lv42's stack (`lv42Stack`: basis `B` to values, the correspondence of
`Mapping.lean`); the first that satisfies `M3Holds` at the proof's row counts. It reads only `C1`: `C2`
(the heap, the quotients) and the setup are not part of the witness.

**Completeness** is stated for a prover given as a parameter (`UniProver`): the univariate PIOP's honest
prover is not transcribed (the Rust's, `src/prover`, is being adapted to iteration 2 on
`leanvm-univariate-prover2`).
`UniCompletenessWith` asks that its proof of a statement with an `M3Honest` stack, at row counts that fit the
shape (`Shape.RowsFit`: at least the fewest rows each height's quotients are sized for), be rejected with
probability at most `δ`.
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
