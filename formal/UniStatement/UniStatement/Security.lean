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

/-! ### The setup -/

/-! ### The extractor -/

/-- `C1`'s root as the stream names it: its 32 bytes after the six row counts (iteration 2, F1: bytes
`24..56`), two 16-byte halves (`next_root`). -/
def c1RootOf (proof : UniProof) : Digest :=
  let b := proof.stream
  let half (o : ℕ) : E := eNew (beWordAt b (o + 8)) (beWordAt b o) 0
  rootOf (half 24, half 40)

/-! ### Knowledge soundness -/

/-! ### Completeness -/

end UniStatement

end
