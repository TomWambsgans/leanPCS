-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The walk is `UniStatement.runWith`
-- (`formal/UniStatement/UniStatement/Run.lean`), the chain `Compose.ChainSpecU.chain`
-- (`formal/Compose/Compose/ListChainU.lean`).
import UniSound.FsCouple
import UniSound.FinalLink

/-!
# The verifier bridge's two halves: the walk is the chain, then the openings

`UniVerifierBridge` (`FsCouple.lean`) compares the Statement's `verifyWith` (the walk on the stream,
`runWith`, then the five `PCS_OPEN` calls) with the composed verifier (the chain `verU`, then the
five openings `opsRun`). It splits at the walk:

* **`UniWalk`** (the walk is the chain): on a stream of the main line's length (`uLen`: the row
  counts' `24` bytes, the rounds' messages, the tail's five scalars), in every lawful monad and over
  every permutation `F`, the walk's verdict and result are a function of the chain's challenges
  over Keccak-256 `= keccak256With F`: the verdict `uAccB` (the row counts' range checks and every
  value the chain program requires zero vanish), the result the chain program's (`uOut`);
* **`UniWalkReject`** (a stream of another length is rejected): every outcome of the walk over `π`
  rejects (the stream runs out, `StreamExhausted`, or is left unread, `StreamNotConsumed`);
* the openings (`uniVerifierBridge_of_walk`, the remaining half): the Statement's five `PCS_OPEN`
  calls are F2's `ourVerifierEarly` at the plain layouts (`Bridge.openingWith_eq_ourVerifier'`),
  which accept at most as often as the composed openings (`Soundness.early_le`), and acceptance
  makes the result well formed (`uniCheck`).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.setupStack

section Walk

variable {κ : ℕ} (nV V : ℕ)

/-- **The row counts' range checks** (`readCounts`), in order: each count below `2^(r + 1)`, and at
most `2^r`, for its height `r`. -/
def countZeros (heights rows : List ℕ) : List E :=
  (heights.zip rows).flatMap fun x =>
    [intBits x.2 (x.1 + 1) 32, intBits x.2 x.1 1 * intBits x.2 0 x.1]

end Walk

end UniSound

