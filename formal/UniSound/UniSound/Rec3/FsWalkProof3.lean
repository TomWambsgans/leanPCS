-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The main line's `FsWalkProof.lean` (`uniWalk`,
-- `uniWalkReject`) for π1-rec3's walk (`UniStatement.runWithFs … .rec3 true`); its generic lemmas (`progRun`,
-- `readCounts_ok`, `consumes_run`, …) are used as they are.
import UniSound.Rec3.FsGame3
import UniSound.FsCouple
import UniSound.FsWalk
import UniSound.FsWalkProof

/-!
# π1-rec3's walk is the chain (`UniWalk3`, `UniWalkReject3`)

The two halves of π1-rec3's verifier bridge's walk (`FsWalk3.lean`), proved for **every** deployment, Flock phase,
`nV`, `np` and code-level link `C` (no hypothesis):

* **`uniWalk3 : UniWalk3 D F3 nV np C`**: on a stream of `uLen3` bytes the walk's verdict and result are `uAccB3`
  and `uOut3` at the chain's challenges;
* **`uniWalkReject3 : UniWalkReject3 D F3 nV np`**: on a stream of another length every outcome rejects.

The route is `FsWalkProof.lean`'s: the walk's wrapper (`runWithFs_pair3`: `runWithFs` is the seed, `reduceWithFs`,
then `finish`; its verdict and result are `walkOf3` of `obsOf3`), the code-level link `C.link` (stated up to
`obsOf3`) replaces `reduceWithFs` by `readCounts` then `C.prog`, and the main line's generic lemmas do the rest:
`readCounts_ok`, **`progRun`** (any chain program on a stream holding its bytes is the chain's steps), the bytes the
chain absorbs (`absorbsI_wAbs`), `Consumes` for the rejection.

**The narrow challenges** (`sampleNarrow`, which records `narrowE x` in `Chan.challenges`) need no change of a walk
lemma: the chain program's rounds draw through `samples` (the raw challenges, `progRun`), the code-level link relates
`reduceWithFs` to it up to `obsOf3` (no `challenges`), and the walk's verdict and result (`walkOf3`) read only the
result, the stream, the cursor and the zeros' verdict.
-/

namespace UniSound

open Compose QuotientRpm LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics UniStatement
open OracleSpec OracleComp

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.setupStack

/-! ## The walk: the seed, π1-rec3's run, `finish` -/

/-- **The verdict and result of a walk** from what `obsOf3` keeps of the run (`walkOf` without the challenges). -/
def walkOf3 (o : Except UniError Reduced × Option (Array UInt8 × ℕ × ℕ × Digest × Bool)) :
    Bool × Except UniError Reduced :=
  match o with
  | (.error e, _) => (false, .error e)
  | (.ok r, some (d, cur, _, _, z)) =>
    if cur = d.size then (z, .ok r) else (false, .error .streamNotConsumed)
  | (.ok _, none) => (false, .error .streamNotConsumed)

theorem walkOf3_ok (x : Except UniError Reduced × Chan) (r : Reduced) (h1 : x.1 = .ok r)
    (h2 : x.2.cursor = x.2.data.size) : walkOf3 (obsOf3 x) = (x.2.zeros.all (· == 0), .ok r) := by
  rcases x with ⟨res, c⟩
  simp only at h1 h2
  subst h1
  simp [obsOf3, walkOf3, h2]

/-! ## WALK -/

/-! ## WALK REJECTS -/

end UniSound
