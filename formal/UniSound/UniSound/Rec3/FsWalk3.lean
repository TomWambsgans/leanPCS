-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The main line's `FsWalk.lean` for π1-rec3's walk
-- (`UniStatement.runWithFs … .rec3 true`, `formal/UniStatement/UniStatement/Rec.lean`).
import UniSound.Rec3.FsCouple3
import UniSound.FsWalk

/-!
# π1-rec3's verifier bridge: the walk is the chain, then the openings

`FsWalk.lean`'s split of the verifier bridge at the walk, for π1-rec3 (`runWithFs … .rec3 true`):

* **`UniWalk3`**: on a stream of π1-rec3's length (`uLen3`: the row counts' `24` bytes, the rounds' messages on
  `rec3Rounds`, the tail's three scalars), in every lawful monad and over every permutation, the walk's verdict
  and result are the chain's challenges read by `uAccB3` and the chain program's result `uOut3`;
* **`UniWalkReject3`**: on a stream of any other length, every outcome of the walk over `π` rejects;
* **`UniOutRoots3`**: the code-level link's result names the stream's two roots (rounds `0` and `nF + 1`).
  It is a hypothesis about the code-level link `C` (another module proves it for the concrete link); it follows
  from the link's `out` naming them on every transcript (`uniOutRoots3_of`).

**The narrow challenges** change nothing here: the chain's challenges are the hash's full outputs
(`challengeOf state`), the chain program `C.prog` applies `narrowE` itself where the code does, and the walk reads
`reduceWithFs`'s run only through `obsOf3` (verdict, result, stream, cursor, absorbed bytes, state, the zeros'
verdict), never the channel's `challenges` (where `sampleNarrow` records the narrow value).
-/

