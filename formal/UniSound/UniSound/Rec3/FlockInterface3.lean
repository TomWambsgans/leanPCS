-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The interface is `UniSound.FlockSound`'s
-- (`FlockInterface.lean`) for π1-rec3's Flock phase, `formal/UniStatement`'s `Flock.verifyWalkedFs` at `.rec3`
-- (`crates/leanvm/statement/src/flock_min.rs`'s `verify_walked` at `FLOCK_REC3`).
import UniSound.Prog
import UniSound.FlockInterface
import UniStatement.RecSecurity

/-!
# Flock's interface at π1-rec3

π1-rec3's verifier runs Flock as `Flock.verifyWalkedFs F (14 + κ) flockMain .rec3` (`UniStatement.Rec`): the main
line's front, but

* the zerocheck's coordinates after the seven fixed ones are `c, c², c⁴, …` of **one** challenge `c`
  (`drawRun .rec3`, `squares`): the first round draws one challenge instead of `4 + κ`;
* the lincheck's terminal is **walked** (`walkedTerminal`, leanVM's forward walk of the BLAKE2s circuit on the sent
  slices): a zero the verifier collects after the slices, before the ring map's challenges; there is no pending
  matrices' reduction, the batching sumcheck has no `λ³` term;
* it returns the slices' point and the ring switch's end.

**`FlockSound3 κ`** is the one hypothesis about it, the analog of `FlockSound κ`:

* `prog`, `link`: `Flock.verifyWalkedFs` is a chain program (no root, no tail; its one zero the walk's);
* **the main line's reading** `outM done` (point, end, pending): the transcript read as the main line's Flock with
  the zerocheck's squares written out. Its point and end are the program's result (`out_end`); its pending is the
  main line's `Pending.new` of the same front, whose claim is its sum exactly when the walk's zero vanishes
  (`walk`: the walk is the matrices' product sum, `formal/FlockSound/FlockSoundUni/Walk.lean`). The univariate
  identity model reads Flock through `outM`, so that the main line's identity model is reused as it is;
* `S`, `err`, `S_nil`, `step`, `finish`: round-by-round soundness from `FlockHolds`, as `FlockSound`'s, its last
  state from the ring claim and the pending claim (which the walk gives).
-/

