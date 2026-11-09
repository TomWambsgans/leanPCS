-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The verifier is `Rec.lean`'s `verifyWithFs` at π1-rec3
-- (`crates/leanvm/univariate`'s `FLOCK_REC3`, `leanvm-rec` 4247e37).
module

public import UniStatement.Rec
public import UniStatement.Security

/-!
# π1-rec3's deployed verifier

`Security.lean`'s deployed verifier replaced by **π1-rec3's** (`docs/leanvm/rec/SPEC-REC.md` §12 item 8; `Rec.lean`):

* the contract's IV binds the variant (`contractIvForWith … (.flock flockMain) .rec3 true`: the main line's
  preimage with `fs-rec3`, the skip `3` and the slices' code `4` appended);
* the verifier is `verifyWithFs … .rec3 true`: the run (`reduceWithFs`: `α = (c, c², c⁴, c⁸)`, Flock's zerocheck
  coordinates after the seven fixed ones as squares of one challenge, Flock's lincheck terminal walked, the batch
  two variables a round with narrow challenges), then **three** `PCS_OPEN` calls (`C1`, `C2`, the setup); `A0`,
  `B0` are not opened (the proof's `a0`, `b0` are not read).

(The statements of π1-rec3 against leanVM 42422001's relation, with its `BLAKE2S` table, were here; they are
removed with `BLAKE2S`. The Keccak VM's are `UniKeccak.Security`'s.)
-/

@[expose] public section

end
