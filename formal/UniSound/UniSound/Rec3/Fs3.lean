-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The links' and the layer's form is `Fs.lean`'s (the main
-- line's), for π1-rec3's verifier (`formal/UniStatement`'s `reduceWithFs`, `verifyWithFs` at `.rec3` with the walk).
import UniSound.Fs
import UniSound.PiopSound
import UniSound.Rec3.Piop3

/-!
# π1-rec3: the code-level link, the last link and the Fiat–Shamir layer

The three hypotheses of π1-rec3's end theorem that speak of `UniStatement`'s verifier, as `Fs.lean`'s:

* **`UniCode3`** (the code-level link): after the row counts, `reduceWithFs … (.flock flockMain) .point .rec3 true`
  is a chain program on `rec3Rounds`, its Flock rounds `F3`'s, its tail the three stacks' values at the batch's
  point (no `a`, `b`).
* **`UniFinal3`** (the last link): on a completed transcript whose zeros vanish (the batch's terminal
  `sum + last = 0`, and Flock's walk) and whose three claims are true (`ClaimsHold`: no matrices' claim), the pending
  claim is its sum (the walk) and the batch's last state holds (`BR.St` at the batch's point), unless `t` is a root
  of the merge polynomial.
* **`FsLayer3`** (the Fiat–Shamir layer): every round-by-round sound protocol on π1-rec3's rounds, its errors at most
  `e`, whose first state is the relation and whose last follows from the checks with true claims, makes π1-rec3's
  deployed verifier knowledge sound for `uniExtractor` with the bound `uniBound3 e`.

**`uniBound3 e Q`**: `uniBound`'s, with **three** openings' doom terms instead of five (the setup still has three
trees, the IV hashing their roots: `Security.lean`'s setup is unchanged; the verifier opens `C1`, `C2` and the setup
only).
-/

namespace UniSound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement Finset WhirBridge
open scoped ENNReal

/-- **What the verdict and the chain read of a run, at π1-rec3**: `obsOf` without the channel's list of challenges.
Decision (recorded): π1-rec3's batch draws through `sampleNarrow`, which records the narrow challenge `narrowE x` in
`Chan.challenges` where a chain program's `samples` records the raw `x`; the verdict, the result, the stream, the
cursor, the absorbed bytes and the state are the same, so the link is stated up to them (`obsOf3`), and the
challenges are read off the states (`challengeOf`), as the Fiat–Shamir layer does. -/
def obsOf3 {α : Type} (x : Except UniError α × Chan) :
    Except UniError α × Option (Array UInt8 × ℕ × ℕ × Digest × Bool) :=
  (x.1, match x.1 with
    | .ok _ => some (x.2.data, x.2.cursor, x.2.absorbed, x.2.state, x.2.zeros.all (· == 0))
    | .error _ => none)

/-- `obsOf3` is a function of `obsOf`. -/
theorem obsOf3_eq_of_obsOf {α : Type} {x y : Except UniError α × Chan} (h : obsOf x = obsOf y) :
    obsOf3 x = obsOf3 y := by
  unfold obsOf at h
  unfold obsOf3
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  rw [h1]
  rcases hx : x.1 with _ | _ <;> rcases hy : y.1 with _ | _ <;> simp_all

/-- **π1-rec3's bound** at `Q` adversary calls, rounds' errors at most `e`: `uniBound`'s with three openings. -/
noncomputable def uniBound3 (e : ℝ≥0∞) (Q : ℕ) : ℝ≥0∞ :=
  3 * openingBoundAt 10122 (uniN Q) +
    (uniN Q : ℝ≥0∞) * (((9952 ^ 2 : ℕ) : ℝ≥0∞) * e + ((2 ^ 128 + 8 * uniN Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508

end UniSound
