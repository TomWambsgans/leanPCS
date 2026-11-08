-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The bound's form is
-- `formal/Compose/Compose/ListChainKDoom.lean`'s `knowledgeSoundness_listChainK_closed_rpm`.
import UniSound.PiopSound

/-!
# The code-level link, the final link and the Fiat–Shamir layer

Three hypotheses of the end theorem, each a statement about `UniStatement`'s verifier, none
about the PIOP's mathematics:

* **`UniCode`** (the code-level link): after the row counts, `reduceWith` on the main line (Flock
  `flockMain`, point claims) is a chain program (`UniSound.Prog`) on `uniRounds`, its Flock
  rounds Flock's chain program, its tail the three stacks' values and `a`, `b` at the batch's point.
* **`UniFinal`** (the last link): the verifier's last check (the batch's terminal) with the
  claims true makes the sumcheck's last claim the identity model's
  `Σ_{k<3} λ^k W_k(r) C_k(r) + λ³ G(r) L(r)` at its point (`I.prod`, `I.target`: `weightAt` is
  the multilinear extension of the cube's weights, the stacks zero-extended, the pending matrices'
  term `(a + α b) L̂(ρ) ŝ(σ)`).
* **`FsLayer`** (the Fiat–Shamir layer): for **every** round-by-round sound protocol on the main
  line's rounds whose first state is leanVM 42422001's relation (`hpre`) and whose last state
  follows from the verifier's checks with true claims on the candidates (`hlink`), the univariate
  verifier is knowledge sound for `uniExtractor` with the bound `uniBound e` (`e` bounding the
  rounds' errors). It is `Compose.knowledgeSoundness_listChainK_closed_rpm` for the univariate
  verifier: its proof is the port of `ListChainK` to the univariate transcript (24-byte scalars,
  roots as two reversed 16-byte halves, the seed `name ‖ iv ‖ input`; see `FsLayer`'s
  docstring), the five `PCS_OPEN` calls as `WhirOp`s (`WhirShape.large`: `C1`, `C2`, the setup
  and `A0`, `B0` at `2^24 … 2^28` words), the setup's three trees and its IV, and the extractor's
  reading (`uniExtractor`'s replay, Merkle inversion and decoders list the chain's candidates).

**`uniBound e Q`**, for an adversary of `Q` calls of `π` and `π⁻¹`: the five openings' doom terms,
the chain's list term with both roots' lists at most `9952` (`largeList` at `2^24`, the largest
of `2^24 … 2^28`), and the random-permutation term, with `N = 2^33 + Q` bounding every count (the
setup's `< 2^26` Keccak-256 calls, twice, the chain's `< 2^10`, the openings' `5 · 10122`):

`5 · openingBoundAt 10122 N + N · (9952² e + (2^128 + 8 N) / 2^256) + (2^81 + Q)² / 2^508`.

The port (`FsProof.lean`'s `fsLayer_of_game`, through `Compose.ListChainU`) separates the seed
`name ‖ iv ‖ input` from a step's input by its 16-byte tag `name`: a fresh answer starting with it is
a bad event, `2^-128` a query (the `2^128 / 2^256` term, `≈ 2^-64` at `Q = 2^64`); an input refers
to at most five digests (`Refers`' three, and a root after a state or after the row counts), so
`ListChainK`'s `5 N` becomes `(5 + 2) N ≤ 8 N`; `QVπ ≤ 2^80` the verifier's calls of `π`.
-/

namespace UniSound

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement Finset WhirBridge
open scoped ENNReal

/-! ## Claims on candidates -/

/-- The multilinear extension of a stack (a function of the word) on its first `n` coordinates. -/
noncomputable def mleStk (c : Stk) (n : ℕ) (pt : List E) : E :=
  ∑ x : Fin (2 ^ n), cubeEq pt n x.val * ofK (c x.val)

/-- **The stack a commitment's claim is on**: `C1`'s and `C2`'s candidates, the setup's honest
stack. -/
def stackFor (D : Deployment) (c1 c2 : Stk) : Commitment → Stk
  | .c1 => c1
  | .c2 => c2
  | .setup => fun i => (setupStack D.prog D.shape).getD i 0

/-- The layout word of a commitment's `PCS_OPEN` call (`layoutWords`: `C1`, `C2`, the setup). -/
def wordIndex : Commitment → ℕ
  | .c1 => 0
  | .c2 => 1
  | .setup => 2

/-- **The opened transcript of a completed one**, round `0`'s root read as `c1`, round
`nF + 1`'s as `c2`. -/
def openedOf (nF : ℕ) (c1 c2 : Stk) (done : Done) : Op Stk :=
  (done.zipIdx).map fun x =>
    ((if x.2 = 0 then some c1 else if x.2 = nF + 1 then some c2 else none, x.1.1.2), x.1.2)

/-! ## The code-level link -/

section With

variable {m : Type → Type} [Monad m]

/-- **The row counts** (iteration 2, F1): six 4-byte big-endian integers, each range-checked for its
height `r` (`countBits`'s checks: below `2^(r+1)`, and at most `2^r`). -/
def readCounts (heights : List ℕ) : ChanM m (List ℕ) :=
  heights.mapM fun r => do
    let count ← nextInteger (m := m) 4
    requireZero (m := m) (intBits count (r + 1) 32)
    requireZero (m := m) (intBits count r 1 * intBits count 0 r)
    pure count

end With

/-- **What the verdict and the chain read of a run**: its result, and on success the stream, the
cursor, the absorbed bytes, the state, the challenges, and whether every value required zero is. -/
def obsOf {α : Type} (x : Except UniError α × Chan) :
    Except UniError α × Option (Array UInt8 × ℕ × ℕ × Digest × Array E × Bool) :=
  (x.1, match x.1 with
    | .ok _ => some (x.2.data, x.2.cursor, x.2.absorbed, x.2.state, x.2.challenges,
        x.2.zeros.all (· == 0))
    | .error _ => none)

/-! ## The last link -/

/-! ## The Fiat–Shamir layer -/

/-- `N`: every count of the bound at `Q` adversary calls. -/
def uniN (Q : ℕ) : ℕ := 2 ^ 33 + Q

/-- **The univariate verifier's bound** at `Q` adversary calls, rounds' errors at most `e`. -/
noncomputable def uniBound (e : ℝ≥0∞) (Q : ℕ) : ℝ≥0∞ :=
  5 * openingBoundAt 10122 (uniN Q) +
    (uniN Q : ℝ≥0∞) * (((9952 ^ 2 : ℕ) : ℝ≥0∞) * e + ((2 ^ 128 + 8 * uniN Q : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508

end UniSound
