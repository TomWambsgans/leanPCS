-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The Flock region and its predicate are
-- `formal/Lv42`'s (leanerVM `mumbai` f0393df4's `FlockRegion.Holds`, MIT OR Apache-2.0); the verifier's
-- Flock phase is `formal/UniStatement`'s `Flock.verify` (`crates/leanvm/statement/src/flock_min.rs`).
import UniSound.Prog

/-!
# Flock's interface: the one hypothesis the end-to-end proof takes about Flock

**The Flock argument is a separate proof.** The univariate verifier (iteration 2, main line
`flockMain = ⟨3, .tower⟩`, point claims) runs Flock's front (`Flock.verifyDeferred`: the
zerocheck with a skip of 3, the lincheck, the 64 slices, the ring map in tower order) between `γ`
and `C2`'s root, on `C1`'s column `q_flock`; it leaves

* the **ring switch's claim** on `q_flock` (`End.ring map target`: `Σ_k d_k q̂(φ^k(p)) = target`,
  `d = towerCoefficients map`, one of `C1`'s relations: the term of twist `ringTwist`), and
* the **matrices' reduction, pending** (`Pending`, lever 4a): the claim
  `Σ_(x, y) G(x, y) L̂(x) ŝ(y) = claim`, `G = Â0 + α B̂0` at the row and column points, whose
  `k + 6` rounds the batching sumcheck runs as its `λ³` term; its terminal hands `PCS_OPEN` the
  claims on `A0`, `B0`.

The end theorem (`UniSound.Final`) takes **one** hypothesis about Flock, `FlockSound κ` below (`κ`
the hash table's log-height, `q_flock` of `2^(8 + κ)` cells), whose fields the Flock proof must
provide:

* **`prog`, `link`**: the code-level link. `Flock.verifyDeferred F (14 + κ) flockMain` is a chain
  program (`UniSound.Prog`): its rounds (no root; the first the zerocheck's sampled coordinates with
  no message), and its result (the slices' point, the end, the pending reduction), each a pure
  function of its transcript; `link` is the equation of channel programs, for every lawful monad
  and permutation (an unfolding of `flock_min.rs`'s transcription).
* **`S`, `err`, `S_nil`, `step`, `finish`**: Flock's **round-by-round** soundness, on its own
  transcript (`Done`: the messages and challenges of its completed rounds), for every column `qf`
  of `2^(8 + κ)` cells: a state `S qf done`, true at the start only if `qf` satisfies
  `FlockRegion.Holds` (`S_nil`: the block R1CS on every block of `2^14` bits, the constant
  position `1`); round `j` turns it from false to true with probability at most `err j` over its
  `ns + 1` uniform challenges, for every transcript before it and every message (`step`); and it
  is true at the end when the ring switch's claim holds of `qf` and the pending reduction's claim
  is its sum (`finish`; `FlockEndHolds`, `PendingHolds`). The pending sum's own rounds are the
  batching sumcheck's (`UniSound.Sumcheck`, generic), not Flock's.

**Why round by round.** The verifier is non-interactive: Flock's challenges are Keccak-256 of the
transcript, so a prover may re-draw them by re-hashing. A bound "except with probability `ε` over
Flock's challenges" for an interactive prover does not survive Fiat–Shamir; a round-by-round bound
does, and the chain (`Compose.ListChainK`, `Piop`) takes exactly that: each of Flock's rounds is a
round of the chain, its error `err j` multiplied by `C1`'s list bound (the candidates of the one
root before it) and union-bounded over the adversary's queries. Over an interactive run the same
fields give the statement asked for, with `εFlock = Σ_j err j` per candidate (`flockError`).

In the end theorem this structure is a hypothesis **named for Flock** (`hFlock : FlockSound κ`),
and its errors enter `ε` through the rounds' bound.
-/

namespace UniSound

open LeanVM.Parameters LeanVM.Semantics UniStatement
open scoped ENNReal

/-! ## Flock's predicate and the claims it emits -/

/-- `eq(p, x)` on the first `n` coordinates, `x` a cube point by its bits (low first):
`Π_k (1 + p_k + x_k)`. -/
def cubeEq (p : List E) (n x : ℕ) : E :=
  ∏ k ∈ Finset.range n, (1 + p.getD k 0 + if x.testBit k then 1 else 0)

/-- **The multilinear extension over `E`** of a column of `K` at a point (low coordinate first):
`Σ_x eq(p, x) q(x)`. -/
noncomputable def mleE {n : ℕ} (q : LeanVM.Protocol.Column n) (p : List E) : E :=
  ∑ x : Fin (2 ^ n), cubeEq p n x.val * ofK (q.values.get x)

/-- The multilinear extension of a table of `2^n` words given as an array (words past its end read
`0`). -/
noncomputable def mleArr (a : Array K) (n : ℕ) (p : List E) : E :=
  ∑ x : Fin (2 ^ n), cubeEq p n x.val * ofK (a.getD x.val 0)

/-- A point's coordinates squared `k` times (`twistedPoints`' `k`-th twist): `φ^k(p)`. -/
def twist (p : List E) (k : ℕ) : List E := p.map fun x ↦ sqn x k

/-- **Flock's claim on `q_flock` holds**: the ring switch's `Σ_{k<64} d_k q̂(φ^k(p)) = target`, `d_k`
the tower-order coefficients of the map (`towerCoefficients`, the weight of the relation the verifier
pushes on `C1`, twist `ringTwist`). Without an end, or with the bit-slice end (extension B), it holds
of nothing here. -/
noncomputable def FlockEndHolds {κ : ℕ} (qf : LeanVM.Protocol.Column (8 + κ))
    (r : List E × Option Flock.End × Flock.Pending) : Prop :=
  match r.2.1 with
  | some (.ring map target) =>
    ∑ k ∈ Finset.range 64, (Flock.towerCoefficients map).getD k 0 * mleE qf (twist r.1 k) = target
  | _ => False

/-- Bit `i` of `u`, the cube point's coordinate, in `E`. -/
def bitsE (u n : ℕ) : List E := (List.range n).map fun i => if u.testBit i then 1 else 0

/-- `L(x) s(y)` at the cube point `u`: the skip's Lagrange weight (`1` without a skip) and the
slice. -/
def Pending.L (p : Flock.Pending) (u : ℕ) : E :=
  (if p.k > 0 then p.skipWeights.getD (u % 2 ^ p.k) 0 else 1) * (p.slices.getD []).getD (u / 2 ^ p.k) 0

/-! ## The interface -/

end UniSound
