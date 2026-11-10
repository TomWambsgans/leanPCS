-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `formal/UniComplete/UniComplete/Whir.lean`'s honest
-- openings (`pcsOpen_honest`, `pcsOpenWith_honest`, `pcsOpenWith_honest'`, `pcsOpen_fails_only_at_pow`) at the plain
-- layouts of `2^23 ..= 2^28` words, admissibility at `2^23` from `formal/UniKeccakSound`'s `Fs/Whir23.lean`
-- (`admissible_k`); through this repository's `E2ECompleteness.ProverOpening` (`openingWithH_proveOpeningWithH`,
-- `exists_failed_pow_opening`), as the original.
import UniComplete.Whir
import UniKeccakSound.Fs.Whir23

/-!
# Honest WHIR openings at the Keccak verifier's plain layouts (`2^23 ..= 2^28` words)

The Keccak verifier opens three commitments, each with one point claim (`UniStatement.pcsOpenWith`) at the plain
layout `plainLayout vars`: `C1` and `C2` at `27`, `26` variables and the setup at **`23`** at the reference shape
(`keccakRefShape`), one below the window `24 ..= 28` the generic `UniComplete.Whir` covers. What
`E2ECompleteness.openingWithH_proveOpeningWithH` and `exists_failed_pow_opening` ask of a layout is its weight
table's shape (`WeightShape`, `UniComplete.weightShape_plain`, every `6 ≤ v ≤ 64`) and admissibility of its size at
rate `1/2` (`Whir.Admissible`); the latter at `23` is `UniKeccakSound.admissible_23` (`decide +kernel` on the ladder),
joined with `WhirBridge.admissible_large` in `UniKeccakSound.admissible_k` for `23 ≤ v ≤ 28`. The claim's meaning
(`UniComplete.plain_holds`, `plain_multilinear`) is size-generic. So:

* **`admissible_plainK`**, **`plainShapesK`**: both facts for `23 ≤ v ≤ 28`;
* **`pcsOpen_honestK`**, **`pcsOpenWith_honestK`**, **`pcsOpenWith_honestK'`**: the honest opening of the point claim
  `⟨pt, stackEval stack pt⟩` is accepted, for `23 ≤ vars ≤ 28`, the statements of `UniComplete`'s with `23` for `24`;
* **`pcsOpen_fails_only_at_powK`**: the opening prover fails only at a `17`-bit proof of work, likewise.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

namespace UniKeccakComplete

open UniComplete
open UniStatement (plainLayout)

/-- **The plain layouts of `2^23 ..= 2^28` words are admissible** at rate `1/2` (`UniKeccakSound.admissible_k`). -/
theorem admissible_plainK {v : ℕ} (h1 : 23 ≤ v) (h2 : v ≤ 28) :
    Whir.Admissible (plainLayout v).logN PcsQuotient.logInvRate :=
  UniKeccakSound.admissible_k h1 h2

/-- **Both facts at the Keccak verifier's sizes**, `23 ≤ v ≤ 28`. -/
theorem plainShapesK {v : ℕ} (h1 : 23 ≤ v) (h2 : v ≤ 28) :
    E2ECompleteness.WeightShape (plainLayout v) ∧ Whir.Admissible v PcsQuotient.logInvRate :=
  ⟨weightShape_plain (by omega) (by omega), admissible_plainK h1 h2⟩

/-- **An honest opening at a plain layout is accepted** (`23 ≤ vars ≤ 28`), at a pure Keccak-256 `H` and
permutation `F`: `UniComplete.pcsOpen_honest` down to `2^23` words. -/
theorem pcsOpen_honestK (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {vars : ℕ}
    (h1 : 23 ≤ vars) (h2 : vars ≤ 28) (stack : Array K) (hs : stack.size = 2 ^ vars) (pt : List E)
    (hpt : pt.length = vars) {π : Compile.Proof}
    (hπ : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout vars)
      (E2ECompleteness.commitWithH (m := Id) H vars stack) stack [⟨pt, stackEval stack pt⟩] = some π) :
    E2ECompleteness.openingWithH (m := Id) H F (plainLayout vars)
      (E2ECompleteness.commitWithH (m := Id) H vars stack).root [⟨pt, stackEval stack pt⟩] π = true :=
  E2ECompleteness.openingWithH_proveOpeningWithH H F fuel (plainLayout vars)
    (weightShape_plain (by omega) (by omega)) (admissible_plainK h1 h2) stack _ (List.cons_ne_nil _ _)
    (fun c hc ↦ by rw [List.mem_singleton] at hc; subst hc; exact hpt)
    (plain_holds (by omega) (by omega) stack hs pt hpt) (plain_multilinear vars _) hπ

/-- **A claim's opening check accepts the honest opening** (`UniStatement.pcsOpenWith` over `F`), at the root the stream
carries as two halves, `23 ≤ vars ≤ 28`: `UniComplete.pcsOpenWith_honest` down to `2^23` words. -/
theorem pcsOpenWith_honestK (F : KeccakState → KeccakState) (fuel : ℕ) {vars : ℕ} (h1 : 23 ≤ vars)
    (h2 : vars ≤ 28) (stack : Array K) (hs : stack.size = 2 ^ vars) (pt : List E) (hpt : pt.length = vars)
    {π : Compile.Proof}
    (hπ : E2ECompleteness.proveOpeningWithH (m := Id) (keccak256With (m := Id) fun s ↦ pure (F s))
      (fun s ↦ pure (F s)) fuel (plainLayout vars)
      (E2ECompleteness.commitWithH (m := Id) (keccak256With (m := Id) fun s ↦ pure (F s)) vars stack) stack
      [⟨pt, stackEval stack pt⟩] = some π) :
    UniStatement.pcsOpenWith (m := Id) (fun s ↦ pure (F s)) vars
      (UniStatement.rootOf (UniStatement.rootHalves
        (E2ECompleteness.commitWithH (m := Id) (keccak256With (m := Id) fun s ↦ pure (F s)) vars stack).root))
      [⟨pt, stackEval stack pt⟩] π = true := by
  rw [rootOf_rootHalves, UniStatement.pcsOpenWith, E2ECompleteness.openingWith_eqH]
  exact pcsOpen_honestK _ F fuel h1 h2 stack hs pt hpt hπ

/-- **The same with the Statement's prover and commitment** over `F`, `23 ≤ vars ≤ 28`:
`UniComplete.pcsOpenWith_honest'` down to `2^23` words. -/
theorem pcsOpenWith_honestK' (F : KeccakState → KeccakState) (fuel : ℕ) {vars : ℕ} (h1 : 23 ≤ vars)
    (h2 : vars ≤ 28) (stack : Array K) (hs : stack.size = 2 ^ vars) (pt : List E) (hpt : pt.length = vars)
    {π : Compile.Proof}
    (hπ : PcsQuotient.proveOpeningWith (m := Id) (fun s ↦ pure (F s)) fuel (plainLayout vars)
      (PcsQuotient.commitWith (m := Id) (fun s ↦ pure (F s)) vars stack) stack
      [⟨pt, stackEval stack pt⟩] = some π) :
    UniStatement.pcsOpenWith (m := Id) (fun s ↦ pure (F s)) vars
      (UniStatement.rootOf (UniStatement.rootHalves
        (PcsQuotient.commitWith (m := Id) (fun s ↦ pure (F s)) vars stack).root))
      [⟨pt, stackEval stack pt⟩] π = true := by
  rw [E2ECompleteness.proveOpeningWith_eqH, E2ECompleteness.commitWith_eqH] at hπ
  rw [E2ECompleteness.commitWith_eqH]
  exact pcsOpenWith_honestK F fuel h1 h2 stack hs pt hpt hπ

/-- **The opening prover fails only at a proof of work** at a plain layout (`23 ≤ vars ≤ 28`):
`UniComplete.pcsOpen_fails_only_at_pow` down to `2^23` words. -/
theorem pcsOpen_fails_only_at_powK (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
    {vars : ℕ} (h1 : 23 ≤ vars) (h2 : vars ≤ 28) (stack : Array K) (claims : List PcsQuotient.Claim)
    (hlen : ∀ c ∈ claims, c.point.length = vars)
    (h : E2ECompleteness.proveOpeningWithH (m := Id) H F fuel (plainLayout vars)
      (E2ECompleteness.commitWithH (m := Id) H vars stack) stack claims = none) :
    ∃ hist k sp, (Whir.Complete.openingProgram vars PcsQuotient.logInvRate
        (PcsQuotient.stackClaims (plainLayout vars) claims)).after hist =
          some (.grind Whir.queryGrindingBits k) ∧
      ∀ n < fuel, powOk Whir.queryGrindingBits (Compile.nonceOf n)
        (Compile.powStep F sp (Compile.nonceOf n)).1 = false :=
  E2ECompleteness.exists_failed_pow_opening H F fuel (plainLayout vars)
    (weightShape_plain (by omega) (by omega)) (admissible_plainK h1 h2) stack claims hlen h

end UniKeccakComplete

/-! ## Axioms -/

/-- info: 'UniKeccakComplete.plainShapesK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.plainShapesK

/-- info: 'UniKeccakComplete.pcsOpen_honestK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.pcsOpen_honestK

/-- info: 'UniKeccakComplete.pcsOpenWith_honestK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.pcsOpenWith_honestK

/-- info: 'UniKeccakComplete.pcsOpenWith_honestK'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.pcsOpenWith_honestK'

/-- info: 'UniKeccakComplete.pcsOpen_fails_only_at_powK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.pcsOpen_fails_only_at_powK
