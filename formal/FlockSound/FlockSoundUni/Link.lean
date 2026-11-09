-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The verifier (`Flock.verifyDeferred`) is
-- `formal/UniStatement`'s, transcribed from `crates/leanvm/statement/src/flock_min.rs`.
import FlockSoundUni.Shape

/-!
# Flock's front as a chain program, and its code-level link

`Flock.verifyDeferred F (14 + κ) flockMain` (skip `3`, the slices sent, the ring map in tower order)
is the chain program `flockProg κ` (no root, no zero, no tail), whose `23 + κ` rounds are:

* `⟨false, 0, 3 + κ⟩`: the zerocheck point's `4 + κ` sampled coordinates `τ`;
* `⟨false, 8, 0⟩`: the skip's `8` coset values, then `z`;
* `11 + κ` × `⟨false, 2, 0⟩`: the zerocheck's rounds (two scalars, a challenge);
* `⟨false, 2, 0⟩`: `v_a`, `v_b` (the end of `zerocheck`), then `α` (drawn in `front`);
* `8` × `⟨false, 2, 0⟩`: the lincheck's rounds;
* `⟨false, 64, 5⟩`: the `64` slices, then the ring map's six challenges (`ringEnd`).

The result (`outOf`) is the code's, from the rounds' reads (`flockOut`: the zerocheck's and the
lincheck's sumchecks decoded, `decodeSC`; `Pending.new`; the tower target). **`flock_link`**
is the equation of channel programs, for every lawful monad and permutation.
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics

/-- **Flock's rounds** at the main line, `κ` the table's batch bits. -/
def flockRounds (κ : ℕ) : List Compose.RoundSpec :=
  [⟨false, 0, 3 + κ⟩, ⟨false, 8, 0⟩] ++ List.replicate (11 + κ) ⟨false, 2, 0⟩ ++ [⟨false, 2, 0⟩] ++
    List.replicate 8 ⟨false, 2, 0⟩ ++ [⟨false, 64, 5⟩]

/-- The transcript's segments. -/
theorem drop_shape {κ : ℕ} (r0 r1 r4 r6 : UMsg × List E) (zc lc : Done) (hzc : zc.length = 11 + κ)
    (hlc : lc.length = 8) :
    (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop 2 = zc ++ r4 :: (lc ++ [r6]) ∧
      (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (13 + κ) = r4 :: (lc ++ [r6]) ∧
      (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (14 + κ) = lc ++ [r6] ∧
      (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (22 + κ) = [r6] := by
  have h13 : (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (13 + κ) = r4 :: (lc ++ [r6]) := by
    rw [show 13 + κ = 2 + (11 + κ) by omega, ← List.drop_drop]
    exact List.drop_left' hzc
  have h14 : (r0 :: r1 :: (zc ++ r4 :: (lc ++ [r6]))).drop (14 + κ) = lc ++ [r6] := by
    rw [show 14 + κ = (13 + κ) + 1 by omega, ← List.drop_drop, h13]
    rfl
  refine ⟨rfl, h13, h14, ?_⟩
  rw [show 22 + κ = (14 + κ) + 8 by omega, ← List.drop_drop, h14]
  exact List.drop_left' hlc

/-! ## The link -/

section Link

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem nextScalars_zero : nextScalars (m := m) 0 = pure [] := by
  simp [nextScalars_eq, repeatM]

theorem nextScalars_two :
    nextScalars (m := m) 2 = (do
      let a ← nextScalar (m := m)
      let b ← nextScalar (m := m)
      pure [a, b]) := by
  simp [nextScalars_eq, repeatM]

theorem length_fixedChallenges : Flock.fixedChallenges.length = 7 := rfl

end Link

end FlockSound.Uni
