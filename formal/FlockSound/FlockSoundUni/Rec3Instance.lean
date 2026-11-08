-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The interface is `UniSound.FlockSound3`
-- (`formal/UniSound/UniSound/Rec3/FlockInterface3.lean`); the instance follows `Instance.lean` (the main line's).
import FlockSoundUni.Rec3Catch
import UniSound.Rec3.FlockInterface3

/-!
# π1-rec3's Flock interface instance

**`flockSound3_of tx hw : UniSound.FlockSound3 κ`**: the chain program `flockProg3 κ` and its link `flock_link3`,
the main line's reading `outOf κ ∘ expandFd κ` (`outOf_expandFd`), the walk (`hw : WalkSpec κ`: on a completed
transcript whose walk's zero vanishes, the reading's pending claim is its sum; `Rec3Walk.lean` proves it from the
walk's lemma), the bad family `flockBad3 κ` of sizes `dBound3 κ`, which catches (`catches3`, given the main line's
evaluator transcription `Tx κ`). Round `j`'s error `Σ_i dBound3 κ j i / |E|`: `(2^(4 + κ) − 1)/|E|` for the
squares' challenge (Kronecker, `2^22 − 1` at `κ = 18`: `sum_dBound3_le`), the main line's after; every round's at most
`(2^(4 + κ) + 90)/|E|` (`flockSound3_err_le`).
-/

/-- info: 'FlockSound.Uni.flock_link3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FlockSound.Uni.flock_link3
