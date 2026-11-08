-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The hypothesis is `formal/UniSound`'s
-- `FlockPendingShaped` (`FinalLink.lean`); the instance is `Instance.lean`'s `flockSoundInstance`.
import FlockSoundUni.Instance
import UniSound.FinalLink

/-!
# Flock's pending reduction has its shape: `FlockPendingShaped` for `flockSoundInstance`

The batch's last link (`UniSound.uniFinal`) needs, of Flock's chain program, that its pending
reduction has the shape `multilinear_eval` reads as multilinear extensions (`Pending.Shaped`), that
the slices are sent, and at most `15` rounds. For `flockSoundInstance κ` (`flockProg κ`): the skip's
weights are `lagrangeWeights (2^k) z` for `k = 6 − |rowLow|` (`2^k` of them whatever the lengths),
the row and column points have at most `3` and `8` coordinates, and the slices are the last round's
64 scalars. **`flockPendingShaped`**, and **`uniKnowledgeSoundness_flock`**: the end theorem with Flock's
interface, the code-level link and the last link in place.
-/

namespace FlockSound.Uni

open UniSound UniStatement LeanVM.Parameters
open scoped ENNReal

theorem pending_new_shaped (z α rLc : E) (rowLow chiIn chiInPrime slices : List E)
    (hrl : rowLow.length ≤ 3) (hci : chiIn.length ≤ 8) (hsl : slices.length = 64) :
    Pending.Shaped (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some slices)) ∧
      (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some slices)).hasSlices = true ∧
      (Flock.Pending.new (some z) rowLow chiIn chiInPrime α rLc (some slices)).rounds ≤ 15 := by
  simp only [Pending.Shaped, Flock.Pending.new, Flock.rowLowWeights, Flock.Pending.rounds,
    Flock.Pending.hasSlices, Flock.packing, Option.getD_some, Option.isSome_some, lagrangeWeights_length,
    List.length_append, matrixVars, blake2sR1csLogSize]
  exact ⟨⟨fun _ => trivial, Or.inl (by rw [hsl]; rfl), by omega⟩, trivial, by omega⟩

end FlockSound.Uni

