-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The predicate is `formal/UniSound`'s
-- `Ids.FlockGood` (`Ids/Model.lean`); the instance is `Instance.lean`'s `flockSoundInstance`.
import FlockSoundUni.PendingShape
import UniSound.Ids.Build

/-!
# Flock's result is the main line's: `FlockGood` for `flockSoundInstance`

The identity model of `formal/UniSound/UniSound/Ids` is degenerate unless Flock's result is the main
line's (`Ids.FlockGood κ V`): a ring end, a point of `q_flock`'s `8 + κ` coordinates, its pending
reduction's rounds within the batch's `V`. For `flockSoundInstance κ` (`flockProg κ`, its result
`flockOut`) on a completed transcript: the end is always `.ring`; the point is the lincheck's `8`
coordinates (reversed) and the zerocheck's after its `3 + 8` first (`11 + κ` rounds, `7` fixed and
`4 + κ` sampled challenges: `decodeSC`'s point has one coordinate per round); the pending reduction has
at most `15` rounds (`flockPendingShaped`), and the batch has at least `15` variables.
**`flockGood`**.
-/

namespace FlockSound.Uni

open UniSound UniStatement LeanVM.Parameters

/-- **`decodeSC`'s point** has one coordinate per round it decodes. -/
theorem decodeSC_length : ∀ (c : E) (es : List (Option E)) (d : Done),
    (decodeSC c es d).1.length = min es.length d.length
  | _, [], _ => by simp [decodeSC]
  | c, e :: es, r :: d => by
    simp only [decodeSC, List.length_cons, decodeSC_length _ es d]
    omega
  | _, _ :: _, [] => by simp [decodeSC]

end FlockSound.Uni
