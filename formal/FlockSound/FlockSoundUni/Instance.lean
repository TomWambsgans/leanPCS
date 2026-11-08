-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import FlockSoundUni.Catch
import FlockSoundUni.Transcription

/-!
# Flock's interface instance, closed

The catch (`catches_of_tx`) takes the evaluator transcription `Tx κ`; `flockTx κ` proves it
(`Transcription.lean`: the skip's interpolation, the fixed coordinates, `E::pow`, the tower target and
ring claim, the pending claim and sum). So **`flockSoundInstance κ : UniSound.FlockSound κ`** is the
one Flock hypothesis of the end theorem, discharged: the chain program `flockProg κ` and its link
`flock_link`, the bad family `flockBad κ` of sizes `dBound κ`, round `j`'s error `roundErr κ j / |E|`
(`4 + κ`, `15`, `2` per zerocheck round, `3`, `2` per lincheck round, `6`) and `εFlock = (66 + 3κ)/|E|`.
-/

