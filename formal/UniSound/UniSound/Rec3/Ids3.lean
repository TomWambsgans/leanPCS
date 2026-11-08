-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The identity model is `Ids/`'s (the main line's),
-- read at π1-rec3's transcripts; the batch's start follows `Ids/Batch.lean`'s `batch_start_of`.
import UniSound.Ids.Build
import UniSound.Rec3.BusSq
import UniSound.Rec3.Piop3
import FlockSoundUni.Rec3Instance

/-!
# π1-rec3's identity model, from the main line's

**`ids3Of`**: `UniIds3 D F3 np` for π1-rec3's Flock phase `F3 = flockSound3_of tx hw`, from the main line's
identity model `idsRestOf D N h Fl d n g` at Flock's main-line instance `Fl` (`flockSoundInstance κ`), read at
π1-rec3's transcripts:

* round `0`'s three challenges `[c, β, γ]` as the main line's six (`expandCh`: `α = (c, c², c⁴, c⁸)`), the bus's
  error over three draws `BusModel.mainSoundSq` (`16 N / |E|` and the constraints');
* Flock's transcript as the main line's (`expandFd`: the squares' one challenge written out), so that
  `F3.outM fd = Fl.prog.out (expandFd fd) []` (definitionally): the polynomials, the merge polynomial, the relations'
  differences (the pending matrices' among them) are the main line's at the expanded transcript;
* **the batch without the pending term** (`prod3Of`: the three commitments' products; `target3Of`: their values'
  combination), whose start holds when the pending claim is its sum (`batch_start3_of`): the pending difference
  then vanishes (`pendDiff_eq_zero`).
-/

