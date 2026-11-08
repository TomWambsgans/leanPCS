-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proof follows `PiopSound.lean` (the main line's).
import UniSound.PiopSound
import UniSound.Rec3.Piop3

/-!
# π1-rec3's PIOP is round-by-round sound

**`uniPiop3 F3 I BR`**: the states `uniPre3`, `uniPost3` and the errors `uniErr3` form a `RbrPiop` on π1-rec3's
rounds (`rec3Rounds`), for π1-rec3's Flock phase `F3`, any identity model `I` and any batch `BR`: round `0` by
`mainSound` (three challenges); Flock's rounds by Flock's `step`; `t` by Schwartz–Zippel for every identity and the
merge polynomial; `ρ, λ` by the two combinations, the batch's start (`batch_start`) under the pending claim the
states carry from `C2`'s round on; the batch's rounds by `BR.step`. `pre_post` from `main_of_polys` and Flock's
`finish` at `C2`'s round, the pending claim there one of `uniPre3`'s.
-/

