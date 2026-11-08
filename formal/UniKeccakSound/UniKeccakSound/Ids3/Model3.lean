-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The model is `UniSound/Rec3/Ids3.lean`'s
-- `ids3Of`, from the Keccak main line's (`Ids/Build.lean`'s `uniIdsK`).
import UniKeccakSound.Ids3.Bus3
import UniKeccakSound.Ids.Build
import UniKeccakSound.PiopK3

/-!
# The Keccak identity model at π1-rec3's shape, from the main line's

**`uniIdsK3 D F3 N h d n g np hV : UniIdsK3 F D F3 np`**: the main line's identity model (`Ids/Model.lean`, generic in
the variant) read at π1-rec3's transcripts: round `0`'s three challenges as the main line's six (`expandCh`), Flock's
transcript `F3`'s own (the model reads Flock only through `F3.prog.out`), the batch `prodK`, `targetK` (the Keccak
verifier has no pending term at either shape), over `varsOf (layoutsOfK D.shape) = 2 np + 1` variables (`hV`). The
bridges `h : IdsHypsK F D κ N` and the reductions `g : IdsGapsK D F3 d n` are the main line's structures, at `F3`.
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak Finset
open scoped ENNReal

/-! ## The identity model -/

/-- **The identity model of the Keccak verifier at π1-rec3's shape** for the deployment `D` and Flock's phase `F3`
on the Keccak-f block, from the main line's bridges `h` and reductions `g` (at `F3`), the batch over
`varsOf (layoutsOfK D.shape) = 2 np + 1` variables. -/
noncomputable def uniIdsK3 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (N : ℕ) (h : IdsHypsK F D κ N) (d n : ℕ) (g : IdsGapsK D F3 d n) (np : ℕ)
    (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) : UniIdsK3 F D F3 np where
  nV := valsCountK
  qf c := qfK D c κ
  MainHolds := (busModelK F D κ N h).MainHolds
  rel_of s c hm hf := (busModelK F D κ N h).rel_of F s c hm (h.auxOfFlock s c hm.2.2.2.2 hf)
  MainOK s c ch := (busModelK F D κ N h).MainOK s c (expandCh ch)
  errMain := (busModelK F D κ N h).errMainSq
  mainSound := (busModelK F D κ N h).mainSoundSq
  polys s c1 ch fd c2 := polysK D F3 s c1 (expandCh ch) fd c2
  degSum := d
  deg_le s c1 ch fd c2 := g.degBound s c1 (expandCh ch) fd c2
  main_of_polys s c1 ch fd c2 hP := g.mainOfPolys s c1 (expandCh ch) fd c2 hP
  zb := zbK D F3
  zb_ne _ := zBad_ne_zero D.shape betaCantor h.functionals h.height2 _
  degBad := zBadDeg D.shape
  zb_deg _ := natDegree_zBad_le D.shape _
  diffs s c1 ch fd c2 t vals := diffsK D F3 s c1 (expandCh ch) fd c2 t vals
  nRel := max n 1
  diffs_len s c1 ch fd c2 t vals := diffsK_len D F3 n g.relCount s c1 (expandCh ch) fd c2 t vals
  diffs_count s c1 ch fd c2 t vals := diffsK_count D F3 s c1 (expandCh ch) fd c2 t vals
  diffs_eval s c1 ch fd c2 t vals hz := g.diffsEval s c1 (expandCh ch) fd c2 t vals (by simp [expandCh]) hz
  diffs_flock s c1 ch fd c2 t vals hz := g.diffsFlock s c1 (expandCh ch) fd c2 t vals hz
  prod s c1 ch fd c2 t vals ρ l := prodK D F3 s c1 (expandCh ch) fd c2 t vals ρ l
  prod_vars s c1 ch fd c2 t vals ρ l := by rw [prodK_vars]; exact hV
  target s c1 ch fd c2 t vals ρ l := targetK D F3 s c1 (expandCh ch) fd c2 t vals ρ l
  batch_start s c1 ch fd c2 t vals ρ l _ := batch_start_K D F3 s c1 (expandCh ch) fd c2 t vals ρ l

/-- **The numbers of `uniIdsK3`** at `e = 2^35 / |E|`: round `0`'s error, the degrees, the relations. -/
theorem uniIdsK3_numbers (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (N : ℕ) (h : IdsHypsK F D κ N) (d n : ℕ) (g : IdsGapsK D F3 d n) (np : ℕ)
    (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) (hB : 16 * N + ncvK D.shape ≤ 2 ^ 35)
    (hdeg : d + zBadDeg D.shape ≤ 2 ^ 35) (hrel : max n 1 + 2 ≤ 2 ^ 35) :
    (uniIdsK3 D F3 N h d n g np hV).errMain ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ∧
      (uniIdsK3 D F3 N h d n g np hV).degSum + (uniIdsK3 D F3 N h d n g np hV).degBad ≤ 2 ^ 35 ∧
      (uniIdsK3 D F3 N h d n g np hV).nRel + 2 ≤ 2 ^ 35 :=
  ⟨(busModelK F D κ N h).errMainSq_le hB, hdeg, hrel⟩

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.uniIdsK3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.uniIdsK3
