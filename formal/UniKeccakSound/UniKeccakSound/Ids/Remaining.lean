-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The assembly is `UniSound/Ids/Remaining.lean`'s, for
-- the Keccak VM.
import UniKeccakSound.Ids.Assembly
import UniKeccakSound.Ids.BusCount
import UniKeccakSound.Ids.FlockEnd

/-!
# What remains of the Keccak identity model

**`IdsRemainingK F D Fl d n`**: the bridges of `IdsHypsK` and the reductions of `IdsGapsK` not proved in this
directory. Proved here and plugged in: the bus counts (`kvBusCount`, at `N = busBoundK D.shape`), the Keccak-f
region with the lanes' copies (`auxOfFlockK`, from `KeccakFlockFits F` and the lanes' slots `LaneSlotsK`), the
ring-switch relation's claim (`diffsFlockK`), for `κ = h_SHA3`.

**`uniKnowledgeSoundnessK_remaining`**: knowledge soundness of the Keccak verifier (main line) at the Keccak
code-level link `uniCodeKAt`, from `IdsRemainingK`, Flock's result the main line's (`FlockGoodDoneK`), the weights
multilinear off `Z_bad`'s roots (`WeightMleK`), the stacks' variables below `256` (`LayoutVarsSmall3K`), the
Fiat–Shamir layer and the numbers.
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak
open scoped ENNReal

/-- **What remains** (named hypotheses), for Flock's phase `Fl` at `κ`, the degrees' bound `d` and the relations'
`n`. -/
structure IdsRemainingK (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (d n : ℕ) : Prop where
  heapGood : HeapGood D.shape
  kvRealizes : KvRealizesK D
  kvConstraints : KvConstraintsK D
  cvecOk : CvecOkK D
  functionals : FunctionalsCorrect (D.shape.heights.getD opSha3 0)
  height2 : 2 ≤ D.shape.heights.getD opSha3 0
  laneSlots : LaneSlotsK
  diffsEval : DiffsEvalK D Fl
  mainOfPolys : MainOfPolysK D Fl
  degBound : DegBoundK D Fl d
  relCount : RelCountK D Fl n

section

variable (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) {κ : ℕ} {v : KeccakVariant} (Fl : KFlockSound F κ v)

/-- **The bridges**, from what remains. -/
theorem idsHypsK_of (hκ : D.shape.heights.getD opSha3 0 = κ) (hF : KeccakFlockFits F) {d n : ℕ}
    (r : IdsRemainingK F D Fl d n) : IdsHypsK F D κ (busBoundK D.shape) where
  heapGood := r.heapGood
  kvRealizes := r.kvRealizes
  kvBusCount := kvBusCount D
  kvConstraints := r.kvConstraints
  cvecOk := r.cvecOk
  auxOfFlock := auxOfFlockK F D κ hκ hF r.laneSlots
  functionals := r.functionals
  height2 := r.height2

/-- **The reductions**, from what remains. -/
theorem idsGapsK_of (hκ : D.shape.heights.getD opSha3 0 = κ) {d n : ℕ} (r : IdsRemainingK F D Fl d n) :
    IdsGapsK D Fl d n where
  diffsEval := r.diffsEval
  mainOfPolys := r.mainOfPolys
  diffsFlock := diffsFlockK D Fl hκ
  degBound := r.degBound
  relCount := r.relCount

end

/-- **Knowledge soundness of the Keccak verifier (main line)** at the Keccak code-level link `uniCodeKAt`, with the
identity model built from what remains (`IdsRemainingK`), for a Keccak-f block whose ports are the verifier's
(`KeccakFlockFits F`) and Flock's phase at `κ = h_SHA3`. -/
theorem uniKnowledgeSoundnessK_remaining (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (hκ : D.shape.heights.getD opSha3 0 = κ) (hF : KeccakFlockFits F)
    (d n : ℕ) (r : IdsRemainingK F D Fl d n) (hgood : FlockGoodDoneK Fl) (hW : WeightMleK D Fl)
    (hsmall : LayoutVarsSmall3K D)
    (hFs : FsLayer128K F D Fl valsCountK (varsOf (layoutsOfK D.shape)) (uniCodeKAt D Fl hκ _ _ rfl rfl))
    (hFl : ∀ j, Fl.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hB : 4 * busBoundK D.shape + ncvK D.shape ≤ 2 ^ 32) (hdeg : d + zBadDeg D.shape ≤ 2 ^ 32)
    (hrel : max n 1 + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundnessKeccak F D (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  uniKnowledgeSoundnessK_code D Fl hκ (busBoundK D.shape) (idsHypsK_of F D Fl hκ hF r) d n
    (idsGapsK_of F D Fl hκ r) hgood hW hsmall hFs hFl hB hdeg hrel

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.uniKnowledgeSoundnessK_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.uniKnowledgeSoundnessK_remaining
