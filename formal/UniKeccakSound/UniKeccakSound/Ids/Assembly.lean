-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The composition is `UniSound/Ids/Build.lean`'s
-- `uniKnowledgeSoundness_ids` and `UniSound/FinalLink.lean`'s `uniKnowledgeSoundness_code`, for the Keccak VM.
import UniKeccakSound.FinalK
import UniKeccakSound.Ids.Final

/-!
# Knowledge soundness of the Keccak verifier with the identity model and the last link constructed

**`uniKnowledgeSoundnessK_ids`**: `FinalK.lean`'s `uniKnowledgeSoundnessK` at the identity model `uniIdsK` (from
the bridges `IdsHypsK` and the reductions `IdsGapsK`) and the last link `uniFinalK_of` (from `CodeIsMainK`,
`FlockGoodDoneK`, `WeightMleK`, `LayoutVarsSmall3K`), its numbers stated on the model's: `4 N + ncv ≤ 2^32` (round
`0`), `d + zBadDeg ≤ 2^32` (`t`), `max n 1 + 2 ≤ 2^32` (`ρ, λ`).
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak
open scoped ENNReal

/-- **The numbers of `uniIdsK`**: round `0`'s error, the degrees, the relations, as `FinalK.lean`'s end theorem
needs them. -/
theorem uniIdsK_numbers (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (N : ℕ) (h : IdsHypsK F D κ N) (d n : ℕ) (g : IdsGapsK D Fl d n)
    (hB : 4 * N + ncvK D.shape ≤ 2 ^ 32) (hdeg : d + zBadDeg D.shape ≤ 2 ^ 32) (hrel : max n 1 + 2 ≤ 2 ^ 32) :
    (uniIdsK D Fl N h d n g).errMain ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ∧
      (uniIdsK D Fl N h d n g).degSum + (uniIdsK D Fl N h d n g).degBad ≤ 2 ^ 32 ∧
      (uniIdsK D Fl N h d n g).nRel + 2 ≤ 2 ^ 32 :=
  ⟨uniIdsK_errMain_le D Fl N h d n g hB, hdeg, hrel⟩

/-- **Knowledge soundness of the Keccak verifier (main line)** for the explicit extractor `uniExtractorK F D`, with
error `uniBound128 (2^32/|E|) Q`, from Flock on the Keccak-f block `Fl`, the identity model's bridges `h` and
reductions `g`, a code-level link `C` whose checks and claims are the main line's (`hC`), Flock's result the main
line's (`hgood`), the weights multilinear off `Z_bad`'s roots (`hW`), the stacks' variables below `256`
(`hsmall`), the Fiat–Shamir layer `hFs`, and the numbers. -/
theorem uniKnowledgeSoundnessK_ids (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (N : ℕ) (h : IdsHypsK F D κ N) (d n : ℕ) (g : IdsGapsK D Fl d n)
    (C : UniCodeK D Fl valsCountK (batchVarsK D.shape)) (hC : CodeIsMainK D Fl _ _ C) (hgood : FlockGoodDoneK Fl)
    (hW : WeightMleK D Fl) (hsmall : LayoutVarsSmall3K D)
    (hFs : FsLayer128K F D Fl valsCountK (batchVarsK D.shape) C)
    (hFl : ∀ j, Fl.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hB : 4 * N + ncvK D.shape ≤ 2 ^ 32) (hdeg : d + zBadDeg D.shape ≤ 2 ^ 32) (hrel : max n 1 + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundnessKeccak F D (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  have hn := uniIdsK_numbers D Fl N h d n g hB hdeg hrel
  uniKnowledgeSoundnessK_bits Fl (uniIdsK D Fl N h d n g) C (uniFinalK_of D Fl N h d n g C hC hgood hW hsmall)
    hFs hn.1 hFl hn.2.1 hn.2.2

/-- **Knowledge soundness of the Keccak verifier (main line), the code-level links constructed**: at the Keccak
code-level link `uniCodeKAt` (`UniKeccakSound.Code.Link`, its checks and claims the main line's by
`codeIsMainK_uniCodeKAt`), for a deployment whose `SHA3` height is Flock's `κ`. -/
theorem uniKnowledgeSoundnessK_code (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (hκ : D.shape.heights.getD opBlake2s 0 = κ) (N : ℕ) (h : IdsHypsK F D κ N)
    (d n : ℕ) (g : IdsGapsK D Fl d n) (hgood : FlockGoodDoneK Fl) (hW : WeightMleK D Fl)
    (hsmall : LayoutVarsSmall3K D)
    (hFs : FsLayer128K F D Fl valsCountK (varsOf (layoutsOfK D.shape)) (uniCodeKAt D Fl hκ _ _ rfl rfl))
    (hFl : ∀ j, Fl.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hB : 4 * N + ncvK D.shape ≤ 2 ^ 32) (hdeg : d + zBadDeg D.shape ≤ 2 ^ 32) (hrel : max n 1 + 2 ≤ 2 ^ 32) :
    UniKnowledgeSoundnessKeccak F D (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  uniKnowledgeSoundnessK_ids D Fl N h d n g _ (codeIsMainK_uniCodeKAt D Fl hκ) hgood hW hsmall hFs hFl hB hdeg
    hrel

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.uniKnowledgeSoundnessK_ids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.uniKnowledgeSoundnessK_ids

/-- info: 'UniKeccakSound.Ids.uniKnowledgeSoundnessK_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.uniKnowledgeSoundnessK_code

/-- info: 'UniKeccakSound.Ids.uniFinalK_uniCodeKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.uniFinalK_uniCodeKAt

/-- info: 'UniKeccakSound.Ids.uniFinalK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.uniFinalK_of

/-- info: 'UniKeccakSound.Ids.uniIdsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.uniIdsK
