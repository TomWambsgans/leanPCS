-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The assembly is `UniSound/Ids/Assembly.lean`'s and
-- `UniSound/Closed.lean`'s (`hB_ref`, `hdeg_ref`, `hrel_ref`) at the reference Keccak shape.
import UniKeccakSound.IdsNum.Degrees
import UniKeccakSound.IdsNum.Counts
import UniKeccakSound.Ids.Remaining

/-!
# The Keccak identity model's numbers at the reference shape, and the end theorem with them discharged

At the reference Keccak shape (`keccakRefShape`, 128 signatures):

* **`hB_ref`**: `4 · busBoundK + ncvK ≤ 2^32` (`3,227,649` tuples a side, at most `98` constraints);
* **`hdeg_ref`**: `19,339,139 + zBadDeg ≤ 2^32` (`Z_bad`'s `2^16`);
* **`hrel_ref`**: `max 187 1 + 2 ≤ 2^32`;
* on the rec3 line (`2^35`): **`hB35_ref`** (`16 · busBoundK + ncvK ≤ 2^35`), **`hdeg35_ref`**, **`hrel35_ref`**;
* **`batchVarsK_ref`**: the batch's `27` variables.

**`IdsRemainingRefK F D Fl`**: what remains of `IdsRemainingK` at the reference shape once the numeric and
deployment bridges are discharged (`HeapGood`, `FunctionalsCorrect 15`, `2 ≤ h_SHA3`, `DegBoundK … 19339139`,
`RelCountK … 187`: `idsRemainingK_ref`): the Keccak VM's relation (`KvRealizesK`, `KvConstraintsK`), the
constraint vectors (`CvecOkK`), the lanes' slots (`LaneSlotsK`), the reductions `DiffsEvalK`, `MainOfPolysK`.

**`uniKnowledgeSoundnessK_ref`**: `Ids/Remaining.lean`'s `uniKnowledgeSoundnessK_remaining` at the reference
shape, with `IdsRemainingRefK`, `LayoutVarsSmall3K` and the numbers discharged; **`uniKnowledgeSoundnessK_refIv`**
also with the Fiat–Shamir layer discharged (`Fs/LayerK.lean`'s `fsLayer128K_refCodeAt`, at leanVM's program IV and
at most `987` of Flock's steps, its rounds of at most `2^30` scalars).
-/

namespace UniKeccakSound.IdsNum

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.Eval UniKeccak UniKeccakSound
  UniKeccakSound.Ids
open scoped ENNReal

/-! ## The numbers -/

/-- **Round `0`'s error at the reference shape**: `4 · 3,227,649 + 98 ≤ 2^32`. -/
theorem hB_ref (D : KDeployment) (hD : D.shape = keccakRefShape) :
    4 * busBoundK D.shape + ncvK D.shape ≤ 2 ^ 32 := by
  have h := ncvK_le D.shape
  rw [hD, busBoundK_ref]
  rw [hD] at h
  omega

/-- **`t`'s error at the reference shape**: `19,339,139 + 2^16 ≤ 2^32`. -/
theorem hdeg_ref (D : KDeployment) (hD : D.shape = keccakRefShape) : 19339139 + zBadDeg D.shape ≤ 2 ^ 32 := by
  unfold zBadDeg
  rw [coordinateFunctionals_size, hD, hSha3_ref]
  norm_num

/-- **`ρ, λ`'s error at the reference shape**: `187` relations. -/
theorem hrel_ref : max 187 1 + 2 ≤ 2 ^ 32 := by norm_num

/-- **Round `0`'s error on the rec3 line at the reference shape**: `16 · 3,227,649 + 98 ≤ 2^35`. -/
theorem hB35_ref (D : KDeployment) (hD : D.shape = keccakRefShape) :
    16 * busBoundK D.shape + ncvK D.shape ≤ 2 ^ 35 := by
  have h := ncvK_le D.shape
  rw [hD, busBoundK_ref]
  rw [hD] at h
  omega

/-- **`t`'s error on the rec3 line at the reference shape**: `19,339,139 + 2^16 ≤ 2^35`. -/
theorem hdeg35_ref (D : KDeployment) (hD : D.shape = keccakRefShape) :
    19339139 + zBadDeg D.shape ≤ 2 ^ 35 :=
  (hdeg_ref D hD).trans (by norm_num)

/-- **`ρ, λ`'s error on the rec3 line at the reference shape**: `187` relations. -/
theorem hrel35_ref : max 187 1 + 2 ≤ 2 ^ 35 := by norm_num

/-- **The batch's variables at the reference shape**: `27` (`C1`'s). -/
theorem batchVarsK_ref : batchVarsK keccakRefShape = 27 := by
  show max (max (max 0 (layoutOfK keccakRefShape .c1).vars) (layoutOfK keccakRefShape .c2).vars)
    (layoutOfK keccakRefShape .setup).vars = 27
  rw [layoutOfK_c1_vars_ref, layoutOfK_c2_vars_ref, layoutOfK_setup_vars_ref]
  rfl

/-! ## What remains at the reference shape -/

/-- **What remains of `IdsRemainingK` at the reference Keccak shape** (named hypotheses): the Keccak VM's relation
read off `C1` (`KvRealizesK`, `KvConstraintsK`), the constraint vectors (`CvecOkK`), the lanes' slots
(`LaneSlotsK`), the reductions between the verifier's checks and the identities (`DiffsEvalK`, `MainOfPolysK`). -/
structure IdsRemainingRefK (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) : Prop where
  kvRealizes : KvRealizesK D
  kvConstraints : KvConstraintsK D
  cvecOk : CvecOkK D
  laneSlots : LaneSlotsK
  diffsEval : DiffsEvalK D Fl
  mainOfPolys : MainOfPolysK D Fl

/-- **`IdsRemainingK` at the reference shape**, its numeric and deployment bridges proved: `HeapGood`
(`heapGoodK_ref`), `FunctionalsCorrect 15` (`functionalsK_ref`), `2 ≤ h_SHA3`, the degrees `19,339,139`
(`degBoundK_ref`), `187` relations (`relCountK_ref`). -/
theorem idsRemainingK_ref (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (hD : D.shape = keccakRefShape)
    {κ : ℕ} {v : KeccakVariant} (Fl : KFlockSound F κ v) (r : IdsRemainingRefK F D Fl) :
    IdsRemainingK F D Fl 19339139 187 where
  heapGood := hD ▸ heapGoodK_ref
  kvRealizes := r.kvRealizes
  kvConstraints := r.kvConstraints
  cvecOk := r.cvecOk
  functionals := functionalsK_ref D hD
  height2 := height2K_ref D hD
  laneSlots := r.laneSlots
  diffsEval := r.diffsEval
  mainOfPolys := r.mainOfPolys
  degBound := degBoundK_ref D Fl hD
  relCount := relCountK_ref D Fl hD

/-! ## The end theorem at the reference shape -/

/-- **Knowledge soundness of the Keccak verifier (main line) at the reference shape**, at the Keccak code-level
link `uniCodeKAt`: `uniKnowledgeSoundnessK_remaining` with the numeric and deployment bridges, the stacks'
variables and the numbers discharged; from `IdsRemainingRefK`, Flock's result the main line's
(`FlockGoodDoneK`), the weights multilinear off `Z_bad`'s roots (`WeightMleK`), the Fiat–Shamir layer and Flock's
errors. -/
theorem uniKnowledgeSoundnessK_ref (F : KeccakVm.KeccakFlockSpec) (D : KDeployment)
    (hD : D.shape = keccakRefShape) {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (hκ : D.shape.heights.getD opSha3 0 = κ) (hF : KeccakFlockFits F) (r : IdsRemainingRefK F D Fl)
    (hgood : FlockGoodDoneK Fl) (hW : WeightMleK D Fl)
    (hFs : FsLayer128K F D Fl valsCountK (varsOf (layoutsOfK D.shape)) (uniCodeKAt D Fl hκ _ _ rfl rfl))
    (hFl : ∀ j, Fl.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) :
    UniKnowledgeSoundnessKeccak F D (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  uniKnowledgeSoundnessK_remaining F D Fl hκ hF 19339139 187 (idsRemainingK_ref F D hD Fl r) hgood hW
    (layoutVarsSmall3K_ref D hD) hFs hFl (hB_ref D hD) (hdeg_ref D hD) hrel_ref

/-- **Knowledge soundness of the Keccak verifier (main line) at the reference deployment**: as
`uniKnowledgeSoundnessK_ref`, the Fiat–Shamir layer also discharged (`fsLayer128K_refCodeAt`) at leanVM's program
IV, for a Flock phase of at most `987` steps (`nSteps`) and rounds of at most `2^30` scalars. -/
theorem uniKnowledgeSoundnessK_refIv (F : KeccakVm.KeccakFlockSpec) (D : KDeployment)
    (hD : D.shape = keccakRefShape) (hIv : D.programIv = UniStatement.programIv) {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (hκ : D.shape.heights.getD opSha3 0 = κ) (hF : KeccakFlockFits F)
    (r : IdsRemainingRefK F D Fl) (hgood : FlockGoodDoneK Fl) (hW : WeightMleK D Fl)
    (hSteps : Compose.nSteps Fl.prog.rounds ≤ 987) (hFlv : ∀ r ∈ Fl.prog.rounds, r.nv ≤ 2 ^ 30)
    (hFl : ∀ j, Fl.err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) :
    UniKnowledgeSoundnessKeccak F D (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  uniKnowledgeSoundnessK_ref F D hD Fl hκ hF r hgood hW
    (fsLayer128K_refCodeAt D hD hIv Fl hκ valsCountK (varsOf (layoutsOfK D.shape)) rfl rfl
      (by
        have h : varsOf (layoutsOfK D.shape) = 27 := by rw [hD]; exact batchVarsK_ref
        omega) hFlv) hFl

end UniKeccakSound.IdsNum

/-- info: 'UniKeccakSound.IdsNum.idsRemainingK_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.idsRemainingK_ref

/-- info: 'UniKeccakSound.IdsNum.uniKnowledgeSoundnessK_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.uniKnowledgeSoundnessK_ref

/-- info: 'UniKeccakSound.IdsNum.uniKnowledgeSoundnessK_refIv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.uniKnowledgeSoundnessK_refIv
