-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniKeccakSound.Ids.Remaining
import UniKeccakSound.Ids3.Remaining3
import UniKeccakSound.IdsW.WeightMle
import UniKeccakSound.IdsReal.Realize
import UniKeccakSound.IdsReal.LaneSlots
import UniKeccakSound.Flock.Bridge
import UniKeccakSound.Fs.LayerK
import UniKeccakSound.Fs.LayerK3
import UniKeccak.Fits
import UniKeccakSound.IdsMain.Discharge
import UniKeccakSound.IdsNum.Numbers

/-!
# The Keccak verifier's knowledge soundness at the reference shape, both shapes, Flock and the links in place

The end statements `UniKnowledgeSoundnessKeccak` (main line) and `UniKnowledgeSoundnessKeccakRec3` (π1-rec3's shape)
at the Keccak-f block `KeccakFlock.keccakFlockSpec`, for every deployment at the reference shape (`keccakRefShape`,
128 signatures) with leanVM's program IV, with everything in place but one bridge of the identity model,
`DiffsEvalK` (`KRemainingRef`: the verifier's relations at `t`, all zero, give every identity at `t`):

* Flock on the Keccak-f block: `KF.flockSoundK_main_closed 15`, `KF.flockSoundK_rec3_closed 15` (`Flock/`), their
  errors, `FlockGoodDoneK`, their rounds' numbers;
* the code-level links `uniCodeKAt`, `uniCodeK3At` (`Code/`), the Fiat–Shamir layers `fsLayer128K_refCodeAt`,
  `fsLayer128K3_refCodeAt` (`Fs/`, the setup's `2^23`-word WHIR opening certified at `269 · 2^-137`);
* the identity models and the last links (`Ids/`, `Ids3/`), with `WeightMleK` (`IdsW/`), `KvRealizesK` and
  `LaneSlotsK` (`IdsReal/`), `MainOfPolysK`, `CvecOkK`, `KvConstraintsK` (`IdsMain/`), `DegBoundK`, `RelCountK`,
  `HeapGood`, `FunctionalsCorrect 15` and the numbers (`IdsNum/`), the bus count, `AuxOfFlockK`, `DiffsFlockK`,
  `KeccakFlockFits` proved.
-/

namespace UniKeccakSound

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak UniKeccakSound.Ids UniKeccakSound.KF
open scoped ENNReal

/-- `h_SHA3 = 15` at the reference shape. -/
theorem hSha3K_ref (D : KDeployment) (hD : D.shape = keccakRefShape) : D.shape.heights.getD opBlake2s 0 = 15 := by
  rw [hD]
  decide +kernel

/-- `varsOf (layoutsOfK ·) = 27` at the reference shape: the largest of `C1`'s `27`, `C2`'s `26`, the setup's `23`. -/
theorem varsOf_ref : varsOf (layoutsOfK keccakRefShape) = 27 := by
  have e : varsOf (layoutsOfK keccakRefShape) = max (max (max 0 (c1LayoutK keccakRefShape).vars)
      (StackLayout.new (Shape.c2ColumnsK keccakRefShape)).vars) (setupLayout keccakRefShape).vars := rfl
  rw [e, c1Vars_ref, c2Vars_ref, setupVars_ref]
  rfl

/-- The identity model's deployment facts at the reference shape (`MainDeployK`). -/
theorem mainDeployK_ref (D : KDeployment) (hD : D.shape = keccakRefShape) : MainDeployK D where
  heap := by rw [hD]; exact IdsNum.heapGoodK_ref
  functionals := IdsNum.functionalsK_ref D hD
  height2 := IdsNum.height2K_ref D hD
  rW := by rw [hD]; decide +kernel
  heightsLt := by rw [hD]; decide +kernel

/-- **What remains**: the bridge `DiffsEvalK` (the verifier's relations at `t`, all zero, give every identity at
`t`) for the main line's and π1-rec3's Flock instances at `κ = 15`. -/
def KRemainingRef (D : KDeployment) : Prop :=
  DiffsEvalK D (flockSoundK_main_closed 15) ∧ DiffsEvalK D (flockSoundK_rec3_closed 15)

/-- `IdsRemainingK` at the reference shape from `DiffsEvalK`. -/
theorem idsRemainingK_refOf (D : KDeployment) (hD : D.shape = keccakRefShape) {v : KeccakVariant}
    (Fl : KFlockSound KeccakFlock.keccakFlockSpec 15 v) (hE : DiffsEvalK D Fl) :
    IdsRemainingK KeccakFlock.keccakFlockSpec D Fl 19339139 187 :=
  idsRemainingK_of _ D Fl (mainDeployK_ref D hD) IdsReal.laneSlotsK
    (IdsReal.kvRealizesK D (mainDeployK_ref D hD).heap) hE (IdsNum.degBoundK_ref D Fl hD)
    (IdsNum.relCountK_ref D Fl hD)

/-- **Knowledge soundness of the Keccak verifier (main line) at the reference shape**, the Keccak-f block, the
explicit extractor `uniExtractorK`: error `uniBound128 (2^32/|E|) Q`, at most `2^-64` for `Q ≤ 2^64`; from the one
named bridge `DiffsEvalK` (`KRemainingRef`). -/
theorem uniKnowledgeSoundnessKeccak_closed_of (D : KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv = UniStatement.programIv) (r : KRemainingRef D) :
    UniKnowledgeSoundnessKeccak KeccakFlock.keccakFlockSpec D
        (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 := by
  have hκ := hSha3K_ref D hD
  have hV : varsOf (layoutsOfK D.shape) = 27 := by rw [hD]; exact varsOf_ref
  exact uniKnowledgeSoundnessK_remaining KeccakFlock.keccakFlockSpec D (flockSoundK_main_closed 15) hκ
    keccakFlockFits_keccakFlockSpec 19339139 187 (idsRemainingK_refOf D hD _ r.1)
    (fun fd h ↦ flockSoundK_main_closed_good 15 fd h) (weightMleK_of D _ hκ) (IdsNum.layoutVarsSmall3K_ref D hD)
    (fsLayer128K_refCodeAt D hD hIv _ hκ _ _ rfl rfl (by rw [hV]; exact flockSoundK_main_closed_nSteps)
      (flockSoundK_main_closed_nv 15))
    (flockSoundK_main_closed_err_le 15 (by norm_num)) (IdsNum.hB_ref D hD) (IdsNum.hdeg_ref D hD)
    IdsNum.hrel_ref

/-- **Knowledge soundness of the Keccak π1 at π1-rec3's shape at the reference shape**, the Keccak-f block, the
explicit extractor `uniExtractorK`: error `uniBound128 (2^35/|E|) Q`, at most `2^-64` for `Q ≤ 2^64`; from the one
named bridge `DiffsEvalK` (`KRemainingRef`). -/
theorem uniKnowledgeSoundnessKeccakRec3_closed_of (D : KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv = UniStatement.programIv) (r : KRemainingRef D) :
    UniKnowledgeSoundnessKeccakRec3 KeccakFlock.keccakFlockSpec D
        (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 := by
  have hκ := hSha3K_ref D hD
  have hV : varsOf (layoutsOfK D.shape) = 2 * 13 + 1 := by rw [hD, varsOf_ref]
  have h13 : Compose.nSteps (flockSoundK_rec3_closed 15).prog.rounds + 13 ≤ 1016 := by
    have := flockSoundK_rec3_closed_nSteps
    omega
  exact uniKnowledgeSoundnessK3_remaining_ref KeccakFlock.keccakFlockSpec D hD hIv (flockSoundK_rec3_closed 15) hκ
    keccakFlockFits_keccakFlockSpec 13 hV 19339139 187 (idsRemainingK_refOf D hD _ r.2)
    (fun fd h ↦ flockSoundK_rec3_closed_good 15 fd h) (weightMleK_of D _ hκ) (IdsNum.layoutVarsSmall3K_ref D hD)
    h13 (flockSoundK_rec3_closed_nv 15) (flockSoundK_rec3_closed_err_le 15 (by norm_num))
    (IdsNum.hB35_ref D hD) (IdsNum.hdeg35_ref D hD) IdsNum.hrel35_ref

end UniKeccakSound
