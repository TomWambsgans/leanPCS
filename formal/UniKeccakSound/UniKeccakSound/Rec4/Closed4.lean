-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The end theorem is `EndClosedK.lean`'s
-- (`uniKnowledgeSoundnessKeccakRec3_closed`) for π1-rec4: `Rec4/End4.lean`'s, its walk discharged by `Rec4/Walk4.lean`.
import UniKeccakSound.Rec4.End4
import UniKeccakSound.Rec4.Walk4

/-!
# Knowledge soundness of π1-rec4 at the reference deployment, closed

**`uniKnowledgeSoundnessKeccakRec4_closed`**: `UniKnowledgeSoundnessKeccakRec4` at the Keccak-f block
`KeccakFlock.keccakFlockSpec`, for every deployment at the reference shape (`keccakRefShape`, 128 signatures) with
leanVM's program IV, the explicit extractor `uniExtractorK`, error `uniBound128 (2^35/|E|) Q`, at most `2^-64` for
`Q ≤ 2^64`, **with no hypothesis**: `Rec4/End4.lean`'s `uniKnowledgeSoundnessKeccakRec4_of_walk` with the walk
(`uniWalkK4`, `uniWalkRejectK4`).
-/

namespace UniKeccakSound

open LeanVM.Parameters UniStatement UniSound UniKeccak
open scoped ENNReal

/-- **Knowledge soundness of the Keccak π1 at π1-rec4's shape at the reference deployment**, the Keccak-f block,
the explicit extractor `uniExtractorK`: error `uniBound128 (2^35/|E|) Q`, at most `2^-64` for `Q ≤ 2^64`. No
hypothesis. -/
theorem uniKnowledgeSoundnessKeccakRec4_closed (D : KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv = UniStatement.programIv) :
    UniKnowledgeSoundnessKeccakRec4 KeccakFlock.keccakFlockSpec D
        (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  Rec4.uniKnowledgeSoundnessKeccakRec4_of_walk D hD hIv (fun _ _ => Rec4.uniWalkK4 D 15 valsCountK 13 _)
    (Rec4.uniWalkRejectK4 D 15 valsCountK 13 (uniCodeK4At D (KF.kFlockSoundRec3 KeccakFlock.keccakFlockSpec
      (KF.terminalSpecK_of_bridge KF.structuredTerminalBridge) 15) rfl (hSha3K_ref D hD) valsCountK 13 rfl
      (by rw [hD, varsOf_ref])))

end UniKeccakSound

/-- info: 'UniKeccakSound.uniKnowledgeSoundnessKeccakRec4_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniKnowledgeSoundnessKeccakRec4_closed
