-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The composition follows `FinalK3.lean`'s
-- (`uniKnowledgeSoundnessK3_bits`), `Ids3/Remaining3.lean`'s and `EndClosedK.lean`'s (`uniKnowledgeSoundnessKeccakRec3_closed`).
import UniKeccakSound.Rec4.Final4
import UniKeccakSound.Rec4.Couple4
import UniKeccakSound.Rec4.Game4
import UniKeccakSound.EndClosedK

/-!
# Knowledge soundness of π1-rec4

* **`uniKnowledgeSoundnessK4_ids`**: `UniKnowledgeSoundnessKeccakRec4 F D (uniBound128 (2^35/|E|))` from the
  Fiat–Shamir layer at the code-level link `uniCodeK4At` (`FsLayer128K4`), for Flock on the Keccak-f block
  `KF.kFlockSoundRec3 F hT κ`, the identity model `uniIdsK3` (π1-rec3's) and the paired batch, π1-rec4's PIOP
  (`uniPiopK4`), its last link (`uniFinalK4`), every round's error at most `2^35/|E|`;
* **`uniKnowledgeSoundnessKeccakRec4_of_walk`**: at the reference deployment (the 128-signature shape, leanVM's
  program IV) and the Keccak-f block, from the walk of `uniCodeK4At` (`UniWalkK4`, `UniWalkRejectK4`): the
  Fiat–Shamir layer is `fsLayer128K4_of_gameV'` with the coupling `uniGameLeVK4_holds`, the identity model's bridges
  and numbers are π1-rec3's (`idsRemainingK_ref`, `IdsNum`).
-/

namespace UniKeccakSound.Rec4

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak UniKeccakSound.Ids Finset
open scoped ENNReal

section Ids

/-- **Round `0`'s error at π1-rec4**: the bus's and the constraints' (`errMainSq`) and Flock's first round's. -/
theorem errMain4_le (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (hT : KF.TerminalSpecK F)
    (_hκ : D.shape.heights.getD opSha3 0 = κ) (N : ℕ) (h : IdsHypsK F D κ N) (d n : ℕ)
    (g : IdsGapsK D (KF.kFlockSoundRec3 F hT κ) d n) (np : ℕ) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1)
    (hB : 16 * N + ncvK D.shape + (2 ^ (7 + κ) + 90) ≤ 2 ^ 35) :
    (uniIdsK3 D (KF.kFlockSoundRec3 F hT κ) N h d n g np hV).errMain + (KF.kFlockSoundRec3 F hT κ).err 0 ≤
      ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have hf := KF.kFlockSoundRec3_err_le' F hT κ 0
  show ((16 * N : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) + ((ncvK D.shape - 1 : ℕ) : ℝ≥0∞) /
      (Fintype.card E : ℝ≥0∞) + (KF.kFlockSoundRec3 F hT κ).err 0 ≤ _
  refine (add_le_add le_rfl hf).trans ?_
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ← Nat.cast_add, ← Nat.cast_add]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (by omega)) _

/-- **Knowledge soundness of π1-rec4** at the code-level link `uniCodeK4At`, with the identity model `uniIdsK3`, the
paired batch, every round's error at most `2^35/|E|`: from the Fiat–Shamir layer. -/
theorem uniKnowledgeSoundnessK4_ids (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (hT : KF.TerminalSpecK F)
    (hκ : D.shape.heights.getD opSha3 0 = κ) (N : ℕ) (h : IdsHypsK F D κ N) (d n : ℕ)
    (g : IdsGapsK D (KF.kFlockSoundRec3 F hT κ) d n) (np : ℕ) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1)
    (hgood : FlockGoodDoneK (KF.kFlockSoundRec3 F hT κ)) (hW : WeightMleK D (KF.kFlockSoundRec3 F hT κ))
    (hsmall : LayoutVarsSmall3K D)
    (hFs : FsLayer128K4 F D κ valsCountK np
      (uniCodeK4At D (KF.kFlockSoundRec3 F hT κ) rfl hκ valsCountK np rfl hV))
    (hFl : ∀ j, (KF.kFlockSoundRec3 F hT κ).err j ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hB : 16 * N + ncvK D.shape + (2 ^ (7 + κ) + 90) ≤ 2 ^ 35) (hdeg : d + zBadDeg D.shape + 60 ≤ 2 ^ 35)
    (hrel : max n 1 + 31 ≤ 2 ^ 35) :
    UniKnowledgeSoundnessKeccakRec4 F D (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 := by
  refine ⟨hFs (uniPiopK4 hT (uniIdsK3 D (KF.kFlockSoundRec3 F hT κ) N h d n g np hV) (pairBatchRec3 np)
      (fun fd x y hfd => hzb_uniIdsK3 D hT N h d n g np hV fd x y hfd)
      (fun s c1 ch fd x y c2 hfd => hpolys_uniIdsK3 D hT N h d n g np hV s c1 ch fd x y c2 hfd)) _
    (uniErrK4_le hT _ (pairBatchRec3 np) _ (errMain4_le D hT hκ N h d n g np hV hB) hFl ?_ ?_
      (pairBatchRec3_errPair np) (pairBatchRec3_errLast np))
    (fun s c m hp => hpre_uniPiopK4 hT _ _ _ _ s c m hp)
    (fun s done tl c1 c2 hd htl hz hc => uniFinalK4 D hT hκ N h d n g np hV hgood hW hsmall s done tl c1 c2 hd htl
      hz hc), uniBound128_le_bits35⟩
  · rw [ENNReal.div_add_div_same, ← Nat.cast_add]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr (show d + zBadDeg D.shape + 60 ≤ 2 ^ 35 from hdeg)) _
  · rw [ENNReal.div_add_div_same, ← Nat.cast_add]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr (show max n 1 - 1 + (3 - 1) + 30 ≤ 2 ^ 35 by omega)) _

end Ids

/-! ## At the reference deployment -/

/-- π1-rec4's rounds at the reference: at most `2^30` scalars each. -/
theorem rec4Rounds_nv_ref : ∀ r ∈ rec4Rounds 15 valsCountK 13, r.nv ≤ 2 ^ 30 := by
  have hv : valsCountK ≤ 2 ^ 30 := by rw [valsCountK_eq]; norm_num
  intro r hr
  simp only [rec4Rounds, kRoundsMid, List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil,
    or_false] at hr
  rcases hr with (((((((h | h | h | h) | h) | h) | h) | h | h) | h) | h) <;> aesop

/-- **Knowledge soundness of π1-rec4 at the reference deployment**, the Keccak-f block, the explicit extractor
`uniExtractorK`: error `uniBound128 (2^35/|E|) Q`, at most `2^-64` for `Q ≤ 2^64`, from the walk of the code-level
link `uniCodeK4At` (`UniWalkK4`, `UniWalkRejectK4`). -/
theorem uniKnowledgeSoundnessKeccakRec4_of_walk (D : KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv = UniStatement.programIv)
    (hWk : ∀ (hκ : D.shape.heights.getD opSha3 0 = 15) (hV : varsOf (layoutsOfK D.shape) = 2 * 13 + 1),
      UniWalkK4 D 15 valsCountK 13 (uniCodeK4At D (KF.kFlockSoundRec3 KeccakFlock.keccakFlockSpec
        (KF.terminalSpecK_of_bridge KF.structuredTerminalBridge) 15) rfl hκ valsCountK 13 rfl hV))
    (hRk : UniWalkRejectK4 D 15 valsCountK 13) :
    UniKnowledgeSoundnessKeccakRec4 KeccakFlock.keccakFlockSpec D
        (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 := by
  have hκ := hSha3K_ref D hD
  have hV : varsOf (layoutsOfK D.shape) = 2 * 13 + 1 := by rw [hD, varsOf_ref]
  set hT := KF.terminalSpecK_of_bridge KF.structuredTerminalBridge
  set F3 := KF.kFlockSoundRec3 KeccakFlock.keccakFlockSpec hT 15
  have r := idsRemainingK_ref D hD F3
  have hs := uniShapesK_ref D hD
  have hFs : FsLayer128K4 KeccakFlock.keccakFlockSpec D 15 valsCountK 13 (uniCodeK4At D F3 rfl hκ valsCountK 13 rfl hV) :=
    fsLayer128K4_of_gameV' D 15 valsCountK 13 _ hs (by rw [uSpec4_nQ]; norm_num) rec4Rounds_nv_ref
      (uniIvK_programIv D hIv)
      (uniGameLeVK4_holds D _ 15 valsCountK 13 _ hs (layoutVarsSmallK_ref D hD) (hWk hκ hV) hRk
        (uniOutRootsK4_uniCodeK4At D F3 rfl hκ valsCountK 13 rfl hV))
  have hB : 16 * busBoundK D.shape + ncvK D.shape + (2 ^ (7 + 15) + 90) ≤ 2 ^ 35 := by
    have := IdsNum.hB_ref D hD
    rw [show (2 : ℕ) ^ (7 + 15) = 4194304 by norm_num, show (2 : ℕ) ^ 35 = 34359738368 by norm_num]
    rw [show (2 : ℕ) ^ 32 = 4294967296 by norm_num] at this
    omega
  have hdeg : 19339139 + zBadDeg D.shape + 60 ≤ 2 ^ 35 := by
    have := IdsNum.hdeg_ref D hD
    rw [show (2 : ℕ) ^ 35 = 34359738368 by norm_num]
    rw [show (2 : ℕ) ^ 32 = 4294967296 by norm_num] at this
    omega
  exact uniKnowledgeSoundnessK4_ids D hT hκ (busBoundK D.shape) (idsHypsK_of _ D F3 hκ keccakFlockFits_keccakFlockSpec r)
    19339139 187 (idsGapsK_of _ D F3 hκ r) 13 hV (fun fd h ↦ KF.flockSoundK_rec3_closed_good 15 fd h)
    (weightMleK_of D _ hκ) (IdsNum.layoutVarsSmall3K_ref D hD) hFs
    (KF.flockSoundK_rec3_closed_err_le 15 (by norm_num)) hB hdeg (by norm_num)

end UniKeccakSound.Rec4

/-- info: 'UniKeccakSound.Rec4.uniKnowledgeSoundnessKeccakRec4_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.uniKnowledgeSoundnessKeccakRec4_of_walk
