-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The assembly is the Keccak main line's
-- (`Ids/Assembly.lean`, `Ids/Remaining.lean`) at π1-rec3's shape, as `UniSound/Rec3/{Final128_3,Closed128_3}.lean`.
import UniKeccakSound.Ids3.Final3
import UniKeccakSound.Ids.Remaining
import UniKeccakSound.Fs.LayerK3

/-!
# Knowledge soundness of the Keccak verifier at π1-rec3's shape, from what remains

* **`uniKnowledgeSoundnessK3_ids`**: `FinalK3.lean`'s `uniKnowledgeSoundnessK3_bits` at the identity model `uniIdsK3`
  (from the main line's bridges `IdsHypsK` and reductions `IdsGapsK`, at `F3`), the paired batch `pairBatchRec3 np`,
  the code-level link `uniCodeK3At` (`Code/Link3.lean`) and the last link `uniFinalK3_uniCodeK3At`, at
  `e = 2^35 / |E|`: round `0` `16 N + ncv ≤ 2^35` (the bus with squares), `d + zBadDeg ≤ 2^35`, `max n 1 + 2 ≤ 2^35`.
* **`uniKnowledgeSoundnessK3_remaining`**: the same from **the main line's named bridges, unchanged**:
  `IdsRemainingK F D F3 d n` (the main line's structure, at π1-rec3's Flock phase: its fields are stated for Flock's
  phase of any variant), `FlockGoodDoneK F3`, `WeightMleK D F3`, `LayoutVarsSmall3K D`; the bus count, the Keccak-f
  region and the ring switch's claim are the main line's proofs (`idsHypsK_of`, `idsGapsK_of`). No bridge specific
  to π1-rec3 remains: round `0` with squares (`BusModelK.mainSoundSq`), the paired batch's last state
  (`uniFinalK3_uniCodeK3At`) and the code-level link are proved.
* **`uniKnowledgeSoundnessK3_remaining_ref`**: at the reference deployment (the 128-signature shape, leanVM's program
  IV), the Fiat–Shamir layer discharged by `Fs/LayerK3.lean`'s `fsLayer128K3_refCodeAt`, leaving Flock's rounds'
  numbers (`nSteps F3.prog.rounds + np ≤ 1016`, each round at most `2^30` scalars).
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak
open scoped ENNReal

/-- **Knowledge soundness of the Keccak verifier at π1-rec3's shape** at the code-level link `uniCodeK3At`, with the
identity model `uniIdsK3` from the main line's bridges `h` and reductions `g` (at `F3`), at `e = 2^35 / |E|`. -/
theorem uniKnowledgeSoundnessK3_ids (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hκ : D.shape.heights.getD opBlake2s 0 = κ) (N : ℕ) (h : IdsHypsK F D κ N)
    (d n : ℕ) (g : IdsGapsK D F3 d n) (np : ℕ) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1)
    (hgood : FlockGoodDoneK F3) (hW : WeightMleK D F3) (hsmall : LayoutVarsSmall3K D)
    (hFs : FsLayer128K3 F D F3 valsCountK np (uniCodeK3At D F3 hκ valsCountK np rfl hV))
    (hFl : ∀ j, F3.err j ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hB : 16 * N + ncvK D.shape ≤ 2 ^ 35) (hdeg : d + zBadDeg D.shape ≤ 2 ^ 35) (hrel : max n 1 + 2 ≤ 2 ^ 35) :
    UniKnowledgeSoundnessKeccakRec3 F D (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  have hn := uniIdsK3_numbers D F3 N h d n g np hV hB hdeg hrel
  uniKnowledgeSoundnessK3_bits F3 (uniIdsK3 D F3 N h d n g np hV) (pairBatchRec3 np)
    (uniCodeK3At D F3 hκ _ np rfl hV)
    (uniFinalK3_uniCodeK3At D F3 hκ N h d n g np hV hgood hW hsmall) hFs hn.1 hFl hn.2.1 hn.2.2
    (pairBatchRec3_errPair np) (pairBatchRec3_errLast np)

/-- **Knowledge soundness of the Keccak verifier at π1-rec3's shape** at the code-level link `uniCodeK3At`, with the
identity model built from what remains (`IdsRemainingK`, the main line's named bridges at `F3`), for a Keccak-f block
whose ports are the verifier's (`KeccakFlockFits F`) and Flock's phase at `κ = h_SHA3`. -/
theorem uniKnowledgeSoundnessK3_remaining (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hκ : D.shape.heights.getD opBlake2s 0 = κ) (hF : KeccakFlockFits F)
    (np : ℕ) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) (d n : ℕ) (r : IdsRemainingK F D F3 d n)
    (hgood : FlockGoodDoneK F3) (hW : WeightMleK D F3) (hsmall : LayoutVarsSmall3K D)
    (hFs : FsLayer128K3 F D F3 valsCountK np (uniCodeK3At D F3 hκ valsCountK np rfl hV))
    (hFl : ∀ j, F3.err j ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hB : 16 * busBoundK D.shape + ncvK D.shape ≤ 2 ^ 35) (hdeg : d + zBadDeg D.shape ≤ 2 ^ 35)
    (hrel : max n 1 + 2 ≤ 2 ^ 35) :
    UniKnowledgeSoundnessKeccakRec3 F D (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  uniKnowledgeSoundnessK3_ids D F3 hκ (busBoundK D.shape) (idsHypsK_of F D F3 hκ hF r) d n
    (idsGapsK_of F D F3 hκ r) np hV hgood hW hsmall hFs hFl hB hdeg hrel

/-- **Knowledge soundness of the Keccak verifier at π1-rec3's shape at the reference deployment** (the 128-signature
shape `keccakRefShape`, leanVM's program IV, any `A0`, `B0`), from what remains: the main line's named bridges at
`F3`, and Flock's rounds' numbers (the Fiat–Shamir layer is `fsLayer128K3_refCodeAt`). -/
theorem uniKnowledgeSoundnessK3_remaining_ref (F : KeccakVm.KeccakFlockSpec) (D : KDeployment)
    (hD : D.shape = keccakRefShape) (hIv : D.programIv = UniStatement.programIv) {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hκ : D.shape.heights.getD opBlake2s 0 = κ) (hF : KeccakFlockFits F)
    (np : ℕ) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1) (d n : ℕ) (r : IdsRemainingK F D F3 d n)
    (hgood : FlockGoodDoneK F3) (hW : WeightMleK D F3) (hsmall : LayoutVarsSmall3K D)
    (hFlR : Compose.nSteps F3.prog.rounds + np ≤ 1016) (hFlv : ∀ r ∈ F3.prog.rounds, r.nv ≤ 2 ^ 30)
    (hFl : ∀ j, F3.err j ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))
    (hB : 16 * busBoundK D.shape + ncvK D.shape ≤ 2 ^ 35) (hdeg : d + zBadDeg D.shape ≤ 2 ^ 35)
    (hrel : max n 1 + 2 ≤ 2 ^ 35) :
    UniKnowledgeSoundnessKeccakRec3 F D (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  uniKnowledgeSoundnessK3_remaining F D F3 hκ hF np hV d n r hgood hW hsmall
    (fsLayer128K3_refCodeAt D hD hIv F3 hκ valsCountK np rfl hV hFlR hFlv) hFl hB hdeg hrel

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.uniKnowledgeSoundnessK3_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.uniKnowledgeSoundnessK3_remaining

/-- info: 'UniKeccakSound.Ids.uniKnowledgeSoundnessK3_remaining_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.uniKnowledgeSoundnessK3_remaining_ref
