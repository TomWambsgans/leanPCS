-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniKeccakSound.FinalK
import UniKeccakSound.FinalK3
import UniSound.Rec3.Batch3
import KeccakFlock
import UniSound.Ids.Facts
import FlockSoundUni.Transcription

/-!
# The Keccak verifier's knowledge soundness at the Keccak-f block, from the named links that remain

The end statements of `formal/UniKeccak` (`UniKnowledgeSoundnessKeccak`, `UniKnowledgeSoundnessKeccakRec3`) at the
Keccak-f block's inhabitant `F = KeccakFlock.keccakFlockSpec`, from `FinalK.lean`'s and `FinalK3.lean`'s compositions
(the PIOPs `uniPiopK`, `uniPiopK3` proved round by round, the bound in bits proved), with the links that are not yet
proved as **named `Prop`s**:

* `KFlockP F κ v e`: Flock's interface on the Keccak-f block (`KFlockSound F κ v`) with every round's error at most
  `e`;
* `KLinksP F D Fl`: for a Flock interface `Fl` of the main line, the identity model, the code-level link, the last
  link and the Fiat–Shamir layer, with the identity model's numbers;
* `KLinksP3 F D F3`: the same at π1-rec3's shape, with π1-rec3's batch `pairBatchRec3`.

The reference Keccak shape is `keccakRef`, the 128-signature run (`keccakShapeNamed "keccak128"`: heights
`15 16 15 16 14 15`, memory `2^20`, bytecode `2^18`; `C1` `2^27` words, `C2` `2^26`, the setup `2^23`).
-/

namespace UniKeccakSound

open LeanVM.Parameters UniStatement UniSound UniKeccak
open scoped ENNReal

/-- **The reference Keccak shape**: leanVM 9d50c92a3's Keccak VM at 128 signatures (`keccakRuns`' `keccak128`: the
memory `⌈log₂ 721598⌉ = 20`, the bytecode `2^18`, the rows XOR, MUL, SET, DEREF, JUMP, SHA3). -/
def keccakRef : Shape := keccakShapeOf 721598 [24260, 36229, 24626, 35812, 15509, 17712]

/-- `2^32 / |E|`. -/
noncomputable abbrev e32 : ℝ≥0∞ := ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)

/-- `2^35 / |E|`. -/
noncomputable abbrev e35 : ℝ≥0∞ := ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)

/-- **Remaining: Flock on the Keccak-f block** (variant `v`, `q_flock` of `2^(11 + κ)` cells): an interface
`KFlockSound F κ v` whose rounds err at most `e`. -/
def KFlockP (F : KeccakVm.KeccakFlockSpec) (κ : ℕ) (v : KeccakVariant) (e : ℝ≥0∞) : Prop :=
  ∃ Fl : KFlockSound F κ v, ∀ j, Fl.err j ≤ e

/-- **Remaining: the main line's links** for the Flock interface `Fl`: an identity model `I`, a code-level link `C`,
the last link and the Fiat–Shamir layer, the identity model's numbers. -/
def KLinksP (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) {κ : ℕ} (Fl : KFlockSound F κ keccakMain) : Prop :=
  ∃ (I : UniIdsK F D Fl) (C : UniCodeK D Fl I.nV I.V), UniFinalK D Fl I C ∧ FsLayer128K F D Fl I.nV I.V C ∧
    I.errMain ≤ e32 ∧ I.degSum + I.degBad ≤ 2 ^ 32 ∧ I.nRel + 2 ≤ 2 ^ 32

/-- **Remaining: π1-rec3's links** for the Flock interface `F3`: an identity model `I` with `np` pair rounds, a
code-level link `C`, the last link with π1-rec3's batch `pairBatchRec3 np` and the Fiat–Shamir layer, the numbers. -/
def KLinksP3 (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) : Prop :=
  ∃ (np : ℕ) (I : UniIdsK3 F D F3 np) (C : UniCodeK3 D F3 I.nV np), UniFinalK3 D F3 I (pairBatchRec3 np) C ∧
    FsLayer128K3 F D F3 I.nV np C ∧ I.errMain ≤ e35 ∧ I.degSum + I.degBad ≤ 2 ^ 35 ∧ I.nRel + 2 ≤ 2 ^ 35

/-- **Knowledge soundness of the Keccak verifier (main line) at the Keccak-f block**, error
`uniBound128 (2^32/|E|) Q ≤ 2^-64` for `Q ≤ 2^64`, from the named links `KFlockP` and `KLinksP`. -/
theorem uniKnowledgeSoundnessKeccak_of (D : KDeployment)
    (hFl : KFlockP KeccakFlock.keccakFlockSpec (D.shape.heights.getD opBlake2s 0) keccakMain e32)
    (hL : ∀ Fl : KFlockSound KeccakFlock.keccakFlockSpec (D.shape.heights.getD opBlake2s 0) keccakMain,
      KLinksP KeccakFlock.keccakFlockSpec D Fl) :
    UniKnowledgeSoundnessKeccak KeccakFlock.keccakFlockSpec D (uniBound128 e32) ∧
      ∀ Q ≤ 2 ^ 64, uniBound128 e32 Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 := by
  obtain ⟨Fl, hFle⟩ := hFl
  obtain ⟨I, C, hFin, hFs, hMain, hdeg, hrel⟩ := hL Fl
  exact uniKnowledgeSoundnessK_bits Fl I C hFin hFs hMain hFle hdeg hrel

/-- **Knowledge soundness of the Keccak π1 at π1-rec3's shape at the Keccak-f block**, error
`uniBound128 (2^35/|E|) Q ≤ 2^-64` for `Q ≤ 2^64`, from the named links `KFlockP` and `KLinksP3`. -/
theorem uniKnowledgeSoundnessKeccakRec3_of (D : KDeployment)
    (hFl : KFlockP KeccakFlock.keccakFlockSpec (D.shape.heights.getD opBlake2s 0) keccakRec3 e35)
    (hL : ∀ F3 : KFlockSound KeccakFlock.keccakFlockSpec (D.shape.heights.getD opBlake2s 0) keccakRec3,
      KLinksP3 KeccakFlock.keccakFlockSpec D F3) :
    UniKnowledgeSoundnessKeccakRec3 KeccakFlock.keccakFlockSpec D (uniBound128 e35) ∧
      ∀ Q ≤ 2 ^ 64, uniBound128 e35 Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 := by
  obtain ⟨F3, hFle⟩ := hFl
  obtain ⟨np, I, C, hFin, hFs, hMain, hdeg, hrel⟩ := hL F3
  exact uniKnowledgeSoundnessK3_bits F3 I (pairBatchRec3 np) C hFin hFs hMain hFle hdeg hrel
    (pairBatchRec3_errPair np) (pairBatchRec3_errLast np)

end UniKeccakSound
