-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The main line's `FsGame.lean` (`fsLayer_of_gameV`)
-- for π1-rec3: its IV (`UniStatement.Deployment.ivRec3With`, `contractIvForWith … .rec3 true`) and its three
-- openings.
import UniSound.Rec3.FsProof3
import UniSound.FsGame

/-!
# π1-rec3's Fiat–Shamir layer, the contract's IV computed by the verifier

`FsGame.lean` for π1-rec3:

* **The IV** (`ivInput3`): π1-rec3's contract IV hashes the main line's preimage (`ivInput`) with the variant
  bytes appended (`rec3Extra = variantBytes (.flock flockMain) .rec3 true`: `fs-rec3`, the skip `3`, the slices'
  code `4`, nine bytes), so its input has `D.programIv.length + 289` bytes; **`UniIv3`** asks it neither a leaf's
  `512` (`D.programIv.length ≠ 223`) nor more than eight calls of `π` (`D.programIv.length ≤ 798`). The reference
  program IV has `32` bytes.
* **`uVerIv3`**: the IV (`ivKC3`, one Keccak-256 call), then the composed verifier (the chain on `rec3Rounds`, the
  three openings) on the proof carrying it; **`UniGameLeV3`**, the coupling with π1-rec3's experiment
  (`uniSoundnessExperimentRec3`), the same adversary log on both sides.
* **`fsLayer3_of_gameV`**: `FsLayer3` from `UniGameLeV3`, `UniNumbers3` and `UniIv3`, through `rpm_le_kcS`, the IV
  moved into the two-oracle adversary (`expU_ivAdv3`; its log entry leaves `C1`'s word, `extractorK_append`), the
  two-oracle theorem, and the bound `uniBound3` (`le_uniBoundV3`: three doom terms).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack

/-! ## π1-rec3's IV -/

/-- **π1-rec3's variant bytes** (`variant_bytes` at `FLOCK_REC3`): `fs-rec3`, the skip, the slices' code. -/
def rec3Extra : List UInt8 := variantBytes (.flock flockMain) .rec3 true

theorem length_rec3Extra : rec3Extra.length = 9 := by decide +kernel

theorem rec3Extra_isEmpty : rec3Extra.isEmpty = false := by decide +kernel

/-- **π1-rec3's IV input** (`contractIvForWith … .rec3 true`): the main line's, then the variant bytes. -/
def ivInput3 (D : Deployment) (roots : SetupRoots) : List UInt8 := ivInput D roots ++ rec3Extra

theorem length_ivInput3 (D : Deployment) (roots : SetupRoots) :
    (ivInput3 D roots).length = D.programIv.length + 289 := by
  rw [ivInput3, List.length_append, length_ivInput, length_rec3Extra]

theorem ivRec3With_eq' {m : Type → Type} [Monad m] [LawfulMonad m]
    (F : LeanVM.Semantics.KeccakState → m LeanVM.Semantics.KeccakState) (D : Deployment) (roots : SetupRoots) :
    D.ivRec3With F roots = digestBytes <$> keccak256With F (ivInput3 D roots) := by
  unfold Deployment.ivRec3With contractIvForWith
  rw [map_eq_bind_pure_comp]
  show (if rec3Extra.isEmpty then _ else _) = _
  rw [rec3Extra_isEmpty]
  rfl

/-- **The Statement's IV is the composed one**, Keccak-256 over `π`. -/
theorem ivRec3With_eq (D : Deployment) (roots : SetupRoots) :
    D.ivRec3With Common.queryPermutation roots =
      (fun b : Bytes32 => b.toList) <$>
        simulateQ keccakCallsOverQueryPermutation (hash256 (ivInput3 D roots)) := by
  rw [ivRec3With_eq', hash256, callKeccak256, simulateQ_bind, simulateQ_spec_query, map_bind]
  simp only [simulateQ_pure, map_pure, Bridge.toB_toList]
  rw [map_eq_bind_pure_comp]
  rfl

/-- **π1-rec3's deployment IV is short and of no Merkle length**: its input (`D.programIv.length + 289` bytes) not a
leaf's `512`, and at most eight calls of `π` (`≤ 1087` bytes). -/
structure UniIv3 (D : Deployment) : Prop where
  ne : D.programIv.length ≠ 223
  le : D.programIv.length ≤ 798

/-- **The IV as the composed verifier computes it**: one Keccak-256 call of its input. -/
def ivKC3 (D : Deployment) (π : UPf) : OracleComp KeccakCalls Bytes32 := hash256 (ivInput3 D π.roots)

/-! ## The IV moved into the adversary, in the two-oracle game -/

/-- The two-oracle adversary with π1-rec3's IV: `A₀`, then the IV of the proof the setup fixes. -/
def ivAdv3 (D : Deployment) (A₀ : Bytes32 × Bytes32 × Bytes32 → OracleComp KeccakCalls UPf)
    (s : Bytes32 × Bytes32 × Bytes32) : OracleComp KeccakCalls UPf :=
  A₀ s >>= fun π => (fun iv => setIv iv π) <$> ivKC3 D (uFix s π)

theorem isTotalQueryBound_ivAdv3 (D : Deployment)
    (A₀ : Bytes32 × Bytes32 × Bytes32 → OracleComp KeccakCalls UPf) (n : ℕ)
    (h : ∀ s, IsTotalQueryBound (A₀ s) n) (s : Bytes32 × Bytes32 × Bytes32) :
    IsTotalQueryBound (ivAdv3 D A₀ s) (n + 1) := by
  unfold ivAdv3
  refine isTotalQueryBound_bind (h s) fun π => (isQueryBound_map_iff _ _ _ _ _).mpr ?_
  simp only [ivKC3, hash256, callKeccak256]
  exact isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩

/-! ## The bound -/

/-- **The composed bound, the IV in the verifier, is at most `uniBound3`**: `le_uniBound3` with the adversary's
`Q + 8` calls and `2^80` verifier calls traded for `Q + 1` Keccak-256 calls of the two-oracle adversary and
`2^80 + 8` verifier calls. -/
theorem le_uniBoundV3 (e : ℝ≥0∞) (Q QS nQ SQO nRf : ℕ) (hQS : QS ≤ 3 * 2 ^ 24) (hnQ : nQ ≤ 2 ^ 10)
    (hSQO : SQO ≤ 3 * 10122) (hr : nRf ≤ 6) (d m t : ℝ≥0∞)
    (hd : d ≤ 3 * openingBoundAt 10122 (uniN Q)) (hm : m ≤ ((9952 ^ 2 : ℕ) : ℝ≥0∞) * e)
    (ht : t = ((256 ^ 16 : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    d + ((QS + (QS + Q + 1) + nQ + SQO : ℕ) : ℝ≥0∞) *
        (m + t + (((nRf + 2) * (QS + (QS + Q + 1) + nQ + SQO) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((QS * 2 ^ 32 + Q + (2 ^ 80 + 8) : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ uniBound3 e Q := by
  have hN : QS + (QS + Q + 1) + nQ + SQO ≤ QS + (QS + (Q + 8)) + nQ + SQO := by omega
  have hR : QS * 2 ^ 32 + Q + (2 ^ 80 + 8) = QS * 2 ^ 32 + (Q + 8) + 2 ^ 80 := by ring
  refine le_trans ?_ (le_uniBound3 e Q QS nQ SQO nRf hQS hnQ hSQO hr d m t hd hm ht)
  rw [hR]
  refine add_le_add (add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr hN) ?_)) le_rfl
  exact add_le_add le_rfl (ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left _ hN)) _)

/-! ## The Fiat–Shamir layer -/

end UniSound

/-- info: 'UniSound.ivRec3With_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.ivRec3With_eq
