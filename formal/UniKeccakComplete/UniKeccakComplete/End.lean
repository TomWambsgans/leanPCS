-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The numbers follow `formal/UniComplete`'s
-- `UniComplete/Prob.lean` (`deltaUni`, `deltaUni_lt`), at the Keccak VM's bus.
import UniKeccakComplete.Staged
import KeccakFlock
import E2ECompleteness.End

/-!
# Completeness of the Keccak verifier, from the staged premise

`deltaK`: the bound of `uniCompletenessKeccak_of_staged` at `Nbad = 2^28 − 1` bad `β` per `α` (the Keccak VM's
divided fingerprints: fewer than `2^28` heap leaves, as a stack of WHIR's `2^28` words has), `ct = 3 · 2^17` bad `t`
per Flock point, `t`'s cache hit `εt = 2^-200`, the grinding's `εpow = 2^-304` and `N = 2^48` block calls
(`UniComplete`'s, but for `Nbad`): `deltaK < 2^-163` (`deltaK_lt`).

**The end theorems** (`uniCompletenessKeccak_end`, `uniCompletenessKeccakRec3_end`): `UniCompletenessKeccak F D P
deltaK` and `UniCompletenessKeccakRec3 F D P deltaK` at the Keccak-f block `F = KeccakFlock.keccakFlockSpec`, for any
prover `P` satisfying the named premise `KStagedHolds` at these numbers: its experiment is, for every honest witness, a
staged two-call run with these bad-event counts, cost, freshness and grinding error. The premise is what
`UniComplete`'s code-level layers (`ProbSplit`, `ProbHyp`, `Core*`, `Alg*`, `Batch*`, `FlockProver*`, …) establish of its
explicit prover for the BLAKE2s VM; for the Keccak VM they, and the explicit prover, are not ported.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters
open UniKeccak
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Prob

/-- **The bound**: `Nbad = 2^28 − 1`, `ct = 3 · 2^17`, `εt = 2^-200`, `εpow = 2^-304`, `N = 2^48`. -/
noncomputable def deltaK : ℝ≥0∞ :=
  ((2 ^ 28 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 + 6 / 2 ^ 256 +
    (((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (2 : ℝ≥0∞)⁻¹ ^ 200) + (2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48)

/-- **`deltaK < 2^-163`.** -/
theorem deltaK_lt : deltaK < (2 : ℝ≥0∞)⁻¹ ^ 163 := by
  have ha : ((2 ^ 28 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 := by
    calc ((2 ^ 28 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 28 * (2 : ℝ≥0∞)⁻¹ ^ (164 + 28) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 164 := E2ECompleteness.two_pow_mul_inv_pow 28 164
  have hb : (6 : ℝ≥0∞) / 2 ^ 256 ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := by
    calc (6 : ℝ≥0∞) / 2 ^ 256 ≤ 2 ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ (253 + 3) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 253 := E2ECompleteness.two_pow_mul_inv_pow 3 253
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hct : ((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := by
    calc ((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 19 * (2 : ℝ≥0∞)⁻¹ ^ (173 + 19) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 173 := E2ECompleteness.two_pow_mul_inv_pow 19 173
  have he : (2 : ℝ≥0∞)⁻¹ ^ 200 ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hc : (2 : ℝ≥0∞)⁻¹ ^ 304 ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hd : rpmError (2 ^ 48) ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := by
    calc rpmError (2 ^ 48) = 2 ^ (48 * 2) * (2 : ℝ≥0∞)⁻¹ ^ (412 + 48 * 2) := by
          rw [rpmError, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ENNReal.div_eq_inv_mul,
            ← ENNReal.inv_pow, mul_comm]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 412 := E2ECompleteness.two_pow_mul_inv_pow _ 412
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hrest : 6 / 2 ^ 256 + ((((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (2 : ℝ≥0∞)⁻¹ ^ 200) +
      ((2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48))) ≤ (2 : ℝ≥0∞)⁻¹ ^ 170 := by
    calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 173 + (((2 : ℝ≥0∞)⁻¹ ^ 173 + (2 : ℝ≥0∞)⁻¹ ^ 173) +
          ((2 : ℝ≥0∞)⁻¹ ^ 173 + (2 : ℝ≥0∞)⁻¹ ^ 173)) :=
          add_le_add hb (add_le_add (add_le_add hct he) (add_le_add hc hd))
      _ = 5 * (2 : ℝ≥0∞)⁻¹ ^ (170 + 3) := by ring
      _ ≤ 2 ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ (170 + 3) := by
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 170 := E2ECompleteness.two_pow_mul_inv_pow 3 170
  have e164 : (2 : ℝ≥0∞)⁻¹ ^ 164 + (2 : ℝ≥0∞)⁻¹ ^ 164 = (2 : ℝ≥0∞)⁻¹ ^ 163 := by
    calc (2 : ℝ≥0∞)⁻¹ ^ 164 + (2 : ℝ≥0∞)⁻¹ ^ 164 = 2 ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ (163 + 1) := by
          rw [← two_mul, pow_one]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 163 := E2ECompleteness.two_pow_mul_inv_pow 1 163
  have h164 : (2 : ℝ≥0∞)⁻¹ ^ 170 < (2 : ℝ≥0∞)⁻¹ ^ 164 := by
    calc (2 : ℝ≥0∞)⁻¹ ^ 170 ≤ (2 : ℝ≥0∞)⁻¹ ^ 165 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
      _ < (2 : ℝ≥0∞)⁻¹ ^ 165 + (2 : ℝ≥0∞)⁻¹ ^ 165 := ENNReal.lt_add_right (by simp) (by simp)
      _ = 2 ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ (164 + 1) := by rw [← two_mul, pow_one]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 164 := E2ECompleteness.two_pow_mul_inv_pow 1 164
  have hne : ((2 ^ 28 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≠ ⊤ := ne_top_of_le_ne_top (by simp) ha
  have hsum : deltaK = ((2 ^ 28 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (6 / 2 ^ 256 +
      ((((3 * 2 ^ 17 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (2 : ℝ≥0∞)⁻¹ ^ 200) +
        ((2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48)))) := by
    unfold deltaK
    ac_rfl
  rw [hsum, ← e164]
  exact ENNReal.add_lt_add_of_le_of_lt hne ha (hrest.trans_lt h164)

/-- **The staged premise at `deltaK`'s numbers.** -/
abbrev KStagedK (D : KDeployment) (v : KeccakVariant) (P : KProver D) : Prop :=
  KStagedHolds KeccakFlock.keccakFlockSpec D v P (2 ^ 28 - 1) (3 * 2 ^ 17) (2 ^ 48) ((2 : ℝ≥0∞)⁻¹ ^ 200)
    ((2 : ℝ≥0∞)⁻¹ ^ 304)

/-- **Completeness of the Keccak verifier (the main line)** at the Keccak-f block, `deltaK < 2^-163`, for a prover
satisfying the staged premise. -/
theorem uniCompletenessKeccak_end (D : KDeployment) (P : KProver D) (hS : KStagedK D keccakMain P) :
    UniCompletenessKeccak KeccakFlock.keccakFlockSpec D P deltaK :=
  uniCompletenessKeccak_of_staged hS

/-- **Completeness of the Keccak π1 at π1-rec3's shape** at the Keccak-f block, `deltaK < 2^-163`, for a prover
satisfying the staged premise. -/
theorem uniCompletenessKeccakRec3_end (D : KDeployment) (P : KProver D) (hS : KStagedK D keccakRec3 P) :
    UniCompletenessKeccakRec3 KeccakFlock.keccakFlockSpec D P deltaK :=
  uniCompletenessKeccak_of_staged hS

end UniKeccakComplete.Prob
