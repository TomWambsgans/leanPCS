-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The numbers follow `formal/UniComplete`'s
-- `UniComplete/Prob.lean` (`deltaUni`, `deltaUni_lt`), at the Keccak VM's bus.
import UniKeccakComplete.Staged
import KeccakFlock
import E2ECompleteness.End

/-!
# Completeness of the Keccak verifier, from the staged premise

`deltaK`: the bound of `uniCompletenessKeccak_of_staged` at `Nbad = 2^22 − 1` bad `β` per `α` (the Keccak VM's divided
fingerprints at the reference shape: at most `3,227,648 < 2^22`, `K/BadFpCount.lean`), `ct = 2^15` bad `t` per Flock
point (`K/ProbBadT.lean`), `t`'s cache hit `εt = 2^-200`, the grinding's `εpow = 2^-304` and `N = 2^48` block calls:
`deltaK < 2^-169` (`deltaK_lt`; the bus challenges' `2^-170` dominate).

**The end theorems** (`uniCompletenessKeccak_end`, `uniCompletenessKeccakRec3_end`): `UniCompletenessKeccak F D P
deltaK` and `UniCompletenessKeccakRec3 F D P deltaK` at the Keccak-f block `F = KeccakFlock.keccakFlockSpec`, for any
prover `P` satisfying the named premise `KStagedHolds` at these numbers: its experiment is, for every honest witness, a
staged two-call run with these bad-event counts, cost, freshness and grinding error. `K/ProbK.lean` establishes it for
the explicit honest prover (main line); π1-rec3 has its own staged form (two chained challenges, `K/Rec3ProbStaged.lean`,
`K/Rec3ProbK.lean`), since `KStagedK`'s five chained answers do not describe its experiment.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters
open UniKeccak
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Prob

/-- **The bound**: `Nbad = 2^22 − 1`, `ct = 2^15`, `εt = 2^-200`, `εpow = 2^-304`, `N = 2^48`. -/
noncomputable def deltaK : ℝ≥0∞ :=
  ((2 ^ 22 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 + 6 / 2 ^ 256 +
    (((2 ^ 15 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (2 : ℝ≥0∞)⁻¹ ^ 200) + (2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48)

/-- **`deltaK < 2^-169`.** -/
theorem deltaK_lt : deltaK < (2 : ℝ≥0∞)⁻¹ ^ 169 := by
  have ha : ((2 ^ 22 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ 170 := by
    calc ((2 ^ 22 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 22 * (2 : ℝ≥0∞)⁻¹ ^ (170 + 22) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 170 := E2ECompleteness.two_pow_mul_inv_pow 22 170
  have hb : (6 : ℝ≥0∞) / 2 ^ 256 ≤ (2 : ℝ≥0∞)⁻¹ ^ 177 := by
    calc (6 : ℝ≥0∞) / 2 ^ 256 ≤ 2 ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ (253 + 3) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 253 := E2ECompleteness.two_pow_mul_inv_pow 3 253
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 177 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hct : ((2 ^ 15 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ (2 : ℝ≥0∞)⁻¹ ^ 177 := by
    calc ((2 ^ 15 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 15 * (2 : ℝ≥0∞)⁻¹ ^ (177 + 15) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 177 := E2ECompleteness.two_pow_mul_inv_pow 15 177
  have he : (2 : ℝ≥0∞)⁻¹ ^ 200 ≤ (2 : ℝ≥0∞)⁻¹ ^ 177 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hc : (2 : ℝ≥0∞)⁻¹ ^ 304 ≤ (2 : ℝ≥0∞)⁻¹ ^ 177 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hd : rpmError (2 ^ 48) ≤ (2 : ℝ≥0∞)⁻¹ ^ 177 := by
    calc rpmError (2 ^ 48) = 2 ^ (48 * 2) * (2 : ℝ≥0∞)⁻¹ ^ (412 + 48 * 2) := by
          rw [rpmError, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ENNReal.div_eq_inv_mul,
            ← ENNReal.inv_pow, mul_comm]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 412 := E2ECompleteness.two_pow_mul_inv_pow _ 412
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 177 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hrest : 6 / 2 ^ 256 + ((((2 ^ 15 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (2 : ℝ≥0∞)⁻¹ ^ 200) +
      ((2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48))) ≤ (2 : ℝ≥0∞)⁻¹ ^ 174 := by
    calc _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 177 + (((2 : ℝ≥0∞)⁻¹ ^ 177 + (2 : ℝ≥0∞)⁻¹ ^ 177) +
          ((2 : ℝ≥0∞)⁻¹ ^ 177 + (2 : ℝ≥0∞)⁻¹ ^ 177)) :=
          add_le_add hb (add_le_add (add_le_add hct he) (add_le_add hc hd))
      _ = 5 * (2 : ℝ≥0∞)⁻¹ ^ (174 + 3) := by ring
      _ ≤ 2 ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ (174 + 3) := by
          gcongr
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 174 := E2ECompleteness.two_pow_mul_inv_pow 3 174
  have e170 : (2 : ℝ≥0∞)⁻¹ ^ 170 + (2 : ℝ≥0∞)⁻¹ ^ 170 = (2 : ℝ≥0∞)⁻¹ ^ 169 := by
    calc (2 : ℝ≥0∞)⁻¹ ^ 170 + (2 : ℝ≥0∞)⁻¹ ^ 170 = 2 ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ (169 + 1) := by
          rw [← two_mul, pow_one]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 169 := E2ECompleteness.two_pow_mul_inv_pow 1 169
  have h170 : (2 : ℝ≥0∞)⁻¹ ^ 174 < (2 : ℝ≥0∞)⁻¹ ^ 170 := by
    calc (2 : ℝ≥0∞)⁻¹ ^ 174 ≤ (2 : ℝ≥0∞)⁻¹ ^ 171 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
      _ < (2 : ℝ≥0∞)⁻¹ ^ 171 + (2 : ℝ≥0∞)⁻¹ ^ 171 := ENNReal.lt_add_right (by simp) (by simp)
      _ = 2 ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ (170 + 1) := by rw [← two_mul, pow_one]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 170 := E2ECompleteness.two_pow_mul_inv_pow 1 170
  have hne : ((2 ^ 22 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≠ ⊤ := ne_top_of_le_ne_top (by simp) ha
  have hsum : deltaK = ((2 ^ 22 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (6 / 2 ^ 256 +
      ((((2 ^ 15 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (2 : ℝ≥0∞)⁻¹ ^ 200) +
        ((2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48)))) := by
    unfold deltaK
    ac_rfl
  rw [hsum, ← e170]
  exact ENNReal.add_lt_add_of_le_of_lt hne ha (hrest.trans_lt h170)

/-- **The staged premise at `deltaK`'s numbers.** -/
abbrev KStagedK (D : KDeployment) (v : KeccakVariant) (P : KProver D) : Prop :=
  KStagedHolds KeccakFlock.keccakFlockSpec D v P (2 ^ 22 - 1) (2 ^ 15) (2 ^ 48) ((2 : ℝ≥0∞)⁻¹ ^ 200)
    ((2 : ℝ≥0∞)⁻¹ ^ 304)

/-- **Completeness of the Keccak verifier (the main line)** at the Keccak-f block, `deltaK < 2^-169`, for a prover
satisfying the staged premise. -/
theorem uniCompletenessKeccak_end (D : KDeployment) (P : KProver D) (hS : KStagedK D keccakMain P) :
    UniCompletenessKeccak KeccakFlock.keccakFlockSpec D P deltaK :=
  uniCompletenessKeccak_of_staged hS

/-- **Completeness of the Keccak π1 at π1-rec3's shape** at the Keccak-f block, `deltaK < 2^-169`, for a prover
satisfying the staged premise. -/
theorem uniCompletenessKeccakRec3_end (D : KDeployment) (P : KProver D) (hS : KStagedK D keccakRec3 P) :
    UniCompletenessKeccakRec3 KeccakFlock.keccakFlockSpec D P deltaK :=
  uniCompletenessKeccak_of_staged hS

end UniKeccakComplete.Prob
