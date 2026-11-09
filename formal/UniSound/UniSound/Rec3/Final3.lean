-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proof follows `Final.lean` (the main line's).
import UniSound.Final
import UniSound.Rec3.Fs3

/-!
# Knowledge soundness of π1-rec3, end to end, from its named links

**`uniKnowledgeSoundness3`**: `UniKnowledgeSoundnessRec3 D (uniBound3 e₃₅)` for every deployment `D`, the rounds'
errors at most `e₃₅ = 2^35 / |E|`, from

* `F3 : FlockSound3 κ` — π1-rec3's Flock phase (its zerocheck's squares, its walk);
* `I : UniIds3 D F3 np` — the identity model at π1-rec3's transcripts;
* `BR : PairBatch np` — the paired, narrow batch's rounds;
* `C : UniCode3 …`, `hFin : UniFinal3 …` — the code-level links; `hFs : FsLayer3 …` — the Fiat–Shamir layer;
* the numbers: round `0`'s error, Flock's rounds', the identities' degrees and the merge polynomial's (at most
  `2^35` in all), at most `2^35 − 2` relations on a commitment, the batch's rounds' (`errPair`, `errLast`).

The protocol is `uniPiop3 F3 I BR` (`PiopSound3.lean`, proved). **The weakest rounds are the batch's narrow
pairs**: `8 · 2^32 / |E| = 2^35 / |E|` (`2^-157`) each, the bound `e₃₅` of every round.

**`uniBound3_le_bits`**: `uniBound3 (2^35 / |E|) Q ≤ 2^-61` for `Q ≤ 2^64` (exactly `2^-61.93` at `Q = 2^64`:
the three openings' doom terms, `≈ 3 · 2^-64`, and the tag's `2^-64`
dominate; the list term is `≈ 2^-66.4`).
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset WhirBridge
open scoped ENNReal

variable {κ : ℕ} {np : ℕ} (BR : PairBatch np)

/-! ## The end theorem, from the named links -/

/-! ## The bits -/

/-- **The bound in bits**: at most `2^-61` for an adversary of at most `2^64` calls of `π` and `π⁻¹`, every round's
error at most `2^35 / |E|`. -/
theorem uniBound3_le_bits (Q : ℕ) (hQ : Q ≤ 2 ^ 64) :
    uniBound3 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 61 := by
  unfold uniBound3 uniN
  rw [cardE_cast, div_192_eq']
  have hX : 2 ^ 33 + Q + 10122 ≤ 18446744082299496586 := by
    have : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
    have h33 : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
    omega
  have b1 := openingBoundAt_le' (QV := 10122) (QA := 2 ^ 33 + Q) (X := 18446744082299496586) hX
  have hN : 2 ^ 33 + Q ≤ 18446744082299496586 := by omega
  have b2 : ((2 ^ 33 + Q : ℕ) : ℝ≥0∞) * (((9952 ^ 2 : ℕ) : ℝ≥0∞) *
      (((2 ^ 35 * 2 ^ 64 : ℕ) : ℝ≥0∞) / 2 ^ 256) + ((2 ^ 128 + 8 * (2 ^ 33 + Q) : ℕ) : ℝ≥0∞) /
        2 ^ 256) ≤
      ((18446744082299496586 * (9952 ^ 2 * (2 ^ 35 * 2 ^ 64)) +
        18446744082299496586 * (2 ^ 128 + 8 * 18446744082299496586) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [← mul_div_assoc, ← Nat.cast_mul, ENNReal.div_add_div_same, ← Nat.cast_add,
      ← mul_div_assoc, ← Nat.cast_mul]
    refine cast_div_le_256 ?_
    calc (2 ^ 33 + Q) * (9952 ^ 2 * (2 ^ 35 * 2 ^ 64) + (2 ^ 128 + 8 * (2 ^ 33 + Q)))
        ≤ 18446744082299496586 * (9952 ^ 2 * (2 ^ 35 * 2 ^ 64) +
            (2 ^ 128 + 8 * 18446744082299496586)) :=
          Nat.mul_le_mul hN (by omega)
      _ = _ := by ring
  have b3 : ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ ((1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    have hq : (2 ^ 81 + Q) ^ 2 ≤ 2 ^ 164 := by
      have h82 : 2 ^ 81 + Q ≤ 2 ^ 82 := by
        have : (2 : ℕ) ^ 82 = 2 ^ 81 + 2 ^ 81 := by norm_num
        have h64 : (2 : ℕ) ^ 64 ≤ 2 ^ 81 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
        omega
      calc (2 ^ 81 + Q) ^ 2 ≤ (2 ^ 82) ^ 2 := Nat.pow_le_pow_left h82 2
        _ = 2 ^ 164 := by norm_num
    have e1 : ((2 ^ 81 + Q : ℕ) : ℝ≥0∞) ^ 2 = (((2 ^ 81 + Q) ^ 2 : ℕ) : ℝ≥0∞) := by
      rw [Nat.cast_pow]
    rw [e1]
    calc (((2 ^ 81 + Q) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 508 ≤ ((2 ^ 164 : ℕ) : ℝ≥0∞) / 2 ^ 508 :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr hq) _
      _ = (2 : ℝ≥0∞)⁻¹ ^ 344 := by
          rw [Nat.cast_pow, Nat.cast_ofNat, show (508 : ℕ) = 164 + 344 from rfl,
            two_pow_div_two_pow]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 256 :=
          pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr (by norm_num)) (by norm_num)
      _ = ((1 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
          rw [Nat.cast_one, one_div, ENNReal.inv_pow]
  refine (add_le_add (add_le_add (mul_le_mul' le_rfl b1) b2) b3).trans ?_
  rw [show (3 : ℝ≥0∞) = ((3 : ℕ) : ℝ≥0∞) from rfl, ← mul_div_assoc, ← Nat.cast_mul,
    ENNReal.div_add_div_same, ENNReal.div_add_div_same, ← Nat.cast_add, ← Nat.cast_add]
  calc _ ≤ ((2 ^ 195 : ℕ) : ℝ≥0∞) / 2 ^ 256 := cast_div_le_256 (by norm_num)
    _ = (2 : ℝ≥0∞)⁻¹ ^ 61 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show (256 : ℕ) = 195 + 61 from rfl, two_pow_div_two_pow]

end UniSound

/-- info: 'UniSound.uniBound3_le_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.uniBound3_le_bits
