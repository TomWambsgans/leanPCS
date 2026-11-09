-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The main line's `FsProof.lean` (the composition's
-- facts, the bound) and `FsCost.lean` (`uniNumbers_of`) for π1-rec3's three openings.
import UniSound.Rec3.FsOps3
import UniSound.FsCost

/-!
# π1-rec3: the composition's facts, the numbers, the bound

`FsProof.lean`'s and `FsCost.lean`'s facts for π1-rec3's three openings (`uOps3`), the chain `uSpec3` on
`rec3Rounds` and the setup **unchanged** (`uSetup`: the three trees of the setup's stack, `A0`, `B0`; the verifier
opens only the first, the IV hashes all three roots):

* the openings match (`hok_uni3`: `C1`, `C2` by `whirOp_ok_tableCode`, the setup's by its tree, `whirOp_ok_tree`),
  every round with a root is opened (`hcov_uni3`), the setup's stack satisfies its claim (`hS_uni3`), the last link
  (`hlink_uni3`, from `FsLayer3`'s: `ClaimsHold`'s matrices' half is vacuous, the result has no matrices' claim);
* **the numbers** (`UniNumbers3`, `uniNumbers3_of`): the chain's `< 2^10` queries, the composed verifier's calls of
  `π` below `2^80` (`(2^10 + 3 · 10122) · 2^32`);
* **the bound** (`le_uniBound3`): the three doom terms at most `openingBoundAt 10122 N` each, the lists at most
  `largeList ≤ 9952` (two roots: `countP_root_rec3Rounds`), the tag's `2^-128`, at most `8 N` references a query.
  `uniBound3`'s definition (`Fs3.lean`) is unchanged: its constants other than the doom terms' count are the
  main line's, and the setup's and the chain's counts are the same (three trees; `< 2^10` queries).
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open LeanVM.Rpm (Short hashBlocks)
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.setupStack

theorem countP_root_rec3Rounds (fr : List RoundSpec) (hfr : ∀ r ∈ fr, r.root = false) (nV np : ℕ) :
    (rec3Rounds fr nV np).countP (fun r => r.root) = 2 := by
  have h0 : fr.countP (fun r => r.root) = 0 :=
    List.countP_eq_zero.mpr fun r hr => by simp [hfr r hr]
  simp [rec3Rounds, List.countP_append, h0]

/-- **The composed bound is at most `uniBound3`**: the three doom terms at most `openingBoundAt 10122 N`, the list
term at most `9952² e`, the tag's `2^-128`, at most `8 N` references a query, the permutation's calls below
`2^81 + Q`. -/
theorem le_uniBound3 (e : ℝ≥0∞) (Q QS nQ SQO nRf : ℕ) (hQS : QS ≤ 3 * 2 ^ 24) (hnQ : nQ ≤ 2 ^ 10)
    (hSQO : SQO ≤ 3 * 10122) (hr : nRf ≤ 6) (d m t : ℝ≥0∞)
    (hd : d ≤ 3 * openingBoundAt 10122 (uniN Q)) (hm : m ≤ ((9952 ^ 2 : ℕ) : ℝ≥0∞) * e)
    (ht : t = ((256 ^ 16 : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    d + ((QS + (QS + (Q + 8)) + nQ + SQO : ℕ) : ℝ≥0∞) *
        (m + t + (((nRf + 2) * (QS + (QS + (Q + 8)) + nQ + SQO) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((QS * 2 ^ 32 + (Q + 8) + 2 ^ 80 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ uniBound3 e Q := by
  unfold uniBound3
  have hN : QS + (QS + (Q + 8)) + nQ + SQO ≤ uniN Q := by
    unfold uniN
    have : (2 : ℕ) ^ 33 = 8589934592 := by norm_num
    have : (2 : ℕ) ^ 24 = 16777216 := by norm_num
    have : (2 : ℕ) ^ 10 = 1024 := by norm_num
    omega
  refine add_le_add (add_le_add hd (mul_le_mul' (Nat.cast_le.mpr hN) ?_)) ?_
  · rw [add_assoc]
    refine add_le_add hm ?_
    rw [ht, ENNReal.div_add_div_same, ← Nat.cast_add]
    refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
    have h7 : (nRf + 2) * (QS + (QS + (Q + 8)) + nQ + SQO) ≤ 8 * uniN Q :=
      Nat.mul_le_mul (by omega) hN
    have h256 : (256 : ℕ) ^ 16 = 2 ^ 128 := by norm_num
    rw [h256]
    exact Nat.add_le_add_left h7 _
  · rw [← Nat.cast_pow, ← Nat.cast_pow]
    refine ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.pow_le_pow_left ?_ 2)) _
    have h32 : QS * 2 ^ 32 ≤ 3 * 2 ^ 24 * 2 ^ 32 := Nat.mul_le_mul_right _ hQS
    have h81 : (3 : ℕ) * 2 ^ 24 * 2 ^ 32 + 8 + 2 ^ 80 ≤ 2 ^ 81 := by norm_num
    calc QS * 2 ^ 32 + (Q + 8) + 2 ^ 80 = (QS * 2 ^ 32 + 8 + 2 ^ 80) + Q := by ring
      _ ≤ 2 ^ 81 + Q := Nat.add_le_add_right
          ((Nat.add_le_add_right (Nat.add_le_add_right h32 8) (2 ^ 80)).trans h81) Q

/-! ## The composition's facts -/

end UniSound

/-- info: 'UniSound.le_uniBound3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.le_uniBound3
