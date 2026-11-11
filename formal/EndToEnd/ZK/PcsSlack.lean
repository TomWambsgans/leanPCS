-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. The multilinear evaluation as a sum is leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `lean_vm/LeanVM/Protocol/Whir/Complete/Tables.lean`'s `multilinearEval_eq_sum`, `LeanVM/Prover/Mle.lean`'s
-- `mleK_eq`).
import ZK.PcsFSClosed
import LeanVM.Prover.Mle
import LeanVM.Protocol.Whir.Complete.Tables

/-!
# The slack words: group 2 of the revealed scalars

The quotient table's four slack words (`Coins.slack`, `quotientTable`) sit at coefficients `slackAt k` of `q`'s low
half, limbs `0`, `1` and `3` (`SlackPos`). The table is the table without them plus the slack words there
(`quotientTable_getD`), so `T`'s out-of-domain answer is the answer without them plus `Σ_k s_k · slackWeight z k`
(`oodT_eq`), the weights functions of the out-of-domain point `z` alone. Where they span `E` over `K`
(`SlackSpan z`), `T`'s answer is uniform given the random rows and the blinding, so the revealed scalars are
uniform as soon as the other four (`W`'s answer, `C`, `V + Y`, `X`: `group1`) are (`rMass_eq`).

**`revealedUniform_of_group1`**: `Group1Uniform ε1 → RevealedUniform (ε1 + εspan) 0`, `εspan` the probability that
the slack's weights at a uniform out-of-domain point do not span `E` (`spanFail`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open PcsQuotient.Transcript PcsQuotient.Domain
open scoped ENNReal

namespace PcsQuotient.EndToEnd

/-! ### The slack's place in the table -/

/-- **Word `w` of a quotient table of `2^m` coefficients a part holds slack word `k`**: kind `0`, low half,
coefficient `slackAt k`, limb `0`, `1` or `3`. -/
def SlackPos (n k w : ℕ) : Prop := w / (8 * n) = 0 ∧ w / n % 2 = 0 ∧ w % n = slackAt k ∧ w / (2 * n) % 4 ≠ 2

instance (n k w : ℕ) : Decidable (SlackPos n k w) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The randomness with the slack words zero. -/
def _root_.PcsQuotient.Coins.noSlack (coins : Coins) : Coins := { coins with slack := 0 }

/-- Slack word `k`, zero past them. -/
def slackVal (coins : Coins) (k : ℕ) : K := if h : k < slackWords then coins.slack ⟨k, h⟩ else 0

/-- The table's fold over the slack words is their sum, at most one of them sitting at a coefficient. -/
theorem slack_fold (coins : Coins) (a b : Prop) [Decidable a] [Decidable b] (i : ℕ) :
    List.foldl (fun acc k ↦ if a ∧ b ∧ i = slackAt k then (if h : k < slackWords then coins.slack ⟨k, h⟩ else 0)
      else acc) 0 (List.range slackWords) =
      ∑ k ∈ Finset.range slackWords, if a ∧ b ∧ i = slackAt k then slackVal coins k else 0 := by
  simp only [show slackWords = 4 from rfl, show List.range 4 = [0, 1, 2, 3] from rfl, List.foldl,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [← show slackWords = 4 from rfl]
  by_cases ha : a <;> by_cases hb : b <;> simp only [ha, hb, true_and, false_and, ite_false, add_zero] <;>
    simp only [slackAt, slackVal] <;> split_ifs <;> simp_all <;> omega

/-- The slack words' contribution to a word. -/
def slackPart (n : ℕ) (coins : Coins) (w : ℕ) : K :=
  ∑ k ∈ Finset.range slackWords, if SlackPos n k w then slackVal coins k else 0

/-- **The table is the table without the slack words, plus them.** -/
theorem quotientTable_getD (circuit : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins) (α β μ : E)
    (w : ℕ) (hw : w < 16 * 2 ^ cellVars circuit.logRows) :
    (quotientTable circuit stmt cells₀ coins α β μ).getD w 0 =
      (quotientTable circuit stmt cells₀ coins.noSlack α β μ).getD w 0 +
        slackPart (2 ^ cellVars circuit.logRows) coins w := by
  have hq : quotientParts circuit stmt cells₀ coins.noSlack α β μ = quotientParts circuit stmt cells₀ coins α β μ := rfl
  have hb : ∀ i, blindAt coins.noSlack i = blindAt coins i := fun _ ↦ rfl
  unfold quotientTable
  rw [LeanVM.Prover.getD_ofFn _ _ hw, LeanVM.Prover.getD_ofFn _ _ hw]
  simp only [hq, hb, slack_fold, slackPart, SlackPos]
  have h0 : ∀ (a b : Prop) [Decidable a] [Decidable b] (i : ℕ),
      (∑ k ∈ Finset.range slackWords, if a ∧ b ∧ i = slackAt k then slackVal coins.noSlack k else 0) = 0 :=
    fun _ _ _ _ _ ↦ Finset.sum_eq_zero fun k _ ↦ by simp [slackVal, Coins.noSlack]
  rw [h0]
  have hl : w / (2 * 2 ^ cellVars circuit.logRows) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  by_cases h1 : w / (2 * 2 ^ cellVars circuit.logRows) % 4 < 2
  · have h3 : w / (2 * 2 ^ cellVars circuit.logRows) % 4 < 3 := by omega
    have h2 : w / (2 * 2 ^ cellVars circuit.logRows) % 4 ≠ 2 := by omega
    simp only [h1, h3, h2, ite_true, ne_eq, not_false_eq_true, and_true, add_zero]
  · by_cases h2 : w / (2 * 2 ^ cellVars circuit.logRows) % 4 = 2
    · simp [h2]
    · have h3 : ¬ w / (2 * 2 ^ cellVars circuit.logRows) % 4 < 3 := by omega
      simp only [h1, h3, h2, ite_false, ne_eq, not_false_eq_true, and_true, zero_add]

/-! ### `T`'s answer -/

theorem ofK_add₂ (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem ofK_zero₂ : ofK (0 : K) = 0 := map_zero (algebraMap K E)

theorem ofK_sum₂ {ι : Type} (s : Finset ι) (f : ι → K) : ofK (∑ i ∈ s, f i) = ∑ i ∈ s, ofK (f i) :=
  map_sum (algebraMap K E) f s

/-- **A table's multilinear as a sum** over its words. -/
theorem tableEval_sum (A : Array K) (V : ℕ) (hA : A.size = 2 ^ V) (z : List E) (hz : z.length = V) :
    tableEval A z = ∑ w ∈ Finset.range (2 ^ V), ofK (A.getD w 0) * eqEval (boolPoint V w) z := by
  rw [tableEval, LeanVM.Prover.mleK_eq,
    LeanVM.Protocol.Whir.Complete.multilinearEval_eq_sum V _ _ (by simp [hA]) hz]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i < 2 ^ V := Finset.mem_range.1 hi
  have h2 : (A.toList.map ofK).getD i 0 = ofK (A.getD i 0) := by
    simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, hi', hA]
  rw [h2]

/-- The weight of slack word `k` in the quotient table's multilinear at `z` (`28` variables). -/
noncomputable def slackWeight (z : List E) (k : ℕ) : E :=
  ∑ w ∈ Finset.range (2 ^ 28), if SlackPos (2 ^ 24) k w then eqEval (boolPoint 28 w) z else 0

theorem cellVars_membership : cellVars (membership logRows).logRows = 24 := rfl

/-- **`T`'s out-of-domain answer is the answer without the slack words plus their weighted sum.** -/
theorem oodT_eq (stmt : Statement) (cells₀ : Array K) (coins : Coins) (α β μ : E) (z : List E)
    (hz : z.length = 28) :
    tableEval (quotientTable (membership logRows) stmt cells₀ coins α β μ) z =
      tableEval (quotientTable (membership logRows) stmt cells₀ coins.noSlack α β μ) z +
        ∑ k ∈ Finset.range slackWords, ofK (slackVal coins k) * slackWeight z k := by
  have hsz : ∀ c : Coins, (quotientTable (membership logRows) stmt cells₀ c α β μ).size = 2 ^ 28 := fun c ↦ by
    unfold quotientTable
    rw [Array.size_ofFn, cellVars_membership]
    norm_num
  rw [tableEval_sum _ 28 (hsz _) z hz, tableEval_sum _ 28 (hsz _) z hz]
  have hw : ∀ w ∈ Finset.range (2 ^ 28),
      ofK ((quotientTable (membership logRows) stmt cells₀ coins α β μ).getD w 0) * eqEval (boolPoint 28 w) z =
        ofK ((quotientTable (membership logRows) stmt cells₀ coins.noSlack α β μ).getD w 0) *
          eqEval (boolPoint 28 w) z +
        ∑ k ∈ Finset.range slackWords,
          ofK (slackVal coins k) * (if SlackPos (2 ^ 24) k w then eqEval (boolPoint 28 w) z else 0) := by
    intro w hw
    have hw' : w < 16 * 2 ^ cellVars (membership logRows).logRows := by
      rw [cellVars_membership]; have := Finset.mem_range.1 hw; omega
    rw [quotientTable_getD _ _ _ _ _ _ _ w hw', ofK_add₂, add_mul, slackPart, ofK_sum₂, Finset.sum_mul,
      cellVars_membership]
    refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
    split_ifs <;> simp [ofK_zero₂]
  rw [Finset.sum_congr rfl hw, Finset.sum_add_distrib, Finset.sum_comm]
  refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
  rw [slackWeight, Finset.mul_sum]

end PcsQuotient.EndToEnd
