-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/Bits.lean` of this repository (F1's round error at the sizes of
-- `quotient::protocol`, times the list factor) to the four certified lists of the EIP's PCS claims.
import ComposePcs.AdversaryLog4
import QuotientRpm.Rpm

/-!
# The numbers, four lists

The list factor times F1's round error at the sizes of `quotient::protocol` (a field of `2^192`
elements, `2^24` cells, eight words, identities of degree at most `2^28`: `11 · 2^24 + 8` on the
instance, `Params.ofCantor_identity_le_margin`), so `roundError ≤ 2^-164` (`roundError_le_164`),
with the certified level-0 lists of the four commitments at `2^22` rows (`WhirBridge`'s README, "The
numbers"): `W` and `G` at `log_n = 25`, `7908` candidates; `H` at `log_n = 27`, `4473`; `Q` at
`log_n = 28`, `3564`. Then `7908 · 4473 · 3564 · 7908 = 996,942,050,774,208 < 2^50` tuples, and
**`listError4_le_certified`**: `listFactor4 · roundError ≤ 2^-114` (the two-root composition's was
`2^-138`: two more lists of `2^12` candidates each).

**`knowledgeSoundness_merkle_adv4_bits`**: the composed bound is then the openings' terms plus
`(Q + 6 + QV) (2^-114 + 8 (Q + 6 + QV) / 2^256)`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace ComposePcs

open Compose QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds}

/-- F1's round error at the sizes of `quotient::protocol`, identities of degree at most `2^28`. -/
theorem roundError_le_164 (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28) : roundError P B ≤ 1 / 2 ^ 164 := by
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have key : ∀ a : ℕ, a ≤ 2 ^ 28 → ((a : ℝ≥0) / (Fintype.card F : ℝ≥0)) ≤ 1 / 2 ^ 164 :=
    fun a ha => div_le_two_pow' hpos (by
      rw [hq]
      calc a * 2 ^ 164 ≤ 2 ^ 28 * 2 ^ 164 := Nat.mul_le_mul_right _ ha
        _ = 2 ^ 192 := by norm_num)
  unfold roundError
  exact max_le (max_le (key _ (by rw [hN, hw]; norm_num)) (key _ hd)) (key _ (by norm_num))

/-- **The certified lists**: `7908` candidates for `W`'s and `G`'s roots, `4473` for `H`'s,
`3564` for `Q`'s; identities of degree at most `2^28`: at most `2^-114`. -/
theorem listError4_le_certified (hq : Fintype.card F = 2 ^ 192) (hN : P.nCells = 2 ^ 24)
    (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28) {LW LH LQ LG : ℕ} (hW : LW ≤ 7908)
    (hH : LH ≤ 4473) (hQ : LQ ≤ 3564) (hG : LG ≤ 7908) :
    (listFactor4 LW LH LQ LG : ℝ≥0∞) * (roundError P B : ℝ≥0∞) ≤
      ((1 / 2 ^ 114 : ℝ≥0) : ℝ≥0∞) := by
  have hr := roundError_le_164 (P := P) (B := B) hq hN hw hd
  have hf : listFactor4 LW LH LQ LG ≤ 2 ^ 50 := by
    unfold listFactor4
    refine max_le (hW.trans (by norm_num)) ?_
    calc LW * (LH * LQ * LG) ≤ 7908 * (4473 * 3564 * 7908) :=
          Nat.mul_le_mul hW (Nat.mul_le_mul (Nat.mul_le_mul hH hQ) hG)
      _ ≤ 2 ^ 50 := by norm_num
  have hf' : (listFactor4 LW LH LQ LG : ℝ≥0) ≤ 2 ^ 50 := by exact_mod_cast hf
  have key : (listFactor4 LW LH LQ LG : ℝ≥0) * roundError P B ≤ 1 / 2 ^ 114 :=
    calc (listFactor4 LW LH LQ LG : ℝ≥0) * roundError P B ≤ 2 ^ 50 * (1 / 2 ^ 164) :=
          mul_le_mul hf' hr zero_le zero_le
      _ = 1 / 2 ^ 114 := by
          rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity), one_mul,
            ← pow_add]
  calc (listFactor4 LW LH LQ LG : ℝ≥0∞) * (roundError P B : ℝ≥0∞)
      = (((listFactor4 LW LH LQ LG : ℝ≥0) * roundError P B : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
    _ ≤ ((1 / 2 ^ 114 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast key

variable {O β : Type} (ok : β → Prop) (W : Wire P B) {MH MQ MG : Type} (K : Commits4 B MH MQ MG)

/-- **The composed statement with the certified lists, the extractor reading the adversary's
queries only**, in mumbai's two-oracle model: the openings' terms plus
`(Q + 6 + QV) (2^-114 + 8 (Q + 6 + QV) / 2^256)`. -/
theorem knowledgeSoundness_merkle_adv4_bits (hq : Fintype.card F = 2 ^ 192)
    (hN : P.nCells = 2 ^ 24) (hw : P.words = 8) (hd : B.identity ≤ 2 ^ 28)
    (cW : TableCode B.Msg₁) (hK : K.CW = cW.commit) (hLW : cW.bound ≤ 7908)
    (hLH : K.CH.bound ≤ 4473) (hLQ : K.CQ.bound ≤ 3564) (hLG : K.CG.bound ≤ 7908)
    (A : OracleComp KeccakCalls (RootProof4 F × O))
    (openings : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (advExperiment4 W A openings)).run' ∅}[
      WitnessDoomed4 ok K z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (advExperiment4 W A openings)).run' ∅}[
      WiringDoomed4 (P := P) ok z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (advExperiment4 W A openings)).run' ∅}[
      QuotientDoomed4 ok W K z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (advExperiment4 W A openings)).run' ∅}[
        Accepted4 (P := P) ok z ∧ ∀ g ∈ adversaryExtractor4 cW z.2 z.1.proof,
          ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 114 : ℝ≥0) : ℝ≥0∞) +
        8 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine (knowledgeSoundness_merkle_adv4 ok W K cW hK A openings Q QV hQ hV εW εσ εQ hW hσ
    hQd).trans ?_
  gcongr
  exact listError4_le_certified hq hN hw hd hLW hLH hLQ hLG

end ComposePcs
