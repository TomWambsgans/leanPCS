-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The rounds as `formal/QuotientSecurity/Spec.lean`'s state function reads them (adapted from leanVM, branch
-- PCS-openings-aggregation, commit 651453c6), and their error.
import Kc3.RoundThree

/-!
# The states, and the rounds' error

The three challenges in the form the composition reads (`Protocol.lean`'s `State₁ … State₆`: a state is true when
the prover can still win): each challenge turns a lost state into a won one for few values,

* `card_state₂_le`: `(α, β, μ)`, at most `E1 q²` of `q³` (the first challenge; it needs the pole condition);
* `card_state₄_le`: `t`, at most `D2` of `q`;
* `card_state₆_le`: `ρ`, at most `3` of `q`;

so with probability at most `roundError = E1 / q` each (`round₁_le`, `round₂_le`, `round₃_le`). At the deployed
size (`n = 2^24` cells, `q = 2^192`): `roundError = 2^27 / 2^192 = 2^-165` (`roundError_deployed`).
-/

set_option linter.unusedSectionVars false

open Finset
open scoped ENNReal

namespace Kc3

open QuotientSecurity QuotientSecurity.Params

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] {P : Params F}

namespace Params

open Classical in
/-- **The first challenge, as states.** -/
theorem card_state₂_le (hpole : P.PoleCondition) (stmt : Stmt F) (g : P.Msg₁) (h : ¬ State₁ stmt g) :
    (univ.filter fun c : F × F × F => State₂ stmt g c).card ≤ P.E1 * Fintype.card F ^ 2 := by
  refine le_trans (Finset.card_le_card fun c hc => ?_) (P.card_round1_le hpole stmt g h)
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, hc.2.resolve_left h⟩

open Classical in
/-- **The second challenge, as states.** -/
theorem card_state₄_le (stmt : Stmt F) (g : P.Msg₁) (c : F × F × F) (R : P.Msg₂) (h : ¬ State₃ stmt g c R) :
    (univ.filter fun t : F => State₄ stmt g c R t).card ≤ P.D2 := by
  have hc : ¬ P.Consistent stmt g.1 R.1 c.1 c.2.1 c.2.2 := fun h' => h (Or.inr h')
  refine le_trans (Finset.card_le_card fun t ht => ?_) (P.card_round2_le stmt g R _ _ _ hc)
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, ht.2.resolve_left h⟩

open Classical in
/-- **The third challenge, as states.** -/
theorem card_state₆_le (stmt : Stmt F) (g : P.Msg₁) (c : F × F × F) (R : P.Msg₂) (t : F)
    (h : ¬ State₄ stmt g c R t) (v : (Fin 3 → F) × F) :
    (univ.filter fun ρ : F => State₆ stmt g c R t v ρ).card ≤ 3 := by
  have hc : ¬ P.ConsistentAt stmt g.1 R.1 c.1 c.2.1 c.2.2 t := fun h' => h (Or.inr h')
  refine le_trans (Finset.card_le_card fun ρ hρ => ?_) (P.card_round3_le stmt g R _ _ _ t hc v.1 v.2)
  rw [Finset.mem_filter] at hρ ⊢
  exact ⟨hρ.1, hρ.2.resolve_left h⟩

/-! ### The rounds' error -/

theorem three_le_D2 : 3 ≤ P.D2 := by
  have := P.eleven_le_card_T
  rw [D2, P.nCells_eq]; omega

theorem D2_le_E1 : P.D2 ≤ P.E1 := by unfold D2 E1; omega

/-- The first challenge's fraction is the round error. -/
theorem round₁_le : ((P.E1 * Fintype.card F ^ 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ^ 3 ≤ P.roundError := by
  have hq : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hq' : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have e : (P.E1 : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞) ^ 2 / (Fintype.card F : ℝ≥0∞) ^ 3 =
      (P.E1 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
    rw [show (Fintype.card F : ℝ≥0∞) ^ 3 = (Fintype.card F : ℝ≥0∞) ^ 2 * Fintype.card F by ring,
      mul_comm (P.E1 : ℝ≥0∞), ENNReal.mul_div_mul_left _ _ (pow_ne_zero _ hq) (ENNReal.pow_ne_top hq')]
  rw [roundError, Nat.cast_mul, Nat.cast_pow, e]

/-- The second challenge's fraction is at most the round error. -/
theorem round₂_le : (P.D2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ P.roundError := by
  rw [roundError]
  gcongr
  exact_mod_cast P.D2_le_E1

/-- The third challenge's fraction is at most the round error. -/
theorem round₃_le : (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ P.roundError := by
  rw [roundError]
  gcongr
  exact_mod_cast P.three_le_D2.trans P.D2_le_E1

/-- **At the deployed size** (`n = 2^24` cells, `q = 2^192`): `roundError = 2^-165`. -/
theorem roundError_deployed (hn : P.nCells = 2 ^ 24) (hq : Fintype.card F = 2 ^ 192) :
    P.roundError = (2⁻¹ : ℝ≥0∞) ^ 165 := by
  rw [roundError, E1, hn, hq, ← ENNReal.inv_pow, ENNReal.div_eq_inv_mul]
  have h1 : ((8 * 2 ^ 24 : ℕ) : ℝ≥0∞) = 2 ^ 27 := by norm_num
  have h2 : ((2 ^ 192 : ℕ) : ℝ≥0∞) = 2 ^ 192 := by norm_num
  rw [h1, h2]
  have h3 : (2 : ℝ≥0∞) ^ 192 = 2 ^ 165 * 2 ^ 27 := by rw [← pow_add]
  rw [h3, ENNReal.mul_inv (Or.inr (by simp)) (Or.inr (by simp)), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

end Params

end Kc3
