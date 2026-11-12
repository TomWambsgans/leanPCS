-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the quotient table's four slots (`PcsHTable.lean`) are the honest second message's polynomials.
import E2ECompleteness.PcsHTable

/-!
# The quotient table's slots

For `q = nov 0 (m+2) qHat` zero past `2^(m+1)`, `Z = w_m`, `n = 2^m` (all generic in `m`, instantiated at `24`):

* `slot_q`: the slot `(0, 0)` holds `q %ₘ Z`;
* `slot_a1`: when `(q /ₘ Z)(0) = 0`, the slot `(1, 0)` (`divX q_h`) holds `(q /ₘ Z) /ₘ X`;
* `slot_b0`: the slot `(0, 1)` (`mulX hHat`) holds `X · hHat`'s polynomial when `hHat`'s top entry is zero;
* `slot_b1`: the slot `(1, 1)` holds `b₀ + b₁ X + b₂ (X² + X)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

namespace E2ECompleteness.Pcs.H

theorem slot_q (m : ℕ) (qHat : Array E) (hq : ∀ j, 2 ^ (m + 1) < j → j < 2 ^ (m + 2) → qHat.getD j 0 = 0) :
    tablePoly (fun b : Fin m → Bool => qHat.getD (Completeness.idx b) 0) =
      Novel.nov 0 (m + 2) (fun j => qHat.getD j 0) %ₘ digitPoly m := by
  rw [tablePoly_idx m (fun j => qHat.getD j 0), (Novel.nov_divmod m _ hq).1]

/-- `Q_h`'s polynomial is `q /ₘ Z`. -/
theorem nov_qh (m : ℕ) (qHat : Array E) (hq : ∀ j, 2 ^ (m + 1) < j → j < 2 ^ (m + 2) → qHat.getD j 0 = 0) :
    Novel.nov 0 (m + 1) (fun j => (qhOf (2 ^ m) qHat).getD j 0) =
      Novel.nov 0 (m + 2) (fun j => qHat.getD j 0) /ₘ digitPoly m := by
  have p1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have hpos : 0 < 2 ^ m := by positivity
  rw [(Novel.nov_divmod m _ hq).2, Novel.nov_split]
  have hlow : ∀ j < 2 ^ m, (qhOf (2 ^ m) qHat).getD j 0 =
      qHat.getD (2 ^ m + j) 0 + (if j = 0 then qHat.getD (2 ^ (m + 1)) 0 else 0) := fun j hj => by
    unfold qhOf
    rw [getD_ofFn _ (by omega)]
    by_cases h0 : j = 0
    · subst h0; simp [p1]
    · simp [h0, hj]
  have hhigh : ∀ j < 2 ^ m, (qhOf (2 ^ m) qHat).getD (2 ^ m + j) 0 =
      (if j = 0 then qHat.getD (2 ^ (m + 1)) 0 else 0) := fun j hj => by
    unfold qhOf
    rw [getD_ofFn _ (by omega)]
    by_cases h0 : j = 0
    · subst h0; simp [p1]
    · simp [h0, show ¬ (2 ^ m + j < 2 ^ m) by omega, show ¬ (2 ^ m + j = 2 ^ m) by omega]
  rw [Novel.nov_congr 0 m hlow, Novel.nov_add, Novel.nov_congr 0 m (f := fun j => (qhOf (2 ^ m) qHat).getD (2 ^ m + j) 0)
    hhigh, Novel.nov_single m _ (fun j hj _ => if_neg (by omega)), if_pos rfl]
  ring

/-- **The slot `(1, 0)`**: `divX q_h` holds `(q /ₘ Z) /ₘ X`. -/
theorem slot_a1 (m : ℕ) (hm : m + 1 ≤ 62) (qHat : Array E)
    (hq : ∀ j, 2 ^ (m + 1) < j → j < 2 ^ (m + 2) → qHat.getD j 0 = 0)
    (h0 : (Novel.nov 0 (m + 2) (fun j => qHat.getD j 0) /ₘ digitPoly m).eval 0 = 0) :
    tablePoly (fun b : Fin m → Bool => (divX (qhOf (2 ^ m) qHat)).getD (Completeness.idx b) 0) =
      (Novel.nov 0 (m + 2) (fun j => qHat.getD j 0) /ₘ digitPoly m) /ₘ X := by
  have hsz : (qhOf (2 ^ m) qHat).size = 2 ^ (m + 1) := by
    unfold qhOf; rw [Array.size_ofFn, pow_succ]; ring
  have hX := Novel.X_mul_nov_divX (m + 1) hm (qhOf (2 ^ m) qHat) hsz
  have hq0 : (qhOf (2 ^ m) qHat).getD 0 0 = 0 := by
    have e := congrArg (fun p : E[X] => p.eval 0) (nov_qh m qHat hq)
    rw [Novel.nov_eval_zero] at e
    rw [e, h0]
  rw [hq0, C_0, sub_zero, nov_qh m qHat hq] at hX
  -- the quotient has degree at most `2^m`, so `divX q_h`'s high half is zero
  have hdQ : (Novel.nov 0 (m + 2) (fun j => qHat.getD j 0) /ₘ digitPoly m).natDegree ≤ 2 ^ m := by
    rw [(Novel.nov_divmod m _ hq).2]
    refine natDegree_add_le_of_degree_le ((Novel.natDegree_nov_lt m _).le) ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_add_le _ _).trans ?_
    rw [Novel.digit_natDegree, natDegree_one]
    omega
  have hdA : (Novel.nov 0 (m + 1) fun i => (divX (qhOf (2 ^ m) qHat)).getD i 0).natDegree < 2 ^ m := by
    by_cases hA : (Novel.nov 0 (m + 1) fun i => (divX (qhOf (2 ^ m) qHat)).getD i 0) = 0
    · rw [hA, natDegree_zero]; positivity
    · have e := congrArg natDegree hX
      rw [natDegree_mul X_ne_zero hA, natDegree_X] at e
      omega
  have hhigh := Novel.nov_high_zero m _ hdA
  have hsplit : (Novel.nov 0 (m + 1) fun i => (divX (qhOf (2 ^ m) qHat)).getD i 0) =
      Novel.nov 0 m fun i => (divX (qhOf (2 ^ m) qHat)).getD i 0 := by
    rw [Novel.nov_split, Novel.nov_congr 0 m (g := fun _ => 0) hhigh, nov_zero_fun, mul_zero, add_zero]
  rw [tablePoly_idx m (fun j => (divX (qhOf (2 ^ m) qHat)).getD j 0), ← hsplit, ← hX,
    mul_divByMonic_cancel_left _ monic_X]

/-- **The slot `(0, 1)`**: `mulX hHat` holds `X` times `hHat`'s polynomial, its top entry zero. -/
theorem slot_b0 (k : ℕ) (hk : k ≤ 62) (hHat : Array E) (hs : hHat.size = 2 ^ k) (htop : hHat.getD (2 ^ k - 1) 0 = 0) :
    tablePoly (fun b : Fin k → Bool => (mulX hHat).getD (Completeness.idx b) 0) =
      X * Novel.nov 0 k (fun j => hHat.getD j 0) := by
  have h := Novel.mul_nov k hk 0 (fun j => hHat.getD j 0)
  rw [show (digitPoly 0 : E[X]) = X from rfl, htop, C_0, zero_mul, add_zero] at h
  rw [h, tablePoly_idx k (fun j => (mulX hHat).getD j 0)]
  exact Novel.nov_congr 0 k fun j hj => Novel.mulX_getD hHat (by omega)

/-- **The slot `(1, 1)`**: `b₀ + b₁ X + b₂ (X² + X)`. -/
theorem slot_b1 (k : ℕ) (hk : 2 ≤ k) (coins : Coins) (b2 : E) :
    tablePoly (fun b : Fin k → Bool => b1Of coins b2 (Completeness.idx b)) =
      blindPoly coins + C b2 * (X ^ 2 + X) := by
  rw [tablePoly_idx k (b1Of coins b2)]
  have hz : ∀ j, 2 ^ 2 ≤ j → b1Of coins b2 j = 0 := fun j hj => by
    unfold b1Of
    rw [if_neg (by simp only [freeBlind, hBlind]; omega), if_neg (by simp only [freeBlind, hBlind]; omega)]
  have e := nov_extend 2 (b1Of coins b2) hz (k - 2)
  rw [show 2 + (k - 2) = k by omega] at e
  rw [e, show (2 : ℕ) = 0 + 1 + 1 from rfl, Novel.nov_split, Novel.nov_split, Novel.nov_split, Novel.nov_zero,
    Novel.nov_zero, Novel.nov_zero, Novel.nov_zero, blindPoly]
  have b0 : b1Of coins b2 0 = blindAt coins 0 := by unfold b1Of; rw [if_pos (by decide)]
  have b1 : b1Of coins b2 1 = blindAt coins 1 := by unfold b1Of; rw [if_pos (by decide)]
  have b2' : b1Of coins b2 2 = b2 := by unfold b1Of; rw [if_neg (by decide), if_pos (by decide)]
  have b3 : b1Of coins b2 3 = 0 := by unfold b1Of; rw [if_neg (by decide), if_neg (by decide)]
  simp only [pow_zero, pow_one, zero_add, add_zero, Nat.reduceAdd, b0, b1, b2', b3, C_0, mul_zero]
  simp only [digitPoly, X_comp, X_pow_comp, add_comp]
  ring

end E2ECompleteness.Pcs.H
