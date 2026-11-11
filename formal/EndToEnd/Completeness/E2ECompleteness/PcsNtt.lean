-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Copied from `formal/EndToEnd/Bridge/Ntt.lean` (the declarations of it the leanVM line does not keep), for the
-- PCS claims' completeness.
import Bridge.Ntt

/-!
# The additive transform as F1's tables (the lemmas the completeness proof reads)

From `Bridge/Ntt.lean`: the statement's basis is a Cantor basis on its first `N ≤ 28` vectors, `values`
evaluates F1's `tablePoly`, `coefficients` inverts it, `B(p)` is F1's point.
-/

open LeanVM.Parameters PcsQuotient.Domain QuotientSecurity Finset
open Bridge.Ntt

set_option autoImplicit false

namespace E2ECompleteness.Pcs.Ntt


theorem cantorUpTo_of_isCantorBasis (hB : IsCantorBasis) {N : ℕ} (hN : N ≤ basisSize) :
    CantorUpTo N :=
  ⟨hB.1, fun k hk ↦ hB.2 ⟨k, by unfold basisSize at hN ⊢; omega⟩⟩


/-- A sum over the first `2^m` numbers is a sum over the cube, a number its bits (`Completeness.idx`). -/
theorem sum_range_eq_sum_cube {m : ℕ} (f : ℕ → K) :
    ∑ j ∈ range (2 ^ m), f j = ∑ b : Fin m → Bool, f (Completeness.idx b) := by
  refine Finset.sum_bij' (fun j _ ↦ Completeness.bitsOf m j) (fun b _ ↦ Completeness.idx b)
    (fun _ _ ↦ Finset.mem_univ _) (fun b _ ↦ Finset.mem_range.mpr (Completeness.idx_lt b))
    (fun j hj ↦ Completeness.idx_bitsOf m j (Finset.mem_range.mp hj))
    (fun b _ ↦ Completeness.bitsOf_idx b) (fun j hj ↦ ?_)
  rw [Completeness.idx_bitsOf m j (Finset.mem_range.mp hj)]


/-- `X_{idx b}` is the product of `b`'s digits, as F1's `digitsEval` weighs entry `b`. -/
theorem X_idx {m : ℕ} (b : Fin m → Bool) (x : K) :
    X m (Completeness.idx b) x = ∏ k : Fin m, if b k then QuotientSecurity.sq^[(k : ℕ)] x else 1 := by
  rw [X, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [Completeness.testBit_idx]
  rfl


/-- **The novel-basis sum is F1's `tablePoly`** of the table `b ↦ c[idx b]`. -/
theorem sum_X_eq_tablePoly {m : ℕ} (c : ℕ → K) (x : K) :
    ∑ j ∈ range (2 ^ m), X m j x * c j =
      (tablePoly (fun b : Fin m → Bool ↦ c (Completeness.idx b))).eval x := by
  rw [tablePoly_eval, digitsEval, sum_range_eq_sum_cube]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [X_idx, mul_comm]


/-- **`values` evaluates F1's table polynomial**: entry `p < 2^m` of `values m offset c` is the
`tablePoly` of the table `b ↦ c[idx b]` at `offset + B(p)`. -/
theorem values_getD_tablePoly {m : ℕ} (hB : CantorUpTo m) (hm : m ≤ basisSize) (offset : K)
    (c : Array K) (hc : c.size = 2 ^ m) {p : ℕ} (hp : p < 2 ^ m) :
    (values m offset c).getD p 0 =
      (tablePoly (fun b : Fin m → Bool ↦ c.getD (Completeness.idx b) 0)).eval (offset + point p) := by
  rw [values_getD_K hB hm offset c hc hp, sum_X_eq_tablePoly]


/-- **`B(p)` is F1's point of `p`'s bits** for the statement's basis. -/
theorem point_eq_cantor {m : ℕ} (hB : CantorUpTo m) (hm : m ≤ basisSize) {p : ℕ} (hp : p < 2 ^ m) :
    point p = (cantorOf hB).point (Completeness.bitsOf m p) := by
  rw [point_eq_sum, CantorBasis.point]
  have e : range basisSize = range (m + (basisSize - m)) := by congr 1; omega
  rw [e, Finset.sum_range_add]
  have z : ∑ x ∈ range (basisSize - m), (if p.testBit (m + x) then betaAt (m + x) else 0) = 0 :=
    Finset.sum_eq_zero fun t _ ↦ by
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num)
        (by omega)))]
      simp
  rw [z, add_zero, ← Fin.sum_univ_eq_sum_range (fun t ↦ if p.testBit t then betaAt t else 0) m]
  rfl


/-- **`coefficients` gives F1's table of the values**: the table `coefficients m offset v` holds the
polynomial whose value at `offset + B(p)` is `v[p]`, for every `p < 2^m`. -/
theorem tablePoly_coefficients {m : ℕ} (hB : CantorUpTo m) (hm : m ≤ basisSize) (offset : K)
    (v : Array K) (hv : v.size = 2 ^ m) {p : ℕ} (hp : p < 2 ^ m) :
    (tablePoly (fun b : Fin m → Bool ↦ (coefficients m offset v).getD (Completeness.idx b) 0)).eval
        (offset + point p) = v.getD p 0 := by
  rw [← values_getD_tablePoly hB hm offset _ (by rw [coefficients_size, hv]) hp,
    values_coefficients_K m offset v hv]


/-- **The same at the Cantor points** (offset `0`): at F1's point of the cube point `x`, the
polynomial of the table `coefficients m 0 v` is `v[idx x]`. -/
theorem tablePoly_coefficients_cantor {m : ℕ} (hB : CantorUpTo m) (hm : m ≤ basisSize)
    (v : Array K) (hv : v.size = 2 ^ m) (x : Fin m → Bool) :
    (tablePoly (fun b : Fin m → Bool ↦ (coefficients m 0 v).getD (Completeness.idx b) 0)).eval
        ((cantorOf hB).point x) = v.getD (Completeness.idx x) 0 := by
  have h := tablePoly_coefficients hB hm 0 v hv (Completeness.idx_lt x)
  rwa [zero_add, point_eq_cantor hB hm (Completeness.idx_lt x), Completeness.bitsOf_idx] at h

end E2ECompleteness.Pcs.Ntt
