-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecPiop.Indicator
import Mathlib.LinearAlgebra.Lagrange

/-!
# A polynomial below `N − 1` sums to zero over `V_m`

π2v4's copy sum (`PI2.md` §7, "The copy sum from `Q`'s layout"): the identity's claim forces `H(0) = 0`, so `h = H/x`
has degree below `N − 1`, and **only `x^(N−1)` has a nonzero sum over the `F_2`-subspace `V_m` of `N` points**.

The proof is Lagrange's interpolation on the `N` points `ω_i` (`Lagrange.eq_interpolate`): a polynomial of degree below
`N` is `Σ_i p(ω_i) L_i`, and `L_i`'s coefficient of `x^(N−1)` is `Π_{j ≠ i} (ω_i + ω_j)^{-1}`, which on a subspace is
the same constant `c = Π_{k ≠ 0} ω_k^{-1}` for every `i` (`j ↦ i ⊕ j` permutes the other points). So `p`'s coefficient
of `x^(N−1)` is `c Σ_i p(ω_i)`, and it is zero below that degree (`sum_eval_eq_zero_of_natDegree_lt`).
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset Polynomial

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

/-- **The product of the other points' differences is the same for every point** of the subspace `V_L`. -/
theorem prod_erase_add_eq {ω : ℕ → F} {n L : ℕ} (hP : Points ω n) (hL : L ≤ n) {i : ℕ} (hi : i < 2 ^ L) :
    ∏ j ∈ (range (2 ^ L)).erase i, (ω i - ω j) = ∏ k ∈ (range (2 ^ L)).erase 0, ω k := by
  refine Finset.prod_nbij' (fun j => i ^^^ j) (fun k => i ^^^ k) (fun j hj => ?_) (fun k hk => ?_)
    (fun j _ => by simp [← Nat.xor_assoc]) (fun k _ => by simp [← Nat.xor_assoc]) (fun j _ => ?_)
  · rw [Finset.mem_erase, Finset.mem_range] at hj ⊢
    refine ⟨fun h => hj.1 ?_, Nat.xor_lt_two_pow hi hj.2⟩
    have := congrArg (i ^^^ ·) h
    simpa [← Nat.xor_assoc] using this
  · rw [Finset.mem_erase, Finset.mem_range] at hk ⊢
    refine ⟨fun h => hk.1 ?_, Nat.xor_lt_two_pow hi hk.2⟩
    have := congrArg (i ^^^ ·) h
    simpa [← Nat.xor_assoc] using this
  · rw [hP.xor, sub_eq_add_neg, CharTwo.neg_eq]

/-- The subspace's nonzero points are nonzero. -/
theorem prod_erase_ne_zero {ω : ℕ → F} {n L : ℕ} (hP : Points ω n) (hL : L ≤ n) :
    ∏ k ∈ (range (2 ^ L)).erase 0, ω k ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro k hk
  rw [Finset.mem_erase, Finset.mem_range] at hk
  intro h0
  have hk2 : k < 2 ^ n := lt_of_lt_of_le hk.2 (Nat.pow_le_pow_right (by norm_num) hL)
  have h00 : (0 : ℕ) < 2 ^ n := Nat.two_pow_pos n
  exact hk.1 (hP.inj k hk2 0 h00 (by rw [h0, hP.zero]))

/-- **Lagrange's basis polynomial's coefficient of `x^(card − 1)`**: the product of the inverse differences. -/
theorem coeff_basis_top {ι : Type} [DecidableEq ι] (s : Finset ι) (v : ι → F) {i : ι} (hi : i ∈ s) :
    (Lagrange.basis s v i).coeff (s.card - 1) = ∏ j ∈ s.erase i, (v i - v j)⁻¹ := by
  have hdeg : ∀ j ∈ s.erase i, (Lagrange.basisDivisor (v i) (v j)).natDegree ≤ 1 := fun j _ => by
    unfold Lagrange.basisDivisor
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simp
  have key := Polynomial.coeff_prod_of_natDegree_le (s := s.erase i)
    (fun j => Lagrange.basisDivisor (v i) (v j)) 1 hdeg
  have hc : s.card - 1 = (s.erase i).card * 1 := by rw [Finset.card_erase_of_mem hi, mul_one]
  unfold Lagrange.basis
  rw [hc]
  refine key.trans (Finset.prod_congr rfl fun j _ => ?_)
  unfold Lagrange.basisDivisor
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C]
  simp

/-- **A polynomial of degree below `N − 1` sums to zero over `V_L`** (`N = 2^L`, `L ≤ n`). -/
theorem sum_eval_eq_zero_of_natDegree_lt {ω : ℕ → F} {n L : ℕ} (hP : Points ω n) (hL : L ≤ n) (p : F[X])
    (hp : p.natDegree + 1 < 2 ^ L) : ∑ i ∈ range (2 ^ L), p.eval (ω i) = 0 := by
  set s := range (2 ^ L)
  have hinj : Set.InjOn ω s := fun a ha b hb h => by
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    have hn : 2 ^ L ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hL
    exact hP.inj a (by omega) b (by omega) h
  have hdeg : p.degree < s.card := by
    rw [Finset.card_range]
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact_mod_cast (by omega : p.natDegree < 2 ^ L)
  have hint := Lagrange.eq_interpolate hinj hdeg
  have hcoef : p.coeff (s.card - 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Finset.card_range]; omega)
  rw [hint, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff] at hcoef
  set c := ∏ k ∈ (range (2 ^ L)).erase 0, ω k with hc
  have hterm : ∀ i ∈ s, (C (p.eval (ω i)) * Lagrange.basis s ω i).coeff (s.card - 1) = p.eval (ω i) * c⁻¹ := by
    intro i hi
    rw [Polynomial.coeff_C_mul, coeff_basis_top s ω hi, Finset.prod_inv_distrib,
      prod_erase_add_eq hP hL (Finset.mem_range.mp hi)]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul] at hcoef
  rcases mul_eq_zero.mp hcoef with h | h
  · exact h
  · exact absurd (inv_eq_zero.mp h) (prod_erase_ne_zero hP hL)

end RecPiop
