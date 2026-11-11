-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The deployed instance of `Kc3.Params` on a Cantor basis, from `formal/QuotientSecurity/{Cantor,Tables,Concrete}`
-- (adapted from leanVM, branch PCS-openings-aggregation, commit 651453c6) and `QuotientSecurity/Instance.lean`'s
-- interpolation.
import Kc3.States
import QuotientSecurity.Concrete

/-!
# The instance on a Cantor basis

`Params.ofCantor B n hm σ pins random`: the cells the span of `β₀ … β_{n+1}` of a Cantor basis (a row the span of
`β₂ …` plus the four shifts `0, 1, θ, θ + 1`, `θ = β₁`; `QuotientSecurity.cantorT`, `cantorCells`), the wiring `σ`
carried by its interpolant, the given pins and random rows; and **the cells sum low-degree polynomials to zero**
(`sum_cells_eq_zero`): a polynomial of degree `< 2^(n+2) − 1` is the polynomial of its table in the novel basis
(`CantorBasis.exists_table`), whose sum over the cells is its top coefficient (`CantorBasis.sum_tablePoly`,
`mle_ones`), the coefficient of `X^(2^(n+2) − 1)` (`coeff_tablePoly_top`), zero.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Kc3

open QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2]

theorem sum_two_pow_fin_add_one (m : ℕ) : ∑ k : Fin m, 2 ^ (k : ℕ) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [pow_succ]
    omega

/-- **The top coefficient of a table's polynomial is its last entry**: the coefficient of `X^(2^m − 1)`, which
only the product of all the digits reaches. -/
theorem coeff_tablePoly_top {m : ℕ} (c : (Fin m → Bool) → F) :
    (tablePoly c).coeff (2 ^ m - 1) = c fun _ => true := by
  have hD : ∑ k : Fin m, 2 ^ (k : ℕ) = 2 ^ m - 1 := by have := sum_two_pow_fin_add_one m; omega
  have hmon : ∀ b : Fin m → Bool, (∏ k : Fin m, (if b k then digitPoly (k : ℕ) else 1 : F[X])).Monic := fun b =>
    monic_prod_of_monic _ _ fun k _ => by
      split_ifs
      · exact (digitPoly_monic_natDegree _).1
      · exact monic_one
  have hdeg : ∀ b : Fin m → Bool, (∏ k : Fin m, (if b k then digitPoly (k : ℕ) else 1 : F[X])).natDegree =
      ∑ k : Fin m, (if b k then 2 ^ (k : ℕ) else 0) := fun b => by
    rw [natDegree_prod_of_monic _ _ fun k _ => by
      split_ifs
      · exact (digitPoly_monic_natDegree _).1
      · exact monic_one]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · exact (digitPoly_monic_natDegree _).2
    · simp
  unfold tablePoly
  rw [finset_sum_coeff, Finset.sum_eq_single fun _ => true]
  · rw [coeff_C_mul]
    have h1 := hdeg fun _ => true
    have hm1 := hmon fun _ => true
    simp only [ite_true] at h1 hm1 ⊢
    rw [← hD, ← h1, hm1.coeff_natDegree, mul_one]
  · intro b _ hb
    obtain ⟨k₀, hk₀⟩ : ∃ k, b k = false := by
      by_contra h
      push Not at h
      exact hb (funext fun k => by simpa using h k)
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [hdeg b, ← hD]
    have hle : ∀ k : Fin m, (if b k then 2 ^ (k : ℕ) else 0) ≤ 2 ^ (k : ℕ) := fun k => by split_ifs <;> simp
    have hlt : (if b k₀ then 2 ^ (k₀ : ℕ) else 0) < 2 ^ (k₀ : ℕ) := by rw [hk₀]; simp
    exact Finset.sum_lt_sum (fun k _ => hle k) ⟨k₀, Finset.mem_univ _, hlt⟩
  · intro h; exact absurd (Finset.mem_univ _) h

variable {N : ℕ} (B : CantorBasis F N)

/-- **A polynomial of degree below `2^m − 1` sums to zero over the span of `β₀ … β_{m−1}`.** -/
theorem sum_cells_eq_zero {m : ℕ} (hm : m ≤ N) (p : F[X]) (hp : p.natDegree + 2 ≤ 2 ^ m) :
    ∑ x : Fin m → Bool, p.eval (B.point x) = 0 := by
  obtain ⟨c, hc⟩ := B.exists_table hm fun x => p.eval (B.point x)
  have heq : tablePoly c = p := by
    rw [← sub_eq_zero]
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (B.point_injective hm) (fun x => ?_) ?_
    · rw [eval_sub, hc x, sub_self]
    · simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt (natDegree_tablePoly_lt c) (by omega))
  rw [← heq, sum_tablePoly B hm, mle_ones, ← coeff_tablePoly_top c, heq]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

variable [DecidableEq F]

/-- The rows of the instance: `2^n` of them. -/
theorem card_cantorT {n : ℕ} (hm : n + 2 ≤ N) : (cantorT B n).card = 2 ^ n := by
  have := Fintype.card_congr (cantorRows B hm)
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_coe] at this
  exact this.symm

/-- **The deployed instance** on a Cantor basis with `n + 2 ≤ N` vectors: rows the span of `β₂ … β_{n+1}`,
`θ = β₁`, the wiring `σ` (carried by its interpolant on the cells), the pins and the random rows given. -/
noncomputable def Params.ofCantor {n : ℕ} (hm : n + 2 ≤ N) (σ : Equiv.Perm (cantorT B n × Fin 4))
    (pins : Fin pinCount ↪ cantorT B n) (random : Finset (cantorT B n)) : Params F :=
  have hinj : Function.Injective fun i : cantorT B n × Fin 4 => (i.1 : F) + shift (B.β 1) i.2 := by
    rintro ⟨⟨x, hx⟩, c⟩ ⟨⟨y, hy⟩, d⟩ h
    obtain ⟨rfl, rfl⟩ := cantor_hT B hm x hx y hy c d h
    rfl
  { θ := B.β 1
    hθ := cantor_theta B (by omega)
    T := cantorT B n
    hT := cantor_hT B hm
    σ := σ
    sigmaPoly := Lagrange.interpolate univ (fun i : cantorT B n × Fin 4 => (i.1 : F) + shift (B.β 1) i.2)
      fun i => ((σ i).1 : F) + shift (B.β 1) (σ i).2
    hσ := fun i => Lagrange.eval_interpolate_at_node _ hinj.injOn (Finset.mem_univ i)
    hσdeg := by
      set q := Lagrange.interpolate univ (fun i : cantorT B n × Fin 4 => (i.1 : F) + shift (B.β 1) i.2)
        fun i => ((σ i).1 : F) + shift (B.β 1) (σ i).2
      have hcard : (univ : Finset (cantorT B n × Fin 4)).card = 4 * (cantorT B n).card := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, mul_comm]
      by_cases h0 : q = 0
      · rw [h0, natDegree_zero, card_cantorT B hm]; positivity
      · have hd := Lagrange.degree_interpolate_lt (s := univ) (fun i => ((σ i).1 : F) + shift (B.β 1) (σ i).2)
          hinj.injOn
        rw [hcard] at hd
        exact (natDegree_lt_iff_degree_lt h0).mpr hd
    pins := pins
    random := random
    hSum := fun p hp => by
      rw [card_cantorT B hm, show 4 * 2 ^ n = 2 ^ (n + 2) by ring] at hp
      rw [← Equiv.sum_comp (cantorCells B hm)]
      have := sum_cells_eq_zero B hm p hp
      rw [← this]
      exact Finset.sum_congr rfl fun x _ => by rw [cantorCells_point] }

theorem ofCantor_nCells {n : ℕ} (hm : n + 2 ≤ N) (σ : Equiv.Perm (cantorT B n × Fin 4))
    (pins : Fin pinCount ↪ cantorT B n) (random : Finset (cantorT B n)) :
    (Params.ofCantor B hm σ pins random).nCells = 2 ^ (n + 2) := by
  rw [Params.nCells_eq, show (Params.ofCantor B hm σ pins random).T = cantorT B n from rfl, card_cantorT B hm]
  ring

end Kc3
