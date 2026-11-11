-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The bound is Mathlib's Schwartz–Zippel lemma
-- (`MvPolynomial.schwartz_zippel_sum_degreeOf`), applied in two blocks.
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# The ring map drawn in two parts (π1-rec4): Schwartz–Zippel in two blocks

π1-rec4 draws the ring switch's six map challenges in two queries: `f_0 … f_3` with `t` (after `C2`'s commitment) and
`f_4, f_5` with `ρ` (after the values at `t`), `docs/leanvm/univariate/SPEC.md` §14.5 (2). For dishonest slices the ring
switch's relation is a nonzero polynomial `P(f_0, …, f_5)` of degree at most `1` in each `f_j`, its coefficients fixed
before `f_0` is drawn. Written `P = Σ_m c_m(f_0 … f_3) f_4^{m_4} f_5^{m_5}` (`P` a polynomial in two variables over
the polynomials in four), **`ring_split_first`**: some `c_m` is nonzero, and it vanishes at no more than `4 |E|^3` of
the `|E|^4` values of `(f_0 … f_3)` (`≤ 4/|E|` for the `t`-query); **`ring_split_second`**: where it does not vanish,
`P` with `f_0 … f_3` substituted is a nonzero polynomial in `f_4, f_5`, which vanishes at no more than `2 |E|` of the
`|E|^2` values (`≤ 2/|E|` for the `ρ`-query). Both are statements about any integral domain `K` with finitely many
elements, at every polynomial of degree at most `1` in each variable.
-/

namespace UniKeccakSound.Rec4

open MvPolynomial Finset

variable {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K] [Fintype K]

/-- Schwartz–Zippel on the whole of `K`, degree at most `1` in each of `n` variables: at most `n |K|^(n−1)` zeros. -/
theorem card_zeros_le {n : ℕ} (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) (hdeg : ∀ i, p.degreeOf i ≤ 1) :
    ((Finset.univ.filter fun x : Fin n → K ↦ eval x p = 0).card : ℚ≥0) / (Fintype.card K : ℚ≥0) ^ n ≤
      n / Fintype.card K := by
  have h := schwartz_zippel_sum_degreeOf hp (fun _ ↦ (Finset.univ : Finset K))
  simp only [Finset.card_univ, Finset.prod_const, Fintype.piFinset_univ, Fintype.card_fin] at h
  refine h.trans ?_
  calc ∑ i : Fin n, ((p.degreeOf i : ℚ≥0) / Fintype.card K)
      ≤ ∑ _i : Fin n, ((1 : ℚ≥0) / Fintype.card K) := by
        gcongr with i
        exact_mod_cast hdeg i
    _ = n / Fintype.card K := by simp [Finset.sum_const, div_eq_mul_inv]

/-- **The first query** (`t`, with `f_0 … f_3`): a polynomial in two variables over the polynomials in four, nonzero,
of degree at most `1` in each of the four inner variables: one of its coefficients is nonzero, and that coefficient
vanishes at at most a `4/|K|` fraction of `(f_0 … f_3)`. -/
theorem ring_split_first (P : MvPolynomial (Fin 2) (MvPolynomial (Fin 4) K)) (hP : P ≠ 0)
    (hin : ∀ m i, (P.coeff m).degreeOf i ≤ 1) :
    ∃ m, P.coeff m ≠ 0 ∧
      ((Finset.univ.filter fun g : Fin 4 → K ↦ eval g (P.coeff m) = 0).card : ℚ≥0) /
          (Fintype.card K : ℚ≥0) ^ 4 ≤ 4 / Fintype.card K := by
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hP
  refine ⟨m, hm, ?_⟩
  have := card_zeros_le (P.coeff m) hm (hin m)
  simpa using this

omit [IsDomain K] [DecidableEq K] [Fintype K] in
/-- Substituting `f_0 … f_3` keeps the outer degrees at most `1`. -/
theorem degreeOf_map_le (P : MvPolynomial (Fin 2) (MvPolynomial (Fin 4) K)) (g : Fin 4 → K) (i : Fin 2) :
    (P.map (eval g)).degreeOf i ≤ P.degreeOf i := by
  rw [degreeOf_le_iff]
  intro m hm
  exact monomial_le_degreeOf i (support_map_subset _ _ hm)

/-- **The second query** (`ρ`, with `f_4, f_5`): where the coefficient `c_m` does not vanish at `(f_0 … f_3) = g`, the
polynomial `P` with `g` substituted is nonzero in `f_4, f_5`, and vanishes at at most a `2/|K|` fraction of them. -/
theorem ring_split_second (P : MvPolynomial (Fin 2) (MvPolynomial (Fin 4) K)) (hout : ∀ i, P.degreeOf i ≤ 1)
    (m : Fin 2 →₀ ℕ) (g : Fin 4 → K) (hg : eval g (P.coeff m) ≠ 0) :
    P.map (eval g) ≠ 0 ∧
      ((Finset.univ.filter fun h : Fin 2 → K ↦ eval h (P.map (eval g)) = 0).card : ℚ≥0) /
          (Fintype.card K : ℚ≥0) ^ 2 ≤ 2 / Fintype.card K := by
  have hne : P.map (eval g) ≠ 0 := by
    intro h
    apply hg
    have := congrArg (fun q : MvPolynomial (Fin 2) K ↦ q.coeff m) h
    simpa [coeff_map] using this
  refine ⟨hne, ?_⟩
  have := card_zeros_le (P.map (eval g)) hne fun i ↦ (degreeOf_map_le P g i).trans (hout i)
  simpa using this

/-- **The two queries together** (`ring_split_first`, `ring_split_second`): for every nonzero `P` of degree at most `1`
in each of its six variables (four inner, two outer), there is a coefficient `c` such that the `t`-query's
`(f_0 … f_3)` makes `c` vanish with probability at most `4/|K|`, and every `(f_0 … f_3)` where it does not leaves `P`
vanishing at the `ρ`-query's `(f_4, f_5)` with probability at most `2/|K|`. -/
theorem ring_split (P : MvPolynomial (Fin 2) (MvPolynomial (Fin 4) K)) (hP : P ≠ 0)
    (hin : ∀ m i, (P.coeff m).degreeOf i ≤ 1) (hout : ∀ i, P.degreeOf i ≤ 1) :
    ∃ c : MvPolynomial (Fin 4) K, c ≠ 0 ∧
      ((Finset.univ.filter fun g : Fin 4 → K ↦ eval g c = 0).card : ℚ≥0) / (Fintype.card K : ℚ≥0) ^ 4 ≤
        4 / Fintype.card K ∧
      ∀ g : Fin 4 → K, eval g c ≠ 0 →
        ((Finset.univ.filter fun h : Fin 2 → K ↦ eval h (P.map (eval g)) = 0).card : ℚ≥0) /
            (Fintype.card K : ℚ≥0) ^ 2 ≤ 2 / Fintype.card K := by
  obtain ⟨m, hm, h1⟩ := ring_split_first P hP hin
  exact ⟨P.coeff m, hm, h1, fun g hg ↦ (ring_split_second P hout m g hg).2⟩

end UniKeccakSound.Rec4
