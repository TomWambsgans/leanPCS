-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the novel basis's halves, degrees and the division by `w_m`, for the honest prover's tables.
import E2ECompleteness.PcsNovel
import QuotientSecurity.Concrete

/-!
# The novel basis by halves, and the division by `Z = w_m`

For `nov 0 k f = Σ_{j < 2^k} f_j X_j` (`PcsNovel.lean`):

* `nov_split`: `nov 0 (k+1) f = nov 0 k f_low + w_k · nov 0 k f_high`;
* `natDegree_basisAt`, `natDegree_nov_lt`, `nov_eval_zero`: `X_j` is monic of degree `j`, `nov 0 k f` of degree
  below `2^k`, its value at `0` is `f 0`;
* `nov_eq_zero`, `nov_high_zero`: a zero polynomial has zero entries; one of degree below `2^k` on `k + 1` digits
  has a zero high half;
* **`nov_divmod`**: for `f` on `2^(m+2)` entries, zero past `2^(m+1)`, `q = nov 0 (m+2) f` has `q %ₘ w_m =
  nov 0 m f` and `q /ₘ w_m = nov 0 m f(2^m + ·) + f(2^(m+1)) (w_m + 1)`, so `(q /ₘ w_m)(0) = f(2^m) + f(2^(m+1))`;
* `divByMonic_add`, `divByMonic_C_mul`: the division by a monic polynomial is linear;
* `divByMonic_eval_zero`: for `Z = X^n + R`, `deg R ≤ n − 2`, and `deg f ≤ n + 1`, `(f /ₘ Z)(0)` is `f`'s
  coefficient `n`; `digitPoly_sub_le`: `w_k = X^(2^k) + R`, `deg R ≤ 2^k / 2`.
-/

set_option autoImplicit false

open Finset Polynomial
open QuotientSecurity

namespace E2ECompleteness.Pcs.Novel

variable {F : Type} [Field F] [CharP F 2]

theorem digit_monic (k : ℕ) : (digitPoly k : F[X]).Monic := (digitPoly_monic_natDegree k).1

theorem digit_natDegree (k : ℕ) : (digitPoly k : F[X]).natDegree = 2 ^ k := (digitPoly_monic_natDegree k).2

/-! ## Halves -/

theorem basisAt_low (k j : ℕ) (hj : j < 2 ^ k) : basisAt (F := F) 0 (k + 1) j = basisAt 0 k j := by
  unfold basisAt
  rw [Finset.prod_range_succ, Nat.testBit_eq_false_of_lt hj]
  simp

theorem basisAt_high (k j : ℕ) (hj : j < 2 ^ k) :
    basisAt (F := F) 0 (k + 1) (2 ^ k + j) = basisAt 0 k j * digitPoly k := by
  unfold basisAt
  rw [Finset.prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt hj]
  simp only [Bool.not_false, ↓reduceIte, zero_add]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hi)]

/-- **The halves**: `nov 0 (k+1) f = nov 0 k f + w_k · nov 0 k f(2^k + ·)`. -/
theorem nov_split (k : ℕ) (f : ℕ → F) :
    nov 0 (k + 1) f = nov 0 k f + digitPoly k * nov 0 k (fun j => f (2 ^ k + j)) := by
  unfold nov
  rw [pow_succ, mul_two, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun j hj => by rw [basisAt_low k j (Finset.mem_range.mp hj)]
  · exact Finset.sum_congr rfl fun j hj => by rw [basisAt_high k j (Finset.mem_range.mp hj)]; ring

theorem basisAt_monic (k j : ℕ) : (basisAt (F := F) 0 k j).Monic :=
  monic_prod_of_monic _ _ fun i _ => by
    split_ifs
    · exact digit_monic _
    · exact monic_one

theorem natDegree_basisAt : ∀ (k j : ℕ), j < 2 ^ k → (basisAt (F := F) 0 k j).natDegree = j
  | 0, j, hj => by
    have : j = 0 := by simpa using hj
    subst this; simp [basisAt]
  | k + 1, j, hj => by
    by_cases hlo : j < 2 ^ k
    · rw [basisAt_low k j hlo, natDegree_basisAt k j hlo]
    · obtain ⟨j', rfl⟩ : ∃ j', j = 2 ^ k + j' := ⟨j - 2 ^ k, by omega⟩
      have hj' : j' < 2 ^ k := by rw [pow_succ] at hj; omega
      rw [basisAt_high k j' hj', (basisAt_monic k j').natDegree_mul (digit_monic k),
        natDegree_basisAt k j' hj', digit_natDegree]
      ring

theorem natDegree_nov_lt (k : ℕ) (f : ℕ → F) : (nov 0 k f).natDegree < 2 ^ k := by
  have hpos : 0 < 2 ^ k := by positivity
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := 2 ^ k - 1) fun j hj => ?_) (by omega)
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_basisAt k j (Finset.mem_range.mp hj)]
  have := Finset.mem_range.mp hj
  omega

theorem digitPoly_eval_zero (k : ℕ) : (digitPoly k : F[X]).eval 0 = 0 := by
  rw [digitPoly_eval, sq_iterate_zero]

theorem nov_eval_zero : ∀ (k : ℕ) (f : ℕ → F), (nov 0 k f).eval 0 = f 0
  | 0, f => by simp [nov_zero]
  | k + 1, f => by
    rw [nov_split, eval_add, eval_mul, digitPoly_eval_zero, zero_mul, add_zero, nov_eval_zero k f]

/-- **A zero polynomial has zero entries.** -/
theorem nov_eq_zero : ∀ (k : ℕ) (f : ℕ → F), nov 0 k f = 0 → ∀ j < 2 ^ k, f j = 0
  | 0, f, h, j, hj => by
    have : j = 0 := by simpa using hj
    subst this
    rw [nov_zero] at h
    exact C_eq_zero.mp h
  | k + 1, f, h, j, hj => by
    rw [nov_split] at h
    have hH : nov 0 k (fun j => f (2 ^ k + j)) = 0 := by
      by_contra hne
      have hdeg : (digitPoly k * nov 0 k (fun j => f (2 ^ k + j))).natDegree ≥ 2 ^ k := by
        rw [(digit_monic k).natDegree_mul' hne, digit_natDegree]
        omega
      have hL := natDegree_nov_lt k f
      have : nov 0 k f + digitPoly k * nov 0 k (fun j => f (2 ^ k + j)) ≠ 0 := by
        intro h0
        have e : digitPoly k * nov 0 k (fun j => f (2 ^ k + j)) = -nov 0 k f := by
          rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h0
        rw [e, natDegree_neg] at hdeg
        omega
      exact this h
    rw [hH, mul_zero, add_zero] at h
    by_cases hlo : j < 2 ^ k
    · exact nov_eq_zero k f h j hlo
    · have := nov_eq_zero k _ hH (j - 2 ^ k) (by rw [pow_succ] at hj; omega)
      rwa [show 2 ^ k + (j - 2 ^ k) = j by omega] at this

theorem nov_sub (k : ℕ) (f g : ℕ → F) : nov 0 k (fun j => f j - g j) = nov 0 k f - nov 0 k g := by
  simp only [nov, C_sub, sub_mul, Finset.sum_sub_distrib]

/-- **Equal polynomials have equal entries.** -/
theorem nov_inj (k : ℕ) {f g : ℕ → F} (h : nov 0 k f = nov 0 k g) : ∀ j < 2 ^ k, f j = g j := by
  intro j hj
  have := nov_eq_zero k (fun j => f j - g j) (by rw [nov_sub, h, sub_self]) j hj
  exact sub_eq_zero.mp this

/-- **A polynomial of degree below `2^k` on `k + 1` digits has a zero high half.** -/
theorem nov_high_zero (k : ℕ) (f : ℕ → F) (h : (nov 0 (k + 1) f).natDegree < 2 ^ k) :
    ∀ j < 2 ^ k, f (2 ^ k + j) = 0 := by
  rw [nov_split] at h
  have hH : nov 0 k (fun j => f (2 ^ k + j)) = 0 := by
    by_contra hne
    have hdeg : (digitPoly k * nov 0 k (fun j => f (2 ^ k + j))).natDegree ≥ 2 ^ k := by
      rw [(digit_monic k).natDegree_mul' hne, digit_natDegree]
      omega
    have hL := natDegree_nov_lt k f
    have e : digitPoly k * nov 0 k (fun j => f (2 ^ k + j)) =
        (nov 0 k f + digitPoly k * nov 0 k (fun j => f (2 ^ k + j))) - nov 0 k f := by ring
    have := natDegree_sub_le (nov 0 k f + digitPoly k * nov 0 k (fun j => f (2 ^ k + j))) (nov 0 k f)
    rw [← e] at this
    omega
  exact nov_eq_zero k _ hH

/-- The polynomial of a table zero but at its first entry. -/
theorem nov_single (k : ℕ) (f : ℕ → F) (h : ∀ j, 0 < j → j < 2 ^ k → f j = 0) : nov 0 k f = C (f 0) := by
  unfold nov
  rw [Finset.sum_eq_single 0 (fun j hj hj0 => by rw [h j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.mp hj), C_0,
    zero_mul]) (fun h0 => absurd (Finset.mem_range.mpr (by positivity)) h0)]
  simp [basisAt]

/-! ## The division by a monic polynomial -/

theorem divByMonic_add {Z : F[X]} (hZ : Z.Monic) (f g : F[X]) : (f + g) /ₘ Z = f /ₘ Z + g /ₘ Z := by
  refine (div_modByMonic_unique (f /ₘ Z + g /ₘ Z) (f %ₘ Z + g %ₘ Z) hZ ⟨?_, ?_⟩).1
  · have h1 := modByMonic_add_div f Z
    have h2 := modByMonic_add_div g Z
    linear_combination h1 + h2
  · exact lt_of_le_of_lt (degree_add_le _ _) (max_lt (degree_modByMonic_lt _ hZ) (degree_modByMonic_lt _ hZ))

theorem divByMonic_C_mul {Z : F[X]} (hZ : Z.Monic) (a : F) (f : F[X]) : (C a * f) /ₘ Z = C a * (f /ₘ Z) := by
  refine (div_modByMonic_unique (C a * (f /ₘ Z)) (C a * (f %ₘ Z)) hZ ⟨?_, ?_⟩).1
  · have h1 := modByMonic_add_div f Z
    linear_combination C a * h1
  · by_cases ha : a = 0
    · rw [ha, C_0, zero_mul, degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by rw [Ne, degree_eq_bot]; exact hZ.ne_zero)
    · rw [degree_C_mul ha]
      exact degree_modByMonic_lt _ hZ

theorem divByMonic_of_lt {Z f : F[X]} (hZ : Z.Monic) (h : f.natDegree < Z.natDegree) : f /ₘ Z = 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · exact (divByMonic_eq_zero_iff hZ).mpr ((degree_lt_degree h))

/-- **The division by `w_m`** of a polynomial on `m + 2` digits zero past `2^(m+1)`. -/
theorem nov_divmod (m : ℕ) (f : ℕ → F) (hf : ∀ j, 2 ^ (m + 1) < j → j < 2 ^ (m + 2) → f j = 0) :
    nov 0 (m + 2) f %ₘ digitPoly m = nov 0 m f ∧
      nov 0 (m + 2) f /ₘ digitPoly m =
        nov 0 m (fun j => f (2 ^ m + j)) + C (f (2 ^ (m + 1))) * (digitPoly m + 1) := by
  have htop : nov 0 (m + 1) (fun j => f (2 ^ (m + 1) + j)) = C (f (2 ^ (m + 1))) := by
    rw [nov_single (m + 1) _ fun j hj hj' => hf _ (by omega) (by rw [pow_succ 2 (m + 1)]; omega), add_zero]
  have hq : nov 0 (m + 2) f = nov 0 m f + digitPoly m *
      (nov 0 m (fun j => f (2 ^ m + j)) + C (f (2 ^ (m + 1))) * (digitPoly m + 1)) := by
    rw [nov_split (m + 1), htop, nov_split m]
    have hd := digit_sq (F := F) m
    have h2 : (2 : F[X]) = 0 := CharTwo.two_eq_zero
    linear_combination (-C (f (2 ^ (m + 1)))) * hd + (-(C (f (2 ^ (m + 1))) * digitPoly m)) * h2
  have hdeg : (nov 0 m f).degree < (digitPoly m : F[X]).degree := by
    rw [degree_eq_natDegree (digit_monic m).ne_zero, digit_natDegree]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast natDegree_nov_lt m f)
  obtain ⟨h1, h2⟩ := div_modByMonic_unique _ _ (digit_monic m) ⟨hq.symm, hdeg⟩
  exact ⟨h2, h1⟩

/-- **`(q /ₘ w_m)(0)`** for `q` on `m + 2` digits zero past `2^(m+1)`: `f(2^m) + f(2^(m+1))`. -/
theorem nov_divByMonic_eval_zero (m : ℕ) (f : ℕ → F) (hf : ∀ j, 2 ^ (m + 1) < j → j < 2 ^ (m + 2) → f j = 0) :
    (nov 0 (m + 2) f /ₘ digitPoly m).eval 0 = f (2 ^ m) + f (2 ^ (m + 1)) := by
  rw [(nov_divmod m f hf).2, eval_add, eval_mul, eval_C, eval_add, eval_one, digitPoly_eval_zero,
    nov_eval_zero, zero_add, mul_one, add_zero]

/-! ## `w_k` is `X^(2^k)` but low terms -/

theorem digitPoly_sub_le : ∀ k : ℕ, (digitPoly k - X ^ 2 ^ k : F[X]).natDegree ≤ 2 ^ k / 2
  | 0 => by simp [digitPoly]
  | k + 1 => by
    have ih := digitPoly_sub_le k
    set R : F[X] := digitPoly k - X ^ 2 ^ k with hR
    have hd : (digitPoly (k + 1) : F[X]) = digitPoly k ^ 2 + digitPoly k := by simp [digitPoly]
    have hk : (digitPoly k : F[X]) = X ^ 2 ^ k + R := by rw [hR]; ring
    have hx : (X : F[X]) ^ 2 ^ (k + 1) = (X ^ 2 ^ k) ^ 2 := by rw [← pow_mul, pow_succ]
    have e : (digitPoly (k + 1) - X ^ 2 ^ (k + 1) : F[X]) = R ^ 2 + X ^ 2 ^ k + R := by
      rw [hd, hk, hx]
      have h2 : (2 : F[X]) = 0 := CharTwo.two_eq_zero
      linear_combination (X ^ 2 ^ k * R) * h2
    rw [e]
    have hpos : 2 ^ k / 2 ≤ 2 ^ k := Nat.div_le_self _ _
    have h1 : (R ^ 2).natDegree ≤ 2 ^ k := by
      refine natDegree_pow_le.trans ?_
      have : 2 * (2 ^ k / 2) ≤ 2 ^ k := Nat.mul_div_le _ _
      calc 2 * R.natDegree ≤ 2 * (2 ^ k / 2) := Nat.mul_le_mul_left _ ih
        _ ≤ 2 ^ k := this
    have h2 : (X ^ 2 ^ k : F[X]).natDegree ≤ 2 ^ k := natDegree_X_pow_le _
    have h3 : R.natDegree ≤ 2 ^ k := ih.trans hpos
    rw [show 2 ^ (k + 1) / 2 = 2 ^ k by rw [pow_succ]; omega]
    exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h1 h2) h3

/-- **`(f /ₘ Z)(0)` is `f`'s coefficient `n`** for `Z = X^n + R` with `deg R ≤ n − 2` and `deg f ≤ n + 1`. -/
theorem divByMonic_eval_zero (n : ℕ) (hn : 2 ≤ n) (Z : F[X]) (hZ : Z.Monic)
    (hR : (Z - X ^ n).natDegree ≤ n - 2) (f : F[X]) (hf : f.natDegree ≤ n + 1) :
    (f /ₘ Z).eval 0 = f.coeff n := by
  set Q : F[X] := C (f.coeff (n + 1)) * X + C (f.coeff n) with hQ
  have hdiv : f /ₘ Z = Q := by
    refine (div_modByMonic_unique Q (f - Z * Q) hZ ⟨by ring, ?_⟩).1
    have hZn : Z.natDegree = n := by
      have : Z = X ^ n + (Z - X ^ n) := by ring
      rw [this, natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_X_pow]; omega), natDegree_X_pow]
    rw [degree_eq_natDegree hZ.ne_zero, hZn]
    refine (degree_lt_iff_coeff_zero _ _).mpr fun i hi => ?_
    have hi' : n ≤ i := by exact_mod_cast hi
    have eZ : Z * Q = X ^ n * Q + (Z - X ^ n) * Q := by ring
    have hRQ : ((Z - X ^ n) * Q).natDegree ≤ n - 1 := by
      refine natDegree_mul_le.trans ?_
      have : Q.natDegree ≤ 1 := by
        rw [hQ]
        exact natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans (by simp)) (by simp)
      omega
    rw [coeff_sub, eZ, coeff_add, coeff_eq_zero_of_natDegree_lt (p := (Z - X ^ n) * Q) (by omega), add_zero,
      coeff_X_pow_mul', if_pos hi']
    rw [hQ]
    simp only [coeff_add, coeff_C_mul, coeff_X, coeff_C]
    rcases Nat.lt_or_ge (n + 1) i with h | h
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), if_neg (by omega), if_neg (by omega)]
      ring
    · rcases Nat.eq_or_lt_of_le h with h | h
      · subst h
        rw [show n + 1 - n = 1 by omega, if_pos rfl, if_neg (by omega)]
        ring
      · obtain rfl : i = n := by omega
        rw [Nat.sub_self, if_neg (by omega), if_pos rfl]
        ring
  rw [hdiv, hQ]
  simp

end E2ECompleteness.Pcs.Novel
