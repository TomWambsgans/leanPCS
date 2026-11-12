-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `mulX` is `crates/membership/quotient/src/protocol.rs`'s
-- `mul_x`; the Lagrange argument is `formal/RecPiop`'s (`SumDeg.lean`).
import RecCompose.Pi2Prover
import RecCompose.Points
import UniKeccakComplete.K.AlgCBasis

/-!
# π2v4's `H = x h` in the novel basis

The honest prover puts `H = x h` in `H`'s slots as `mulX` of `h`'s novel coefficients (`quotient::protocol::mul_x`: no
product, the basis' own structure, `h`'s top coefficient dropped). Here:

* **`lowBit`**: a power of two dividing `j > 0` (`lowBit_spec`), `lowBit (2^m) = 2^m`, `lowBit (2^m + j) = lowBit j`
  for `0 < j < 2^m`, and `j + lowBit j ≤ 2^m` for `0 < j < 2^m`;
* **`X_mul_novP`**: `x · Σ_k d_k X_k = Σ_k (mul_x d)_k X_k + d_{2^m − 1} w_m` (the product's coefficient `2^m` is `F`'s
  top one: the basis is monic), by induction on the top variable with `w_m² = w_{m+1} + w_m`;
* **`novP_coeff_top`**: the coefficient of `x^(2^m − 1)` of `Σ_k d_k X_k` is `d_{2^m − 1}`;
* **`coeff_top_eq_zero_of_sum`**: a polynomial of degree below `2^L` whose values on `V_L` sum to zero has no
  coefficient of `x^(2^L − 1)` (Lagrange, as `RecPiop.sum_eval_eq_zero_of_natDegree_lt`);
* so **`novP_mulX`**: when the values sum to zero on `V_m`, the polynomial of `mulX` of the novel coefficients is
  `x` times the polynomial.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open LeanVM.Parameters Finset Polynomial
open UniKeccakComplete.AlgC (novP novP_succ novP_zero novP_congr novP_natDegree_lt)
open UniComplete.Domain (wP wP_succ wP_natDegree wP_monic)

/-! ## `lowBit` -/

theorem lowBit_eq {j : ℕ} (hj : 0 < j) : lowBit j = if j % 2 = 1 then 1 else 2 * lowBit (j / 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [lowBit.eq_2]

/-- **`lowBit j` is a power of two dividing `j`**, `j > 0`. -/
theorem lowBit_spec : ∀ j, 0 < j → ∃ k, lowBit j = 2 ^ k ∧ 2 ^ k ∣ j
  | 0, h => absurd h (lt_irrefl 0)
  | j + 1, _ => by
    rw [lowBit_eq (Nat.succ_pos j)]
    split
    · exact ⟨0, rfl, one_dvd _⟩
    · rename_i hodd
      have hpos : 0 < (j + 1) / 2 := by omega
      have hlt : (j + 1) / 2 < j + 1 := by omega
      obtain ⟨k, hk, hd⟩ := lowBit_spec ((j + 1) / 2) hpos
      refine ⟨k + 1, by rw [hk, pow_succ, mul_comm], ?_⟩
      have he : j + 1 = 2 * ((j + 1) / 2) := by omega
      rw [he, pow_succ, mul_comm]
      exact Nat.mul_dvd_mul_left 2 hd
termination_by j => j

theorem lowBit_two_pow : ∀ m : ℕ, lowBit (2 ^ m) = 2 ^ m
  | 0 => by rw [pow_zero, lowBit_eq (by norm_num)]; rfl
  | m + 1 => by
    rw [lowBit_eq (by positivity), ite_eq_right (by rw [pow_succ]; omega), show 2 ^ (m + 1) / 2 = 2 ^ m by
      rw [pow_succ]; omega, lowBit_two_pow m, pow_succ, mul_comm]

/-- `lowBit (2^m + j) = lowBit j` for `0 < j < 2^m`. -/
theorem lowBit_two_pow_add : ∀ (m j : ℕ), 0 < j → j < 2 ^ m → lowBit (2 ^ m + j) = lowBit j
  | 0, j, h0, h1 => by omega
  | m + 1, j, h0, h1 => by
    rw [lowBit_eq (by positivity), lowBit_eq h0]
    have hp : 2 ^ (m + 1) % 2 = 0 := by rw [pow_succ]; omega
    by_cases hj : j % 2 = 1
    · rw [ite_eq_left (by omega), ite_eq_left hj]
    · rw [ite_eq_right (by omega), ite_eq_right hj, show (2 ^ (m + 1) + j) / 2 = 2 ^ m + j / 2 by rw [pow_succ]; omega,
        lowBit_two_pow_add m (j / 2) (by omega) (by rw [pow_succ] at h1; omega)]

/-- **`j + lowBit j ≤ 2^m`** for `0 < j < 2^m`: both are multiples of `lowBit j`, a power of two at most `2^m`. -/
theorem add_lowBit_le {m j : ℕ} (h0 : 0 < j) (h1 : j < 2 ^ m) : j + lowBit j ≤ 2 ^ m := by
  obtain ⟨k, hk, hd⟩ := lowBit_spec j h0
  rw [hk]
  have hkle : 2 ^ k ≤ j := Nat.le_of_dvd h0 hd
  have hkm : k ≤ m := by
    by_contra h
    have : 2 ^ m < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨a, rfl⟩ := hd
  have hm : 2 ^ m = 2 ^ k * 2 ^ (m - k) := by rw [← pow_add, Nat.add_sub_cancel' hkm]
  rw [hm] at h1 ⊢
  have ha : a < 2 ^ (m - k) := Nat.lt_of_mul_lt_mul_left h1
  have hk0 : 0 < 2 ^ k := Nat.two_pow_pos k
  nlinarith

/-! ## `mul_x` -/

/-- **`mul_x`'s coefficient `j`** on `2^m` coefficients `d`: `0` at `0`, `d_{j−1} + d_{j + low(j) − 1}` (zero past
`2^m`). -/
def mxF (m : ℕ) (d : ℕ → E) (j : ℕ) : E :=
  if j = 0 then 0 else d (j - 1) + (if j + lowBit j - 1 < 2 ^ m then d (j + lowBit j - 1) else 0)

/-- `Σ_k (d_k + [k = 0] c) X_k = Σ_k d_k X_k + c`. -/
theorem novP_add_const : ∀ (m : ℕ) (d : ℕ → E) (c : E),
    novP m (fun k ↦ d k + if k = 0 then c else 0) = novP m d + C c
  | 0, d, c => by simp [novP_zero, C_add]
  | m + 1, d, c => by
    rw [novP_succ, novP_succ, novP_add_const m d c]
    have : (fun k ↦ d (2 ^ m + k) + if 2 ^ m + k = 0 then c else 0) = fun k ↦ d (2 ^ m + k) := by
      funext k
      rw [ite_eq_right (by positivity), add_zero]
    rw [this]
    ring

/-- **`x` times a novel polynomial**: `x Σ_k d_k X_k = Σ_k (mul_x d)_k X_k + d_{2^m − 1} w_m`. -/
theorem X_mul_novP : ∀ (m : ℕ) (d : ℕ → E), X * novP m d = novP m (mxF m d) + C (d (2 ^ m - 1)) * wP m
  | 0, d => by
    simp only [novP_zero, mxF, pow_zero, Nat.sub_self, ite_true, C_0, zero_add, UniComplete.Domain.wP_zero]
    ring
  | m + 1, d => by
    set dh : ℕ → E := fun k ↦ d (2 ^ m + k) with hdh
    have ihl := X_mul_novP m d
    have ihh := X_mul_novP m dh
    -- the low half of `mul_x` on `2^(m+1)` is `mul_x` on `2^m`
    have hlo : novP m (mxF (m + 1) d) = novP m (mxF m d) := by
      refine novP_congr m fun k hk ↦ ?_
      unfold mxF
      by_cases hk0 : k = 0
      · simp [hk0]
      · have hle := add_lowBit_le (by omega : 0 < k) hk
        rw [ite_eq_right hk0, ite_eq_right hk0, ite_eq_left (show k + lowBit k - 1 < 2 ^ (m + 1) by rw [pow_succ]; omega),
          ite_eq_left (show k + lowBit k - 1 < 2 ^ m by omega)]
    -- the high half: `mul_x` of the high half, plus `d_{2^m − 1} + d_{2^(m+1) − 1}` at `X_{2^m}`
    have hhi : novP m (fun k ↦ mxF (m + 1) d (2 ^ m + k)) =
        novP m (mxF m dh) + C (d (2 ^ m - 1) + d (2 ^ (m + 1) - 1)) := by
      rw [← novP_add_const]
      refine novP_congr m fun k hk ↦ ?_
      by_cases hk0 : k = 0
      · subst hk0
        have e1 : 2 ^ m + 2 ^ m - 1 = 2 ^ (m + 1) - 1 := by rw [pow_succ]; omega
        have e2 : 2 ^ (m + 1) - 1 < 2 ^ (m + 1) := by have := Nat.one_le_two_pow (n := m + 1); omega
        have e3 : 2 ^ m ≠ 0 := by positivity
        simp only [mxF, Nat.add_zero, lowBit_two_pow, e1, ite_eq_right e3, ite_eq_left e2, ↓reduceIte, zero_add]
      · have hlb := lowBit_two_pow_add m k (by omega) hk
        have hle := add_lowBit_le (by omega : 0 < k) hk
        have e0 : 2 ^ m + k ≠ 0 := by positivity
        have e1 : 2 ^ m + k + lowBit k - 1 < 2 ^ (m + 1) := by rw [pow_succ]; omega
        have e2 : k + lowBit k - 1 < 2 ^ m := by omega
        have e3 : 2 ^ m + k - 1 = 2 ^ m + (k - 1) := by omega
        have e4 : 2 ^ m + k + lowBit k - 1 = 2 ^ m + (k + lowBit k - 1) := by omega
        have e5 : 2 ^ m + (k + lowBit k - 1) < 2 ^ (m + 1) := by rw [← e4]; exact e1
        simp only [mxF, ite_eq_right e0, ite_eq_right hk0, hlb, ite_eq_left e2, add_zero, e3, e4, hdh, ite_eq_left e5]
    have htop : dh (2 ^ m - 1) = d (2 ^ (m + 1) - 1) := by
      rw [hdh]; simp only; congr 1; rw [pow_succ]; omega
    rw [htop] at ihh
    rw [novP_succ, novP_succ, hlo, hhi, wP_succ, C_add]
    have h2X : (2 : E[X]) = 0 := CharTwo.two_eq_zero
    linear_combination ihl + wP m * ihh - C (d (2 ^ (m + 1) - 1)) * wP m * h2X

/-! ## The top coefficient -/

/-- **The coefficient of `x^(2^m − 1)` of a novel polynomial is its top novel coefficient** (`X_{2^m − 1}` is monic of
degree `2^m − 1`, the others of lower degree). -/
theorem novP_coeff_top : ∀ (m : ℕ) (d : ℕ → E), (novP m d).coeff (2 ^ m - 1) = d (2 ^ m - 1)
  | 0, d => by simp [novP_zero]
  | m + 1, d => by
    rw [novP_succ, coeff_add,
      coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (novP_natDegree_lt m d) (by rw [pow_succ]; omega)), zero_add,
      show 2 ^ (m + 1) - 1 = 2 ^ m + (2 ^ m - 1) by rw [pow_succ]; omega,
      coeff_mul_add_eq_of_natDegree_le (wP_natDegree m).le
        (Nat.le_sub_one_of_lt (novP_natDegree_lt m fun k ↦ d (2 ^ m + k))),
      novP_coeff_top m, ← wP_natDegree m, (wP_monic m).coeff_natDegree, one_mul]

/-- **A polynomial below `2^L` whose values on `V_L` sum to zero has no `x^(2^L − 1)`** (Lagrange: that coefficient is
`c⁻¹ Σ_i p(ω_i)`, `RecPiop.sum_eval_eq_zero_of_natDegree_lt`'s argument). -/
theorem coeff_top_eq_zero_of_sum {ω : ℕ → E} {n L : ℕ} (hP : RecPiop.Points ω n) (hL : L ≤ n) (p : E[X])
    (hp : p.natDegree < 2 ^ L) (hs : ∑ i ∈ range (2 ^ L), p.eval (ω i) = 0) : p.coeff (2 ^ L - 1) = 0 := by
  set s := range (2 ^ L)
  have hinj : Set.InjOn ω s := fun a ha b hb h => by
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    have hn : 2 ^ L ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hL
    exact hP.inj a (by omega) b (by omega) h
  have hdeg : p.degree < s.card := by
    rw [Finset.card_range]
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact_mod_cast hp
  have hint := Lagrange.eq_interpolate hinj hdeg
  set c := ∏ k ∈ (range (2 ^ L)).erase 0, ω k with hc
  have hterm : ∀ i ∈ s, (C (p.eval (ω i)) * Lagrange.basis s ω i).coeff (s.card - 1) = p.eval (ω i) * c⁻¹ := by
    intro i hi
    rw [Polynomial.coeff_C_mul, RecPiop.coeff_basis_top s ω hi, Finset.prod_inv_distrib,
      RecPiop.prod_erase_add_eq hP hL (Finset.mem_range.mp hi)]
  rw [show 2 ^ L - 1 = s.card - 1 by rw [Finset.card_range], hint, Lagrange.interpolate_apply,
    Polynomial.finsetSum_coeff, Finset.sum_congr rfl hterm, ← Finset.sum_mul, hs, zero_mul]

/-! ## `mulX` -/

/-- `mulX`'s entries are `mxF`'s below the size. -/
theorem mulX_getD (f : Array E) {m : ℕ} (hf : f.size = 2 ^ m) {k : ℕ} (hk : k < 2 ^ m) :
    (mulX f).getD k 0 = mxF m (fun j ↦ f.getD j 0) k := by
  have hk' : k < (mulX f).size := by simp [mulX, hf, hk]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk', Option.getD_some]
  simp only [mulX, Array.getElem_ofFn, mxF]
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hle := add_lowBit_le (by omega : 0 < k) hk
    rw [ite_eq_right hk0, ite_eq_right hk0, ite_eq_left (show k + lowBit k - 1 < 2 ^ m by omega)]

/-- **`x` times a novel polynomial whose values on `V_m` sum to zero is `mulX` of its coefficients** (`H = x h`:
`h`'s top novel coefficient is zero, so `mul_x` drops nothing). -/
theorem novP_mulX (f : Array E) {m : ℕ} (hm : m ≤ 32) (hf : f.size = 2 ^ m)
    (hs : ∑ i ∈ range (2 ^ m), (novP m fun j ↦ f.getD j 0).eval (pi2Omega i) = 0) :
    novP m (fun k ↦ (mulX f).getD k 0) = X * novP m (fun k ↦ f.getD k 0) := by
  have htop : f.getD (2 ^ m - 1) 0 = 0 := by
    rw [← novP_coeff_top m (fun j ↦ f.getD j 0)]
    exact coeff_top_eq_zero_of_sum (RecPiop.Points.ofCantor UniComplete.Domain.basisE) hm _
      (novP_natDegree_lt m _) hs
  rw [X_mul_novP, htop, C_0, zero_mul, add_zero]
  exact novP_congr m fun k hk ↦ mulX_getD f hf hk

end RecCompose

/-- info: 'RecCompose.X_mul_novP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.X_mul_novP

/-- info: 'RecCompose.novP_mulX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.novP_mulX
