-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: `crates/membership/quotient/src/protocol.rs`'s `mul_x` and `div_x` (the Statement's `mulX`, `divX`)
-- are the product and the quotient by `x` in the novel basis.
import QuotientSecurity.Tables
import PcsQuotient.Prover

/-!
# Products and quotients by `x` in the novel basis

The novel basis at level `s` over `k` digits: `X_j = Π_{bit i of j} w_{s+i}` (`w_k = digitPoly k`), and
`nov s k f = Σ_{j < 2^k} f_j X_j`. With `w_s² = w_{s+1} + w_s` (characteristic two):

* `mul_nov`: `w_s · nov s k f = nov s k (M f) + f_{2^k − 1} w_{s+k}`, `M f j = f (j − 1) + f (j + low j − 1)` for
  `j ≥ 1`, `M f 0 = 0`: one level's product is the next level's on the odd half (`nov_succ`), so `M` does not
  depend on the level; `low` is the Statement's `lowBit` (`lowBit_odd`, `lowBit_even`);
* `mulX_getD`: the Statement's `mulX` is `M`;
* `divX_rec`: the Statement's `divX g` solves `f i = g (i + 1) + f (i + low (i + 1))`, its top zero;
* **`X_mul_nov_divX`**: `X · nov 0 k (divX g) = nov 0 k g − g 0`.
-/

set_option autoImplicit false

open Finset Polynomial
open QuotientSecurity

namespace E2ECompleteness.Pcs.Novel

/-! ## `lowBit` -/

theorem two_pow_64_sub_mod {j : ℕ} (h0 : 0 < j) (h : j < 2 ^ 64) : (2 ^ 64 - j) % 2 ^ 64 = 2 ^ 64 - j :=
  Nat.mod_eq_of_lt (by omega)

theorem testBit_lowBit_succ (x i : ℕ) (hx : x + 1 < 2 ^ 64) (hi : i < 64) :
    (PcsQuotient.lowBit (x + 1)).testBit i = ((x + 1).testBit i && !x.testBit i) := by
  unfold PcsQuotient.lowBit
  rw [two_pow_64_sub_mod (by omega) hx, Nat.testBit_land, Nat.testBit_two_pow_sub_succ (by omega)]
  simp [hi]

theorem testBit_ge_64 {x i : ℕ} (hx : x < 2 ^ 64) (hi : 64 ≤ i) : x.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

theorem lowBit_lt {j : ℕ} (hj : j < 2 ^ 64) : PcsQuotient.lowBit j < 2 ^ 64 := by
  unfold PcsQuotient.lowBit
  exact lt_of_le_of_lt Nat.and_le_left hj

/-- `low (2y + 1) = 1`. -/
theorem lowBit_odd (y : ℕ) (h : 2 * y + 1 < 2 ^ 64) : PcsQuotient.lowBit (2 * y + 1) = 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · rw [testBit_lowBit_succ (2 * y) i h hi]
    rcases i with _ | i
    · simp [Nat.testBit_zero]
    · rw [Nat.testBit_succ, Nat.testBit_succ]
      have e1 : (2 * y + 1) / 2 = y := by omega
      have e2 : 2 * y / 2 = y := by omega
      rw [e1, e2]
      cases y.testBit i <;> simp [Nat.testBit_succ]
  · rw [testBit_ge_64 (lowBit_lt (by omega)) (by omega), testBit_ge_64 (by norm_num) (by omega)]

/-- `low (2y) = 2 low y` for `y ≥ 1`. -/
theorem lowBit_even (y : ℕ) (hy : 0 < y) (h : 2 * y < 2 ^ 64) :
    PcsQuotient.lowBit (2 * y) = 2 * PcsQuotient.lowBit y := by
  apply Nat.eq_of_testBit_eq
  intro i
  obtain ⟨x, rfl⟩ : ∃ x, y = x + 1 := ⟨y - 1, by omega⟩
  by_cases hi : i < 64
  · rw [show 2 * (x + 1) = (2 * x + 1) + 1 by ring, testBit_lowBit_succ (2 * x + 1) i (by omega) hi]
    rcases i with _ | i
    · simp [Nat.testBit_zero, Nat.mul_mod_right]
    · rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      have e1 : (2 * x + 1 + 1) / 2 = x + 1 := by omega
      have e2 : (2 * x + 1) / 2 = x := by omega
      have e3 : 2 * PcsQuotient.lowBit (x + 1) / 2 = PcsQuotient.lowBit (x + 1) := by omega
      rw [e1, e2, e3, testBit_lowBit_succ x i (by omega) (by omega)]
  · rw [testBit_ge_64 (lowBit_lt (by omega)) (by omega)]
    have : 2 * PcsQuotient.lowBit (x + 1) < 2 ^ 64 := by
      have := lowBit_lt (j := x + 1) (by omega)
      unfold PcsQuotient.lowBit at this ⊢
      -- `low (x + 1) ≤ x + 1`, and `2 (x + 1) < 2^64`.
      have hle : (x + 1) &&& (2 ^ 64 - (x + 1)) % 2 ^ 64 ≤ x + 1 := Nat.and_le_left
      omega
    rw [testBit_ge_64 this (by omega)]

theorem lowBit_pos (j : ℕ) (h0 : 0 < j) (h : j < 2 ^ 64) : 0 < PcsQuotient.lowBit j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    obtain ⟨y, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [lowBit_even y (by omega) h]
      have := ih y (by omega) (by omega) (by omega)
      omega
    · rw [lowBit_odd y h]; omega

/-! ## The novel basis at a level -/

variable {F : Type} [Field F] [CharP F 2]

/-- The basis element `X_j` at level `s` over `k` digits: `Π_{bit i of j, i < k} w_{s+i}`. -/
noncomputable def basisAt (s k j : ℕ) : F[X] := ∏ i ∈ range k, if j.testBit i then digitPoly (s + i) else 1

/-- **The novel-basis polynomial** at level `s` of `f` on `2^k` coefficients. -/
noncomputable def nov (s k : ℕ) (f : ℕ → F) : F[X] := ∑ j ∈ range (2 ^ k), C (f j) * basisAt s k j

theorem nov_zero (s : ℕ) (f : ℕ → F) : nov s 0 f = C (f 0) := by
  simp [nov, basisAt]

theorem nov_add (s k : ℕ) (f g : ℕ → F) : nov s k (fun j => f j + g j) = nov s k f + nov s k g := by
  simp only [nov, C_add, add_mul, Finset.sum_add_distrib]

theorem nov_congr (s k : ℕ) {f g : ℕ → F} (h : ∀ j < 2 ^ k, f j = g j) : nov s k f = nov s k g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]

theorem basisAt_even (s k j : ℕ) : basisAt (F := F) s (k + 1) (2 * j) = basisAt (s + 1) k j := by
  unfold basisAt
  rw [Finset.prod_range_succ']
  simp only [Nat.testBit_zero, Nat.mul_mod_right, decide_eq_true_eq, if_neg (by decide : ¬ (0 = 1)), mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.testBit_succ, show 2 * j / 2 = j by omega, show s + (i + 1) = s + 1 + i by ring]

theorem basisAt_odd (s k j : ℕ) :
    basisAt (F := F) s (k + 1) (2 * j + 1) = digitPoly s * basisAt (s + 1) k j := by
  unfold basisAt
  rw [Finset.prod_range_succ', mul_comm]
  simp only [Nat.testBit_zero, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.one_mod, decide_true, if_true,
    add_zero]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.testBit_succ, show (2 * j + 1) / 2 = j by omega, show s + (i + 1) = s + 1 + i by ring]

/-- A sum over `2^(k+1)` by its even and odd terms. -/
theorem sum_range_two_pow_succ {M : Type*} [AddCommMonoid M] (k : ℕ) (g : ℕ → M) :
    ∑ j ∈ range (2 ^ (k + 1)), g j = ∑ j ∈ range (2 ^ k), g (2 * j) + ∑ j ∈ range (2 ^ k), g (2 * j + 1) := by
  rw [pow_succ, mul_comm, ← Finset.sum_range_add_sum_Ico _ (show 2 ^ k ≤ 2 * 2 ^ k by omega)]
  -- Reindex by parity.
  have : ∀ n : ℕ, ∑ j ∈ range (2 * n), g j = ∑ j ∈ range n, g (2 * j) + ∑ j ∈ range n, g (2 * j + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ, Finset.sum_range_succ]
      abel
  rw [Finset.sum_range_add_sum_Ico _ (show 2 ^ k ≤ 2 * 2 ^ k by omega), this]

/-- **One level by the parity of the index**: `nov s (k+1) f = nov (s+1) k f_even + w_s nov (s+1) k f_odd`. -/
theorem nov_succ (s k : ℕ) (f : ℕ → F) :
    nov s (k + 1) f = nov (s + 1) k (fun j => f (2 * j)) + digitPoly s * nov (s + 1) k (fun j => f (2 * j + 1)) := by
  unfold nov
  rw [sum_range_two_pow_succ, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by rw [basisAt_even]
  · exact Finset.sum_congr rfl fun j _ => by rw [basisAt_odd]; ring

/-- `w_s² = w_{s+1} + w_s` in characteristic two. -/
theorem digit_sq (s : ℕ) : digitPoly (F := F) s * digitPoly s = digitPoly (s + 1) + digitPoly s := by
  show _ = (X ^ 2 + X).comp (digitPoly s) + _
  rw [add_comp, X_pow_comp, X_comp, pow_two, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-! ## The product by `w_s` -/

/-- The coefficients of `w_s · nov s k f` (but its top term): `M f j = f (j − 1) + f (j + low j − 1)`. -/
def M {R : Type*} [Add R] [Zero R] (f : ℕ → R) (j : ℕ) : R :=
  if j = 0 then 0 else f (j - 1) + f (j + PcsQuotient.lowBit j - 1)

theorem M_odd {R : Type*} [Add R] [Zero R] (f : ℕ → R) (y : ℕ) (h : 2 * y + 1 < 2 ^ 64) :
    M f (2 * y + 1) = f (2 * y) + f (2 * y + 1) := by
  simp only [M, Nat.add_one_ne_zero, ↓reduceIte, lowBit_odd y h]
  congr 1

theorem M_even {R : Type*} [Add R] [Zero R] (f : ℕ → R) (y : ℕ) (h : 2 * y < 2 ^ 64) :
    M f (2 * y) = M (fun j => f (2 * j + 1)) y := by
  by_cases hy : y = 0
  · subst hy; simp [M]
  · have hl := lowBit_pos y (by omega) (by omega)
    simp only [M, show 2 * y ≠ 0 by omega, hy, ↓reduceIte, lowBit_even y (by omega) h]
    congr 1
    · congr 1; omega
    · congr 1; omega

/-- **The product by `w_s` in the novel basis.** -/
theorem mul_nov (k : ℕ) (hk : k ≤ 62) : ∀ (s : ℕ) (f : ℕ → F),
    digitPoly s * nov s k f = nov s k (M f) + C (f (2 ^ k - 1)) * digitPoly (s + k) := by
  induction k with
  | zero =>
    intro s f
    simp [nov_zero, M, mul_comm]
  | succ k ih =>
    intro s f
    have hk' : k ≤ 62 := by omega
    have h2k : 2 ^ k ≤ 2 ^ 62 := Nat.pow_le_pow_right (by norm_num) hk'
    rw [nov_succ, nov_succ]
    -- The even and odd halves of `M f`.
    have hev : nov (s + 1) k (fun j => M f (2 * j)) = nov (s + 1) k (M fun j => f (2 * j + 1)) :=
      nov_congr _ _ fun j hj => M_even f j (by omega)
    have hod : nov (s + 1) k (fun j => M f (2 * j + 1)) =
        nov (s + 1) k (fun j => f (2 * j) + f (2 * j + 1)) :=
      nov_congr _ _ fun j hj => M_odd f j (by omega)
    rw [hev, hod, nov_add]
    have hih := ih hk' (s + 1) (fun j => f (2 * j + 1))
    have htop : 2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ]; omega
    rw [htop, show s + 1 + k = s + (k + 1) by ring] at hih
    rw [mul_add, ← mul_assoc, digit_sq, add_mul, hih]
    ring

/-! ## The Statement's `mulX` and `divX` -/

section Arrays

variable [Inhabited F]

theorem mulX_getD (a : Array F) {j : ℕ} (hj : j < a.size) :
    (PcsQuotient.mulX a).getD j 0 = M (fun i => a.getD i 0) j := by
  unfold PcsQuotient.mulX
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hj, ↓reduceDIte, Option.getD_some, M]

/-- One step of `divX`'s fold. -/
def divStep (g : Array F) (i : ℕ) (f : Array F) : Array F :=
  if i + 1 < g.size then f.set! i (g.getD (i + 1) 0 + f.getD (i + PcsQuotient.lowBit (i + 1)) 0) else f

theorem divX_eq (g : Array F) :
    PcsQuotient.divX g = (List.range' 0 g.size).foldr (divStep g) (Array.replicate g.size 0) := by
  unfold PcsQuotient.divX
  dsimp only
  rw [List.range_eq_range']
  rfl

theorem getD_replicate (n i : ℕ) : (Array.replicate n (0 : F)).getD i 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem getD_set! (f : Array F) (k i : ℕ) (x : F) (hk : k < f.size) :
    (f.set! k x).getD i 0 = if i = k then x else f.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hik : k = i
  · subst hik; simp [hk]
  · simp [hik, Ne.symm hik]

/-- The invariant of the fold from `k`. -/
structure DivInv (g : Array F) (k : ℕ) (f : Array F) : Prop where
  size : f.size = g.size
  below : ∀ i < k, f.getD i 0 = 0
  recur : ∀ i, k ≤ i → i + 1 < g.size → f.getD i 0 = g.getD (i + 1) 0 + f.getD (i + PcsQuotient.lowBit (i + 1)) 0
  top : ∀ i, k ≤ i → g.size ≤ i + 1 → f.getD i 0 = 0

theorem divInv_step (g : Array F) (hg : g.size < 2 ^ 63) (k : ℕ) (hk : k < g.size) (f : Array F)
    (hI : DivInv g (k + 1) f) : DivInv g k (divStep g k f) := by
  have hlow : 0 < PcsQuotient.lowBit (k + 1) := lowBit_pos (k + 1) (by omega) (by omega)
  unfold divStep
  by_cases hk1 : k + 1 < g.size
  · rw [if_pos hk1]
    have hkf : k < f.size := by rw [hI.size]; exact hk
    refine ⟨by simp [hI.size], fun i hi => ?_, fun i hi hi' => ?_, fun i hi hi' => ?_⟩
    · rw [getD_set! f k i _ hkf, if_neg (by omega)]
      exact hI.below i (by omega)
    · rw [getD_set! f k i _ hkf, getD_set! f k _ _ hkf]
      by_cases hik : i = k
      · subst hik
        rw [if_pos rfl, if_neg (by omega)]
      · rw [if_neg hik, if_neg (by omega)]
        exact hI.recur i (by omega) hi'
    · rw [getD_set! f k i _ hkf, if_neg (by omega)]
      exact hI.top i (by omega) hi'
  · rw [if_neg hk1]
    refine ⟨hI.size, fun i hi => ?_, fun i hi hi' => ?_, fun i hi hi' => ?_⟩
    · by_cases hik : i = k
      · subst hik; exact hI.top i (by omega) (by omega)
      · exact hI.below i (by omega)
    · by_cases hik : i = k
      · omega
      · exact hI.recur i (by omega) hi'
    · by_cases hik : i = k
      · subst hik; exact hI.below i (by omega)
      · exact hI.top i (by omega) hi'

theorem divInv_fold (g : Array F) (hg : g.size < 2 ^ 63) : ∀ n ≤ g.size,
    DivInv g (g.size - n) ((List.range' (g.size - n) n).foldr (divStep g) (Array.replicate g.size 0)) := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨by simp, fun i _ => getD_replicate _ _, fun i hi hi' => by omega, fun i _ _ => getD_replicate _ _⟩
  | succ n ih =>
    intro hn
    have hI := ih (by omega)
    have e : List.range' (g.size - (n + 1)) (n + 1) = (g.size - (n + 1)) :: List.range' (g.size - n) n := by
      rw [List.range'_succ]
      congr 2
      omega
    rw [e, List.foldr_cons]
    have hkn : g.size - n = (g.size - (n + 1)) + 1 := by omega
    rw [hkn] at hI ⊢
    exact divInv_step g hg _ (by omega) _ hI

/-- **`divX` solves its recurrence**, its top entry zero. -/
theorem divX_inv (g : Array F) (hg : g.size < 2 ^ 63) : DivInv g 0 (PcsQuotient.divX g) := by
  have h := divInv_fold g hg g.size le_rfl
  rw [Nat.sub_self] at h
  rw [divX_eq]
  exact h

/-- **`M` of `divX g` is `g` but its first entry.** -/
theorem M_divX (g : Array F) (hg : g.size < 2 ^ 63) {j : ℕ} (hj : j < g.size) :
    M (fun i => (PcsQuotient.divX g).getD i 0) j = if j = 0 then 0 else g.getD j 0 := by
  have hI := divX_inv g hg
  unfold M
  split_ifs with h0
  · rfl
  · dsimp only
    have := hI.recur (j - 1) (by omega) (by omega)
    rw [show j - 1 + 1 = j by omega] at this
    rw [show j + PcsQuotient.lowBit j - 1 = j - 1 + PcsQuotient.lowBit j by omega, this, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
    simp [Array.getD, hj]

/-- **The quotient by `x`**: `X · nov 0 k (divX g) = nov 0 k g − g 0`, for `g` of `2^k` entries. -/
theorem X_mul_nov_divX (k : ℕ) (hk : k ≤ 62) (g : Array F) (hg : g.size = 2 ^ k) :
    X * nov 0 k (fun i => (PcsQuotient.divX g).getD i 0) = nov 0 k (fun i => g.getD i 0) - C (g.getD 0 0) := by
  have hg63 : g.size < 2 ^ 63 := by rw [hg]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hI := divX_inv g hg63
  have hmul := mul_nov k hk 0 (fun i => (PcsQuotient.divX g).getD i 0)
  rw [show digitPoly (F := F) 0 = X from rfl] at hmul
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [hmul, hI.top (2 ^ k - 1) (by omega) (by rw [hg]; omega), C_0, zero_mul, add_zero]
  rw [nov_congr 0 k (g := fun j => (if j = 0 then 0 else g.getD j 0)) fun j hj => M_divX g hg63 (by omega)]
  unfold nov
  rw [eq_sub_iff_add_eq]
  have hpos : 0 ∈ range (2 ^ k) := Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_erase_add _ _ hpos, ← Finset.sum_erase_add (range (2 ^ k)) _ hpos]
  simp only [↓reduceIte, C_0, zero_mul, add_zero]
  rw [show basisAt (F := F) 0 k 0 = 1 by simp [basisAt], mul_one]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)]

end Arrays

end E2ECompleteness.Pcs.Novel
