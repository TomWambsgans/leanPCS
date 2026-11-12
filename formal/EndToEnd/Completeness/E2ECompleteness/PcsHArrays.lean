-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the prover's arrays (`PcsHDefs.lean`) on the coset and on the cells, as polynomials over `E`.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E`.
import E2ECompleteness.PcsHCoset

/-!
# The prover's arrays as polynomials

For a circuit of `2^22` rows (`hl`; the circuit is taken apart, so that nothing of a concrete circuit is
evaluated), at the coset point `xc i`, `i < 2^26`:

* `wValues_getD`: the witness values are `Wp`, the witness table's polynomial (`24` digits);
* `sigmaValues_getD`: the wiring values are `Sp`, the wiring table's polynomial;
* `hValues_getD`: the sum's values are `Hp + w₂₄ (b₀ + b₁ X)`, `Hp` the polynomial of `hHat`;
* `hArr_getD`, `Hp_eval_point`: the sum on the cells, and `Hp` at `B(i)` is it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

namespace E2ECompleteness.Pcs.H

variable (cir : Circuit) (cells₀ : Array K) (coins : Coins) (α β : E)

/-- The witness table's polynomial. -/
noncomputable def Wp : E[X] := Novel.nov 0 24 fun j => ofK ((witnessParts cir cells₀ coins).2.getD j 0)

/-- The wiring table's polynomial. -/
noncomputable def Sp : E[X] := Novel.nov 0 24 fun j => ofK (cir.wiringTable.getD j 0)

/-- `h`'s polynomial. -/
noncomputable def Hp : E[X] := Novel.nov 0 24 fun j => (hHatOf cir cells₀ coins α β).getD j 0

/-- The blinding `b₀ + b₁ X`. -/
noncomputable def blindPoly : E[X] := C (blindAt coins 0) + C (blindAt coins 1) * X

theorem blindAt_ge (i : ℕ) (hi : 2 ≤ i) : blindAt coins i = 0 := by
  unfold blindAt
  rw [dif_neg (by simp only [freeBlind, hBlind]; omega)]

/-- The coset's offset and transform, for a circuit of `2^22` rows. -/
theorem nov_coset {F : ℕ → E} {G : ℕ → E} (hFG : ∀ j < 2 ^ 26, F j = G j) (hG : ∀ j, 2 ^ 24 ≤ j → G j = 0)
    (x : E) : (Novel.nov 0 26 F).eval x = (Novel.nov 0 24 G).eval x := by
  rw [Novel.nov_congr 0 26 hFG]
  exact congrArg (fun p : E[X] => p.eval x) (nov_extend 24 G hG 2)

theorem getD_ge {A : Type} [Inhabited A] (a : Array A) (d : A) {j : ℕ} (h : a.size ≤ j) : a.getD j d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

theorem wValues_getD (hl : cir.logRows = 22) (hw : (witnessParts cir cells₀ coins).2.size = 2 ^ 24) {i : ℕ}
    (hi : i < 2 ^ 26) : ofK ((wValuesOf cir cells₀ coins).getD i 0) = (Wp cir cells₀ coins).eval (xc i) := by
  obtain ⟨l, u, rows, inputs, sigma, packing⟩ := cir
  simp only at hl
  subst hl
  have h := values_getD_nov_K (m := 26) (by norm_num) (betaAt 26)
    (Array.ofFn (n := 4 * 2 ^ 24) fun i =>
      (witnessParts ⟨22, u, rows, inputs, sigma, packing⟩ cells₀ coins).2.getD i.val 0) (by simp) hi
  refine h.trans (nov_coset (fun j hj => ?_) (fun j hj => ?_) _)
  · rw [getD_ofFn _ (by omega)]
  · rw [getD_ge _ _ (by omega), Compose.Reduce.ofK_zero]

theorem sigmaValues_getD (hl : cir.logRows = 22) (hs : cir.wiringTable.size = 2 ^ 24) {i : ℕ} (hi : i < 2 ^ 26) :
    ofK ((sigmaValuesOf cir).getD i 0) = (Sp cir).eval (xc i) := by
  obtain ⟨l, u, rows, inputs, sigma, packing⟩ := cir
  simp only at hl
  subst hl
  have h := values_getD_nov_K (m := 26) (by norm_num) (betaAt 26)
    (Array.ofFn (n := 4 * 2 ^ 24) fun i =>
      (Circuit.wiringTable ⟨22, u, rows, inputs, sigma, packing⟩).getD i.val 0) (by simp) hi
  refine h.trans (nov_coset (fun j hj => ?_) (fun j hj => ?_) _)
  · rw [getD_ofFn _ (by omega)]
  · rw [getD_ge _ _ (by omega), Compose.Reduce.ofK_zero]

theorem nov_blind : Novel.nov 0 24 (fun j => blindAt coins j) = blindPoly coins := by
  have e := nov_extend 1 (fun j => blindAt coins j) (fun j hj => blindAt_ge coins j (by simpa using hj)) 23
  rw [show (1 + 23 : ℕ) = 24 from rfl] at e
  rw [e, show (1 : ℕ) = 0 + 1 from rfl, Novel.nov_split, Novel.nov_zero, Novel.nov_zero, blindPoly]
  simp only [pow_zero, zero_add, digitPoly]
  ring

/-- The sum's coset polynomial, from any table holding `h`'s coefficients then the blinding. -/
theorem nov_hValues (m : ℕ) (hm : 1 ≤ m) (hh : Array E) (F : ℕ → E)
    (hF : ∀ j < 2 ^ (m + 1 + 1), F j = if j < 2 ^ m then hh.getD j 0 else blindAt coins (j - 2 ^ m)) :
    Novel.nov 0 (m + 1 + 1) F = Novel.nov 0 m (fun j => hh.getD j 0) + digitPoly m * blindPoly coins := by
  have p1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have p2 : 2 ^ (m + 1 + 1) = 4 * 2 ^ m := by rw [pow_succ, pow_succ]; ring
  have p0 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hz : (Novel.nov 0 (m + 1) fun j => F (2 ^ (m + 1) + j)) = 0 := by
    have hz' : ∀ j < 2 ^ (m + 1), F (2 ^ (m + 1) + j) = (fun _ => (0 : E)) j := fun j hj => by
      rw [hF _ (by omega), if_neg (by omega), blindAt_ge coins _ (by omega)]
    rw [Novel.nov_congr 0 (m + 1) hz', nov_zero_fun]
  have h1 : ∀ j < 2 ^ m, F j = hh.getD j 0 := fun j hj => by rw [hF _ (by omega), if_pos hj]
  have h2 : ∀ j < 2 ^ m, F (2 ^ m + j) = blindAt coins j := fun j hj => by
    rw [hF _ (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
  have hb := nov_extend 1 (fun j => blindAt coins j) (fun j hj => blindAt_ge coins j (by simpa using hj)) (m - 1)
  rw [show 1 + (m - 1) = m by omega] at hb
  rw [Novel.nov_split, hz, mul_zero, add_zero, Novel.nov_split, Novel.nov_congr 0 m h1,
    Novel.nov_congr 0 m (f := fun j => F (2 ^ m + j)) h2, hb, show (1 : ℕ) = 0 + 1 from rfl, Novel.nov_split,
    Novel.nov_zero, Novel.nov_zero, blindPoly]
  simp only [pow_zero, digitPoly]
  ring

theorem hValues_generic (k : ℕ) (hk : k = 24) (offset : K) (hh : Array E) {i : ℕ} (hi : i < 2 ^ (k + 2)) :
    (values (k + 2) offset (Array.ofFn (n := 4 * 2 ^ k) fun i =>
        if i.val < 2 ^ k then hh.getD i.val 0 else blindAt coins (i.val - 2 ^ k))).getD i 0 =
      (Novel.nov 0 k (fun j => hh.getD j 0) + digitPoly k * blindPoly coins).eval (ofK (offset + point i)) := by
  have hsz : (Array.ofFn (n := 4 * 2 ^ k) fun i =>
      if i.val < 2 ^ k then hh.getD i.val 0 else blindAt coins (i.val - 2 ^ k)).size = 2 ^ (k + 2) := by
    rw [Array.size_ofFn, pow_add]; ring
  rw [values_getD_nov (m := k + 2) (by omega) _ _ hsz hi]
  refine congrArg (fun p : E[X] => p.eval _) (nov_hValues coins k (by omega) _ _ fun j hj => ?_)
  exact getD_ofFn _ (by rw [pow_add] at hj; omega) _

theorem hValues_getD (hl : cir.logRows = 22) {i : ℕ} (hi : i < 2 ^ 26) :
    (hValuesOf cir cells₀ coins α β).getD i 0 =
      (Hp cir cells₀ coins α β + digitPoly 24 * blindPoly coins).eval (xc i) := by
  have hm : cellVars cir.logRows = 24 := by rw [hl]; rfl
  have h := hValues_generic coins (cellVars cir.logRows) hm (betaAt (cellVars cir.logRows + 2))
    (hHatOf cir cells₀ coins α β) (i := i) (by rw [hm]; exact hi)
  unfold hValuesOf offsetOf
  refine h.trans ?_
  rw [hm, Hp, xc, show (24 + 2 : ℕ) = 26 from rfl]

/-- The sum on the cells. -/
theorem hArr_getD (hl : cir.logRows = 22) {i : ℕ} (hi : i < 2 ^ 24) :
    (hArr cir cells₀ coins α β).getD i 0 =
      (α + ofK ((witnessParts cir cells₀ coins).1.getD i 0) + β * ofK (point i))⁻¹ +
        (α + ofK ((witnessParts cir cells₀ coins).1.getD i 0) + β * ofK (point (cir.sigma.getD i 0)))⁻¹ := by
  obtain ⟨l, u, rows, inputs, sigma, packing⟩ := cir
  simp only at hl
  subst hl
  exact getD_ofFn _ hi _

theorem hArr_size (hl : cir.logRows = 22) : (hArr cir cells₀ coins α β).size = 2 ^ 24 := by
  obtain ⟨l, u, rows, inputs, sigma, packing⟩ := cir
  simp only at hl
  subst hl
  simp [hArr, cellVars]

/-- **`Hp` at a cell is the sum there.** -/
theorem Hp_eval_point (hl : cir.logRows = 22) {i : ℕ} (hi : i < 2 ^ 24) :
    (Hp cir cells₀ coins α β).eval (ofK (point i)) = (hArr cir cells₀ coins α β).getD i 0 := by
  have hs := hArr_size cir cells₀ coins α β hl
  obtain ⟨l, u, rows, inputs, sigma, packing⟩ := cir
  simp only at hl
  subst hl
  have h := nov_coefficients (m := 24) (by norm_num) 0 _ hs hi
  rw [zero_add] at h
  exact h

end E2ECompleteness.Pcs.H
