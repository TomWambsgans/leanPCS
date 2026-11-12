-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the prover's arrays on the coset (`PcsHDefs.lean`) as polynomials over `E`.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E`.
import E2ECompleteness.PcsHDefs
import E2ECompleteness.PcsHInstance

/-!
# The prover's arrays as polynomials

For any circuit of `2^22` rows (`hl`), at the coset point `x_i = β₂₆ + B(i)`, `i < 2^26` (`xc i`):

* `wValues_getD`, `sigmaValues_getD`: the witness and wiring values are their tables' polynomials (`Wp`, `Sp`);
* `hValues_getD`: the sum's values are `H + w₂₄ (b₀ + b₁ X)`, `H` the polynomial of `hHat`; `H_eval_point`: `H` at
  `B(i)` is the sum at cell `i`;
* `rowPolyOf_ofK`, `zPinsOf_ofK`, `pinTerm_ofK`, `chain_ofK`: the rows', the pins' and the cells' vanishing
  polynomials and the pins' term;
* `point_xor_low`: `B(i ⊕ c) = B(i) + B(c)`; `zc_ne_zero`: `w₂₄` does not vanish on the coset.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

namespace E2ECompleteness.Pcs.H

/-! ## Generic helpers -/

theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) {i : ℕ} (h : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp [h]

theorem nov_zero_fun {F : Type} [Field F] [CharP F 2] (k : ℕ) : Novel.nov (F := F) 0 k (fun _ => 0) = 0 := by
  simp [Novel.nov]

/-- A table zero from `2^k` on is the same on more digits. -/
theorem nov_extend {F : Type} [Field F] [CharP F 2] (k : ℕ) (f : ℕ → F) (hf : ∀ j, 2 ^ k ≤ j → f j = 0) :
    ∀ l, Novel.nov 0 (k + l) f = Novel.nov 0 k f
  | 0 => rfl
  | l + 1 => by
    rw [← add_assoc, Novel.nov_split, nov_extend k f hf l,
      Novel.nov_congr 0 (k + l) (g := fun _ => 0) fun j _ => hf _ (by
        have := Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.le_add_right k l); omega),
      nov_zero_fun, mul_zero, add_zero]

/-! ## The coset -/

/-- The coset point `x_i = β₂₆ + B(i)`, in `E`. -/
noncomputable def xc (i : ℕ) : E := ofK (betaAt 26 + point i)

theorem point_xor_low (a b : ℕ) : point (a ^^^ b) = point a + point b := by
  rw [Bridge.Ntt.point_eq_sum, Bridge.Ntt.point_eq_sum, Bridge.Ntt.point_eq_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit t <;> cases b.testBit t <;> simp [CharTwo.add_self_eq_zero]

theorem point_zero : point 0 = 0 := by
  rw [Bridge.Ntt.point_eq_sum]
  simp

theorem point_one : point 1 = 1 := by
  rw [point_eq_sum (m := 1) (by norm_num) (by norm_num)]
  simp [(cantorUpTo (m := 28) le_rfl).1]

theorem point_two : point 2 = betaAt 1 := by
  rw [point_eq_sum (m := 2) (by norm_num) (by norm_num)]
  have h0 : Nat.testBit 2 0 = false := by decide
  have h1 : Nat.testBit 2 1 = true := by decide
  simp [Finset.sum_range_succ, h0, h1]

theorem point_three : point 3 = 1 + betaAt 1 := by
  rw [point_eq_sum (m := 2) (by norm_num) (by norm_num)]
  have h0 : Nat.testBit 3 0 = true := by decide
  have h1 : Nat.testBit 3 1 = true := by decide
  simp [Finset.sum_range_succ, h0, h1, (cantorUpTo (m := 28) le_rfl).1]

/-- **`w₂₄` does not vanish on the coset**: `w₂₄(x_i) = β₂ + B(i / 2^24)`, which `w₂` sends to `1`. -/
theorem zc_ne_zero {i : ℕ} (hi : i < 2 ^ 26) : sq^[24] (xc i) ≠ 0 := by
  have hB := cantorUpTo (m := 28) le_rfl
  rw [xc, ← ofK_S_iterate]
  intro h0
  have h1 : S^[24] (betaAt 26 + point i) = betaAt 2 + point (i / 2 ^ 24) := by
    rw [show S^[24] (betaAt 26 + point i) = S^[24] (betaAt 26) + S^[24] (point i) by
      rw [Bridge.Ntt.S_eq_sq]; exact sq_iterate_add 24 _ _]
    rw [Bridge.Ntt.iterate_betaAt hB (by norm_num), if_pos (by norm_num),
      Bridge.Ntt.iterate_point (cantorUpTo (m := 26) (by norm_num)) (by unfold basisSize; norm_num) hi (by norm_num)]
  have h2 : S^[2] (betaAt 2 + point (i / 2 ^ 24)) = 1 := by
    rw [show S^[2] (betaAt 2 + point (i / 2 ^ 24)) = S^[2] (betaAt 2) + S^[2] (point (i / 2 ^ 24)) by
      rw [Bridge.Ntt.S_eq_sq]; exact sq_iterate_add 2 _ _]
    rw [Bridge.Ntt.iterate_betaAt hB (by norm_num), if_pos (by norm_num),
      Bridge.Ntt.iterate_point (cantorUpTo (m := 2) (by norm_num)) (by unfold basisSize; norm_num)
        (show i / 2 ^ 24 < 2 ^ 2 by omega) (by norm_num), hB.1]
    have : i / 2 ^ 24 / 2 ^ 2 = 0 := by omega
    rw [this, point_zero, add_zero]
  have h3 : ofK (S^[2] (S^[24] (betaAt 26 + point i))) = 0 := by
    rw [ofK_S_iterate, h0]; exact sq_iterate_zero 2
  rw [h1, h2, Compose.Reduce.ofK_one] at h3
  exact one_ne_zero h3

/-! ## The rows', pins' and cells' polynomials on `K` -/

theorem chain_ofK (x : K) : ofK ((chain x (24 + 1)).getD 24 0) = sq^[24] (ofK x) := by
  rw [Bridge.Ntt.chain_getD _ (by norm_num), ofK_S_iterate]

theorem rowPolyAt_ofK (x : K) : ofK (rowPolyAt 24 x) = PcsBridge.Kc3.rowsAt (ofK x) := by
  rw [rowPolyAt_eq_sum', ofK_sum, PcsBridge.Kc3.rowsAt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Compose.Reduce.ofK_mul, ofK_S_iterate]

theorem zPinsOf_ofK (x : K) : ofK (zPinsOf x) = ∏ k ∈ range 11, (ofK x + PcsBridge.Kc3.pinE k) := by
  unfold zPinsOf pinPoints
  rw [List.foldl_map, PcsBridge.Kc3.foldl_mul_range, one_mul, ofK_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Compose.Reduce.ofK_add]
  rfl

theorem pinPolyOf_ofK (stmt : Statement) (x : K) :
    ofK (pinPolyOf stmt x) = ∑ k ∈ range 11, ofK (pinWeights.getD k 0 * anchorValues stmt.words k) *
      ∏ j ∈ (range 11).erase k, (ofK x + PcsBridge.Kc3.pinE j) := by
  unfold pinPolyOf
  rw [show publicRows = 11 from rfl, PcsBridge.Kc3.foldl_add_range, zero_add, ofK_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Compose.Reduce.ofK_mul]
  congr 1
  rw [PcsBridge.Kc3.foldl_congr_mem _ (fun acc j => acc * (if j = k then 1 else x + pinPoints.getD j 0)) _
      (fun j _ acc => by split_ifs <;> simp), PcsBridge.Kc3.foldl_mul_range, one_mul, ofK_prod,
    ← Finset.prod_erase_mul _ _ hk, if_pos rfl, Compose.Reduce.ofK_one, mul_one]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [if_neg (Finset.ne_of_mem_erase hj), Compose.Reduce.ofK_add,
    PcsBridge.Kc3.pinPoints_getD (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))]
  rfl

/-- **The pins' term on `K`** is the barycentric `(x + v) / Z_P`. -/
theorem pinTerm_ofK (stmt : Statement) (x w : K) (hx : ∀ k < 11, ofK x + PcsBridge.Kc3.pinE k ≠ 0) :
    ofK ((w + pinPolyOf stmt x) * (zPinsOf x)⁻¹) = PcsBridge.Kc3.pinnedV stmt (ofK x) (ofK w) := by
  have hZ : ∏ k ∈ range 11, (ofK x + PcsBridge.Kc3.pinE k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k hk => hx k (Finset.mem_range.mp hk)
  rw [Compose.Reduce.ofK_mul, PcsBridge.Kc3.ofK_inv, zPinsOf_ofK, Compose.Reduce.ofK_add, pinPolyOf_ofK]
  unfold PcsBridge.Kc3.pinnedV
  rw [Finset.prod_inv_distrib, add_mul, Finset.sum_mul, add_right_inj]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hne : ∏ j ∈ (range 11).erase k, (ofK x + PcsBridge.Kc3.pinE j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => hx j (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))
  have hk' : ofK x + PcsBridge.Kc3.pinE k ≠ 0 := hx k (Finset.mem_range.mp hk)
  rw [← Finset.prod_erase_mul _ _ hk]
  field_simp

end E2ECompleteness.Pcs.H
