-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this directory's previous `PcsValues.lean` (`novelEval` as a sum) to the deployed protocol's `valuesAt`.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E`.
import E2ECompleteness.PcsHSlots

/-!
# The prover's values at `t`

`valuesAt` sends the three values the gate reads and `next`. For a witness table `wHat` and a wiring table `σ̂` of
`2^24` entries (generic in the number of rows' digits `k`, instantiated at `22`):

* `novelEval_eq_sum`: `novelEval` is the novel-basis sum;
* `novelEval_rows`: the row polynomial `j` of the witness table, `nov 0 k (wHat[j + 4 ·])`, at `w₂(t)`;
* `rowValues_eq_rowVals`: the Statement's `rowValues` is F1's `rowVals` at `θ = β₁`;
* **`valuesAt_fst`**, **`valuesAt_snd`**: the values are F1's `rowValues` of the witness table's first message
  and the wiring polynomial at `t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

namespace E2ECompleteness.Pcs.H

/-! ## `novelEval` -/

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∀ N : ℕ, ∑ i ∈ range (2 * N), g i = ∑ j ∈ range N, (g (2 * j) + g (2 * j + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_two_mul g N, sum_range_succ, add_assoc]

theorem prod_testBit_two_mul_add {M : Type*} [CommMonoid M] (d : M) (ds : ℕ → M) (j : ℕ)
    (b : Bool) (L : ℕ) :
    ∏ k ∈ range (L + 1), (if (2 * j + (if b then 1 else 0)).testBit k then
        (if k = 0 then d else ds (k - 1)) else 1) =
      (if b then d else 1) * ∏ k ∈ range L, (if j.testBit k then ds k else 1) := by
  rw [prod_range_succ']
  have h0 : (2 * j + (if b then 1 else 0)).testBit 0 = b := by
    cases b <;> simp [Nat.testBit_zero, Nat.mul_mod_right]
  have hs : ∀ k, (2 * j + (if b then 1 else 0)).testBit (k + 1) = j.testBit k := by
    intro k
    rw [Nat.testBit_succ]
    congr 1
    cases b <;> simp <;> omega
  simp only [h0, hs, if_true, show ∀ k : ℕ, k + 1 ≠ 0 from fun k ↦ by omega, if_false,
    Nat.add_sub_cancel]
  rw [mul_comm]

def novelStep (cur : Array E) (d : E) : Array E :=
  Array.ofFn (n := cur.size / 2) fun j ↦ cur.getD (2 * j.val) 0 + d * cur.getD (2 * j.val + 1) 0

theorem novelStep_getD (cur : Array E) (d : E) (j : ℕ) (hj : j < cur.size / 2) :
    (novelStep cur d).getD j 0 = cur.getD (2 * j) 0 + d * cur.getD (2 * j + 1) 0 := by
  simp [novelStep, Array.getD_eq_getD_getElem?, hj]

theorem fold_novel : ∀ (ds : List E) (cur : Array E), cur.size = 2 ^ ds.length →
    (ds.foldl novelStep cur).getD 0 0 =
      ∑ i ∈ range (2 ^ ds.length),
        cur.getD i 0 * ∏ k ∈ range ds.length, (if i.testBit k then ds.getD k 0 else 1)
  | [], cur, h => by
    simp only [List.foldl_nil, List.length_nil, pow_zero, range_one, sum_singleton,
      range_zero, prod_empty, mul_one]
  | d :: ds, cur, h => by
    rw [List.foldl_cons, fold_novel ds (novelStep cur d) (by
      simp only [novelStep, Array.size_ofFn, h, List.length_cons, pow_succ]; omega)]
    rw [List.length_cons, pow_succ, mul_comm (2 ^ ds.length) 2, sum_range_two_mul]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' : j < cur.size / 2 := by
      rw [h, List.length_cons, pow_succ]; simp only [mem_range] at hj; omega
    rw [novelStep_getD cur d j hj']
    have e0 := prod_testBit_two_mul_add d (fun k ↦ ds.getD k 0) j false ds.length
    have e1 := prod_testBit_two_mul_add d (fun k ↦ ds.getD k 0) j true ds.length
    simp only [Bool.false_eq_true, if_false, add_zero, if_true] at e0 e1
    have hl : ∀ i : ℕ, ∏ k ∈ range (ds.length + 1),
        (if i.testBit k then (d :: ds).getD k 0 else 1) =
        ∏ k ∈ range (ds.length + 1),
          (if i.testBit k then (if k = 0 then d else ds.getD (k - 1) 0) else 1) := by
      intro i
      refine prod_congr rfl fun k _ ↦ ?_
      rcases k with _ | k <;> simp
    rw [hl, hl, e0, e1]
    ring

/-- **`novelEval` as a sum.** -/
theorem novelEval_eq_sum (coeffs : Array K) (first step : ℕ) (ds : List E) :
    novelEval coeffs first step ds =
      ∑ i ∈ range (2 ^ ds.length), ofK (coeffs.getD (first + step * i) 0) *
        ∏ k ∈ range ds.length, (if i.testBit k then ds.getD k 0 else 1) := by
  unfold novelEval
  have h := fold_novel ds (Array.ofFn (n := 2 ^ ds.length) fun j ↦
    ofK (coeffs.getD (first + step * j.val) 0)) (by simp)
  refine (Eq.trans ?_ h).trans (sum_congr rfl fun i hi ↦ ?_)
  · rfl
  · simp [Array.getD_eq_getD_getElem?, mem_range.mp hi]

/-- The novel-basis polynomial at `x`, as a sum. -/
theorem nov_eval (m : ℕ) (f : ℕ → E) (x : E) :
    (Novel.nov 0 m f).eval x = ∑ i ∈ range (2 ^ m), f i * ∏ k ∈ range m, (if i.testBit k then sq^[k] x else 1) := by
  unfold Novel.nov Novel.basisAt
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_mul, eval_C, eval_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs
  · rw [zero_add, digitPoly_eval]
  · exact eval_one

/-- **`novelEval` on digits `w_s(t) … w_{s+m-1}(t)`** is the novel-basis polynomial at `w_s(t)`. -/
theorem novelEval_digits (coeffs : Array K) (first step s m : ℕ) (t : E) (ds : List E) (hl : ds.length = m)
    (hd : ∀ k < m, ds.getD k 0 = sq^[s + k] t) :
    novelEval coeffs first step ds =
      (Novel.nov 0 m (fun i => ofK (coeffs.getD (first + step * i) 0))).eval (sq^[s] t) := by
  rw [novelEval_eq_sum, nov_eval, hl]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [hd k (Finset.mem_range.mp hk), ← Function.iterate_add_apply, add_comm]

/-! ## The rows -/

theorem digitsOf_eq' (t : E) (count : ℕ) :
    digitsOf t count = (List.range (count + 1)).map fun k ↦ sq^[k] t :=
  PcsBridge.Kc3.digitsOf_eq t count

theorem idx_cons_cons {k : ℕ} (x y : Bool) (b : Fin k → Bool) :
    Completeness.idx (Fin.cons x (Fin.cons y b) : Fin (k + 1 + 1) → Bool) =
      ((if x then 1 else 0) + 2 * (if y then 1 else 0)) + 4 * Completeness.idx b := by
  rw [Completeness.idx_cons, Completeness.idx_cons]
  ring

/-- The witness table's role `j` first message is the table of `wHat[j + 4 ·]`. -/
theorem witnessOfTable_nov {k : ℕ} (wHat : Array K) (j : Fin 4) :
    witnessOfTable (k := k) (fun b => ofK (wHat.getD (Completeness.idx b) 0)) j =
      Novel.nov 0 k (fun i => ofK (wHat.getD (j + 4 * i) 0)) := by
  rw [← tablePoly_idx k]
  fin_cases j
  · exact congrArg tablePoly (funext fun b => by beta_reduce; rw [idx_cons_cons]; rfl)
  · exact congrArg tablePoly (funext fun b => by beta_reduce; rw [idx_cons_cons]; rfl)
  · exact congrArg tablePoly (funext fun b => by beta_reduce; rw [idx_cons_cons]; rfl)
  · exact congrArg tablePoly (funext fun b => by beta_reduce; rw [idx_cons_cons]; rfl)

/-- **The Statement's `rowValues` is F1's `rowVals`** at `θ = β₁`, `ω = w₁(t)`. -/
theorem rowValues_eq_rowVals (a : Vector E 4) (t : E) :
    rowValues a t (QuotientSecurity.sq t) = Vector.ofFn (_root_.Kc3.rowVals (ofK (betaAt 1)) t (fun j => a[j])) := by
  have hθ : ofK (betaAt 1) * ofK (betaAt 1) + ofK (betaAt 1) + 1 = (0 : E) := cantor_theta BE (by norm_num)
  apply Vector.ext
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi' with rfl | rfl | rfl
  · simp only [rowValues, Vector.getElem_ofFn, _root_.Kc3.rowVals, QuotientSecurity.sq]
    simp
    ring
  · simp only [rowValues, Vector.getElem_ofFn, _root_.Kc3.rowVals, QuotientSecurity.sq]
    simp
    ring
  · simp only [rowValues, Vector.getElem_ofFn, _root_.Kc3.rowVals, QuotientSecurity.sq]
    simp
    linear_combination (norm := char2_norm) (0 : E)

variable (cir : Circuit) (cells₀ : Array K) (coins : Coins)

theorem valuesAt_snd (hl : cir.logRows = 22) (t : E) :
    (valuesAt cir cells₀ coins t).2 = (Sp cir).eval t := by
  have hm : cellVars cir.logRows = 24 := by rw [hl]; rfl
  unfold valuesAt
  dsimp only
  rw [hm, novelEval_digits cir.wiringTable 0 1 0 24 t _ (by simp [digitsOf_eq'])
    (fun k hk => by
      rw [digitsOf_eq', List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hk, List.getElem?_map,
        List.getElem?_range (by omega), zero_add]
      rfl), Sp]
  rw [Novel.nov_congr 0 24 (g := fun i => ofK (cir.wiringTable.getD i 0)) fun i _ => by rw [zero_add, one_mul]]
  rfl

theorem valuesAt_fst (hl : cir.logRows = 22) (t : E) :
    (valuesAt cir cells₀ coins t).1 = Vector.ofFn (_root_.Kc3.rowVals (ofK (betaAt 1)) t
      (fun j => (Novel.nov 0 22 (fun i => ofK ((witnessParts cir cells₀ coins).2.getD (j + 4 * i) 0))).eval
        (sq^[2] t))) := by
  have hm : cellVars cir.logRows = 24 := by rw [hl]; rfl
  unfold valuesAt witnessTable
  dsimp only
  have h1 : (digitsOf t 24).getD 1 0 = QuotientSecurity.sq t := by
    rw [digitsOf_eq', List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  rw [hm, h1, rowValues_eq_rowVals]
  refine congrArg (fun a => Vector.ofFn (_root_.Kc3.rowVals (ofK (betaAt 1)) t a)) (funext fun j => ?_)
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  refine novelEval_digits _ _ _ 2 22 t _ (by simp [digitsOf_eq']) fun k hk => ?_
  rw [digitsOf_eq', List.getD_eq_getElem?_getD, List.getElem?_take, if_pos (by omega), List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (by omega)]
  rfl

end E2ECompleteness.Pcs.H
