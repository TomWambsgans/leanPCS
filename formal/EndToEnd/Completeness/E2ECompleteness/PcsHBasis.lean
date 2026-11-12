-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this directory's previous `PcsConstants.lean` (the constants' kernel checks) to the deployed
-- protocol; new here: the bridges from the Statement's transforms to `PcsNovel.lean`'s polynomials over `E`.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E`.
import E2ECompleteness.PcsNovelDiv
import E2ECompleteness.PcsNtt
import QuotientSecurity.DeployedBasis
import Bridge.Claims.Tau
import Compose.Reduce

/-!
# The Statement's constants and transforms, as polynomials over `E`

* `isCantorBasis` (kernel), `BE`: `beta()` is a Cantor basis, read in `E`;
* `rowPolyAt_beta`, `rowVanishing_last`: `row_vanishing(24)` vanishes at `β₂ … β₂₃` and ends in `1` (kernel, from
  its words);
* `ofK_point`: `B(p)` in `E` is `BE`'s point of `p`'s bits;
* **`values_getD_nov`**, **`nov_coefficients`**: entry `p` of `values m offset c` is `nov 0 m c` at
  `offset + B(p)`, and `coefficients` interpolates (entries in `K` read in `E`, or in `E`).
-/

set_option autoImplicit false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

namespace E2ECompleteness.Pcs.H

theorem ofK_sum {ι : Type*} (s : Finset ι) (f : ι → K) : ofK (∑ i ∈ s, f i) = ∑ i ∈ s, ofK (f i) :=
  map_sum (algebraMap K E) f s

theorem ofK_prod {ι : Type*} (s : Finset ι) (f : ι → K) : ofK (∏ i ∈ s, f i) = ∏ i ∈ s, ofK (f i) :=
  map_prod (algebraMap K E) f s

/-! ## The basis -/

/-- **`beta()` is a Cantor basis** (its `28` vectors), by kernel evaluation. -/
theorem isCantorBasis : IsCantorBasis := by decide +kernel

theorem cantorUpTo {m : ℕ} (hm : m ≤ 28) : Bridge.Ntt.CantorUpTo m :=
  E2ECompleteness.Pcs.Ntt.cantorUpTo_of_isCantorBasis isCantorBasis (by unfold basisSize; omega)

theorem ofK_S_iterate (k : ℕ) (x : K) : ofK (S^[k] x) = sq^[k] (ofK x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    rw [Bridge.Ntt.S_eq_sq]
    simp only [QuotientSecurity.sq, Compose.Reduce.ofK_add, Compose.Reduce.ofK_mul]

/-- **The statement's basis in `E`.** -/
noncomputable def BE : CantorBasis E 28 where
  β k := ofK (betaAt k)
  zero := by rw [(cantorUpTo le_rfl).1]; exact Compose.Reduce.ofK_one
  succ k hk := by
    rw [← (cantorUpTo le_rfl).2 k hk]
    have := ofK_S_iterate 1 (betaAt (k + 1))
    simpa using this.symm

theorem BE_β (k : ℕ) : BE.β k = ofK (betaAt k) := rfl

theorem ofK_point {m : ℕ} (hm : m ≤ 28) {p : ℕ} (hp : p < 2 ^ m) :
    ofK (point p) = (BE.point (Completeness.bitsOf m p) : E) := by
  rw [E2ECompleteness.Pcs.Ntt.point_eq_cantor (cantorUpTo hm) (by unfold basisSize; omega) hp,
    CantorBasis.point, CantorBasis.point, ofK_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · exact Compose.Reduce.ofK_zero

/-- `B(p)` is additive in the bits: `B(p) = Σ_{bit t of p} β_t`. -/
theorem point_eq_sum {m : ℕ} (hm : m ≤ 28) {p : ℕ} (hp : p < 2 ^ m) :
    point p = ∑ t ∈ range m, if p.testBit t then betaAt t else 0 :=
  Bridge.Ntt.point_eq_sum_of_lt (by unfold basisSize; omega) hp

/-! ## The rows' polynomial (`row_vanishing(24)`) -/

theorem getD_of_words {l : List K} {ws : List UInt64} (h : l.map K.lane = ws) (i : ℕ) :
    l.getD i 0 = K.ofLane (ws.getD i 0) := by
  subst h
  by_cases hi : i < l.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none]
    rfl

theorem beta_lanes : PcsQuotient.Domain.beta.toList.map K.lane =
    betaWords ++ [0xf89578714bd28f96, 0x564dda59237a3352, 0xad33bc6cc75aed38, 0x57a3104fcd0e5f34] := by
  decide +kernel

theorem betaAt_eq_getD (k : ℕ) : betaAt k = PcsQuotient.Domain.beta.toList.getD k 0 := by
  simp [betaAt, List.getD_eq_getElem?_getD]

theorem betaAt_eq_betaF64 (k : ℕ) (hk : k < 22 + 2) : betaAt k = betaF64 k := by
  rw [betaAt_eq_getD, getD_of_words beta_lanes,
    List.getD_append _ _ _ _ (show k < betaWords.length by rw [show betaWords.length = 24 from rfl]; omega)]
  rfl

/-- `row_vanishing(24)`'s words. -/
def tauWords : List UInt64 :=
  [5246327309480240592, 462416703093199623, 5836061695391999385, 17933131952861334950,
    18372946041939442404, 12828942987611060278, 13588355210333287157, 1205146552516504875,
    981042065287506825, 5923339044450209179, 951408172292342183, 12676167449202766892,
    13719231351162120800, 12661900118541078806, 12449589984762772511, 11682037014426230835,
    1012368888076811759, 18272804218237563919, 5328687504910262779, 18383142605220007825,
    802269026382174146, 1506959928840120550, 1]

theorem rowVanishing_24_words : (rowVanishing 24).map K.lane = tauWords :=
  Bridge.Claims.rowVanishing_24_lanes

theorem sum_range_eq_list (f : ℕ → K) :
    ∀ n, ∑ k ∈ Finset.range n, f k = ((List.range n).map f).sum
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_eq_list f n, List.range_succ, List.map_append,
      List.sum_append]
    simp

theorem tau_system : ∀ j < 22 + 2, 2 ≤ j →
    ((List.range (22 + 1)).map fun k ↦
      (if k ≤ j then betaF64 (j - k) else 0) * K.ofLane (tauWords.getD k 0)).sum = 0 := by
  decide +kernel

theorem length_rowVanishing (m : ℕ) : (rowVanishing m).length = m - 2 + 1 := by
  simp [rowVanishing]

/-- `rowPolyAt` as a sum. -/
theorem rowPolyAt_eq_sum (x : K) :
    rowPolyAt (22 + 2) x = ∑ k ∈ range (22 + 1), (rowVanishing (22 + 2)).getD k 0 *
      (chain x (22 + 2 - 1)).getD k 0 := by
  unfold rowPolyAt
  have hl1 : (chain x (22 + 2 - 1)).length = 22 + 1 := by
    rw [chain, Bridge.Ntt.chain_foldl]
    simp
  have hl2 : (rowVanishing (22 + 2)).length = 22 + 1 := length_rowVanishing _
  generalize hc : chain x (22 + 2 - 1) = ws at hl1 ⊢
  generalize hr : rowVanishing (22 + 2) = ts at hl2 ⊢
  have key : ∀ (ws ts : List K) (n : ℕ), ws.length = n → ts.length = n → ∀ a : K,
      (ws.zip ts).foldl (fun acc (p : K × K) ↦ acc + p.2 * p.1) a =
        a + ∑ k ∈ range n, ts.getD k 0 * ws.getD k 0 := by
    intro ws
    induction ws with
    | nil => intro ts n h1 _ a; subst h1; simp
    | cons w ws ih =>
      intro ts n h1 h2 a
      rcases ts with _ | ⟨t, ts⟩
      · simp at h1 h2; omega
      · rcases n with _ | n
        · simp at h1
        simp only [List.zip_cons_cons, List.foldl_cons]
        rw [ih ts n (by simpa using h1) (by simpa using h2), sum_range_succ', add_assoc]
        simp [add_comm]
  rw [key ws ts (22 + 1) hl1 hl2 0, zero_add]

/-- The rows' polynomial at `x` with `S^k`. -/
theorem rowPolyAt_eq_sum' (x : K) :
    rowPolyAt 24 x = ∑ k ∈ range 23, (rowVanishing 24).getD k 0 * S^[k] x := by
  rw [show (24 : ℕ) = 22 + 2 from rfl, rowPolyAt_eq_sum]
  exact Finset.sum_congr rfl fun k hk => by
    rw [Bridge.Ntt.chain_getD _ (by simp at hk; omega)]

/-- **`row_vanishing(24)` vanishes at `β₂ … β₂₃`.** -/
theorem rowPolyAt_beta {j : ℕ} (hj2 : 2 ≤ j) (hj : j < 24) : rowPolyAt 24 (betaAt j) = 0 := by
  have hB := cantorUpTo (m := 28) le_rfl
  rw [rowPolyAt_eq_sum', sum_range_eq_list]
  refine Eq.trans (congrArg List.sum (List.map_congr_left fun k hk ↦ ?_)) (tau_system j hj hj2)
  rw [getD_of_words rowVanishing_24_words, Bridge.Ntt.iterate_betaAt hB (by omega), mul_comm]
  by_cases hkj : k ≤ j
  · rw [if_pos hkj, if_pos hkj, betaAt_eq_betaF64 _ (by omega)]
  · rw [if_neg hkj, if_neg hkj]

/-- **`row_vanishing(24)` ends in `1`.** -/
theorem rowVanishing_last : (rowVanishing 24).getD 22 0 = 1 := by
  rw [getD_of_words rowVanishing_24_words]
  rfl

/-! ## The transforms -/

theorem ofK_X (m j : ℕ) (x : K) :
    ofK (Bridge.Ntt.X m j x) = ∏ i ∈ range m, if j.testBit i then sq^[i] (ofK x) else 1 := by
  rw [Bridge.Ntt.X, ofK_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · exact ofK_S_iterate i x
  · exact Compose.Reduce.ofK_one

theorem nov_eval_ofK (m : ℕ) (f : ℕ → E) (x : K) :
    (Novel.nov 0 m f).eval (ofK x) = ∑ j ∈ range (2 ^ m), ofK (Bridge.Ntt.X m j x) * f j := by
  unfold Novel.nov Novel.basisAt
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, eval_C, eval_prod, ofK_X, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · rw [zero_add, digitPoly_eval]
  · exact eval_one

/-- **`values` over `E`**: entry `p` is the novel-basis polynomial at `offset + B(p)`. -/
theorem values_getD_nov {m : ℕ} (hm : m ≤ 28) (offset : K) (c : Array E) (hc : c.size = 2 ^ m) {p : ℕ}
    (hp : p < 2 ^ m) :
    (values m offset c).getD p 0 = (Novel.nov 0 m fun j => c.getD j 0).eval (ofK (offset + point p)) := by
  rw [Bridge.Ntt.values_getD_E (cantorUpTo hm) (by unfold basisSize; omega) offset c hc hp, nov_eval_ofK]

/-- **`values` over `K`**, read in `E`. -/
theorem values_getD_nov_K {m : ℕ} (hm : m ≤ 28) (offset : K) (c : Array K) (hc : c.size = 2 ^ m) {p : ℕ}
    (hp : p < 2 ^ m) :
    ofK ((values m offset c).getD p 0) =
      (Novel.nov 0 m fun j => ofK (c.getD j 0)).eval (ofK (offset + point p)) := by
  rw [Bridge.Ntt.values_getD_K (cantorUpTo hm) (by unfold basisSize; omega) offset c hc hp, nov_eval_ofK,
    ofK_sum]
  exact Finset.sum_congr rfl fun j _ => Compose.Reduce.ofK_mul _ _

/-- **`coefficients` over `E` interpolates.** -/
theorem nov_coefficients {m : ℕ} (hm : m ≤ 28) (offset : K) (v : Array E) (hv : v.size = 2 ^ m) {p : ℕ}
    (hp : p < 2 ^ m) :
    (Novel.nov 0 m fun j => (coefficients m offset v).getD j 0).eval (ofK (offset + point p)) = v.getD p 0 := by
  rw [← values_getD_nov hm offset _ (by rw [Bridge.Ntt.coefficients_size, hv]) hp,
    Bridge.Ntt.values_coefficients_E m offset v hv]

/-- **`coefficients` over `K` interpolates**, read in `E`. -/
theorem nov_coefficients_K {m : ℕ} (hm : m ≤ 28) (offset : K) (v : Array K) (hv : v.size = 2 ^ m) {p : ℕ}
    (hp : p < 2 ^ m) :
    (Novel.nov 0 m fun j => ofK ((coefficients m offset v).getD j 0)).eval (ofK (offset + point p)) =
      ofK (v.getD p 0) := by
  rw [← values_getD_nov_K hm offset _ (by rw [Bridge.Ntt.coefficients_size, hv]) hp,
    Bridge.Ntt.values_coefficients_K m offset v hv]

end E2ECompleteness.Pcs.H
