-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import KeccakFlock.TerminalEq
import UniStatement.BasicFacts

/-!
# The terminals' inputs: eq tables, packing weights, correlations

The facts that connect the two transcriptions' inputs to `structuredCore_eq`'s tables:

* `eqKernel_factor`: the eq table of an 11-coordinate point at word `w` is the product of the tables of its lane field
  (`[..5]`) and round field (`[6..]`) and the kind factor of coordinate 5 (`wordW`);
* `eqKernel_sum`: an eq table sums to 1; `eqKernel_append`: the table of a concatenated point is the tensor product;
* `eqEval_constantBits`: the pin's weight is the eq table at word 1;
* `bilinear_eq_WF`: the matrices' bilinear form is the walked form with the eq tables as word weights.
-/

namespace KeccakFlock.Core

open LeanVM.Parameters PcsCircuit PcsCircuit.Builder Finset KeccakFlock.Terminal UniStatement UniStatement.Flock

/-! ## Eq tables -/

theorem sum_getD_eq_sum (l : List E) : ∑ i ∈ range l.length, l.getD i 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons, ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- **An eq table sums to 1.** -/
theorem eqKernel_sum (l : List E) : ∑ i ∈ range (2 ^ l.length), (eqKernel l).getD i 0 = 1 := by
  have hs : ∀ l : List E, (eqKernel l).toList.sum = 1 := by
    intro l
    induction l using List.reverseRecOn with
    | nil => simp [eqKernel]
    | append_singleton l r ih =>
      rw [UniSound.Ids.Facts.eqKernel_snoc, Array.toList_append, Array.toList_map, Array.toList_map,
        List.sum_append, List.sum_map_mul_right, List.sum_map_mul_right]
      simp only [List.map_id']
      rw [ih]
      linear_combination r * two_eq_zero_E
  have hl : (eqKernel l).toList.length = 2 ^ l.length := by
    rw [Array.length_toList, UniSound.Ids.Facts.size_eqKernel]
  rw [← hl, ← hs l]
  rw [← sum_getD_eq_sum]
  exact Finset.sum_congr rfl fun i _ ↦ FlockSound.Uni.tx_array_getD _ _ _

theorem testBit_kind (w : ℕ) : w.testBit 5 = decide (w / 32 % 2 = 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]

/-- **The eq table of an 11-coordinate point factors** into its lane, kind and round fields. -/
theorem eqKernel_factor (c : List E) (hc : c.length = 11) {w : ℕ} (hw : w < 2048) :
    (eqKernel c).getD w 0 = wordW (fun i ↦ (eqKernel (c.take 5)).getD i 0) (fun i ↦ (eqKernel (c.drop 6)).getD i 0)
      (c.getD 5 0) w := by
  have h5 : (c.take 5).length = 5 := by simp [hc]
  have h6 : (c.drop 6).length = 5 := by simp [hc]
  simp only [wordW]
  rw [UniSound.Ids.Facts.eqKernel_getD c w (by rw [hc]; exact hw),
    UniSound.Ids.Facts.eqKernel_getD _ _ (by rw [h5]; omega),
    UniSound.Ids.Facts.eqKernel_getD _ _ (by rw [h6]; omega), hc, h5, h6,
    show (11 : ℕ) = 5 + (1 + 5) from rfl, Finset.prod_range_add, Finset.prod_range_add, Finset.prod_range_one]
  have hl : ∀ j ∈ range 5, (if w.testBit j then c.getD j 0 else 1 + c.getD j 0) =
      (if (w % 32).testBit j then (c.take 5).getD j 0 else 1 + (c.take 5).getD j 0) := fun j hj ↦ by
    have hj := mem_range.mp hj
    rw [show (32 : ℕ) = 2 ^ 5 from rfl, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]
    simp [List.getD_eq_getElem?_getD, hj]
  have hr : ∀ j ∈ range 5, (if w.testBit (5 + (1 + j)) then c.getD (5 + (1 + j)) 0 else 1 + c.getD (5 + (1 + j)) 0) =
      (if (w / 64).testBit j then (c.drop 6).getD j 0 else 1 + (c.drop 6).getD j 0) := fun j _ ↦ by
    rw [show (64 : ℕ) = 2 ^ 6 from rfl, Nat.testBit_div_two_pow, show j + 6 = 5 + (1 + j) by ring]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, show 6 + j = 5 + (1 + j) by ring]
  rw [Finset.prod_congr rfl hl, Finset.prod_congr rfl hr, Nat.add_zero, testBit_kind]
  unfold kindW
  by_cases h : w / 32 % 2 = 1
  · rw [decide_eq_true h, ite_eq_left rfl, ite_eq_right (by omega)]
    ring
  · rw [decide_eq_false h, ite_eq_right (by decide), ite_eq_left (by omega)]
    ring

/-- **The pin's weight** `eq(bits(1), chi')` is the eq table at word 1. -/
theorem eqEval_constantBits (c : List E) (hc : c.length = 11) : eqEval constantBits c = (eqKernel c).getD 1 0 := by
  rw [eqEval, FlockSound.Uni.tx_eqEval_foldl _ _ 1 (by simp [constantBits, hc]), one_mul,
    UniSound.Ids.Facts.eqKernel_getD c 1 (by rw [hc]; decide), hc]
  simp only [constantBits, List.length_map, List.length_range]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  have hj := mem_range.mp hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.getD_some,
    bitE]
  split_ifs
  · linear_combination two_eq_zero_E
  · ring

/-! ## The walked form of the bilinear form -/

/-- **The matrices' bilinear form is the walked form**, the row and column word weights the eq tables of `chi_in`
and `chi_in'`, the packing weights `lowWeights`. -/
theorem bilinear_eq_WF (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (α : E) :
    bilinear zSkip rowLow chiIn chiInPrime s α =
      WF (fun z ↦ (rowLowWeights zSkip rowLow).2.getD z 0) (fun i ↦ s.getD i 0)
        (fun w ↦ (eqKernel chiIn).getD w 0) (fun w ↦ (eqKernel chiInPrime).getD w 0) α := by
  set sv := fun i ↦ s.getD i 0
  set γ := fun w ↦ (eqKernel chiInPrime).getD w 0
  set G : ℕ → E := fun k ↦ eRow zSkip rowLow chiIn k *
    (lsum sv γ (rowW (k / 64) (k % 64)).1 + α * lsum sv γ (rowW (k / 64) (k % 64)).2)
  have hk : ∀ k : Pos, (∑ j : Pos, eRow zSkip rowLow chiIn k * ((if matA k j then wCol chiInPrime s j else 0) +
      α * (if matB k j then wCol chiInPrime s j else 0))) = G k := fun k ↦ by
    have e1 : (∑ j : Pos, if matA k j then wCol chiInPrime s j else 0) = lsum sv γ (row k).1 :=
      sum_ite_xorMem (row k).1 (fun j : Pos ↦ wCol chiInPrime s j)
    have e2 : (∑ j : Pos, if matB k j then wCol chiInPrime s j else 0) = lsum sv γ (row k).2 :=
      sum_ite_xorMem (row k).2 (fun j : Pos ↦ wCol chiInPrime s j)
    have e3 : (∑ j : Pos, eRow zSkip rowLow chiIn k * ((if matA k j then wCol chiInPrime s j else 0) +
        α * (if matB k j then wCol chiInPrime s j else 0))) = eRow zSkip rowLow chiIn k *
          ((∑ j : Pos, if matA k j then wCol chiInPrime s j else 0) +
            α * ∑ j : Pos, if matB k j then wCol chiInPrime s j else 0) := by
      rw [Finset.mul_sum (a := α), ← Finset.sum_add_distrib, Finset.mul_sum]
    rw [e3, e1, e2]
    rfl
  unfold bilinear WF
  rw [Finset.sum_congr rfl fun k _ ↦ hk k, Fin.sum_univ_eq_sum_range G, show (2 : ℕ) ^ m = 64 * 2048 from rfl,
    ← sum_range_mul G 64 2048]
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  unfold wordTerm
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz := mem_range.mp hz
  simp only [G, eRow, show (64 * w + z) % 64 = z by omega, show (64 * w + z) / 64 = w by omega, mul_add,
    mul_assoc]

/-- The walked form reads the word weights only at words `< 2048` and the slices at `< 64`. -/
theorem WF_congr (Ew : ℕ → E) {sv sv' ρ ρ' γ γ' : ℕ → E} (α : E) (hs : ∀ z < 64, sv z = sv' z)
    (hρ : ∀ w < 2048, ρ w = ρ' w) (hγ : ∀ w < 2048, γ w = γ' w) : WF Ew sv ρ γ α = WF Ew sv' ρ' γ' α := by
  have hl : ∀ L : List Pos, lsum sv γ L = lsum sv' γ' L := fun L ↦ by
    unfold lsum
    refine congrArg List.sum (List.map_congr_left fun p _ ↦ ?_)
    have : p.val < 131072 := p.isLt
    unfold wc
    rw [hs _ (Nat.mod_lt _ (by decide)), hγ _ (by omega)]
  unfold WF wordTerm
  refine Finset.sum_congr rfl fun w hw ↦ Finset.sum_congr rfl fun z _ ↦ ?_
  rw [hl, hl, hρ w (mem_range.mp hw)]

end KeccakFlock.Core
