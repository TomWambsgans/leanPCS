-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import KeccakFlock.TerminalCore

/-!
# The structured terminal's parts, matched to the walked form

With the row and column word weights factored as the eq tables of an 11-coordinate point are
(`wordW lr rd kr5 w = lr[w mod 32] · kd[(w / 32) mod 2] · rd[w / 64]`: lane, kind, round field), each part of
`structuredCore` is a sum of `TerminalCore.lean`'s class-by-class walked form:

* the constant column's coefficient (`tOne`, `rcOne`, `constants`, `bOne`): `tOne_eq`, `rcOne_eq`, `constants_eq`
  (characteristic two: `kd[0] + kd[1] = 1`), `bOne_eq`;
* the diagonal (`freeW`, `copiesW`, `aTMid`, `aTLast`): `diagonal_eq`;
* the shifts: `shifts_eq` (`TerminalShifts.lean`).
-/

namespace KeccakFlock.Core

open LeanVM.Parameters PcsCircuit PcsCircuit.Builder Finset KeccakFlock.Terminal UniStatement

/-- A word's eq weight from its lane, kind and round fields' tables. -/
def wordW (lAt rAt : ℕ → E) (k5 : E) (w : ℕ) : E := lAt (w % 32) * kindW k5 (w / 32 % 2) * rAt (w / 64)

theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

/-! ## Sums of the transcription -/

theorem esum_map_range' (f : ℕ → E) (a n : ℕ) : esum ((List.range' a n).map f) = ∑ i ∈ range n, f (a + i) := by
  rw [List.range'_eq_map_range, List.map_map, esum_map_range]
  rfl

theorem sumRange_eq (a b : ℕ) (f : ℕ → E) : sumRange a b f = ∑ i ∈ range (b - a), f (a + i) := by
  rw [sumRange, esum_map_range']

theorem colSum_eq (f : ℕ → E) (x : ℕ) : colSum f x = ∑ y ∈ range 5, f (x + 5 * y) := by
  rw [colSum, esum_map_range]

theorem grouped_eq (w x : ℕ → E) : grouped 25 w x = ∑ q ∈ range 25, w (q / 8) * x q := by
  have hf : (List.range 4).filter (fun g ↦ decide (8 * g < 25)) = [0, 1, 2, 3] := rfl
  simp only [grouped, hf, List.map_cons, List.map_nil, esum_map_range']
  rw [esum_eq]
  norm_num [Finset.sum_range_succ]
  ring


theorem esum_filter (l : List ℕ) (p : ℕ → Bool) (g : ℕ → E) :
    esum ((l.filter p).map g) = esum (l.map fun x ↦ if p x then g x else 0) := by
  rw [esum_eq, esum_eq]
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← ih]
    cases p a <;> simp

theorem rcBitR_eq (j z : ℕ) : rcBitR j z = rcBit j z := by
  unfold rcBitR rcBit
  rw [← RecCircuit.testBit_toNat64, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  cases h : (keccakRC.getD j 0).toNat / 2 ^ z % 2 == 1 <;> simp_all

/-- `rc_mid`: ι's bits of rounds `0..22`. -/
theorem rcMid_eq (Ew rd : ℕ → E) : rcMid Ew rd = ∑ j ∈ range 23, rd (j + 2) * RCw Ew j := by
  rw [rcMid, esum_map_range]
  have hz : ∀ z ∈ range 64, (let rounds := (List.range 24).filter fun j ↦ rcBitR j z
      if rounds.isEmpty then 0 else Ew z * esum ((rounds.filter fun j ↦ decide (j < 23)).map fun j ↦ rd (j + 2))) =
      ∑ j ∈ range 23, rd (j + 2) * (if rcBit j z then Ew z else 0) := by
    intro z _
    dsimp only
    have he : (if ((List.range 24).filter fun j ↦ rcBitR j z).isEmpty then (0 : E) else
        Ew z * esum ((((List.range 24).filter fun j ↦ rcBitR j z).filter fun j ↦ decide (j < 23)).map
          fun j ↦ rd (j + 2))) =
        Ew z * esum ((((List.range 24).filter fun j ↦ rcBitR j z).filter fun j ↦ decide (j < 23)).map
          fun j ↦ rd (j + 2)) := by
      split_ifs with h
      · rw [List.isEmpty_iff.mp h]
        simp [esum]
      · rfl
    rw [he, esum_filter, esum_filter, esum_map_range, Finset.sum_range_succ, mul_add, Finset.mul_sum]
    simp only [lt_irrefl, decide_false, Bool.false_eq_true, ite_false, ite_self, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [rcBitR_eq, decide_eq_true (mem_range.mp hj)]
    split_ifs <;> simp_all [mul_comm]
  rw [Finset.sum_congr rfl hz, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [RCw, Finset.mul_sum]

/-- `rc_last`: ι's bits of round 23. -/
theorem rcLast_eq (Ew : ℕ → E) : rcLast Ew = RCw Ew 23 := by
  rw [rcLast, esum_map_range, RCw]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  dsimp only
  have hc : ((List.range 24).filter fun j ↦ rcBitR j z).contains 23 = rcBit 23 z := by
    rw [← rcBitR_eq]
    cases h : rcBitR 23 z <;> simp [List.mem_filter, h]
  rw [hc]
  cases h : rcBit 23 z
  · simp
  · have hne : ((List.range 24).filter fun j ↦ rcBitR j z).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff_exists_mem]
      exact ⟨23, by simp [List.mem_filter, rcBitR_eq, h]⟩
    simp [hne]

/-! ## Word weights at the layout's words -/

section Words

variable (lAt rAt : ℕ → E) (k5 : E)

theorem wordW_port {q r : ℕ} (hr : r < 4) : wordW lAt rAt k5 (4 * q + r) = portW lAt rAt k5 q r := by
  unfold wordW portW groupW laneOf
  rw [show (4 * q + r) / 32 % 2 = q / 8 % 2 by omega, show (4 * q + r) / 64 = q / 8 / 2 by omega]
  ring

theorem wordW_t {j l : ℕ} (hl : l < 32) : wordW lAt rAt k5 (tWord j l) = lAt l * kindW k5 0 * rAt (j + 2) := by
  unfold wordW tWord
  rw [show (64 * (j + 2) + l) % 32 = l by omega, show (64 * (j + 2) + l) / 32 % 2 = 0 by omega,
    show (64 * (j + 2) + l) / 64 = j + 2 by omega]

theorem wordW_a {j l : ℕ} (hl : l < 32) : wordW lAt rAt k5 (aWord j l) = lAt l * kindW k5 1 * rAt (j + 2) := by
  unfold wordW aWord
  rw [show (64 * (j + 2) + 32 + l) % 32 = l by omega, show (64 * (j + 2) + 32 + l) / 32 % 2 = 1 by omega,
    show (64 * (j + 2) + 32 + l) / 64 = j + 2 by omega]

theorem stWord_succ {j l : ℕ} (hj : j < 23) : stWord (j + 1) l = aWord j l := by
  unfold stWord
  rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel]

theorem stWord_24 (l : ℕ) : stWord 24 l = 4 * l + 0 := rfl

theorem stWord_0 (l : ℕ) : stWord 0 l = 4 * l + 2 := rfl

end Words

/-! ## The constant column's coefficient -/

section Parts

variable (Ew lr rd lh rh : ℕ → E) (kr5 kh5 α cEq : E)

/-- `t_one`: the `t` rows' `1 +`, every round. -/
theorem tOne_eq : tOne lr rd kr5 = ∑ j ∈ range 24, ∑ l ∈ range 25, wordW lr rd kr5 (tWord j l) := by
  have h : sumRange 2 25 rd + rd 25 = ∑ j ∈ range 24, rd (j + 2) := by
    rw [sumRange_eq, show 25 - 2 = 23 from rfl, Finset.sum_range_succ (fun j ↦ rd (j + 2)) 23]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ ↦ by rw [Nat.add_comm]) rfl
  rw [tOne, h, sumRange_eq, show 25 - 0 = 25 from rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  rw [wordW_t _ _ _ (by have := mem_range.mp hl; omega), Nat.zero_add]
  ring

/-- `rc_one`: ι's bits, lane 0 of every round's `A` row (round 23's in the `X` word of quad 0). -/
theorem rcOne_eq : rcOne Ew lr rd kr5 = ∑ j ∈ range 24, wordW lr rd kr5 (stWord (j + 1) 0) * RCw Ew j := by
  rw [rcOne, rcMid_eq, rcLast_eq, Finset.sum_range_succ (fun j ↦ wordW lr rd kr5 (stWord (j + 1) 0) * RCw Ew j) 23,
    stWord_24, wordW_port _ _ _ (by decide), Finset.mul_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j hj ↦ ?_) rfl
  rw [stWord_succ (mem_range.mp hj), wordW_a _ _ _ (by decide)]
  ring

/-- `constants`: the `Y` words' bit 0 and the `x` quad's bit 1 (characteristic two: `kd[0] + kd[1] = 1`). -/
theorem constants_eq : constants Ew lr rd kr5 = Ew 0 * ∑ q ∈ range 32, wordW lr rd kr5 (4 * q + 1) +
    Ew 1 * (wordW lr rd kr5 (4 * 25 + 0) + wordW lr rd kr5 (4 * 25 + 3)) := by
  have hY : ∑ q ∈ range 32, wordW lr rd kr5 (4 * q + 1) =
      ∑ h ∈ range 4, ∑ a ∈ range 8, lr (laneOf a 1) * groupW kr5 rd h := by
    rw [show (32 : ℕ) = 8 * 4 from rfl, ← sum_range_mul _ 8 4]
    refine Finset.sum_congr rfl fun h hh ↦ Finset.sum_congr rfl fun a ha ↦ ?_
    have := mem_range.mp ha
    rw [wordW_port _ _ _ (by decide), portW, show (8 * h + a) / 8 = h by omega, laneOf, laneOf,
      show (4 * (8 * h + a) + 1) % 32 = (4 * a + 1) % 32 by omega]
  rw [constants, hY, wordW_port _ _ _ (by decide), wordW_port _ _ _ (by decide), esum_map_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, portW, groupW, kindW]
  norm_num
  linear_combination (-(Ew 0 * kr5 * (rd 0 + rd 1) * (lr (laneOf 0 1) + lr (laneOf 1 1) + lr (laneOf 2 1) +
    lr (laneOf 3 1) + lr (laneOf 4 1) + lr (laneOf 5 1) + lr (laneOf 6 1) + lr (laneOf 7 1)))) * two_eq_zero_E

/-- `b_one`: the `B = [1]` of the `A` rows (rounds 0..22 and the `X` words), the free inputs and the copies. -/
theorem bOne_eq : bOne lr rd kr5 = ∑ j ∈ range 24, ∑ l ∈ range 25, wordW lr rd kr5 (stWord (j + 1) l) +
    ∑ q ∈ range 25, wordW lr rd kr5 (4 * q + 2) + ∑ q ∈ range 25, wordW lr rd kr5 (4 * q + 3) := by
  have hA : kindW kr5 1 * sumRange 0 25 lr * sumRange 2 25 rd =
      ∑ j ∈ range 23, ∑ l ∈ range 25, wordW lr rd kr5 (stWord (j + 1) l) := by
    rw [sumRange_eq, sumRange_eq, show 25 - 0 = 25 from rfl, show 25 - 2 = 23 from rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [stWord_succ (mem_range.mp hj), wordW_a _ _ _ (by have := mem_range.mp hl; omega), Nat.zero_add,
      Nat.add_comm 2 j]
    ring
  have hX : esum ((List.range 25).map fun q ↦ portW lr rd kr5 q 0) =
      ∑ l ∈ range 25, wordW lr rd kr5 (stWord 24 l) := by
    rw [esum_map_range]
    exact Finset.sum_congr rfl fun l _ ↦ by rw [stWord_24, wordW_port _ _ _ (by decide)]
  have hg : ∀ r < 4, grouped 25 (groupW kr5 rd) (fun q ↦ lr (laneOf q r)) =
      ∑ q ∈ range 25, wordW lr rd kr5 (4 * q + r) := fun r hr ↦ by
    rw [grouped_eq]
    exact Finset.sum_congr rfl fun q _ ↦ by rw [wordW_port _ _ _ hr, portW, mul_comm]
  rw [bOne, hA, hX, hg 2 (by decide), hg 3 (by decide), Finset.sum_range_succ (n := 23)]

/-- **The diagonal**: the free inputs, the copies, the lin-id rows' `t` term, the `C = I` claim, times `Corr[0]`. -/
theorem diagonal_eq (c : ℕ → E) : diagonal c lr rd lh rh kr5 kh5 α cEq = c 0 *
    (∑ q ∈ range 25, wordW lr rd kr5 (4 * q + 2) * wordW lh rh kh5 (4 * q + 2) +
      ∑ q ∈ range 25, wordW lr rd kr5 (4 * q + 3) * wordW lh rh kh5 (4 * q) +
      ∑ j ∈ range 24, ∑ l ∈ range 25, wordW lr rd kr5 (stWord (j + 1) l) * wordW lh rh kh5 (tWord j l) +
      α * α * cEq) := by
  have hF : freeW lr rd lh rh kr5 kh5 = ∑ q ∈ range 25, wordW lr rd kr5 (4 * q + 2) * wordW lh rh kh5 (4 * q + 2) := by
    rw [freeW, grouped_eq]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [wordW_port _ _ _ (by decide), wordW_port _ _ _ (by decide), portW, portW]
    ring
  have hC : copiesW lr rd lh rh kr5 kh5 = ∑ q ∈ range 25, wordW lr rd kr5 (4 * q + 3) * wordW lh rh kh5 (4 * q) := by
    rw [copiesW, grouped_eq]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [wordW_port _ _ _ (by decide), show 4 * q = 4 * q + 0 from rfl, wordW_port lh rh _ (by decide), portW, portW]
    ring
  have hM : aTMid lr rd lh rh kr5 kh5 =
      ∑ j ∈ range 23, ∑ l ∈ range 25, wordW lr rd kr5 (stWord (j + 1) l) * wordW lh rh kh5 (tWord j l) := by
    rw [aTMid, sumRange_eq, sumRange_eq, show 25 - 0 = 25 from rfl, show 25 - 2 = 23 from rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [stWord_succ (mem_range.mp hj), wordW_a _ _ _ (by have := mem_range.mp hl; omega),
      wordW_t _ _ _ (by have := mem_range.mp hl; omega), Nat.zero_add, Nat.add_comm 2 j]
    ring
  have hL : aTLast lr rd lh rh kr5 kh5 =
      ∑ l ∈ range 25, wordW lr rd kr5 (stWord 24 l) * wordW lh rh kh5 (tWord 23 l) := by
    rw [aTLast, sumRange_eq, show 25 - 0 = 25 from rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    rw [stWord_24, wordW_port _ _ _ (by decide), wordW_t _ _ _ (by have := mem_range.mp hl; omega), Nat.zero_add]
    ring
  rw [diagonal, hF, hC, hM, hL, Finset.sum_range_succ (n := 23)]
  ring

end Parts

end KeccakFlock.Core
