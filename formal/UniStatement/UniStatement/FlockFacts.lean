-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Moved from `formal/FlockSound`'s
-- `FlockSoundUni/TxBasic.lean` (`sub_eq_add_E`, `ofLane_zero`, `ofLane_xor`,
-- `eK_eq`) and `FlockSoundUni/Transcription.lean` (the PHI points and the skip's Lagrange weights, `tx_dot_eq`), which
-- import this module; the declarations keep their names and namespaces.
module

public import UniStatement.FlockBase
public import Lv42.Parameters.Flock
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Facts about Flock's PHI points and the skip's Lagrange weights

The code's `phi` is `φ_8` (`Lv42.Parameters.Flock.phi8`, injective below `128`: `FlockSound.phi8_injOn`) (`phi_eq`); the window denominator is every node's (`windowDenominator_eq`); the code's
`lagrangeWeights` are the Lagrange basis values at the nodes (`lagrangeWeights_getD`); `dot` as a sum (`tx_dot_eq`).
Instruction-set-independent: the Flock soundness of both blocks and the Keccak-f block's terminal
(`formal/KeccakFlock`) read them.
-/

-- The proofs are moved unchanged from `FlockSoundUni` (built without `warningAsError`).
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

@[expose] public section

namespace FlockSound.Uni

open UniStatement LeanVM.Parameters Finset

theorem sub_eq_add_E (a b : E) : a - b = a + b := CharTwo.sub_eq_add a b

theorem ofLane_zero : K.ofLane 0 = 0 := rfl

theorem ofLane_xor (a b : UInt64) : K.ofLane (a ^^^ b) = K.ofLane a + K.ofLane b := by
  simp only [K.ofLane, BF64.add_def, BF64.toBitVec_ofBitVec, UInt64.toBitVec_xor]

theorem eK_eq (c : UInt64) : eK c = ofK (K.ofLane c) := by
  rw [ofK_eq_ofLimbs]
  rfl

theorem tx_foldl_mul_range' (f : ℕ → E) : ∀ (m s : ℕ) (a : E),
    (List.range' s m).foldl (fun acc k ↦ acc * f k) a = a * ∏ k ∈ range m, f (s + k)
  | 0, s, a => by simp
  | m + 1, s, a => by
    rw [List.range'_succ, List.foldl_cons, tx_foldl_mul_range' f m (s + 1), Finset.prod_range_succ']
    simp only [add_zero]
    rw [Finset.prod_congr rfl fun k _ ↦ show f (s + 1 + k) = f (s + (k + 1)) by congr 1; omega]
    ring

theorem tx_ofLane_phiFold (v : ℕ) : ∀ n : ℕ,
    K.ofLane ((List.range n).foldl (fun acc bit ↦
      if v.testBit bit then acc ^^^ Flock.phiBasis.getD bit 0 else acc) 0) =
      ∑ b ∈ range n, if v.testBit b then K.ofLane (Flock.phiBasis.getD b 0) else 0
  | 0 => by simp [ofLane_zero]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ,
      ← tx_ofLane_phiFold v n]
    split_ifs <;> simp [ofLane_xor]

/-- **`phi` is `φ_8`**: the code's `UInt64` xor of the basis words is the sum in `K`. -/
theorem phi_eq (v : ℕ) : Flock.phi v = ofK (Lv42.Parameters.Flock.phi8 v) := by
  rw [Flock.phi, eK_eq, tx_ofLane_phiFold, Lv42.Parameters.Flock.phi8, ← Fin.sum_univ_eq_sum_range]
  refine congrArg ofK (Finset.sum_congr rfl fun i _ ↦ ?_)
  by_cases h : v.testBit i
  · simp only [h, ↓reduceIte]
    fin_cases i <;> rfl
  · simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem tx_ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

/-- **`phi` is `F_2`-linear.** -/
theorem phi_xor (a b : ℕ) : Flock.phi (a ^^^ b) = Flock.phi a + Flock.phi b := by
  rw [phi_eq, phi_eq, phi_eq, phi8_xor, tx_ofK_add]

/-- The nodes below `128` are distinct (`phi8_injOn`). -/
theorem phi_injOn {a b : ℕ} (ha : a < 128) (hb : b < 128) (h : Flock.phi a = Flock.phi b) : a = b := by
  rw [phi_eq, phi_eq] at h
  exact phi8_injOn ha hb (ofK_injective h)

theorem tx_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  have h' : a ^^^ (a ^^^ b) = a ^^^ 0 := by rw [h]
  rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero, eq_comm] at h'

/-- Every node's denominator `Π_{j ≠ i} (φ_i − φ_j)` is the window's `Π_{t ≠ 0} φ_t`: `j ↦ i xor j`. -/
theorem tx_prod_window {n i : ℕ} (hi : i < 2 ^ n) :
    ∏ j ∈ (range (2 ^ n)).erase i, (Flock.phi i - Flock.phi j) =
      ∏ t ∈ range (2 ^ n - 1), Flock.phi (1 + t) := by
  have hne : ∀ j, j ≠ i → i ^^^ j ≠ 0 := fun j hj h ↦ hj (tx_xor_eq_zero h).symm
  refine Finset.prod_nbij' (fun j ↦ (i ^^^ j) - 1) (fun t ↦ i ^^^ (t + 1)) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj ⊢
    have h1 := Nat.xor_lt_two_pow hi hj.2
    have h2 := hne j hj.1
    omega
  · intro t ht
    simp only [Finset.mem_erase, Finset.mem_range] at ht ⊢
    refine ⟨fun h ↦ ?_, Nat.xor_lt_two_pow hi (by omega)⟩
    have h' : i ^^^ (i ^^^ (t + 1)) = i ^^^ i := by rw [h]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h'
    omega
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    have h2 := hne j hj.1
    show i ^^^ ((i ^^^ j) - 1 + 1) = j
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h2), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · intro t _
    show (i ^^^ (i ^^^ (t + 1))) - 1 = t
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.add_sub_cancel]
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    have h2 := hne j hj.1
    rw [sub_eq_add_E, ← phi_xor, Nat.add_sub_cancel' (Nat.one_le_iff_ne_zero.mpr h2)]

/-- **The window denominator** is every node's denominator. -/
theorem windowDenominator_eq {n i : ℕ} (hi : i < 2 ^ n) :
    Flock.windowDenominator (2 ^ n) =
      (∏ j ∈ (range (2 ^ n)).erase i, (Flock.phi i - Flock.phi j))⁻¹ := by
  rw [tx_prod_window hi, Flock.windowDenominator, tx_foldl_mul_range', one_mul]

/-- Prefix products pushed one by one. -/
theorem tx_foldl_push (d : ℕ → E) : ∀ n : ℕ,
    (List.range n).foldl (fun acc i ↦ acc.push (acc.back?.getD 1 * d i)) #[1] =
      ((List.range (n + 1)).map fun t ↦ ∏ j ∈ range t, d j).toArray
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, tx_foldl_push d n, List.foldl_cons, List.foldl_nil,
      @List.range_succ (n + 1), List.map_append]
    simp [Finset.prod_range_succ, List.getLast?_range]

theorem lagrangeWeights_length (count : ℕ) (pt : E) :
    (Flock.lagrangeWeights count pt).length = count := by
  simp [Flock.lagrangeWeights]

theorem tx_lagrangeWeights_getD {count i : ℕ} (hi : i < count) (pt : E) :
    (Flock.lagrangeWeights count pt).getD i 0 =
      (∏ j ∈ range i, (pt + Flock.phi j)) *
        (∏ j ∈ range (count - 1 - i), (pt + Flock.phi (count - 1 - j))) * Flock.windowDenominator count := by
  simp only [Flock.lagrangeWeights]
  simp only [tx_foldl_push]
  simp [List.getD_eq_getElem?_getD, hi, Array.getD_eq_getD_getElem?]
  left
  rw [List.getElem?_range (by omega), Option.map_some, Option.getD_some]
  congr 1
  · refine Finset.prod_congr rfl fun x hx ↦ ?_
    rw [Finset.mem_range] at hx
    simp [Array.getElem?_ofFn, show x < count by omega]
  · rw [show count - (i + 1) = count - 1 - i by omega]
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    rw [Finset.mem_range] at hx
    simp [Array.getElem?_ofFn, show count - 1 - x < count by omega]

/-- `Π_{j ∈ [0, N) \ {i}} f j` as the prefix before `i` and the suffix after. -/
theorem tx_prod_erase (f : ℕ → E) {N i : ℕ} (hi : i < N) :
    ∏ j ∈ (range N).erase i, f j = (∏ j ∈ range i, f j) * ∏ j ∈ range (N - 1 - i), f (i + 1 + j) := by
  have hmem : i ∈ range N := Finset.mem_range.mpr hi
  have h1 := Finset.mul_prod_erase (range N) (fun j ↦ if j = i then 1 else f j) hmem
  simp only [if_true, one_mul] at h1
  rw [Finset.prod_congr rfl fun j hj ↦ show f j = (if j = i then 1 else f j) by
    rw [if_neg (Finset.ne_of_mem_erase hj)], h1]
  rw [show N = i + 1 + (N - 1 - i) by omega, Finset.prod_range_add, Finset.prod_range_succ, if_pos rfl,
    mul_one, show i + 1 + (N - 1 - i) - 1 - i = N - 1 - i by omega]
  congr 1
  · exact Finset.prod_congr rfl fun j hj ↦ by rw [if_neg (by rw [Finset.mem_range] at hj; omega)]
  · exact Finset.prod_congr rfl fun j _ ↦ by rw [if_neg (by omega)]

/-- **The code's weight at node `i`** is the Lagrange basis polynomial's value:
`Π_{j ≠ i} (z − φ_j) / (φ_i − φ_j)` over the nodes `φ(0), …, φ(2^n − 1)`. -/
theorem lagrangeWeights_getD {n i : ℕ} (hi : i < 2 ^ n) (z : E) :
    (Flock.lagrangeWeights (2 ^ n) z).getD i 0 =
      ∏ j ∈ (range (2 ^ n)).erase i, (Flock.phi i - Flock.phi j)⁻¹ * (z - Flock.phi j) := by
  rw [tx_lagrangeWeights_getD hi, windowDenominator_eq hi, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, tx_prod_erase (fun j ↦ z - Flock.phi j) hi]
  have hB : ∏ j ∈ range (2 ^ n - 1 - i), (z + Flock.phi (2 ^ n - 1 - j)) =
      ∏ j ∈ range (2 ^ n - 1 - i), (z - Flock.phi (i + 1 + j)) := by
    rw [← Finset.prod_range_reflect (fun j ↦ z - Flock.phi (i + 1 + j))]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    rw [sub_eq_add_E]
    congr 2
    omega
  rw [hB]
  simp only [sub_eq_add_E]
  ring

/-- `dot` is the sum of the products, the second list read by `getD`. -/
theorem tx_dot_foldl : ∀ (w v : List E) (a : E),
    (w.zip v).foldl (fun acc (x, y) ↦ acc + x * y) a =
      a + ∑ i ∈ range w.length, w.getD i 0 * v.getD i 0
  | [], _, a => by simp
  | x :: w, [], a => by simp
  | x :: w, y :: v, a => by
    rw [List.zip_cons_cons, List.foldl_cons, tx_dot_foldl w v, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem tx_dot_eq (w v : List E) : dot w v = ∑ i ∈ range w.length, w.getD i 0 * v.getD i 0 := by
  rw [dot, tx_dot_foldl, zero_add]

end FlockSound.Uni

end
