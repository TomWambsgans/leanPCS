-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Moved from `formal/UniSound`'s `UniSound/Ids/Facts.lean`
-- (`eqKernel_snoc`, `size_eqKernel`, `eqKernel_getElem`, `eqKernel_getD`) and `formal/FlockSound`'s
-- `FlockSoundUni/Transcription.lean` (`tx_array_getD`, `tx_eqEval_foldl`), which import this module; the declarations
-- keep their names and namespaces.
module

public import UniStatement.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Facts about the verifier's `eqKernel` and `eqEval`

`eqKernel`'s size and entries (`size_eqKernel`, `eqKernel_getD`: the entry `x` is `Π_j (r_j if bit j of x else
1 + r_j)`), and `eqEval`'s fold as a product (`tx_eqEval_foldl`). Instruction-set-independent: the univariate
verifier's soundness and the Keccak-f block's terminal (`formal/KeccakFlock`) read them.
-/

@[expose] public section

namespace UniSound.Ids.Facts

open LeanVM.Parameters UniStatement Finset

/-! ## `eqKernel` is the fingerprint's weights -/

theorem eqKernel_snoc (l : List E) (r : E) :
    eqKernel (l ++ [r]) = (eqKernel l).map (· * (1 + r)) ++ (eqKernel l).map (· * r) := by
  simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem size_eqKernel (l : List E) : (eqKernel l).size = 2 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l r ih =>
    rw [eqKernel_snoc, Array.size_append, Array.size_map, Array.size_map, ih, List.length_append,
      List.length_singleton, pow_succ, mul_two]

/-- **`eqKernel`'s entry `x`**: `Π_j (r_j if bit j of x else 1 + r_j)`, the first coordinate the lowest
bit. -/
theorem eqKernel_getElem (l : List E) (x : ℕ) (hx : x < (eqKernel l).size) :
    (eqKernel l)[x] =
      ∏ j ∈ range l.length, (if x.testBit j then l.getD j 0 else 1 + l.getD j 0) := by
  induction l using List.reverseRecOn generalizing x with
  | nil =>
    have : x = 0 := by simpa [eqKernel] using hx
    subst this
    rfl
  | append_singleton l r ih =>
    have hlen := size_eqKernel l
    have hgetD : ∀ j < l.length, (l ++ [r]).getD j 0 = l.getD j 0 := fun j hj ↦ by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    have hlast : (l ++ [r]).getD l.length 0 = r := by simp [List.getD_eq_getElem?_getD]
    simp only [eqKernel_snoc]
    rw [List.length_append, List.length_singleton, Finset.prod_range_succ]
    by_cases hlo : x < 2 ^ l.length
    · rw [Array.getElem_append_left (by simp [hlen, hlo]), Array.getElem_map,
        ih x (by rw [hlen]; exact hlo), Nat.testBit_lt_two_pow hlo, hlast]
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ by rw [hgetD j (Finset.mem_range.mp hj)]
    · have hx' : x < 2 ^ l.length + 2 ^ l.length := by
        simp only [eqKernel_snoc, Array.size_append, Array.size_map, hlen] at hx
        omega
      obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ l.length + y := ⟨x - 2 ^ l.length, by omega⟩
      have hy : y < 2 ^ l.length := by omega
      rw [Array.getElem_append_right (by simp [hlen]), Array.getElem_map]
      simp only [Array.size_map, hlen, Nat.add_sub_cancel_left]
      rw [ih y (by rw [hlen]; exact hy), Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy, hlast]
      simp only [Bool.not_false, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun j hj ↦ by
        rw [hgetD j (Finset.mem_range.mp hj), Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hj)]

theorem eqKernel_getD (l : List E) (x : ℕ) (hx : x < 2 ^ l.length) :
    (eqKernel l).getD x 0 =
      ∏ j ∈ range l.length, (if x.testBit j then l.getD j 0 else 1 + l.getD j 0) := by
  have hx' : x < (eqKernel l).size := by rw [size_eqKernel]; exact hx
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hx', Option.getD_some,
    eqKernel_getElem l x hx']

end UniSound.Ids.Facts

namespace FlockSound.Uni

open UniStatement LeanVM.Parameters Finset

theorem tx_array_getD (a : Array E) (i : ℕ) (d : E) : a.getD i d = a.toList.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem tx_eqEval_foldl : ∀ (x y : List E) (a : E), x.length = y.length →
    (x.zip y).foldl (fun acc (u, v) ↦ acc * (1 + u + v)) a =
      a * ∏ i ∈ range x.length, (1 + x.getD i 0 + y.getD i 0)
  | [], [], a, _ => by simp
  | u :: x, v :: y, a, h => by
    rw [List.zip_cons_cons, List.foldl_cons, tx_eqEval_foldl x y _ (by simpa using h),
      List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

end FlockSound.Uni

end
