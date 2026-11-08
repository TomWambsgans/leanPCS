-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniSound.Ids.Leaves

/-!
# `MainOfPolysP`: the identities as polynomials give the heap and the constraint vectors

`mainOfPolys`: where every polynomial of `polysOf` is zero (so the counts are in range: out of range the
list is the constant `1`), the heap read off `C1` holds at `(α, β)` with `T` the committed heap at the
points (`heapT`: the tree `tree_of_treeP`, every block's leaves laid end to end at the heap's positions
`leavesHold_of`, the root `root_of_rootP`), and the constraint vectors vanish on `V_{r_W}`
(`cvec_of_wP`).
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset Polynomial

/-- Blocks laid end to end, each holding at its position, hold. -/
theorem leavesHold_of {τ M : Type} [CommMonoid M] (fp : τ → M) (T : ℕ → M) :
    ∀ (bs : List (Heap.LeafBlock τ)) (o : ℕ) (pos : ℕ → ℕ),
      (∀ i < bs.length, pos i = o + ((bs.take i).map Heap.LeafBlock.size).sum) →
      (∀ i (h : i < bs.length), (bs[i]).Holds fp T (pos i)) → Heap.LeavesHold fp T o bs
  | [], _, _, _, _ => trivial
  | b :: bs, o, pos, hp, hh => by
    refine ⟨?_, leavesHold_of fp T bs (o + b.size) (fun i ↦ pos (i + 1)) (fun i hi ↦ ?_) (fun i hi ↦ ?_)⟩
    · have h0 := hh 0 (by simp)
      rw [hp 0 (by simp)] at h0
      simpa using h0
    · rw [hp (i + 1) (by simp; omega)]
      simp [List.take_succ_cons, add_assoc]
    · exact hh (i + 1) (by simp; omega)

theorem sum_take_succ_le (l : List ℕ) (i : ℕ) (hi : i < l.length) :
    (l.take i).sum + l[i] ≤ l.sum := by
  have h1 : (l.take (i + 1)).sum = (l.take i).sum + l[i] := by
    rw [List.take_add_one, List.sum_append]
    simp [List.getElem?_eq_getElem hi]
  rw [← h1]
  exact List.Sublist.sum_le_sum (List.take_sublist _ _) (fun _ _ ↦ Nat.zero_le _)

theorem mem_zip_range {α : Type} (l : List α) (i : ℕ) (hi : i < l.length) :
    (l[i], i) ∈ l.zip (List.range l.length) := by
  have hz : i < (l.zip (List.range l.length)).length := by simp [hi]
  have := List.getElem_mem hz
  rwa [List.getElem_zip, List.getElem_range] at this

end UniSound.Ids
