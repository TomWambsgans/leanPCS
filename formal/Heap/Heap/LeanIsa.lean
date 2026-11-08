-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Heap.Realize
import Lv42.Protocol.LeanIsaBase

/-!
# Two list facts of leanISA's heap

The list lemmas the assembly of a leanISA heap uses (`UniKeccakSound.IdsReal.Realize` for the Keccak VM): a
`flatMap` over a filtered list, and the opcode tables as tables `3 … 8`. (SPEC §5.2's heap for leanVM 42422001's
`leanIsaInstance`, with its `BLAKE2S` table, was here; it is removed with `BLAKE2S`.)
-/

namespace Heap.LeanIsa

open Lv42.Protocol.LeanIsa

theorem flatMap_filter_of_nil {α β : Type*} (p : α → Bool) (g : α → List β) :
    ∀ l : List α, (∀ a ∈ l, p a = false → g a = []) → (l.filter p).flatMap g = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    have ih := flatMap_filter_of_nil p g l fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    by_cases hp : p a = true
    · rw [List.filter_cons_of_pos hp, List.flatMap_cons, List.flatMap_cons, ih]
    · rw [List.filter_cons_of_neg hp, List.flatMap_cons, h a (List.mem_cons_self ..)
        (by simpa using hp), List.nil_append, ih]

/-- The opcode tables are tables `3 … 8`. -/
theorem finRange_filter : (List.finRange 9).filter (fun j ↦ decide (3 ≤ j.val)) =
    (List.finRange 6).map opIdx := by decide

end Heap.LeanIsa
