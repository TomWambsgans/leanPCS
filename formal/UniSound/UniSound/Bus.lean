-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The bus is `formal/Heap`'s.
import UniSound.Piop

/-!
# Round `0`: the bus and the constraints' batching

After `C1`'s root the verifier draws `α ∈ E^4`, `β` (the bus) and `γ` (the constraints' batching).
The state after them (`BusModel.MainOK`): **the heap holds** at `(α, β)` (`Heap.HeapData.Sat`: some
heap values meet the tree, leaf and root identities, `formal/Heap`) for the heap the verifier reads
off `C1` (`hd`), and **the batched constraints vanish** on every row (`Σ_i γ^i C_i(x) = 0`, the
constraint quotient's numerator on the domain, `cvec`).

**`BusModel.mainSound`**: round `0` turns `¬ MainHolds` (`ConstraintsVanish ∧ Balanced ∧
CountsNonzero ∧ PublicLinesHold` of `C1`'s Lv42 stack) into `MainOK` with probability at most
`busError N + (ncv − 1) / |E|`: if every constraint vanishes (so the limb copies equal `q_flock`'s
slots and the heap realizes Lv42's bus, `realizes`), the bus is unbalanced and `Heap`'s
`card_sat_not_balanced_le` bounds the `(α, β)` that make the heap hold (`4N/|E|`); otherwise some
row's constraint vector is nonzero and at most `ncv − 1` values of `γ` cancel it
(`card_powComb_le`).

**`BusModel.rel_of`**: with Flock's predicate on `C1`'s `q_flock` (`aux_of_flock`), `MainHolds` is
the relation.

The model's fields are the bridges left (`formal/Heap`'s report: the verifier's leaves read as
Lv42's flushes with the copies, the padded rows' leaves `1`): `hd` well formed and realizing Lv42's
bus when the copies hold, the constraint vectors' vanishing giving the four clauses and the copies,
Flock's column read off `C1` as Lv42's region.
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

namespace BusModel

variable {D : Deployment} {κ : ℕ}

/-- Five challenges are `(α, β)`. -/
theorem card_fin_five (P : (Fin 4 → E) → E → Prop) [∀ a b, Decidable (P a b)] :
    (univ.filter fun v : Fin (4 + 1) → E =>
      P (fun i => (List.ofFn v).getD i.val 0) ((List.ofFn v).getD 4 0)).card =
      (univ.filter fun ab : (Fin 4 → E) × E => P ab.1 ab.2).card := by
  refine Finset.card_bij (fun v _ => (fun i => v i.castSucc, v 4)) (fun v hv => ?_)
    (fun v _ w _ h => ?_) (fun ab hab => ?_)
  · simp only [mem_filter, mem_univ, true_and] at hv ⊢
    have h1 : (fun i : Fin 4 => (List.ofFn v).getD i.val 0) = fun i => v i.castSucc := by
      funext i
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      rfl
    have h2 : (List.ofFn v).getD 4 0 = v 4 := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      rfl
    rw [h1, h2] at hv
    exact hv
  · simp only [Prod.mk.injEq] at h
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact h.2
    · exact congrFun h.1 j
  · refine ⟨Fin.snoc ab.1 ab.2, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hab ⊢
      have h1 : (fun i : Fin 4 => (List.ofFn (Fin.snoc ab.1 ab.2 : Fin (4 + 1) → E)).getD i.val 0) =
          ab.1 := by
        funext i
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        exact Fin.snoc_castSucc (α := fun _ => E) ab.2 ab.1 i
      have h2 : (List.ofFn (Fin.snoc ab.1 ab.2 : Fin (4 + 1) → E)).getD 4 0 = ab.2 := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
        exact Fin.snoc_last (α := fun _ => E) ab.2 ab.1
      rw [h1, h2]
      exact hab
    · refine Prod.ext (funext fun i => ?_) ?_
      · exact Fin.snoc_castSucc (α := fun _ => E) ab.2 ab.1 i
      · exact Fin.snoc_last (α := fun _ => E) ab.2 ab.1

end BusModel

end UniSound
