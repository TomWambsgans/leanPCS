-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniStatement.Rec
import FlockSoundUni.Transcription

/-!
# `for` loops in `Id` as folds

A `for` loop in `Id` whose body always yields is a `List.foldl` (`forIn_list_eq`, `forIn_range0_eq`; and with the
body's own value as the step, `forIn_list_value`, `forIn_range0_value`, `forIn_range_value`). The Keccak-f block's
terminal bridge (`UniKeccakSound.Flock.Bridge`) rewrites its loops with these, without evaluating anything.
-/

namespace FlockSound.Uni.Walk

open UniStatement UniStatement.Flock LeanVM.Parameters

/-! ## `for` loops in `Id` as folds -/

theorem forIn_list_eq {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β)) (g : β → α → β)
    (h : ∀ a b, f a b = pure (ForInStep.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons x l ih =>
    rw [List.forIn_cons, h, List.foldl_cons, ← ih]
    rfl

theorem forIn_range0_eq {β : Type} (n : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β)) (g : β → ℕ → β)
    (h : ∀ i b, f i b = pure (ForInStep.yield (g b i))) :
    forIn [:n] init f = pure ((List.range' 0 n).foldl g init) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_list_eq _ _ _ g fun a b ↦ h a b]
  congr 2
  simp [Std.Legacy.Range.size]

theorem forIn_list_value {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (h : ∀ a b, ∃ c, f a b = pure (ForInStep.yield c)) :
    forIn l init f = pure (l.foldl (fun b a ↦ (Id.run (f a b)).value) init) := by
  refine forIn_list_eq l init f _ fun a b ↦ ?_
  obtain ⟨c, hc⟩ := h a b
  rw [hc]
  rfl

theorem forIn_range0_value {β : Type} (n : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β))
    (h : ∀ a b, ∃ c, f a b = pure (ForInStep.yield c)) :
    forIn [:n] init f = pure ((List.range' 0 n).foldl (fun b a ↦ (Id.run (f a b)).value) init) := by
  refine forIn_range0_eq n init f _ fun a b ↦ ?_
  obtain ⟨c, hc⟩ := h a b
  rw [hc]
  rfl

theorem forIn_range_value {β : Type} (a n : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β))
    (h : ∀ a b, ∃ c, f a b = pure (ForInStep.yield c)) :
    forIn [a:a + n] init f = pure ((List.range' a n).foldl (fun b i ↦ (Id.run (f i b)).value) init) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_list_value _ _ _ h]
  congr 2
  simp [Std.Legacy.Range.size]

end FlockSound.Uni.Walk
