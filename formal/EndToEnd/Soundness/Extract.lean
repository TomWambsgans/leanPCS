-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import QuotientSecurity.DeployedConcrete
import Soundness.MerkleWord
import Soundness.Replay

/-!
# Search lemmas of the extractor

`List.findSome?` and `Option.orElse` specifications (`findSome_sat`, `findSome_spec`, `orElse_spec`) and the
decoded stacks' congruence (`mem_decodeStacks_congr`).

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

set_option linter.unusedSectionVars false

-- The membership circuit is a closed term of `2^22` rows, and its cells an additive transform of
-- `2^24` entries: never evaluate them (no simprocs here, which would try to decide the relation).
attribute [local irreducible] PcsQuotient.membershipBuilder PcsQuotient.secretOfStack
set_option simprocs false

namespace Soundness

open QuotientRpm QuotientSecurity Compose Compose.Reduce LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge
open LeanVM.Protocol.EndToEnd

/-! ## Lists -/

/-- A list's find, when every find satisfies `p`, satisfies `p`. -/
theorem findSome_sat {α β : Type} (l : List α) (f : α → Option β) (p : β → Prop)
    (hf : ∀ a b, f a = some b → p b) : ∀ b, l.findSome? f = some b → p b := fun b h ↦ by
  obtain ⟨a, -, hfa⟩ := List.exists_of_findSome?_eq_some h
  exact hf a b hfa

/-- A list with a find has a find satisfying `p`, when every find satisfies `p`. -/
theorem findSome_spec {α β : Type} (l : List α) (f : α → Option β) (p : β → Prop)
    (hf : ∀ a b, f a = some b → p b) (h : ∃ a ∈ l, (f a).isSome) :
    ∃ b, l.findSome? f = some b ∧ p b := by
  obtain ⟨a, ha, hfa⟩ := h
  rcases h₂ : l.findSome? f with _ | b
  · exact absurd hfa (by rw [List.findSome?_eq_none_iff.mp h₂ a ha]; simp)
  · exact ⟨b, rfl, findSome_sat l f p hf b h₂⟩

/-- The first of two options, the second if the first is none: when the first satisfies `p` if it
is some, and the second is some satisfying `p`, some satisfying `p`. -/
theorem orElse_spec {β : Type} (o₁ o₂ : Option β) (p : β → Prop)
    (h₁ : ∀ b, o₁ = some b → p b) (h₂ : ∃ b, o₂ = some b ∧ p b) :
    ∃ b, (o₁ <|> o₂) = some b ∧ p b := by
  rcases o₁ with _ | b
  · simpa using h₂
  · exact ⟨b, rfl, h₁ b rfl⟩

/-! ## The decoder's members -/

/-- mumbai's `decodeStacks` lists the same stacks for two words that agree on the code's columns. -/
theorem mem_decodeStacks_congr {μ R : ℕ} (hw : Whir.Admissible μ R) {W W' : Word}
    (h : ∀ v < 2 ^ (μ - laneBits + R), W v = W' v) (st : Vector K (2 ^ μ))
    (hst : st ∈ LeanVM.Extraction.decodeStacks μ R W) :
    st ∈ LeanVM.Extraction.decodeStacks μ R W' := by
  have h1 : (Column.mk st : Column μ) ∈ decodeColumns μ R W := List.mem_map.mpr ⟨st, hst, rfl⟩
  rw [mem_decodeColumns hw, candidates_congr h] at h1
  rw [← mem_decodeColumns hw] at h1
  obtain ⟨st', hst', he⟩ := List.mem_map.mp h1
  rwa [← column_mk_injective μ he]

end Soundness
