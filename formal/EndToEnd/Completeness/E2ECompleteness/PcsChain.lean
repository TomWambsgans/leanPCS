-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/Chain.lean` (the previous protocol's three challenges) to the PCS
-- claims' chain. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the two calls `KeccakCalls` and their random oracles,
-- `|Digest| = 2^256`; and VCVio's lazy random oracle.
import E2ECompleteness.Chain
import PcsQuotient.Reduction

/-!
# The reduction's challenges in the random-oracle model (the PCS claims)

The reduction's Fiat–Shamir chain (`PcsQuotient.Transcript`, `transcript.rs`) draws its challenges
as Keccak-256 answers: after the witness table's commitment (its root's two scalars and its
out-of-domain answer), `s₁ = H(s₀ ‖ w)` (`128` bytes), `s₂ = H(s₁)`, `s₃ = H(s₂)` (`32` bytes each),
the challenges `α, β, γ` their low `192` bits (`challengeOf`); after the three parts' commitments,
`s₄ = H(s₃ ‖ h ‖ q ‖ g)` (`320` bytes), `t`; after the four values and `next`,
`s₅ = H(s₄ ‖ a ‖ next)` (`192` bytes), `ρ`. In the two-call random-oracle model these answers are
uniform as long as the queries are fresh, and they are fresh **by their lengths**: everything hashed
before them has another length (`Good4`; between `t` and `ρ`, `GoodC`). `γ` is not needed: the
degenerate challenges do not involve it, so its query may repeat `β`'s.

**`prEvent_staged4_le`**: for a computation of this shape (`staged4 A B C D`), from a cache with no
input of the chain's lengths, the quadruple `(α, β, t, ρ)` lies in a set `Bad` with probability at
most `|Bad| / 2^768`, for any challenge map whose fibres have at most `2^64` digests (`Regular`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open PcsQuotient PcsQuotient.Transcript
open E2ECompleteness (ro Cache HashOK hashOK_callKeccak256 cache_of_hashOK prEvent_fresh
  prEvent_final_le Regular digestBytes_injective length_digestBytes simulateQ_callKeccak256
  card_digest_ennreal two_pow_256_ne_zero two_pow_256_ne_top)
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness.Pcs

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Lengths -/

theorem length_scalarBytes (x : E) : (scalarBytes x).length = 32 := by
  simp [scalarBytes, beBytes, wordBytes]

theorem length_flatMap_scalarBytes (l : List E) : (l.flatMap scalarBytes).length = 32 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, length_scalarBytes, List.length_cons]
    ring

/-- The parts' three commitments, as the stream carries them. -/
abbrev Scalars9 : Type := CommitmentScalars × CommitmentScalars × CommitmentScalars

/-- The `α` query: the state, then the witness commitment's three scalars. -/
def in3 (s : Digest) (w : CommitmentScalars) : Bytes := digestBytes s ++ w.stream.flatMap scalarBytes

/-- The `t` query: the state, then the parts' nine scalars. -/
def in9 (s : Digest) (x : Scalars9) : Bytes :=
  digestBytes s ++ (x.1.stream ++ x.2.1.stream ++ x.2.2.stream).flatMap scalarBytes

/-- The `ρ` query: the state, then the four values and `next`. -/
def in5 (s : Digest) (v : Vector E 4 × E) : Bytes :=
  digestBytes s ++ (v.1.toList ++ [v.2]).flatMap scalarBytes

theorem length_in3 (s : Digest) (w : CommitmentScalars) : (in3 s w).length = 128 := by
  rw [in3, List.length_append, length_digestBytes, length_flatMap_scalarBytes]
  simp only [CommitmentScalars.stream, List.length_cons, List.length_nil]

theorem length_in9 (s : Digest) (x : Scalars9) : (in9 s x).length = 320 := by
  rw [in9, List.length_append, length_digestBytes, length_flatMap_scalarBytes]
  simp only [CommitmentScalars.stream, List.length_append, List.length_cons, List.length_nil]

theorem length_in5 (s : Digest) (v : Vector E 4 × E) : (in5 s v).length = 192 := by
  rw [in5, List.length_append, length_digestBytes, length_flatMap_scalarBytes, List.length_append,
    Vector.length_toList]
  rfl

/-- Before `α` and between `γ` and `t`: no input of the chain's lengths. -/
def Good4 (m : Bytes) : Prop :=
  m.length ≠ 32 ∧ m.length ≠ 128 ∧ m.length ≠ 320 ∧ m.length ≠ 192

/-- Between `t` and `ρ`: no input of `ρ`'s length. -/
def GoodC (m : Bytes) : Prop := m.length ≠ 192

theorem hashOK_callKeccakF1600 (P : Bytes → Prop) (s : KeccakState) :
    HashOK P (callKeccakF1600 s) :=
  (isQueryBound_query_iff (spec := KeccakCalls) (.inr s) () _ _).2 trivial

/-! ## The chain's shape -/

variable {α β γ δ : Type}

/-- **The chain's shape**: `A` up to the seeded state `s₀` and the witness commitment `w`;
`s₁ = H(s₀ ‖ w)`, `s₂ = H(s₁)`, `s₃ = H(s₂)`; `B` from the three states to the parts' commitments;
`s₄ = H(s₃ ‖ h ‖ q ‖ g)`; `C` to a state `s` and the values `v`; `s₅ = H(s ‖ v)`; `D` the rest. Its
output carries `(chal s₁, chal s₂, chal s₄, chal s₅)`, the `(α, β, t, ρ)` of `transcript.rs` when
`chal` is `challengeOf`. -/
def staged4 (chal : Digest → E) (A : OracleComp KeccakCalls (α × Digest × CommitmentScalars))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × Scalars9))
    (C : α → β → Digest → Digest → Digest → Digest →
      OracleComp KeccakCalls (γ × Digest × (Vector E 4 × E)))
    (D : α → β → γ → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls δ) :
    OracleComp KeccakCalls (δ × (E × E × E × E)) := do
  let x ← A
  let s₁ ← callKeccak256 (in3 x.2.1 x.2.2)
  let s₂ ← callKeccak256 (digestBytes s₁)
  let s₃ ← callKeccak256 (digestBytes s₂)
  let y ← B x.1 s₁ s₂ s₃
  let s₄ ← callKeccak256 (in9 s₃ y.2)
  let z ← C x.1 y.1 s₁ s₂ s₃ s₄
  let s₅ ← callKeccak256 (in5 z.2.1 z.2.2)
  let v ← D x.1 y.1 z.1 s₁ s₂ s₃ s₄ s₅
  return (v, (chal s₁, chal s₂, chal s₄, chal s₅))

theorem run_staged4 (chal : Digest → E) (A : OracleComp KeccakCalls (α × Digest × CommitmentScalars))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × Scalars9))
    (C : α → β → Digest → Digest → Digest → Digest →
      OracleComp KeccakCalls (γ × Digest × (Vector E 4 × E)))
    (D : α → β → γ → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls δ)
    (c₀ : Cache) :
    (simulateQ ro (staged4 chal A B C D)).run c₀ =
      (simulateQ ro A).run c₀ >>= fun p ↦
      (ro (.inl (in3 p.1.2.1 p.1.2.2))).run p.2 >>= fun q₁ ↦
      (ro (.inl (digestBytes q₁.1))).run q₁.2 >>= fun q₂ ↦
      (ro (.inl (digestBytes q₂.1))).run q₂.2 >>= fun q₃ ↦
      (simulateQ ro (B p.1.1 q₁.1 q₂.1 q₃.1)).run q₃.2 >>= fun y ↦
      (ro (.inl (in9 q₃.1 y.1.2))).run y.2 >>= fun q₄ ↦
      (simulateQ ro (C p.1.1 y.1.1 q₁.1 q₂.1 q₃.1 q₄.1)).run q₄.2 >>= fun z ↦
      (ro (.inl (in5 z.1.2.1 z.1.2.2))).run z.2 >>= fun q₅ ↦
      (simulateQ ro (D p.1.1 y.1.1 z.1.1 q₁.1 q₂.1 q₃.1 q₄.1 q₅.1)).run q₅.2 >>= fun v ↦
      pure ((v.1, (chal q₁.1, chal q₂.1, chal q₄.1, chal q₅.1)), v.2) := by
  simp only [staged4, simulateQ_bind, simulateQ_pure, simulateQ_callKeccak256, StateT.run_bind,
    StateT.run_pure]
  rfl

/-! ## The bound -/

section Bound

variable (chal : Digest → E) (Bad : Finset (E × E × E × E))

/-- The answers `s₅` that put `(chal s₁, chal s₂, chal s₄, chal s₅)` in `Bad`. -/
noncomputable def slice4 (s₁ s₂ s₄ : Digest) : ℝ≥0∞ :=
  ((Finset.univ.filter fun s₅ : Digest ↦ (chal s₁, chal s₂, chal s₄, chal s₅) ∈ Bad).card : ℝ≥0∞)

/-- The `ρ` query, fresh: the event is the slice's fraction. -/
theorem bound_ρ (s₁ s₂ s₄ : Digest) (x : Bytes) (c : Cache) (hc : c (.inl x) = none)
    (K : Digest → Cache → ProbComp (δ × Cache)) :
    Pr{let z ← ((ro (.inl x)).run c >>= fun q₅ ↦ (K q₅.1 q₅.2 >>= fun v ↦
        pure ((v.1, (chal s₁, chal s₂, chal s₄, chal q₅.1)), v.2)))}[z.1.2 ∈ Bad] ≤
      slice4 chal Bad s₁ s₂ s₄ / 2 ^ 256 := by
  rw [prEvent_fresh _ _ hc]
  refine ENNReal.div_le_div_right ?_ _
  calc ∑ u : Digest, Pr{let z ← (K u (c.cacheQuery (.inl x) u) >>= fun w ↦
          pure ((w.1, (chal s₁, chal s₂, chal s₄, chal u)), w.2))}[z.1.2 ∈ Bad]
      ≤ ∑ u : Digest, (if (chal s₁, chal s₂, chal s₄, chal u) ∈ Bad then 1 else 0) :=
        Finset.sum_le_sum fun u _ ↦ prEvent_final_le _ _ (· ∈ Bad)
    _ = slice4 chal Bad s₁ s₂ s₄ := by
        rw [Finset.sum_boole]
        rfl

/-- A fresh query, then anything bounded by `g` of its answer: the average of `g`. -/
theorem bound_fresh {ε : Type} (x : Bytes) (c : Cache) (hc : c (.inl x) = none)
    (K : Digest × Cache → ProbComp ((ε × (E × E × E × E)) × Cache)) (g : Digest → ℝ≥0∞)
    (hK : ∀ u, Pr{let z ← K (u, c.cacheQuery (.inl x) u)}[z.1.2 ∈ Bad] ≤ g u) :
    Pr{let z ← ((ro (.inl x)).run c >>= K)}[z.1.2 ∈ Bad] ≤ (∑ u, g u) / 2 ^ 256 := by
  rw [prEvent_fresh _ _ hc]
  exact ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hK u) _

end Bound

/-! ## Counting -/

theorem card_quads_le (chal : Digest → E) (hreg : Regular chal) (Bad : Finset (E × E × E × E)) :
    (Finset.univ.filter fun x : Digest × Digest × Digest × Digest ↦
      (chal x.1, chal x.2.1, chal x.2.2.1, chal x.2.2.2) ∈ Bad).card ≤ 2 ^ 256 * Bad.card := by
  classical
  set S := Finset.univ.filter fun x : Digest × Digest × Digest × Digest ↦
    (chal x.1, chal x.2.1, chal x.2.2.1, chal x.2.2.2) ∈ Bad
  let f : Digest × Digest × Digest × Digest → E × E × E × E :=
    fun x ↦ (chal x.1, chal x.2.1, chal x.2.2.1, chal x.2.2.2)
  have himg : S.image f ⊆ Bad := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hx).2
  refine (Finset.card_le_mul_card_image S (2 ^ 256) fun e _ ↦ ?_).trans
    (Nat.mul_le_mul_left _ (Finset.card_le_card himg))
  have hsub : S.filter (fun x ↦ f x = e) ⊆
      (Finset.univ.filter fun d : Digest ↦ chal d = e.1) ×ˢ
        ((Finset.univ.filter fun d : Digest ↦ chal d = e.2.1) ×ˢ
          ((Finset.univ.filter fun d : Digest ↦ chal d = e.2.2.1) ×ˢ
            (Finset.univ.filter fun d : Digest ↦ chal d = e.2.2.2))) := by
    intro x hx
    have hfx := (Finset.mem_filter.mp hx).2
    simp only [f, Prod.ext_iff] at hfx
    simp [hfx.1, hfx.2.1, hfx.2.2.1, hfx.2.2.2]
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Finset.card_product, Finset.card_product]
  calc _ ≤ 2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64)) :=
        Nat.mul_le_mul (hreg _) (Nat.mul_le_mul (hreg _) (Nat.mul_le_mul (hreg _) (hreg _)))
    _ = 2 ^ 256 := by norm_num

theorem sum_slice4_le (chal : Digest → E) (hreg : Regular chal) (Bad : Finset (E × E × E × E)) :
    (∑ s₁ : Digest, ∑ s₂ : Digest, ∑ s₄ : Digest, slice4 chal Bad s₁ s₂ s₄) ≤
      2 ^ 256 * (Bad.card : ℝ≥0∞) := by
  classical
  have hN : (∑ s₁ : Digest, ∑ s₂ : Digest, ∑ s₄ : Digest,
      (Finset.univ.filter fun s₅ : Digest ↦ (chal s₁, chal s₂, chal s₄, chal s₅) ∈ Bad).card) =
      (Finset.univ.filter fun x : Digest × Digest × Digest × Digest ↦
        (chal x.1, chal x.2.1, chal x.2.2.1, chal x.2.2.2) ∈ Bad).card := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s₁ _ ↦ ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s₂ _ ↦ ?_
    rw [Fintype.sum_prod_type]
  have h := card_quads_le chal hreg Bad
  rw [← hN] at h
  unfold slice4
  exact_mod_cast h

/-! ## The bound on the chain's challenges -/

theorem ne_of_length_ne {x y : Bytes} (h : x.length ≠ y.length) : x ≠ y := fun e ↦ h (e ▸ rfl)

/-- **The reduction's challenges in the random-oracle model.** For a computation of the chain's
shape (`staged4`) whose stages before `α` and between `γ` and `t` hash only inputs of other lengths
than the chain's (`HashOK Good4`), and whose stage between `t` and `ρ` hashes nothing of `ρ`'s length
(`HashOK GoodC`), run from a cache holding no input of the chain's lengths, with a regular challenge
map: the quadruple `(α, β, t, ρ)` lies in `Bad` with probability at most `|Bad| / 2^768`. -/
theorem prEvent_staged4_le (chal : Digest → E) (hreg : Regular chal) (Bad : Finset (E × E × E × E))
    (A : OracleComp KeccakCalls (α × Digest × CommitmentScalars))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × Scalars9))
    (C : α → β → Digest → Digest → Digest → Digest →
      OracleComp KeccakCalls (γ × Digest × (Vector E 4 × E)))
    (D : α → β → γ → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls δ)
    (hA : HashOK Good4 A) (hB : ∀ a s₁ s₂ s₃, HashOK Good4 (B a s₁ s₂ s₃))
    (hC : ∀ a b s₁ s₂ s₃ s₄, HashOK GoodC (C a b s₁ s₂ s₃ s₄)) (c₀ : Cache)
    (hc₀ : ∀ m, c₀ (.inl m) ≠ none → Good4 m) :
    Pr{let z ← (simulateQ ro (staged4 chal A B C D)).run c₀}[z.1.2 ∈ Bad] ≤
      (Bad.card : ℝ≥0∞) / 2 ^ 768 := by
  have hfin : (∑ s₁ : Digest, ∑ s₂ : Digest, ∑ s₄ : Digest, slice4 chal Bad s₁ s₂ s₄) /
      2 ^ 256 / 2 ^ 256 / 2 ^ 256 / 2 ^ 256 ≤ (Bad.card : ℝ≥0∞) / 2 ^ 768 := by
    have e : (Bad.card : ℝ≥0∞) / 2 ^ 768 * 2 ^ 256 * 2 ^ 256 * 2 ^ 256 * 2 ^ 256 =
        2 ^ 256 * (Bad.card : ℝ≥0∞) := by
      rw [mul_assoc, mul_assoc, mul_assoc, ← pow_add, ← pow_add, ← pow_add,
        show (2 : ℝ≥0∞) ^ (256 + (256 + (256 + 256))) = 2 ^ 768 * 2 ^ 256 by rw [← pow_add],
        ← mul_assoc, ENNReal.div_mul_cancel (by simp) (by simp), mul_comm]
    refine ENNReal.div_le_of_le_mul (ENNReal.div_le_of_le_mul (ENNReal.div_le_of_le_mul
      (ENNReal.div_le_of_le_mul ?_)))
    rw [e]
    exact sum_slice4_le chal hreg Bad
  refine le_trans ?_ hfin
  rw [run_staged4]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp ↦ ?_
  -- After `A`: only `Good4` inputs.
  have hc₁ : ∀ m, p.2 (.inl m) ≠ none → Good4 m := fun m hm ↦
    (cache_of_hashOK hA c₀ hp m hm).elim (hc₀ m) id
  have f₁ : p.2 (.inl (in3 p.1.2.1 p.1.2.2)) = none := by
    by_contra h
    exact (hc₁ _ h).2.1 (length_in3 _ _)
  -- The `α` query.
  rw [show ((∑ s₁ : Digest, ∑ s₂ : Digest, ∑ s₄ : Digest, slice4 chal Bad s₁ s₂ s₄) / 2 ^ 256 /
      2 ^ 256 / 2 ^ 256 / 2 ^ 256) = (∑ s₁ : Digest, (∑ s₂ : Digest, ∑ s₄ : Digest,
        slice4 chal Bad s₁ s₂ s₄) / 2 ^ 256 / 2 ^ 256 / 2 ^ 256) / 2 ^ 256 by
    rw [ENNReal.sum_div, ENNReal.sum_div, ENNReal.sum_div]]
  refine bound_fresh Bad _ p.2 f₁ _ _ fun s₁ ↦ ?_
  set c₂ := p.2.cacheQuery (.inl (in3 p.1.2.1 p.1.2.2)) s₁ with hc₂
  -- After `α`: `Good4` inputs and the `128`-byte `α` input.
  have hc₂' : ∀ m, c₂ (.inl m) ≠ none → Good4 m ∨ m.length = 128 := by
    intro m hm
    by_cases hx : m = in3 p.1.2.1 p.1.2.2
    · exact Or.inr (hx ▸ length_in3 _ _)
    · rw [hc₂, QueryCache.cacheQuery_of_ne _ _ (Sum.inl_injective.ne hx)] at hm
      exact Or.inl (hc₁ m hm)
  have f₂ : c₂ (.inl (digestBytes s₁)) = none := by
    by_contra h
    rcases hc₂' _ h with h' | h'
    · exact h'.1 (length_digestBytes _)
    · rw [length_digestBytes] at h'; omega
  -- The `β` query.
  rw [show ((∑ s₂ : Digest, ∑ s₄ : Digest, slice4 chal Bad s₁ s₂ s₄) / 2 ^ 256 / 2 ^ 256 /
      2 ^ 256) = (∑ s₂ : Digest, (∑ s₄ : Digest, slice4 chal Bad s₁ s₂ s₄) / 2 ^ 256 / 2 ^ 256) /
        2 ^ 256 by
    rw [ENNReal.sum_div, ENNReal.sum_div]]
  refine bound_fresh Bad _ c₂ f₂ _ _ fun s₂ ↦ ?_
  set c₃ := c₂.cacheQuery (.inl (digestBytes s₁)) s₂ with hc₃
  -- After `β`: nothing of `320` or `192` bytes.
  have hc₃' : ∀ m, c₃ (.inl m) ≠ none → m.length ≠ 320 ∧ m.length ≠ 192 := by
    intro m hm
    by_cases hx : m = digestBytes s₁
    · rw [hx, length_digestBytes]; omega
    · rw [hc₃, QueryCache.cacheQuery_of_ne _ _ (Sum.inl_injective.ne hx)] at hm
      rcases hc₂' m hm with h' | h'
      · exact ⟨h'.2.2.1, h'.2.2.2⟩
      · omega
  -- The `γ` query: any answer.
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun q₃ hq₃ ↦ ?_
  have hc₄ : ∀ m, q₃.2 (.inl m) ≠ none → m.length ≠ 320 ∧ m.length ≠ 192 := by
    intro m hm
    rcases E2ECompleteness.mem_support_ro_run hq₃ with e | ⟨v, e⟩
    · rw [e] at hm; exact hc₃' m hm
    · rw [e] at hm
      by_cases hx : m = digestBytes s₂
      · rw [hx, length_digestBytes]; omega
      · rw [QueryCache.cacheQuery_of_ne _ _ (Sum.inl_injective.ne hx)] at hm
        exact hc₃' m hm
  -- Stage `B`.
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun y hy ↦ ?_
  have hc₅ : ∀ m, y.2 (.inl m) ≠ none → m.length ≠ 320 ∧ m.length ≠ 192 := fun m hm ↦
    (cache_of_hashOK (hB _ _ _ _) _ hy m hm).elim (hc₄ m) fun h ↦ ⟨h.2.2.1, h.2.2.2⟩
  have f₅ : y.2 (.inl (in9 q₃.1 y.1.2)) = none := by
    by_contra h
    exact (hc₅ _ h).1 (length_in9 _ _)
  -- The `t` query.
  rw [show ((∑ s₄ : Digest, slice4 chal Bad s₁ s₂ s₄) / 2 ^ 256 / 2 ^ 256) =
      (∑ s₄ : Digest, slice4 chal Bad s₁ s₂ s₄ / 2 ^ 256) / 2 ^ 256 by
    rw [ENNReal.sum_div]]
  refine bound_fresh Bad _ y.2 f₅ _ _ fun s₄ ↦ ?_
  set c₆ := y.2.cacheQuery (.inl (in9 q₃.1 y.1.2)) s₄ with hc₆
  have hc₆' : ∀ m, c₆ (.inl m) ≠ none → m.length ≠ 192 := by
    intro m hm
    by_cases hx : m = in9 q₃.1 y.1.2
    · rw [hx, length_in9]; omega
    · rw [hc₆, QueryCache.cacheQuery_of_ne _ _ (Sum.inl_injective.ne hx)] at hm
      exact (hc₅ m hm).2
  -- Stage `C`.
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz ↦ ?_
  have hc₇ : ∀ m, z.2 (.inl m) ≠ none → m.length ≠ 192 := fun m hm ↦
    (cache_of_hashOK (hC _ _ _ _ _ _) _ hz m hm).elim (hc₆' m) id
  have f₇ : z.2 (.inl (in5 z.1.2.1 z.1.2.2)) = none := by
    by_contra h
    exact hc₇ _ h (length_in5 _ _)
  -- The `ρ` query.
  exact bound_ρ chal Bad s₁ s₂ s₄ _ z.2 f₇
    (fun s₅ c ↦ (simulateQ ro (D p.1.1 y.1.1 z.1.1 s₁ s₂ q₃.1 s₄ s₅)).run c)

end E2ECompleteness.Pcs
