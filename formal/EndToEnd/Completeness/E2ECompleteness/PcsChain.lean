-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/Chain.lean` (the previous protocol's three challenges) to the deployed chain
-- (`pcs-quotient-kc3`). Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the two calls `KeccakCalls` and their random oracles, `|Digest| = 2^256`; and
-- VCVio's lazy random oracle.
import E2ECompleteness.Chain
import PcsQuotient.Reduction

/-!
# The reduction's challenges in the random-oracle model

The reduction's Fiat–Shamir chain (`PcsQuotient.Transcript`, `transcript.rs`) draws its challenges as Keccak-256
answers: after the witness table's commitment (its root's two scalars and its out-of-domain answer),
`s₁ = H(s₀ ‖ w)` (`128` bytes), `s₂ = H(s₁)`, `s₃ = H(s₂)` (`32` bytes each), the challenges `α, β, μ` their low
`192` bits (`challengeOf`); after the quotient table's commitment, `s₄ = H(s₃ ‖ T)` (`128` bytes), `t`; after the
three values and `next`, `s₅ = H(s₄ ‖ v ‖ next)` (`160` bytes), `ρ`. In the two-call random-oracle model these
answers are uniform as long as the queries are fresh. They are fresh by their lengths (everything hashed before them
has another length: `Good4`; between `t` and `ρ`, `GoodC`), but for two: `s₂`'s input repeats `s₁`'s only if
`s₂ = s₁`, and `t`'s input (of `α`'s length) repeats `α`'s only if `s₃ = s₀`; each happens with probability
`2^-256`. `μ` is not needed: the degenerate challenges do not involve it.

**`prEvent_staged4_le`**: for a computation of this shape (`staged4 A B C D`), from a cache with no input of the
chain's lengths, the quadruple `(α, β, t, ρ)` lies in a set `Bad` with probability at most
`|Bad| / 2^768 + 2 / 2^256`, for any challenge map whose fibres have at most `2^64` digests (`Regular`).
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

/-- The `α` and `t` queries: a state, then a commitment's three scalars. -/
def in3 (s : Digest) (w : CommitmentScalars) : Bytes := digestBytes s ++ w.stream.flatMap scalarBytes

/-- The `ρ` query: the state, then the three values and `next`. -/
def in4 (s : Digest) (v : Vector E 3 × E) : Bytes :=
  digestBytes s ++ (v.1.toList ++ [v.2]).flatMap scalarBytes

theorem length_in3 (s : Digest) (w : CommitmentScalars) : (in3 s w).length = 128 := by
  rw [in3, List.length_append, length_digestBytes, length_flatMap_scalarBytes]
  simp only [CommitmentScalars.stream, List.length_cons, List.length_nil]

theorem length_in4 (s : Digest) (v : Vector E 3 × E) : (in4 s v).length = 160 := by
  rw [in4, List.length_append, length_digestBytes, length_flatMap_scalarBytes, List.length_append,
    Vector.length_toList]
  rfl

theorem in3_state {s s' : Digest} {w w' : CommitmentScalars} (h : in3 s w = in3 s' w') : s = s' := by
  have h32 := congrArg (List.take 32) h
  simp only [in3, List.take_left' (length_digestBytes _)] at h32
  exact digestBytes_injective h32

/-- Before `α` and between `μ` and `t`: no input of the chain's lengths. -/
def Good4 (m : Bytes) : Prop := m.length ≠ 32 ∧ m.length ≠ 128 ∧ m.length ≠ 160

/-- Between `t` and `ρ`: no input of `ρ`'s length. -/
def GoodC (m : Bytes) : Prop := m.length ≠ 160

theorem hashOK_callKeccakF1600 (P : Bytes → Prop) (s : KeccakState) :
    HashOK P (callKeccakF1600 s) :=
  (isQueryBound_query_iff (spec := KeccakCalls) (.inr s) () _ _).2 trivial

/-! ## The chain's shape -/

variable {α β γ δ : Type}

/-- **The chain's shape**: `A` up to the seeded state `s₀` and the witness commitment `w`;
`s₁ = H(s₀ ‖ w)`, `s₂ = H(s₁)`, `s₃ = H(s₂)`; `B` from the three states to the quotient table's commitment;
`s₄ = H(s₃ ‖ T)`; `C` to a state `s` and the values `v`; `s₅ = H(s ‖ v)`; `D` the rest. Its output carries
`(chal s₁, chal s₂, chal s₄, chal s₅)`, the `(α, β, t, ρ)` of `transcript.rs` when `chal` is `challengeOf`. -/
def staged4 (chal : Digest → E) (A : OracleComp KeccakCalls (α × Digest × CommitmentScalars))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × CommitmentScalars))
    (C : α → β → Digest → Digest → Digest → Digest →
      OracleComp KeccakCalls (γ × Digest × (Vector E 3 × E)))
    (D : α → β → γ → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls δ) :
    OracleComp KeccakCalls (δ × (E × E × E × E)) := do
  let x ← A
  let s₁ ← callKeccak256 (in3 x.2.1 x.2.2)
  let s₂ ← callKeccak256 (digestBytes s₁)
  let s₃ ← callKeccak256 (digestBytes s₂)
  let y ← B x.1 s₁ s₂ s₃
  let s₄ ← callKeccak256 (in3 s₃ y.2)
  let z ← C x.1 y.1 s₁ s₂ s₃ s₄
  let s₅ ← callKeccak256 (in4 z.2.1 z.2.2)
  let v ← D x.1 y.1 z.1 s₁ s₂ s₃ s₄ s₅
  return (v, (chal s₁, chal s₂, chal s₄, chal s₅))

theorem run_staged4 (chal : Digest → E) (A : OracleComp KeccakCalls (α × Digest × CommitmentScalars))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × CommitmentScalars))
    (C : α → β → Digest → Digest → Digest → Digest →
      OracleComp KeccakCalls (γ × Digest × (Vector E 3 × E)))
    (D : α → β → γ → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls δ)
    (c₀ : Cache) :
    (simulateQ ro (staged4 chal A B C D)).run c₀ =
      (simulateQ ro A).run c₀ >>= fun p ↦
      (ro (.inl (in3 p.1.2.1 p.1.2.2))).run p.2 >>= fun q₁ ↦
      (ro (.inl (digestBytes q₁.1))).run q₁.2 >>= fun q₂ ↦
      (ro (.inl (digestBytes q₂.1))).run q₂.2 >>= fun q₃ ↦
      (simulateQ ro (B p.1.1 q₁.1 q₂.1 q₃.1)).run q₃.2 >>= fun y ↦
      (ro (.inl (in3 q₃.1 y.1.2))).run y.2 >>= fun q₄ ↦
      (simulateQ ro (C p.1.1 y.1.1 q₁.1 q₂.1 q₃.1 q₄.1)).run q₄.2 >>= fun z ↦
      (ro (.inl (in4 z.1.2.1 z.1.2.2))).run z.2 >>= fun q₅ ↦
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

/-! ## Averages -/

theorem card_univ_digest : (Finset.univ : Finset Digest).card = 2 ^ 256 := by
  rw [Finset.card_univ, LeanVM.Protocol.Compile.Rom.card_digest]

theorem two_pow_mul_div (c : ℝ≥0∞) : 2 ^ 256 * c / 2 ^ 256 = c := by
  rw [mul_comm]
  exact ENNReal.mul_div_cancel_right two_pow_256_ne_zero two_pow_256_ne_top

/-- The average of `f` plus a constant. -/
theorem avg_add_const (f : Digest → ℝ≥0∞) (c : ℝ≥0∞) :
    (∑ u, (f u + c)) / 2 ^ 256 = (∑ u, f u) / 2 ^ 256 + c := by
  rw [Finset.sum_add_distrib, Finset.sum_const, card_univ_digest, nsmul_eq_mul, ENNReal.add_div]
  congr 1
  rw [Nat.cast_pow, Nat.cast_ofNat, two_pow_mul_div]

/-- The average of `f` with one point weighed `1` more. -/
theorem avg_ite_add (a : Digest) (f : Digest → ℝ≥0∞) :
    (∑ u, ((if u = a then 1 else 0) + f u)) / 2 ^ 256 = 1 / 2 ^ 256 + (∑ u, f u) / 2 ^ 256 := by
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ a, if_pos (Finset.mem_univ _), ENNReal.add_div]

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

/-- **The reduction's challenges in the random-oracle model.** For a computation of the chain's shape
(`staged4`) whose stages before `α` and between `μ` and `t` hash only inputs of other lengths than the chain's
(`HashOK Good4`), and whose stage between `t` and `ρ` hashes nothing of `ρ`'s length (`HashOK GoodC`), run from a
cache holding no input of the chain's lengths, with a regular challenge map: the quadruple `(α, β, t, ρ)` lies in
`Bad` with probability at most `|Bad| / 2^768 + 2 / 2^256`. -/
theorem prEvent_staged4_le (chal : Digest → E) (hreg : Regular chal) (Bad : Finset (E × E × E × E))
    (A : OracleComp KeccakCalls (α × Digest × CommitmentScalars))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × CommitmentScalars))
    (C : α → β → Digest → Digest → Digest → Digest →
      OracleComp KeccakCalls (γ × Digest × (Vector E 3 × E)))
    (D : α → β → γ → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls δ)
    (hA : HashOK Good4 A) (hB : ∀ a s₁ s₂ s₃, HashOK Good4 (B a s₁ s₂ s₃))
    (hC : ∀ a b s₁ s₂ s₃ s₄, HashOK GoodC (C a b s₁ s₂ s₃ s₄)) (c₀ : Cache)
    (hc₀ : ∀ m, c₀ (.inl m) ≠ none → Good4 m) :
    Pr{let z ← (simulateQ ro (staged4 chal A B C D)).run c₀}[z.1.2 ∈ Bad] ≤
      (Bad.card : ℝ≥0∞) / 2 ^ 768 + 2 / 2 ^ 256 := by
  -- `S(s₁, s₂) = Σ_{s₄} slice / 2^512`, the bound after `μ`.
  set Bs : Digest → Digest → ℝ≥0∞ := fun s₁ s₂ ↦
    (∑ s₄ : Digest, slice4 chal Bad s₁ s₂ s₄) / 2 ^ 256 / 2 ^ 256 with hBs
  have hfin : (∑ s₁ : Digest, ∑ s₂ : Digest, Bs s₁ s₂) / 2 ^ 256 / 2 ^ 256 ≤
      (Bad.card : ℝ≥0∞) / 2 ^ 768 := by
    have e : (∑ s₁ : Digest, ∑ s₂ : Digest, Bs s₁ s₂) / 2 ^ 256 / 2 ^ 256 =
        (∑ s₁ : Digest, ∑ s₂ : Digest, ∑ s₄ : Digest, slice4 chal Bad s₁ s₂ s₄) /
          2 ^ 256 / 2 ^ 256 / 2 ^ 256 / 2 ^ 256 := by
      simp only [hBs, ← ENNReal.sum_div]
    rw [e]
    have e2 : (Bad.card : ℝ≥0∞) / 2 ^ 768 * 2 ^ 256 * 2 ^ 256 * 2 ^ 256 * 2 ^ 256 =
        2 ^ 256 * (Bad.card : ℝ≥0∞) := by
      rw [mul_assoc, mul_assoc, mul_assoc, ← pow_add, ← pow_add, ← pow_add,
        show (2 : ℝ≥0∞) ^ (256 + (256 + (256 + 256))) = 2 ^ 768 * 2 ^ 256 by rw [← pow_add],
        ← mul_assoc, ENNReal.div_mul_cancel (by simp) (by simp), mul_comm]
    refine ENNReal.div_le_of_le_mul (ENNReal.div_le_of_le_mul (ENNReal.div_le_of_le_mul
      (ENNReal.div_le_of_le_mul ?_)))
    rw [e2]
    exact sum_slice4_le chal hreg Bad
  have htot : (∑ s₁ : Digest, ((∑ s₂ : Digest, Bs s₁ s₂) / 2 ^ 256 + 2 / 2 ^ 256)) / 2 ^ 256 ≤
      (Bad.card : ℝ≥0∞) / 2 ^ 768 + 2 / 2 ^ 256 := by
    rw [avg_add_const]
    refine add_le_add ?_ le_rfl
    rw [← ENNReal.sum_div]
    exact hfin
  refine le_trans ?_ htot
  rw [run_staged4]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp ↦ ?_
  -- After `A`: only `Good4` inputs.
  have hc₁ : ∀ m, p.2 (.inl m) ≠ none → Good4 m := fun m hm ↦
    (cache_of_hashOK hA c₀ hp m hm).elim (hc₀ m) id
  have f₁ : p.2 (.inl (in3 p.1.2.1 p.1.2.2)) = none := by
    by_contra h
    exact (hc₁ _ h).2.1 (length_in3 _ _)
  -- The `α` query.
  refine bound_fresh Bad _ p.2 f₁ _ _ fun s₁ ↦ ?_
  set c₂ := p.2.cacheQuery (.inl (in3 p.1.2.1 p.1.2.2)) s₁ with hc₂
  -- After `α`: `Good4` inputs and the `α` input.
  have hc₂' : ∀ m, c₂ (.inl m) ≠ none → Good4 m ∨ m = in3 p.1.2.1 p.1.2.2 := by
    intro m hm
    by_cases hx : m = in3 p.1.2.1 p.1.2.2
    · exact Or.inr hx
    · rw [hc₂, QueryCache.cacheQuery_of_ne _ _ (Sum.inl_injective.ne hx)] at hm
      exact Or.inl (hc₁ m hm)
  have f₂ : c₂ (.inl (digestBytes s₁)) = none := by
    by_contra h
    rcases hc₂' _ h with h' | h'
    · exact h'.1 (length_digestBytes _)
    · have := congrArg List.length h'
      rw [length_digestBytes, length_in3] at this; omega
  -- The `β` query: a repeated `μ` input (`s₂ = s₁`) charged `1`.
  have hβ : (∑ s₂ : Digest, Bs s₁ s₂) / 2 ^ 256 + 2 / 2 ^ 256 =
      (∑ s₂ : Digest, ((if s₂ = s₁ then 1 else 0) + (Bs s₁ s₂ + 1 / 2 ^ 256))) / 2 ^ 256 := by
    rw [avg_ite_add, avg_add_const]
    have h2 : (2 : ℝ≥0∞) / 2 ^ 256 = 1 / 2 ^ 256 + 1 / 2 ^ 256 := by
      rw [← ENNReal.add_div]; norm_num
    rw [h2]
    ring
  rw [hβ]
  refine bound_fresh Bad _ c₂ f₂ _ _ fun s₂ ↦ ?_
  by_cases hs₂ : s₂ = s₁
  · rw [if_pos hs₂]
    exact (prEvent_le_one _).trans le_self_add
  rw [if_neg hs₂, zero_add]
  set c₃ := c₂.cacheQuery (.inl (digestBytes s₁)) s₂ with hc₃
  -- After `β`: `Good4` inputs, the `α` input, and `s₁`'s bytes.
  have hc₃' : ∀ m, c₃ (.inl m) ≠ none →
      Good4 m ∨ m = in3 p.1.2.1 p.1.2.2 ∨ m = digestBytes s₁ := by
    intro m hm
    by_cases hx : m = digestBytes s₁
    · exact Or.inr (Or.inr hx)
    · rw [hc₃, QueryCache.cacheQuery_of_ne _ _ (Sum.inl_injective.ne hx)] at hm
      rcases hc₂' m hm with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have f₃ : c₃ (.inl (digestBytes s₂)) = none := by
    by_contra h
    rcases hc₃' _ h with h' | h' | h'
    · exact h'.1 (length_digestBytes _)
    · have := congrArg List.length h'
      rw [length_digestBytes, length_in3] at this; omega
    · exact hs₂ (digestBytes_injective h')
  -- The `μ` query: an answer `s₃ = s₀` (which would repeat `α`'s input at `t`) charged `1`.
  have hμ : Bs s₁ s₂ + 1 / 2 ^ 256 =
      (∑ s₃ : Digest, ((if s₃ = p.1.2.1 then 1 else 0) + Bs s₁ s₂)) / 2 ^ 256 := by
    rw [avg_ite_add, Finset.sum_const, card_univ_digest, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
      two_pow_mul_div, add_comm]
  rw [hμ]
  refine bound_fresh Bad _ c₃ f₃ _ _ fun s₃ ↦ ?_
  by_cases hs₃ : s₃ = p.1.2.1
  · rw [if_pos hs₃]
    exact (prEvent_le_one _).trans le_self_add
  rw [if_neg hs₃, zero_add]
  set c₄ := c₃.cacheQuery (.inl (digestBytes s₂)) s₃ with hc₄
  have hc₄' : ∀ m, c₄ (.inl m) ≠ none → Good4 m ∨ m = in3 p.1.2.1 p.1.2.2 ∨ m.length = 32 := by
    intro m hm
    by_cases hx : m = digestBytes s₂
    · exact Or.inr (Or.inr (hx ▸ length_digestBytes _))
    · rw [hc₄, QueryCache.cacheQuery_of_ne _ _ (Sum.inl_injective.ne hx)] at hm
      rcases hc₃' m hm with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (h ▸ length_digestBytes _))
  -- Stage `B`.
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun y hy ↦ ?_
  have hc₅ : ∀ m, y.2 (.inl m) ≠ none → Good4 m ∨ m = in3 p.1.2.1 p.1.2.2 ∨ m.length = 32 :=
    fun m hm ↦ (cache_of_hashOK (hB _ _ _ _) _ hy m hm).elim (hc₄' m) Or.inl
  have f₅ : y.2 (.inl (in3 s₃ y.1.2)) = none := by
    by_contra h
    rcases hc₅ _ h with h' | h' | h'
    · exact h'.2.1 (length_in3 _ _)
    · exact hs₃ (in3_state h')
    · rw [length_in3] at h'; omega
  -- The `t` query.
  simp only [hBs]
  rw [ENNReal.sum_div]
  refine bound_fresh Bad _ y.2 f₅ _ _ fun s₄ ↦ ?_
  set c₆ := y.2.cacheQuery (.inl (in3 s₃ y.1.2)) s₄ with hc₆
  have hc₆' : ∀ m, c₆ (.inl m) ≠ none → m.length ≠ 160 := by
    intro m hm
    by_cases hx : m = in3 s₃ y.1.2
    · rw [hx, length_in3]; omega
    · rw [hc₆, QueryCache.cacheQuery_of_ne _ _ (Sum.inl_injective.ne hx)] at hm
      rcases hc₅ m hm with h | h | h
      · exact h.2.2
      · rw [h, length_in3]; omega
      · omega
  -- Stage `C`.
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz ↦ ?_
  have hc₇ : ∀ m, z.2 (.inl m) ≠ none → m.length ≠ 160 := fun m hm ↦
    (cache_of_hashOK (hC _ _ _ _ _ _) _ hz m hm).elim (hc₆' m) id
  have f₇ : z.2 (.inl (in4 z.1.2.1 z.1.2.2)) = none := by
    by_contra h
    exact hc₇ _ h (length_in4 _ _)
  -- The `ρ` query.
  exact bound_ρ chal Bad s₁ s₂ s₄ _ z.2 f₇
    (fun s₅ c ↦ (simulateQ ro (D p.1.1 y.1.1 z.1.1 s₁ s₂ s₃ s₄ s₅)).run c)

end E2ECompleteness.Pcs
