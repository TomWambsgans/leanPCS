-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the two calls `KeccakCalls` (Keccak-256 and Keccak-f[1600]) and their
-- random oracles, `|Digest| = 2^256`; and VCVio's lazy random oracle.
import LeanVM.Protocol.WithHash
import LeanVM.Protocol.Compile.Rom.Encoding
import PcsQuotient.Transcript
import Common.Lanes

/-!
# Keccak-256 as a random oracle

The lazily sampled oracle `ro` with its cache, hashes of good inputs (`HashOK`, `Good`, `hashOK_callKeccak256`),
the cache's invariants (`cache_of_hashOK`, `ro_run_fresh`, `ro_run_cached`), digests' bytes
(`digestBytes_injective`) and the fresh answer's probability (`prEvent_fresh`, `prEvent_final_le`,
`card_triples_le`).

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-- The two calls' lazy random oracles. -/
noncomputable abbrev ro : QueryImpl KeccakCalls (StateT KeccakCalls.QueryCache ProbComp) :=
  KeccakCalls.randomOracle

/-- The cache of the two calls. -/
abbrev Cache : Type := KeccakCalls.QueryCache

/-! ## Hash queries of a computation -/

/-- A query is allowed when it is a permutation call, or a hash of an input satisfying `P`. -/
def hashOK (P : Bytes → Prop) : (Bytes ⊕ KeccakState) → Unit → Prop
  | .inl x, _ => P x
  | .inr _, _ => True

/-- **Every hash query of `oa` satisfies `P`**, along every path. -/
def HashOK (P : Bytes → Prop) {α : Type} (oa : OracleComp KeccakCalls α) : Prop :=
  oa.IsQueryBound () (hashOK P) (fun _ _ ↦ ())

theorem HashOK.pure (P : Bytes → Prop) {α : Type} (a : α) :
    HashOK P (pure a : OracleComp KeccakCalls α) := trivial

theorem HashOK.bind {P : Bytes → Prop} {α β : Type} {oa : OracleComp KeccakCalls α}
    {f : α → OracleComp KeccakCalls β} (h₁ : HashOK P oa) (h₂ : ∀ a, HashOK P (f a)) :
    HashOK P (oa >>= f) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using h₂ a
  | query_bind t k ih =>
    rw [bind_assoc]
    exact (isQueryBound_query_bind_iff _ _ _ _ _).2
      ⟨((isQueryBound_query_bind_iff _ _ _ _ _).1 h₁).1,
        fun u ↦ ih u (((isQueryBound_query_bind_iff _ _ _ _ _).1 h₁).2 u)⟩

theorem HashOK.map {P : Bytes → Prop} {α β : Type} {oa : OracleComp KeccakCalls α} (f : α → β)
    (h : HashOK P oa) : HashOK P (f <$> oa) :=
  (isQueryBound_map_iff oa f _ _ _).2 h

theorem hashOK_callKeccak256 {P : Bytes → Prop} {x : Bytes} (hx : P x) :
    HashOK P (callKeccak256 x) :=
  (isQueryBound_query_iff (spec := KeccakCalls) (.inl x) () _ _).2 hx

theorem hashOK_callKeccakF1600 (P : Bytes → Prop) (s : KeccakState) :
    HashOK P (callKeccakF1600 s) :=
  (isQueryBound_query_iff (spec := KeccakCalls) (.inr s) () _ _).2 trivial

/-! ## What a run adds to the cache -/

theorem mem_support_ro_run {t : Bytes ⊕ KeccakState} {c : Cache} {z}
    (hz : z ∈ support ((ro t).run c)) :
    z.2 = c ∨ ∃ v, z.2 = c.cacheQuery t v := by
  rw [randomOracle.run_eq] at hz
  rcases h : c t with _ | v
  · simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact Or.inr ⟨w, rfl⟩
  · simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl

/-- **A run hashes only what it queries**: after a run of a computation whose hash queries satisfy
`P`, every hash input the cache answers was answered before or satisfies `P`. -/
theorem cache_of_hashOK {P : Bytes → Prop} {α : Type} {oa : OracleComp KeccakCalls α}
    (h : HashOK P oa) (c : Cache) {z : α × Cache} (hz : z ∈ support ((simulateQ ro oa).run c))
    (m : Bytes) (hm : z.2 (.inl m) ≠ none) : c (.inl m) ≠ none ∨ P m := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl hm
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 h
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self,
      OracleQuery.cont_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨⟨u, c₁⟩, hu', hz⟩ := hz
    rcases ih u (hk u) c₁ hz with h₁ | h₁
    · rcases mem_support_ro_run hu' with e | ⟨v, e⟩
      · exact Or.inl (e ▸ h₁)
      · simp only at e
        subst e
        by_cases htm : (Sum.inl m : Bytes ⊕ KeccakState) = t
        · subst htm
          exact Or.inr ht
        · rw [QueryCache.cacheQuery_of_ne _ _ htm] at h₁
          exact Or.inl h₁
    · exact Or.inr h₁

/-! ## Lengths -/

/-- The chain's challenge queries hash `32` or `96` bytes; everything else has another length. -/
def Good (m : Bytes) : Prop := m.length ≠ 32 ∧ m.length ≠ 96

theorem length_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  have : digestBytes d = LeanVM.Rpm.lanesBytes d.toList := rfl
  rw [this, LeanVM.Rpm.length_lanesBytes]
  simp

theorem digestBytes_injective : Function.Injective digestBytes := by
  intro d d' h
  have e : ∀ x : Digest, digestBytes x = LeanVM.Rpm.lanesBytes x.toList := fun _ ↦ rfl
  rw [e, e] at h
  apply Vector.toList_inj.mp
  apply List.ext_getElem (by simp)
  intro i hi hi'
  rw [← LeanVM.Rpm.leLane_lanesBytes _ i hi, ← LeanVM.Rpm.leLane_lanesBytes _ i hi', h]

/-! ## The chain's shape -/

variable {α β γ : Type}

theorem simulateQ_callKeccak256 (x : Bytes) :
    simulateQ ro (callKeccak256 x) = ro (.inl x) := by
  unfold callKeccak256
  exact simulateQ_spec_query _ _

/-! ## One query -/

theorem card_digest_ennreal : (Fintype.card Digest : ℝ≥0∞) = 2 ^ 256 := by
  rw [LeanVM.Protocol.Compile.Rom.card_digest]
  norm_num

theorem two_pow_256_ne_zero : (2 : ℝ≥0∞) ^ 256 ≠ 0 := by simp

theorem two_pow_256_ne_top : (2 : ℝ≥0∞) ^ 256 ≠ ⊤ := by simp

/-- A fresh hash query is answered uniformly. -/
theorem ro_run_fresh (x : Bytes) (c : Cache) (hc : c (.inl x) = none) :
    (ro (.inl x)).run c = ($ᵗ Digest) >>= fun u ↦ pure (u, c.cacheQuery (.inl x) u) := by
  rw [randomOracle.run_eq, hc]
  rfl

/-- A cached hash query is answered from the cache. -/
theorem ro_run_cached (x : Bytes) (c : Cache) {u : Digest} (hc : c (.inl x) = some u) :
    (ro (.inl x)).run c = pure (u, c) := by
  rw [randomOracle.run_eq, hc]

/-- **A fresh hash query**: the event after it is the average over the uniform answer. -/
theorem prEvent_fresh {δ : Type} (x : Bytes) (c : Cache) (hc : c (.inl x) = none)
    (f : Digest × Cache → ProbComp δ) (q : δ → Prop) :
    Pr{let z ← (ro (.inl x)).run c >>= f}[q z] =
      (∑ u : Digest, Pr{let z ← f (u, c.cacheQuery (.inl x) u)}[q z]) / 2 ^ 256 := by
  rw [ro_run_fresh x c hc, bind_assoc]
  simp only [pure_bind]
  rw [prEvent_bind_eq_sum_fintype]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, card_digest_ennreal]
  rw [← Finset.mul_sum, ENNReal.div_eq_inv_mul]

/-- The event on a value fixed before the last steps. -/
theorem prEvent_final_le {γ' δ : Type} (X : ProbComp (γ' × Cache)) (v : δ) (S : δ → Prop)
    [Decidable (S v)] :
    Pr{let z ← X >>= fun z ↦ pure ((z.1, v), z.2)}[S z.1.2] ≤ if S v then 1 else 0 := by
  split_ifs with h
  · exact prEvent_le_one _
  · refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_)
    rw [mem_support_bind_iff] at hz
    obtain ⟨w, -, hz⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact h

/-! ## Counting -/

/-- **A regular challenge map**: each challenge is the image of at most `2^64` digests (the low
192 bits of a 256-bit digest). -/
def Regular (chal : Digest → E) : Prop :=
  ∀ e : E, (Finset.univ.filter fun d : Digest ↦ chal d = e).card ≤ 2 ^ 64

theorem card_triples_le (chal : Digest → E) (hreg : Regular chal) (Bad : Finset (E × E × E)) :
    (Finset.univ.filter fun x : Digest × Digest × Digest ↦
      (chal x.1, chal x.2.1, chal x.2.2) ∈ Bad).card ≤ 2 ^ 192 * Bad.card := by
  classical
  set S := Finset.univ.filter fun x : Digest × Digest × Digest ↦
    (chal x.1, chal x.2.1, chal x.2.2) ∈ Bad
  let f : Digest × Digest × Digest → E × E × E := fun x ↦ (chal x.1, chal x.2.1, chal x.2.2)
  have himg : S.image f ⊆ Bad := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hx).2
  refine (Finset.card_le_mul_card_image S (2 ^ 192) fun e _ ↦ ?_).trans
    (Nat.mul_le_mul_left _ (Finset.card_le_card himg))
  have hsub : S.filter (fun x ↦ f x = e) ⊆
      (Finset.univ.filter fun d : Digest ↦ chal d = e.1) ×ˢ
        ((Finset.univ.filter fun d : Digest ↦ chal d = e.2.1) ×ˢ
          (Finset.univ.filter fun d : Digest ↦ chal d = e.2.2)) := by
    intro x hx
    have hfx := (Finset.mem_filter.mp hx).2
    simp only [f, Prod.ext_iff] at hfx
    simp [hfx.1, hfx.2.1, hfx.2.2]
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Finset.card_product]
  calc _ ≤ 2 ^ 64 * (2 ^ 64 * 2 ^ 64) :=
        Nat.mul_le_mul (hreg _) (Nat.mul_le_mul (hreg _) (hreg _))
    _ = 2 ^ 192 := by norm_num

end E2ECompleteness
