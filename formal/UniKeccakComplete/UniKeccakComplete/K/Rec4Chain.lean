-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `ProbTFresh.lean`'s chain calculus (`ChainF`,
-- `prHit_le`, `EndsT`, `WCh`, `WEnd`) for π1-rec4's five-digest reading, where every challenge's query is followed by
-- four tail queries; itself following `formal/EndToEnd/Completeness/E2ECompleteness/Chain.lean`; uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- `KeccakCalls`, their lazy random oracles, the weight calculus `Common.QueryCostAtMost`.
import UniKeccakComplete.K.Rec4ProbK
import UniKeccakComplete.K.ProbTFresh

/-!
# Chains of challenges with tails (`ChainX`)

In π1-rec4's five-digest reading a challenge's hash is five digest queries: the input `x` (its answer the next state),
then four tails `extIn i x` that do not depend on that answer. `ChainF`'s steps become `ChainX.step`: a query `x` on
the state, then any computation `T` that does not ask `x`, the chain going on from the answer and `T`'s output.

* **`prHitX_le`**: from a cache of at most `K` hashed inputs, a fresh query `x` and a chain of at most `n` challenges
  and `N` hashed inputs from its answer, an event `E` that implies a hashed input beginning with the final state's
  bytes holds with probability at most `(n + 1) · M / 2^256` (`K + N + 1 ≤ M`): `prHit_le`'s argument, a step's `T`
  moved before the step's answer by `run_frame` and `prEvent_swap_unif`;
* **`prHitX_top`**: the same when the fresh query is itself followed by such a `T`;
* **`EndsX`**: a chain that ends with an `80`-byte challenge, after which any computation that hashes no `80`-byte
  input can be moved into that last step;
* **`WChX`**, **`WEndX`**: the writer's chains and their combinators.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open UniStatement UniKeccak
open E2ECompleteness (ro Cache HashOK cache_of_hashOK prEvent_fresh ro_run_fresh simulateQ_callKeccak256
  length_digestBytes)
open UniKeccakComplete.Prob.TFresh (HC hq CacheBound cacheBound_run Hit take_digestBytes take_digestBytes'
  sum_hit_le run_frame prEvent_swap_unif)
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Rec4.TF4

open UniComplete

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Chains with tails -/

/-- **A chain of challenges from state `s`** (at most `n` challenges, `N` hashed inputs): its output `b` with
`Q b s`; or a challenge `x` on the state (beginning with its `32` bytes), then a computation `T` that never asks `x`
(at most `NT` hashed inputs), the chain going on from `x`'s answer. -/
inductive ChainX {γ : Type} (Q : γ → Digest → Prop) : ℕ → ℕ → Digest → OracleComp KeccakCalls γ → Prop
  | ret {n N : ℕ} {s : Digest} (b : γ) : Q b s → ChainX Q n N s (pure b)
  | step {n N n' N' NT : ℕ} {s : Digest} {δ : Type} (x : Bytes) (T : OracleComp KeccakCalls δ)
      (k : Digest → δ → OracleComp KeccakCalls γ) :
      x.take 32 = digestBytes s → HashOK (fun m ↦ m ≠ x) T → HC T NT → n + 1 ≤ n' → N + 1 + NT ≤ N' →
      (∀ u d, ChainX Q n N u (k u d)) → ChainX Q n' N' s (callKeccak256 x >>= fun u ↦ T >>= k u)

theorem ChainX.mono {γ : Type} {Q : γ → Digest → Prop} {n N n' N' : ℕ} {s : Digest}
    {X : OracleComp KeccakCalls γ} (h : ChainX Q n N s X) (hn : n ≤ n') (hN : N ≤ N') : ChainX Q n' N' s X := by
  cases h with
  | ret b hb => exact .ret b hb
  | step x T k hx hT hTc h1 h2 hk => exact .step x T k hx hT hTc (by omega) (by omega) hk

theorem ChainX.weakenQ {γ : Type} {Q Q' : γ → Digest → Prop} (hQ : ∀ b s, Q b s → Q' b s) {n N : ℕ}
    {s : Digest} {X : OracleComp KeccakCalls γ} (h : ChainX Q n N s X) : ChainX Q' n N s X := by
  induction h with
  | ret b hb => exact .ret b (hQ _ _ hb)
  | step x T k hx hT hTc h1 h2 _ ih => exact .step x T k hx hT hTc h1 h2 ih

/-- **Chains compose.** -/
theorem ChainX.bind {β γ : Type} {Q₁ : β → Digest → Prop} {Q₂ : γ → Digest → Prop} {n₂ N₂ : ℕ}
    {F : β → OracleComp KeccakCalls γ} (hF : ∀ b s, Q₁ b s → ChainX Q₂ n₂ N₂ s (F b)) {n₁ N₁ : ℕ}
    {s : Digest} {X : OracleComp KeccakCalls β} (h : ChainX Q₁ n₁ N₁ s X) :
    ChainX Q₂ (n₁ + n₂) (N₁ + N₂) s (X >>= F) := by
  induction h with
  | ret b hb =>
    rw [pure_bind]
    exact (hF b _ hb).mono (Nat.le_add_left _ _) (Nat.le_add_left _ _)
  | step x T k hx hT hTc h1 h2 _ ih =>
    simp only [bind_assoc]
    exact .step x T (fun u d ↦ k u d >>= F) hx hT hTc (by omega) (by omega) ih

/-! ## The bound on a chain -/

/-- **A chain hits its final state with probability at most `(n + 1) · M / 2^256`**: from a cache of at most `K`
hashed inputs, a fresh query `x` (its answer the chain's first state), then a chain of at most `n` challenges and `N`
hashed inputs from every answer, `K + N + 1 ≤ M`; the event `E` implies a hashed input beginning with the final
state's bytes (`Q` gives the final state, `pf`). -/
theorem prHitX_le {γ : Type} (Q : γ → Digest → Prop) (pf : γ → Digest) (hQ : ∀ z s, Q z s → pf z = s)
    (E : Cache → γ → Prop) (hE : ∀ c z, E c z → Hit c (pf z)) (Mb : ℕ)
    (n : ℕ) : ∀ (N K : ℕ) (x : Bytes) (Y : Digest → OracleComp KeccakCalls γ) (c : Cache),
      (∀ u, ChainX Q n N u (Y u)) → CacheBound c K → K + N + 1 ≤ Mb → c (.inl x) = none →
      Pr{let z ← (ro (.inl x)).run c >>= fun p ↦ (simulateQ ro (Y p.1)).run p.2}[E z.2 z.1] ≤
        ((n + 1 : ℕ) : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N K x Y c hY hc hM hx
  -- One continuation, from a cache with no hit at its state.
  have one : ∀ (u : Digest) (c₁ : Cache) (Y₀ : OracleComp KeccakCalls γ), ChainX Q n N u Y₀ →
      CacheBound c₁ (K + 1) → ¬ Hit c₁ u →
      Pr{let z ← (simulateQ ro Y₀).run c₁}[E z.2 z.1] ≤ (n : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
    intro u c₁ Y₀ h hc₁ hit
    cases h with
    | ret b hb =>
      rw [simulateQ_pure, StateT.run_pure]
      refine (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_)).trans (by simp)
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      intro hEz
      have h' := hE _ _ hEz
      rw [hQ _ _ hb] at h'
      exact hit h'
    | @step n₀ N₀ _ _ NT₀ _ δ₀ x' T k hx' hT hTc h1 h2 hk =>
      have hfresh : c₁ (.inl x') = none := by
        by_contra hne
        exact hit ⟨x', hne, hx'⟩
      have hframe : ∀ v, (simulateQ ro T).run (c₁.cacheQuery (.inl x') v) =
          (fun p ↦ (p.1, p.2.cacheQuery (.inl x') v)) <$> (simulateQ ro T).run c₁ :=
        fun v ↦ run_frame _ v T hT c₁
      rw [simulateQ_bind, simulateQ_callKeccak256, StateT.run_bind, ro_run_fresh _ _ hfresh]
      simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind, hframe, bind_map_left]
      rw [prEvent_swap_unif]
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun q hq ↦ ?_
      have hq' : q.2 (.inl x') = none := by
        by_contra hne
        rcases cache_of_hashOK hT c₁ hq _ hne with h' | h'
        · exact h' hfresh
        · exact h' rfl
      have e := ih n₀ (by omega) N₀ (K + 1 + NT₀) x' (fun v ↦ k v q.1) q.2 (fun v ↦ hk v q.1)
        (cacheBound_run hTc hc₁ hq) (by omega) hq'
      rw [ro_run_fresh _ _ hq'] at e
      simp only [bind_assoc, pure_bind] at e
      refine e.trans ?_
      exact mul_le_mul' (by exact_mod_cast h1) le_rfl
  obtain ⟨L, hL, hLc⟩ := hc
  have hc₁ : ∀ u, CacheBound (c.cacheQuery (.inl x) u) (K + 1) :=
    fun u ↦ CacheBound.cacheQuery_inl ⟨L, hL, hLc⟩ x u
  have hterm : ∀ u, Pr{let z ← (simulateQ ro (Y u)).run (c.cacheQuery (.inl x) u)}[E z.2 z.1] ≤
      (if Hit (c.cacheQuery (.inl x) u) u then 1 else 0) + (n : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
    intro u
    by_cases hit : Hit (c.cacheQuery (.inl x) u) u
    · simp only [hit, ↓reduceIte]
      exact (prEvent_le_one _).trans le_self_add
    · simp only [hit, ↓reduceIte, zero_add]
      exact one u _ (Y u) (hY u) (hc₁ u) hit
  have hsum : (∑ u : Digest, if Hit (c.cacheQuery (.inl x) u) u then (1 : ℝ≥0∞) else 0) ≤
      ((K + 1 : ℕ) : ℝ≥0∞) := by
    refine (sum_hit_le (insert x L) (fun u ↦ Hit (c.cacheQuery (.inl x) u) u) fun u hu ↦ ?_).trans ?_
    · obtain ⟨m, hm, hmu⟩ := hu
      refine ⟨m, ?_, hmu⟩
      by_cases hmx : m = x
      · rw [hmx]
        exact Finset.mem_insert_self _ _
      · rw [QueryCache.cacheQuery_of_ne _ _ (fun h ↦ hmx (Sum.inl_injective h))] at hm
        exact Finset.mem_insert_of_mem (hLc m hm)
    · exact_mod_cast (Finset.card_insert_le _ _).trans (by omega)
  rw [prEvent_fresh _ _ hx]
  calc (∑ u : Digest, Pr{let z ← (simulateQ ro (Y u)).run (c.cacheQuery (.inl x) u)}[E z.2 z.1]) / 2 ^ 256
      ≤ (∑ u : Digest, ((if Hit (c.cacheQuery (.inl x) u) u then 1 else 0) +
          (n : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256))) / 2 ^ 256 :=
        ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hterm u) _
    _ = (∑ u : Digest, if Hit (c.cacheQuery (.inl x) u) u then (1 : ℝ≥0∞) else 0) / 2 ^ 256 +
          (n : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
        rw [Finset.sum_add_distrib, ENNReal.add_div, UniKeccakComplete.Prob.sum_const_div]
    _ ≤ (Mb : ℝ≥0∞) / 2 ^ 256 + (n : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
        refine add_le_add (ENNReal.div_le_div_right (hsum.trans ?_) _) le_rfl
        exact_mod_cast (show K + 1 ≤ Mb by omega)
    _ = ((n + 1 : ℕ) : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
        push_cast
        ring

/-- **The bound when the fresh query is followed by tails**: a fresh `x`, then `T` (never asking `x`, at most `NT`
hashed inputs), then a chain from `x`'s answer; `K + NT + N + 1 ≤ M`. -/
theorem prHitX_top {γ δ : Type} (Q : γ → Digest → Prop) (pf : γ → Digest) (hQ : ∀ z s, Q z s → pf z = s)
    (E : Cache → γ → Prop) (hE : ∀ c z, E c z → Hit c (pf z)) (Mb n N K NT : ℕ) (x : Bytes)
    (T : OracleComp KeccakCalls δ) (k : Digest → δ → OracleComp KeccakCalls γ) (c : Cache)
    (hT : HashOK (fun m ↦ m ≠ x) T) (hTc : HC T NT) (hk : ∀ u d, ChainX Q n N u (k u d)) (hc : CacheBound c K)
    (hM : K + NT + N + 1 ≤ Mb) (hx : c (.inl x) = none) :
    Pr{let z ← (simulateQ ro (callKeccak256 x >>= fun u ↦ T >>= k u)).run c}[E z.2 z.1] ≤
      ((n + 1 : ℕ) : ℝ≥0∞) * ((Mb : ℝ≥0∞) / 2 ^ 256) := by
  classical
  have hframe : ∀ v, (simulateQ ro T).run (c.cacheQuery (.inl x) v) =
      (fun p ↦ (p.1, p.2.cacheQuery (.inl x) v)) <$> (simulateQ ro T).run c :=
    fun v ↦ run_frame _ v T hT c
  rw [simulateQ_bind, simulateQ_callKeccak256, StateT.run_bind, ro_run_fresh _ _ hx]
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind, hframe, bind_map_left]
  rw [prEvent_swap_unif]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun q hq ↦ ?_
  have hq' : q.2 (.inl x) = none := by
    by_contra hne
    rcases cache_of_hashOK hT c hq _ hne with h' | h'
    · exact h' hx
    · exact h' rfl
  have e := prHitX_le Q pf hQ E hE Mb n N (K + NT) x (fun v ↦ k v q.1) q.2 (fun v ↦ hk v q.1)
    (cacheBound_run hTc hc hq) (by omega) hq'
  rw [ro_run_fresh _ _ hq'] at e
  simp only [bind_assoc, pure_bind] at e
  exact e

/-! ## Chains that end with an `80`-byte challenge -/

/-- **`X` ends with an `80`-byte challenge**: from state `s`, followed by any computation `T` that hashes no `80`-byte
input (at most `NT`) and then any chain `G` from `X`'s final state (`P`), it is a chain. -/
def EndsX {β : Type} (P : β → Digest → Prop) (n N : ℕ) (s : Digest) (X : OracleComp KeccakCalls β) : Prop :=
  ∀ (δ γ : Type) (T : OracleComp KeccakCalls δ) (NT : ℕ) (G : β → δ → OracleComp KeccakCalls γ)
    (Q : γ → Digest → Prop) (n' N' : ℕ), HashOK (fun m ↦ m.length ≠ 80) T → HC T NT →
    (∀ b s' d, P b s' → ChainX Q n' N' s' (G b d)) →
    ChainX Q (n + n') (N + NT + N') s (X >>= fun b ↦ T >>= G b)

theorem EndsX.mono {β : Type} {P P' : β → Digest → Prop} {n N n' N' : ℕ} {s : Digest}
    {X : OracleComp KeccakCalls β} (h : EndsX P n N s X) (hn : n ≤ n') (hN : N ≤ N')
    (hP : ∀ b s, P b s → P' b s) : EndsX P' n' N' s X := by
  intro δ γ T NT G Q n₀ N₀ hT hTc hG
  exact (h δ γ T NT G Q n₀ N₀ hT hTc fun b s d hb ↦ hG b s d (hP b s hb)).mono (by omega) (by omega)

/-- **The last challenge**: an `80`-byte input on the state, then tails `T₀` (never asking it, at most `N₀`), then the
output. -/
theorem endsX_last {β δ₀ : Type} {P : β → Digest → Prop} {s : Digest} (x : Bytes) (T₀ : OracleComp KeccakCalls δ₀)
    (N₀ : ℕ) (f : Digest → δ₀ → β) (hx : x.take 32 = digestBytes s) (hlen : x.length = 80)
    (hT₀ : HashOK (fun m ↦ m ≠ x) T₀) (hT₀c : HC T₀ N₀) (hf : ∀ u d, P (f u d) u) :
    EndsX P 1 (1 + N₀) s (callKeccak256 x >>= fun u ↦ T₀ >>= fun d ↦ pure (f u d)) := by
  intro δ γ T NT G Q n' N' hT hTc hG
  have e : ((callKeccak256 x >>= fun u ↦ T₀ >>= fun d ↦ pure (f u d)) >>= fun b ↦ T >>= G b) =
      (callKeccak256 x >>= fun u ↦ (T₀ >>= fun d ↦ T >>= fun t ↦ pure (d, t)) >>= fun dt ↦ G (f u dt.1) dt.2) := by
    simp only [bind_assoc, pure_bind]
  rw [e]
  refine .step (n := n') (N := N') (NT := N₀ + NT) x _ _ hx ?_ ?_ (by omega) (by omega) fun u dt ↦ hG _ _ _ (hf u dt.1)
  · refine E2ECompleteness.HashOK.bind hT₀ fun _ ↦ E2ECompleteness.HashOK.bind
      (UniKeccakComplete.Prob.HashOK.mono (fun m hm he ↦ hm (by rw [he]; exact hlen)) hT) fun _ ↦
      E2ECompleteness.HashOK.pure _ _
  · exact Common.QueryCostAtMost.bind hT₀c fun _ ↦ Common.QueryCostAtMost.bind (b := 0) hTc fun _ ↦ trivial

theorem endsX_bind {β β' : Type} {Q₁ : β → Digest → Prop} {P : β' → Digest → Prop} {n₁ N₁ n₂ N₂ : ℕ}
    {s : Digest} {X : OracleComp KeccakCalls β} {F : β → OracleComp KeccakCalls β'} (hX : ChainX Q₁ n₁ N₁ s X)
    (hF : ∀ b s', Q₁ b s' → EndsX P n₂ N₂ s' (F b)) : EndsX P (n₁ + n₂) (N₁ + N₂) s (X >>= F) := by
  intro δ γ T NT G Q n' N' hT hTc hG
  rw [bind_assoc]
  exact (ChainX.bind (fun b s' hb ↦ hF b s' hb δ γ T NT G Q n' N' hT hTc hG) hX).mono (by omega) (by omega)

theorem endsX_map {β β' : Type} {P : β → Digest → Prop} {P' : β' → Digest → Prop} {n N : ℕ} {s : Digest}
    {X : OracleComp KeccakCalls β} (g : β → β') (hX : EndsX P n N s X) (hg : ∀ b s', P b s' → P' (g b) s') :
    EndsX P' n N s (X >>= fun b ↦ pure (g b)) := by
  intro δ γ T NT G Q n' N' hT hTc hG
  simp only [bind_assoc, pure_bind]
  exact hX δ γ T NT (fun b d ↦ G (g b) d) Q n' N' hT hTc fun b s' d hb ↦ hG _ _ d (hg b s' hb)

/-! ## The writer's chains -/

/-- **A writer's chain** with tails. -/
def WChX {α : Type} (M : PM α) (n N : ℕ) (pre : Wr → Prop) (post : α → Wr → Prop) : Prop :=
  ∀ w, pre w → ChainX (fun p s ↦ p.2.state = s ∧ post p.1 p.2) n N w.state (M.run w)

/-- **A writer's chain that ends with an `80`-byte challenge.** -/
def WEndX {α : Type} (M : PM α) (n N : ℕ) (pre : Wr → Prop) (post : α → Wr → Prop) : Prop :=
  ∀ w, pre w → EndsX (fun p s ↦ p.2.state = s ∧ post p.1 p.2) n N w.state (M.run w)

section Writer

variable {α β : Type}

theorem WChX.mono {M : PM α} {n N n' N' : ℕ} {pre : Wr → Prop} {post post' : α → Wr → Prop}
    (h : WChX M n N pre post) (hn : n ≤ n') (hN : N ≤ N') (hp : ∀ a w, post a w → post' a w) :
    WChX M n' N' pre post' :=
  fun w hw ↦ ((h w hw).weakenQ fun _ _ hq ↦ ⟨hq.1, hp _ _ hq.2⟩).mono hn hN

theorem WChX.weaken {M : PM α} {n N : ℕ} {pre : Wr → Prop} {post : α → Wr → Prop}
    (h : WChX M n N (fun _ ↦ True) post) : WChX M n N pre post :=
  fun w _ ↦ h w trivial

theorem WChX.const_pre {M : PM α} {n N : ℕ} {P : Prop} {post : α → Wr → Prop}
    (h : P → WChX M n N (fun _ ↦ True) post) : WChX M n N (fun _ ↦ P) post :=
  fun w hw ↦ h hw w trivial

theorem WEndX.mono {M : PM α} {n N n' N' : ℕ} {pre : Wr → Prop} {post post' : α → Wr → Prop}
    (h : WEndX M n N pre post) (hn : n ≤ n') (hN : N ≤ N') (hp : ∀ a w, post a w → post' a w) :
    WEndX M n' N' pre post' :=
  fun w hw ↦ (h w hw).mono hn hN fun _ _ hq ↦ ⟨hq.1, hp _ _ hq.2⟩

theorem wchX_bind {M : PM α} {f : α → PM β} {n₁ N₁ n₂ N₂ : ℕ} {pre : Wr → Prop} {mid : α → Wr → Prop}
    {post : β → Wr → Prop} (hM : WChX M n₁ N₁ pre mid) (hf : ∀ a, WChX (f a) n₂ N₂ (mid a) post) :
    WChX (M >>= f) (n₁ + n₂) (N₁ + N₂) pre post := by
  intro w hw
  rw [StateT.run_bind]
  refine ChainX.bind (fun p s hp ↦ ?_) (hM w hw)
  rw [← hp.1]
  exact hf p.1 p.2 hp.2

theorem wchX_seq {M : PM α} {f : α → PM β} {n₁ N₁ n N : ℕ} {pre : Wr → Prop} {mid : α → Wr → Prop}
    {post : β → Wr → Prop} (hM : WChX M n₁ N₁ pre mid) (hf : ∀ a, WChX (f a) (n - n₁) (N - N₁) (mid a) post)
    (hn : n₁ ≤ n) (hN : N₁ ≤ N) : WChX (M >>= f) n N pre post :=
  (wchX_bind hM hf).mono (by omega) (by omega) fun _ _ h ↦ h

theorem wendX_bind {M : PM α} {f : α → PM β} {n₁ N₁ n₂ N₂ : ℕ} {pre : Wr → Prop} {mid : α → Wr → Prop}
    {post : β → Wr → Prop} (hM : WChX M n₁ N₁ pre mid) (hf : ∀ a, WEndX (f a) n₂ N₂ (mid a) post) :
    WEndX (M >>= f) (n₁ + n₂) (N₁ + N₂) pre post := by
  intro w hw
  rw [StateT.run_bind]
  refine endsX_bind (hM w hw) fun p s hp ↦ ?_
  rw [← hp.1]
  exact hf p.1 p.2 hp.2

theorem wendX_seq {M : PM α} {f : α → PM β} {n₁ N₁ n N : ℕ} {pre : Wr → Prop} {mid : α → Wr → Prop}
    {post : β → Wr → Prop} (hM : WChX M n₁ N₁ pre mid) (hf : ∀ a, WEndX (f a) (n - n₁) (N - N₁) (mid a) post)
    (hn : n₁ ≤ n) (hN : N₁ ≤ N) : WEndX (M >>= f) n N pre post :=
  (wendX_bind hM hf).mono (by omega) (by omega) fun _ _ h ↦ h

/-- **A writer's chain ending with an `80`-byte challenge, then a computation without queries.** -/
theorem wendX_then {M : PM α} {f : α → PM β} {n N : ℕ} {pre : Wr → Prop} {mid : α → Wr → Prop}
    {post : β → Wr → Prop} (hM : WEndX M n N pre mid) (g : α → Wr → β × Wr)
    (hf : ∀ a w, (f a).run w = pure (g a w)) (hg : ∀ a w, mid a w → (g a w).2.state = w.state ∧
      post (g a w).1 (g a w).2) : WEndX (M >>= f) n N pre post := by
  intro w hw
  rw [StateT.run_bind]
  have e : ((M.run w) >>= fun p ↦ (f p.1).run p.2) = (M.run w) >>= fun p ↦ pure (g p.1 p.2) := by
    simp only [hf]
  rw [e]
  refine (endsX_map (fun p ↦ g p.1 p.2) (hM w hw) ?_).mono le_rfl le_rfl fun _ _ h ↦ h
  intro p s hp
  obtain ⟨h1, h2⟩ := hg p.1 p.2 hp.2
  exact ⟨h1.trans hp.1, h2⟩

theorem wchX_ret (a : α) {n N : ℕ} {pre : Wr → Prop} {post : α → Wr → Prop} (h : ∀ w, pre w → post a w) :
    WChX (pure a : PM α) n N pre post := by
  intro w hw
  rw [StateT.run_pure]
  exact .ret _ ⟨rfl, h w hw⟩

theorem wchX_sendBytes (b : List UInt8) {pre : Wr → Prop} :
    WChX (sendBytes (m := OracleComp KeccakCalls) b) 0 0 pre
      (fun _ w' ↦ ∃ w, pre w ∧ w' = { w with stream := w.stream ++ b.toArray }) := by
  intro w hw
  have e : (sendBytes (m := OracleComp KeccakCalls) b).run w =
      pure (PUnit.unit, { w with stream := w.stream ++ b.toArray }) := by
    simp [sendBytes]
  rw [e]
  exact .ret _ ⟨rfl, w, hw, rfl⟩

end Writer

end UniKeccakComplete.Rec4.TF4

/-- info: 'UniKeccakComplete.Rec4.TF4.prHitX_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.TF4.prHitX_top
