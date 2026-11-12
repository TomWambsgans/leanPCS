-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Pi2Chain.lean`'s and `Pi2Prob.lean`'s bounds with the
-- freshness conditioned on a predicate off which the verdict rejects (moved from `Pi2AlphaG.lean`, π2v4: `ρ` added);
-- uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the
-- two calls `KeccakCalls`, their lazy random oracles, `rpmError`, `DuplexVm`, `hashBlocks`; VCVio's `support`.
import RecCompose.Pi2Chain

/-!
# π2's staged experiment, its freshness conditioned on the graph's acceptance (`Holds3`)

Stage A's `α` input need not be fresh off the graph's acceptance (π1's prover returning none, or a witness that is not
honest: `fixLen`'s zeros), where the verdict's first component (π1-rec4's graph's) is `false`. So:

* **`Pi2Staged.Holds3`**: the code-level bridge (the experiment as the staged run, its duplex discipline and cost),
  `α`'s length, `α`'s and `t`'s freshness on predicates `G` (stage A's output) and `Gβ` (stage B's), off which the
  rest of the run's verdict rejects (**`accA`**, **`accB`**), the bad sets' counts, **`ρ`'s bound** (`rhoBad`, π2v4)
  and the grinding at good challenges (`rejectGood`).
* **`prEvent_staged3_triple_leG`**, **`prEvent_tquery_leG`**: `α, β, γ` and `t`, conditioned.
* **`recCompleteness2_of_staged3`**: `RecCompleteness2 D P1 P2 (deltaStaged2 M ct N εα εt ερ εpow)` from `Holds3`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open E2ECompleteness (ro Cache HashOK cache_of_hashOK prEvent_fresh prEvent_final_le Regular length_digestBytes
  simulateQ_callKeccak256)
open UniKeccakComplete.Prob (GoodL prEvent_query_le sum_const_div sum_mem_le sum_bad_le)
open UniKeccakComplete.Prob.TFresh (HC hc_of_qc CacheBound cacheBound_empty cacheBound_run sum_hit_le take_digestBytes' run_frame)
open scoped ENNReal

set_option autoImplicit false

namespace RecCompose.Pi2P

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## `α, β, γ`, conditioned -/

set_option exponentiation.threshold 1024 in
/-- **`α, β, γ` in the random-oracle model, conditioned** (`prEvent_staged3_triple_le2` with `α`'s input fresh but on
`G`): off `G` no outcome of the rest is `Acc`; the event `Acc ∧ triple ∈ Bad` has probability at most
`εα + (2K + 1) / 2^256 + M / 2^192`. -/
theorem prEvent_staged3_triple_leG {α ρ γ : Type} (chal : Digest → E) (hreg : Regular chal) {L : ℕ} (hL : L ≠ 32)
    (Bad : ρ → Finset (E × E × E)) (M : ℕ) (hM : ∀ p, (Bad p).card ≤ M * 2 ^ 384)
    (inp : α → Bytes) (hinp : ∀ a, (inp a).length = L) (pr : α → ρ) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → Digest → OracleComp KeccakCalls γ) (G : α → Prop) (Acc : γ → Prop)
    (hacc : ∀ a, ¬ G a → ∀ (s₁ s₂ s₃ : Digest) (c : Cache) z,
      z ∈ support ((simulateQ ro (C a s₁ s₂ s₃)).run c) → ¬ Acc z.1)
    {KA K₀ : ℕ} (hA : HC A KA) (c₀ : Cache) (hc₀ : CacheBound c₀ K₀) (εα : ℝ≥0∞)
    (hα : Pr{let p ← (simulateQ ro A).run c₀}[p.2 (.inl (inp p.1)) ≠ none ∧ G p.1] ≤ εα) :
    Pr{let z ← (simulateQ ro (staged3 chal inp pr A C)).run c₀}[Acc z.1.1 ∧ z.1.2.2 ∈ Bad z.1.2.1] ≤
      εα + (((2 * (K₀ + KA) + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192) := by
  classical
  rw [run_staged3]
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun p ↦ p.2 (.inl (inp p.1)) ≠ none ∧ G p.1) _
    fun p hp hpα ↦ ?_).trans (add_le_add hα le_rfl)
  by_cases hG : G p.1
  swap
  · refine (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun w hw hev ↦ ?_)).trans zero_le
    rw [mem_support_bind_iff] at hw
    obtain ⟨q₁, -, hw⟩ := hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨q₂, -, hw⟩ := hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨q₃, -, hw⟩ := hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨z, hz, hw⟩ := hw
    rw [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact hacc p.1 hG _ _ _ _ z hz hev.1
  have hfα : p.2 (.inl (inp p.1)) = none := not_not.mp fun h ↦ hpα ⟨h, hG⟩
  refine (prEvent_mono _ _ (fun w ↦ w.1.2.2 ∈ Bad w.1.2.1) fun w hw ↦ hw.2).trans ?_
  have hcp : CacheBound p.2 (K₀ + KA) := cacheBound_run hA hc₀ hp
  set K := K₀ + KA with hK
  set c := p.2 with hc
  set T := Bad (pr p.1) with hT
  set I : Digest → Digest → Digest → ℝ≥0∞ := fun s₁ s₂ s₃ ↦ if (chal s₁, chal s₂, chal s₃) ∈ T then 1 else 0
    with hI
  have hne : ∀ s : Digest, (Sum.inl (digestBytes s) : Bytes ⊕ KeccakState) ≠ .inl (inp p.1) := fun s h ↦
    hL ((hinp p.1).symm.trans (by rw [← Sum.inl_injective h, length_digestBytes]))
  refine (prEvent_query_le _ _ False (fun _ ↦ hfα) _ _
    (fun s₁ ↦ (if c (.inl (digestBytes s₁)) ≠ none then 1 else 0) +
      (((K + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (∑ s₂ : Digest, ∑ s₃ : Digest, I s₁ s₂ s₃) / 2 ^ 256 / 2 ^ 256))
    fun s₁ ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    rw [Finset.sum_add_distrib, ENNReal.add_div, Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    have h1 : (∑ u : Digest, (if c (.inl (digestBytes u)) ≠ none then 1 else 0 : ℝ≥0∞)) / 2 ^ 256 ≤
        (K : ℝ≥0∞) / 2 ^ 256 := ENNReal.div_le_div_right (sum_cached_le hcp) _
    have h2 : (∑ s₁ : Digest, (∑ s₂ : Digest, ∑ s₃ : Digest, I s₁ s₂ s₃) / 2 ^ 256 / 2 ^ 256) / 2 ^ 256 ≤
        (M : ℝ≥0∞) / 2 ^ 192 := by
      rw [← ENNReal.sum_div, ← ENNReal.sum_div]
      refine ENNReal.div_le_of_le_mul (ENNReal.div_le_of_le_mul (ENNReal.div_le_of_le_mul ?_))
      have e : (M : ℝ≥0∞) / 2 ^ 192 * 2 ^ 256 * 2 ^ 256 * 2 ^ 256 = 2 ^ 192 * ((M : ℝ≥0∞) * 2 ^ 384) := by
        rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add,
          show (2 : ℝ≥0∞) ^ (256 + (256 + 256)) = 2 ^ 192 * (2 ^ 192 * 2 ^ 384) by rw [← pow_add, ← pow_add],
          ← mul_assoc, ENNReal.div_mul_cancel (by simp) (by simp)]
        ring
      rw [e]
      refine (sum_triples_le chal hreg T).trans ?_
      gcongr
      exact_mod_cast hM (pr p.1)
    calc _ ≤ (K : ℝ≥0∞) / 2 ^ 256 + (((K + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192) :=
          add_le_add h1 (add_le_add le_rfl h2)
      _ = _ := by
          rw [← add_assoc, ← ENNReal.add_div]
          congr 2
          push_cast
          ring
  refine (prEvent_query_le _ _ (c (.inl (digestBytes s₁)) ≠ none)
    (fun hs ↦ by rw [QueryCache.cacheQuery_of_ne _ _ (hne s₁)]; exact not_not.mp hs) _ _
    (fun s₂ ↦ (if s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none then 1 else 0) +
      (∑ s₃ : Digest, I s₁ s₂ s₃) / 2 ^ 256) fun s₂ ↦ ?_).trans ?_
  rotate_left
  · refine add_le_add le_rfl ?_
    rw [Finset.sum_add_distrib, ENNReal.add_div, ← ENNReal.sum_div]
    refine add_le_add (ENNReal.div_le_div_right ?_ _) le_rfl
    calc (∑ s₂ : Digest, (if s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none then 1 else 0 : ℝ≥0∞))
        ≤ ∑ s₂ : Digest, ((if s₂ ∈ [s₁] then 1 else 0) + (if c (.inl (digestBytes s₂)) ≠ none then 1 else 0)) :=
          Finset.sum_le_sum fun s₂ _ ↦ by
            simpa only [List.mem_singleton] using ite_or_le (s₂ = s₁) (c (.inl (digestBytes s₂)) ≠ none)
      _ ≤ (([s₁].length : ℕ) : ℝ≥0∞) + K := by
          rw [Finset.sum_add_distrib]
          exact add_le_add (sum_mem_le _) (sum_cached_le hcp)
      _ = ((K + 1 : ℕ) : ℝ≥0∞) := by simp only [List.length_singleton, Nat.cast_one]; push_cast; ring
  refine (prEvent_query_le _ _ (s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none) (fun hs ↦ ?_) _ _
    (fun s₃ ↦ I s₁ s₂ s₃) fun s₃ ↦ ?_).trans le_rfl
  · rw [not_or] at hs
    have h12 : (Sum.inl (digestBytes s₂) : Bytes ⊕ KeccakState) ≠ .inl (digestBytes s₁) := fun h ↦
      hs.1 (E2ECompleteness.digestBytes_injective (Sum.inl_injective h))
    rw [QueryCache.cacheQuery_of_ne _ _ h12, QueryCache.cacheQuery_of_ne _ _ (hne s₂)]
    exact not_not.mp hs.2
  exact prEvent_final_le _ (pr p.1, chal s₁, chal s₂, chal s₃) (fun v ↦ v.2 ∈ Bad v.1)

/-! ## `t`, conditioned -/

/-- **The point challenge `t`, conditioned** (`prEvent_tquery_le'` with `t`'s input fresh but on `Gx`): off `Gx` no
outcome of the rest makes the event; the event is at most `t`'s input cached on `Gx`, plus `ct / 2^192`. -/
theorem prEvent_tquery_leG {β γ ω τ : Type} (chal : Digest → E) (hreg : Regular chal) (badT : τ → E → Prop)
    (ct : ℕ) (hct : ∀ fp, ∃ T : Finset E, T.card ≤ ct ∧ ∀ b, badT fp b → b ∈ T)
    (X : OracleComp KeccakCalls β) (tin : β → Bytes) (pr : β → τ)
    (K : β → Digest → OracleComp KeccakCalls γ) (h : β → Digest → γ → ω) (ev : ω → Prop)
    (hev : ∀ x st z, ev (h x st z) → badT (pr x) (chal st)) (Gx : β → Prop)
    (hacc : ∀ x, ¬ Gx x → ∀ (st : Digest) (c : Cache) z, z ∈ support ((simulateQ ro (K x st)).run c) →
      ¬ ev (h x st z.1)) (c₀ : Cache) :
    Pr{let z ← (simulateQ ro (X >>= fun x ↦ callKeccak256 (tin x) >>= fun st ↦ K x st >>= fun z ↦
        pure (h x st z))).run c₀}[ev z.1] ≤
      Pr{let p ← (simulateQ ro X).run c₀}[p.2 (.inl (tin p.1)) ≠ none ∧ Gx p.1] + (ct : ℝ≥0∞) / 2 ^ 192 := by
  classical
  simp only [simulateQ_bind, simulateQ_callKeccak256, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  refine prEvent_bind_le_prEvent_add_of_support _ _ _ _ fun p _ hp ↦ ?_
  by_cases hG : Gx p.1
  swap
  · refine (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun w hw hw' ↦ ?_)).trans zero_le
    rw [mem_support_bind_iff] at hw
    obtain ⟨q, -, hw⟩ := hw
    rw [mem_support_bind_iff] at hw
    obtain ⟨z, hz, hw⟩ := hw
    rw [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact hacc p.1 hG _ _ z hz hw'
  have hfresh : p.2 (.inl (tin p.1)) = none := not_not.mp fun h' ↦ hp ⟨h', hG⟩
  rw [prEvent_fresh _ _ hfresh]
  refine le_trans (ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ ?_) _)
    (sum_bad_le chal hreg (badT (pr p.1)) ct (hct _))
  by_cases hb : badT (pr p.1) (chal u)
  · simp only [hb, ↓reduceIte]
    exact prEvent_le_one _
  · simp only [hb, ↓reduceIte]
    refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_)
    rw [mem_support_bind_iff] at hz
    obtain ⟨w, -, hz⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact fun he ↦ hb (hev _ _ _ he)

/-! ## The staged experiment, conditioned -/

/-- **The code-level bridge, conditioned**: `Holds2`'s fields, `α`'s and `t`'s freshness on `G` and `Gβ`, and off them
the verdict's first component is `false` (`accA`, `accB`). -/
structure Pi2Staged.Holds3 (S : Pi2Staged) (D : RecStatement.RecDeployment) (P1 : RecStatement.Pi1Prover D)
    (P2 : RecStatement.Pi2Prover) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows)
    (L : ℕ) (Bad : S.ρ → Finset (E × E × E)) (badT : S.τ → E → Prop) (badR : S.υ → E → Prop) (G : S.α → Prop)
    (Gβ : S.β → Prop) (M ct N : ℕ) (εα εt ερ εpow : ℝ≥0∞) : Prop where
  /-- (as `Holds2`) The experiment's event is at most the two-call run's against the random permutation. -/
  experiment : Pr{let v ← RecStatement.recCompletenessExperiment2 D P1 P2 input rows q}[v.1 = true ∧ v.2 = false] ≤
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation S.run).run' []}[z.1.1.1 = true ∧ z.1.1.2 = false]
  /-- (as `Holds2`) The duplex discipline. -/
  duplex : DuplexVm S.run []
  /-- (as `Holds2`) At most `N` block calls. -/
  cost : Common.QueryCostAtMost S.run hashBlocks N
  /-- (as `Holds2`) `α`'s input has `L ≠ 32` bytes. -/
  L_ne : L ≠ 32
  inp_length : ∀ a, (S.inp a).length = L
  /-- `α`'s input is already hashed after stage A, on `G`, with probability at most `εα`. -/
  alphaFresh : Pr{let p ← (simulateQ ro S.A).run ∅}[p.2 (.inl (S.inp p.1)) ≠ none ∧ G p.1] ≤ εα
  /-- Off `G` the rest of the run's verdict has the first component `false`. -/
  accA : ∀ a, ¬ G a → ∀ (s₁ s₂ s₃ : Digest) (c : Cache) z,
    z ∈ support ((simulateQ ro (S.tail a s₁ s₂ s₃)).run c) → z.1.1.1 = false
  /-- Off `Gβ` stage C's verdict has the first component `false`. -/
  accB : ∀ b, ¬ Gβ b → ∀ (st : Digest) (c : Cache) z, z ∈ support ((simulateQ ro (S.C b st)).run c) →
    z.1.1.1 = false
  /-- (as `Holds2`) The copy argument's bad triples' count. -/
  badCard : ∀ p, (Bad p).card ≤ M * 2 ^ 384
  /-- (as `Holds2`) At most `ct` bad values of `t` for each prior. -/
  badTCard : ∀ fp, ∃ T : Finset E, T.card ≤ ct ∧ ∀ t, badT fp t → t ∈ T
  /-- `t`'s input is already hashed before its query, on `Gβ`, with probability at most `εt`. -/
  tFresh : Pr{let p ← (simulateQ ro S.pre).run ∅}[p.2 (.inl (S.tin p.1.1)) ≠ none ∧ Gβ p.1.1] ≤ εt
  /-- `ρ` (π2v4): the graph accepting, `ρ` lands in its bad set with probability at most `ερ`. -/
  rhoBad : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ badR z.1.2.2.1 z.1.2.2.2] ≤ ερ
  /-- The grinding: at good challenges (the triple, `t`, `ρ`), the graph accepting, the contract rejects with
  probability at most `εpow`. -/
  rejectGood : Pr{let z ← (simulateQ ro S.run).run' ∅}[
    z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ Bad z.2.1 ∧ ¬ badT z.1.2.1.1 z.1.2.1.2 ∧
      ¬ badR z.1.2.2.1 z.1.2.2.2] ≤ εpow

/-- **One statement**, `Holds3`'s: the graph accepting and the contract rejecting has probability at most
`deltaStaged2`. -/
theorem prEvent_staged_bad_le3 (S : Pi2Staged) {D : RecStatement.RecDeployment} {P1 : RecStatement.Pi1Prover D}
    {P2 : RecStatement.Pi2Prover} {input : Vector UInt8 32} {rows : List ℕ} {q : D.pi1.Stack rows} {L : ℕ}
    {Bad : S.ρ → Finset (E × E × E)} {badT : S.τ → E → Prop} {badR : S.υ → E → Prop} {G : S.α → Prop}
    {Gβ : S.β → Prop} {M ct N : ℕ} {εα εt ερ εpow : ℝ≥0∞}
    (h : S.Holds3 D P1 P2 input rows q L Bad badT badR G Gβ M ct N εα εt ερ εpow) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation S.run).run' []}[z.1.1.1 = true ∧ z.1.1.2 = false] ≤
      deltaStaged2 M ct N εα εt ερ εpow := by
  refine E2ECompleteness.rpm_le_rom S.run h.duplex h.cost (fun z ↦ z.1.1.1 = true ∧ z.1.1.2 = false) ?_
  have hab : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ z.2.2 ∈ Bad z.2.1] ≤
      εα + (((2 * N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192) := by
    rw [StateT.run'_eq, prEvent_map]
    have := prEvent_staged3_triple_leG chalP E2ECompleteness.challengeOf_regular h.L_ne Bad M h.badCard S.inp
      h.inp_length S.pr S.A S.tail G (fun y ↦ y.1.1 = true)
      (fun a ha s₁ s₂ s₃ c z hz hz' ↦ Bool.false_ne_true ((h.accA a ha s₁ s₂ s₃ c z hz).symm.trans hz'))
      (S.hc_A h.cost) ∅ cacheBound_empty εα h.alphaFresh
    rw [zero_add] at this
    exact this
  have ht : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ badT z.1.2.1.1 z.1.2.1.2] ≤
      εt + (ct : ℝ≥0∞) / 2 ^ 192 := by
    rw [StateT.run'_eq, prEvent_map, S.run_eq_pre]
    refine (prEvent_tquery_leG chalP E2ECompleteness.challengeOf_regular badT ct h.badTCard S.pre
      (fun x ↦ S.tin x.1) (fun x ↦ S.prT x.1) (fun x st ↦ S.C x.1 st)
      (fun x st z ↦ ((z.1, (S.prT x.1, chalP st), z.2), x.2))
      (fun w ↦ w.1.1.1 = true ∧ badT w.1.2.1.1 w.1.2.1.2)
      (fun _ _ _ hw ↦ hw.2) (fun x ↦ Gβ x.1)
      (fun x hx st c z hz hz' ↦ Bool.false_ne_true ((h.accB x.1 hx st c z hz).symm.trans hz'.1)) ∅).trans ?_
    exact add_le_add h.tFresh le_rfl
  have hsplit : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ z.1.1.2 = false] ≤
      Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ z.2.2 ∈ Bad z.2.1] +
        (Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ badT z.1.2.1.1 z.1.2.1.2] +
          (Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ badR z.1.2.2.1 z.1.2.2.2] +
            Pr{let z ← (simulateQ ro S.run).run' ∅}[
              z.1.1.1 = true ∧ z.1.1.2 = false ∧ z.2.2 ∉ Bad z.2.1 ∧ ¬ badT z.1.2.1.1 z.1.2.1.2 ∧
                ¬ badR z.1.2.2.1 z.1.2.2.2])) := by
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _
      (fun z : S.Tail × (S.ρ × E × E × E) ↦ z.1.1.1 = true ∧ z.2.2 ∈ Bad z.2.1)).trans
        (add_le_add le_rfl ?_)
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _
      (fun z : S.Tail × (S.ρ × E × E × E) ↦ z.1.1.1 = true ∧ badT z.1.2.1.1 z.1.2.1.2)).trans
        (add_le_add le_rfl ?_)
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _
      (fun z : S.Tail × (S.ρ × E × E × E) ↦ z.1.1.1 = true ∧ badR z.1.2.2.1 z.1.2.2.2)).trans
        (add_le_add le_rfl ?_)
    exact prEvent_mono _ _ _ fun z hz ↦
      ⟨hz.1.1.1.1, hz.1.1.1.2, fun hb ↦ hz.1.1.2 ⟨hz.1.1.1.1, hb⟩, fun hb ↦ hz.1.2 ⟨hz.1.1.1.1, hb⟩,
        fun hb ↦ hz.2 ⟨hz.1.1.1.1, hb⟩⟩
  refine hsplit.trans ?_
  calc _ ≤ (εα + (((2 * N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192)) +
        ((εt + (ct : ℝ≥0∞) / 2 ^ 192) + (ερ + εpow)) :=
      add_le_add hab (add_le_add ht (add_le_add h.rhoBad h.rejectGood))
    _ = _ := by ac_rfl

/-- **`RecCompleteness2` from `Holds3`.** -/
theorem recCompleteness2_of_staged3 {D : RecStatement.RecDeployment} {P1 : RecStatement.Pi1Prover D}
    {P2 : RecStatement.Pi2Prover} {L M ct N : ℕ} {εα εt ερ εpow : ℝ≥0∞}
    (hS : ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
      D.pi1.HonestRelation D.flock rows input q → ∃ (S : Pi2Staged) (Bad : S.ρ → Finset (E × E × E))
        (badT : S.τ → E → Prop) (badR : S.υ → E → Prop) (G : S.α → Prop) (Gβ : S.β → Prop),
        S.Holds3 D P1 P2 input rows q L Bad badT badR G Gβ M ct N εα εt ερ εpow) :
    RecStatement.RecCompleteness2 D P1 P2 (deltaStaged2 M ct N εα εt ερ εpow) := by
  intro input rows q hfit hrel
  obtain ⟨S, Bad, badT, badR, G, Gβ, h⟩ := hS input rows q hfit hrel
  exact h.experiment.trans (prEvent_staged_bad_le3 S h)


end RecCompose.Pi2P

/-- info: 'RecCompose.Pi2P.prEvent_staged3_triple_leG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.prEvent_staged3_triple_leG

/-- info: 'RecCompose.Pi2P.recCompleteness2_of_staged3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.recCompleteness2_of_staged3
