-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Generalizes `Pi2Prob.lean`'s `prEvent_staged3_triple_le`
-- (itself following `formal/UniComplete/UniComplete/ProbChain.lean`), with `ProbTFresh.lean`'s counting of hashed
-- inputs (`HC`, `hc_of_qc`, `CacheBound`, `cacheBound_run`, `sum_hit_le`); uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- `KeccakCalls`, their lazy random oracles, `rpmError`, `DuplexVm`, `hashBlocks`, `Common.QueryCostAtMost.of_bind`.
import RecCompose.Pi2P1
import RecCompose.Pi2Prob
import Common.Rerun
import UniKeccakComplete.K.ProbTFresh

/-!
# π2's chain `α, β, γ` when stage A hashes `32`-byte inputs

Stage A (π2's experiment up to `α`'s query) runs π1-rec4's prover (`P1k`), which may hash `32`-byte inputs (a
challenge chained on the last answer). So `α`'s chain is bounded here by counting stage A's hashed inputs instead of
asking it to hash nothing of `32` bytes:

* **`prEvent_staged3_triple_le2`**: for a computation of the chain's shape (`staged3`) whose stage A makes at most
  `KA` Keccak-256 queries (`HC`), from a cache of at most `K₀` hashed inputs, the first input of length `L ≠ 32`, if
  `α`'s input is already cached after A with probability at most `εα`, the triple lands in a bad set of at most
  `M · |E|²` with probability at most `εα + (2K + 1) / 2^256 + M / 2^192`, `K = K₀ + KA`.
* **`deltaStaged2 M ct N εα εt ερ εpow = (εα + (2N + 1) / 2^256 + M / 2^192) + (εt + ct / 2^192) + ερ + εpow +
  rpmError N`**: the error `Pi2Holds3.recCompleteness2_of_staged3` gives (`ερ` `ρ`'s bad event, π2v4).
* **`delta2'`**, **`delta2'_le`**: π2v4's numbers (`M = 2^25`: the copy argument's `2N`; `ct = 10 · 2^24 + 1`: `t`'s);
  below `2^-164` at `N ≤ 2^50`, `εα, εt, ερ ≤ 2^-170`, `εpow ≤ 2^-300`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open E2ECompleteness (ro Cache HashOK cache_of_hashOK prEvent_fresh prEvent_final_le Regular length_digestBytes
  simulateQ_callKeccak256)
open UniKeccakComplete.Prob (GoodL prEvent_query_le sum_const_div sum_mem_le)
open UniKeccakComplete.Prob.TFresh (HC hc_of_qc CacheBound cacheBound_empty cacheBound_run sum_hit_le take_digestBytes')
open scoped ENNReal

set_option autoImplicit false

namespace RecCompose.Pi2P

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Counting -/

/-- **The digests whose bytes are a cached input**: at most the cache's count. -/
theorem sum_cached_le {c : Cache} {K : ℕ} (hc : CacheBound c K) :
    (∑ u : Digest, (if c (.inl (digestBytes u)) ≠ none then 1 else 0 : ℝ≥0∞)) ≤ K := by
  classical
  obtain ⟨L, hL, hm⟩ := hc
  refine (sum_hit_le L (fun u ↦ c (.inl (digestBytes u)) ≠ none) fun u hu ↦
    ⟨digestBytes u, hm _ hu, take_digestBytes' u⟩).trans ?_
  exact_mod_cast hL

theorem ite_or_le (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P ∨ Q then (1 : ℝ≥0∞) else 0) ≤ (if P then 1 else 0) + (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-! ## The chain -/

set_option exponentiation.threshold 1024 in
/-- **`α, β, γ` in the random-oracle model, stage A hashing anything** (`prEvent_staged3_triple_le` without
`HashOK (GoodL L)`): stage A of at most `KA` Keccak-256 queries, from a cache of at most `K₀` hashed inputs, `α`'s
input (`L ≠ 32` bytes) cached after A with probability at most `εα`; bad sets of at most `M · |E|²` triples. -/
theorem prEvent_staged3_triple_le2 {α ρ γ : Type} (chal : Digest → E) (hreg : Regular chal) {L : ℕ} (hL : L ≠ 32)
    (Bad : ρ → Finset (E × E × E)) (M : ℕ) (hM : ∀ p, (Bad p).card ≤ M * 2 ^ 384)
    (inp : α → Bytes) (hinp : ∀ a, (inp a).length = L) (pr : α → ρ) (A : OracleComp KeccakCalls α)
    (C : α → Digest → Digest → Digest → OracleComp KeccakCalls γ) {KA K₀ : ℕ} (hA : HC A KA) (c₀ : Cache)
    (hc₀ : CacheBound c₀ K₀) (εα : ℝ≥0∞)
    (hα : Pr{let p ← (simulateQ ro A).run c₀}[p.2 (.inl (inp p.1)) ≠ none] ≤ εα) :
    Pr{let z ← (simulateQ ro (staged3 chal inp pr A C)).run c₀}[z.1.2.2 ∈ Bad z.1.2.1] ≤
      εα + (((2 * (K₀ + KA) + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192) := by
  classical
  rw [run_staged3]
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun p ↦ p.2 (.inl (inp p.1)) ≠ none) _
    fun p hp hpα ↦ ?_).trans (add_le_add hα le_rfl)
  have hfα : p.2 (.inl (inp p.1)) = none := not_not.mp hpα
  have hcp : CacheBound p.2 (K₀ + KA) := cacheBound_run hA hc₀ hp
  set K := K₀ + KA with hK
  set c := p.2 with hc
  set T := Bad (pr p.1) with hT
  set I : Digest → Digest → Digest → ℝ≥0∞ := fun s₁ s₂ s₃ ↦ if (chal s₁, chal s₂, chal s₃) ∈ T then 1 else 0
    with hI
  -- a state's bytes are never `α`'s input
  have hne : ∀ s : Digest, (Sum.inl (digestBytes s) : Bytes ⊕ KeccakState) ≠ .inl (inp p.1) := fun s h ↦
    hL ((hinp p.1).symm.trans (by rw [← Sum.inl_injective h, length_digestBytes]))
  -- `s₁`: fresh.
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
  -- `s₂`: fresh unless `s₁`'s bytes were cached.
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
  -- `s₃`: fresh unless `s₂ = s₁` or `s₂`'s bytes were cached.
  refine (prEvent_query_le _ _ (s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none) (fun hs ↦ ?_) _ _
    (fun s₃ ↦ I s₁ s₂ s₃) fun s₃ ↦ ?_).trans le_rfl
  · rw [not_or] at hs
    have h12 : (Sum.inl (digestBytes s₂) : Bytes ⊕ KeccakState) ≠ .inl (digestBytes s₁) := fun h ↦
      hs.1 (E2ECompleteness.digestBytes_injective (Sum.inl_injective h))
    rw [QueryCache.cacheQuery_of_ne _ _ h12, QueryCache.cacheQuery_of_ne _ _ (hne s₂)]
    exact not_not.mp hs.2
  exact prEvent_final_le _ (pr p.1, chal s₁, chal s₂, chal s₃) (fun v ↦ v.2 ∈ Bad v.1)

/-! ## The staged experiment's error -/

/-- **π2's completeness error from the staged experiment's numbers** (π2v4): `α, β, γ` (`α`'s input fresh but with
probability `εα`, stage A's `N` hashed inputs, `M |E|²` bad triples), `t` (its input fresh but with probability `εt`,
`ct` bad values), `ρ` (`ερ`), the grinding `εpow`, the permutation's `rpmError N`. -/
noncomputable def deltaStaged2 (M ct N : ℕ) (εα εt ερ εpow : ℝ≥0∞) : ℝ≥0∞ :=
  (εα + (((2 * N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (M : ℝ≥0∞) / 2 ^ 192)) + (εt + (ct : ℝ≥0∞) / 2 ^ 192) + ερ + εpow +
    rpmError N

/-- **Stage A's Keccak-256 queries**: at most the run's block calls. -/
theorem Pi2Staged.hc_A (S : Pi2Staged) {N : ℕ} (h : Common.QueryCostAtMost S.run hashBlocks N) : HC S.A N := by
  unfold Pi2Staged.run staged3 at h
  exact hc_of_qc (Common.QueryCostAtMost.of_bind h)

/-! ## π2's numbers -/

/-- **π2's completeness error** (π2v4), `α`'s input fresh but with probability `εα`: the copy argument's `2^25 |E|²`
bad triples (`2N`), `t`'s `10 · 2^24 + 1` bad points (`10N + 1`), `ρ`'s error `ερ`. -/
noncomputable def delta2' (N : ℕ) (εα εt ερ εpow : ℝ≥0∞) : ℝ≥0∞ :=
  deltaStaged2 (2 ^ 25) (10 * 2 ^ 24 + 1) N εα εt ερ εpow

/-- **`δ2` in bits**: below `2^-164` at `N ≤ 2^50`, `εα, εt, ερ ≤ 2^-170`, `εpow ≤ 2^-300` (`t`'s `10 · 2^-168` and
the copy argument's `2^-167` dominate: about `2^-164.4`). -/
theorem delta2'_le {N : ℕ} {εα εt ερ εpow : ℝ≥0∞} (hN : N ≤ 2 ^ 50) (ha : εα ≤ (2 : ℝ≥0∞)⁻¹ ^ 170)
    (ht : εt ≤ (2 : ℝ≥0∞)⁻¹ ^ 170) (hr : ερ ≤ (2 : ℝ≥0∞)⁻¹ ^ 170) (hp : εpow ≤ (2 : ℝ≥0∞)⁻¹ ^ 300) :
    delta2' N εα εt ερ εpow ≤ (2 : ℝ≥0∞)⁻¹ ^ 164 := by
  set x : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ 170 with hx
  have hsmall : ∀ k, 170 ≤ k → (2 : ℝ≥0∞)⁻¹ ^ k ≤ x := fun k hk ↦ E2ECompleteness.inv_pow_le_inv_pow hk
  have ha' : ((2 * N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ x := by
    calc ((2 * N + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ((2 ^ 52 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (204 + 52) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          exact_mod_cast (show 2 * N + 1 ≤ 2 ^ 52 by omega)
      _ = (2 : ℝ≥0∞)⁻¹ ^ 204 := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
          exact E2ECompleteness.two_pow_mul_inv_pow 52 204
      _ ≤ x := hsmall 204 (by norm_num)
  have hb : ((2 ^ 25 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 2 ^ 3 * x := by
    refine le_of_eq ?_
    calc ((2 ^ 25 : ℕ) : ℝ≥0∞) / 2 ^ 192 = 2 ^ 25 * (2 : ℝ≥0∞)⁻¹ ^ (167 + 25) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          norm_num
      _ = (2 : ℝ≥0∞)⁻¹ ^ 167 := E2ECompleteness.two_pow_mul_inv_pow 25 167
      _ = 2 ^ 3 * x := (E2ECompleteness.two_pow_mul_inv_pow 3 167).symm
  have hc : ((10 * 2 ^ 24 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ 41 * x := by
    calc ((10 * 2 ^ 24 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 ≤ ((41 * 2 ^ 22 : ℕ) : ℝ≥0∞) / 2 ^ 192 :=
          ENNReal.div_le_div_right (Nat.cast_le.mpr (by norm_num)) _
      _ = 41 * (2 ^ 22 * (2 : ℝ≥0∞)⁻¹ ^ (170 + 22)) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow]
          push_cast
          ring
      _ = 41 * x := by rw [E2ECompleteness.two_pow_mul_inv_pow 22 170]
  have he : εpow ≤ x := hp.trans (hsmall 300 (by norm_num))
  have hf : rpmError N ≤ x := by
    calc rpmError N ≤ rpmError (2 ^ 50) := by
          unfold rpmError
          gcongr
      _ = 2 ^ (50 * 2) * (2 : ℝ≥0∞)⁻¹ ^ (408 + 50 * 2) := by
          rw [rpmError, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 408 := E2ECompleteness.two_pow_mul_inv_pow _ 408
      _ ≤ x := hsmall 408 (by norm_num)
  unfold delta2' deltaStaged2
  calc _ ≤ (x + (x + 2 ^ 3 * x)) + (x + 41 * x) + x + x + x :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ha (add_le_add ha' hb)) (add_le_add ht hc)) hr)
          he) hf
    _ = 55 * x := by ring
    _ ≤ 2 ^ 6 * x := by gcongr; norm_num
    _ = (2 : ℝ≥0∞)⁻¹ ^ 164 := by rw [hx]; exact E2ECompleteness.two_pow_mul_inv_pow 6 164

end RecCompose.Pi2P

/-- info: 'RecCompose.Pi2P.prEvent_staged3_triple_le2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.prEvent_staged3_triple_le2

/-- info: 'RecCompose.Pi2P.delta2'_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.delta2'_le
