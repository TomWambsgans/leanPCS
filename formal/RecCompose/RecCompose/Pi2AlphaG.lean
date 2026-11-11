-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Pi2Chain.lean`'s `prEvent_staged3_triple_le2`,
-- `prEvent_staged_bad_le2`, `Pi2Prob.lean`'s `prEvent_tquery_le'` and `Pi2TFresh.lean`'s `TF.tFresh_of`, with the
-- freshness conditioned on a predicate off which the verdict rejects; uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- `KeccakCalls`, their lazy random oracles, `rpmError`, `DuplexVm`, `hashBlocks`; VCVio's `support`.
import RecCompose.Pi2TFreshPi2
import RecCompose.Pi2Holds3

/-!
# `t`'s freshness, conditioned on the graph's acceptance

Off the graph's acceptance (π1's prover returning none, or a proof the graph rejects) `α`'s freshness is not asked
(`Pi2Holds3.Holds3`: the verdict's first component, the graph's, is `false` there). So `t`'s freshness is conditioned
too:

* **`TF.tFresh_ofG`**: `t`'s input cached when asked, on `Gβ` (stage B's output, implying `G` of stage A's), with
  probability at most `εα + (4 KA + 6 + NT) / 2^256`, from `α`'s freshness on `G`;
* **`Pi2G.pi2TFresh_ofG`**: at π2's staged run (`α`'s and `t`'s inputs of `88` bytes), the bound `tFreshBound2 N εα`
  from the run's block count `N`.
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

/-! ## `t`'s freshness, conditioned -/

namespace TF

/-- **`t`'s query is fresh on `Gβ`** (`tFresh_of`, conditioned): `α`'s input cached after A on `G` with probability at
most `εα`, `Gβ` of stage B's output implying `G` of stage A's; `t`'s input is cached when asked, on `Gβ`, with
probability at most `εα + (4 KA + 6 + NT) / 2^256`. -/
theorem tFresh_ofG (S : Pi2Staged) {δ : Type} (T : S.α → Digest → Digest → Digest → OracleComp KeccakCalls δ)
    (g : S.α → Digest → Digest → Digest → δ → S.β)
    (hB : ∀ a s₁ s₂ s₃, S.B a s₁ s₂ s₃ = T a s₁ s₂ s₃ >>= fun d ↦ pure (g a s₁ s₂ s₃ d))
    (hTap : ∀ a s₁ s₂ s₃, APq (fun _ _ ↦ True) [default] (T a s₁ s₂ s₃))
    (hT32 : ∀ a s₁ s₂ s₃, HashOK (fun m ↦ m.length ≠ 32) (T a s₁ s₂ s₃))
    {NT : ℕ} (hTc : ∀ a s₁ s₂ s₃, HC (T a s₁ s₂ s₃) NT)
    (htin : ∀ a s₁ s₂ s₃ d, (S.tin (g a s₁ s₂ s₃ d)).length = tLen ∧
      (S.tin (g a s₁ s₂ s₃ d)).take 32 = digestBytes s₃)
    {L : ℕ} (hL : L ≠ 32) (hinp : ∀ a, (S.inp a).length = L) {KA : ℕ} (hA : HC S.A KA)
    (G : S.α → Prop) (Gβ : S.β → Prop) (hg : ∀ a s₁ s₂ s₃ d, Gβ (g a s₁ s₂ s₃ d) → G a) {εα : ℝ≥0∞}
    (hα : Pr{let p ← (simulateQ ro S.A).run ∅}[p.2 (.inl (S.inp p.1)) ≠ none ∧ G p.1] ≤ εα) :
    Pr{let p ← (simulateQ ro S.pre).run ∅}[p.2 (.inl (S.tin p.1.1)) ≠ none ∧ Gβ p.1.1] ≤
      εα + ((4 * KA + 6 + NT : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  classical
  rw [run_pre_tree S T g hB]
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun p ↦ p.2 (.inl (S.inp p.1)) ≠ none ∧ G p.1) _
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
    obtain ⟨z, -, hw⟩ := hw
    rw [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact hG (hg _ _ _ _ _ hev.2)
  have hfα : p.2 (.inl (S.inp p.1)) = none := not_not.mp fun h ↦ hpα ⟨h, hG⟩
  refine (prEvent_mono _ _ (fun w ↦ w.2 (.inl (S.tin w.1.1)) ≠ none) fun w hw ↦ hw.1).trans ?_
  have hcp : CacheBound p.2 KA := by simpa using cacheBound_run hA cacheBound_empty hp
  set c := p.2 with hc
  have hne : ∀ s : Digest, (Sum.inl (digestBytes s) : Bytes ⊕ KeccakState) ≠ .inl (S.inp p.1) := fun s h ↦
    hL ((hinp p.1).symm.trans (by rw [← Sum.inl_injective h, length_digestBytes]))
  -- `s₁`: fresh.
  refine (prEvent_query_le _ _ False (fun _ ↦ hfα) _ _
    (fun s₁ ↦ (if c (.inl (digestBytes s₁)) ≠ none then 1 else 0) +
      ((KA + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + ((2 * KA + 5 + NT : ℕ) : ℝ≥0∞) / 2 ^ 256)
    fun s₁ ↦ ?_).trans ?_
  rotate_left
  · simp only [↓reduceIte, zero_add]
    rw [Finset.sum_add_distrib, ENNReal.add_div, Finset.sum_add_distrib, ENNReal.add_div, sum_const_div,
      sum_const_div]
    refine (add_le_add (add_le_add (ENNReal.div_le_div_right (sum_cached_le hcp) _) le_rfl) le_rfl).trans
      (le_of_eq ?_)
    rw [← ENNReal.add_div, ← ENNReal.add_div]
    congr 1
    push_cast
    ring
  -- `s₂`: fresh unless `s₁`'s bytes were cached.
  refine (prEvent_query_le _ _ (c (.inl (digestBytes s₁)) ≠ none)
    (fun hs ↦ by rw [QueryCache.cacheQuery_of_ne _ _ (hne s₁)]; exact not_not.mp hs) _ _
    (fun s₂ ↦ (if s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none then 1 else 0) +
      ((2 * KA + 5 + NT : ℕ) : ℝ≥0∞) / 2 ^ 256) fun s₂ ↦ ?_).trans ?_
  rotate_left
  · refine le_trans ?_ (le_of_eq (add_assoc _ _ _).symm)
    refine add_le_add le_rfl ?_
    rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    refine add_le_add (ENNReal.div_le_div_right ?_ _) le_rfl
    calc (∑ s₂ : Digest, (if s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none then 1 else 0 : ℝ≥0∞))
        ≤ ∑ s₂ : Digest, ((if s₂ ∈ [s₁] then 1 else 0) + (if c (.inl (digestBytes s₂)) ≠ none then 1 else 0)) :=
          Finset.sum_le_sum fun s₂ _ ↦ by
            simpa only [List.mem_singleton] using ite_or_le (s₂ = s₁) (c (.inl (digestBytes s₂)) ≠ none)
      _ ≤ (([s₁].length : ℕ) : ℝ≥0∞) + KA := by
          rw [Finset.sum_add_distrib]
          exact add_le_add (sum_mem_le _) (sum_cached_le hcp)
      _ = ((KA + 1 : ℕ) : ℝ≥0∞) := by simp only [List.length_singleton, Nat.cast_one]; push_cast; ring
  -- the cache before `s₃`
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Cache,
      (c.cacheQuery (.inl (S.inp p.1)) s₁).cacheQuery (.inl (digestBytes s₁)) s₂ = c₂ := ⟨_, rfl⟩
  have hc₂b : CacheBound c₂ (KA + 2) := by
    rw [← hc₂]
    exact (hcp.cacheQuery_inl _ _).cacheQuery_inl _ _
  dsimp only
  rw [hc₂]
  -- `s₃`: fresh unless `s₂ = s₁` or `s₂`'s bytes were cached.
  refine (prEvent_query_le _ _ (s₂ = s₁ ∨ c (.inl (digestBytes s₂)) ≠ none) (fun hs ↦ ?_) _ _
    (fun u ↦ (if u = default ∨ Ans c₂ u ∨ Hit64 c₂ u then 1 else 0) + (NT : ℝ≥0∞) / 2 ^ 256)
    fun u ↦ ?_).trans (add_le_add le_rfl ?_)
  · rw [not_or] at hs
    have h12 : (Sum.inl (digestBytes s₂) : Bytes ⊕ KeccakState) ≠ .inl (digestBytes s₁) := fun h ↦
      hs.1 (E2ECompleteness.digestBytes_injective (Sum.inl_injective h))
    rw [← hc₂, QueryCache.cacheQuery_of_ne _ _ h12, QueryCache.cacheQuery_of_ne _ _ (hne s₂)]
    exact not_not.mp hs.2
  · -- the tree after `u = s₃`
    by_cases hbad : u = default ∨ Ans c₂ u ∨ Hit64 c₂ u
    · simp only [hbad, ↓reduceIte]
      exact (prEvent_le_one _).trans le_self_add
    simp only [hbad, ↓reduceIte, zero_add]
    rw [not_or, not_or] at hbad
    have hT2 : HashOK (fun m ↦ m ≠ digestBytes s₂) (T p.1 s₁ s₂ u) :=
      UniKeccakComplete.Prob.HashOK.mono (P := fun m ↦ m.length ≠ 32) (Q := fun m ↦ m ≠ digestBytes s₂)
        (fun m hm he ↦ hm (by rw [he]; exact length_digestBytes s₂)) (hT32 _ _ _ _)
    try dsimp only
    rw [run_frame _ u _ hT2 c₂]
    refine (prEvent_map_bind_pure _ _ _ _ (fun z ↦ Hit64 z.2 u) fun z hz ↦ ?_).trans ?_
    · obtain ⟨hl, ht⟩ := htin p.1 s₁ s₂ u z.1
      have hn : (Sum.inl (S.tin (g p.1 s₁ s₂ u z.1)) : Bytes ⊕ KeccakState) ≠ .inl (digestBytes s₂) := fun h ↦ by
        have := congrArg List.length (Sum.inl_injective h)
        rw [hl, length_digestBytes] at this
        exact absurd this (by decide)
      dsimp only at hz
      rw [QueryCache.cacheQuery_of_ne _ _ hn] at hz
      exact ⟨_, hz, hl, ht⟩
    · exact prHit64_le (hTap p.1 s₁ s₂ u) (hTc _ _ _ _) c₂ u
        (fun hm ↦ hbad.1 (List.mem_singleton.mp hm)) hbad.2.1 hbad.2.2
  · -- the average over `u`
    rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]
    have hsum : (∑ u : Digest, (if u = default ∨ Ans c₂ u ∨ Hit64 c₂ u then 1 else 0 : ℝ≥0∞)) ≤
        ((2 * KA + 5 : ℕ) : ℝ≥0∞) := by
      calc (∑ u : Digest, (if u = default ∨ Ans c₂ u ∨ Hit64 c₂ u then 1 else 0 : ℝ≥0∞))
          ≤ ∑ u : Digest, ((if u ∈ [default] then 1 else 0) + ((if Ans c₂ u then 1 else 0) +
              (if Hit64 c₂ u then 1 else 0))) :=
            Finset.sum_le_sum fun u _ ↦ (ite_or_le _ _).trans (add_le_add (by simp) (ite_or_le _ _))
        _ ≤ (([default].length : ℕ) : ℝ≥0∞) + (((KA + 2 : ℕ) : ℝ≥0∞) + ((KA + 2 : ℕ) : ℝ≥0∞)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            exact add_le_add (sum_mem_le _) (add_le_add (sum_ans_le hc₂b) (sum_hit64_le hc₂b))
        _ = ((2 * KA + 5 : ℕ) : ℝ≥0∞) := by
            simp only [List.length_singleton, Nat.cast_one]
            push_cast
            ring
    refine (add_le_add (ENNReal.div_le_div_right hsum _) le_rfl).trans (le_of_eq ?_)
    rw [← ENNReal.add_div]
    congr 1
    push_cast
    ring

end TF

end RecCompose.Pi2P

namespace RecCompose.Pi2G

open RecStatement LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom
open Pi2S Pi2K Pi2P Pi2E

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-- **`t`'s freshness at π2's staged run, conditioned on `G` of stage B's `a`** (`pi2TFresh_of`, conditioned): from the
run's cost and `α`'s freshness on `G`. -/
theorem pi2TFresh_ofG {D : RecDeployment} (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) (input : Vector UInt8 32) {N : ℕ}
    (hcost : Common.QueryCostAtMost (pi2Staged D C Fa P1k input).run hashBlocks N) (G : StA → Prop) {εα : ℝ≥0∞}
    (hα : Pr{let p ← (simulateQ ro (pi2Staged D C Fa P1k input).A).run ∅}[
      p.2 (.inl ((pi2Staged D C Fa P1k input).inp p.1)) ≠ none ∧ G p.1] ≤ εα) :
    Pr{let p ← (simulateQ ro (pi2Staged D C Fa P1k input).pre).run ∅}[
      p.2 (.inl ((pi2Staged D C Fa P1k input).tin p.1.1)) ≠ none ∧ G p.1.1.a] ≤ tFreshBound2 N εα := by
  refine TF.tFresh_ofG (pi2Staged D C Fa P1k input) (fun a s₁ s₂ s₃ ↦ treeB C input a s₁ s₂ s₃)
    (fun a s₁ s₂ s₃ qT ↦ outB C input a s₁ s₂ s₃ qT) (fun a s₁ s₂ s₃ ↦ stageB_eq D C input a s₁ s₂ s₃)
    (fun a s₁ s₂ s₃ ↦ apq_treeB C input a s₁ s₂ s₃) (fun a s₁ s₂ s₃ ↦ hashOK32_treeB C input a s₁ s₂ s₃)
    (NT := E2ECompleteness.Cost.treeCost muQ + muQ) (fun a s₁ s₂ s₃ ↦ hc_treeB C Fa input a s₁ s₂ s₃)
    (fun a s₁ s₂ s₃ qT ↦ tin_stageB_length C input a s₁ s₂ s₃ qT) (by norm_num : (88 : ℕ) ≠ 32)
    (fun a ↦ fixLen_length 88 _) ((pi2Staged D C Fa P1k input).hc_A hcost) G (fun b : StB ↦ G b.a)
    (fun _ _ _ _ _ h ↦ h) hα |>.trans (le_of_eq ?_)
  unfold tFreshBound2
  rfl

end RecCompose.Pi2G

/-- info: 'RecCompose.Pi2P.TF.tFresh_ofG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.TF.tFresh_ofG

/-- info: 'RecCompose.Pi2G.pi2TFresh_ofG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2G.pi2TFresh_ofG
