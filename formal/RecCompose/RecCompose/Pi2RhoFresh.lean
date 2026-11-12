-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Pi2AlphaG.lean`'s `prEvent_tquery_leG` for π2v4's last
-- challenge `ρ` (`crates/leanvm/rec/src/pi2/prover.rs`: `ρ` drawn right after the values at `t`), with
-- `Pi2AlphaChain.lean`'s hits (`HitAt`, `sum_hitAt_le`); uses leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls `KeccakCalls`, their lazy random oracles.
import RecCompose.Pi2AlphaChain

/-!
# `ρ`'s bad set (π2v4)

π2v4 draws `ρ` after the values at `t` (`a`, `ξ`, `s`): its input is the state after `t`'s query (its answer's `32`
bytes) and the values' bytes, with no hash query between `t`'s and `ρ`'s. Its bad set (`BadRho`: `Y_3 = 0`) depends
on `t` only. So, where the run's verdict can accept (`Gβ`):

* `t`'s input is cached before its query with probability at most `εt` (`Pi2Staged.Holds3.tFresh`);
* else `t`'s answer `u` is uniform, and `ρ`'s input (beginning with `u`'s bytes, of another length than `t`'s) is cached
  only if a cached input of its length began with `u` (a hit: at most `K` of the `2^256` answers, `K` the hashed inputs
  before `t`'s query);
* else `ρ`'s answer is uniform and `ρ` lands in its bad set of at most `cr` values with probability `cr / 2^192`.

**`prEvent_rho_leG`**: the graph accepting and `ρ` bad has probability at most
`εt + (K + 1) / 2^256 + cr / 2^192` (the `1`: `t`'s own input, of the same `32`-byte prefix).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open E2ECompleteness (ro Cache prEvent_fresh Regular length_digestBytes simulateQ_callKeccak256)
open UniKeccakComplete.Prob (sum_const_div sum_bad_le)
open UniKeccakComplete.Prob.TFresh (HC CacheBound cacheBound_empty cacheBound_run)
open scoped ENNReal

set_option autoImplicit false

namespace RecCompose.Pi2P

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-- **`ρ` in the random-oracle model, conditioned**: for a staged run whose stage C, where `Gβ` holds, queries `ρ`'s
input `rin b st` (of `Lr` bytes, beginning with `t`'s answer, `t`'s input of another length) first and returns `ρ`
with its prior `prR b st`, and off `Gβ` never accepts: the graph accepting with `ρ` in a bad set of at most `cr` values
has probability at most `εt + (K + 1) / 2^256 + cr / 2^192` (the `1`: `t`'s own input). -/
theorem prEvent_rho_leG (S : Pi2Staged) (rin : S.β → Digest → Bytes) (prR : S.β → Digest → S.υ)
    (Z : S.β → Digest → Digest → OracleComp KeccakCalls (Bool × Bool)) (Gβ : S.β → Prop)
    (hC : ∀ b, Gβ b → ∀ st, S.C b st =
      callKeccak256 (rin b st) >>= fun sr ↦ (fun v ↦ (v, (prR b st, chalP sr))) <$> Z b st sr)
    {Lr : ℕ} (hrin : ∀ b st, Gβ b → (rin b st).length = Lr ∧ (rin b st).take 32 = digestBytes st)
    (badR : S.υ → E → Prop) (cr : ℕ) (hcr : ∀ fr, ∃ T : Finset E, T.card ≤ cr ∧ ∀ ρ, badR fr ρ → ρ ∈ T)
    (accB : ∀ b, ¬ Gβ b → ∀ (st : Digest) (c : Cache) z, z ∈ support ((simulateQ ro (S.C b st)).run c) →
      z.1.1.1 = false)
    {K : ℕ} (hK : HC S.pre K) {εt : ℝ≥0∞}
    (hT : Pr{let p ← (simulateQ ro S.pre).run ∅}[p.2 (.inl (S.tin p.1.1)) ≠ none ∧ Gβ p.1.1] ≤ εt) :
    Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1.1 = true ∧ badR z.1.2.2.1 z.1.2.2.2] ≤
      εt + (((K + 1 : ℕ) : ℝ≥0∞) / 2 ^ 256 + (cr : ℝ≥0∞) / 2 ^ 192) := by
  classical
  rw [StateT.run'_eq, prEvent_map, S.run_eq_pre, simulateQ_bind, StateT.run_bind]
  refine (prEvent_bind_le_prEvent_add_of_support _ _ (fun p ↦ p.2 (.inl (S.tin p.1.1)) ≠ none ∧ Gβ p.1.1) _
    fun p hp hpt ↦ ?_).trans (add_le_add hT le_rfl)
  rw [Pi2C.run_H_bind]
  by_cases hG : Gβ p.1.1
  swap
  · refine (le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun w hw hev ↦ ?_)).trans zero_le
    rw [mem_support_bind_iff] at hw
    obtain ⟨q, -, hw⟩ := hw
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hw
    obtain ⟨z, hz, hw⟩ := hw
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact Bool.false_ne_true ((accB p.1.1 hG _ _ z hz).symm.trans hev.1)
  have hfresh : p.2 (.inl (S.tin p.1.1)) = none := not_not.mp fun h ↦ hpt ⟨h, hG⟩
  have hcp : CacheBound p.2 K := by simpa using cacheBound_run hK cacheBound_empty hp
  rw [prEvent_fresh _ _ hfresh]
  -- each answer `u` of `t`'s query: a hit, or `ρ`'s input fresh
  have hstep : ∀ u : Digest,
      Pr{let w ← (simulateQ ro (S.C p.1.1 u >>= fun z ↦
          pure ((z.1, (S.prT p.1.1, chalP u), z.2), p.1.2))).run (p.2.cacheQuery (.inl (S.tin p.1.1)) u)}[
        w.1.1.1.1 = true ∧ badR w.1.1.2.2.1 w.1.1.2.2.2] ≤
        (if Pi2C.HitAt Lr 0 p.2 u ∨ (S.tin p.1.1).take 32 = digestBytes u then 1 else 0) +
          (cr : ℝ≥0∞) / 2 ^ 192 := by
    intro u
    by_cases hh : Pi2C.HitAt Lr 0 p.2 u ∨ (S.tin p.1.1).take 32 = digestBytes u
    · simp only [hh, ↓reduceIte]
      exact (prEvent_le_one _).trans le_self_add
    simp only [hh, ↓reduceIte, zero_add]
    rw [not_or] at hh
    obtain ⟨hl, ht⟩ := hrin p.1.1 u hG
    have hne : (Sum.inl (rin p.1.1 u) : Bytes ⊕ KeccakState) ≠ .inl (S.tin p.1.1) := fun h ↦
      hh.2 (by rw [← Sum.inl_injective h, ht])
    have hrf : (p.2.cacheQuery (.inl (S.tin p.1.1)) u) (.inl (rin p.1.1 u)) = none := by
      rw [QueryCache.cacheQuery_of_ne _ _ hne]
      by_contra hc
      exact hh.1 ⟨_, hc, hl, by rw [List.drop_zero]; exact ht⟩
    rw [hC p.1.1 hG u, bind_assoc, Pi2C.run_H_bind, prEvent_fresh _ _ hrf]
    refine le_trans (ENNReal.div_le_div_right (Finset.sum_le_sum fun sr _ ↦ ?_) _)
      (sum_bad_le chalP E2ECompleteness.challengeOf_regular (badR (prR p.1.1 u)) cr (hcr _))
    by_cases hb : badR (prR p.1.1 u) (chalP sr)
    · simp only [hb, ↓reduceIte]
      exact prEvent_le_one _
    · simp only [hb, ↓reduceIte]
      refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun w hw hev ↦ hb ?_)
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind] at hw
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hw
      obtain ⟨v, -, hw⟩ := hw
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
      subst hw
      exact hev.2
  have hone : (∑ u : Digest, (if (S.tin p.1.1).take 32 = digestBytes u then 1 else 0 : ℝ≥0∞)) ≤ 1 := by
    rw [Finset.sum_boole]
    have h1 : (Finset.univ.filter fun u : Digest ↦ (S.tin p.1.1).take 32 = digestBytes u).card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb ↦ E2ECompleteness.digestBytes_injective
        ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
    exact_mod_cast h1
  have hsum : (∑ u : Digest, (if Pi2C.HitAt Lr 0 p.2 u ∨ (S.tin p.1.1).take 32 = digestBytes u then 1 else 0 :
      ℝ≥0∞)) ≤ ((K + 1 : ℕ) : ℝ≥0∞) := by
    refine (Finset.sum_le_sum fun u _ ↦ ite_or_le _ _).trans ?_
    rw [Finset.sum_add_distrib, Nat.cast_add, Nat.cast_one]
    exact add_le_add (Pi2C.sum_hitAt_le Lr 0 hcp) hone
  refine (ENNReal.div_le_div_right (Finset.sum_le_sum fun u _ ↦ hstep u) _).trans (le_of_eq ?_) |>.trans
    (add_le_add (ENNReal.div_le_div_right hsum _) le_rfl)
  rw [Finset.sum_add_distrib, ENNReal.add_div, sum_const_div]

end RecCompose.Pi2P

/-- info: 'RecCompose.Pi2P.prEvent_rho_leG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2P.prEvent_rho_leG
