-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec3's analogue of `ProbTFresh.lean`
-- (`tQueryFresh_flockProve`, `tQueryFresh_reference`), reusing its chain calculus (`Prob.TFresh`: `ChainF`, `EndsT`,
-- `WCh`, `WEnd`, `prHit_le`, the writer's and Flock's steps), itself following
-- `formal/EndToEnd/Completeness/E2ECompleteness/Chain.lean`; uses leanerVM (https://github.com/Verified-zkEVM/leanerVM,
-- branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls `KeccakCalls`, their lazy random oracles, the
-- weight calculus `Common.QueryCostAtMost`.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/Rec3ProbTFresh.lean`.
import UniKeccakComplete.K.Rec3ProbExp
import UniKeccakComplete.K.ProbTFresh

/-!
# `t`'s query is fresh for π1-rec3 (`TQueryFresh3`), for Flock's honest prover

`TQueryFresh3 flock D εt` (`Rec3ProbExp.lean`): in the two-call random-oracle model, the input of the query that draws
`t` (`tInput` of the writer after `C2`'s root) is already cached when it is asked with probability at most `εt`.
Proved here for Flock's honest prover `FlockP.flockProve` (as `fun H ↦ FlockP.flockProve H`, the main line's
`flockProveH`; π1-rec3 runs it at `keccakRec3`):

* **`tQueryFresh3_flockProve`**: for every deployment, `εt = tFreshBound3 D = (n + 1) · M / 2^256`,
  `n = tSteps3 D` the challenges after the first bus challenge (`β`, `γ`, Flock's), `M = tCache3 D` (the main line's
  stage A count `stageACost`, the chain's, `C2`'s tree's `c2Cost`, one);
* **`tQueryFresh3_reference`**: at the reference Keccak shape, `εt = 2^-200` (`n = 72`, `M ≤ 2^28`: `73 · 2^28 / 2^256
  < 2^-200`).

**The chain still holds at π1-rec3.** The argument is `ProbTFresh.lean`'s: after the first bus challenge (`88` bytes,
fresh by its length, `hashA_stagedU3`) only **one** more (`β`, `s₂ = H(s₁)`, `preTail3`), then `γ` and Flock's prover
at `keccakRec3` (`TFresh.wend_flockProve`, whose draw at the rec3 shape is at most one challenge, bounded here by the
main line's count), then `C2`'s tree. So `n = 1 + 1 + flockSteps 32 3 = 72` at the reference shape (an upper bound;
main line: `75`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open UniStatement UniKeccak UniKeccakSound
open E2ECompleteness (ro Cache HashOK cache_of_hashOK simulateQ_callKeccak256)
open UniKeccakComplete.Prob (firstInput_length ProverA chal run_sendRoot)
open UniKeccakComplete.Prob.TFresh
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Rec3

open UniComplete

namespace TFresh3

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The staged run -/

/-- Flock's challenges at the deployment (`keccakRec3`), at most. -/
def flockStepsD3 (D : KDeployment) : ℕ := flockSteps (flockLogNT D.shape) keccakRec3.skip

/-- **The challenges after the first bus challenge**: `β`, `γ`, Flock's. -/
def tSteps3 (D : KDeployment) : ℕ := flockStepsD3 D + 2

/-- **The hashed inputs before `t`**, at most (and one). -/
def tCache3 (D : KDeployment) : ℕ := stageACost D + (tSteps3 D + c2Cost D) + 1

/-- **`t`'s cache-hit bound**: `(tSteps3 + 1) · tCache3 / 2^256`. -/
noncomputable def tFreshBound3 (D : KDeployment) : ℝ≥0∞ :=
  ((tSteps3 D + 1 : ℕ) : ℝ≥0∞) * ((tCache3 D : ℝ≥0∞) / 2 ^ 256)

/-- **Stage A hashes at most `stageACost` inputs** (π1-rec3's IV is one query, as the main line's). -/
theorem hc_stageA3 (flock : FlockProverH) (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) : HC (stagedU3 flock D input rows q).A (stageACost D) := by
  have hcm : ∀ (μ : ℕ) (stack : Array K),
      HC (E2ECompleteness.commitWithH callKeccak256 μ stack) (5 * 2 ^ (μ - 6 + 1)) :=
    fun μ stack ↦ hc_of_qc (E2ECompleteness.Cost.qc_commitWithH μ stack)
  simp only [stagedU3, proverA3, setupTreeOf, setupTreeKWithH, contractIvOf, seedOf, bind_assoc, pure_bind]
  refine Common.QueryCostAtMost.mono (Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦
    Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦ Common.QueryCostAtMost.bind (hc_H _) fun _ ↦
    Common.QueryCostAtMost.bind (hc_H _) fun _ ↦ Common.QueryCostAtMost.bind (b := 0) (hcm _ _) fun _ ↦
    trivial) ?_
  simp only [stageACost, E2ECompleteness.Cost.treeCost, honestTrace_shape]
  omega

/-- `midB3` over the two calls, run: `γ`, Flock's prover at `keccakRec3`, `C2`'s commitment, its root written. -/
theorem run_midB3 (flock : FlockProver (OracleComp KeccakCalls)) (tr : Trace) (alphas : List E) (beta : E)
    (w : Wr) :
    (midB3 callKeccak256 (commitReal callKeccak256) flock tr alphas beta).run w =
      (sampleW callKeccak256).run w >>= fun p ↦
        (flock (keccakR1csLogSize + tr.shape.heights.getD opBlake2s 0) keccakRec3 tr.qflock).run p.2 >>= fun q ↦
          commitReal callKeccak256 .c2 (((layoutsOfK tr.shape).lookup .c2).getD default).vars
              (c2DataOf tr (eqKernel alphas) beta p.1).stack >>= fun c ↦
            pure ((p.1, q.1, c), { q.2 with stream := q.2.stream ++ (rootWord c.halves).toArray }) := by
  simp only [midB3, StateT.run_bind, StateT.run_lift, run_sendRoot, bind_assoc, pure_bind, StateT.run_pure]

/-- **π1-rec3's staged run after the first bus challenge**: `s₂`, then `B` (`γ`, Flock, `C2`). -/
def preTail3 (S : KStaged3) (a : S.α) (s₁ : Digest) : OracleComp KeccakCalls (S.β × (List E × E)) := do
  let s₂ ← callKeccak256 (digestBytes s₁)
  let b ← S.B a s₁ s₂
  return (b, (alphaOf3 s₁, PcsQuotient.Transcript.challengeOf s₂))

theorem pre_eq3 (S : KStaged3) : S.pre = S.A >>= fun a ↦ callKeccak256 (S.inp a) >>= preTail3 S a := rfl

/-- **π1-rec3's staged run after the first bus challenge is a chain** of `tSteps3` challenges and
`tSteps3 + c2Cost` hashed inputs, its final state the writer's before `t`. -/
theorem chainF_preTail3 (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (a : LeanVM.Prover.Tree × ProverA) (s₁ : Digest) :
    ChainF (fun (z : MidU3 × (List E × E)) s ↦ z.1.mw.2.state = s) (tSteps3 D) (tSteps3 D + c2Cost D) s₁
      (preTail3 (stagedU3 flockP D input rows q) a s₁) := by
  unfold preTail3
  refine .step (n := flockStepsD3 D + 1) (N := flockStepsD3 D + c2Cost D + 1) _ _ (take_digestBytes' s₁)
    (by unfold tSteps3; omega) (by unfold tSteps3; omega) fun s₂ ↦ ?_
  simp only [stagedU3, midU3, bind_assoc, pure_bind]
  rw [run_midB3]
  simp only [bind_assoc, pure_bind]
  have h1 := wch_sampleW (pre := fun _ ↦ True) (writerAfter3 rows a.2.c1 s₁ s₂) trivial
  refine ChainF.mono (n := 1 + flockStepsD3 D) (N := 1 + (flockStepsD3 D + c2Cost D))
    (n' := flockStepsD3 D + 1) (N' := flockStepsD3 D + c2Cost D + 1)
    (ChainF.bind (n₂ := flockStepsD3 D) (N₂ := flockStepsD3 D + c2Cost D) (fun p s hp ↦ ?_) h1) (by omega)
    (by omega)
  obtain ⟨hs, -⟩ := hp
  subst hs
  have h := wend_flockProve (flockLogNT D.shape) keccakRec3 (honestTrace D input rows q).qflock p.2 trivial
  refine ChainF.mono (n := flockSteps (flockLogNT D.shape) keccakRec3.skip + 0)
    (N := flockSteps (flockLogNT D.shape) keccakRec3.skip + c2Cost D + 0)
    (n' := flockStepsD3 D) (N' := flockStepsD3 D + c2Cost D)
    (h _ _ _ (c2Cost D) _ _ 0 0 (hashOK_commitReal _ _ _) (hc_commitReal _ _ _) ?_)
    (by unfold flockStepsD3; omega) (by unfold flockStepsD3; omega)
  intro b s' d hb
  exact .ret _ hb.1

end TFresh3

open TFresh3

/-- **`t`'s query is fresh for π1-rec3 with Flock's honest prover**, at every deployment: its input is cached when
asked with probability at most `tFreshBound3 D = (tSteps3 D + 1) · tCache3 D / 2^256`. -/
theorem tQueryFresh3_flockProve (D : KDeployment) :
    TQueryFresh3 (fun H ↦ FlockP.flockProve H) D (tFreshBound3 D) := by
  intro input rows q hfit _
  have hmono := prEvent_mono ((simulateQ ro (stagedU3 flockP D input rows q).pre).run ∅)
    (fun p ↦ p.2 (.inl ((stagedU3 flockP D input rows q).tin p.1.1)) ≠ none)
    (fun (p : (MidU3 × (List E × E)) × Cache) ↦ Hit p.2 p.1.1.mw.2.state)
    (fun p hp ↦ ⟨_, hp, take_digestBytes _ _⟩)
  refine hmono.trans ?_
  rw [pre_eq3, simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp ↦ ?_
  rw [simulateQ_bind, simulateQ_callKeccak256, StateT.run_bind]
  have hc : CacheBound p.2 (stageACost D) :=
    (cacheBound_run (hc_stageA3 flockP D input rows q) cacheBound_empty hp).mono (by omega)
  have hx : p.2 (.inl ((stagedU3 flockP D input rows q).inp p.1)) = none := by
    by_contra h
    rcases cache_of_hashOK (hashA_stagedU3 flockP D input rows q) ∅ hp _ h with h' | h'
    · exact h' rfl
    · exact h'.2 (firstInput_length hfit.1 p.1.2)
  exact prHit_le _ (fun (z : MidU3 × (List E × E)) ↦ z.1.mw.2.state) (fun _ _ h ↦ h) (tCache3 D) (tSteps3 D)
    (tSteps3 D + c2Cost D) (stageACost D) _ _ _ (fun s₁ ↦ chainF_preTail3 D input rows q p.1 s₁) hc
    (by unfold tCache3; omega) hx

/-! ## At the reference Keccak shape -/

theorem tSteps3_reference (D : KDeployment) (hD : D.shape = keccakRefShape) : tSteps3 D = 72 := by
  unfold tSteps3 flockStepsD3 flockSteps frontSteps zcSteps flockLogNT
  rw [hD, UniKeccakSound.IdsNum.hSha3_ref]
  rfl

theorem tCache3_reference (D : KDeployment) (hD : D.shape = keccakRefShape) : tCache3 D ≤ 2 ^ 28 := by
  have h := Prob.tCache_reference D hD
  have h1 := tSteps3_reference D hD
  have h2 := Prob.tSteps_reference D hD
  unfold tCache3
  unfold Prob.TFresh.tCache at h
  omega

/-- **The reference bound**: `tFreshBound3 D ≤ 2^-200` (`(72 + 1) · 2^28 / 2^256 < 2^-200`). -/
theorem tFreshBound3_reference (D : KDeployment) (hD : D.shape = keccakRefShape) :
    tFreshBound3 D ≤ (2 : ℝ≥0∞)⁻¹ ^ 200 := by
  have hN : (tSteps3 D + 1) * tCache3 D ≤ 2 ^ 56 := by
    rw [tSteps3_reference D hD]
    have := tCache3_reference D hD
    omega
  unfold tFreshBound3
  rw [← mul_div_assoc, ← Nat.cast_mul]
  calc (((tSteps3 D + 1) * tCache3 D : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ((2 ^ 56 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
        ENNReal.div_le_div_right (by exact_mod_cast hN) _
    _ = (2 : ℝ≥0∞)⁻¹ ^ 200 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.div_eq_inv_mul, ENNReal.inv_pow, mul_comm,
          show (256 : ℕ) = 200 + 56 from rfl]
        exact E2ECompleteness.two_pow_mul_inv_pow 56 200

/-- **`t`'s query is fresh at the reference Keccak shape** for π1-rec3 with Flock's honest prover, with probability of
a cache hit at most `2^-200`. -/
theorem tQueryFresh3_reference (D : KDeployment) (hD : D.shape = keccakRefShape) :
    TQueryFresh3 (fun H ↦ FlockP.flockProve H) D ((2 : ℝ≥0∞)⁻¹ ^ 200) :=
  fun input rows q hfit hrel ↦
    (tQueryFresh3_flockProve D input rows q hfit hrel).trans (tFreshBound3_reference D hD)

end UniKeccakComplete.Rec3

/-! ## Axioms -/

/-- info: 'UniKeccakComplete.Rec3.tQueryFresh3_flockProve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.tQueryFresh3_flockProve

/-- info: 'UniKeccakComplete.Rec3.tQueryFresh3_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.tQueryFresh3_reference
