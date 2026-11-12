-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's analogue of `Rec3ProbTFresh.lean`
-- (`tQueryFresh3_flockProve`, `tQueryFresh3_reference`) in the five-digest reading, on `Rec4Chain.lean`'s chains with
-- tails; uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR
-- Apache-2.0): the two calls `KeccakCalls`, their lazy random oracles, the weight calculus.
import UniKeccakComplete.K.Rec4Chain
import UniKeccakComplete.K.Rec3ProbTFresh

/-!
# The point draw's query is fresh for π1-rec4 (`TQueryFresh4`)

`TQueryFresh4 D εt` (`Rec4ProbK.lean`): in the five-digest reading (`stagedU4`: a rate the input's digest and four
tails `extIn i x`), the point draw's input (`tInput` of the writer after `C2`'s answer) is already hashed before its
query with probability at most `εt`. Proved here:

* **`tQueryFresh4_le`**: at every deployment, with probability at most `(n + 1) · M / 2^256`, `n = flock4Steps` the
  challenges after the bus draw (Flock's: the skip's `z`, the zerocheck's rounds, `α`, the lincheck's `11`), `M` the
  hashed inputs before (five a challenge, the stage A's and `C2`'s trees five times);
* **`tQueryFresh4_reference`**: at the reference shape, `εt = 2^-200` (`n = 42`, `M < 2^28`).

**The chain.** The bus draw's input (`112` bytes) is fresh by its length (`fresh_x1`); its tails follow it
(`prHitX_top`). Each of Flock's challenges is a step on the writer's state followed by its four tails
(`wchX_sampleW5`). Flock's last challenge (the lincheck's last round) hashes `80` bytes: the state and the round's two
scalars (`wendX_lcRounds`: nothing pending before a round); `C2`'s tree hashes `64`- and `512`-byte inputs and their
tails, none of `80` bytes, so it joins that last step's tails (`EndsX`). The writer's state is then the point draw's
input's first `32` bytes.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open UniStatement UniKeccak UniKeccakSound
open E2ECompleteness (ro Cache HashOK cache_of_hashOK simulateQ_callKeccak256 length_digestBytes)
open UniKeccakComplete.Prob (firstInput_length ProverA chal run_sendRoot run_sendScalar tInput)
open UniKeccakComplete.Prob.TFresh (HC hq hc_H hc_of_qc CacheBound cacheBound_run cacheBound_empty Hit
  take_digestBytes stageACost c2Cost tCache tSteps flockLogNT hc_commitReal honestTrace_shape)
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Rec4.TF4

open UniComplete

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The five-digest hash -/

/-- **A hash's four tails.** -/
def tails5 (x : Bytes) : OracleComp KeccakCalls (Digest × Digest × Digest × Digest) := do
  let t1 ← callKeccak256 (extIn 1 x)
  let t2 ← callKeccak256 (extIn 2 x)
  let t3 ← callKeccak256 (extIn 3 x)
  let t4 ← callKeccak256 (extIn 4 x)
  pure (t1, t2, t3, t4)

theorem rate5_eq (x : Bytes) : rate5 x = callKeccak256 x >>= fun d ↦ tails5 x >>= fun ts ↦
    pure (mkRate d ts.1 ts.2.1 ts.2.2.1 ts.2.2.2) := by
  simp only [rate5, tails5, bind_assoc, pure_bind]

theorem hash5_eq (x : Bytes) : hash5 x = callKeccak256 x >>= fun u ↦ tails5 x >>= fun _ ↦ pure u := by
  simp only [hash5, rate5_eq, map_bind, map_pure, digestOfRate_mkRate]

theorem extIn_ne_self {i : ℕ} (hi : 1 ≤ i) (x : Bytes) : extIn i x ≠ x := by
  intro h
  have := congrArg List.length h
  rw [length_extIn] at this
  unfold lenB at this
  have : 1152921504606846976 ≤ i * 1152921504606846976 := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem hashOK_tails5 (x : Bytes) : HashOK (fun m ↦ m ≠ x) (tails5 x) := by
  unfold tails5
  exact E2ECompleteness.HashOK.bind (E2ECompleteness.hashOK_callKeccak256 (extIn_ne_self le_rfl x)) fun _ ↦
    E2ECompleteness.HashOK.bind (E2ECompleteness.hashOK_callKeccak256 (extIn_ne_self (by norm_num) x)) fun _ ↦
    E2ECompleteness.HashOK.bind (E2ECompleteness.hashOK_callKeccak256 (extIn_ne_self (by norm_num) x)) fun _ ↦
    E2ECompleteness.HashOK.bind (E2ECompleteness.hashOK_callKeccak256 (extIn_ne_self (by norm_num) x)) fun _ ↦
    E2ECompleteness.HashOK.pure _ _

theorem hc_pure {α : Type} (a : α) : HC (pure a : OracleComp KeccakCalls α) 0 := trivial

theorem hc_tails5 (x : Bytes) : HC (tails5 x) 4 := by
  unfold tails5
  exact (Common.QueryCostAtMost.bind (hc_H _) fun _ ↦ Common.QueryCostAtMost.bind (hc_H _) fun _ ↦
    Common.QueryCostAtMost.bind (hc_H _) fun _ ↦ Common.QueryCostAtMost.bind (hc_H _) fun _ ↦
    hc_pure _).mono (by omega)

theorem hc_hash5 (x : Bytes) : HC (hash5 x) 5 := by
  rw [hash5_eq]
  exact (Common.QueryCostAtMost.bind (hc_H x) fun _ ↦ Common.QueryCostAtMost.bind (hc_tails5 x) fun _ ↦
    hc_pure _).mono (by omega)

/-- **The five-digest reading of a computation hashes five times as many inputs.** -/
theorem hc_iota5 {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ} (h : HC X n) :
    HC (simulateQ iota5 X) (5 * n) := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => rw [simulateQ_pure]; trivial
  | query_bind t k ih =>
    rw [simulateQ_query_bind]
    have h' := (Common.isWeightBound_query_bind_iff _ _ _ _).1 h
    rcases t with x | s
    · have h1 : hq (Sum.inl x) ≤ n := h'.1
      exact (Common.QueryCostAtMost.bind (hc_hash5 x) fun u ↦ ih u (h'.2 u)).mono
        (by simp only [hq] at h1 ⊢; omega)
    · have hF : HC (callKeccakF1600 s) 0 := Common.isWeightBound_query hq (Sum.inr s)
      exact (Common.QueryCostAtMost.bind hF fun u ↦ ih u (h'.2 u)).mono (by simp [hq])

/-! ## The writer's steps in the five-digest reading -/

theorem run_sampleW5 (w : Wr) :
    (sampleW hash5).run w = callKeccak256 (tInput w) >>= fun u ↦ tails5 (tInput w) >>= fun _ ↦
      pure (chal u, { w with absorbed := w.stream.size, state := u, challenges := w.challenges.push (chal u) }) := by
  rw [Prob.run_sampleW, hash5_eq]
  simp only [bind_assoc, pure_bind]
  rfl

/-- **A challenge**: one step on the writer's state, five hashed inputs; afterwards nothing is pending. -/
theorem wchX_sampleW5 {pre : Wr → Prop} :
    WChX (sampleW hash5) 1 5 pre (fun _ w ↦ w.absorbed = w.stream.size) := by
  intro w _
  rw [run_sampleW5]
  exact .step (n := 0) (N := 0) (NT := 4) _ _ _ (take_digestBytes _ _) (hashOK_tails5 _) (hc_tails5 _) le_rfl
    (by omega) fun u d ↦ .ret _ ⟨rfl, rfl⟩

/-- **A challenge on `48` pending bytes** hashes `80` bytes: it can end a chain. -/
theorem wendX_sampleW5 :
    WEndX (sampleW hash5) 1 5 (fun w ↦ w.stream.size = w.absorbed + 48) (fun _ _ ↦ True) := by
  intro w hw
  rw [run_sampleW5]
  refine (endsX_last (tInput w) (tails5 (tInput w)) 4 _ (take_digestBytes _ _) ?_ (hashOK_tails5 _) (hc_tails5 _)
    fun u d ↦ ⟨rfl, trivial⟩).mono le_rfl (by omega) fun _ _ h ↦ h
  simp only [tInput, List.length_append, length_digestBytes, Array.length_toList, Array.size_extract, hw]
  omega

theorem wchX_sendScalar (x : E) {pre : Wr → Prop} :
    WChX (sendScalar (m := OracleComp KeccakCalls) x) 0 0 pre (fun _ _ ↦ True) :=
  (wchX_sendBytes _).mono le_rfl le_rfl fun _ _ _ ↦ trivial

theorem wchX_sendScalars (xs : List E) {pre : Wr → Prop} :
    WChX (sendScalars (m := OracleComp KeccakCalls) xs) 0 0 pre (fun _ _ ↦ True) :=
  (wchX_sendBytes _).mono le_rfl le_rfl fun _ _ _ ↦ trivial

/-- **A scalar** adds `24` pending bytes. -/
theorem wchX_sendScalarT (x : E) (k : ℕ) :
    WChX (sendScalar (m := OracleComp KeccakCalls) x) 0 0 (fun w ↦ w.stream.size = w.absorbed + k)
      (fun _ w ↦ w.stream.size = w.absorbed + (k + 24)) := by
  intro w hw
  rw [run_sendScalar]
  refine .ret _ ⟨rfl, ?_⟩
  simp [hw, Prob.scalarWire_length]
  omega

theorem WEndX.pre_mono {α : Type} {M : PM α} {n N : ℕ} {pre pre' : Wr → Prop} {post : α → Wr → Prop}
    (h : WEndX M n N pre post) (hp : ∀ w, pre' w → pre w) : WEndX M n N pre' post :=
  fun w hw ↦ h w (hp w hw)

/-! ## Flock at π1-rec4 -/

theorem wchX_zcRounds (r : List E) : ∀ (claim : E) (a b c : Array E),
    WChX (FlockP.zcRounds hash5 r claim a b c) r.length (5 * r.length) (fun _ ↦ True) (fun _ _ ↦ True) := by
  induction r with
  | nil =>
    intro claim a b c
    simp only [FlockP.zcRounds]
    exact wchX_ret _ fun _ _ ↦ trivial
  | cons x rest ih =>
    intro claim a b c
    simp only [FlockP.zcRounds, List.length_cons]
    refine wchX_seq (wchX_sendScalar _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    refine wchX_seq (wchX_sendScalar _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    refine wchX_seq wchX_sampleW5 (fun y ↦ ?_) (by omega) (by omega)
    refine wchX_seq (ih _ _ _ _).weaken (fun _ ↦ ?_) (by omega) (by omega)
    exact wchX_ret _ fun _ _ ↦ trivial

theorem wchX_skipW (k : ℕ) (r : List E) (wit : FlockP.Wit) :
    WChX (FlockP.skipW hash5 k r wit) 1 5 (fun _ ↦ True) (fun _ _ ↦ True) := by
  unfold FlockP.skipW
  split_ifs
  · refine wchX_seq (wchX_sendScalars _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    refine wchX_seq wchX_sampleW5 (fun _ ↦ ?_) (by omega) (by omega)
    exact wchX_ret _ fun _ _ ↦ trivial
  · exact wchX_ret _ fun _ _ ↦ trivial

/-- π1-rec4's zerocheck's challenges: the skip's `z`, one per round. -/
def zc4Steps (logN k : ℕ) : ℕ := 1 + (Flock.nFixed + (logN - k - Flock.nFixed))

/-- π1-rec4's Flock's challenges: the zerocheck's, `α`, the lincheck's `11`. -/
def flock4Steps (logN k : ℕ) : ℕ := zc4Steps logN k + 1 + 11

theorem wchX_zerocheckW4 (logN k : ℕ) (c : E) (wit : FlockP.Wit) :
    WChX (zerocheckW4 hash5 logN k c wit) (zc4Steps logN k) (5 * zc4Steps logN k) (fun _ ↦ True)
      (fun _ _ ↦ True) := by
  unfold zerocheckW4
  have hlen : (Flock.fixedChallenges ++ squares c (logN - k - Flock.nFixed)).length =
      Flock.nFixed + (logN - k - Flock.nFixed) := by
    rw [List.length_append, FlockP.squares_length]
    rfl
  refine wchX_seq (wchX_skipW _ _ _) (fun st ↦ ?_) (by unfold zc4Steps; omega) (by unfold zc4Steps; omega)
  refine wchX_seq (wchX_zcRounds _ _ _ _ _) (fun zc ↦ ?_) (by rw [hlen]; unfold zc4Steps; omega)
    (by rw [hlen]; unfold zc4Steps; omega)
  refine wchX_seq (wchX_sendScalar _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
  refine wchX_seq (wchX_sendScalar _) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
  exact wchX_ret _ fun _ _ ↦ trivial

/-- **The lincheck's rounds end with an `80`-byte challenge** (nothing pending before a round). -/
theorem wendX_lcRounds : ∀ (n : ℕ) (claim : E) (wt z : Array E),
    WEndX (FlockP.lcRounds hash5 (n + 1) claim wt z) (n + 1) (5 * (n + 1))
      (fun w ↦ w.stream.size = w.absorbed + 0) (fun _ _ ↦ True)
  | 0, claim, wt, z => by
    simp only [FlockP.lcRounds, pure_bind]
    refine wendX_seq (wchX_sendScalarT _ 0) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    refine wendX_seq (wchX_sendScalarT _ (0 + 24)) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    exact wendX_then (wendX_sampleW5.pre_mono fun w hw ↦ by omega) _ (fun _ _ ↦ rfl) fun _ _ _ ↦ ⟨rfl, trivial⟩
  | n + 1, claim, wt, z => by
    rw [FlockP.lcRounds]
    refine wendX_seq (wchX_sendScalarT _ 0) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    refine wendX_seq (wchX_sendScalarT _ (0 + 24)) (fun _ ↦ ?_) (Nat.zero_le _) (Nat.zero_le _)
    refine wendX_seq wchX_sampleW5 (fun x ↦ ?_) (by omega) (by omega)
    exact wendX_then (((wendX_lcRounds n _ _ _).pre_mono fun w hw ↦ by omega).mono (by omega) (by omega)
      fun _ _ h ↦ h) (fun out w ↦ (⟨x :: out.challenges, out.claim, out.z⟩, w)) (fun _ _ ↦ rfl)
      fun _ _ _ ↦ ⟨rfl, trivial⟩

theorem wendX_frontW4 (logN : ℕ) (v : KeccakVariant) (c : E) (q : Array K) :
    WEndX (frontW4 hash5 logN v c q) (flock4Steps logN v.skip) (5 * flock4Steps logN v.skip) (fun _ ↦ True)
      (fun _ _ ↦ True) := by
  unfold frontW4
  refine wendX_seq (wchX_zerocheckW4 _ _ _ _) (fun zc ↦ ?_) (by unfold flock4Steps; omega)
    (by unfold flock4Steps; omega)
  refine wendX_seq wchX_sampleW5 (fun alpha ↦ ?_) (by unfold flock4Steps; omega) (by unfold flock4Steps; omega)
  rw [show UniKeccak.lincheckRoundsK = 10 + 1 from rfl]
  exact wendX_then (((wendX_lcRounds 10 _ _ _).pre_mono fun w hw ↦ by omega).mono
      (by unfold flock4Steps; omega) (by unfold flock4Steps; omega) fun _ _ h ↦ h)
    (fun lc w ↦ (FlockP.frontOf v zc alpha lc,
      { w with stream := w.stream ++ (lc.z.toList.flatMap scalarWire).toArray }))
    (fun _ _ ↦ rfl) fun _ _ _ ↦ ⟨rfl, trivial⟩

theorem wendX_flockProve4 (logN : ℕ) (v : KeccakVariant) (c : E) (q : Array K) :
    WEndX (flockProve4 hash5 logN v c q) (flock4Steps logN v.skip) (5 * flock4Steps logN v.skip)
      (fun _ ↦ True) (fun _ _ ↦ True) := by
  unfold flockProve4
  exact wendX_then (wendX_frontW4 logN v c q) (fun frs w ↦ ((frs.1.point, frs.2), w)) (fun _ _ ↦ rfl)
    fun _ _ _ ↦ ⟨rfl, trivial⟩

/-! ## `C2`'s tree joins Flock's last step -/

theorem commitReal_hash5 (c : Commitment) (vars : ℕ) (stack : Array K) :
    commitReal hash5 c vars stack = simulateQ iota5 (commitReal callKeccak256 c vars stack) := by
  simp only [commitReal, simulateQ_bind, simulateQ_pure, E2ECompleteness.simulateQ_commitWithH]
  rfl

theorem hashOK_commitReal5 (c : Commitment) (vars : ℕ) (stack : Array K) :
    HashOK (fun m ↦ m.length ≠ 80) (commitReal hash5 c vars stack) := by
  rw [commitReal_hash5]
  have h : HashOK (fun m : Bytes ↦ m.length = 512 ∨ m.length = 64) (commitReal callKeccak256 c vars stack) := by
    unfold commitReal
    exact E2ECompleteness.HashOK.bind (hashOK_buildTreeP _ (fun _ h ↦ Or.inl h) (fun _ h ↦ Or.inr h) _ _
      (E2ECompleteness.length_stackWordFast vars 1 stack)) fun _ ↦ E2ECompleteness.HashOK.pure _ _
  refine UniKeccakComplete.Prob.HashOK.mono (fun m hm ↦ ?_) (hashOK_iota5 (fun m hm ↦ ?_) h)
  · rcases hm with hm | ⟨i, m', hi, _, hs, _, rfl⟩
    · omega
    · rw [length_extIn]
      unfold lenB
      have : 1152921504606846976 ≤ i * 1152921504606846976 := Nat.le_mul_of_pos_left _ (by omega)
      omega
  · unfold Short lenB
    omega

theorem hc_commitReal5 (c : Commitment) (vars : ℕ) (stack : Array K) :
    HC (commitReal hash5 c vars stack) (5 * E2ECompleteness.Cost.treeCost vars) := by
  rw [commitReal_hash5]
  exact hc_iota5 (hc_commitReal c vars stack)

theorem run_midB4 (tr : Trace) (bus : List E) (w : Wr) :
    (midB4 hash5 (commitReal hash5) tr bus).run w =
      (flockProve4 hash5 (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) keccakRec4 (bus.getD 3 0)
        tr.qflock).run w >>= fun p ↦
        commitReal hash5 .c2 (((layoutsOfK tr.shape).lookup .c2).getD default).vars
            (c2DataOf tr (eqKernel (squares (bus.getD 0 0) 4)) (bus.getD 1 0) (bus.getD 2 0)).stack >>= fun c ↦
          pure ((p.1, c), { p.2 with stream := p.2.stream ++ (rootWord c.halves).toArray ++
            (scalarWire (pcsOod (((layoutsOfK tr.shape).lookup .c2).getD default).vars
              (c2DataOf tr (eqKernel (squares (bus.getD 0 0) 4)) (bus.getD 1 0) (bus.getD 2 0)).stack
              (rootOf c.halves))).toArray }) := by
  simp only [midB4, StateT.run_bind, StateT.run_lift, run_sendRoot, run_sendScalar, bind_assoc, pure_bind,
    StateT.run_pure]

/-- **From Flock to `C2`'s answer, a chain**: Flock's challenges, `C2`'s tree in its last step. -/
theorem chainX_midB4 (tr : Trace) (bus : List E) (w : Wr) :
    ChainX (fun (x : ((List E × List E) × Committed) × Wr) s ↦ x.2.state = s)
      (flock4Steps (flockLogNT tr.shape) keccakRec4.skip)
      (5 * flock4Steps (flockLogNT tr.shape) keccakRec4.skip +
        5 * E2ECompleteness.Cost.treeCost (((layoutsOfK tr.shape).lookup .c2).getD default).vars)
      w.state ((midB4 hash5 (commitReal hash5) tr bus).run w) := by
  rw [run_midB4]
  have h := wendX_flockProve4 (flockLogNT tr.shape) keccakRec4 (bus.getD 3 0) tr.qflock w trivial
  refine (h _ _ _ _ _ _ 0 0 (hashOK_commitReal5 _ _ _) (hc_commitReal5 _ _ _) ?_).mono (by omega) (by omega)
  intro p s c hp
  exact .ret _ hp.1

/-! ## The staged run -/

/-- **Stage A hashes at most `stageACost` inputs** in leanerVM's two calls (π1-rec4's IV is one query). -/
theorem hc_stageA4 (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    HC (stageA4 D input rows q) (stageACost D) := by
  have hcm : ∀ (μ : ℕ) (stack : Array K),
      HC (E2ECompleteness.commitWithH callKeccak256 μ stack) (5 * 2 ^ (μ - 6 + 1)) :=
    fun μ stack ↦ hc_of_qc (E2ECompleteness.Cost.qc_commitWithH μ stack)
  simp only [stageA4, proverA4, setupTreeOf, setupTreeKWithH, contractIvOf, seedOf, bind_assoc, pure_bind]
  refine Common.QueryCostAtMost.mono (Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦
    Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦ Common.QueryCostAtMost.bind (hc_H _) fun _ ↦
    Common.QueryCostAtMost.bind (hc_H _) fun _ ↦ Common.QueryCostAtMost.bind (hcm _ _) fun _ ↦
    hc_pure _) ?_
  simp only [stageACost, E2ECompleteness.Cost.treeCost, honestTrace_shape]
  omega

/-- π1-rec4's Flock's challenges at the deployment. -/
def flock4StepsD (D : KDeployment) : ℕ := flock4Steps (flockLogNT D.shape) keccakRec4.skip

/-- **The hashed inputs before the point draw**, at most (and one): stage A's five times, the bus draw's tails,
Flock's challenges and `C2`'s tree five times. -/
def tCache4 (D : KDeployment) : ℕ := 5 * stageACost D + 4 + (5 * flock4StepsD D + 5 * c2Cost D) + 1

/-- **The point draw's cache-hit bound**: `(flock4StepsD + 1) · tCache4 / 2^256`. -/
noncomputable def tFreshBound4 (D : KDeployment) : ℝ≥0∞ :=
  ((flock4StepsD D + 1 : ℕ) : ℝ≥0∞) * ((tCache4 D : ℝ≥0∞) / 2 ^ 256)

/-- **The point draw's query is fresh for π1-rec4**, at every deployment (a program IV of `32 … 2^16` bytes): its
input is cached when asked with probability at most `tFreshBound4 D`. -/
theorem tQueryFresh4_le (D : KDeployment) (hiv : D.programIv.length ≤ 2 ^ 16) (hpiv : 32 ≤ D.programIv.length) :
    TQueryFresh4 D (tFreshBound4 D) := by
  intro input rows q hfit _
  have hpre : (stagedU4 D input rows q).pre = (stagedU4 D input rows q).A >>= fun a ↦
      callKeccak256 ((stagedU4 D input rows q).inp a) >>= fun u ↦ tails5 ((stagedU4 D input rows q).inp a) >>=
        fun ts ↦ (stagedU4 D input rows q).B a (mkRate u ts.1 ts.2.1 ts.2.2.1 ts.2.2.2) >>= fun b ↦
          pure (b, (alphaOf4 (mkRate u ts.1 ts.2.1 ts.2.2.1 ts.2.2.2),
            challengeAt (mkRate u ts.1 ts.2.1 ts.2.2.1 ts.2.2.2).toList 1)) := by
    simp only [KStaged4.pre, rate5_eq, bind_assoc, pure_bind]
  rw [hpre, simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p hp ↦ ?_
  have hcA : HC (stagedU4 D input rows q).A (5 * stageACost D) := by
    rw [stagedU4_A_eq]
    exact hc_iota5 (hc_stageA4 D input rows q)
  have hc : CacheBound p.2 (5 * stageACost D) := (cacheBound_run hcA cacheBound_empty hp).mono (by omega)
  have hx : p.2 (.inl ((stagedU4 D input rows q).inp p.1)) = none :=
    fresh_x1 (fun m hm ↦ (cache_of_hashOK (hashA_stagedU4 D hiv hpiv input rows q) ∅ hp m hm).resolve_left
      (by simp)) (firstInput_length hfit.1 p.1.2)
  refine prHitX_top (fun (z : MidU4 × (List E × E)) s ↦ z.1.mw.2.state = s) (fun z ↦ z.1.mw.2.state)
    (fun _ _ h ↦ h) (fun c z ↦ c (.inl ((stagedU4 D input rows q).tin z.1)) ≠ none)
    (fun c z h ↦ ⟨_, h, take_digestBytes _ _⟩) (tCache4 D) (flock4StepsD D) (5 * flock4StepsD D + 5 * c2Cost D)
    (5 * stageACost D) 4 _ _ _ _ (hashOK_tails5 _) (hc_tails5 _) ?_ hc (by unfold tCache4; omega) hx
  intro u ts
  have h := chainX_midB4 (honestTrace D input rows q) (busOf (mkRate u ts.1 ts.2.1 ts.2.2.1 ts.2.2.2))
    (writerAfter4 rows p.1.2.c1 p.1.2.ood (mkRate u ts.1 ts.2.1 ts.2.2.1 ts.2.2.2))
  have hs : (writerAfter4 rows p.1.2.c1 p.1.2.ood (mkRate u ts.1 ts.2.1 ts.2.2.1 ts.2.2.2)).state = u :=
    digestOfRate_mkRate _ _ _ _ _
  rw [hs, honestTrace_shape] at h
  have h2 := ChainX.bind (Q₂ := fun (b : MidU4) s ↦ b.mw.2.state = s) (n₂ := 0) (N₂ := 0)
    (F := fun mw ↦ pure (⟨p.1.1, p.1.2, mkRate u ts.1 ts.2.1 ts.2.2.1 ts.2.2.2, mw⟩ : MidU4))
    (fun mw s hmw ↦ .ret _ hmw) h
  have h3 := ChainX.bind (Q₂ := fun (z : MidU4 × (List E × E)) s ↦ z.1.mw.2.state = s) (n₂ := 0) (N₂ := 0)
    (F := fun b ↦ pure (b, (alphaOf4 (mkRate u ts.1 ts.2.1 ts.2.2.1 ts.2.2.2),
      challengeAt (mkRate u ts.1 ts.2.1 ts.2.2.1 ts.2.2.2).toList 1))) (fun b s hb ↦ .ret _ hb) h2
  exact h3.mono (by unfold flock4StepsD; omega) (by unfold flock4StepsD c2Cost; omega)

/-! ## At the reference Keccak shape -/

theorem flock4StepsD_reference (D : KDeployment) (hD : D.shape = keccakRefShape) : flock4StepsD D = 42 := by
  unfold flock4StepsD flock4Steps zc4Steps flockLogNT
  rw [hD, UniKeccakSound.IdsNum.hSha3_ref]
  rfl

theorem tCache4_reference (D : KDeployment) (hD : D.shape = keccakRefShape) : tCache4 D ≤ 2 ^ 28 := by
  have h := Prob.tCache_reference_eq D hD
  have h1 := Prob.tSteps_reference D hD
  have h2 := flock4StepsD_reference D hD
  unfold tCache4
  unfold tCache at h
  omega

/-- **The reference bound**: `tFreshBound4 D ≤ 2^-200` (`(42 + 1) · 2^28 / 2^256 < 2^-200`). -/
theorem tFreshBound4_reference (D : KDeployment) (hD : D.shape = keccakRefShape) :
    tFreshBound4 D ≤ (2 : ℝ≥0∞)⁻¹ ^ 200 := by
  have hN : (flock4StepsD D + 1) * tCache4 D ≤ 2 ^ 56 := by
    rw [flock4StepsD_reference D hD]
    have := tCache4_reference D hD
    omega
  unfold tFreshBound4
  rw [← mul_div_assoc, ← Nat.cast_mul]
  calc (((flock4StepsD D + 1) * tCache4 D : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ ((2 ^ 56 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
        ENNReal.div_le_div_right (by exact_mod_cast hN) _
    _ = (2 : ℝ≥0∞)⁻¹ ^ 200 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.div_eq_inv_mul, ENNReal.inv_pow, mul_comm,
          show (256 : ℕ) = 200 + 56 from rfl]
        exact E2ECompleteness.two_pow_mul_inv_pow 56 200

end UniKeccakComplete.Rec4.TF4

namespace UniKeccakComplete.Rec4

/-- **The point draw's query is fresh at the reference shape** for π1-rec4: a cache hit with probability at most
`2^-200`. -/
theorem tQueryFresh4_reference (D : KDeployment) (hD : D.shape = UniKeccakSound.keccakRefShape)
    (hiv : D.programIv.length ≤ 2 ^ 16) (hpiv : 32 ≤ D.programIv.length) :
    TQueryFresh4 D ((2 : ℝ≥0∞)⁻¹ ^ 200) :=
  fun input rows q hfit hrel ↦
    (TF4.tQueryFresh4_le D hiv hpiv input rows q hfit hrel).trans (TF4.tFreshBound4_reference D hD)

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.tQueryFresh4_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.tQueryFresh4_reference
