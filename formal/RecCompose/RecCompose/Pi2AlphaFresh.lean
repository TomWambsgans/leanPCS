-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `α`'s freshness at π2's staged run (`Pi2ProbStaged`'s
-- `pi2Staged`, `stageA`) for π1-rec4's prover (`Pi2P1`'s named facts), from `Pi2AlphaLen` (the census before `σ`'s hash),
-- `Pi2AlphaChain` (the chain from `σ` to `α`) and `Pi2AlphaSupport` (`α`'s input's length on every outcome); uses
-- leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two
-- calls, their lazy random oracles, the block cost.
import RecCompose.Pi2AlphaLen
import RecCompose.Pi2AlphaSupport

/-!
# `α`'s input is fresh at π1-rec4's prover (π2v4)

**`alphaFresh_of`**: in the two-call random-oracle model, after stage A of π2's staged run at a π1 prover `P1k` of at
most `2^47` block calls (`Pi1Cost`) hashing only inputs shorter than `2^26` bytes (`Pi1HashShort`), `α`'s input is
cached while π1-rec4's graph accepted (`GAccA`) with probability at most

  `alphaBound = 4 · (2 · setupR + 2^47 + 3 · gOpen + 4) / 2^256 ≤ 2^-204` (**`alphaBound_le`**).

The proof: with `GAccA`, `α`'s input is the writer's `88` bytes (`gAcc_length`), so it suffices to bound their being
cached (**`prA_le`**). Stage A is the setup, π1-rec4's prover, its graph, the setup again (every input shorter than
`2^26` bytes: `Pi2AlphaLen` and `Pi1HashShort`, at most `2 · setupR + 2^47 + 3 · gOpen` hashed inputs), then π2's IV,
its seed (`80` bytes and the frame words: `176` on an honest witness, `80` otherwise, `frameWords_choice`) and `W`'s
tree: `Pi2AlphaChain.chain_le` from `σ`'s `2^26` bytes, not cached.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF)
open E2ECompleteness (ro runAt Cache HashOK cache_of_hashOK length_digestBytes)
open UniComplete (Wr WrM)
open UniKeccakComplete (Morph)
open UniKeccakComplete.Prob.TFresh (HC hc_of_qc CacheBound cacheBound_empty cacheBound_run take_digestBytes)
open Pi2S Pi2K Pi2P Pi2E Pi2G Pi2G.Cost2
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The cache's invariant before `σ` -/

/-- **Every cached hash input is shorter than `σ`'s.** -/
def CacheShort (c : Cache) : Prop := ∀ m, c (.inl m) ≠ none → Pi2A.Short m

theorem cacheShort_empty : CacheShort ∅ := fun _ h ↦ absurd rfl h

/-- A run of a computation hashing short inputs keeps the cache short, and adds at most its hash count. -/
theorem inv_run {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ} (hX : HashOK Pi2A.Short X) (hn : HC X n)
    {c : Cache} {K : ℕ} (hc : CacheShort c) (hK : CacheBound c K) {z : α × Cache}
    (hz : z ∈ support ((simulateQ ro X).run c)) : CacheShort z.2 ∧ CacheBound z.2 (K + n) :=
  ⟨fun m hm ↦ (cache_of_hashOK hX c hz m hm).elim (hc m) id, cacheBound_run hn hK hz⟩

/-! ## `pre2`'s writer on every outcome -/

theorem runAt_pre2 (Ht : List UInt8 → Digest) (Ft : KeccakState → KeccakState) (G : RecPiop.Circuit E)
    (reads : List Read) (values : List PublicValue) (w : ℕ → K) (w0 : Wr) :
    runAt Ht Ft ((pre2 callKeccak256 G (WhirBridge.Pcs.oodPointM callKeccak256) reads values w).run w0) =
      Id.run ((pre2 (m := Id) (Pure.pure ∘ Ht) G (WhirBridge.Pcs.oodPointM (Pure.pure ∘ Ht)) reads values w).run
        w0) := by
  have h := wr_pre2 (Morph.sim (LeanVM.Protocol.Compile.totalImpl Ht Ft)) callKeccak256 G
    (WhirBridge.Pcs.oodPointM callKeccak256) reads values w
  simp only [app_oodPointM] at h
  rw [Morph.sim_H] at h
  have h2 := congrArg (fun x ↦ StateT.run x w0) h
  simp only [Morph.wr_run] at h2
  exact h2

/-! ## `W`'s tree -/

/-- A Merkle tree of rows of `64` words hashes `512`-byte leaves and `64`-byte nodes: nothing of `88` bytes. -/
theorem hashOK_buildTree88 (height : ℕ) (word : LeanVM.Protocol.Compile.Word) (hw : ∀ p, (word p).length = 64) :
    HashOK (fun m ↦ m.length ≠ 88) (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) := by
  unfold LeanVM.Prover.buildTreeWithHash
  refine E2ECompleteness.HashOK.bind ?_ fun leaves ↦ E2ECompleteness.HashOK.bind ?_ fun _ ↦
    E2ECompleteness.HashOK.pure _ _
  · unfold LeanVM.Prover.leafDigestsWithHash
    refine E2ECompleteness.HashOK.arrayMapM _ (fun i ↦ E2ECompleteness.hashOK_callKeccak256 ?_) _
    show _ ≠ 88
    rw [E2ECompleteness.length_flatMap_kBytes, hw]
    norm_num
  · suffices h : ∀ k (level : Array Digest),
        HashOK (fun m ↦ m.length ≠ 88) (LeanVM.Prover.levelsWithHash callKeccak256 k level) from h _ _
    intro k
    induction k with
    | zero => intro level; exact E2ECompleteness.HashOK.pure _ _
    | succ k ih =>
      intro level
      unfold LeanVM.Prover.levelsWithHash
      refine E2ECompleteness.HashOK.bind ?_ fun up ↦ E2ECompleteness.HashOK.bind (ih up) fun _ ↦
        E2ECompleteness.HashOK.pure _ _
      unfold LeanVM.Prover.parentsWithHash
      refine E2ECompleteness.HashOK.arrayMapM _ (fun j ↦ E2ECompleteness.hashOK_callKeccak256 ?_) _
      show _ ≠ 88
      rw [List.length_append, length_digestBytes, length_digestBytes]
      norm_num

theorem hashOK_commitWithH88 (μ : ℕ) (stack : Array K) :
    HashOK (fun m ↦ m.length ≠ 88) (E2ECompleteness.commitWithH callKeccak256 μ stack) :=
  hashOK_buildTree88 _ _ (E2ECompleteness.length_stackWordFast μ 1 stack)

/-! ## Stage A -/

/-- `α`'s input before `fixLen`. -/
abbrev rawInp (a : StA) : List UInt8 := UniKeccakComplete.Prob.tInput a.wr

theorem rawInp_start : (UniKeccakComplete.Prob.tInput (Wr.start default)).length = 32 := by
  simp [UniKeccakComplete.Prob.tInput, Wr.start, length_digestBytes]

set_option maxHeartbeats 1600000 in
/-- **Stage A caches its writer's `88`-byte input** with probability at most `4 · (K + 4) / 2^256`, `K` the hash count
before `σ`, for a π1 prover hashing short inputs. -/
theorem prA_le {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) (input : Vector UInt8 32) {K₂ : ℕ}
    (hpS : HashOK Pi2A.Short P1k) (hpC : HC P1k K₂) :
    Pr{let p ← (simulateQ ro (stageA callKeccak256 callKeccakF1600 D C Fa P1k input)).run ∅}[
      p.2 (.inl (rawInp p.1)) ≠ none ∧ (rawInp p.1).length = 88] ≤
      4 * (((0 + setupR + K₂ + 3 * gOpen + setupR + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  classical
  have hsS := Pi2A.hashOK_setupTreesWithH2 D
  have hsC : HC (Pi2H.setupTreesWithH callKeccak256 callKeccakF1600 D) setupR :=
    hc_of_qc ((qc_setupTreesWithH2 hD).mono (setup2_le hD))
  unfold stageA
  rw [simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p₀ hp₀ ↦ ?_
  obtain ⟨hs₀, hb₀⟩ := inv_run hsS hsC cacheShort_empty cacheBound_empty hp₀
  rw [simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p₁ hp₁ ↦ ?_
  obtain ⟨hs₁, hb₁⟩ := inv_run hpS hpC hs₀ hb₀ hp₁
  obtain ⟨o, c₁⟩ := p₁
  rcases o with _ | p1
  · -- π1's prover returned none: the writer is the start's.
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hev ↦ ?_) zero_le
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    have := hev.2
    rw [rawInp, rawInp_start] at this
    exact absurd this (by norm_num)
  · dsimp only
    rw [simulateQ_bind, StateT.run_bind]
    refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p₂ hp₂ ↦ ?_
    obtain ⟨hs₂, hb₂⟩ := inv_run (Pi2A.hashOK_graph D _ input p1)
      (hc_of_qc (qc_pi1GraphVerifierWithH D _ input p1)) hs₁ hb₁ hp₂
    rw [simulateQ_bind, StateT.run_bind]
    refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p₃ hp₃ ↦ ?_
    obtain ⟨hs₃, hb₃⟩ := inv_run hsS hsC hs₂ hb₂ hp₃
    obtain ⟨tr, c₃⟩ := p₃
    dsimp only at hs₃ hb₃ ⊢
    set vw := pi2Choice D C.G Fa.pubOf tr.roots input p1.stream (pi1ClaimsOf D tr.roots.pi1 input p1.stream) with hvw
    have hfw := frameWords_choice hD C Fa tr.roots input p1.stream (pi1ClaimsOf D tr.roots.pi1 input p1.stream)
    rw [← hvw] at hfw
    have hc : (D.circuitAt tr.roots.pi1).circuit = Data.circuit := by rw [RecDeployment.circuitAt, hD.1]
    have hn : (D.circuitAt tr.roots.pi1).n = 2 ^ 24 := by rw [Pi2Circuit.n, hc]; rfl
    simp only [Pi2H.ivOfH, Pi2H.digestWithH, Pi2H.ivWithH, bind_assoc, pure_bind]
    have hσ : ((List.range (D.circuitAt tr.roots.pi1).n).flatMap fun i ↦
        (le64 ((D.circuitAt tr.roots.pi1).sigma i)).take 4).length = 2 ^ 26 := by
      rw [Pi2G.Cost2.length_flatMap_const _ 4 (fun i ↦ by simp [length_le64]), List.length_range, hn]
      norm_num
    have hκ : ((List.range (D.circuitAt tr.roots.pi1).n).flatMap fun i ↦
        le64 ((D.circuitAt tr.roots.pi1).kappa i).lane.toNat).length = 2 ^ 27 := by
      rw [Pi2G.Cost2.length_flatMap_const _ 8 (fun i ↦ length_le64 _), List.length_range, hn]
      norm_num
    have h0 : c₃ (.inl ((List.range (D.circuitAt tr.roots.pi1).n).flatMap fun i ↦
        (le64 ((D.circuitAt tr.roots.pi1).sigma i)).take 4)) = none := by
      by_contra h
      have := hs₃ _ h
      unfold Pi2A.Short at this
      omega
    refine (Pi2C.chain_le _ _
      (fun σ κ ↦ (D.circuitAt tr.roots.pi1).circuit.encoding ++ digestBytes σ ++ digestBytes κ)
      (fun d ↦ ivTag ++ D.pi1IvAt tr.roots.pi1 ++ digestBytes tr.roots.pi2 ++ UniKeccak.elementBytes24 tr.roots.pi2Ood ++
        digestBytes d ++ [(D.circuitAt tr.roots.pi1).circuit.logN.toUInt8])
      (fun iv ↦ RecStatement.name ++ digestBytes iv ++ input.toList ++ frameWordsOf vw.1)
      (by rw [hκ]; norm_num) (by rw [hσ]; norm_num) (fun σ κ ↦ ⟨?_, ?_⟩) (fun d ↦ ⟨?_, ?_⟩)
      (Ls := 80 + (frameWordsOf vw.1).length) (by omega) (by omega) (fun iv ↦ ⟨?_, ?_⟩)
      _ rawInp ?_ ?_ c₃ hb₃ h0).trans ?_
    · simp only [List.length_append, hc, encoding_length, length_digestBytes]
    · rw [hc, List.append_assoc, List.drop_left' encoding_length]
      exact take_digestBytes _ _
    · simp only [List.length_append, ivTag_length, RecDeployment.pi1IvAt, length_pi1Iv, length_digestBytes,
        UniKeccakComplete.Cost.elementBytes24_length, List.length_singleton]
    · have e : ivTag ++ D.pi1IvAt tr.roots.pi1 ++ digestBytes tr.roots.pi2 ++ UniKeccak.elementBytes24 tr.roots.pi2Ood ++
          digestBytes d ++ [(D.circuitAt tr.roots.pi1).circuit.logN.toUInt8] =
          (ivTag ++ D.pi1IvAt tr.roots.pi1 ++ digestBytes tr.roots.pi2 ++ UniKeccak.elementBytes24 tr.roots.pi2Ood) ++
            (digestBytes d ++ [(D.circuitAt tr.roots.pi1).circuit.logN.toUInt8]) := by
        simp only [List.append_assoc]
      rw [e, List.drop_left' (by simp only [List.length_append, ivTag_length, RecDeployment.pi1IvAt, length_pi1Iv,
        length_digestBytes, UniKeccakComplete.Cost.elementBytes24_length])]
      exact take_digestBytes _ _
    · simp only [List.length_append, name_length, length_digestBytes, Vector.length_toList]
      try omega
    · rw [List.append_assoc, List.append_assoc, List.drop_left' name_length]
      exact take_digestBytes _ _
    · -- `W`'s tree hashes nothing of `88` bytes.
      intro seed
      refine E2ECompleteness.HashOK.bind ?_ fun x ↦ ?_
      · obtain ⟨s', h, -, -⟩ := run_sendPublic ((D.circuitAt tr.roots.pi1).circuit.reads.zip vw.1) (Wr.start seed)
        unfold pre2
        simp only [StateT.run_bind, h, pure_bind, StateT.run_lift, bind_assoc, run_sendRoot2, run_sendScalar2,
          StateT.run_pure]
        exact E2ECompleteness.HashOK.bind (hashOK_commitWithH88 _ _) fun _ ↦
          E2ECompleteness.HashOK.bind (Pi2A.hashOK_oodPointM _ _ fun j ↦ by
            show (WhirBridge.Pcs.oodInput _ _ j).length ≠ 88
            rw [Pi2A.oodInput_length]
            decide) fun _ ↦ E2ECompleteness.HashOK.pure _ _
      · obtain ⟨_, _⟩ := x
        exact E2ECompleteness.HashOK.pure _ _
    · -- the input begins with the seed.
      intro seed c z hz _
      have e := Pi2C.runAt_read hz
      rw [← e]
      generalize Pi2C.readH z.2 = Ht
      generalize Pi2C.readF z.2 = Ft
      unfold runAt
      rw [simulateQ_bind]
      generalize hy : simulateQ (LeanVM.Protocol.Compile.totalImpl Ht Ft)
        ((pre2 callKeccak256 (C.G tr.roots) (WhirBridge.Pcs.oodPointM callKeccak256)
          (D.circuitAt tr.roots.pi1).circuit.reads vw.1 vw.2).run (Wr.start seed)) = y
      obtain ⟨ws, wr⟩ := y
      have hwr : wr = (Id.run ((pre2 (m := Id) (Pure.pure ∘ Ht) (C.G tr.roots) (WhirBridge.Pcs.oodPointM (Pure.pure ∘ Ht))
          (D.circuitAt tr.roots.pi1).circuit.reads vw.1 vw.2).run (Wr.start seed))).2 := by
        rw [← runAt_pre2 Ht Ft]
        unfold runAt
        rw [hy]
      obtain ⟨hh, ho, hw⟩ := pre2_writer (C.G tr.roots) (WhirBridge.Pcs.oodPointM (Pure.pure ∘ Ht))
        (D.circuitAt tr.roots.pi1).circuit.reads vw.1 vw.2 Ht (Wr.start seed)
      show (UniKeccakComplete.Prob.tInput wr).take 32 = digestBytes seed
      rw [hwr, hw, tInput_start_append]
      exact take_digestBytes _ _
    · exact le_rfl

/-! ## At π1-rec4's prover -/

/-- **`α`'s bound**: four links, each at most the hashed inputs before `σ` (the setup twice, π1-rec4's prover, its graph)
and four, over `2^256`. -/
noncomputable def alphaBound : ℝ≥0∞ := 4 * (((0 + setupR + 2 ^ 47 + 3 * gOpen + setupR + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256)

theorem alphaK_le : 0 + setupR + 2 ^ 47 + 3 * gOpen + setupR + 4 ≤ 2 ^ 50 := by
  unfold setupR gOpen UniKeccakComplete.Cost.openCost
  norm_num [E2ECompleteness.Cost.treeCost, E2ECompleteness.Cost.vOpen, LeanVM.Protocol.Verifier.whirBound]

/-- **`α`'s bound in bits**: at most `2^-204`. -/
theorem alphaBound_le : alphaBound ≤ (2 : ℝ≥0∞)⁻¹ ^ 204 := by
  unfold alphaBound
  have h1 : ((0 + setupR + 2 ^ 47 + 3 * gOpen + setupR + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ (2 : ℝ≥0∞)⁻¹ ^ 206 := by
    calc ((0 + setupR + 2 ^ 47 + 3 * gOpen + setupR + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256
        ≤ ((2 ^ 50 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (206 + 50) := by
          rw [ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow, mul_comm]
          gcongr
          exact_mod_cast alphaK_le
      _ = (2 : ℝ≥0∞)⁻¹ ^ 206 := by
          rw [Nat.cast_pow, Nat.cast_ofNat]
          exact E2ECompleteness.two_pow_mul_inv_pow 50 206
  calc 4 * (((0 + setupR + 2 ^ 47 + 3 * gOpen + setupR + 4 : ℕ) : ℝ≥0∞) / 2 ^ 256)
      ≤ 2 ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ (204 + 2) := by
        rw [show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num]
        gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ 204 := E2ECompleteness.two_pow_mul_inv_pow 2 204

theorem alphaBound_le201 : alphaBound ≤ (2 : ℝ≥0∞)⁻¹ ^ 201 :=
  alphaBound_le.trans (E2ECompleteness.inv_pow_le_inv_pow (by norm_num))

/-- **`α`'s input is fresh while the graph accepts**, for a π1 prover hashing short inputs (`HashOK Short`) in at most
`2^47` hash queries: in the two-call random-oracle model, after stage A of π2's staged run, `α`'s input is cached and
π1-rec4's graph accepted with probability at most `alphaBound ≤ 2^-204`. -/
theorem alphaFresh_of {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (P1k : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) (input : Vector UInt8 32)
    (hshort : HashOK Pi2A.Short P1k) (hc : HC P1k (2 ^ 47)) :
    Pr{let p ← (simulateQ ro (pi2Staged D C Fa P1k input).A).run ∅}[
      p.2 (.inl ((pi2Staged D C Fa P1k input).inp p.1)) ≠ none ∧ GAccA p.1] ≤ alphaBound := by
  refine (prEvent_mono_of_support _ _ (fun p ↦ p.2 (.inl (rawInp p.1)) ≠ none ∧ (rawInp p.1).length = 88)
    fun p hp hev ↦ ?_).trans ?_
  · have hl := gAcc_length C Fa input hD P1k hp hev.2
    have e : (pi2Staged D C Fa P1k input).inp p.1 = rawInp p.1 := by
      show fixLen 88 (UniKeccakComplete.Prob.tInput p.1.wr) = _
      unfold fixLen
      simp only [hl, ↓reduceIte]
    have h1 := hev.1
    rw [e] at h1
    exact ⟨h1, hl⟩
  · exact prA_le hD C Fa P1k input hshort hc

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.prA_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.prA_le

/-- info: 'RecCompose.Pi2Sim.alphaFresh_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.alphaFresh_of

/-- info: 'RecCompose.Pi2Sim.alphaBound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.alphaBound_le
