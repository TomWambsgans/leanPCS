-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Follows `formal/EndToEnd/Completeness/E2ECompleteness/Experiment.lean`, `Staging.lean`, `HashLen.lean`, `Assemble.lean`
-- for the univariate experiment; uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the two calls answered over `π` (`keccakCallsOverQueryPermutation`) and the lazy
-- permutation after them (`simulateQ_lazy_keccakCallsOverQueryPermutation`), the duplex discipline (`DuplexVm`) and
-- the block cost (`hashBlocks`).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/ProbExp.lean`.
import UniKeccakComplete.K.ProbHyp
import UniKeccakComplete.Staged
import UniKeccakComplete.K.VerifierHDuplex
import E2ECompleteness.HashLen
import LeanVM.Protocol.ExperimentBridge

/-!
# The univariate experiment, staged

`uniCompletenessExperiment D (uniProverRP flock D)` (the setup, the honest prover, the deployed verifier over `π`) is
the two-call experiment `expW` (the same three, with Keccak-256 and Keccak-f[1600] the calls) answered by the
sponge over the random permutation (**`experiment_eq`**, from `ProverCommutes` and the verifier's and the setup's
commutations, `simulateQ_verifierWithH`, `simulateQ_setupTreesWithH`). Its staged form **`stagedU`** (a
`UniStaged`): `A` the setup and the prover before the bus challenges (`proverA`), the five answers, `C` the prover
after them (`proverC`) and the verifier (`verdictW`); `expW = (·.1) <$> (stagedU …).run` (**`expW_eq_staged`**,
from `uniProverWith_split`). Then:

* **`hashA_stagedU`**: stage A hashes `512`-byte leaves, `64`-byte nodes, the IV's `280 + |IV|` bytes and the
  seed's `80`: never `32` or `88` (`GoodL 88`);
* **`duplexVm_stagedU`**: the duplex discipline, from `ProverDuplex`, the setup's (`hOnly_setupTreesWithH`) and the
  verifier's (`disc_verifierWithH`), through the map (`duplexVm_map_iff`);
* **`cost_stagedU`**: at most `setupCost D + (N + verifierCost D S)` block calls, from `ProverCost N`,
  `ProverStreamSize S` and the verifier's count on streams of at most `S` bytes (`cost_verifierWithH`), along the
  prover's outputs (`qc_bind_support`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH)
open UniStatement
open E2ECompleteness (HashOK hashOK_callKeccak256 Disc)
open scoped ENNReal
open Common (queryPermutation)

set_option autoImplicit false

namespace UniKeccakComplete.Prob

open UniComplete UniKeccak

/-! ## The two-call experiment -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- The verdict on the prover's output: no proof is rejected, a proof goes to the deployed verifier. -/
def verdictW (D : KDeployment) (tree : LeanVM.Prover.Tree) (input : Vector UInt8 32) :
    Option KeccakProof → m Bool
  | none => pure false
  | some proof => KDeployment.verifierWithH H F D keccakMain (D.setupRoots tree) input proof

/-- **The experiment with Keccak-256 explicit**: the setup, the honest prover, the verdict. -/
def expW (flock : FlockProver m) (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    m Bool := do
  let tree ← setupTreeKWithH H F D
  let o ← uniProverWith H F flock D input rows q
  verdictW H F D tree input o

end With

variable (flock : FlockProverH) (D : KDeployment)

/-- **The experiment over the two calls commutes with simulation.** -/
theorem simulateQ_expW (hc : ProverCommutes flock D) {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl KeccakCalls r) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ impl (expW callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) =
      expW (implH impl) (implF impl) (flock (implH impl)) D input rows q := by
  simp only [expW, simulateQ_bind, simulateQ_setupTreeKWithH, hc impl]
  refine bind_congr fun tree ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => simp [verdictW]
  | some proof => simp [verdictW, simulateQ_verifierWithH]

/-- **The completeness experiment is the two-call experiment against the random permutation.** -/
theorem experiment_eq (hc : ProverCommutes flock D) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    keccakCompletenessExperiment D keccakMain (uniProverRP flock D) input rows q =
      (simulateQ keccakCallsOverRandomPermutation
        (expW callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)).run' [] := by
  rw [← simulateQ_lazy_keccakCallsOverQueryPermutation, simulateQ_expW flock D hc]
  unfold keccakCompletenessExperiment Common.runWithRandomPermutation
  congr 2
  rw [setupTreeKWith_eqH]
  unfold expW
  refine bind_congr fun tree ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => rfl
  | some proof => simp only [verdictW, verifierWith_eqH]; rfl

/-! ## The staged form -/

/-- **The prover before the bus challenges commutes with simulation** (its trees, IV and seed only hash). -/
theorem simulateQ_proverA {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ impl (proverA callKeccak256 D input rows q) = proverA (implH impl) D input rows q := by
  simp only [proverA, setupTreeOf, contractIvOf, seedOf, simulateQ_bind, simulateQ_pure,
    E2ECompleteness.simulateQ_commitWithH, simulateQ_queryH]

/-- **What the run carries to `t`**: the setup's trees, the prover before the bus challenges, the five answers, and
the stream from `γ` to `C2`'s root (`midB`'s output, the writer). -/
structure MidU where
  tree : LeanVM.Prover.Tree
  a : ProverA
  s₁ : Digest
  s₂ : Digest
  s₃ : Digest
  s₄ : Digest
  s₅ : Digest
  mw : (E × FlockOut × Committed) × Wr

/-- `midB` over the two calls, from the writer after the bus challenges. -/
def midU (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (a : ProverA) (s₁ s₂ s₃ s₄ s₅ : Digest) :
    OracleComp KeccakCalls ((E × FlockOut × Committed) × Wr) :=
  (midB callKeccak256 (commitReal callKeccak256) (flock callKeccak256) (honestTrace D input rows q)
    [chal s₁, chal s₂, chal s₃, chal s₄] (chal s₅)).run (writerAfter rows a.c1 s₁ s₂ s₃ s₄ s₅)

/-- **The experiment's stages**: `A` the setup and the prover before the bus challenges; `B` the prover from `γ` to
`C2`'s root (`midB`); `t`'s input the writer's (`tInput`), its prior Flock's point; `C` the prover after `t`
(`proverD`) and the verdict. -/
def stagedU (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : KStaged where
  α := LeanVM.Prover.Tree × ProverA
  β := MidU
  inp x := firstInput rows x.2
  A := do
    let tree ← setupTreeKWithH callKeccak256 callKeccakF1600 D
    let a ← proverA callKeccak256 D input rows q
    return (tree, a)
  B x s₁ s₂ s₃ s₄ s₅ := do
    let m ← midU flock D input rows q x.2 s₁ s₂ s₃ s₄ s₅
    return ⟨x.1, x.2, s₁, s₂, s₃, s₄, s₅, m⟩
  tin b := tInput b.mw.2
  pr b := b.mw.1.2.1.point
  C b st := do
    let o ← proverD callKeccak256 callKeccakF1600 D input rows q b.a b.s₁ b.s₂ b.s₃ b.s₄ b.s₅ b.mw st
    verdictW callKeccak256 callKeccakF1600 D b.tree input o

/-- **The two-call experiment is the staged run's verdict.** -/
theorem expW_eq_staged (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    expW callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q =
      (fun z ↦ z.1.1) <$> (stagedU flock D input rows q).run := by
  simp only [expW, uniProverWith_split, proverC_split, KStaged.run, KStaged.tail, stagedU, midU, staged5,
    map_bind, map_pure, bind_assoc, pure_bind, bind_pure]

/-- **The staged experiment**, against the random permutation. -/
theorem experiment_staged (hc : ProverCommutes flock D) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) :
    keccakCompletenessExperiment D keccakMain (uniProverRP flock D) input rows q =
      (fun z ↦ z.1.1) <$>
        (simulateQ keccakCallsOverRandomPermutation (stagedU flock D input rows q).run).run' [] := by
  rw [experiment_eq flock D hc, expW_eq_staged, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map,
    Functor.map_map, Functor.map_map]

/-- **`midB` over the two calls commutes with simulation**, given Flock's prover's. -/
theorem simulateQ_midU (hf : FlockSimCommutes flock) {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl KeccakCalls r) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (a : ProverA)
    (s₁ s₂ s₃ s₄ s₅ : Digest) :
    simulateQ impl (midU flock D input rows q a s₁ s₂ s₃ s₄ s₅) =
      (midB (implH impl) (commitReal (implH impl)) (flock (implH impl)) (honestTrace D input rows q)
        [chal s₁, chal s₂, chal s₃, chal s₄] (chal s₅)).run (writerAfter rows a.c1 s₁ s₂ s₃ s₄ s₅) := by
  simp only [midU, midB, StateT.run_bind, run_sampleW, StateT.run_lift, run_sendRoot, commitReal, bind_assoc,
    pure_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, simulateQ_queryH, hf impl,
    E2ECompleteness.simulateQ_commitWithH]

/-- **`t`'s freshness** (a named hypothesis, not proved here): in the two-call random-oracle model, `t`'s input
(`tInput`, the writer's state and the bytes since the last challenge, `C2`'s root word) has been hashed before its
query with probability at most `εt`. It is not fresh by its length (`64` bytes when Flock's prover ends with a
challenge, a Merkle node's length): an earlier node query has the same input only if its left child is the writer's
state, Flock's last challenge's answer, so the bound needs Flock's prover's chain (that its last query is fresh, of
another length than a Merkle node's) and the Merkle digests computed after it (`C2`'s tree). -/
def TQueryFresh (εt : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation KeccakFlock.keccakFlockSpec rows input q →
    Pr{let p ← (simulateQ E2ECompleteness.ro (stagedU flock D input rows q).pre).run ∅}[
      p.2 (.inl ((stagedU flock D input rows q).tin p.1.1)) ≠ none] ≤ εt

/-! ## What stage A hashes -/

theorem len_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  have : digestBytes d = LeanVM.Rpm.lanesBytes d.toList := rfl
  rw [this, LeanVM.Rpm.length_lanesBytes]
  simp

theorem name_length : name.length = 16 := by decide +kernel

theorem ivTag_length : ivTag.length = 16 := by decide +kernel

theorem shapeBytes_length (s : UniStatement.Shape) : (shapeBytes s).length = 8 := by simp [shapeBytes]

theorem layoutWord_length (s : UniStatement.Shape) (code vars placed : ℕ) : (layoutWord s code vars placed).length = 32 := by
  simp [layoutWord, shapeBytes_length]

theorem layoutWordsK_length (s : UniStatement.Shape) : (layoutWordsK s).flatten.length = 160 := by
  simp [layoutWordsK, layoutWord_length]

/-- Lengths other than the bus chain's. -/
theorem goodL_of_length {m : Bytes} (h : m.length = 512 ∨ m.length = 64 ∨ m.length = 80 ∨ 280 ≤ m.length) :
    GoodL 88 m := by
  refine ⟨?_, ?_⟩ <;> omega

/-- A Merkle tree of rows of `64` words hashes `512`-byte leaves and `64`-byte nodes (`E2ECompleteness.HashLen`'s
`hashOK_buildTree`, at `GoodL 88`). -/
theorem hashOK_buildTree (height : ℕ) (word : LeanVM.Protocol.Compile.Word)
    (hw : ∀ p, (word p).length = 64) :
    HashOK (GoodL 88) (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) := by
  unfold LeanVM.Prover.buildTreeWithHash
  refine E2ECompleteness.HashOK.bind ?_ fun leaves ↦ E2ECompleteness.HashOK.bind ?_ fun _ ↦
    E2ECompleteness.HashOK.pure _ _
  · unfold LeanVM.Prover.leafDigestsWithHash
    refine E2ECompleteness.HashOK.arrayMapM _
      (fun i ↦ hashOK_callKeccak256 (goodL_of_length (Or.inl ?_))) _
    rw [E2ECompleteness.length_flatMap_kBytes, hw]
  · suffices h : ∀ k (level : Array Digest),
        HashOK (GoodL 88) (LeanVM.Prover.levelsWithHash callKeccak256 k level) from h _ _
    intro k
    induction k with
    | zero => intro level; exact E2ECompleteness.HashOK.pure _ _
    | succ k ih =>
      intro level
      unfold LeanVM.Prover.levelsWithHash
      refine E2ECompleteness.HashOK.bind ?_ fun up ↦ E2ECompleteness.HashOK.bind (ih up) fun _ ↦
        E2ECompleteness.HashOK.pure _ _
      unfold LeanVM.Prover.parentsWithHash
      refine E2ECompleteness.HashOK.arrayMapM _
        (fun j ↦ hashOK_callKeccak256 (goodL_of_length (Or.inr (Or.inl ?_)))) _
      rw [List.length_append, E2ECompleteness.length_digestBytes, E2ECompleteness.length_digestBytes]

theorem hashOK_commitWithH (μ : ℕ) (stack : Array K) :
    HashOK (GoodL 88) (E2ECompleteness.commitWithH callKeccak256 μ stack) :=
  hashOK_buildTree _ _ (E2ECompleteness.length_stackWordFast μ 1 stack)

/-- **Stage A hashes nothing of the bus chain's lengths.** -/
theorem hashA_stagedU (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    HashOK (GoodL 88) (stagedU flock D input rows q).A := by
  simp only [stagedU, proverA, setupTreeOf, setupTreeKWithH, contractIvOf, seedOf, bind_assoc, pure_bind]
  refine E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_callKeccak256 (goodL_of_length (Or.inr (Or.inr (Or.inr ?_))))) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_callKeccak256 (goodL_of_length (Or.inr (Or.inr (Or.inl ?_))))) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦ E2ECompleteness.HashOK.pure _ _
  · simp only [List.length_append, ivTag_length, len_digestBytes, shapeBytes_length, layoutWordsK_length]
    omega
  · simp [name_length, len_digestBytes, honestTrace]

/-! ## The duplex discipline -/

/-- The duplex discipline sees only the queries: a map keeps it. -/
theorem duplexVm_map_iff {α β : Type} (f : α → β) (X : OracleComp KeccakCalls α) (h : List KeccakState) :
    DuplexVm (f <$> X) h ↔ DuplexVm X h := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a =>
    rw [map_pure]
    exact ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩
  | query_bind t k ih =>
    rw [map_bind, duplexVm_query_bind, duplexVm_query_bind]
    rcases t with x | x
    · exact forall_congr' fun u ↦ ih u h
    · exact and_congr Iff.rfl (forall_congr' fun y ↦ ih y _)

/-- **The staged run follows the duplex discipline.** -/
theorem duplexVm_stagedU (hdup : ProverDuplex flock D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    DuplexVm (stagedU flock D input rows q).run [] := by
  have hd : Disc (expW callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) := by
    unfold expW
    refine (E2ECompleteness.disc_of_hOnly (hOnly_setupTreeKWithH D)).bind fun tree ↦
      (hdup input rows q hfit hrel).bind fun o ↦ ?_
    cases o with
    | none => exact E2ECompleteness.disc_pure _
    | some π => exact disc_verifierWithH D keccakMain _ input π
  have h := (duplexVm_iff_duplexP _ _).mpr (hd [])
  rwa [expW_eq_staged, duplexVm_map_iff] at h

/-! ## The block count -/

/-- **A bind's cost along the outputs**: the continuation bounded only on the prefix's possible outputs. -/
theorem qc_bind_support {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    {a b : ℕ} (ha : Common.QueryCostAtMost X hashBlocks a)
    (hb : ∀ x ∈ support X, Common.QueryCostAtMost (f x) hashBlocks b) :
    Common.QueryCostAtMost (X >>= f) hashBlocks (a + b) := by
  induction X using OracleComp.inductionOn generalizing a with
  | pure x =>
    rw [pure_bind]
    exact (hb x (by simp)).mono (Nat.le_add_left _ _)
  | query_bind t k ih =>
    rw [bind_assoc]
    rw [Common.isWeightBound_query_bind_iff] at ha ⊢
    refine ⟨le_trans ha.1 (Nat.le_add_right _ _), fun u ↦ ?_⟩
    have h := ih u (ha.2 u) fun x hx ↦ hb x (by
      rw [mem_support_bind_iff]
      exact ⟨u, by simp, hx⟩)
    exact h.mono (by have := ha.1; omega)

/-- **The staged run's block count**: the setup's `Ns`, the prover's `N`, the verifier's `Nv` on streams of at most
`S` bytes. -/
theorem cost_stagedU {Ns N S Nv : ℕ}
    (hset : Common.QueryCostAtMost (setupTreeKWithH callKeccak256 callKeccakF1600 D) hashBlocks Ns)
    (hver : ∀ roots input (π : KeccakProof), π.stream.size ≤ S →
      Common.QueryCostAtMost (KDeployment.verifierWithH callKeccak256 callKeccakF1600 D keccakMain roots input π)
        hashBlocks Nv)
    (hcost : ProverCost flock D N) (hstream : ProverStreamSize flock D S)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    Common.QueryCostAtMost (stagedU flock D input rows q).run hashBlocks (Ns + (N + Nv)) := by
  have h : Common.QueryCostAtMost (expW callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q)
      hashBlocks (Ns + (N + Nv)) := by
    unfold expW
    refine Common.QueryCostAtMost.bind hset fun tree ↦ ?_
    refine qc_bind_support (hcost input rows q hfit hrel) fun o ho ↦ ?_
    cases o with
    | none => trivial
    | some π => exact hver _ input π (hstream input rows q hfit hrel π ho)
  rw [expW_eq_staged] at h
  exact (isQueryBound_map_iff _ _ _ _ _).1 h

end UniKeccakComplete.Prob
