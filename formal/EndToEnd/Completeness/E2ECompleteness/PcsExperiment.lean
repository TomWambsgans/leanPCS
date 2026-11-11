-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/Experiment.lean` (the previous protocol's coins) to the PCS claims'
-- coins. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the two calls answered over `π` (`keccakCallsOverQueryPermutation`) and the lazy
-- permutation after them (`simulateQ_lazy_keccakCallsOverQueryPermutation`).
import E2ECompleteness.PcsWithHash
import LeanVM.Protocol.ExperimentBridge

/-!
# The completeness experiment, coins first, with two calls (the PCS claims)

`PcsQuotient.completenessExperiment` runs, against the lazily sampled permutation, the setup, the
coins (`sampleCoins`: `32 + 6` uniform words), the honest prover and the verifier. Here:

* **the coins are drawn first** (`completenessExperiment_eq`): the coins touch no edge of the
  permutation, and two draws of countable outcomes commute in distribution (the raw coin words
  `RawCoins` in place of the function-typed coins);
* **with two calls** (`experimentBody_eq`): for fixed coins the setup, the prover and the verifier
  over `π` are the two-call experiment `expH` answered over `π`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open PcsQuotient
open Common (RandomPermutationOracles lazyRandomPermutationOracles runWithRandomPermutation
  queryPermutation PermutationEdges)
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-! ## The coins -/

/-- The raw coins: the `32 + 6` words. -/
abbrev RawCoins : Type := List UInt64

/-- The coins of the raw words (`sampleCoins`). -/
def coinsOf (w : RawCoins) : Coins :=
  let word (k : ℕ) : K := K.ofLane (w.getD k 0)
  ⟨fun r ↦ word r.val, fun e i ↦ word (randomWords + freeBlind * e.val + i.val)⟩

/-- The raw coins' draw. -/
def rawCoins : OracleComp RandomPermutationOracles RawCoins :=
  (List.range (randomWords + 3 * freeBlind)).mapM fun _ ↦ coinWord

theorem sampleCoins_eq : sampleCoins = coinsOf <$> rawCoins := by
  simp only [sampleCoins, rawCoins, bind_pure_comp]
  rfl

/-! ## Coins touch no edge -/

/-- `oa` makes coin queries only. -/
def CoinsOnly {α : Type} (oa : OracleComp RandomPermutationOracles α) : Prop :=
  oa.IsQueryBound () (fun t _ ↦ t.isLeft = true) (fun _ _ ↦ ())

theorem CoinsOnly.bind {α β : Type} {oa : OracleComp RandomPermutationOracles α}
    {f : α → OracleComp RandomPermutationOracles β} (h₁ : CoinsOnly oa) (h₂ : ∀ a, CoinsOnly (f a)) :
    CoinsOnly (oa >>= f) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using h₂ a
  | query_bind t k ih =>
    rw [bind_assoc]
    exact (isQueryBound_query_bind_iff _ _ _ _ _).2
      ⟨((isQueryBound_query_bind_iff _ _ _ _ _).1 h₁).1,
        fun u ↦ ih u (((isQueryBound_query_bind_iff _ _ _ _ _).1 h₁).2 u)⟩

theorem coinsOnly_pure {α : Type} (a : α) :
    CoinsOnly (pure a : OracleComp RandomPermutationOracles α) := trivial

theorem coinsOnly_coinWord : CoinsOnly coinWord := by
  unfold coinWord
  refine CoinsOnly.bind ?_ fun _ ↦ coinsOnly_pure _
  exact (isQueryBound_query_iff (spec := RandomPermutationOracles) (.inl _) () _ _).2 rfl

theorem coinsOnly_mapM {α β : Type} (f : α → OracleComp RandomPermutationOracles β)
    (hf : ∀ a, CoinsOnly (f a)) : ∀ l : List α, CoinsOnly (l.mapM f)
  | [] => coinsOnly_pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact CoinsOnly.bind (hf a) fun _ ↦ CoinsOnly.bind (coinsOnly_mapM f hf l)
      fun _ ↦ coinsOnly_pure _

theorem coinsOnly_rawCoins : CoinsOnly rawCoins :=
  coinsOnly_mapM _ (fun _ ↦ coinsOnly_coinWord) _

theorem run_lazy_coin (n : ℕ) (E : PermutationEdges KeccakState) :
    (lazyRandomPermutationOracles (.inl n)).run E =
      (fun u ↦ (u, E)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := by
  simp [lazyRandomPermutationOracles, StateT.run_monadLift]

/-- Coin queries only: the run from any edges is the run from any other, the edges kept. -/
theorem run_lazy_of_coinsOnly' {α : Type} (oa : OracleComp RandomPermutationOracles α)
    (h : CoinsOnly oa) (E E' : PermutationEdges KeccakState) :
    (simulateQ lazyRandomPermutationOracles oa).run E =
      (fun p ↦ (p.1, E)) <$> (simulateQ lazyRandomPermutationOracles oa).run E' := by
  induction oa using OracleComp.inductionOn generalizing E E' with
  | pure a => simp
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (isQueryBound_query_bind_iff _ _ _ _ _).1 h
    rcases t with n | q
    · simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self,
        OracleQuery.cont_query, StateT.run_bind, run_lazy_coin, bind_map_left, map_bind]
      exact bind_congr fun u ↦ ih u (hk u) E E'
    · exact absurd ht (by simp)

/-- **Coins touch no edge**. -/
theorem run_lazy_of_coinsOnly {α : Type} (oa : OracleComp RandomPermutationOracles α)
    (h : CoinsOnly oa) (E : PermutationEdges KeccakState) :
    (simulateQ lazyRandomPermutationOracles oa).run E =
      (fun a ↦ (a, E)) <$> (simulateQ lazyRandomPermutationOracles oa).run' [] := by
  rw [run_lazy_of_coinsOnly' oa h E [], StateT.run'_eq, Functor.map_map]

/-! ## Coins first -/

/-- The experiment's body after the setup, for given coins. -/
noncomputable def body (stmt : Statement) (w : Secret) (idx : Commitment) (coins : Coins) :
    OracleComp RandomPermutationOracles Bool := do
  match ← prover queryPermutation stmt w coins with
  | none => return false
  | some proof => verifier queryPermutation idx stmt proof

/-- The raw coins' distribution. -/
noncomputable def rawDist : ProbComp RawCoins :=
  (simulateQ lazyRandomPermutationOracles rawCoins).run' []

theorem countable_commitment_edges : Countable (Commitment × PermutationEdges KeccakState) := by
  have : Finite Digest := Finite.of_fintype _
  have : Finite KeccakState := Finite.of_fintype _
  have : Finite E := Finite.of_fintype _
  have : Countable Commitment :=
    Function.Injective.countable (f := fun c : Commitment ↦ (c.root, c.ood)) fun a b h ↦ by
      cases a; cases b; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  infer_instance

/-- The setup's commitment over `π`. -/
def setupIndex : OracleComp RandomPermutationOracles Commitment :=
  Prod.snd <$> setupWith queryPermutation

theorem countable_raw : Countable RawCoins := inferInstance

/-- **The coins first**: the completeness experiment is, in distribution, the raw coins, then the
setup, the prover and the verifier against the lazy permutation. -/
theorem completenessExperiment_eq (stmt : Statement) (w : Secret) :
    completenessExperiment stmt w =ᵈ rawDist >>= fun c ↦
      runWithRandomPermutation (setupIndex >>= fun idx ↦ body stmt w idx (coinsOf c)) := by
  have hc : Countable (Commitment × PermutationEdges KeccakState) := countable_commitment_edges
  have e0 : completenessExperiment stmt w = runWithRandomPermutation (setupIndex >>= fun idx ↦
      sampleCoins >>= fun coins ↦ body stmt w idx coins) := by
    simp only [completenessExperiment, setupIndex, body, map_eq_bind_pure_comp, bind_assoc,
      Function.comp_apply, pure_bind]
    rfl
  have e1 : completenessExperiment stmt w =
      (simulateQ lazyRandomPermutationOracles setupIndex).run [] >>= fun p ↦
        rawDist >>= fun c ↦
          (simulateQ lazyRandomPermutationOracles (body stmt w p.1 (coinsOf c))).run' p.2 := by
    rw [e0]
    simp only [runWithRandomPermutation, sampleCoins_eq, simulateQ_bind, StateT.run'_eq,
      StateT.run_bind, map_bind, bind_map_left]
    refine bind_congr fun p ↦ ?_
    rw [run_lazy_of_coinsOnly _ coinsOnly_rawCoins p.2, bind_map_left]
    simp only [rawDist, StateT.run'_eq, bind_map_left]
  have e2 : (rawDist >>= fun c ↦ runWithRandomPermutation (setupIndex >>= fun idx ↦
      body stmt w idx (coinsOf c))) = rawDist >>= fun c ↦
        (simulateQ lazyRandomPermutationOracles setupIndex).run [] >>= fun p ↦
          (simulateQ lazyRandomPermutationOracles (body stmt w p.1 (coinsOf c))).run' p.2 := by
    simp only [runWithRandomPermutation, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rw [e1, e2]
  let : MeasurableSpace (Commitment × PermutationEdges KeccakState) := ⊤
  let : MeasurableSpace RawCoins := ⊤
  let : MeasurableSpace Bool := ⊤
  exact EvalDistEq.of_evalDist_eq (evalDist_bind_bind_swap_of_countable _ _ _)

/-! ## With two calls -/

/-- **The experiment with two calls**, for given coins: the setup, the prover and the verifier, with
Keccak-256 and Keccak-f[1600] the calls. -/
def expH (stmt : Statement) (w : Secret) (coins : Coins) : OracleComp KeccakCalls Bool := do
  let idx ← Prod.snd <$> setupWithH callKeccak256
  match ← proverWithH callKeccak256 callKeccakF1600 nonceFuel stmt w coins with
  | none => return false
  | some proof => verifyWithH callKeccak256 callKeccakF1600 logRows idx stmt proof

theorem implH_keccakCallsOverQueryPermutation :
    LeanVM.Protocol.Compile.Rom.implH keccakCallsOverQueryPermutation =
      keccak256With queryPermutation := rfl

theorem implF_keccakCallsOverQueryPermutation :
    LeanVM.Protocol.Compile.Rom.implF keccakCallsOverQueryPermutation = queryPermutation := rfl

/-- **For given coins, the body over `π` is the two-call experiment answered over `π`.** -/
theorem experimentBody_eq (stmt : Statement) (w : Secret) (coins : Coins) :
    (setupIndex >>= fun idx ↦ body stmt w idx coins) =
      simulateQ keccakCallsOverQueryPermutation (expH stmt w coins) := by
  simp only [expH, setupIndex, simulateQ_bind, simulateQ_map, simulateQ_setupWithH,
    simulateQ_proverWithH, implH_keccakCallsOverQueryPermutation,
    implF_keccakCallsOverQueryPermutation, body, PcsQuotient.prover, PcsQuotient.verifier,
    setupWith_eqH, proverWith_eqH, verifyWith_eqH]
  refine bind_congr fun idx ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => simp
  | some proof => simp [simulateQ_verifyWithH, implH_keccakCallsOverQueryPermutation,
      implF_keccakCallsOverQueryPermutation]

/-- **The completeness experiment, coins first, with two calls.** -/
theorem completenessExperiment_eq_expH (stmt : Statement) (w : Secret) :
    completenessExperiment stmt w =ᵈ rawDist >>= fun c ↦
      (simulateQ keccakCallsOverRandomPermutation (expH stmt w (coinsOf c))).run' [] := by
  refine (completenessExperiment_eq stmt w).trans ?_
  have e : (fun c ↦ runWithRandomPermutation (setupIndex >>= fun idx ↦
      body stmt w idx (coinsOf c))) = fun c ↦
        (simulateQ keccakCallsOverRandomPermutation (expH stmt w (coinsOf c))).run' [] := by
    funext c
    rw [runWithRandomPermutation, experimentBody_eq,
      simulateQ_lazy_keccakCallsOverQueryPermutation]
  rw [e]

end E2ECompleteness.Pcs
