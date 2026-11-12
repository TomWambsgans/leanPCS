-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. The proof pattern of the commutation lemmas (one lemma per function, pushed through the binds; the run
-- by induction on the program) is the earlier `ZK/ProverBridgeParam.lean`'s (git history, commit 6020cc77) and
-- `Completeness/E2ECompleteness/PcsWithHash.lean`'s, adapted to the prover on the EIP's PCS claims. The functions
-- are leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/LeanVmVerifier.lean`'s
-- `duplex`, `absorb`, `squeeze`; `Statement/Prover/Run.lean`'s `leafDigestsM`, `parentsM`, `levelsM`,
-- `buildTreeM`, `powStepM`, `searchM`, `findNonceM`, `runFrom`; `Statement/RandomPermutation.lean`'s
-- `runWithRandomPermutation`) and `formal/Statement`'s.
import ZK.PcsSpan
import ZK.ProverBridgeParam

/-!
# The PCS hypothesis is satisfiable: the ideal PCS of the model

`PcsZeroKnowledge pcs sim εpcs` (`formal/Statement/PcsQuotient/Zk.lean`) is the hypothesis of the zero-knowledge
theorems, for a PCS `pcs` in the model (`PcsOps` over `OracleComp RandomPermutationOracles`). It is not vacuous:

**`pcsZeroKnowledge_idealOf`**: for every opening program `simO` of the model (a function of the commitment and
the claim alone, which may draw coins and query `π`, `π⁻¹`), the ideal PCS `PcsOps.idealOf simO` (roots uniform from
the coins, independent of the table; the out-of-domain answer the table's; openings `simO`) meets it with
`εpcs = 0` for the simulator `PcsSimulator.ofOpen simO`: the protocol's experiment over it **is** the hybrid
(`pcsExperiment_idealOf`).

**`zeroKnowledge_idealOf`**: hence, under `Group1Uniform ε1` alone, the protocol over that PCS is zero-knowledge
within `ε1 + εslack + εfs₀` (`zeroKnowledge_pcs_slack` at `εpcs = 0`).

The proof reads the honest prover through the model's oracle: `simulateQ` is a monad morphism (`simHom`), the
prover is a program over a permutation in any monad, and one lemma per function pushes the morphism through its
binds (`proveWithPcs_hom`: the prover over `F` and `pcs`, read through `φ`, is the prover over `φ ∘ F` and `pcs`
read through `φ`); and the lazily sampled permutation on the edges of a state with an extra component
(`edgeOracle`) runs a game as `runWithRandomPermutation` does (`run'_simulateQ_edgeOracle`).
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient PcsQuotient.Transcript
open scoped ENNReal

set_option autoImplicit false

namespace PcsQuotient.EndToEnd.PcsParam

open PcsQuotient.EndToEnd.Param

/-! ### Monad morphisms -/

section Hom

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] (φ : MHom m n)

theorem app_map {α β : Type} (f : α → β) (x : m α) : φ.app (f <$> x) = f <$> φ.app x := by
  rw [map_eq_bind_pure_comp, φ.app_bind, map_eq_bind_pure_comp]
  simp only [Function.comp_apply, φ.app_pure]
  rfl

theorem app_mapM_list {α β : Type} (f : α → m β) :
    ∀ l : List α, φ.app (l.mapM f) = l.mapM fun a ↦ φ.app (f a)
  | [] => by simp only [List.mapM_nil, φ.app_pure]
  | a :: l => by
    simp only [List.mapM_cons, φ.app_bind, φ.app_pure]
    refine congrArg _ (funext fun b ↦ ?_)
    rw [app_mapM_list f l]

theorem app_mapM_array {α β : Type} (f : α → m β) (a : Array α) :
    φ.app (a.mapM f) = a.mapM fun x ↦ φ.app (f x) := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList, app_map, app_mapM_list]

end Hom

/-- **Running an oracle computation with an implementation** is a monad morphism. -/
def simHom {ι : Type} {spec : OracleSpec.{0, 0} ι} {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl spec r) : MHom (OracleComp spec) r where
  app x := simulateQ impl x
  app_pure a := simulateQ_pure impl a
  app_bind x f := simulateQ_bind impl x f

/-- **PCS operations read through a monad morphism.** -/
def _root_.PcsQuotient.PcsOps.mapHom {m n : Type → Type} [Monad m] [Monad n] {Hd : Type} (pcs : PcsOps m Hd)
    (φ : MHom m n) : PcsOps n Hd where
  commit μ table := φ.app (pcs.commit μ table)
  openClaim h c claim := φ.app (pcs.openClaim h c claim)

/-! ### The prover through a monad morphism -/

section Programs

variable {m n : Type → Type} [Monad m] [Monad n] (φ : MHom m n) (F : KeccakState → m KeccakState)

theorem duplex_hom (sp : Sponge) : φ.app (duplex F sp) = duplex (fun x ↦ φ.app (F x)) sp := by
  simp only [duplex, φ.app_bind, φ.app_pure]

theorem absorb_hom (sp : Sponge) (x : E) (tag : ℕ) :
    φ.app (Compile.absorb F sp x tag) = Compile.absorb (fun y ↦ φ.app (F y)) sp x tag := by
  simp only [Compile.absorb]
  split <;> simp only [φ.app_bind, φ.app_pure, duplex_hom]

theorem squeeze_hom (sp : Sponge) : φ.app (squeeze F sp) = squeeze (fun x ↦ φ.app (F x)) sp := by
  simp only [squeeze, φ.app_bind, φ.app_pure, duplex_hom]

theorem startWith_hom (lbl : List UInt8) :
    φ.app (Chain.startWith F lbl) = Chain.startWith (fun x ↦ φ.app (F x)) lbl := by
  simp only [Chain.startWith, φ.app_bind, φ.app_pure, keccak256With_hom]

theorem squeezeWith_hom (c : Chain) :
    φ.app (c.squeezeWith F) = c.squeezeWith (fun x ↦ φ.app (F x)) := by
  simp only [Chain.squeezeWith, φ.app_bind, φ.app_pure, keccak256With_hom]

theorem pcsSpongeWith_hom (c : Commitment) (claim : Claim) :
    φ.app (pcsSpongeWith F c claim) = pcsSpongeWith (fun x ↦ φ.app (F x)) c claim := by
  simp only [pcsSpongeWith, φ.app_bind, φ.app_pure, keccak256With_hom]

theorem powStepM_hom (sp : Sponge) (x : E) :
    φ.app (powStepM F sp x) = powStepM (fun y ↦ φ.app (F y)) sp x := by
  simp only [powStepM, φ.app_bind, absorb_hom, squeeze_hom]

theorem searchM_hom (bits : ℕ) (sp : Sponge) : ∀ (start count : ℕ),
    φ.app (searchM F bits sp start count) = searchM (fun x ↦ φ.app (F x)) bits sp start count
  | _, 0 => by simp only [searchM, φ.app_pure]
  | start, count + 1 => by
    simp only [searchM, φ.app_bind, powStepM_hom]
    congr 1; funext r
    split
    · simp only [φ.app_pure]
    · exact searchM_hom bits sp (start + 1) count

theorem findNonceM_hom (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    φ.app (findNonceM F bits sp fuel) = findNonceM (fun x ↦ φ.app (F x)) bits sp fuel := by
  unfold findNonceM
  split
  · simp only [φ.app_pure]
  · exact searchM_hom φ F bits sp 0 fuel

theorem reduceWith_hom (logRows : ℕ) (index : Commitment) (stmt : Statement) (p : ReductionProof) :
    φ.app (reduceWith F logRows index stmt p) = reduceWith (fun x ↦ φ.app (F x)) logRows index stmt p := by
  unfold reduceWith
  by_cases hs : Supported logRows
  · simp only [hs, not_true_eq_false, ite_false, φ.app_bind, startWith_hom]
    congr 1; funext c
    rcases hw : readCommitment c p.witness with _ | ⟨w, c₁⟩
    · simp [φ.app_pure]
    simp only [φ.app_bind, squeezeWith_hom]
    congr 1; funext x₁; congr 1; funext x₂; congr 1; funext x₃
    rcases hh : readCommitment x₃.2 p.table with _ | ⟨h, c₂⟩
    · simp [φ.app_pure]
    simp only [φ.app_bind, φ.app_pure, squeezeWith_hom]
  · simp [hs, φ.app_pure]

end Programs

section Lawful

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  (φ : MHom m n) (F : KeccakState → m KeccakState)

theorem oodPointWith_hom (k : ℕ) (root : Digest) :
    φ.app (oodPointWith F k root) = oodPointWith (fun x ↦ φ.app (F x)) k root := by
  simp only [oodPointWith, app_mapM_list φ, φ.app_bind, φ.app_pure, keccak256With_hom]

theorem leafDigestsM_hom (height : ℕ) (word : Word) :
    φ.app (leafDigestsM F height word) = leafDigestsM (fun x ↦ φ.app (F x)) height word := by
  simp only [leafDigestsM, app_mapM_array φ, keccak256With_hom]

theorem parentsM_hom (level : Array Digest) (count : ℕ) :
    φ.app (parentsM F level count) = parentsM (fun x ↦ φ.app (F x)) level count := by
  simp only [parentsM, app_mapM_array φ, keccak256With_hom]

theorem levelsM_hom : ∀ (k : ℕ) (level : Array Digest),
    φ.app (levelsM F k level) = levelsM (fun x ↦ φ.app (F x)) k level
  | 0, level => by simp only [levelsM, φ.app_pure]
  | k + 1, level => by
    simp only [levelsM, φ.app_bind, φ.app_pure, parentsM_hom, levelsM_hom k]

theorem buildTreeM_hom (height : ℕ) (word : Word) :
    φ.app (buildTreeM F height word) = buildTreeM (fun x ↦ φ.app (F x)) height word := by
  simp only [buildTreeM, φ.app_bind, φ.app_pure, leafDigestsM_hom, levelsM_hom]

theorem commitmentWith_hom (μ : ℕ) (table : Array K) :
    φ.app (commitmentWith F μ table) = commitmentWith (fun x ↦ φ.app (F x)) μ table := by
  simp only [commitmentWith, commitWith, φ.app_bind, φ.app_pure, buildTreeM_hom, oodPointWith_hom]

/-- **The run** (mumbai's `runFrom`), by induction on the program. -/
theorem runFrom_hom (fuel : ℕ) {α β : Type} (P : Prog α) :
    ∀ (S : Option (Script β)) (sp : Sponge) (cs : List LeanVM.Prover.Tree),
      φ.app (runFrom F fuel P S sp cs) = runFrom (fun x ↦ φ.app (F x)) fuel P S sp cs := by
  induction P with
  | ret a => intro S sp cs; simp only [runFrom, φ.app_pure]
  | fail => intro S sp cs; simp only [runFrom, φ.app_pure]
  | read k ih =>
    intro S sp cs
    simp only [runFrom, φ.app_bind, φ.app_pure, absorb_hom, ih]
  | sample k ih =>
    intro S sp cs
    simp only [runFrom, φ.app_bind, squeeze_hom, ih]
  | grind bits k ih =>
    intro S sp cs
    simp only [runFrom, φ.app_bind, findNonceM_hom]
    congr 1; funext o
    cases o with
    | none => simp only [φ.app_pure]
    | some x => simp only [φ.app_bind, φ.app_pure, powStepM_hom, ih]
  | commit ht w k ih =>
    intro S sp cs
    simp only [runFrom, φ.app_bind, φ.app_pure, buildTreeM_hom, absorb_hom, ih]
  | query i ps k ih =>
    intro S sp cs
    simp only [runFrom]
    split
    · simp only [φ.app_pure]
    · simp only [φ.app_bind, φ.app_pure, ih]

theorem proveClaimWith_hom (fuel : ℕ) (tree : LeanVM.Prover.Tree) (table : Array K) (c : Commitment)
    (claim : Claim) :
    φ.app (proveClaimWith F fuel tree table c claim) =
      proveClaimWith (fun x ↦ φ.app (F x)) fuel tree table c claim := by
  simp only [proveClaimWith, φ.app_bind, φ.app_pure, pcsSpongeWith_hom, absorb_hom, oodPointWith_hom,
    runFrom_hom]

/-- **The prover over a PCS, through a monad morphism**: `φ` pushed through the binds, the pure computations
untouched; the PCS read through `φ`. -/
theorem proveWithPcs_hom {Hd : Type} (pcs : PcsOps m Hd) (fuel : ℕ) (circuit : Circuit) (stmt : Statement)
    (cells₀ : Array K) (coins : Coins) :
    φ.app (proveWithPcs F pcs fuel circuit stmt cells₀ coins) =
      proveWithPcs (fun x ↦ φ.app (F x)) (pcs.mapHom φ) fuel circuit stmt cells₀ coins := by
  unfold proveWithPcs PcsOps.mapHom
  simp only [φ.app_bind, commitmentWith_hom, startWith_hom, squeezeWith_hom]
  congr 1; funext x₀; congr 1; funext x₁; congr 1; funext c
  congr 1; funext a₁; congr 1; funext a₂; congr 1; funext a₃
  congr 1; funext x₂; congr 1; funext t
  rw [reduceWith_hom]
  congr 1; funext r
  rcases r with _ | r
  · simp [φ.app_pure]
  simp only [φ.app_bind]
  congr 1; funext o₁
  rcases o₁ with _ | o₁
  · simp [φ.app_pure]
  simp only [φ.app_bind, proveClaimWith_hom]
  congr 1; funext o₂
  rcases o₂ with _ | o₂
  · simp [φ.app_pure]
  simp only [φ.app_bind]
  congr 1; funext o₃
  rcases o₃ with _ | o₃ <;> simp [φ.app_pure]

end Lawful

/-! ### The model's oracle on a state with an extra component -/

theorem onEdges_pure {A α : Type} (a : α) : onEdges (A := A) (pure a : StateT Edges ProbComp α) = pure a := by
  funext s
  show (fun p ↦ (p.1, (p.2, s.2))) <$> (pure (a, s.1) : ProbComp _) = pure (a, s)
  simp

theorem onEdges_bind {A α β : Type} (x : StateT Edges ProbComp α) (f : α → StateT Edges ProbComp β) :
    onEdges (A := A) (x >>= f) = onEdges x >>= fun a ↦ onEdges (f a) := by
  funext s
  show (fun p ↦ (p.1, (p.2, s.2))) <$> (x >>= f).run s.1 = (onEdges x >>= fun a ↦ onEdges (f a)).run s
  rw [StateT.run_bind, StateT.run_bind, map_bind, onEdges_run, bind_map_left]
  rfl

/-- **The model's oracle on the edges component** is the lazily sampled permutation, the extra component kept. -/
theorem simulateQ_edgeOracle {A α : Type} (X : OracleComp RandomPermutationOracles α) :
    simulateQ (edgeOracle (A := A)) X = onEdges (simulateQ lazyRandomPermutationOracles X) := by
  induction X using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure, simulateQ_pure, onEdges_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, ih,
      onEdges_bind]
    rfl

/-- **A game run with the model's oracle on the edges component, from no edge**, is the game run against the
lazily sampled permutation. -/
theorem run'_simulateQ_edgeOracle {A α : Type} (a₀ : A) (X : OracleComp RandomPermutationOracles α) :
    (simulateQ (edgeOracle (A := A)) X).run' ([], a₀) = runWithRandomPermutation X := by
  rw [simulateQ_edgeOracle]
  show Prod.fst <$> (onEdges (simulateQ lazyRandomPermutationOracles X)).run ([], a₀) =
    Prod.fst <$> (simulateQ lazyRandomPermutationOracles X).run []
  rw [onEdges_run, Functor.map_map]

/-! ### The ideal PCS of the model -/

variable (simO : Commitment → Claim → OracleComp RandomPermutationOracles (Option Compile.Proof))

/-- The ideal PCS read through the model's oracle is the hybrid's ideal PCS of `PcsSimulator.ofOpen simO`. -/
theorem idealOf_mapHom :
    (PcsOps.idealOf simO).mapHom (simHom (edgeOracle (A := Unit))) = (PcsSimulator.ofOpen simO).idealPcs := by
  have hc : ∀ μ table, (simHom (edgeOracle (A := Unit))).app ((PcsOps.idealOf simO).commit μ table) =
      (PcsSimulator.ofOpen simO).idealPcs.commit μ table := fun μ table ↦ by
    simp only [PcsOps.idealOf, (simHom (edgeOracle (A := Unit))).app_bind,
      (simHom (edgeOracle (A := Unit))).app_pure, oodPointWith_hom]
    rfl
  simp only [PcsOps.mapHom, hc]
  rfl

/-- **The protocol's experiment over the ideal PCS of the model is its hybrid** for `PcsSimulator.ofOpen simO`. -/
theorem pcsExperiment_idealOf (stmt : Statement) (w : Secret) (D : Distinguisher) :
    pcsExperiment (PcsOps.idealOf simO) stmt w D = hybridExperiment (PcsSimulator.ofOpen simO) stmt w D := by
  have h : ∀ coins, simulateQ (edgeOracle (A := Unit)) (proveWithPcs queryPermutation (PcsOps.idealOf simO)
      nonceFuel (membership logRows) stmt ((membership logRows).cells (membershipInputs w)) coins) =
      proveWithPcs (PcsSimulator.ofOpen simO).perm (PcsSimulator.ofOpen simO).idealPcs nonceFuel
        (membership logRows) stmt ((membership logRows).cells (membershipInputs w)) coins := fun coins ↦ by
    rw [← idealOf_mapHom]
    exact proveWithPcs_hom (simHom (edgeOracle (A := Unit))) queryPermutation (PcsOps.idealOf simO) nonceFuel _ _ _
      coins
  rw [pcsExperiment, ← run'_simulateQ_edgeOracle (A := Unit) ()]
  unfold hybridExperiment
  simp only [simulateQ_bind, h]
  rfl

/-- **The PCS hypothesis is satisfiable**: the ideal PCS of the model, with any opening program `simO`, is
zero-knowledge with `εpcs = 0` for `PcsSimulator.ofOpen simO`. -/
theorem pcsZeroKnowledge_idealOf : PcsZeroKnowledge (PcsOps.idealOf simO) (PcsSimulator.ofOpen simO) fun _ ↦ 0 := by
  intro stmt w _ D Q _
  rw [pcsExperiment_idealOf, add_zero]
  exact ⟨le_rfl, le_rfl⟩

/-- **Zero knowledge of the protocol over the ideal PCS of the model**, from group 1's uniformity alone: within
`ε1 + εslack + εfs₀` (`zeroKnowledge_pcs_slack` at `εpcs = 0`, `pcsZeroKnowledge_idealOf`). -/
theorem zeroKnowledge_idealOf (ε1 : ℝ≥0∞) (h1 : Group1Uniform ε1) :
    ZeroKnowledgeWith (PcsOps.idealOf simO) (PcsSimulator.ofOpen simO).s₀ (zkSimulator (PcsSimulator.ofOpen simO))
      (PcsSimulator.ofOpen simO).oracle (fun _ ↦ ε1 + εslack + εfs₀) := by
  have h := zeroKnowledge_pcs_slack (PcsOps.idealOf simO) (PcsSimulator.ofOpen simO) (fun _ ↦ 0) ε1
    (pcsZeroKnowledge_idealOf simO) h1
  simpa only [zero_add] using h

end PcsQuotient.EndToEnd.PcsParam
