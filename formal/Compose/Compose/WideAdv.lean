-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows `ListChainUDoom.lean`, `ListChainUDoom128.lean`
-- and `GOps.lean` (the experiment, the bad events with the adversary's roots, the traces `trace_advU'` and
-- `trace_whirUG`) for the wide chain (`WideChain.lean`), in mumbai's two-oracle model with the tails fixed (`τ`): the
-- rate model's computations split at a tail table (`WideSpec.lean`'s `instR τ`).
import Compose.WideChain
import Compose.GOps

/-!
# The wide chain's experiment, with the tails fixed

In mumbai's two-oracle model with a fixed table of tails `τ`, a wide draw is Keccak-256's digest and `τ` of its input
(`hashτ τ`). The rate model's experiment, split at its table of tails (`instR`, `WideSpec.lean`), is this one
(`WideRate.lean`). Here, for every `τ`:

* the verifier (`verWide`: the wide chain, then `post`), the experiment (`expWide`), the run (`runWide`), the run before the
  openings (`preWide`), and the run against a table (`runMW_run`, `expWide_run`, `runWide_run`, `preWide_run`);
* **the bad events** (`kcBadW`, `advBadW`): a Keccak-256 query bad for `listBadW` (`WideChain.lean`) on the view, or
  a fresh answer after the adversary's last query that is one of its roots (`rootBadK`);
* **`trace_advW`** and **`trace_whirWG`**: `trace_advU'` and `trace_whirUG` (`GOps.lean`'s, openings of any verifier,
  the doom read at the run's end, the seed separated by a pair of answers) for the wide chain, word for word.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The experiment -/

/-- **A wide call with the tails fixed**: Keccak-256's digest, and `τ` of the input. -/
def hashτ (τ : List UInt8 → TailP) (x : List UInt8) : OracleComp KeccakCalls (Bytes32 × TailP) :=
  hash256 x >>= fun d => pure (d, τ x)

section Exp

variable {F St M Pf β : Type} [SampleableType F]
variable (W : ChainSpecW F St) (C : ℕ → ListCommit M) (R : Piop W.K M)
  (view : Pf → St × List (RMsg F)) (τ : List UInt8 → TailP)

/-- **The verifier after the adversary**: the wide chain on the statement and messages the proof carries, then
`post` (the openings). -/
def verWide (post : Pf → List (List F) → OracleComp KeccakCalls β) (π : Pf) :
    OracleComp KeccakCalls (List (List F) × β) :=
  W.chain (hashτ τ) (view π).1 (view π).2 >>= fun ch => post π ch >>= fun b => pure (ch, b)

/-- **The experiment**: the adversary, its Keccak-256 queries logged, then the verifier. -/
def expWide (A : OracleComp KeccakCalls Pf) (post : Pf → List (List F) → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls (OutK Pf F β) :=
  loggedKC A >>= fun pt => verWide W view τ post pt.1 >>= fun v => pure ((pt.1, v), pt.2)

/-- The run, unlogged. -/
def runWide (A : OracleComp KeccakCalls Pf) (post : Pf → List (List F) → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls (Pf × (List (List F) × β)) :=
  A >>= fun p => verWide W view τ post p >>= fun v => pure (p, v)

/-- The adversary, its queries logged, then the wide chain. -/
def preWide (A : OracleComp KeccakCalls Pf) : OracleComp KeccakCalls (PreK Pf F) :=
  loggedKC A >>= fun pt => W.chain (hashτ τ) (view pt.1).1 (view pt.1).2 >>= fun ch =>
    pure (pt.1, ch, pt.2)

/-! ### The bad events -/

/-- **A bad query of both oracles**: a Keccak-256 query bad for `listBadW` on the view; never a Keccak-f query. -/
def kcBadW (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  match d with
  | .inl x => listBadW W C R τ (viewH H) x (viewT T)
  | .inr _ => False

/-- A bad query: `kcBadW`, or a fresh answer that is an announced root. -/
def advBadW (A : OracleComp KeccakCalls Pf) (H : Finset (List UInt8 ⊕ KeccakState))
    (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  kcBadW W C R τ H d T ∨ rootBadK W.K view A H d T

theorem freshBad_kcW (T : KTable) : ∀ (H : Finset (List UInt8 ⊕ KeccakState))
    (L : List (List UInt8 ⊕ KeccakState)),
    FreshBad (listBadW W C R τ) (viewT T) (viewH H) (L.filterMap Sum.getLeft?) →
      FreshBad (kcBadW W C R τ) T H L
  | _, [], h => by simp [FreshBad] at h
  | H, .inl x :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inl, FreshBad] at h ⊢
    rcases h with ⟨hx, hb⟩ | h
    · exact Or.inl ⟨fun hm => hx (mem_viewH.mpr hm), hb⟩
    · refine Or.inr (freshBad_kcW T _ L ?_)
      rwa [viewH_insert_inl]
  | H, .inr s :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inr, FreshBad] at h ⊢
    refine Or.inr (freshBad_kcW T _ L ?_)
    rwa [viewH_insert_inr]

/-! ### The run against a table -/

/-- **The wide chain against a table**: it asks the chain's inputs, and answers each with its digest and `τ`. -/
theorem runMW_run (T : KTable) : ∀ (y : List UInt8) (es : List (List UInt8)),
    (tableQueryLog (ChainSpecW.runMW (hashτ τ) y es) T).map Sigma.fst = (allIn (viewT T) y es).map Sum.inl ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (ChainSpecW.runMW (hashτ τ) y es) =
        (allIn (viewT T) y es).map fun x => (viewT T x, τ x)
  | y, [] => by
    simp only [ChainSpecW.runMW, hashτ, hash256, callKeccak256, bind_assoc, pure_bind, tableQueryLog_query_bind,
      tableQueryLog_pure, evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query,
      evalWithAnswerFn_pure, allIn, List.map_cons, List.map_nil]
    refine ⟨?_, ?_⟩ <;> trivial
  | y, e :: es => by
    obtain ⟨ih1, ih2⟩ := runMW_run T (stepIn (viewT T y) e) es
    simp only [ChainSpecW.runMW, hashτ, hash256, callKeccak256, bind_assoc, pure_bind,
      tableQueryLog_bind, tableQueryLog_pure, List.append_nil, evalWithAnswerFn_bind,
      evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure, allIn, List.map_cons]
    refine ⟨?_, ?_⟩
    · exact congrArg (List.cons _) ih1
    · exact congrArg (List.cons _) ih2

/-- The chain's challenges, from its answers on a table, are `chalsT`'s. -/
theorem chalsOf_allIn (T : KTable) (s : St) (ms : List (RMsg F)) :
    W.chalsOf ((allIn (viewT T) (W.label s) (W.absorbsS s W.K.rounds ms)).map fun x => (viewT T x, τ x)) =
      W.chalsT (viewT T) τ s W.K.rounds ms := by
  have ht : ∀ (l : List (List UInt8)) (f : List UInt8 → Bytes32 × TailP), (l.map f).tail = l.tail.map f := by
    intro l f
    cases l <;> rfl
  simp only [ChainSpecW.chalsOf, ChainSpecW.chalsT, chalsTW, ht, List.zip_map_right, List.map_map]
  rfl

theorem isTotalQueryBound_runMW : ∀ (y : List UInt8) (es : List (List UInt8)),
    IsTotalQueryBound (ChainSpecW.runMW (hashτ τ) y es) (es.length + 1)
  | y, [] => by
    simp only [ChainSpecW.runMW, hashτ, hash256, callKeccak256, bind_assoc, pure_bind]
    exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun _ => trivial⟩
  | y, e :: es => by
    simp only [ChainSpecW.runMW, hashτ, hash256, callKeccak256, bind_assoc, pure_bind]
    refine isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun u => ?_⟩
    have h := isTotalQueryBound_runMW (stepIn (toB u) e) es
    have h' := isTotalQueryBound_bind (ob := fun rest =>
      (pure ((toB u, τ y) :: rest) : OracleComp KeccakCalls (List (Bytes32 × TailP)))) h (n₂ := 0)
      fun _ => trivial
    simpa using h'

theorem isTotalQueryBound_chainW (s : St) (ms : List (RMsg F)) :
    IsTotalQueryBound (W.chain (hashτ τ) s ms) W.nQ := by
  have h := isTotalQueryBound_runMW τ (W.label s) (W.absorbsS s W.K.rounds ms)
  rw [ChainSpecW.absorbsS, length_absorbsW] at h
  exact (isQueryBound_map_iff _ _ _ _ _).mpr h

/-- The experiment against a table: the run's queries, and the adversary's transcript. -/
theorem expWide_run (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (T : KTable) :
    tableQueryLog (expWide W view τ A post) T = tableQueryLog (runWide W view τ A post) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (expWide W view τ A post) =
        (evalWithAnswerFn (QueryImpl.ofFn T) (runWide W view τ A post),
          (tableQueryLog A T).filterMap inlEntry) := by
  have hl := log_loggedKC_run T A []
  have he := eval_loggedKC_run T A []
  rw [List.nil_append] at he
  constructor
  · simp only [expWide, runWide, loggedKC, tableQueryLog_bind, tableQueryLog_pure, hl, he]
  · simp only [expWide, runWide, loggedKC, evalWithAnswerFn_bind, evalWithAnswerFn_pure, he]

/-- The run against a table: the adversary's queries, the chain's inputs, the openings'. -/
theorem runWide_run (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (T : KTable) :
    let p := evalWithAnswerFn (QueryImpl.ofFn T) A
    let ch := W.chalsT (viewT T) τ (view p).1 W.K.rounds (view p).2
    (tableQueryLog (runWide W view τ A post) T).map Sigma.fst =
        (tableQueryLog A T).map Sigma.fst ++
          ((allIn (viewT T) (W.label (view p).1) (W.absorbsS (view p).1 W.K.rounds (view p).2)).map
            Sum.inl ++ (tableQueryLog (post p ch) T).map Sigma.fst) ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (runWide W view τ A post) =
        (p, (ch, evalWithAnswerFn (QueryImpl.ofFn T) (post p ch))) := by
  intro p ch
  obtain ⟨h1, h2⟩ := runMW_run τ T (W.label (view p).1) (W.absorbsS (view p).1 W.K.rounds (view p).2)
  have hch := chalsOf_allIn W τ T (view p).1 (view p).2
  constructor
  · simp only [runWide, verWide, ChainSpecW.chain, tableQueryLog_bind, tableQueryLog_pure,
      List.map_append, List.append_nil, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
      pure_bind]
    rw [h1, h2, hch]
  · simp only [runWide, verWide, ChainSpecW.chain, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rw [h2, hch]

theorem preWide_run (A : OracleComp KeccakCalls Pf) (T : KTable) :
    tableQueryLog (preWide W view τ A) T = tableQueryLog A T ++
        tableQueryLog (W.chain (hashτ τ) (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).1
          (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).2) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (preWide W view τ A) =
        (evalWithAnswerFn (QueryImpl.ofFn T) A,
          evalWithAnswerFn (QueryImpl.ofFn T) (W.chain (hashτ τ)
            (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).1
            (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).2),
          (tableQueryLog A T).filterMap inlEntry) := by
  obtain ⟨hl, he⟩ := run_logged A T
  have hl' : tableQueryLog (loggedKC A) T = tableQueryLog A T := hl
  have he' : evalWithAnswerFn (QueryImpl.ofFn T) (loggedKC A) =
      (evalWithAnswerFn (QueryImpl.ofFn T) A, (tableQueryLog A T).filterMap inlEntry) := he
  constructor
  · simp only [preWide, tableQueryLog_bind, hl', he', tableQueryLog_pure, List.append_nil]
  · simp only [preWide, evalWithAnswerFn_bind, he', evalWithAnswerFn_pure]

theorem isTotalQueryBound_preWide (A : OracleComp KeccakCalls Pf) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) : IsTotalQueryBound (preWide W view τ A) (QA + W.nQ) := by
  have h := isTotalQueryBound_bind
    (ob := fun pt : Pf × Transcript => W.chain (hashτ τ) (view pt.1).1 (view pt.1).2 >>= fun ch =>
      (pure (pt.1, ch, pt.2) : OracleComp KeccakCalls (PreK Pf F)))
    (isTotalQueryBound_loggedKC_run A QA [] hA) fun pt =>
      isTotalQueryBound_bind
        (ob := fun ch => (pure (pt.1, ch, pt.2) : OracleComp KeccakCalls (PreK Pf F))) (n₂ := 0)
        (isTotalQueryBound_chainW W τ (view pt.1).1 (view pt.1).2) fun _ => trivial
  rwa [Nat.add_zero] at h

/-- **`expW` is the run before the openings (`preWide`), then the openings.** -/
theorem expWide_eqG {M' : Type} (A : OracleComp KeccakCalls Pf) (ops : List (GOp Pf F M')) :
    expWide W view τ A (gopsRun view ops) =
      preWide W view τ A >>= fun x => opsOut x <$> gopsRun view ops x.1 x.2.1 := by
  simp only [expWide, verWide, preWide, opsOut, bind_assoc, pure_bind, map_eq_bind_pure_comp,
    Function.comp_def]

open Classical in
/-- **The trace, with the adversary's transcript** (`trace_advU` for `listBadU'`): on every table
of both oracles, a run whose log holds no answer equal to the label's first 32 bytes (`hseed`) and
whose candidates, read off the adversary's queries, make the transcript lost at the start and won
at the end asks a bad fresh query. -/
theorem trace_advW (A : OracleComp KeccakCalls Pf)
    (post : Pf → List (List F) → OracleComp KeccakCalls β) (T : KTable)
    (hseed : ∀ z ∈ ((tableQueryLog (expWide W view τ A post) T).map Sigma.fst).filterMap Sum.getLeft?,
      (viewT T z).toList ≠ (W.label (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).1).take 32)
    (hwin : ListWinsK W.K C R view (evalWithAnswerFn (QueryImpl.ofFn T) (expWide W view τ A post))) :
    FreshBad (advBadW W C R view τ A) T ∅
      ((tableQueryLog (expWide W view τ A post) T).map Sigma.fst) := by
  obtain ⟨hlogE, hevalE⟩ := expWide_run W view τ A post T
  obtain ⟨hL, heval⟩ := runWide_run W view τ A post T
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A
  set s := (view p).1
  set ms := (view p).2
  rw [hlogE] at hseed ⊢
  rw [hevalE, heval] at hwin
  set lg := tableQueryLog (runWide W view τ A post) T
  set lA := tableQueryLog A T
  set Lk := lg.map Sigma.fst
  set L := Lk.filterMap Sum.getLeft?
  set LA := (lA.map Sigma.fst).filterMap Sum.getLeft?
  set tr : Transcript := lA.filterMap inlEntry
  have hLsplit : ∃ rest, L = LA ++ rest := by
    refine ⟨?_, ?_⟩
    swap
    · simp only [L, LA, Lk, hL, List.filterMap_append]
      exact rfl
  obtain ⟨rest, hLA⟩ := hLsplit
  have htrH : histOfTr tr = LA.toFinset := by
    simp only [histOfTr, tr, LA, map_fst_filterMap_inlEntry]
  have htrT : ∀ d ∈ histOfTr tr, tableOfTr tr d = viewT T d := by
    intro d hd
    refine tableOfTr_eq (viewT T) tr (fun e he => ?_) d (by simpa [histOfTr] using hd)
    obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp he
    obtain ⟨d', u⟩ := q
    cases d' with
    | inl x =>
      simp only [inlEntry, Option.some.injEq] at hqe
      subst hqe
      have := tableQueryLog_snd_dep T _ _ hq
      simp only at this
      simp [viewT, this]
    | inr s => simp [inlEntry] at hqe
  obtain ⟨hfit, cs, hcs, hlw⟩ := hwin
  simp only at hfit hcs hlw
  rw [candLists_congr C htrT, htrH] at hcs
  by_contra hnb
  have hk : ¬ FreshBad (kcBadW W C R τ) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hr : ¬ FreshBad (rootBadK W.K view A) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBadW W C R τ) (viewT T) ∅ L := fun h =>
    hk (freshBad_kcW W C R τ T ∅ Lk (by rw [viewH_empty]; exact h))
  have hord := rf_beforeW hl
  -- No fresh answer after the adversary's queries is a root it announced.
  have hroot : ∀ w ∈ L, viewT T w ∈ W.K.rootsK ms → w ∈ LA := by
    intro w hw hwr
    by_contra hwA
    have hwk : Sum.inl w ∈ Lk := mem_filterMap_getLeft?.mp hw
    have hwA' : Sum.inl w ∉ lA.map Sigma.fst := fun h => hwA (mem_filterMap_getLeft?.mpr h)
    have nb := not_bad_before (rootBadK W.K view A) T ∅ Lk hr (.inl w) hwk
      (Finset.notMem_empty _)
    rw [Finset.empty_union] at nb
    refine nb ⟨fun q hq => ?_, hwr⟩
    simp only [Lk, lg, hL]
    exact subset_before_append _ _ hwA' q hq
  -- So the candidates read off the adversary's queries are those read off the run's.
  have hstab : ∀ {N : Type} (Cn : ListCommit N) (r : Bytes32), r ∈ W.K.rootsK ms →
      Cn.cands LA.toFinset (viewT T) r = Cn.cands L.toFinset (viewT T) r := by
    intro N Cn r hr'
    refine (Cn.stable LA.toFinset L.toFinset (viewT T) r (fun w hw => ?_) (fun w hw hwr => ?_)
      (fun y hy w hw h => ?_)).symm
    · rw [hLA]
      exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hw))
    · exact List.mem_toFinset.mpr (hroot w (List.mem_toFinset.mp hw) (hwr ▸ hr'))
    · have hyA := List.mem_toFinset.mp hy
      have hyL : y ∈ L := by rw [hLA]; exact List.mem_append_left _ hyA
      have hb := hord w (List.mem_toFinset.mp hw) y hyL (W.refers_rf _ _ h)
      rw [hLA, before_append_of_mem LA rest hyA] at hb
      exact List.mem_toFinset.mpr (mem_of_mem_before LA w y hb)
  have hms : ms.take W.K.rounds.length = ms := List.take_of_length_le (le_of_eq hfit.length_eq)
  rw [candLists_stable C 0 ms fun m hm r hr k => hstab (C k) r (by
    simp only [ChainSpec.rootsK, hms]
    exact List.mem_filterMap.mpr ⟨m, hm, hr⟩)] at hcs
  refine hl (trace_coreW W C R τ L (viewT T) s ms cs hfit (fun y hy => ?_) hcs hlw hseed)
  simp only [L, Lk, lg, hL, List.filterMap_append]
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [filterMap_getLeft?_map_inl]
  exact hy

/-! ## Each fresh query is bad with small probability -/

end Exp

/-! ## The trace -/

section Trace

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]
variable (W : ChainSpecW F St) (R : Piop W.K M) (view : Pf → St × List (RMsg F)) (τ : List UInt8 → TailP)

open Classical in
/-- **The trace of the run with its whole transcript**: on every table of both oracles, a run that
breaks knowledge soundness while no opening is doomed at the end of the run (`DoomF`) and no two
answers of its transcript make a pair (`PairTr`) asks a bad fresh query, when the label's first 32
bytes are `tag ‖` the first bytes of an answer the adversary asked (`hlabT`). Doom read at the
run's end: an undoomed opening's candidate is read off the whole history `L`, whose word under a
root of the adversary is the adversary's (`hstab` at `H = L`). -/
theorem trace_whirWG {σ : Type} (ops : List (GOp Pf F M)) (tc : ℕ → TableCode M)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A₀ : σ → OracleComp KeccakCalls Pf)
    (hok : ∀ o ∈ ops, GOp.OK tc good setup fix o)
    (hcov : ∀ i < W.K.rounds.length, (W.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, GOp.SetupHolds o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll W.K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = W.K.rounds.length →
      (∀ i (h : i < cs.length), (W.K.spec i).root → good i π ch cs[i]) →
      (∀ i (h : i < cs.length), (W.K.spec i).root = false → cs[i] = none) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (tag : List UInt8) (T : KTable)
    (hlabT : ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG setup fix A₀) T).map Sigma.fst ∧
      (W.label (view (evalWithAnswerFn (QueryImpl.ofFn T) (withSetupG setup fix A₀))).1).take 32 =
        tag ++ (viewT T w).toList.take (32 - tag.length))
    (hev : BreaksOK W.K (fun i => (tc i).commit) R view check
        (fun bs => ∀ k < ops.length, bs.getD k false = true)
        (evalWithAnswerFn (QueryImpl.ofFn T)
          (expLG view (preWide W view τ (withSetupG setup fix A₀)) ops)).1 ∧
      ¬ DoomFG view ops (evalWithAnswerFn (QueryImpl.ofFn T)
          (expLG view (preWide W view τ (withSetupG setup fix A₀)) ops)) ∧
      ¬ PairTr tag (evalWithAnswerFn (QueryImpl.ofFn T)
          (expLG view (preWide W view τ (withSetupG setup fix A₀)) ops)).2) :
    FreshBad (advBadW W (fun i => (tc i).commit) R view τ (withSetupG setup fix A₀)) T ∅
      ((tableQueryLog (expLG view (preWide W view τ (withSetupG setup fix A₀)) ops) T).map
        Sigma.fst) := by
  -- The run's parts, against the table.
  obtain ⟨hsl, hse⟩ := withSetupG_run setup fix A₀ T
  obtain ⟨hpl, hpe⟩ := preWide_run W view τ (withSetupG setup fix A₀) T
  set A := withSetupG setup fix A₀ with hAdef
  set CC : ℕ → ListCommit M := fun i => (tc i).commit with hCC
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A with hp
  set ch := evalWithAnswerFn (QueryImpl.ofFn T) (W.chain (hashτ τ) (view p).1 (view p).2) with hch
  set lA := tableQueryLog A T with hlA
  set lC := tableQueryLog (W.chain (hashτ τ) (view p).1 (view p).2) T with hlC
  set lO := tableQueryLog (gopsRun view ops p ch) T with hlO
  set bs := evalWithAnswerFn (QueryImpl.ofFn T) (gopsRun view ops p ch) with hbs
  set tA : Transcript := lA.filterMap inlEntry with htA
  set Y := preWide W view τ A >>= fun x => opsOut x <$> gopsRun view ops x.1 x.2.1 with hY
  have hYl : tableQueryLog Y T = (lA ++ lC) ++ lO := by
    rw [hY, tableQueryLog_bind, tableQueryLog_map, hpl, hpe]
  have hYe : evalWithAnswerFn (QueryImpl.ofFn T) Y = ((p, (ch, bs)), tA) := by
    rw [hY, evalWithAnswerFn_bind, evalWithAnswerFn_map, hpe]
    rfl
  obtain ⟨hLl, hLe⟩ := run_logged Y T
  have hlogL : tableQueryLog (expLG view (preWide W view τ A) ops) T = (lA ++ lC) ++ lO := by
    rw [← hYl]
    exact hLl
  have hevalL : evalWithAnswerFn (QueryImpl.ofFn T) (expLG view (preWide W view τ A) ops) =
      (((p, (ch, bs)), tA), ((lA ++ lC) ++ lO).filterMap inlEntry) := by
    rw [← hYl, ← hYe]
    exact hLe
  have hYU : Y = expWide W view τ A (gopsRun view ops) := (expWide_eqG W view τ A ops).symm
  have hlogU : tableQueryLog (expWide W view τ A (gopsRun view ops)) T = (lA ++ lC) ++ lO := by
    rw [← hYU]
    exact hYl
  set zK := evalWithAnswerFn (QueryImpl.ofFn T) (expWide W view τ A (gopsRun view ops)) with hzK
  have hzKe : zK = ((p, (ch, bs)), tA) := by
    rw [hzK, ← hYU]
    exact hYe
  have hK11 : zK.1.1 = p := by rw [hzKe]
  have hK121 : zK.1.2.1 = ch := by rw [hzKe]
  have hK2 : zK.2 = tA := by rw [hzKe]
  -- Every entry of the run's log holds the table's answer.
  have hsnd : ∀ e ∈ (lA ++ lC) ++ lO, e.2 = T e.1 := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · exact tableQueryLog_snd_dep T _ e he
      · exact tableQueryLog_snd_dep T _ e he
    · exact tableQueryLog_snd_dep T _ e he
  -- The event.
  obtain ⟨hB, hnd, hnp⟩ := hev
  rw [hevalL] at hB hnd hnp
  have hBK : BreaksOK W.K CC R view check (fun bs => ∀ k < ops.length, bs.getD k false = true)
      zK := by
    rw [hzKe]
    exact hB
  have hcheck : check p ch := hB.1
  have hverd : ∀ k < ops.length, bs.getD k false = true := hB.2.1
  have hnotdoom : ∀ m (hm : m < ops.length), ¬ GDoomed view ops[m] p ch
      (cacheOfTr (((lA ++ lC) ++ lO).filterMap inlEntry)) :=
    fun m hm hD => hnd ⟨m, hm, hverd m hm, hD⟩
  -- No bad fresh query, from here on.
  rw [hlogL]
  by_contra hnb
  set Lk := ((lA ++ lC) ++ lO).map Sigma.fst with hLkdef
  set L := Lk.filterMap Sum.getLeft? with hLdef
  set LA := (lA.map Sigma.fst).filterMap Sum.getLeft? with hLAdef
  have hk : ¬ FreshBad (kcBadW W CC R τ) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hr : ¬ FreshBad (rootBadK W.K view A) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBadW W CC R τ) (viewT T) ∅ L := fun h =>
    hk (freshBad_kcW W CC R τ T ∅ Lk (by rw [viewH_empty]; exact h))
  have hord := rf_beforeW hl
  have hinj : Set.InjOn (viewT T) ↑L.toFinset := injOn_of_not_freshBadW hl
  have hLk : Lk = lA.map Sigma.fst ++ ((lC ++ lO).map Sigma.fst) := by
    rw [hLkdef]
    simp only [List.map_append, List.append_assoc]
  obtain ⟨rest, hLA⟩ : ∃ rest, L = LA ++ rest :=
    ⟨_, by rw [hLdef, hLk, List.filterMap_append]⟩
  -- No fresh answer after the adversary's queries is a root it announced.
  have hroot : ∀ w ∈ L, viewT T w ∈ W.K.rootsK (view p).2 → w ∈ LA := by
    intro w hw hwr
    by_contra hwA
    have hwk : Sum.inl w ∈ Lk := mem_filterMap_getLeft?.mp hw
    have hwA' : Sum.inl w ∉ lA.map Sigma.fst := fun h => hwA (mem_filterMap_getLeft?.mpr h)
    have nb := not_bad_before (rootBadK W.K view A) T ∅ Lk hr (.inl w) hwk
      (Finset.notMem_empty _)
    rw [Finset.empty_union] at nb
    refine nb ⟨fun q hq => ?_, hwr⟩
    rw [hLk]
    exact subset_before_append _ _ hwA' q hq
  -- A history between the adversary's and the run's reads the adversary's word.
  have hstab : ∀ (H : List (List UInt8)), (∀ y ∈ LA, y ∈ H) → (∀ y ∈ H, y ∈ L) →
      ∀ r ∈ W.K.rootsK (view p).2, ∀ ht ℓ,
        merkleWord H.toFinset (viewT T) ht ℓ r = merkleWord LA.toFinset (viewT T) ht ℓ r := by
    intro H hAH hHL r hr' ht ℓ
    refine merkleWord_stable (H := LA.toFinset) (H' := H.toFinset) (T := viewT T) (r := r)
      (fun y hy => List.mem_toFinset.mpr (hAH y (List.mem_toFinset.mp hy)))
      (fun w hw hwr => List.mem_toFinset.mpr
        (hroot w (hHL w (List.mem_toFinset.mp hw)) (hwr ▸ hr')))
      (fun y hy w hw h => ?_) ht ℓ
    have hyA := List.mem_toFinset.mp hy
    have hyL : y ∈ L := by rw [hLA]; exact List.mem_append_left _ hyA
    have hb := hord w (hHL w (List.mem_toFinset.mp hw)) y hyL (W.refers_rf _ _ h)
    rw [hLA, before_append_of_mem LA rest hyA] at hb
    exact List.mem_toFinset.mpr (mem_of_mem_before LA w y hb)
  have hLAL : ∀ y ∈ LA, y ∈ L := fun y hy => by
    rw [hLA]
    exact List.mem_append_left _ hy
  -- An undoomed opening has a candidate of the run's word satisfying its claims.
  have hcand : ∀ m (hm : m < ops.length) (o : GOp Pf F M), ops[m] = o →
      ∃ q ∈ Candidates o.μ o.R (code₀ o.μ o.R).thr
          (Rom.extract (ansOf L.toFinset (viewT T)) (ofB (GOp.root view o p))
            (rootHeight o.μ o.R) (2 ^ laneFold)),
        o.holds p ch q := by
    intro m hm o ho
    have hd := hnotdoom m hm
    rw [ho] at hd
    unfold GDoomed at hd
    push Not at hd
    obtain ⟨q, hq, hqc⟩ := hd
    rw [cacheOfTr_eq_ansOf T _ hsnd] at hq
    exact ⟨q, hq, hqc⟩
  -- Every round with a root has a candidate, read off the adversary's queries, that is good.
  have htrH : histOfTr tA = LA.toFinset := by
    simp only [histOfTr, htA, hLAdef, map_fst_filterMap_inlEntry]
  have htrT : ∀ d ∈ histOfTr tA, tableOfTr tA d = viewT T d := by
    intro d hd
    refine tableOfTr_eq (viewT T) tA (fun e he => ?_) d (by simpa [histOfTr] using hd)
    obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp he
    obtain ⟨d', u⟩ := q
    cases d' with
    | inl x =>
      simp only [inlEntry, Option.some.injEq] at hqe
      subst hqe
      have := tableQueryLog_snd_dep T _ _ hq
      simp only at this
      simp [viewT, this]
    | inr s => simp [inlEntry] at hqe
  have hfit' := hfit p ch hcheck
  have hD : ∀ i < W.K.rounds.length, (W.K.spec i).root →
      ¬ DoomK CC view (gopW ops check good goodS) i zK := by
    intro i hi hri hDK
    obtain ⟨o, hoops, rd, htgt⟩ := hcov i hi hri
    obtain ⟨m, hm, ho⟩ := List.mem_iff_getElem.mp hoops
    obtain ⟨q, hq, hqc⟩ := hcand m hm o ho
    have hokO : GOp.OK tc good setup fix o := hok o hoops
    obtain ⟨r, hmr, hrr⟩ := exists_root_of_fits W.K hfit' i hi hri
    unfold GOp.OK at hokO
    rw [htgt] at hokO
    obtain ⟨hht, hlf, hcomp, hgood⟩ := hokO
    have hroot_o : GOp.root view o p = r := by
      unfold GOp.root
      rw [htgt]
      show ((msgK view p i).1).getD (Vector.replicate 32 0) = r
      simp only [msgK]
      rw [hmr]
      rfl
    rw [hroot_o] at hq
    have hword := candidates_congr (μ := o.μ) (R := o.R)
      (A := (code₀ o.μ o.R).thr)
      (W := Rom.extract (ansOf L.toFinset (viewT T)) (ofB r) (rootHeight o.μ o.R)
        (2 ^ laneFold))
      (W' := wordOfMerkle (rootHeight o.μ o.R) (2 ^ laneFold)
        (merkleWord L.toFinset (viewT T) (rootHeight o.μ o.R) (8 * 2 ^ laneFold)
          (toB (ofB r))))
      fun v hv => (wordOfMerkle_eq_extract hinj _ _ _ hv).symm
    have htoB : toB (ofB r) = r := LeanVM.Rpm.digestToRpm_ofRpm _
    rw [hword, htoB, hstab L hLAL (fun y hy => hy) r hrr] at hq
    have hmem : rd q ∈ (tc i).dec
        (merkleWord LA.toFinset (viewT T) (tc i).height (tc i).leafLen r) :=
      hcomp _ q (by rw [hht, hlf]; exact hq)
    have hgq : good i p ch (some (rd q)) := hgood p ch q hqc
    obtain ⟨-, hdoom⟩ := hDK
    refine hdoom (some (rd q)) ?_ ?_
    · rw [hK2, hK11, optC_congr (CC i) htrT, htrH]
      unfold optC
      simp only [msgK] at hmr ⊢
      rw [hmr]
      exact List.mem_map.mpr ⟨rd q, hmem, rfl⟩
    · rw [hK11, hK121]
      exact hgq
  -- Every setup opening's stack satisfies its claims.
  have hSH : ∀ o ∈ ops, GOp.SetupHolds o p ch := by
    intro o hoops
    obtain ⟨m, hm, ho⟩ := List.mem_iff_getElem.mp hoops
    obtain ⟨q, hq, hqc⟩ := hcand m hm o ho
    have hokO : GOp.OK tc good setup fix o := hok o hoops
    unfold GOp.SetupHolds
    unfold GOp.OK at hokO
    rcases htg : o.tgt with ⟨i, rd⟩ | ⟨root, q₀⟩
    · trivial
    · rw [htg] at hokO
      obtain ⟨word, hhon, hsw⟩ := hokO
      have hsub : ∀ x, Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst →
          x ∈ L.toFinset := by
        intro x hx
        refine List.mem_toFinset.mpr (hLAL x (mem_filterMap_getLeft?.mpr ?_))
        rw [hsl, List.map_append]
        exact List.mem_append_left _ hx
      have hroot_o : GOp.root view o p = root p := by
        unfold GOp.root
        rw [htg]
      rw [hroot_o, hse] at hq
      have hword := candidates_congr (μ := o.μ) (R := o.R)
        (A := (code₀ o.μ o.R).thr)
        (W := Rom.extract (ansOf L.toFinset (viewT T))
          (ofB (root (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup)
            (evalWithAnswerFn (QueryImpl.ofFn T)
              (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup))))))
          (rootHeight o.μ o.R) (2 ^ laneFold))
        (W' := word) fun v hv => hsw T L.toFinset
          (evalWithAnswerFn (QueryImpl.ofFn T) (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup)))
          hsub hinj v hv
      rw [hword] at hq
      have hq₀ := candidates_honest o.adm hhon hq
      subst hq₀
      exact hqc
  have hgS : goodS p ch := hS p ch hSH
  -- The seed: no answer of the run is the label's first 32 bytes, else a pair.
  have hseed : ∀ z ∈ ((tableQueryLog (expWide W view τ A (gopsRun view ops)) T).map
      Sigma.fst).filterMap Sum.getLeft?,
      (viewT T z).toList ≠ (W.label (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).1).take 32 := by
    obtain ⟨w, hwA, hw⟩ := hlabT
    intro z hz hzl
    rw [hlogU] at hz
    refine hnp ⟨(z, viewT T z), mem_filterMap_inlEntry T _ hsnd (mem_filterMap_getLeft?.mp hz),
      (w, viewT T w), mem_filterMap_inlEntry T _ hsnd ?_, ?_⟩
    · rw [List.map_append, List.map_append]
      exact List.mem_append_left _ (List.mem_append_left _ hwA)
    · exact hzl.trans hw
  -- The list game, then a bad fresh query.
  have hBK' := breaksK_of_breaksOKG W.K CC R view ops check good goodS zK hBK
  rcases breaksU_imp W.K CC R view (gopW ops check good goodS) (fun π ch' _ h => hfit π ch' h)
      (fun π ch' _ cs h hl' hg hn hs => hlink π ch' cs h hl' hg hn hs) zK hBK' with
    ⟨i, hi, hri, hDK⟩ | hDS | hwin
  · exact hD i hi hri hDK
  · obtain ⟨-, hng⟩ := hDS
    refine hng ?_
    show goodS zK.1.1 zK.1.2.1
    rw [hK11, hK121]
    exact hgS
  · have := trace_advW W CC R view τ A (gopsRun view ops) T hseed hwin
    rw [hlogU] at this
    exact hnb this

/-! ## Knowledge soundness, the seed separated by a pair of answers -/


end Trace

end Compose

/-- info: 'Compose.trace_whirWG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.trace_whirWG
