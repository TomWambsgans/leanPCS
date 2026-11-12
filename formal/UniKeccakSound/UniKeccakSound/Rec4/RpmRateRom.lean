-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Adapted from leanerVM `mumbai`
-- (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0:
-- `lean_vm/LeanVM/Protocol/Rpm/RomRelabel.lean`'s `cmap`, `step_toRHF`, `run'_toRHF`, `step_ofRHF`, `run_ofRHF`,
-- `isWeightBound_advImpl2`, `isWeightBound_simulateQ_ofRHF`; `Rpm/Paths.lean`'s `step_replayOf`) and from this
-- repository's `formal/Compose/Compose/Rpm.lean` (`advImpl2_logRelC`, `CacheRel`, `cacheRel_step`, `cacheRel_run`,
-- `pathsOf_ideal2C`, `adv_cache`), on `RState` and the rate model.
import UniKeccakSound.Rec4.RpmRateGame

/-!
# The rate model's random oracles against the transfer's on `RState`

* `cmapR`: a cache of the random oracles on `RState` read in the rate model (`rbij`, `rEquiv`);
* `run'_toRHFR`, `run_ofRHFR`: a computation of the rate model read on `RState`, and back, has the same distribution
  against the random oracles, the caches related by `cmapR`;
* `evalTr_eq`: the Keccak-256 evaluations of a transcript (`Compose.evalTr`, digests) are its sponge paths on `RState`
  (`transcriptPathsR`, whole rates), the rates read as their digests (`replay_mapK`: the two bookkeepings);
* **`adv_cacheSR`**: after the adversary with the simulator, the cache's `H` answers are the setup's and exactly the
  sponge paths of the adversary's transcript.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace UniKeccakSound.Rec4

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Common (KCap)
open Compose (TailP KeccakCallsR liftR loggedKCR Transcript loggedKC evalTr RpmOutTG)
open LeanVM.Rpm (HOnly DuplexVm AdmissibleVm StRel)

/-- The rate model's two oracles, with coins. -/
abbrev CSpecR := unifSpec + KeccakCallsR

/-! ## Caches -/

/-- A cache of the random oracles on `RState`, read in the rate model. -/
def cmapR (c : HFSR.QueryCache) : KeccakCallsR.QueryCache :=
  QueryCache.ofFn fun
    | .inl m => (c (.inl m)).map rbij
    | .inr s => (c (.inr (rEquiv s))).map rEquiv.symm

theorem cmapR_empty : cmapR ∅ = ∅ := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m | s <;> rfl

@[simp] theorem cmapR_inl (c : HFSR.QueryCache) (m : List UInt8) :
    cmapR c (.inl m) = (c (.inl m)).map rbij := rfl

@[simp] theorem cmapR_inr (c : HFSR.QueryCache) (s : KeccakState) :
    cmapR c (.inr s) = (c (.inr (rEquiv s))).map rEquiv.symm := rfl

theorem cmapR_cacheQuery_inl (c : HFSR.QueryCache) (m : List UInt8) (u : RateBytes) :
    cmapR (c.cacheQuery (.inl m) u) = (cmapR c).cacheQuery (.inl m) (rbij u) := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m' | s
  · by_cases h : m' = m
    · subst h; simp
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h), cmapR_inl, cmapR_inl,
        QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp), cmapR_inr, cmapR_inr,
      QueryCache.cacheQuery_of_ne _ _ (by simp)]

theorem cmapR_cacheQuery_inr (c : HFSR.QueryCache) (x u : RState) :
    cmapR (c.cacheQuery (.inr x) u) = (cmapR c).cacheQuery (.inr (rEquiv.symm x)) (rEquiv.symm u) := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m | s
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp), cmapR_inl, cmapR_inl,
      QueryCache.cacheQuery_of_ne _ _ (by simp)]
  · by_cases h : s = rEquiv.symm x
    · subst h
      rw [cmapR_inr, Equiv.apply_symm_apply, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
      rfl
    · have h' : rEquiv s ≠ x := fun e ↦ h (by rw [← e, Equiv.symm_apply_apply])
      rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h), cmapR_inr, cmapR_inr,
        QueryCache.cacheQuery_of_ne _ _ (by simpa using h')]

theorem cmapR_cacheQuery_inr' (c : HFSR.QueryCache) (x : KeccakState) (u : RState) :
    cmapR (c.cacheQuery (.inr (rEquiv x)) u) = (cmapR c).cacheQuery (.inr x) (rEquiv.symm u) := by
  have h := cmapR_cacheQuery_inr c (rEquiv x) u
  rwa [Equiv.symm_apply_apply] at h

/-! ## The rate model's calls read on `RState` -/

theorem step_toRHFR (t : KeccakCallsR.Domain) (c : HFSR.QueryCache) :
    Prod.map id cmapR <$> ((HFSR.romImpl ∘ₛ toRHFR) t).run c =ᵈ
      (KeccakCallsR.randomOracle t).run (cmapR c) := by
  rcases t with m | x
  · rw [QueryImpl.apply_compose]
    simp only [toRHFR, simulateQ_map, StateT.run_map, Common.run_hq, Functor.map_map]
    rw [randomOracle.run_eq, cmapR_inl]
    rcases h : c (.inl m) with _ | u
    · simp only [Common.roStep_of_none h, Option.map_none, map_bind, map_pure, Prod.map,
        id, cmapR_cacheQuery_inl]
      refine EvalDistEq.trans ?_ (EvalDistEq.bind_left
        (SampleableType.map_uniformSample_evalDistEq_of_bijective rbij.bijective)
        (fun d ↦ (pure (d, (cmapR c).cacheQuery (.inl m) d) : ProbComp _)))
      rw [bind_map_left]
      exact EvalDistEq.rfl
    · simp only [Common.roStep_of_some h, Option.map_some, map_pure]
      exact EvalDistEq.rfl
  · rw [QueryImpl.apply_compose]
    simp only [toRHFR, simulateQ_map, StateT.run_map, Common.run_hq, Functor.map_map]
    rw [randomOracle.run_eq, cmapR_inr]
    rcases h : c (.inr (rEquiv x)) with _ | u
    · simp only [Common.roStep_of_none h, Option.map_none, map_bind, map_pure, Prod.map,
        id, cmapR_cacheQuery_inr']
      refine EvalDistEq.trans ?_ (EvalDistEq.bind_left
        (SampleableType.map_uniformSample_evalDistEq_of_bijective rEquiv.symm.bijective)
        (fun d ↦ (pure (d, (cmapR c).cacheQuery (.inr x) d) : ProbComp _)))
      rw [bind_map_left]
      exact EvalDistEq.rfl
    · simp only [Common.roStep_of_some h, Option.map_some, map_pure]
      exact EvalDistEq.rfl

/-- **The rate model's calls read on `RState`**: against the two random oracles on `RState`, the outputs are those
against the rate model's random oracles, the caches related by `cmapR`. -/
theorem run'_toRHFR {β : Type} (V : OracleComp KeccakCallsR β) (c : HFSR.QueryCache) :
    (simulateQ HFSR.romImpl (simulateQ toRHFR V)).run' c =ᵈ
      (simulateQ KeccakCallsR.randomOracle V).run' (cmapR c) := by
  rw [← QueryImpl.simulateQ_compose]
  exact Common.run'_simulateQ_evalDistEq_of_inv _ _ (fun _ ↦ True) cmapR
    (fun _ _ _ _ _ ↦ trivial) (fun t c _ ↦ step_toRHFR t c) V c trivial

/-- The transfer's oracles on `RState` read in the rate model: coins, `H` (through `rbij`), the permutation. -/
def ofRHFR : QueryImpl HFSpecR (OracleComp CSpecR)
  | .inl n => liftM (CSpecR.query (.inl n))
  | .inr (.inl m) => rbij.symm <$> (liftM (CSpecR.query (.inr (.inl m))) : OracleComp CSpecR (Digest × TailP))
  | .inr (.inr x) =>
    rEquiv <$> (liftM (CSpecR.query (.inr (.inr (rEquiv.symm x)))) : OracleComp CSpecR KeccakState)

theorem cmapR_inr_ofR (c : HFSR.QueryCache) (x : RState) :
    cmapR c (.inr (rEquiv.symm x)) = (c (.inr x)).map rEquiv.symm := by
  rw [cmapR_inr, Equiv.apply_symm_apply]

theorem step_ofRHFR (t : HFSpecR.Domain) (c : HFSR.QueryCache) :
    Prod.map id cmapR <$> (HFSR.romImpl t).run c =ᵈ ((KeccakCallsR.romImpl ∘ₛ ofRHFR) t).run (cmapR c) := by
  rcases t with n | m | x
  · rw [QueryImpl.apply_compose]
    simp only [ofRHFR, simulateQ_spec_query, roSim.run_apply_inl, Functor.map_map]
    exact EvalDistEq.rfl
  · rw [QueryImpl.apply_compose]
    simp only [ofRHFR, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      OracleSpec.romImpl_apply_inr, randomOracle.run_eq, cmapR_inl]
    rcases h : c (.inl m) with _ | u
    · simp only [Option.map_none, map_bind, map_pure, Prod.map, id, cmapR_cacheQuery_inl]
      refine EvalDistEq.symm (EvalDistEq.trans (EvalDistEq.bind_left
        (SampleableType.map_uniformSample_evalDistEq_of_bijective rbij.bijective).symm
        (fun d ↦ (pure (rbij.symm d, (cmapR c).cacheQuery (.inl m) d) : ProbComp _))) ?_)
      rw [bind_map_left]
      simp only [Equiv.symm_apply_apply]
      exact EvalDistEq.rfl
    · simp only [Option.map_some, map_pure, Prod.map, id, Equiv.symm_apply_apply]
      exact EvalDistEq.rfl
  · rw [QueryImpl.apply_compose]
    simp only [ofRHFR, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      OracleSpec.romImpl_apply_inr, randomOracle.run_eq, cmapR_inr_ofR]
    rcases h : c (.inr x) with _ | u
    · simp only [Option.map_none, map_bind, map_pure, Prod.map, id, cmapR_cacheQuery_inr]
      refine EvalDistEq.symm (EvalDistEq.trans (EvalDistEq.bind_left
        (SampleableType.map_uniformSample_evalDistEq_of_bijective rEquiv.symm.bijective).symm
        (fun d ↦ (pure (rEquiv d, (cmapR c).cacheQuery (.inr (rEquiv.symm x)) d) : ProbComp _))) ?_)
      rw [bind_map_left]
      simp only [Equiv.apply_symm_apply]
      exact EvalDistEq.rfl
    · simp only [Option.map_some, map_pure, Prod.map, id, Equiv.apply_symm_apply]
      exact EvalDistEq.rfl

/-- **A computation on the oracles on `RState`, read in the rate model**: against the rate model's random oracles
(with coins), it is the computation against the oracles on `RState`, the final cache read through `cmapR`. -/
theorem run_ofRHFR {α : Type} (X : OracleComp HFSpecR α) (c : HFSR.QueryCache) :
    (simulateQ KeccakCallsR.romImpl (simulateQ ofRHFR X)).run (cmapR c) =ᵈ
      Prod.map id cmapR <$> (simulateQ HFSR.romImpl X).run c := by
  rw [← QueryImpl.simulateQ_compose]
  exact (Common.map_run_simulateQ_evalDistEq_of_inv _ _ (fun _ ↦ True) cmapR
    (fun _ _ _ _ _ ↦ trivial) (fun t c _ ↦ step_ofRHFR t c) X c trivial).symm

/-! ## The transcript's sponge paths on `RState` -/

/-- A transcript entry, on `RState`. -/
def entryR (e : Common.PermutationQuery KeccakState × KeccakState) : Common.PermutationQuery RState × RState :=
  (LeanVM.Rpm.mapQ rEquiv e.1, rEquiv e.2)

/-- A transcript entry on `RState`, on lanes. -/
def entryOfR (e : Common.PermutationQuery RState × RState) : Common.PermutationQuery KeccakState × KeccakState :=
  (LeanVM.Rpm.mapQ rEquiv.symm e.1, rEquiv.symm e.2)

theorem entryR_ofR (e : Common.PermutationQuery RState × RState) : entryR (entryOfR e) = e := by
  obtain ⟨q, y⟩ := e
  cases q <;> simp [entryR, entryOfR, LeanVM.Rpm.mapQ]

theorem entryOfR_R (e : Common.PermutationQuery KeccakState × KeccakState) : entryOfR (entryR e) = e := by
  obtain ⟨q, y⟩ := e
  cases q <;> simp [entryR, entryOfR, LeanVM.Rpm.mapQ]

/-- **The sponge paths a transcript holds, on `RState`**: messages with the whole rate of their paths' ends. -/
def transcriptPathsR (T : PermutationTranscript) : List (List UInt8 × RateBytes) :=
  Common.pathsOf keccakPaddingR RState.zero (T.map entryR)

/-- A byte state's bookkeeping on `RState`. -/
def mapK (σ : Common.SimState Common.DigestBytes Common.KRest KCap) : Common.SimState RateBytes Rate0 KCap :=
  ⟨LeanVM.Rpm.logMap kEquivR σ.edges, σ.chains.map fun p ↦ (kEquivR p.1, p.2.map kBlockEquiv)⟩

theorem kEquivR_snd (k : Common.KState) : (kEquivR k).2 = k.2 := rfl

theorem fwdLookup_mapK (E : Common.PermutationEdges Common.KState) (x : Common.KState) :
    Common.forwardLookup (LeanVM.Rpm.logMap kEquivR E) (kEquivR x) = (Common.forwardLookup E x).map kEquivR := by
  have h := LeanVM.Rpm.fwdLookup_logMap kEquivR.symm E (kEquivR x)
  simpa using h

theorem invLookup_mapK (E : Common.PermutationEdges Common.KState) (y : Common.KState) :
    Common.inverseLookup (LeanVM.Rpm.logMap kEquivR E) (kEquivR y) = (Common.inverseLookup E y).map kEquivR := by
  have h := LeanVM.Rpm.invLookup_logMap kEquivR.symm E (kEquivR y)
  simpa using h

theorem chainOf_mapK (VC : List (Common.KState × List Common.KBlock)) (x : Common.KState) :
    Common.chainOf (VC.map fun p ↦ (kEquivR p.1, p.2.map kBlockEquiv)) (kEquivR x) =
      (Common.chainOf VC x).map fun p ↦ (kEquivR p.1, p.2.map kBlockEquiv) := by
  unfold Common.chainOf
  rw [List.find?_map]
  rfl

/-- **One step of the bookkeeping on `RState` is one step on bytes, relabelled.** -/
theorem replayStep_mapK (σ : Common.SimState Common.DigestBytes Common.KRest KCap)
    (e : Common.PermutationQuery Common.KState × Common.KState) :
    Common.replayStep (mapK σ) (LeanVM.Rpm.mapQ kEquivR e.1, kEquivR e.2) = mapK (Common.replayStep σ e) := by
  obtain ⟨q, y⟩ := e
  cases q with
  | forward x =>
    simp only [LeanVM.Rpm.mapQ, Common.replayStep, mapK, fwdLookup_mapK]
    rcases hf : Common.forwardLookup σ.edges x with _ | z
    · simp only [Option.map_none, chainOf_mapK]
      rcases hc : Common.chainOf σ.chains x with _ | ⟨s, β⟩
      · simp [LeanVM.Rpm.logMap]
      · simp [LeanVM.Rpm.logMap, blockTo_kEquivR]
    · simp
  | inverse y' =>
    simp only [LeanVM.Rpm.mapQ, Common.replayStep, mapK, invLookup_mapK]
    rcases hf : Common.inverseLookup σ.edges y' with _ | z
    · simp [LeanVM.Rpm.logMap]
    · simp

theorem foldl_mapK (log : List (Common.PermutationQuery Common.KState × Common.KState))
    (σ : Common.SimState Common.DigestBytes Common.KRest KCap) :
    (log.map fun e ↦ (LeanVM.Rpm.mapQ kEquivR e.1, kEquivR e.2)).foldl Common.replayStep (mapK σ) =
      mapK (log.foldl Common.replayStep σ) := by
  induction log generalizing σ with
  | nil => rfl
  | cons e log ih => simp only [List.map_cons, List.foldl_cons, replayStep_mapK, ih]

theorem mapK_init : mapK (Common.SimState.init Common.KState.zero) = Common.SimState.init RState.zero := by
  simp [mapK, Common.SimState.init, LeanVM.Rpm.logMap, kEquivR_zero]

/-- **The bookkeeping on `RState` is the one on bytes, relabelled.** -/
theorem replay_mapK (log : List (Common.PermutationQuery Common.KState × Common.KState)) :
    Common.replay RState.zero (log.map fun e ↦ (LeanVM.Rpm.mapQ kEquivR e.1, kEquivR e.2)) =
      mapK (Common.replay Common.KState.zero log) := by
  rw [Common.replay, Common.replay, ← mapK_init, foldl_mapK]

theorem unpadR_map (β : List Common.KBlock) : keccakPaddingR.unpad (β.map kBlockEquiv) = Common.keccakPadding.unpad β := by
  show Common.keccakPadding.unpad ((β.map kBlockEquiv).map kBlockEquiv.symm) = _
  rw [List.map_map]
  simp

theorem simPaths_mapK (σ : Common.SimState Common.DigestBytes Common.KRest KCap) :
    Common.simPaths Common.keccakPadding σ =
      (Common.simPaths keccakPaddingR (mapK σ)).map fun p ↦ (p.1, dgOf p.2) := by
  simp only [Common.simPaths, mapK, List.filterMap_map, List.map_filterMap]
  refine List.filterMap_congr fun p _ ↦ ?_
  simp only [Function.comp_apply, unpadR_map]
  generalize Common.keccakPadding.unpad p.2 = o
  cases o with
  | none => rfl
  | some m => simp only [Option.map_some, dgOf_kEquivR]

theorem entryR_eq (e : Common.PermutationQuery KeccakState × KeccakState) :
    entryR e = (LeanVM.Rpm.mapQ kEquivR (LeanVM.Rpm.entryToRpm e).1, kEquivR (LeanVM.Rpm.entryToRpm e).2) := by
  obtain ⟨q, y⟩ := e
  cases q <;> rfl

/-- **The byte paths of a transcript are its paths on `RState`, their rates read as digests.** -/
theorem transcriptPathsB_eq (T : PermutationTranscript) :
    LeanVM.Rpm.transcriptPathsB T = (transcriptPathsR T).map fun p ↦ (p.1, dgOf p.2) := by
  have hT : T.map entryR = (T.map LeanVM.Rpm.entryToRpm).map fun e ↦ (LeanVM.Rpm.mapQ kEquivR e.1, kEquivR e.2) := by
    rw [List.map_map]
    exact List.map_congr_left fun e _ ↦ entryR_eq e
  rw [transcriptPathsR, Common.pathsOf, hT, replay_mapK, ← simPaths_mapK]
  rfl

/-- **The Keccak-256 evaluations of a transcript are its sponge paths on `RState`, the rates read as digests.** -/
theorem evalTr_eq (T : PermutationTranscript) :
    evalTr T = (transcriptPathsR T).map fun p ↦ (p.1, dgOf p.2) := by
  rw [evalTr, LeanVM.Rpm.transcriptPaths_eq, List.map_map, ← transcriptPathsB_eq]
  conv_rhs => rw [← List.map_id (LeanVM.Rpm.transcriptPathsB T)]
  refine List.map_congr_left fun p _ ↦ ?_
  simp only [Function.comp_apply, id]
  rw [show Compose.toB (LeanVM.Digest.ofRpm p.2) = p.2 from LeanVM.Rpm.digestToRpm_ofRpm p.2]

/-- The evaluation of `x` among the paths on `RState`, its digest. -/
def hashesOfR (P : List (List UInt8 × RateBytes)) (x : List UInt8) : Option Digest :=
  (P.find? (·.1 = x)).map fun p ↦ (rbij p.2).1

theorem lookTr_evalTr (T : PermutationTranscript) (x : List UInt8) :
    Compose.lookTr (evalTr T) x = hashesOfR (transcriptPathsR T) x := by
  rw [evalTr_eq, Compose.lookTr, hashesOfR, List.find?_map, Option.map_map]
  simp only [Function.comp_def, rbij_fst]

/-! ## The adversary's cache -/

/-- The simulator's bookkeeping on `RState`. -/
abbrev RSim := Common.SimState RateBytes Rate0 KCap

/-- A transcript on `RState`. -/
abbrev RLogR := List (Common.PermutationQuery RState × RState)

/-- **The lane transcript is the log on `RState`**, coins included. -/
theorem advImpl2_logRelCR {α : Type} (B : OracleComp Common.RandomPermutationOracles α)
    (T : PermutationTranscript) (σ : RSim) :
    (fun x ↦ (x.1.1, (x.2, x.1.2.map entryR))) <$>
        (simulateQ (Common.advImpl2 keccakPaddingR) ((simulateQ logRelCR B).run T)).run σ =
      (simulateQ (Common.advImplLog2 keccakPaddingR) (simulateQ relPCR B)).run (σ, T.map entryR) := by
  induction B using OracleComp.inductionOn generalizing T σ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | q
    · simp only [StateT.run_bind, OracleQuery.input_query, relPCR, logRelCR,
        StateT.run_mk, bind_map_left, simulateQ_bind, simulateQ_query,
        OracleQuery.cont_query, id_map, map_bind]
      have h2 : (Common.advImplLog2 keccakPaddingR (.inl n)).run (σ, T.map entryR) =
          (fun z ↦ (z.1, (z.2, T.map entryR))) <$>
            (Common.advImpl2 (Msg := List UInt8) keccakPaddingR (.inl n)).run σ := rfl
      rw [h2, bind_map_left]
      refine bind_congr fun z ↦ ?_
      rw [← ih]
    · simp only [StateT.run_bind, OracleQuery.input_query, relPCR, relPR, logRelCR, logRelR,
        StateT.run_mk, bind_map_left, simulateQ_bind, simulateQ_query,
        OracleQuery.cont_query, id_map, map_bind]
      have h1 : (Common.advImpl2 keccakPaddingR (.inr (.inr (LeanVM.Rpm.mapQ rEquiv q)))).run σ =
          (Common.simulator2 (Msg := List UInt8) keccakPaddingR (LeanVM.Rpm.mapQ rEquiv q)).run σ := rfl
      have h2 : (Common.advImplLog2 keccakPaddingR (.inr (.inr (LeanVM.Rpm.mapQ rEquiv q)))).run
          (σ, T.map entryR) = (fun z ↦ (z.1, (z.2, T.map entryR ++
            [(LeanVM.Rpm.mapQ rEquiv q, z.1)]))) <$>
              (Common.simulator2 (Msg := List UInt8) keccakPaddingR (LeanVM.Rpm.mapQ rEquiv q)).run σ :=
        rfl
      rw [h1, h2, bind_map_left]
      refine bind_congr fun z ↦ ?_
      have e : T.map entryR ++ [(LeanVM.Rpm.mapQ rEquiv q, z.1)] =
          (T ++ [(q, rEquiv.symm z.1)]).map entryR := by
        simp [entryR]
      rw [e, ← ih]

/-- The transfer's adversary is the adversary with the simulator logging the queries on `RState`, its log read on
lanes. -/
theorem advS2_advBSR {Pf σ : Type} (A : σ → OracleComp Common.RandomPermutationOracles Pf) (x : σ × Transcript) :
    Common.advS2 keccakPaddingR RState.zero (advBSR A x) =
      (fun y ↦ (y.1, y.2.2.map entryOfR)) <$>
        (simulateQ (Common.advImplLog2 keccakPaddingR) (simulateQ relPCR (A x.1))).run
          (Common.SimState.init RState.zero, []) := by
  have h := advImpl2_logRelCR (A x.1) [] (Common.SimState.init RState.zero)
  rw [List.map_nil] at h
  rw [← h, Functor.map_map, Common.advS2, advBSR, StateT.run'_eq]
  congr 1
  funext y
  simp only [List.map_map]
  have e : entryOfR ∘ entryR = id := funext entryOfR_R
  rw [e, List.map_id]

/-- **Every `H` answer in the cache was there at the start or is a rooted path's.** -/
def CacheRelR (c₀ : HFSR.QueryCache) (σ : RSim) (c : HFSR.QueryCache) : Prop :=
  ∀ m d, c (.inl m) = some d → c₀ (.inl m) = some d ∨ (m, d) ∈ Common.simPaths keccakPaddingR σ

theorem mem_simPaths_consR {σ : RSim} {E : Common.PermutationEdges RState} {e : RState × List RBlock}
    {md : List UInt8 × RateBytes} (h : md ∈ Common.simPaths keccakPaddingR σ) :
    md ∈ Common.simPaths keccakPaddingR (⟨E, e :: σ.chains⟩ : RSim) := by
  simp only [Common.simPaths, List.filterMap_cons] at h ⊢
  split <;> simp_all

/-- **One step of the simulator keeps the relation.** -/
theorem cacheRel_stepR (c₀ : HFSR.QueryCache) (q : Common.PermutationQuery RState) (σ : RSim) (c : HFSR.QueryCache)
    (h : CacheRelR c₀ σ c) {v : (RState × RSim) × HFSR.QueryCache}
    (hv : v ∈ support ((simulateQ HFSR.romImpl
      ((Common.simulator2 (Msg := List UInt8) keccakPaddingR q).run σ)).run c)) :
    CacheRelR c₀ v.1.2 v.2 := by
  cases q with
  | inverse y =>
    simp only [Common.simulator2, StateT.run_mk] at hv
    split at hv
    · simp at hv; subst hv; exact h
    · simp only [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM_run, simulateQ_pure,
        StateT.run_pure, bind_map_left, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hv
      obtain ⟨_, -, rfl⟩ := hv
      exact h
  | forward x =>
    simp only [Common.simulator2, StateT.run_mk] at hv
    split at hv
    · simp at hv; subst hv; exact h
    · split at hv
      · next s β hch =>
        simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        rcases hm : keccakPaddingR.unpad (β ++ [Common.blockTo s x]) with _ | m
        · rw [Common.rootedAnswer2_run_none _ hm] at hw
          obtain ⟨-, -, hc⟩ := Common.roStep_support _ c hw
          intro m' d hd
          rw [hc _ (by simp)] at hd
          exact (h m' d hd).imp_right mem_simPaths_consR
        · rw [Common.rootedAnswer2_run_some _ hm] at hw
          simp only [mem_support_bind_iff, support_uniformSample, Set.mem_univ, true_and,
            support_pure, Set.mem_singleton_iff] at hw
          obtain ⟨w', hw', ec, rfl⟩ := hw
          obtain ⟨-, hself, hc⟩ := Common.roStep_support _ c hw'
          intro m' d hd
          by_cases hmm : m' = m
          · subst hmm
            rw [hself, Option.some_inj] at hd
            subst hd
            exact Or.inr (by simp [Common.simPaths, hm])
          · rw [hc _ (by simpa using hmm)] at hd
            exact (h m' d hd).imp_right mem_simPaths_consR
      · simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          Common.fQuery_run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        obtain ⟨-, -, hc⟩ := Common.roStep_support _ c hw
        intro m' d hd
        rw [hc _ (by simp)] at hd
        exact h m' d hd

/-- A coin of the adversary changes neither the simulator's state nor the cache. -/
theorem foldRO_coinR (n : ℕ) (s : (RSim × RLogR) × HFSR.QueryCache)
    {v : RSpecR.Range (.inl n) × (RSim × RLogR) × HFSR.QueryCache}
    (hv : v ∈ support ((Common.foldRO (Common.advImplLog2 (Msg := List UInt8) keccakPaddingR)
      (.inl n)).run s)) : v.2 = s := by
  rw [Common.foldRO_run] at hv
  simp only [Common.advImplLog2, Common.advImpl2, StateT.run_mk, support_map,
    Set.mem_image] at hv
  obtain ⟨y, hy, rfl⟩ := hv
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  simp only [StateT.run_monadLift, monadLift_self, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hy'
  obtain ⟨x, hx, rfl⟩ := hy'
  rw [simulateQ_romImpl_liftM_run, support_map] at hx
  obtain ⟨u, -, rfl⟩ := hx
  rfl

/-- **The relation along the adversary's run**, coins included. -/
theorem cacheRel_runR {α : Type} (c₀ : HFSR.QueryCache) (B : OracleComp Common.RandomPermutationOracles α)
    (s : (RSim × RLogR) × HFSR.QueryCache) (hs : CacheRelR c₀ s.1.1 s.2) :
    ∀ w ∈ support ((simulateQ (Common.foldRO
        (Common.advImplLog2 (Msg := List UInt8) keccakPaddingR)) (simulateQ relPCR B)).run s),
      CacheRelR c₀ w.2.1.1 w.2.2 := by
  induction B using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro w hw
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact hs
  | query_bind t k ih =>
    intro w hw
    rcases t with n | q
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, relPCR, StateT.run_bind, mem_support_bind_iff] at hw
      obtain ⟨v, hv, hw⟩ := hw
      refine ih _ v.2 ?_ w hw
      rw [foldRO_coinR n s hv]
      exact hs
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, relPCR, relPR, bind_map_left, StateT.run_bind, mem_support_bind_iff] at hw
      obtain ⟨v, hv, hw⟩ := hw
      refine ih _ v.2 ?_ w hw
      rw [Common.foldRO_run] at hv
      simp only [support_map, Set.mem_image] at hv
      obtain ⟨y, hy, rfl⟩ := hv
      have e : (Common.advImplLog2 (Msg := List UInt8) keccakPaddingR
          (.inr (.inr (LeanVM.Rpm.mapQ rEquiv q)))).run s.1 =
          (fun z ↦ (z.1, (z.2, s.1.2 ++ [(LeanVM.Rpm.mapQ rEquiv q, z.1)]))) <$>
            (Common.simulator2 (Msg := List UInt8) keccakPaddingR (LeanVM.Rpm.mapQ rEquiv q)).run s.1.1 := rfl
      rw [e, simulateQ_map, StateT.run_map, support_map] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      exact cacheRel_stepR c₀ _ _ _ hs hu

/-- **The hash queries of the adversary's transcript are cached**, from any starting cache. -/
theorem pathsOf_ideal2CR {α : Type} (X : OracleComp RSpecR α) (c₀ : HFSR.QueryCache) {z}
    (hz : z ∈ support ((simulateQ (Common.foldRO (Common.advImplLog2 (Msg := List UInt8)
      keccakPaddingR)) X).run ((Common.SimState.init RState.zero, []), c₀))) :
    ∀ md ∈ Common.pathsOf keccakPaddingR RState.zero z.2.1.2, z.2.2 (.inl md.1) = some md.2 := by
  have hRO := Common.inv_of_mem_support_run (spec' := unifSpec)
    (Common.foldRO (Common.advImplLog2 (Msg := List UInt8) keccakPaddingR))
    (fun s ↦ ∀ md ∈ Common.simPaths keccakPaddingR s.1.1, s.2 (.inl md.1) = some md.2)
    (fun t s hs w hw ↦ Common.roOK2_step keccakPaddingR t s hs hw) X
    (s := ((Common.SimState.init RState.zero, []), c₀)) (by
      simp only [Common.simPaths, Common.SimState.init, List.filterMap_cons, List.filterMap_nil]
      rcases h : keccakPaddingR.unpad [] with _ | a
      · simp
      · exact absurd ((keccakPaddingR.unpad_eq_some_iff _ _).mp h) (keccakPaddingR.pad_ne_nil a))
    z hz
  have h1 := Common.run_simulateQ_foldRO (Common.advImplLog2 (Msg := List UInt8) keccakPaddingR)
    X (Common.SimState.init RState.zero, []) c₀
  have hz' : ((z.1, z.2.1), z.2.2) ∈ support ((simulateQ HFSR.romImpl
      ((simulateQ (Common.advImplLog2 (Msg := List UInt8) keccakPaddingR) X).run
        (Common.SimState.init RState.zero, []))).run c₀) := by
    rw [h1, support_map]
    exact ⟨z, hz, rfl⟩
  have hrep := Common.simulator2_state_eq_replay keccakPaddingR RState.zero X
    (Common.fst_mem_support_of_mem_support_ro2 hz')
  intro md hmd
  rw [Common.pathsOf, ← hrep] at hmd
  exact hRO md hmd

/-- **The adversary's cache** after the adversary with the simulator, from a cache `c₀`: it extends `c₀`, holds every
sponge path of the adversary's transcript, and holds no other new `H` answer. -/
theorem adv_cacheSR {Pf σ : Type} (A : σ → OracleComp Common.RandomPermutationOracles Pf) (x : σ × Transcript)
    (c₀ : HFSR.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HFSR.romImpl (Common.advS2 keccakPaddingR RState.zero (advBSR A x))).run c₀)) :
    c₀ ≤ z.2 ∧ (∀ md ∈ transcriptPathsR z.1.2, z.2 (.inl md.1) = some md.2) ∧
      (∀ m d, z.2 (.inl m) = some d → c₀ (.inl m) = some d ∨ (m, d) ∈ transcriptPathsR z.1.2) := by
  refine ⟨Common.le_of_mem_support_run _ c₀ hz, ?_⟩
  rw [advS2_advBSR, simulateQ_map, StateT.run_map, Common.run_simulateQ_foldRO, Functor.map_map,
    support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have eT : (w.2.1.2.map entryOfR).map entryR = w.2.1.2 := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id w.2.1.2]
    exact List.map_congr_left fun e _ ↦ entryR_ofR e
  have hpaths : transcriptPathsR (w.2.1.2.map entryOfR) = Common.pathsOf keccakPaddingR RState.zero w.2.1.2 := by
    rw [transcriptPathsR, eT]
  have hrep : w.2.1.1 = Common.replay RState.zero w.2.1.2 := by
    have h1 := Common.run_simulateQ_foldRO
      (Common.advImplLog2 (Msg := List UInt8) keccakPaddingR) (simulateQ relPCR (A x.1))
      (Common.SimState.init RState.zero, []) c₀
    have hz' : ((w.1, w.2.1), w.2.2) ∈ support ((simulateQ HFSR.romImpl
        ((simulateQ (Common.advImplLog2 (Msg := List UInt8) keccakPaddingR)
          (simulateQ relPCR (A x.1))).run (Common.SimState.init RState.zero, []))).run c₀) := by
      rw [h1, support_map]
      exact ⟨w, hw, rfl⟩
    exact Common.simulator2_state_eq_replay _ _ _ (Common.fst_mem_support_of_mem_support_ro2 hz')
  have hrel := cacheRel_runR c₀ (A x.1) ((Common.SimState.init RState.zero, []), c₀)
    (fun m d hd => Or.inl hd) w hw
  refine ⟨?_, fun m d hd => ?_⟩
  · simp only [hpaths]
    exact pathsOf_ideal2CR _ c₀ hw
  · simp only [hpaths]
    rcases hrel m d hd with h | h
    · exact Or.inl h
    · rw [hrep] at h
      exact Or.inr h

/-! ## The random-oracle adversary's calls -/

/-- Oracle calls of the adversary on `RState`: a hash or permutation query one, a coin nothing. -/
def wRR : RSpecR.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- Oracle calls on the random oracles on `RState`: a hash or permutation call one, a coin nothing. -/
def wHFR : HFSpecR.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- Oracle calls of the rate model, coins free. -/
def hashCallsR : CSpecR.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem isWeightBound_liftM_probComp_hfR {β : Type} (p : ProbComp β) :
    Common.QueryCostAtMost (liftM p : OracleComp HFSpecR β) wHFR 0 :=
  Common.isWeightBound_liftM_probComp wHFR (fun _ ↦ rfl) p

set_option maxRecDepth 8000 in
/-- Each step of the adversary with the simulator makes at most one call of the random oracles, none for a coin. -/
theorem isWeightBound_advImpl2R (t : RSpecR.Domain) (s : RSim) :
    Common.QueryCostAtMost ((Common.advImpl2 keccakPaddingR t).run s) wHFR (wRR t) := by
  rcases t with n | m | q
  · simp only [Common.advImpl2, StateT.run_monadLift, monadLift_self]
    exact (isWeightBound_liftM_probComp_hfR _).bind fun _ ↦ Common.isWeightBound_pure _ _ 0
  · simp only [Common.advImpl2, StateT.run_monadLift, monadLift_self]
    exact (Common.isWeightBound_query wHFR (.inr (.inl m))).bind fun _ ↦
      Common.isWeightBound_pure _ _ 0
  · cases q with
    | forward x =>
      simp only [Common.advImpl2, Common.simulator2, StateT.run_mk]
      split
      · trivial
      · split
        · refine (Common.QueryCostAtMost.bind (b := 0) ?_ fun _ ↦ Common.isWeightBound_pure _ _ 0)
          unfold Common.rootedAnswer2
          split
          · exact ((Common.isWeightBound_query wHFR (.inr (.inl _))).bind fun _ ↦
              (isWeightBound_liftM_probComp_hfR _).bind fun _ ↦ Common.isWeightBound_pure _ _ 0)
          · exact Common.isWeightBound_query wHFR (.inr (.inr _))
        · exact (Common.isWeightBound_query wHFR (.inr (.inr _))).bind fun _ ↦
            Common.isWeightBound_pure _ _ 0
    | inverse y =>
      simp only [Common.advImpl2, Common.simulator2, StateT.run_mk]
      split
      · trivial
      · exact ((isWeightBound_liftM_probComp_hfR _).bind fun _ ↦
          Common.isWeightBound_pure _ _ 0).mono (Nat.zero_le _)

theorem isWeightBound_simulateQ_ofRHFR {β : Type} {Y : OracleComp HFSpecR β} {Q : ℕ}
    (h : Common.QueryCostAtMost Y wHFR Q) : Common.QueryCostAtMost (simulateQ ofRHFR Y) hashCallsR Q := by
  induction Y using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    have hstep : Common.QueryCostAtMost (ofRHFR t) hashCallsR (wHFR t) := by
      rcases t with n | m | x
      · exact Common.isWeightBound_query hashCallsR (.inl n)
      · exact Common.isWeightBound_map _ (Common.isWeightBound_query hashCallsR (.inr (.inl m)))
      · exact Common.isWeightBound_map _
          (Common.isWeightBound_query hashCallsR (.inr (.inr (rEquiv.symm x))))
    exact (hstep.bind fun u ↦ ih u (h.2 u)).mono (by omega)

theorem cost_advB_wRSR {Pf σ : Type} (A : σ → OracleComp Common.RandomPermutationOracles Pf) (Q : ℕ)
    (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q)
    (x : σ × Transcript) : Common.QueryCostAtMost (advBSR A x) wRR Q := by
  refine Common.isWeightBound_run_simulateQ logRelCR Common.permutationCallCost wRR
    (fun t T => ?_) (hA x.1) []
  rcases t with n | q
  · exact Common.isWeightBound_map _ (Common.isWeightBound_query wRR (.inl n))
  · simp only [logRelCR, logRelR, StateT.run_mk, relPR]
    exact Common.isWeightBound_map _ (Common.isWeightBound_map _
      (Common.isWeightBound_query wRR (.inr (.inr (LeanVM.Rpm.mapQ rEquiv q)))))

end UniKeccakSound.Rec4
