-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Adapted from this repository's
-- `formal/Compose/Compose/ListChainKRpmS.lean` (`rom_leS`, `consistent_romPrefixS`, `le_kcGameS`, `rpm_le_kcS`),
-- `formal/Compose/Compose/Rpm.lean` (`consB_run`, `ofRHF_hInF_toRH`, `cacheImpl`, `rerun_cacheImpl`,
-- `exists_det_setup`) and `formal/Compose/Compose/Coupling.lean` (`consistent_step`, `consistent_run_loggedKC`,
-- `map_run_loggedKC`), themselves adapted from leanerVM `mumbai` (https://github.com/Verified-zkEVM/leanerVM, commit
-- 6175f1a0, MIT OR Apache-2.0: `Rpm/Coins.lean`'s `exists_det`, `stepCache`), with the verifier in the rate model and
-- the transfer `UniKeccakSound.Rec4.keccak256RateTransfer` (the whole rate as `H`'s answer) in place of
-- `Common.keccak256_transfer2`.
import UniKeccakSound.Rec4.RpmRateRom

/-!
# From the random-permutation model to the rate model: `rpm_le_kcSR`

`Compose.rpm_le_kcS` moves a game (a setup of Keccak-256 calls, an adversary with coins, `π`, `π⁻¹`, a verifier in
the duplex discipline) from leanerVM's random-permutation model to the two-oracle model, Keccak-256 answering its
32-byte digest. π1-rec4's wide draws read the sponge's whole rate after Keccak-256's last permutation, which that model
does not give. Here the verifier is of the **rate model** (`Compose.KeccakCallsR`: Keccak-256 answering the digest and
the tail, `rateOfState` of its last state over `π`), and **`rpm_le_kcSR`** moves the game to the rate model's random
oracles, at the same cost `(QSπ + Q + QVπ)² / 2^508`. The proof is `rpm_le_kcS`'s:

1. the game is the real world of a transfer game on `RState` (`rpmThreadedSR_evalDistEq`);
2. the rate transfer (`keccak256RateTransfer`) moves it to the two-oracle world, `H` answering 136 uniform bytes;
3. there the adversary's cache holds the setup's answers and exactly the sponge paths of its transcript, whose digests
   are the Keccak-256 evaluations the event reads (`consistent_romPrefixSR`, `rom_leSR`);
4. coins do not help, the deterministic adversary recomputing the public setup (`exists_det_setupR`);
5. that adversary's game is `kcGameSR` (`le_kcGameSR`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace UniKeccakSound.Rec4

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Common (KCap)
open Compose (TailP KeccakCallsR liftR loggedKCR logImplKCR inlEntryR Transcript loggedKC logImplKC evalTr
  RpmOutTG lookTr)
open LeanVM.Rpm (HOnly DuplexVm AdmissibleVm StRel)

variable {Pf β σ : Type}

/-! ## Transcripts and rate-model caches -/

/-- **The cache's Keccak-256 digests are the transcript's.** -/
def ConsistentR (tr : Transcript) (c : KeccakCallsR.QueryCache) : Prop :=
  ∀ x, (c (.inl x)).map Prod.fst = lookTr tr x

theorem consistentR_nil : ConsistentR [] ∅ := fun _ => rfl

/-- One query keeps the cache's digests the transcript's. -/
theorem consistent_stepR {tr : Transcript} {c : KeccakCallsR.QueryCache} (hc : ConsistentR tr c)
    (t : List UInt8 ⊕ KeccakState) (u : KeccakCallsR t) {c' : KeccakCallsR.QueryCache}
    (hc' : (c t = some u ∧ c' = c) ∨ (c t = none ∧ c' = c.cacheQuery t u)) :
    ConsistentR (tr ++ (inlEntryR ⟨t, u⟩).toList) c' := by
  intro y
  cases t with
  | inr s =>
    show (c' (.inl y)).map Prod.fst = lookTr (tr ++ []) y
    rw [List.append_nil, ← hc y]
    rcases hc' with ⟨-, he⟩ | ⟨-, he⟩
    · rw [he]
    · rw [he, QueryCache.cacheQuery_of_ne _ _ (by simp)]
  | inl x =>
    show (c' (.inl y)).map Prod.fst = lookTr (tr ++ [(x, Compose.toB u.1)]) y
    rw [Compose.lookTr_append, ← hc y]
    rcases hc' with ⟨hx, he⟩ | ⟨hx, he⟩
    · rw [he]
      cases hy : c (.inl y) with
      | some d => rfl
      | none =>
        have hne : x ≠ y := fun e => by rw [e, hy] at hx; cases hx
        simp [hne]
    · rw [he]
      by_cases hxy : x = y
      · subst hxy
        rw [hx, QueryCache.cacheQuery_self]
        simp [LeanVM.Rpm.digestOfRpm_toRpm]
      · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using Ne.symm hxy)]
        cases c (.inl y) <;> simp [hxy]

/-- **On every outcome of the logged run, the cache's digests are the transcript's.** -/
theorem consistent_run_loggedKCR {α : Type} (v : OracleComp KeccakCallsR α) :
    ∀ (tr : Transcript) (c : KeccakCallsR.QueryCache), ConsistentR tr c →
      ∀ z ∈ support ((simulateQ randomOracle ((simulateQ logImplKCR v).run tr)).run c),
        ConsistentR z.1.2 z.2 := by
  induction v using OracleComp.inductionOn with
  | pure a =>
    intro tr c hc z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hc
  | query_bind t k ih =>
    intro tr c hc z hz
    rw [Compose.loggedKCR_run_query_bind, LeanVM.Protocol.Rom.run_simulateQ_bind,
      simulateQ_spec_query, randomOracle.run_eq] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    cases hct : c t with
    | some u =>
      rw [hct] at hp
      simp only [support_pure, Set.mem_singleton_iff] at hp
      subst hp
      exact ih u _ _ (consistent_stepR hc t u (Or.inl ⟨hct, rfl⟩)) z hz
    | none =>
      rw [hct] at hp
      rw [mem_support_bind_iff] at hp
      obtain ⟨u, -, hu⟩ := hp
      simp only [support_pure, Set.mem_singleton_iff] at hu
      subst hu
      exact ih u _ _ (consistent_stepR hc t u (Or.inr ⟨hct, rfl⟩)) z hz

/-- **Logging changes nothing of the run**: the result and the cache are the unlogged run's. -/
theorem map_run_loggedKCR {α : Type} (v : OracleComp KeccakCallsR α) :
    ∀ (tr : Transcript) (c : KeccakCallsR.QueryCache),
      (fun z => (z.1.1, z.2)) <$> (simulateQ randomOracle ((simulateQ logImplKCR v).run tr)).run c =
        (simulateQ randomOracle v).run c := by
  induction v using OracleComp.inductionOn with
  | pure a =>
    intro tr c
    simp
  | query_bind t k ih =>
    intro tr c
    rw [Compose.loggedKCR_run_query_bind, LeanVM.Protocol.Rom.run_simulateQ_bind,
      LeanVM.Protocol.Rom.run_simulateQ_bind, map_bind]
    refine bind_congr fun p => ?_
    exact ih p.1 _ p.2

/-! ## The setup's log records the cache it fills -/

/-- The rate model's calls as queries of its random oracles with coins. -/
def liftC : QueryImpl KeccakCallsR (OracleComp CSpecR) := fun t => liftM (CSpecR.query (.inr t))

theorem run_liftC {α : Type} (X : OracleComp KeccakCallsR α) (c : KeccakCallsR.QueryCache) :
    (simulateQ KeccakCallsR.romImpl (simulateQ liftC X)).run c = (simulateQ randomOracle X).run c := by
  rw [← QueryImpl.simulateQ_compose]
  congr 2
  funext t
  simp [liftC, QueryImpl.apply_compose]

/-- The setup on `RState`, read back in the rate model, is the setup lifted to the rate model. -/
theorem ofRHFR_hInF_toRHR {α : Type} (X : OracleComp KeccakCalls α) (hX : HOnly X) :
    simulateQ ofRHFR (simulateQ (Common.hInF (E := Rate0) (C := KCap)) (simulateQ toRHR X)) =
      simulateQ liftC (simulateQ liftR X) := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [LeanVM.Rpm.hOnly_query_bind] at hX
    rcases t with m | s
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, toRHR, liftR, bind_map_left]
      simp only [Common.hInF, simulateQ_spec_query, ofRHFR, liftC, bind_map_left, Equiv.apply_symm_apply]
      exact bind_congr fun u => ih _ (hX _)
    · exact hX.elim

/-- **The setup's log records the cache it fills**, on `RState`. -/
theorem consB_runR {α : Type} (v : OracleComp KeccakCalls α) (hv : HOnly v) :
    ∀ (tr : Transcript) (c : HFSR.QueryCache), ConsistentR tr (cmapR c) →
      ∀ z ∈ support ((simulateQ HFSR.romImpl (simulateQ (Common.hInF (E := Rate0) (C := KCap))
          (simulateQ toRHR ((simulateQ logImplKC v).run tr)))).run c),
        ConsistentR z.1.2 (cmapR z.2) := by
  induction v using OracleComp.inductionOn with
  | pure a =>
    intro tr c hc z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hc
  | query_bind t k ih =>
    rw [LeanVM.Rpm.hOnly_query_bind] at hv
    rcases t with x | s
    · intro tr c hc z hz
      rw [Compose.loggedKC_run_query_bind] at hz
      simp only [simulateQ_bind, simulateQ_spec_query, toRHR, bind_map_left,
        Common.hInF, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨d, c'⟩, hd, hz⟩ := hz
      have hstep : ConsistentR (tr ++ (inlEntryR ⟨.inl x, rbij d⟩).toList) (cmapR c') := by
        refine consistent_stepR hc (.inl x) (rbij d) ?_
        rw [OracleSpec.romImpl_apply_inr, randomOracle.run_eq] at hd
        rcases hcx : c.toFn (.inl x) with _ | u
        · rw [hcx] at hd
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hd
          obtain ⟨u, -, rfl, rfl⟩ := hd
          refine Or.inr ⟨?_, cmapR_cacheQuery_inl c x _⟩
          show (c (.inl x)).map rbij = none
          rw [show c (.inl x) = c.toFn (.inl x) from rfl, hcx]
          rfl
        · rw [hcx] at hd
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hd
          obtain ⟨h1, h2⟩ := hd
          refine Or.inl ⟨?_, by rw [h2]⟩
          show (c (.inl x)).map rbij = some (rbij d)
          rw [show c (.inl x) = c.toFn (.inl x) from rfl, hcx, h1]
          rfl
      exact ih ((rbij d).1) (hv _) _ c' hstep z hz
    · exact hv.elim

/-! ## The random-oracle side -/

/-- **The adversary with the simulator, in the rate model, with its transcript.** -/
noncomputable def romAdvTSR (A : σ → OracleComp Common.RandomPermutationOracles Pf) (x : σ × Transcript) :
    OracleComp CSpecR (Pf × PermutationTranscript) :=
  simulateQ ofRHFR (Common.advS2 keccakPaddingR RState.zero (advBSR A x))

/-- **The random-oracle adversary of the rate transfer**: the adversary with the indifferentiability simulator
(`Common.advS2` on `RState`), with coins, its queries read in the rate model. -/
noncomputable def romAdvCSR (A : σ → OracleComp Common.RandomPermutationOracles Pf) (ir : σ) : OracleComp CSpecR Pf :=
  Prod.fst <$> romAdvTSR A (ir, [])

/-- The verifier from the cache after the adversary, that cache kept. -/
noncomputable def gLSR (fix : σ → Pf → Pf) (V : Pf → OracleComp KeccakCallsR β)
    (p : (σ × Pf) × KeccakCallsR.QueryCache) : ProbComp ((Pf × β) × KeccakCallsR.QueryCache) :=
  (fun v => ((fix p.1.1 p.1.2, v), p.2)) <$> (simulateQ randomOracle (V (fix p.1.1 p.1.2))).run' p.2

/-- **The event on the cache after the adversary**: the event for every transcript recording that cache's
Keccak-256 digests. -/
def BreaksCGR (E : (Pf × β) → Transcript → Prop) (z : (Pf × β) × KeccakCallsR.QueryCache) : Prop :=
  ∀ tr, ConsistentR tr z.2 → E z.1 tr

/-- The prefix of the transfer's random-oracle game: the setup, then the adversary with the simulator. -/
noncomputable def romPrefixSR (setup : OracleComp KeccakCalls σ)
    (A : σ → OracleComp Common.RandomPermutationOracles Pf) :
    OracleComp HFSpecR ((σ × Transcript) × (Pf × PermutationTranscript)) :=
  simulateQ (Common.hInF (E := Rate0) (C := KCap)) (preBSR setup) >>= fun x =>
    (x, ·) <$> Common.advS2 keccakPaddingR RState.zero (advBSR A x)

/-- **After the setup and the adversary, the cache's Keccak-256 digests are those the setup's log and the
Keccak-256 evaluations of the adversary's transcript record.** -/
theorem consistent_romPrefixSR (setup : OracleComp KeccakCalls σ) (hS : HOnly setup)
    (A : σ → OracleComp Common.RandomPermutationOracles Pf)
    {p : ((σ × Transcript) × (Pf × PermutationTranscript)) × HFSR.QueryCache}
    (hp : p ∈ support ((simulateQ HFSR.romImpl (romPrefixSR setup A)).run ∅)) :
    ConsistentR (p.1.1.2 ++ evalTr p.1.2.2) (cmapR p.2) := by
  rw [romPrefixSR, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨⟨x, c₁⟩, h1, hp⟩ := hp
  rw [simulateQ_map, StateT.run_map, support_map] at hp
  obtain ⟨⟨a, c₂⟩, h2, rfl⟩ := hp
  have hc1 : ConsistentR x.2 (cmapR c₁) := consB_runR setup hS [] ∅
    (by rw [cmapR_empty]; exact consistentR_nil) (x, c₁) h1
  obtain ⟨hle, hpaths, hrel⟩ := adv_cacheSR A x c₁ h2
  intro m
  show ((cmapR c₂) (.inl m)).map Prod.fst = lookTr (x.2 ++ evalTr a.2) m
  rw [Compose.lookTr_append', lookTr_evalTr, ← hc1 m, cmapR_inl, cmapR_inl]
  rcases h : c₁ (.inl m) with _ | d
  · simp only [Option.map_none]
    unfold hashesOfR
    rcases hf : (transcriptPathsR a.2).find? (·.1 = m) with _ | e
    · rw [hf]
      rcases h2' : c₂ (.inl m) with _ | d'
      · rfl
      · exfalso
        rcases hrel m d' h2' with h3 | h3
        · rw [h] at h3
          cases h3
        · rw [List.find?_eq_none] at hf
          exact hf _ h3 (by simp)
    · have he := List.find?_some hf
      have hmem := List.mem_of_find?_eq_some hf
      simp only [decide_eq_true_eq] at he
      rw [hf, ← he, hpaths e hmem]
      rfl
  · simp only [Option.map_some]
    rw [hle h]
    rfl

theorem romRun2_splitSR (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A : σ → OracleComp Common.RandomPermutationOracles Pf) (V : Pf → OracleComp KeccakCallsR β) :
    Common.romRun2 (simulateQ (Common.hInF (E := Rate0) (C := KCap)) (preBSR setup) >>=
      fun x => Common.advS2 keccakPaddingR RState.zero (advBSR A x) >>= fun a => postBSR fix V x a) =
      (simulateQ HFSR.romImpl (romPrefixSR setup A)).run ∅ >>= fun p =>
        (simulateQ HFSR.romImpl (postBSR fix V p.1.1 p.1.2)).run' p.2 := by
  simp only [Common.romRun2, romPrefixSR, simulateQ_bind, simulateQ_map, StateT.run'_eq,
    StateT.run_bind, StateT.run_map, map_bind, bind_map_left, bind_assoc]

/-- **The rate transfer's random-oracle game, in the rate model, with the event on the cache**: the verifier from
the cache after the adversary with the simulator (with coins), the event read on any transcript of that cache's
digests. -/
theorem rom_leSR (setup : OracleComp KeccakCalls σ) (hS : HOnly setup)
    (fix : σ → Pf → Pf) (A : σ → OracleComp Common.RandomPermutationOracles Pf)
    (V : Pf → OracleComp KeccakCallsR β) (E : (Pf × β) → Transcript → Prop)
    (hE : ∀ z tr tr', (∀ x, lookTr tr x = lookTr tr' x) → E z tr → E z tr') :
    Pr{let z ← Common.romRun2 (simulateQ (Common.hInF (E := Rate0) (C := KCap))
        (preBSR setup) >>= fun x => Common.advS2 keccakPaddingR RState.zero
          (advBSR A x) >>= fun a => postBSR fix V x a)}[E z.1 (z.2.1 ++ evalTr z.2.2)] ≤
      Pr{let y ← (simulateQ KeccakCallsR.romImpl (simulateQ liftC (simulateQ liftR setup) >>= fun ir =>
          (ir, ·) <$> romAdvCSR A ir)).run ∅ >>= gLSR fix V}[BreaksCGR E y] := by
  rw [romRun2_splitSR]
  have hpost : ∀ p : ((σ × Transcript) × (Pf × PermutationTranscript)) × HFSR.QueryCache,
      Pr{let z ← (simulateQ HFSR.romImpl (postBSR fix V p.1.1 p.1.2)).run' p.2}[
          E z.1 (z.2.1 ++ evalTr z.2.2)] =
        Pr{let v ← (simulateQ randomOracle (V (fix p.1.1.1 p.1.2.1))).run' (cmapR p.2)}[
          E (fix p.1.1.1 p.1.2.1, v) (p.1.1.2 ++ evalTr p.1.2.2)] := by
    intro p
    rw [postBSR, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, prEvent_map]
    have h := (run'_toRHFR (V (fix p.1.1.1 p.1.2.1)) p.2).prEvent_eq
      (fun v => E (fix p.1.1.1 p.1.2.1, v) (p.1.1.2 ++ evalTr p.1.2.2))
    rw [StateT.run'_eq, prEvent_map] at h
    exact h
  have h := run_ofRHFR (romPrefixSR setup A) ∅
  rw [cmapR_empty] at h
  have hX : (fun r => (r.1.1, r.2.1)) <$> simulateQ ofRHFR (romPrefixSR setup A) =
      simulateQ liftC (simulateQ liftR setup) >>= fun ir => (ir, ·) <$> romAdvCSR A ir := by
    rw [romPrefixSR, simulateQ_bind, preBSR,
      ofRHFR_hInF_toRHR (loggedKC setup) (Compose.hOnly_loggedKC_run setup hS [])]
    conv_rhs => rw [← Compose.fst_loggedKC_run setup [], simulateQ_map, simulateQ_map, bind_map_left]
    simp only [simulateQ_map, map_bind, Functor.map_map]
    refine bind_congr fun x => ?_
    simp only [romAdvCSR, romAdvTSR, Functor.map_map]
    rfl
  have hJ : (fun p : ((σ × Transcript) × (Pf × PermutationTranscript)) × HFSR.QueryCache =>
      ((p.1.1.1, p.1.2.1), cmapR p.2)) <$> (simulateQ HFSR.romImpl (romPrefixSR setup A)).run ∅ =ᵈ
      (simulateQ KeccakCallsR.romImpl (simulateQ liftC (simulateQ liftR setup) >>= fun ir =>
        (ir, ·) <$> romAdvCSR A ir)).run ∅ := by
    rw [← hX, simulateQ_map, StateT.run_map]
    refine EvalDistEq.trans ?_ (h.symm.map _)
    rw [Functor.map_map]
    exact EvalDistEq.rfl
  calc _ ≤ Pr{let y ← (simulateQ HFSR.romImpl (romPrefixSR setup A)).run ∅ >>= fun p =>
              gLSR fix V ((p.1.1.1, p.1.2.1), cmapR p.2)}[BreaksCGR E y] := by
        refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp => ?_
        rw [hpost, gLSR, prEvent_map]
        refine prEvent_mono _ _ _ fun v hv tr htr => ?_
        have hcons := consistent_romPrefixSR setup hS A hp
        exact hE _ _ _ (fun x => (hcons x).symm.trans (htr x)) hv
    _ = _ := by
        rw [← bind_map_left]
        exact (EvalDistEq.bind_left hJ _).prEvent_eq _

/-! ## Coins do not help: the deterministic adversary recomputes the public setup -/

/-- The cache after a random-oracle step of the rate model answering `u` at `t` from `c`. -/
def stepCacheR (c : KeccakCallsR.QueryCache) (t : KeccakCallsR.Domain) (u : KeccakCallsR.Range t) :
    KeccakCallsR.QueryCache :=
  match c t with
  | some _ => c
  | none => c.cacheQuery t u

theorem snd_eq_stepCacheR {c : KeccakCallsR.QueryCache} {t : KeccakCallsR.Domain}
    {z : KeccakCallsR.Range t × KeccakCallsR.QueryCache}
    (hz : z ∈ support ((KeccakCallsR.randomOracle t).run c)) : z.2 = stepCacheR c t z.1 := by
  rw [randomOracle.run_eq] at hz
  unfold stepCacheR
  cases h : c t with
  | some u =>
    simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz; rfl
  | none =>
    simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    rfl

theorem romImpl_inl_runR (n : ℕ) (c : KeccakCallsR.QueryCache) :
    (KeccakCallsR.romImpl (.inl n)).run c = (fun x => (x, c)) <$> (unifSpec.query n : ProbComp _) := by
  simp [unifFwdImpl]

/-- **Derandomization against the rate model's random oracles** (`LeanVM.Rpm.exists_det`). -/
theorem exists_detR {α γ : Type} (g : α × KeccakCallsR.QueryCache → ProbComp γ) (E : γ → Prop)
    (X : OracleComp CSpecR α) :
    ∀ (Q : ℕ), Common.QueryCostAtMost X hashCallsR Q → ∀ c : KeccakCallsR.QueryCache,
      ∃ A : OracleComp KeccakCallsR α, IsTotalQueryBound A Q ∧
        Pr{let y ← (simulateQ KeccakCallsR.romImpl X).run c >>= g}[E y] ≤
          Pr{let y ← (simulateQ KeccakCallsR.randomOracle A).run c >>= g}[E y] :=
  LeanVM.Rpm.exists_det_of KeccakCallsR.romImpl stepCacheR
    (fun n c z hz ↦ by
      rw [romImpl_inl_runR, support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      rfl)
    (fun _ _ _ hz ↦ snd_eq_stepCacheR hz) hashCallsR (fun _ ↦ rfl) (fun _ ↦ rfl) g E X

/-- The setup's queries, with the cache the random oracle holds after them. -/
def cacheImplR : QueryImpl KeccakCallsR (StateT KeccakCallsR.QueryCache (OracleComp KeccakCallsR)) :=
  fun t => StateT.mk fun c =>
    (fun u => (u, stepCacheR c t u)) <$> (liftM (KeccakCallsR.query t) : OracleComp _ _)

theorem le_of_mem_support_runROR {α : Type} (X : OracleComp KeccakCallsR α)
    (c : KeccakCallsR.QueryCache) {z : α × KeccakCallsR.QueryCache}
    (hz : z ∈ support ((simulateQ randomOracle X).run c)) : c ≤ z.2 := by
  rw [← run_liftC] at hz
  exact Common.le_of_mem_support_run _ c hz

theorem randomOracle_mem_supportR {t : KeccakCallsR.Domain} {c : KeccakCallsR.QueryCache}
    {z : KeccakCallsR.Range t × KeccakCallsR.QueryCache}
    (hz : z ∈ support ((randomOracle t).run c)) : z.2 t = some z.1 := by
  rw [randomOracle.run_eq] at hz
  rcases hct : c.toFn t with _ | u
  · rw [hct] at hz
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact QueryCache.cacheQuery_self _ _ _
  · rw [hct] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hct

/-- **Recomputing the setup** from any cache extending one it left: the same output, the cache it left, and no
change to the random oracle's cache. -/
theorem rerun_cacheImplR {α : Type} (S : OracleComp KeccakCallsR α) :
    ∀ (c : KeccakCallsR.QueryCache) {z : α × KeccakCallsR.QueryCache},
      z ∈ support ((simulateQ randomOracle S).run c) → ∀ c', z.2 ≤ c' →
        (simulateQ randomOracle ((simulateQ cacheImplR S).run c)).run c' = pure (z, c') := by
  induction S using OracleComp.inductionOn with
  | pure a =>
    intro c z hz c' _
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz ⊢
    subst hz
    rfl
  | query_bind t k ih =>
    intro c z hz c' hc'
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hw2 := snd_eq_stepCacheR hw
    have hwt := randomOracle_mem_supportR hw
    have hle := le_of_mem_support_runROR (k w.1) w.2 hz
    have hct' : c'.toFn t = some w.1 := hc' (hle hwt)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, cacheImplR, StateT.run_mk,
      bind_map_left, randomOracle.run_eq, hct', pure_bind]
    rw [← hw2]
    exact ih w.1 w.2 hz c' hc'

theorem isTotalQueryBound_cacheRunR {α : Type} (S : OracleComp KeccakCallsR α) :
    ∀ (n : ℕ) (c : KeccakCallsR.QueryCache), IsTotalQueryBound S n →
      IsTotalQueryBound ((simulateQ cacheImplR S).run c) n := by
  induction S using OracleComp.inductionOn with
  | pure a => intro n c _; simp only [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind t k ih =>
    intro n c hn
    obtain ⟨hn1, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, cacheImplR, StateT.run_mk,
      bind_map_left]
    exact isTotalQueryBound_query_bind_iff.mpr ⟨hn1, fun u => ih u (n - 1) _ (hk u)⟩

/-- **Derandomization after a public setup**, in the rate model (`Compose.exists_det_setup`): an adversary with
coins, run after the setup, does no better than a deterministic one, which recomputes the setup to learn that cache
(`QS` more queries). -/
theorem exists_det_setupR {σ₀ α γ : Type} (S : OracleComp KeccakCallsR σ₀) (QS : ℕ)
    (hS : IsTotalQueryBound S QS) (Y : σ₀ → OracleComp CSpecR α) (Q : ℕ)
    (hY : ∀ x, Common.QueryCostAtMost (Y x) hashCallsR Q)
    (g : (σ₀ × α) × KeccakCallsR.QueryCache → ProbComp γ) (E : γ → Prop) :
    ∃ A' : σ₀ → OracleComp KeccakCallsR α, (∀ x, IsTotalQueryBound (A' x) (QS + Q)) ∧
      Pr{let y ← (simulateQ KeccakCallsR.romImpl (simulateQ liftC S >>= fun x =>
          (x, ·) <$> Y x)).run ∅ >>= g}[E y] ≤
        Pr{let y ← (simulateQ randomOracle (S >>= fun x => (x, ·) <$> A' x)).run ∅ >>= g}[E y] := by
  choose A₀ hA₀ hle using fun (x : σ₀) (c : KeccakCallsR.QueryCache) =>
    exists_detR (fun p => g ((x, p.1), p.2)) E (Y x) Q (hY x) c
  refine ⟨fun x => (simulateQ cacheImplR S).run ∅ >>= fun r => A₀ x r.2,
    fun x => isTotalQueryBound_bind (isTotalQueryBound_cacheRunR S QS ∅ hS) fun r => hA₀ x r.2, ?_⟩
  rw [simulateQ_bind, StateT.run_bind, run_liftC, simulateQ_bind, StateT.run_bind, bind_assoc,
    bind_assoc]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp => ?_
  simp only [simulateQ_map, StateT.run_map, bind_map_left]
  rw [simulateQ_bind, StateT.run_bind, rerun_cacheImplR S ∅ hp p.2 le_rfl, pure_bind]
  exact hle p.1 p.2

theorem isTotalQueryBound_liftR {α : Type} (X : OracleComp KeccakCalls α) :
    ∀ n, IsTotalQueryBound X n → IsTotalQueryBound (simulateQ liftR X) n := by
  induction X using OracleComp.inductionOn with
  | pure a => intro n _; simp only [simulateQ_pure]; trivial
  | query_bind t k ih =>
    intro n hn
    obtain ⟨hn1, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    rcases t with x | s
    · simp only [simulateQ_bind, simulateQ_spec_query, liftR, bind_map_left]
      exact isTotalQueryBound_query_bind_iff.mpr ⟨hn1, fun u => ih u.1 (n - 1) (hk _)⟩
    · simp only [simulateQ_bind, simulateQ_spec_query, liftR]
      exact isTotalQueryBound_query_bind_iff.mpr ⟨hn1, fun u => ih u (n - 1) (hk u)⟩

/-- **The random-oracle adversary makes at most one oracle query per call of `π` or `π⁻¹` of the adversary**,
coins free. -/
theorem cost_romAdvCSR (A : σ → OracleComp Common.RandomPermutationOracles Pf) (Q : ℕ)
    (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q) (ir : σ) :
    Common.QueryCostAtMost (romAdvCSR A ir) hashCallsR Q := by
  refine Common.isWeightBound_map _ (isWeightBound_simulateQ_ofRHFR ?_)
  rw [Common.advS2, StateT.run'_eq]
  exact Common.isWeightBound_map _ (Common.isWeightBound_run_simulateQ _ wRR wHFR
    isWeightBound_advImpl2R (cost_advB_wRSR A Q hA (ir, [])) _)

/-! ## The deterministic adversary's game is `kcGameSR` -/

/-- **The deterministic adversary's game, the event on its cache, is bounded by `kcGameSR`'s**: the log of the setup
and the adversary records the cache's digests (`consistent_run_loggedKCR`). -/
theorem le_kcGameSR (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A' : σ → OracleComp KeccakCallsR Pf) (V : Pf → OracleComp KeccakCallsR β)
    (E : (Pf × β) → Transcript → Prop) :
    Pr{let y ← (simulateQ randomOracle (simulateQ liftR setup >>= fun ir => (ir, ·) <$> A' ir)).run ∅ >>=
        gLSR fix V}[BreaksCGR E y] ≤
      Pr{let z ← (simulateQ randomOracle (kcGameSR setup fix A' V)).run' ∅}[E z.1 z.2] := by
  set SA := simulateQ liftR setup >>= fun ir => fix ir <$> A' ir
  have hAw : (fun p : σ × Pf => fix p.1 p.2) <$>
      (simulateQ liftR setup >>= fun ir => (ir, ·) <$> A' ir) = SA := by
    simp only [SA, map_bind, Functor.map_map]
  have hL : (simulateQ randomOracle (simulateQ liftR setup >>= fun ir => (ir, ·) <$> A' ir)).run ∅ >>=
      gLSR fix V = (simulateQ randomOracle SA).run ∅ >>= fun q =>
        (fun v => ((q.1, v), q.2)) <$> (simulateQ randomOracle (V q.1)).run' q.2 := by
    rw [← hAw, simulateQ_map, StateT.run_map, bind_map_left]
    rfl
  have hR : (simulateQ randomOracle (kcGameSR setup fix A' V)).run' ∅ =
      (simulateQ randomOracle (loggedKCR SA)).run ∅ >>= fun q =>
        (fun v => ((q.1.1, v), q.1.2)) <$> (simulateQ randomOracle (V q.1.1)).run' q.2 := by
    simp only [kcGameSR, SA, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind,
      bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [hL, hR, ← map_run_loggedKCR SA [] ∅, bind_map_left]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun q hq => ?_
  have hcons := consistent_run_loggedKCR SA [] ∅ consistentR_nil q hq
  rw [prEvent_map, prEvent_map]
  exact prEvent_mono _ _ _ fun v hv => hv q.1.2 hcons

/-! ## The transfer -/

/-- **From the random-permutation model to the rate model, for any proof, rate-model verifier and event that reads
the transcript through its answers.** For a setup of Keccak-256 calls only (at most `QS` of them, `QSπ` calls of
`π`), an adversary with coins, `π` and `π⁻¹` (at most `Q` calls given any setup output) and a verifier of the rate
model (its Keccak-256 calls answered by the whole rate after the last permutation, `rateOfState`) following the duplex
discipline with at most `QVπ` calls of `π`: some deterministic adversary of the rate model's random oracles, of at
most `QS + Q` queries given any setup output (it recomputes the public setup), meets the event in the rate model's
game, on the log of the setup's and its Keccak-256 queries (their digests), at least as often as the RPM game's
adversary meets it on the setup's log and the Keccak-256 evaluations of its permutation transcript, less
`(QSπ + Q + QVπ)² / 2^508`. -/
theorem rpm_le_kcSR (setup : OracleComp KeccakCalls σ) (hSH : HOnly setup) (QS QSπ : ℕ)
    (hS : IsTotalQueryBound setup QS) (hSπ : Common.QueryCostAtMost setup LeanVM.Rpm.hashBlocks QSπ)
    (fix : σ → Pf → Pf) (A : σ → OracleComp Common.RandomPermutationOracles Pf)
    (Q : ℕ) (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q)
    (V : Pf → OracleComp KeccakCallsR β) (hVd : ∀ π, DuplexVmR (V π) []) (QVπ : ℕ)
    (hVπ : ∀ π, Common.QueryCostAtMost (V π) hashBlocksR QVπ)
    (E : (Pf × β) → Transcript → Prop)
    (hE : ∀ z tr tr', (∀ x, lookTr tr x = lookTr tr' x) → E z tr → E z tr') :
    ∃ A' : σ → OracleComp KeccakCallsR Pf, (∀ ir, IsTotalQueryBound (A' ir) (QS + Q)) ∧
      Pr{let z ← Common.runWithRandomPermutation (rpmGameSR setup fix A V)}[
          E z.1 (z.2.1 ++ evalTr (permutationQueries z.2.2))] ≤
        Pr{let z ← (simulateQ randomOracle (kcGameSR setup fix A' V)).run' ∅}[E z.1 z.2] +
          ((QSπ + Q + QVπ : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 := by
  obtain ⟨A', hA', hle⟩ := exists_det_setupR (simulateQ liftR setup) QS (isTotalQueryBound_liftR setup QS hS)
    (romAdvCSR A) Q (cost_romAdvCSR A Q hA) (gLSR fix V) (BreaksCGR E)
  refine ⟨A', hA', ?_⟩
  rw [prEvent_rpmGameSR]
  refine le_trans (le_of_eq ((rpmThreadedSR_evalDistEq setup hSH fix A V).prEvent_eq
    (fun z => E z.1 (z.2.1 ++ evalTr z.2.2)))) ?_
  obtain ⟨ht, -⟩ := keccak256RateTransfer (preBSR setup) (advBSR A) (postBSR fix V)
    (duplex_postBSR fix V hVd) (QSπ + Q + QVπ) (cost_gameBSR setup hSH QSπ hSπ fix A Q hA V QVπ hVπ)
    (fun z => E z.1 (z.2.1 ++ evalTr z.2.2))
  exact ht.trans (add_le_add ((rom_leSR setup hSH fix A V E hE).trans
    (hle.trans (le_kcGameSR setup fix A' V E))) le_rfl)

end UniKeccakSound.Rec4

/-- info: 'UniKeccakSound.Rec4.rpm_le_kcSR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.rpm_le_kcSR

/-- info: 'UniKeccakSound.Rec4.simulateQ_liftR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.simulateQ_liftR

/-- info: 'UniKeccakSound.Rec4.duplexVmR_liftR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.duplexVmR_liftR

/-- info: 'UniKeccakSound.Rec4.cost_liftR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.cost_liftR

/-- info: 'UniKeccakSound.Rec4.cost_hashR_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.cost_hashR_bind

/-- info: 'UniKeccakSound.Rec4.DuplexVmR.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.DuplexVmR.bind

/-- info: 'UniKeccakSound.Rec4.duplexVmR_hashR_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.duplexVmR_hashR_bind
