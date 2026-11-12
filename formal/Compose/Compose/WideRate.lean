-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The end theorem follows `GOps.lean`'s
-- `knowledgeSoundness_listChainU_closed128G` (its probability steps `ListChainUDoom128.lean`'s `prob_kcBadU'`,
-- `ListChainKAdv.lean`'s `prob_rootBadK`, `ListChainU128.lean`'s `prob_roundBadU'`, `ListChainU.lean`'s `prob_collU`)
-- for the wide chain in the rate model.
import Compose.WideAdv
import Compose.WideSplit

/-!
# The wide chain in the rate model: knowledge soundness

π1-rec4's verifier reads its wide draws off Keccak-256's rate, so its experiment is one of the rate model
(`KeccakCallsR`, `WideSpec.lean`): the setup (any computation of the two-oracle model, lifted: `liftR`), the
adversary of the rate model, its queries' digests logged (`loggedKCR`), the wide chain over `hashR` (`preWideR`),
then the openings (any verifiers of the two-oracle model, lifted), every Keccak-256 query's digest logged
(`expLGR`). Split at its table of tails (`instR τ`), it is `WideAdv.lean`'s experiment with the tails `τ`
(`instR_expLGR`, `instR_preWideR`, `instR_withSetupGR`).

* **The bad events** (`advBadWR`): on a rate table, `WideAdv.lean`'s at its tails (`kcBadW … (splitT T)`) and the
  adversary's roots (`rootBadR`); **`trace_whirWR`**: a run of the rate model that breaks knowledge soundness while
  no opening is doomed and no pair is in its transcript asks a bad fresh query (`trace_whirWG` at the table's tails);
* **each fresh query is bad with probability at most** `(|H| + nRf (|H| + 1) + k) / 2^256 + maxErrK`
  (**`prob_advBadWR`**): the query's answer is a uniform digest and a uniform tail; its wide draw's challenges are
  uniform (`wide_evalDistEq`), so a round is bad with probability at most its error times its factor, as for the
  narrow chain;
* **the openings' doom and the seed's pair** are events the two-oracle model bounds for every computation; the rate
  model's are bounded tail table by tail table (`prEvent_rate_le`, `WideSplit.lean`).

**`knowledgeSoundness_listChainW_closed128R`**: the verifier accepts while no candidate of round `0`'s root read
off the setup's and the adversary's queries satisfies the first round's state with probability at most

`bnd (QS + Q + nQ + Σ_k QO_k) + 2 (QS + Q + nQ + Σ_k QO_k)² / 2^256 + N (maxErrK + (nRf + 2) N / 2^256)`,

`N = QS + Q + nQ + Σ_k QO_k` (`nQ` the label and one query a round), for openings whose union is sound at `bnd`
(`GUnionSound`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The experiment in the rate model -/

section Exp

variable {F St M Pf : Type} [SampleableType F]
variable (W : ChainSpecW F St) (view : Pf → St × List (RMsg F))

/-- The setup (of the two-oracle model, lifted), then the adversary given its output. -/
def withSetupGR {σ : Type} (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A₀ : σ → OracleComp KeccakCallsR Pf) : OracleComp KeccakCallsR Pf :=
  simulateQ liftR setup >>= fun s => fix s <$> A₀ s

/-- **The adversary, its queries' digests logged, then the wide chain over Keccak-256's rate.** -/
def preWideR (A : OracleComp KeccakCallsR Pf) : OracleComp KeccakCallsR (PreK Pf F) :=
  loggedKCR A >>= fun pt => W.chain hashR (view pt.1).1 (view pt.1).2 >>= fun ch => pure (pt.1, ch, pt.2)

/-- **The run with its whole transcript**: `X`, then the openings (lifted), every Keccak-256 query's digest
logged. -/
def expLGR (X : OracleComp KeccakCallsR (PreK Pf F)) (ops : List (GOp Pf F M)) :
    OracleComp KeccakCallsR (OutK Pf F (List Bool) × Transcript) :=
  (simulateQ logImplKCR (X >>= fun x => opsOut x <$> simulateQ liftR (gopsRun view ops x.1 x.2.1))).run []

/-! ### Split at a table of tails -/

theorem instR_hashR (τ : List UInt8 → TailP) (x : List UInt8) :
    simulateQ (instR τ) (hashR x) = hashτ τ x := by
  simp only [hashR, callKeccak256R, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, hashτ, hash256,
    callKeccak256]
  show ((fun d => (d, τ x)) <$> (liftM (KeccakCalls.query (.inl x)) : OracleComp KeccakCalls Digest)) >>= _ = _
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

theorem instR_runMW (τ : List UInt8 → TailP) : ∀ (y : List UInt8) (es : List (List UInt8)),
    simulateQ (instR τ) (ChainSpecW.runMW hashR y es) = ChainSpecW.runMW (hashτ τ) y es
  | y, [] => by
    simp only [ChainSpecW.runMW, simulateQ_bind, instR_hashR, simulateQ_pure]
  | y, e :: es => by
    simp only [ChainSpecW.runMW, simulateQ_bind, instR_hashR, simulateQ_pure]
    refine bind_congr fun a => ?_
    rw [instR_runMW τ (stepIn a.1 e) es]

theorem instR_chain (τ : List UInt8 → TailP) (s : St) (ms : List (RMsg F)) :
    simulateQ (instR τ) (W.chain hashR s ms) = W.chain (hashτ τ) s ms := by
  simp only [ChainSpecW.chain, simulateQ_map, instR_runMW]

theorem instR_preWideR (τ : List UInt8 → TailP) (A : OracleComp KeccakCallsR Pf) :
    simulateQ (instR τ) (preWideR W view A) = preWide W view τ (simulateQ (instR τ) A) := by
  simp only [preWideR, preWide, simulateQ_bind, instR_loggedKCR, instR_chain, simulateQ_pure]

theorem instR_expLGR (τ : List UInt8 → TailP) (X : OracleComp KeccakCallsR (PreK Pf F))
    (ops : List (GOp Pf F M)) :
    simulateQ (instR τ) (expLGR view X ops) = expLG view (simulateQ (instR τ) X) ops := by
  rw [expLGR, expLG, instR_loggedKCR_run]
  simp only [simulateQ_bind, simulateQ_map, instR_liftR]

theorem instR_withSetupGR {σ : Type} (τ : List UInt8 → TailP) (setup : OracleComp KeccakCalls σ)
    (fix : σ → Pf → Pf) (A₀ : σ → OracleComp KeccakCallsR Pf) :
    simulateQ (instR τ) (withSetupGR setup fix A₀) =
      withSetupG setup fix (fun s => simulateQ (instR τ) (A₀ s)) := by
  simp only [withSetupGR, withSetupG, simulateQ_bind, simulateQ_map, instR_liftR]

/-! ### Query bounds -/

theorem isTotalQueryBound_instR (τ : List UInt8 → TailP) {α : Type} :
    ∀ (oa : OracleComp KeccakCallsR α) (n : ℕ), IsTotalQueryBound oa n →
      IsTotalQueryBound (simulateQ (instR τ) oa) n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _; trivial
  | query_bind t k ih =>
    intro n hn
    obtain ⟨hn1, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    rcases t with x | s
    · have e : simulateQ (instR τ) (liftM (KeccakCallsR.query (.inl x)) >>= k) =
          liftM (KeccakCalls.query (.inl x)) >>= fun dg => simulateQ (instR τ) (k (dg, τ x)) := by
        rw [simulateQ_bind, simulateQ_spec_query]
        show ((fun d => (d, τ x)) <$> (liftM (KeccakCalls.query (.inl x)) : OracleComp KeccakCalls Digest)) >>= _ = _
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
        rfl
      rw [e]
      exact isTotalQueryBound_query_bind_iff.mpr ⟨hn1, fun dg => ih _ _ (hk _)⟩
    · have e : simulateQ (instR τ) (liftM (KeccakCallsR.query (.inr s)) >>= k) =
          liftM (KeccakCalls.query (.inr s)) >>= fun y => simulateQ (instR τ) (k y) := by
        rw [simulateQ_bind, simulateQ_spec_query]
        rfl
      rw [e]
      exact isTotalQueryBound_query_bind_iff.mpr ⟨hn1, fun y => ih _ _ (hk _)⟩

theorem isTotalQueryBound_liftR {α : Type} :
    ∀ (oa : OracleComp KeccakCalls α) (n : ℕ), IsTotalQueryBound oa n →
      IsTotalQueryBound (simulateQ liftR oa) n := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro n _; trivial
  | query_bind t k ih =>
    intro n hn
    obtain ⟨hn1, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    rcases t with x | s
    · have e : simulateQ liftR (liftM (KeccakCalls.query (.inl x)) >>= k) =
          liftM (KeccakCallsR.query (.inl x)) >>= fun u => simulateQ liftR (k u.1) := by
        rw [simulateQ_bind, simulateQ_spec_query]
        show (Prod.fst <$> (liftM (KeccakCallsR.query (.inl x)) : OracleComp KeccakCallsR (Digest × TailP))) >>=
          _ = _
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
        rfl
      rw [e]
      exact isTotalQueryBound_query_bind_iff.mpr ⟨hn1, fun u => ih _ _ (hk _)⟩
    · have e : simulateQ liftR (liftM (KeccakCalls.query (.inr s)) >>= k) =
          liftM (KeccakCallsR.query (.inr s)) >>= fun y => simulateQ liftR (k y) := by
        rw [simulateQ_bind, simulateQ_spec_query]
        rfl
      rw [e]
      exact isTotalQueryBound_query_bind_iff.mpr ⟨hn1, fun y => ih _ _ (hk _)⟩

theorem isTotalQueryBound_loggedKCR_run {α : Type} (oa : OracleComp KeccakCallsR α) :
    ∀ (n : ℕ) (l : Transcript), IsTotalQueryBound oa n →
      IsTotalQueryBound ((simulateQ logImplKCR oa).run l) n := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n l _; simp only [simulateQ_pure, StateT.run_pure]; trivial
  | query_bind t k ih =>
    intro n l hn
    obtain ⟨hn1, hk⟩ := isTotalQueryBound_query_bind_iff.mp hn
    rw [loggedKCR_run_query_bind]
    exact isTotalQueryBound_query_bind_iff.mpr ⟨hn1, fun u => ih u (n - 1) _ (hk u)⟩

theorem isTotalQueryBound_runMWR : ∀ (y : List UInt8) (es : List (List UInt8)),
    IsTotalQueryBound (ChainSpecW.runMW hashR y es) (es.length + 1)
  | y, [] => by
    simp only [ChainSpecW.runMW, hashR, callKeccak256R, bind_assoc, pure_bind]
    exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun _ => trivial⟩
  | y, e :: es => by
    simp only [ChainSpecW.runMW, hashR, callKeccak256R, bind_assoc, pure_bind]
    refine isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun u => ?_⟩
    have h := isTotalQueryBound_runMWR (stepIn (toB u.1) e) es
    have h' := isTotalQueryBound_bind (ob := fun rest =>
      (pure ((toB u.1, u.2) :: rest) : OracleComp KeccakCallsR (List (Bytes32 × TailP)))) h (n₂ := 0)
      fun _ => trivial
    simpa using h'

theorem isTotalQueryBound_preWideR (A : OracleComp KeccakCallsR Pf) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) : IsTotalQueryBound (preWideR W view A) (QA + W.nQ) := by
  have hc : ∀ s ms, IsTotalQueryBound (W.chain hashR s ms) W.nQ := by
    intro s ms
    have h := isTotalQueryBound_runMWR (W.label s) (W.absorbsS s W.K.rounds ms)
    rw [ChainSpecW.absorbsS, length_absorbsW] at h
    exact (isQueryBound_map_iff _ _ _ _ _).mpr h
  have h := isTotalQueryBound_bind
    (ob := fun pt : Pf × Transcript => W.chain hashR (view pt.1).1 (view pt.1).2 >>= fun ch =>
      (pure (pt.1, ch, pt.2) : OracleComp KeccakCallsR (PreK Pf F)))
    (isTotalQueryBound_loggedKCR_run A QA [] hA) fun pt =>
      isTotalQueryBound_bind
        (ob := fun ch => (pure (pt.1, ch, pt.2) : OracleComp KeccakCallsR (PreK Pf F))) (n₂ := 0)
        (hc (view pt.1).1 (view pt.1).2) fun _ => trivial
  rwa [Nat.add_zero] at h

theorem isTotalQueryBound_expLGR (X : OracleComp KeccakCallsR (PreK Pf F)) (ops : List (GOp Pf F M))
    (QX : ℕ) (hX : IsTotalQueryBound X QX) :
    IsTotalQueryBound (expLGR view X ops) (QX + (ops.map fun o => o.QO).sum) := by
  unfold expLGR
  exact isTotalQueryBound_loggedKCR_run _ _ [] (isTotalQueryBound_bind hX fun x =>
    (isQueryBound_map_iff _ _ _ _ _).mpr
      (isTotalQueryBound_liftR _ _ (isTotalQueryBound_gopsRun view ops x.1 x.2.1)))

theorem isTotalQueryBound_withSetupGR {σ : Type} (setup : OracleComp KeccakCalls σ)
    (fix : σ → Pf → Pf) (A₀ : σ → OracleComp KeccakCallsR Pf) (QS Q : ℕ)
    (hS : IsTotalQueryBound setup QS) (hQ : ∀ s, IsTotalQueryBound (A₀ s) Q) :
    IsTotalQueryBound (withSetupGR setup fix A₀) (QS + Q) :=
  isTotalQueryBound_bind (isTotalQueryBound_liftR _ _ hS) fun s =>
    (isQueryBound_map_iff _ _ _ _ _).mpr (hQ s)

end Exp

/-! ## The bad events of the rate model -/

section Bad

variable {F St M Pf : Type} [SampleableType F]
variable (W : ChainSpecW F St) (C : ℕ → ListCommit M) (R : Piop W.K M) (view : Pf → St × List (RMsg F))

/-- **A fresh answer after the adversary's last query is one of its roots**, in the rate model. -/
def rootBadR (A : OracleComp KeccakCallsR Pf) (H : Finset (List UInt8 ⊕ KeccakState))
    (d : List UInt8 ⊕ KeccakState) (T : KTableR) : Prop :=
  match d with
  | .inl x => (∀ q ∈ (tableQueryLog A T).map Sigma.fst, q ∈ H) ∧
      toB (T (.inl x)).1 ∈ W.K.rootsK (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).2
  | .inr _ => False

/-- **A bad query of the rate model**: on its two-oracle table and its tails, a query bad for the wide chain
(`kcBadW`), or a fresh answer that is an announced root. -/
def advBadWR (A : OracleComp KeccakCallsR Pf) (H : Finset (List UInt8 ⊕ KeccakState))
    (d : List UInt8 ⊕ KeccakState) (T : KTableR) : Prop :=
  kcBadW W C R (splitT T) H d (splitD T) ∨ rootBadR W view A H d T

/-- A fresh bad query for one table and family is one for another, when the one implies the other. -/
theorem freshBad_table {D τ₁ τ₂ : Type} [DecidableEq D] {b₁ : Finset D → D → τ₁ → Prop}
    {b₂ : Finset D → D → τ₂ → Prop} {T₁ : τ₁} {T₂ : τ₂} (h : ∀ H x, b₁ H x T₁ → b₂ H x T₂) :
    ∀ (H : Finset D) (L : List D), FreshBad b₁ T₁ H L → FreshBad b₂ T₂ H L
  | _, [], hb => hb
  | H, x :: xs, hb => by
    rcases hb with ⟨hx, hbx⟩ | hb
    · exact Or.inl ⟨hx, h _ _ hbx⟩
    · exact Or.inr (freshBad_table h _ xs hb)

end Bad

/-! ## The trace -/

section Trace

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]
variable (W : ChainSpecW F St) (R : Piop W.K M) (view : Pf → St × List (RMsg F))

open Classical in
/-- **The trace in the rate model**: on every rate table, a run that breaks knowledge soundness while no opening is
doomed at its end and no two answers of its transcript make a pair asks a bad fresh query (`trace_whirWG` at the
table's tails). -/
theorem trace_whirWR {σ : Type} (ops : List (GOp Pf F M)) (tc : ℕ → TableCode M)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A₀ : σ → OracleComp KeccakCallsR Pf)
    (hok : ∀ o ∈ ops, GOp.OK tc good setup fix o)
    (hcov : ∀ i < W.K.rounds.length, (W.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, GOp.SetupHolds o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll W.K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = W.K.rounds.length →
      (∀ i (h : i < cs.length), (W.K.spec i).root → good i π ch cs[i]) →
      (∀ i (h : i < cs.length), (W.K.spec i).root = false → cs[i] = none) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (tag : List UInt8) (T : KTableR)
    (hlabT : ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG setup fix
        (fun s => simulateQ (instR (splitT T)) (A₀ s))) (splitD T)).map Sigma.fst ∧
      (W.label (view (evalWithAnswerFn (QueryImpl.ofFn (splitD T)) (withSetupG setup fix
        (fun s => simulateQ (instR (splitT T)) (A₀ s))))).1).take 32 =
        tag ++ (viewT (splitD T) w).toList.take (32 - tag.length))
    (hev : BreaksOK W.K (fun i => (tc i).commit) R view check
        (fun bs => ∀ k < ops.length, bs.getD k false = true)
        (evalWithAnswerFn (QueryImpl.ofFn T)
          (expLGR view (preWideR W view (withSetupGR setup fix A₀)) ops)).1 ∧
      ¬ DoomFG view ops (evalWithAnswerFn (QueryImpl.ofFn T)
          (expLGR view (preWideR W view (withSetupGR setup fix A₀)) ops)) ∧
      ¬ PairTr tag (evalWithAnswerFn (QueryImpl.ofFn T)
          (expLGR view (preWideR W view (withSetupGR setup fix A₀)) ops)).2) :
    FreshBad (advBadWR W (fun i => (tc i).commit) R view (withSetupGR setup fix A₀)) T ∅
      ((tableQueryLog (expLGR view (preWideR W view (withSetupGR setup fix A₀)) ops) T).map
        Sigma.fst) := by
  set τ := splitT T
  have hcomm : simulateQ (instR τ) (expLGR view (preWideR W view (withSetupGR setup fix A₀)) ops) =
      expLG view (preWide W view τ (withSetupG setup fix (fun s => simulateQ (instR τ) (A₀ s)))) ops := by
    rw [instR_expLGR, instR_preWideR, instR_withSetupGR]
  have heval := eval_instR T (expLGR view (preWideR W view (withSetupGR setup fix A₀)) ops)
  rw [hcomm] at heval
  have hlog := log_instR T (expLGR view (preWideR W view (withSetupGR setup fix A₀)) ops)
  rw [hcomm] at hlog
  rw [heval] at hev
  have hD := trace_whirWG W R view τ ops tc check good goodS setup fix
    (fun s => simulateQ (instR τ) (A₀ s)) hok hcov hS hfit hlink tag (splitD T) hlabT hev
  rw [hlog]
  refine freshBad_table (fun H d hb => ?_) ∅ _ hD
  rcases hb with hk | hr
  · exact Or.inl hk
  · right
    rcases d with x | s
    · obtain ⟨hq, hroot⟩ := hr
      have e1 := eval_instR T (withSetupGR setup fix A₀)
      rw [instR_withSetupGR] at e1
      have e2 := log_instR T (withSetupGR setup fix A₀)
      rw [instR_withSetupGR] at e2
      refine ⟨fun q hq' => hq q (by rw [← e2]; exact hq'), ?_⟩
      rw [e1]
      exact hroot
    · exact hr.elim

end Trace

/-! ## Each fresh query is bad with small probability -/

section Prob

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]
variable (W : ChainSpecW F St) (C : ℕ → ListCommit M) (R : Piop W.K M) (view : Pf → St × List (RMsg F))

/-- **A rate answer, its digest read as 32 bytes, is uniform.** -/
theorem prEvent_rateAns (P : Bytes32 × TailP → Prop) :
    Pr{let u ← $ᵗ (Digest × TailP)}[P (toB u.1, u.2)] = Pr{let p ← $ᵗ (Bytes32 × TailP)}[P p] := by
  classical
  refine prEvent_uniform_balanced (fun u : Digest × TailP => (toB u.1, u.2)) 1 (fun y => ?_) P
  rw [Finset.card_eq_one]
  refine ⟨(LeanVM.Rpm.digestEquiv.symm y.1, y.2), ?_⟩
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    rw [← h]
    exact Prod.ext (LeanVM.Rpm.digestEquiv.symm_apply_apply u.1).symm rfl
  · intro h
    rw [h]
    exact Prod.ext (LeanVM.Rpm.digestEquiv.apply_symm_apply y.1) rfl

/-- **The first component of a uniform pair is uniform.** -/
theorem prEvent_fst {X Y : Type} [SampleableType X] [SampleableType Y] (P : X → Prop) :
    Pr{let p ← $ᵗ (X × Y)}[P p.1] = Pr{let x ← $ᵗ X}[P x] := by
  have h : (Prod.fst <$> ($ᵗ (X × Y) : ProbComp (X × Y))) =ᵈ ($ᵗ X : ProbComp X) := by
    rw [SampleableType.uniformSample_prod_eq_bind]
    simp only [map_bind, map_pure]
    refine (EvalDistEq.bind_right _ fun x => OracleComp.EvalDistEq.bind_const _ _).trans ?_
    rw [bind_pure]
  exact (prEvent_map _ Prod.fst P).symm.trans (h.prEvent_eq P)

/-- A digest in a set of `k` 32-byte strings: at most `k / 2^256`. -/
theorem prEvent_rate_mem_le (B : Finset Bytes32) :
    Pr{let u ← $ᵗ (Digest × TailP)}[toB u.1 ∈ B] ≤ (B.card : ℝ≥0∞) / 2 ^ 256 := by
  classical
  rw [prEvent_rateAns (fun p => p.1 ∈ B), prEvent_fst (fun b : Bytes32 => b ∈ B),
    SampleableType.prEvent_uniformSample, card_bytes32, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Nat.cast_pow, Nat.cast_ofNat]

/-- The rate model's uniform answer to a Keccak-256 query is a uniform digest and tail. -/
theorem prEvent_rateRange (x : List UInt8) (P : KeccakCallsR.Range (.inl x) → Prop) :
    Pr{let u ← $ᵗ (KeccakCallsR.Range (.inl x))}[P u] = Pr{let u ← $ᵗ (Digest × TailP)}[P u] := rfl

/-- **A collision of a fresh digest**: at most `(|H| + nRf (|H| + 1)) / 2^256`. -/
theorem prob_collW (H' : Hist) (x : List UInt8) (hxv : x ∉ H') (Tf : Table) :
    Pr{let u ← $ᵗ (Digest × TailP)}[W.CollW H' x (Function.update Tf x (toB u.1))] ≤
      ((H'.card + W.nRf * (H'.card + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  classical
  let Bad : Finset Bytes32 := H'.image Tf ∪ (insert x H').biUnion fun y => (W.refs y).toFinset
  have hsub : ∀ u : Digest × TailP, W.CollW H' x (Function.update Tf x (toB u.1)) → toB u.1 ∈ Bad := by
    intro u h
    rcases h with ⟨y, hy, hyx⟩ | ⟨y, hy, h⟩
    · have hyx' : y ≠ x := fun e => hxv (e ▸ hy)
      rw [Function.update_of_ne hyx', Function.update_self] at hyx
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y, hy, hyx⟩)
    · rw [Function.update_self] at h
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨y, hy, List.mem_toFinset.mpr (W.rf_refs y _ h)⟩)
  have hc : Bad.card ≤ H'.card + W.nRf * (H'.card + 1) := by
    refine (Finset.card_union_le _ _).trans ?_
    have h3 : ∑ y ∈ insert x H', (W.refs y).toFinset.card ≤ (insert x H').card * W.nRf := by
      simpa using Finset.sum_le_card_nsmul _ _ W.nRf fun y _ =>
        (List.toFinset_card_le _).trans (W.length_refs y)
    have h2 := Finset.card_biUnion_le (s := insert x H') (t := fun y => (W.refs y).toFinset)
    have h4 := Finset.card_insert_le x H'
    have h5 := Finset.card_image_le (s := H') (f := Tf)
    have h6 : (insert x H').card * W.nRf ≤ (H'.card + 1) * W.nRf := Nat.mul_le_mul_right _ h4
    nlinarith
  calc Pr{let u ← $ᵗ (Digest × TailP)}[W.CollW H' x (Function.update Tf x (toB u.1))]
      ≤ Pr{let u ← $ᵗ (Digest × TailP)}[toB u.1 ∈ Bad] := prEvent_mono _ _ _ hsub
    _ ≤ (Bad.card : ℝ≥0∞) / 2 ^ 256 := prEvent_rate_mem_le Bad
    _ ≤ _ := by gcongr

/-- **A round is bad at a fresh query with probability at most its error times its factor**: the parse is read off
the history, so at most one round and one parse are possible, the candidates and the challenges before are fixed by
the history, and the query's wide draw is uniform. -/
theorem prob_roundBadW (H' : Hist) (x : List UInt8) (hxv : x ∉ H') (Tf : Table) (τf : List UInt8 → TailP) :
    Pr{let u ← $ᵗ (Digest × TailP)}[
      RoundBadW W C R H' x (Function.update Tf x (toB u.1)) (Function.update τf x u.2)] ≤ maxErrK W.K C R := by
  classical
  have hcg : ∀ u : Digest × TailP, ∀ y ∈ H', Function.update Tf x (toB u.1) y = Tf y :=
    fun u y hy => Function.update_of_ne (fun e : y = x => hxv (e ▸ hy)) _ _
  have hτg : ∀ u : Digest × TailP, ∀ y ∈ H', Function.update τf x u.2 y = τf y :=
    fun u y hy => Function.update_of_ne (fun e : y = x => hxv (e ▸ hy)) _ _
  by_cases hp : ∃ j s ms m, ParseW W H' x Tf j s ms m
  · obtain ⟨j, s, ms, m, hp⟩ := hp
    have hj : j < W.K.rounds.length := hp.1
    let chs := W.chalsT Tf τf s (W.K.rounds.take j) ms
    let Ls := candLists C H' Tf 0 ms
    let oc := optC (C j) H' Tf m
    let E : List (Option M) → Digest × TailP → Prop := fun cs u => ∃ c' ∈ oc,
      ¬ R.pre s (opened cs ms chs) (c', m.2) ∧ R.post s (opened cs ms chs) (c', m.2)
        (chalsW W.K.lim ((W.K.spec j).ns + 1) (toB u.1) u.2)
    have hsub : ∀ u : Digest × TailP,
        RoundBadW W C R H' x (Function.update Tf x (toB u.1)) (Function.update τf x u.2) →
          ∃ cs, List.Forall₂ (· ∈ ·) cs Ls ∧ E cs u := by
      intro u hu
      obtain ⟨j', s', ms', m', hp', cs, c', hcs, hc', h3, h4⟩ := hu
      rw [parseW_congr (hcg u)] at hp'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := parseW_unique hp hp'
      have hch : W.chalsT (Function.update Tf x (toB u.1)) (Function.update τf x u.2) s
          (W.K.rounds.take j) ms = chs :=
        chalsTW_congr _ _ _ _ (fun z hz => (hcg u z (hp.allIn_sub z hz)).symm)
          (fun z hz => (hτg u z (hp.allIn_sub z hz)).symm)
      rw [candLists_congr C (hcg u)] at hcs
      rw [optC_congr (C j) (hcg u)] at hc'
      rw [hch] at h3 h4
      rw [Function.update_self, Function.update_self] at h4
      exact ⟨cs, hcs, c', hc', h3, h4⟩
    have hone : ∀ cs, List.Forall₂ (· ∈ ·) cs Ls → ∀ c' ∈ oc,
        Pr{let u ← $ᵗ (Digest × TailP)}[¬ R.pre s (opened cs ms chs) (c', m.2) ∧
          R.post s (opened cs ms chs) (c', m.2)
            (chalsW W.K.lim ((W.K.spec j).ns + 1) (toB u.1) u.2)] ≤ R.err j := by
      intro cs hcs c' _
      have hlen : (opened cs ms chs).length = j := by
        rw [length_opened cs ms chs (hcs.length_eq.trans (length_candLists C _ _ 0 ms)), hp.length_eq]
      have e1 := prEvent_rateAns (fun p : Bytes32 × TailP => ¬ R.pre s (opened cs ms chs) (c', m.2) ∧
        R.post s (opened cs ms chs) (c', m.2) (chalsW W.K.lim ((W.K.spec j).ns + 1) p.1 p.2))
      have e2 := prEvent_wide W.K.lim ((W.K.spec j).ns) (W.ns_le_spec j)
        (fun l => ¬ R.pre s (opened cs ms chs) (c', m.2) ∧ R.post s (opened cs ms chs) (c', m.2) l)
      refine le_trans (le_of_eq (e1.trans e2)) ?_
      exact R.sound j s _ _ hj hlen
    have hf1 := prod_candLists_le C H' Tf 0 _ ms hp.2.1
    have hf2 := length_optC_le (C j) H' Tf hp.2.2.1
    have hfac : (Ls.map List.length).prod * oc.length ≤ facL C 0 (W.K.rounds.take (j + 1)) := by
      rw [facL_take_succ W.K C j hj]
      exact Nat.mul_le_mul hf1 hf2
    calc Pr{let u ← $ᵗ (Digest × TailP)}[
          RoundBadW W C R H' x (Function.update Tf x (toB u.1)) (Function.update τf x u.2)]
        ≤ Pr{let u ← $ᵗ (Digest × TailP)}[∃ cs, List.Forall₂ (· ∈ ·) cs Ls ∧ E cs u] :=
          prEvent_mono _ _ _ hsub
      _ ≤ ((Ls.map List.length).prod : ℝ≥0∞) * ((oc.length : ℝ≥0∞) * R.err j) :=
          prEvent_forall₂_le _ E ((oc.length : ℝ≥0∞) * R.err j) Ls fun cs hcs =>
            prEvent_exists_mem_le _ _ _ oc fun c' hc' => hone cs hcs c' hc'
      _ = (((Ls.map List.length).prod * oc.length : ℕ) : ℝ≥0∞) * R.err j := by
          push_cast
          ring
      _ ≤ (facL C 0 (W.K.rounds.take (j + 1)) : ℝ≥0∞) * R.err j := by
          gcongr
      _ ≤ maxErrK W.K C R :=
          Finset.le_sup (f := fun j => (facL C 0 (W.K.rounds.take (j + 1)) : ℝ≥0∞) * R.err j)
            (Finset.mem_range.mpr hj)
  · rw [prEvent_eq_zero_of_forall_not _ _ fun u hu => ?_]
    · exact bot_le
    obtain ⟨j, s, ms, m, hp', -⟩ := hu
    exact hp ⟨j, s, ms, m, (parseW_congr (hcg u) _ _ _ _ _).mp hp'⟩

/-- **A fresh answer is one of the adversary's roots** with probability at most `k / 2^256`. -/
theorem prob_rootBadR (A : OracleComp KeccakCallsR Pf) (Hm : Finset (List UInt8 ⊕ KeccakState))
    (x : List UInt8) (hx : (Sum.inl x : List UInt8 ⊕ KeccakState) ∉ Hm) (T₀ : KTableR) :
    Pr{let u ← $ᵗ (Digest × TailP)}[rootBadR W view A Hm (.inl x) (Function.update T₀ (.inl x) u)] ≤
      (W.K.rounds.length : ℝ≥0∞) / 2 ^ 256 := by
  classical
  have hagree : ∀ u u' : Digest × TailP, ∀ q ∈ Hm,
      Function.update T₀ (.inl x) u q = Function.update T₀ (.inl x) u' q := by
    intro u u' q hq
    have hqx : q ≠ .inl x := fun e => hx (e ▸ hq)
    rw [Function.update_of_ne hqx, Function.update_of_ne hqx]
  by_cases hex : ∃ u₀ : Digest × TailP,
      ∀ q ∈ (tableQueryLog A (Function.update T₀ (.inl x) u₀)).map Sigma.fst, q ∈ Hm
  · obtain ⟨u₀, hu₀⟩ := hex
    obtain ⟨rs₀, hrs₀⟩ : ∃ l, l = W.K.rootsK (view (evalWithAnswerFn
        (QueryImpl.ofFn (Function.update T₀ (.inl x) u₀)) A)).2 := ⟨_, rfl⟩
    have hsub : ∀ u : Digest × TailP,
        rootBadR W view A Hm (.inl x) (Function.update T₀ (.inl x) u) → toB u.1 ∈ rs₀.toFinset := by
      intro u hu
      obtain ⟨-, hr⟩ := hu
      have hc := run_congr A (Function.update T₀ (.inl x) u₀) (Function.update T₀ (.inl x) u)
        fun q hq => hagree u₀ u q (hu₀ q hq)
      rw [Function.update_self, ← hc.1, ← hrs₀] at hr
      exact List.mem_toFinset.mpr hr
    calc Pr{let u ← $ᵗ (Digest × TailP)}[rootBadR W view A Hm (.inl x) (Function.update T₀ (.inl x) u)]
        ≤ Pr{let u ← $ᵗ (Digest × TailP)}[toB u.1 ∈ rs₀.toFinset] := prEvent_mono _ _ _ hsub
      _ ≤ (rs₀.toFinset.card : ℝ≥0∞) / 2 ^ 256 := prEvent_rate_mem_le _
      _ ≤ _ := by
          gcongr
          rw [hrs₀]
          exact_mod_cast (List.toFinset_card_le _).trans (W.K.length_rootsK_le _)
  · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
    intro u h
    exact hex ⟨u, h.1⟩

/-- **Each fresh query of the rate model is bad with probability at most
`(|H| + nRf (|H| + 1) + k) / 2^256 + maxErrK`.** -/
theorem prob_advBadWR (A : OracleComp KeccakCallsR Pf) (S : Finset (List UInt8 ⊕ KeccakState))
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCallsR d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCallsR d.1)}[advBadWR W C R view A
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      (((cacheDom c).card + W.nRf * ((cacheDom c).card + 1) + W.K.rounds.length : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        maxErrK W.K C R := by
  classical
  set Hm := (cacheDom c).map (Function.Embedding.subtype (· ∈ S)) with hHm
  have htH : t.1 ∉ Hm := by
    intro h
    obtain ⟨y, hy, hyt⟩ := Finset.mem_map.mp h
    have : y = t := Subtype.ext hyt
    subst this
    rw [mem_cacheDom] at hy
    exact hy ht
  have hH' : (viewH Hm).card ≤ (cacheDom c).card := by
    refine (Finset.card_le_card_of_injOn (t := Hm) Sum.inl (fun y hy => ?_)
      Sum.inl_injective.injOn).trans (Finset.card_map _).le
    exact mem_viewH.mp hy
  refine prEvent_completeTable_cell_le c t ht
    (fun t' g => advBadWR W C R view A Hm t'.1 (extendTable S g)) _ (fun g => ?_)
  simp only [extendTable_update]
  obtain ⟨d, hd⟩ := t
  cases d with
  | inr s =>
    refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
    intro u h
    rcases h with h | h <;> exact h
  | inl x =>
    simp only at htH ⊢
    have hxv : x ∉ viewH Hm := fun h => htH (mem_viewH.mp h)
    -- The event, on a fresh digest and tail.
    have hev : ∀ u : Digest × TailP,
        advBadWR W C R view A Hm (.inl x) (Function.update (extendTable S g) (.inl x) u) →
          (W.CollW (viewH Hm) x (Function.update (viewT (splitD (extendTable S g))) x (toB u.1)) ∨
            RoundBadW W C R (viewH Hm) x (Function.update (viewT (splitD (extendTable S g))) x (toB u.1))
              (Function.update (splitT (extendTable S g)) x u.2)) ∨
            rootBadR W view A Hm (.inl x) (Function.update (extendTable S g) (.inl x) u) := by
      intro u h
      have hTu : ∀ y : List UInt8, y ≠ x →
          Function.update (extendTable S g) (.inl x) u (.inl y) = extendTable S g (.inl y) := fun y hy =>
        Function.update_of_ne (fun h => hy (Sum.inl_injective h)) _ _
      rcases h with h | h
      · left
        refine (listBadW_congr W C R (fun y hy => ?_) ?_ (fun y hy => ?_) ?_).mp h
        · have hyx : y ≠ x := fun e => hxv (e ▸ hy)
          rw [Function.update_of_ne hyx]
          simp only [viewT, splitD]
          rw [hTu y hyx]
        · simp [viewT, splitD]
        · have hyx : y ≠ x := fun e => hxv (e ▸ hy)
          rw [Function.update_of_ne hyx]
          simp only [splitT]
          rw [hTu y hyx]
        · simp [splitT]
      · exact Or.inr h
    rw [prEvent_rateRange x]
    calc _ ≤ _ := prEvent_mono _ _ _ hev
      _ ≤ _ := prEvent_or_le _ _ _
      _ ≤ _ := add_le_add (prEvent_or_le _ _ _) le_rfl
      _ ≤ (((viewH Hm).card + W.nRf * ((viewH Hm).card + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 + maxErrK W.K C R +
            (W.K.rounds.length : ℝ≥0∞) / 2 ^ 256 :=
          add_le_add (add_le_add (prob_collW W _ x hxv _) (prob_roundBadW W C R _ x hxv _ _))
            (prob_rootBadR W view A Hm x htH _)
      _ ≤ _ := by
          have hle : (viewH Hm).card + W.nRf * ((viewH Hm).card + 1) ≤
              (cacheDom c).card + W.nRf * ((cacheDom c).card + 1) := by
            have := Nat.mul_le_mul_left W.nRf (Nat.add_le_add_right hH' 1)
            omega
          rw [Nat.cast_add (R := ℝ≥0∞) ((cacheDom c).card + W.nRf * ((cacheDom c).card + 1))
            W.K.rounds.length, ENNReal.add_div]
          calc (((viewH Hm).card + W.nRf * ((viewH Hm).card + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 + maxErrK W.K C R +
                (W.K.rounds.length : ℝ≥0∞) / 2 ^ 256
              ≤ (((cacheDom c).card + W.nRf * ((cacheDom c).card + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 +
                  maxErrK W.K C R + (W.K.rounds.length : ℝ≥0∞) / 2 ^ 256 := by
                gcongr
            _ = _ := by ring

end Prob

/-! ## Knowledge soundness in the rate model -/

section Closed

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]
variable (W : ChainSpecW F St) (R : Piop W.K M) (view : Pf → St × List (RMsg F))

/-- **Knowledge soundness of the wide chain with openings, in the rate model, at `≥ 128` bits**: the verifier
accepts while no candidate of round `0`'s root read off the adversary's (and the setup's) queries satisfies the
first round's state with probability at most

`bnd N + 2 N² / 2^256 + N (maxErrK + (nRf + 2) N / 2^256)`,  `N = QS + Q + nQ + Σ_k QO_k`,

for openings whose union is sound at `bnd` (`GUnionSound`), when the label's first 32 bytes are `tag ‖` the first
`32 − |tag|` bytes of an answer the adversary asked, at every table of tails (`hlab`). -/
theorem knowledgeSoundness_listChainW_closed128R {σ : Type} (ops : List (GOp Pf F M))
    (tc : ℕ → TableCode M) (check : Pf → List (List F) → Prop)
    (good : ℕ → Pf → List (List F) → Option M → Prop) (goodS : Pf → List (List F) → Prop)
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf) (A₀ : σ → OracleComp KeccakCallsR Pf)
    (QS Q : ℕ) (hSq : IsTotalQueryBound setup QS) (hQ : ∀ s, IsTotalQueryBound (A₀ s) Q)
    (hok : ∀ o ∈ ops, GOp.OK tc good setup fix o)
    (hcov : ∀ i < W.K.rounds.length, (W.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, GOp.SetupHolds o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll W.K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = W.K.rounds.length →
      (∀ i (h : i < cs.length), (W.K.spec i).root → good i π ch cs[i]) →
      (∀ i (h : i < cs.length), (W.K.spec i).root = false → cs[i] = none) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (tag : List UInt8) (htag : tag.length = 16)
    (hlab : ∀ (τ : List UInt8 → TailP) (T : KTable), ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG setup fix
        (fun s => simulateQ (instR τ) (A₀ s))) T).map Sigma.fst ∧
      (W.label (view (evalWithAnswerFn (QueryImpl.ofFn T) (withSetupG setup fix
        (fun s => simulateQ (instR τ) (A₀ s))))).1).take 32 =
        tag ++ (viewT T w).toList.take (32 - tag.length))
    (bnd : ℕ → ℝ≥0∞) (hU : GUnionSound view ops bnd) :
    Pr{let z ← (simulateQ randomOracle
        (expLGR view (preWideR W view (withSetupGR setup fix A₀)) ops)).run' ∅}[
        BreaksOK W.K (fun i => (tc i).commit) R view check
          (fun bs => ∀ k < ops.length, bs.getD k false = true) z.1] ≤
      bnd (QS + Q + W.nQ + (ops.map fun o => o.QO).sum) +
      ((2 * (QS + Q + W.nQ + (ops.map fun o => o.QO).sum) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
      ((QS + Q + W.nQ + (ops.map fun o => o.QO).sum : ℕ) : ℝ≥0∞) *
        (maxErrK W.K (fun i => (tc i).commit) R +
          (((W.nRf + 2) * (QS + Q + W.nQ + (ops.map fun o => o.QO).sum) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  set A := withSetupGR setup fix A₀ with hAdef
  have hA : IsTotalQueryBound A (QS + Q) := isTotalQueryBound_withSetupGR setup fix A₀ QS Q hSq hQ
  set CC : ℕ → ListCommit M := fun i => (tc i).commit with hCC
  set accL : List Bool → Prop := fun bs => ∀ k < ops.length, bs.getD k false = true with haccL
  set N := QS + Q + W.nQ + (ops.map fun o => o.QO).sum with hN
  set X := preWideR W view A with hX
  have hXq : IsTotalQueryBound X (QS + Q + W.nQ) := isTotalQueryBound_preWideR W view A _ hA
  set mx := (simulateQ randomOracle (expLGR view X ops)).run' ∅ with hmx
  refine (prEvent_mono mx _ (fun z => DoomFG view ops z ∨ PairTr tag z.2 ∨
    (BreaksOK W.K CC R view check accL z.1 ∧ ¬ DoomFG view ops z ∧ ¬ PairTr tag z.2))
    fun z h => ?_).trans ((prEvent_or_le _ _ _).trans ?_)
  · by_cases hd : DoomFG view ops z
    · exact Or.inl hd
    · by_cases hpt : PairTr tag z.2
      · exact Or.inr (Or.inl hpt)
      · exact Or.inr (Or.inr ⟨h, hd, hpt⟩)
  rw [add_assoc]
  -- The openings' doom and the seed's pair, tail table by tail table.
  have hdoom : Pr{let z ← mx}[DoomFG view ops z] ≤ bnd N :=
    prEvent_rate_le _ _ _ fun τ => by
      rw [instR_expLGR]
      exact prEvent_doomFG_le view ops bnd hU _ _ (isTotalQueryBound_instR τ _ _ hXq)
  have hpair : Pr{let z ← mx}[PairTr tag z.2] ≤ ((2 * N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
    prEvent_rate_le _ _ _ fun τ => by
      rw [instR_expLGR]
      exact prEvent_pairTr_expLG_le view _ ops _ (isTotalQueryBound_instR τ _ _ hXq) tag htag
  refine add_le_add hdoom ((prEvent_or_le _ _ _).trans (add_le_add hpair ?_))
  -- The fresh bad queries.
  refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCallsR) (expLGR view X ops) N
    (isTotalQueryBound_expLGR view X ops _ hXq) ∅ Set.finite_empty _ (advBadWR W CC R view A) _
    (fun S _ c t ht hcard => ?_)
    (fun T h => trace_whirWR W R view ops tc check good goodS setup fix A₀ hok hcov hS hfit hlink tag T
      (hlab (splitT T) (splitD T)) h)
  refine (prob_advBadWR W CC R view A S c t ht).trans ?_
  have hk : W.K.rounds.length < W.nQ := by
    simp only [ChainSpecW.nQ]
    omega
  have hNle : (cacheDom c).card + W.nRf * ((cacheDom c).card + 1) + W.K.rounds.length ≤
      (W.nRf + 2) * N := by
    have hc1 : (cacheDom c).card + 1 ≤ N := hcard
    have h2 : W.nRf * ((cacheDom c).card + 1) ≤ W.nRf * N := Nat.mul_le_mul_left _ hc1
    have h3 : W.K.rounds.length ≤ N := by omega
    nlinarith
  calc (((cacheDom c).card + W.nRf * ((cacheDom c).card + 1) + W.K.rounds.length : ℕ) :
        ℝ≥0∞) / 2 ^ 256 + maxErrK W.K CC R
      ≤ (((W.nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256 + maxErrK W.K CC R :=
        add_le_add (ENNReal.div_le_div_right (Nat.cast_le.mpr hNle) _) le_rfl
    _ = maxErrK W.K CC R + (((W.nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256 := by ring

end Closed

end Compose

/-- info: 'Compose.knowledgeSoundness_listChainW_closed128R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_listChainW_closed128R
