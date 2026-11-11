-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/TwoOracle.lean` of this repository (its chain-specific part:
-- the bad query of both oracles, its probability, the experiment, the trace), whose engine, view and
-- logging are reused as they are. The model is leanerVM `mumbai`'s
-- (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0): `KeccakCalls`.
import ComposePcs.ListChain4
import Compose.TwoOracle

/-!
# The four-root chain in mumbai's two-oracle model

`ListChain4.lean`'s list argument in leanerVM `mumbai`'s random-oracle model `KeccakCalls`
(Keccak-256 and Keccak-f[1600], two independent lazily sampled oracles), F2's model, as
`Compose/TwoOracle.lean` does for the two-root chain: a query is bad when it is Keccak-256's and
`listBad4` of the view (`kcBad4`); each fresh query is bad with `listBad4`'s probability
(`prob_kcBad4`, through `Compose.prEvent_view`); the experiment (`kcExperiment4`) runs the adversary,
the chain over Keccak-256 (`Compose.hash256`), then any computation of both oracles (the openings),
with the transcript of the Keccak-256 queries (`Compose.loggedKC`).

**`knowledgeSoundness_list_kc4`**: `knowledgeSoundness_list4`'s bound in mumbai's model.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace ComposePcs

open Compose QuotientRpm QuotientSecurity QuotientSecurity.Params
open LeanVM LeanVM.Protocol LeanVM.Semantics

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {P : Params F} {B : P.Bounds} (W : Wire P B) {MH MQ MG : Type} (K : Commits4 B MH MQ MG)

/-- **A bad query of both oracles**: a Keccak-256 query bad for the view; never a Keccak-f
query. -/
def kcBad4 (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) :
    Prop :=
  match d with
  | .inl x => listBad4 W K (viewH H) x (viewT T)
  | .inr _ => False

/-- A bad fresh Keccak-256 input of the view is a bad fresh query. -/
theorem freshBad_kc4 (T : KTable) : ∀ (H : Finset (List UInt8 ⊕ KeccakState))
    (L : List (List UInt8 ⊕ KeccakState)),
    FreshBad (listBad4 W K) (viewT T) (viewH H) (L.filterMap Sum.getLeft?) →
      FreshBad (kcBad4 W K) T H L
  | _, [], h => by simp [FreshBad] at h
  | H, .inl x :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inl, FreshBad] at h ⊢
    rcases h with ⟨hx, hb⟩ | h
    · exact Or.inl ⟨fun hm => hx (mem_viewH.mpr hm), hb⟩
    · refine Or.inr (freshBad_kc4 T _ L ?_)
      rwa [viewH_insert_inl]
  | H, .inr s :: L, h => by
    simp only [List.filterMap_cons, Sum.getLeft?_inr, FreshBad] at h ⊢
    refine Or.inr (freshBad_kc4 T _ L ?_)
    rwa [viewH_insert_inr]

/-- `listBad4` reads the table on the inputs asked, at the fresh input, and at the 32-byte inputs
(the states the first round's lookahead hashes). -/
theorem listBad4_congr {H : Hist} {x : List UInt8} {T T' : Table} (hH : ∀ d ∈ H, T d = T' d)
    (hx : T x = T' x) (hs : ∀ v : Bytes32, T v.toList = T' v.toList) :
    listBad4 W K H x T ↔ listBad4 W K H x T' := by
  have hcW : ∀ r, K.CW.cands H T r = K.CW.cands H T' r := fun r => K.CW.congr H T T' r hH
  have hq : ∀ rH rQ rG, K.quot H T rH rQ rG = K.quot H T' rH rQ rG := fun rH rQ rG =>
    K.quot_congr H T T' rH rQ rG hH
  have hcoll : Coll4 H x T ↔ Coll4 H x T' := by
    unfold Coll4
    rw [hx]
    constructor
    · rintro (⟨y, hy, h⟩ | h)
      · exact Or.inl ⟨y, hy, (hH y hy).symm.trans h⟩
      · exact Or.inr h
    · rintro (⟨y, hy, h⟩ | h)
      · exact Or.inl ⟨y, hy, (hH y hy).trans h⟩
      · exact Or.inr h
  unfold listBad4 FirstBad4 SecondBad4 ThirdBad4 ParseFirst4 FreshFirst4 ParseSecond4 ParseThird4
  simp only [hcoll, hx, hs, hcW, hq, has_congr hH, injOn_congr hH]

/-- **Each fresh query of both oracles is bad with probability at most
`(7 |H| + 6) / 2^256 + listFactor4 · roundError`.** -/
theorem prob_kcBad4 (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[kcBad4 W K
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      ((7 * (cacheDom c).card + 6 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        (listFactor4 K.CW.bound K.CH.bound K.CQ.bound K.CG.bound : ℝ≥0∞) *
          (roundError P B : ℝ≥0∞) := by
  obtain ⟨d, hd⟩ := t
  cases d with
  | inr s =>
    refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
    intro g h
    exact h
  | inl x =>
    have hx : x ∈ viewH S := mem_viewH.mpr hd
    have hS₁ : ∀ v : Bytes32, v.toList ∈ viewH S := fun v => mem_viewH.mpr (hS₀ v)
    have hc₁ : viewC S c ⟨x, hx⟩ = none := by simp [viewC, ht]
    have hH : histOf (viewC S c) ⊆ viewH S := fun y hy => (mem_histOf.mp hy).1
    have hev : ∀ g, kcBad4 W K ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) (.inl x)
        (extendTable S (completeTable c g)) ↔
        listBad4 W K (histOf (viewC S c)) x (tableOf (viewC S c) (viewG S g)) := by
      intro g
      show listBad4 W K _ x _ ↔ _
      rw [← histOf_viewC]
      exact listBad4_congr W K (fun y hy => viewT_extendTable c g (hH hy))
        (viewT_extendTable c g hx) (fun v => viewT_extendTable c g (hS₁ v))
    refine (prEvent_mono _ _ (fun g => listBad4 W K (histOf (viewC S c)) x
      (tableOf (viewC S c) (viewG S g))) fun g h => (hev g).mp h).trans ?_
    rw [prEvent_view S (fun h => listBad4 W K (histOf (viewC S c)) x (tableOf (viewC S c) h))]
    refine (prob_listBad4 W K hS₁ (viewC S c) ⟨x, hx⟩ hc₁).trans ?_
    gcongr
    have hcard : (histOf (viewC S c)).card ≤ (cacheDom c).card := by
      rw [histOf_viewC]
      refine (Finset.card_le_card_of_injOn
        (t := (cacheDom c).map (Function.Embedding.subtype (· ∈ S))) Sum.inl (fun y hy => ?_)
        Sum.inl_injective.injOn).trans (Finset.card_map (Function.Embedding.subtype (· ∈ S))).le
      exact mem_viewH.mp hy
    omega

/-! ## The experiment in mumbai's model -/

variable {O β : Type}

/-- **The run in mumbai's model**: the adversary, the chain over Keccak-256 on its reduction
proof, then `post` (the openings, any computation of both oracles). -/
def kcRun4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls (Run4 F O β) :=
  A >>= fun p => chainWith4 W hash256 p.1 >>= fun ch => post p ch >>= fun b =>
    pure ⟨p.1, p.2, ch, b⟩

/-- **The experiment in mumbai's model**: the run, with the transcript of its Keccak-256
queries, the adversary's, the chain's and the openings'. -/
def kcExperiment4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls (Run4 F O β × Transcript) :=
  loggedKC (kcRun4 W A post)

theorem chain4_queryBound_kc (π : RootProof4 F) : IsTotalQueryBound (chainWith4 W hash256 π) 6 := by
  simp only [chainWith4, hash256, callKeccak256, bind_assoc, pure_bind]
  repeat' (first | trivial | refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => ?_⟩)

theorem kcExperiment4_queryBound (A : OracleComp KeccakCalls (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    IsTotalQueryBound (kcExperiment4 W A post) (Q + 6 + QV) := by
  refine isTotalQueryBound_loggedKC_run _ _ _ ?_
  have h : ∀ p : RootProof4 F × O, IsTotalQueryBound (chainWith4 W hash256 p.1 >>= fun ch =>
      post p ch >>= fun b => (pure ⟨p.1, p.2, ch, b⟩ : OracleComp KeccakCalls (Run4 F O β)))
        (6 + (QV + 0)) :=
    fun p => isTotalQueryBound_bind (chain4_queryBound_kc W p.1) fun ch =>
      isTotalQueryBound_bind (hV p ch) fun b =>
        (trivial : IsTotalQueryBound (pure ⟨p.1, p.2, ch, b⟩ :
          OracleComp KeccakCalls (Run4 F O β)) 0)
  have := isTotalQueryBound_bind hQ h
  rwa [Nat.add_zero, ← Nat.add_assoc] at this

/-- The run against a table of both oracles. -/
theorem kcRun4_run (A : OracleComp KeccakCalls (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) (T : KTable) :
    let p := evalWithAnswerFn (QueryImpl.ofFn T) A
    let x₀ := labelOf4 W p.1.pre
    let x₁ := afterW W (viewT T x₀) p.1.comW
    let x₂ := (viewT T x₁).toList
    let x₃ := (viewT T x₂).toList
    let x₄ := afterHQG W (viewT T x₃) p.1.comHQG
    let x₅ := W.afterValues (viewT T x₄) p.1.v
    let ch : Chals F := ⟨W.chal (viewT T x₁), W.chal (viewT T x₂), W.chal (viewT T x₃),
      W.chal (viewT T x₄), W.chal (viewT T x₅)⟩
    (tableQueryLog (kcRun4 W A post) T).map Sigma.fst =
        (tableQueryLog A T).map Sigma.fst ++
          ([.inl x₀, .inl x₁, .inl x₂, .inl x₃, .inl x₄, .inl x₅] ++
            (tableQueryLog (post p ch) T).map Sigma.fst) ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (kcRun4 W A post) =
        ⟨p.1, p.2, ch, evalWithAnswerFn (QueryImpl.ofFn T) (post p ch)⟩ := by
  intro p x₀ x₁ x₂ x₃ x₄ x₅ ch
  constructor
  · simp only [kcRun4, chainWith4, hash256, callKeccak256, bind_assoc, pure_bind,
      tableQueryLog_bind, tableQueryLog_pure, List.map_append, List.append_nil,
      evalWithAnswerFn_liftM_query]
    rfl
  · simp only [kcRun4, chainWith4, hash256, callKeccak256, bind_assoc, pure_bind,
      evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, evalWithAnswerFn_pure]
    rfl

/-- The six chain inputs, as Keccak-256 queries, are the chain inputs. -/
theorem filterMap_six (a b c d e f : List UInt8) :
    [(Sum.inl a : List UInt8 ⊕ KeccakState), .inl b, .inl c, .inl d, .inl e, .inl f].filterMap
      Sum.getLeft? = [a, b, c, d, e, f] := by
  rw [show [(Sum.inl a : List UInt8 ⊕ KeccakState), .inl b, .inl c, .inl d, .inl e, .inl f] =
    [a, b, c, d, e, f].map Sum.inl from rfl, filterMap_getLeft?_map_inl]

/-- A transcript of Keccak-256 queries answers as the view of the table. -/
theorem tableOfTr_inlEntry (T : KTable) (lg : List ((d : List UInt8 ⊕ KeccakState) × KeccakCalls d))
    (hlg : ∀ q ∈ lg, q.2 = T q.1) :
    ∀ d ∈ histOfTr (lg.filterMap inlEntry), tableOfTr (lg.filterMap inlEntry) d = viewT T d := by
  intro d hd
  refine tableOfTr_eq (viewT T) _ (fun e he => ?_) d (by simpa [histOfTr] using hd)
  obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.mp he
  obtain ⟨d', u⟩ := q
  cases d' with
  | inl x =>
    simp only [inlEntry, Option.some.injEq] at hqe
    subst hqe
    have := hlg _ hq
    simp only at this
    simp [viewT, this]
  | inr s => simp [inlEntry] at hqe

open Classical in
/-- **The trace in mumbai's model**: on every table of both oracles, a winning run asks a bad
fresh query. -/
theorem trace_kc4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) (T : KTable)
    (hwin : ListWins4 W K (evalWithAnswerFn (QueryImpl.ofFn T) (kcExperiment4 W A post))) :
    FreshBad (kcBad4 W K) T ∅ ((tableQueryLog (kcExperiment4 W A post) T).map Sigma.fst) := by
  obtain ⟨hL, heval⟩ := kcRun4_run W A post T
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A
  set π := p.1
  have hlogE := log_loggedKC_run T (kcRun4 W A post) []
  have hevalE := eval_loggedKC_run T (kcRun4 W A post) []
  rw [List.nil_append] at hevalE
  unfold kcExperiment4 loggedKC
  rw [hlogE]
  unfold kcExperiment4 loggedKC at hwin
  rw [hevalE, heval] at hwin
  set lg := tableQueryLog (kcRun4 W A post) T
  set L := (lg.map Sigma.fst).filterMap Sum.getLeft?
  set tr : Transcript := lg.filterMap inlEntry
  have htrH : histOfTr tr = L.toFinset := by
    simp only [histOfTr, tr, L, map_fst_filterMap_inlEntry]
  have htrT : ∀ d ∈ histOfTr tr, tableOfTr tr d = viewT T d :=
    tableOfTr_inlEntry T lg fun q hq => tableQueryLog_snd_dep T _ _ hq
  obtain ⟨g, hg, h, hh, q, hq, gg, hgg, hacc, hsat⟩ := hwin
  simp only at hg hh hq hgg hacc hsat
  rw [K.CW.congr _ _ _ _ htrT, htrH] at hg
  rw [K.CH.congr _ _ _ _ htrT, htrH] at hh
  rw [K.CQ.congr _ _ _ _ htrT, htrH] at hq
  rw [K.CG.congr _ _ _ _ htrT, htrH] at hgg
  have hcore := trace_core4 W K L (viewT T) π g h q gg (fun y hy => by
    simp only [L, hL, List.filterMap_append]
    refine List.mem_append_right _ (List.mem_append_left _ ?_)
    rw [filterMap_six]
    exact hy) hg hh hq hgg hacc hsat
  exact freshBad_kc4 W K T ∅ (lg.map Sigma.fst) (by rw [viewH_empty]; exact hcore)

/-- **The reduction's knowledge soundness with four real roots, union-bounded over the lists, in
mumbai's two-oracle model.** `knowledgeSoundness_list4` with Keccak-256 and Keccak-f[1600]
independent random oracles, the chain on Keccak-256, the openings any computation of both. -/
theorem knowledgeSoundness_list_kc4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    Pr{let z ← (simulateQ randomOracle (kcExperiment4 W A post)).run' ∅}[ListWins4 W K z] ≤
      ((Q + 6 + QV : ℕ) : ℝ≥0∞) *
        ((listFactor4 K.CW.bound K.CH.bound K.CQ.bound K.CG.bound : ℝ≥0∞) *
          (roundError P B : ℝ≥0∞) + 7 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls) (kcExperiment4 W A post)
    (Q + 6 + QV) (kcExperiment4_queryBound W A post Q QV hQ hV)
    (Set.range fun v : Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
    (Set.finite_range _) (ListWins4 W K) (kcBad4 W K) _ (fun S hS c t ht hcard => ?_)
    (fun T h => trace_kc4 W K A post T h)
  have hS' : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
    fun v => hS _ ⟨v, rfl⟩
  refine (prob_kcBad4 W K S hS' c t ht).trans ?_
  rw [add_comm]
  gcongr
  have : 7 * (cacheDom c).card + 6 ≤ 7 * (Q + 6 + QV) := by omega
  calc ((7 * (cacheDom c).card + 6 : ℕ) : ℝ≥0∞) ≤ ((7 * (Q + 6 + QV) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast this
    _ = 7 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) := by push_cast; ring

end ComposePcs
