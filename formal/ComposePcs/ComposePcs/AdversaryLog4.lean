-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/AdversaryLog.lean` of this repository (the experiment logging the
-- adversary's queries, the root-bad event, the trace through `ListCommit.stable`) to the four roots of
-- the EIP's PCS claims; its generic lemmas (`run_congr`, `freshBad_mono`, `before_append_of_mem`,
-- `subset_before_append`, `prEvent_bytes32_eq_le`) are reused as they are. The step from the whole
-- transcript to the adversary's follows leanerVM `mumbai`'s `Sound.prEvent_logged2_root_le`
-- (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0).
import ComposePcs.Openings4
import Compose.AdversaryLog

/-!
# The extractor reads the adversary's queries only (four roots)

As `Compose/AdversaryLog.lean`: the experiment logs **the adversary's Keccak-256 queries only**
(`advExperiment4`), and the extractor (`adversaryExtractor4`) is an explicit, computable function of
that log and the proof: climb the witness table's Merkle tree from the proof's `W` root through the
log's answers, and decode.

The verifier's queries can change what a root commits to only if one of their fresh answers is the
root itself, or a digest an earlier input refers to (`Coll4`). A fresh Keccak-256 answer after the
adversary's last query that is one of the **four** roots it announced is a bad query (`rootBad4`),
of probability at most `4/2^256` (`prob_rootBad4`). Without it, the candidates read off the
adversary's log are those read off the whole run's (`ListCommit.stable`), and the trace applies
(`trace_adv4`).

**`knowledgeSoundness_list_adv4`**, **`knowledgeSoundness_composed_adv4`**,
**`knowledgeSoundness_merkle_adv4`**: the bounds of `Openings4.lean`, the collision term
`7 (Q + 6 + QV)` becoming `8 (Q + 6 + QV)` (the root-bad terms, `4/2^256` a query, folded in).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace ComposePcs

open Compose QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol
  LeanVM.Semantics

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F] [SampleableType F]
variable {O β : Type} (ok : β → Prop)
variable {P : Params F} {B : P.Bounds} (W : Wire P B) {MH MQ MG : Type} (K : Commits4 B MH MQ MG)

/-! ## The experiment and the bad events -/

/-- **The experiment whose transcript is the adversary's**: the adversary, its Keccak-256 queries
and answers logged; then the chain and the openings, unlogged. -/
def advExperiment4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) :
    OracleComp KeccakCalls (Run4 F O β × Transcript) :=
  loggedKC A >>= fun pt => chainWith4 W hash256 pt.1.1 >>= fun ch => post pt.1 ch >>= fun b =>
    pure (⟨pt.1.1, pt.1.2, ch, b⟩, pt.2)

/-- **The extractor**: an explicit, computable function of the adversary's Keccak-256 query log
(inputs and answers) and the proof: the witness table's Merkle tree climbed down from the proof's
`W` root through the log's answers, then decoded. -/
def adversaryExtractor4 (c₁ : TableCode B.Msg₁) (log : Transcript) (π : RootProof4 F) :
    List B.Msg₁ :=
  c₁.dec (merkleWord (histOfTr log) (tableOfTr log) c₁.height c₁.leafLen π.rW)

/-- The four roots a proof announces. -/
def RootProof4.roots (π : RootProof4 F) : List Bytes32 := [π.rW, π.rH, π.rQ, π.rG]

/-- **A fresh Keccak-256 answer after the adversary's last query is one of its four roots.** -/
def rootBad4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  match d with
  | .inl x => (∀ q ∈ (tableQueryLog A T).map Sigma.fst, q ∈ H) ∧
      viewT T x ∈ (evalWithAnswerFn (QueryImpl.ofFn T) A).1.roots
  | .inr _ => False

/-- A bad query: `kcBad4`, or a fresh answer that is an announced root. -/
def advBad4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (H : Finset (List UInt8 ⊕ KeccakState)) (d : List UInt8 ⊕ KeccakState) (T : KTable) : Prop :=
  kcBad4 W K H d T ∨ rootBad4 A H d T

/-! ## The new bad event has probability `4/2^256` -/

theorem prob_rootBad4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (S : Finset (List UInt8 ⊕ KeccakState))
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[rootBad4 A
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤ (4 : ℝ≥0∞) / 2 ^ 256 := by
  classical
  set Hm := (cacheDom c).map (Function.Embedding.subtype (· ∈ S))
  obtain ⟨d, hd⟩ := t
  cases d with
  | inr s =>
    refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
    intro g h
    exact h
  | inl x =>
    have hagree : ∀ g g', ∀ q ∈ Hm, extendTable S (completeTable c g) q =
        extendTable S (completeTable c g') q := by
      intro g g' q hq
      obtain ⟨⟨q', hq'S⟩, hq'c, rfl⟩ := Finset.mem_map.mp hq
      rw [show (Function.Embedding.subtype (· ∈ S)) ⟨q', hq'S⟩ = (⟨q', hq'S⟩ : ↥S).1 from rfl,
        extendTable_subtype, extendTable_subtype]
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (mem_cacheDom.mp hq'c)
      simp [completeTable, hv]
    by_cases hex : ∃ g₀, ∀ q ∈ (tableQueryLog A (extendTable S (completeTable c g₀))).map
        Sigma.fst, q ∈ Hm
    · obtain ⟨g₀, hg₀⟩ := hex
      set π₀ := (evalWithAnswerFn (QueryImpl.ofFn (extendTable S (completeTable c g₀))) A).1
      have hx : x ∈ viewH S := mem_viewH.mpr hd
      refine (prEvent_mono _ _ (fun g => ∃ r ∈ π₀.roots, viewG S g ⟨x, hx⟩ = r) ?_).trans ?_
      · intro g hg
        obtain ⟨hq, hroot⟩ := hg
        have hc := run_congr A (extendTable S (completeTable c g₀))
          (extendTable S (completeTable c g)) fun q hq' => hagree g₀ g q (hg₀ q hq')
        have hfresh : viewT (extendTable S (completeTable c g)) x = viewG S g ⟨x, hx⟩ := by
          show toB (extendTable S (completeTable c g) (⟨.inl x, hd⟩ : ↥S).1) = _
          rw [extendTable_subtype]
          simp [completeTable, ht, viewG]
        rw [hfresh, ← hc.1] at hroot
        exact ⟨_, hroot, rfl⟩
      · rw [prEvent_view S (fun h => ∃ r ∈ π₀.roots, h ⟨x, hx⟩ = r)]
        refine (prEvent_exists_mem_le _ (fun r (h : ↥(viewH S) → Bytes32) => h ⟨x, hx⟩ = r)
          ((1 : ℝ≥0∞) / 2 ^ 256) π₀.roots fun r _ =>
            (prEvent_cell (⟨x, hx⟩ : ↥(viewH S)) (fun u : Bytes32 => u = r)).trans
              (prEvent_bytes32_eq_le r)).trans (le_of_eq ?_)
        simp only [RootProof4.roots, List.length_cons, List.length_nil]
        rw [mul_one_div]
        norm_num
    · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) bot_le
      intro g h
      exact hex ⟨g, h.1⟩

/-- **Each fresh query is bad with probability at most
`(7 |H| + 10) / 2^256 + listFactor4 · roundError`.** -/
theorem prob_advBad4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (S : Finset (List UInt8 ⊕ KeccakState))
    (hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S)
    (c : (OracleSpec.ofFn fun d : ↥S => KeccakCalls d.1).QueryCache) (t : ↥S) (ht : c t = none) :
    Pr{let g ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[advBad4 W K A
        ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
        (extendTable S (completeTable c g))] ≤
      ((7 * (cacheDom c).card + 10 : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        (listFactor4 K.CW.bound K.CH.bound K.CQ.bound K.CG.bound : ℝ≥0∞) *
          (roundError P B : ℝ≥0∞) := by
  refine (prEvent_or_le _ _ _).trans ((add_le_add (prob_kcBad4 W K S hS₀ c t ht)
    (prob_rootBad4 A S c t ht)).trans (le_of_eq ?_))
  rw [add_comm (((7 * (cacheDom c).card + 6 : ℕ) : ℝ≥0∞) / 2 ^ 256), add_assoc,
    ENNReal.div_add_div_same, add_comm]
  congr 2
  push_cast
  ring

/-! ## The trace -/

/-- The run: the adversary, then the chain and the openings. Its queries are those of
`TwoOracle4.lean`'s run. -/
theorem advExperiment4_run (A : OracleComp KeccakCalls (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) (T : KTable) :
    tableQueryLog (advExperiment4 W A post) T = tableQueryLog (kcRun4 W A post) T ∧
      evalWithAnswerFn (QueryImpl.ofFn T) (advExperiment4 W A post) =
        (evalWithAnswerFn (QueryImpl.ofFn T) (kcRun4 W A post),
          (tableQueryLog A T).filterMap inlEntry) := by
  have hl := log_loggedKC_run T A []
  have he := eval_loggedKC_run T A []
  rw [List.nil_append] at he
  constructor
  · simp only [advExperiment4, kcRun4, loggedKC, tableQueryLog_bind, tableQueryLog_pure, hl, he]
  · simp only [advExperiment4, kcRun4, loggedKC, evalWithAnswerFn_bind, evalWithAnswerFn_pure, he]

theorem advExperiment4_queryBound (A : OracleComp KeccakCalls (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    IsTotalQueryBound (advExperiment4 W A post) (Q + 6 + QV) := by
  have h : ∀ pt : (RootProof4 F × O) × Transcript, IsTotalQueryBound
      (chainWith4 W hash256 pt.1.1 >>= fun ch => post pt.1 ch >>= fun b =>
        (pure (⟨pt.1.1, pt.1.2, ch, b⟩, pt.2) : OracleComp KeccakCalls (Run4 F O β × Transcript)))
        (6 + (QV + 0)) :=
    fun pt => isTotalQueryBound_bind (chain4_queryBound_kc W pt.1.1) fun ch =>
      isTotalQueryBound_bind (hV pt.1 ch) fun b =>
        (trivial : IsTotalQueryBound (pure (⟨pt.1.1, pt.1.2, ch, b⟩, pt.2) :
          OracleComp KeccakCalls (Run4 F O β × Transcript)) 0)
  have := isTotalQueryBound_bind (isTotalQueryBound_loggedKC_run A Q [] hQ) h
  rwa [Nat.add_zero, ← Nat.add_assoc] at this

open Classical in
/-- **The trace, with the adversary's transcript**: on every table of both oracles, a run whose
candidates, read off the adversary's queries, satisfy the claims while the witness candidate fails
the relation asks a bad fresh query. -/
theorem trace_adv4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) (T : KTable)
    (hwin : ListWins4 W K (evalWithAnswerFn (QueryImpl.ofFn T) (advExperiment4 W A post))) :
    FreshBad (advBad4 W K A) T ∅
      ((tableQueryLog (advExperiment4 W A post) T).map Sigma.fst) := by
  obtain ⟨hlogE, hevalE⟩ := advExperiment4_run W A post T
  obtain ⟨hL, heval⟩ := kcRun4_run W A post T
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A
  set π := p.1
  rw [hlogE]
  rw [hevalE, heval] at hwin
  set lg := tableQueryLog (kcRun4 W A post) T
  set lA := tableQueryLog A T
  set Lk := lg.map Sigma.fst
  set L := Lk.filterMap Sum.getLeft?
  set LA := (lA.map Sigma.fst).filterMap Sum.getLeft?
  set tr : Transcript := lA.filterMap inlEntry
  -- The adversary's queries come first.
  have hLsplit : ∃ rest, L = LA ++ rest := by
    refine ⟨?_, ?_⟩
    swap
    · simp only [L, LA, hL, List.filterMap_append]
      exact rfl
  obtain ⟨rest, hLA⟩ := hLsplit
  have htrH : histOfTr tr = LA.toFinset := by
    simp only [histOfTr, tr, LA, map_fst_filterMap_inlEntry]
  have htrT : ∀ d ∈ histOfTr tr, tableOfTr tr d = viewT T d :=
    tableOfTr_inlEntry T lA fun q hq => tableQueryLog_snd_dep T _ _ hq
  obtain ⟨g, hg, h, hh, q, hq, gg, hgg, hacc, hsat⟩ := hwin
  simp only at hg hh hq hgg hacc hsat
  rw [K.CW.congr _ _ _ _ htrT, htrH] at hg
  rw [K.CH.congr _ _ _ _ htrT, htrH] at hh
  rw [K.CQ.congr _ _ _ _ htrT, htrH] at hq
  rw [K.CG.congr _ _ _ _ htrT, htrH] at hgg
  by_contra hnb
  have hk : ¬ FreshBad (kcBad4 W K) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hr : ¬ FreshBad (rootBad4 A) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBad4 W K) (viewT T) ∅ L := fun h =>
    hk (freshBad_kc4 W K T ∅ Lk (by rw [viewH_empty]; exact h))
  have hord := refers4_before W K hl
  -- No fresh answer after the adversary's queries is a root it announced.
  have hroot : ∀ w ∈ L, viewT T w ∈ π.roots → w ∈ LA := by
    intro w hw hwr
    by_contra hwA
    have hwk : Sum.inl w ∈ Lk := mem_filterMap_getLeft?.mp hw
    have hwA' : Sum.inl w ∉ lA.map Sigma.fst := fun h => hwA (mem_filterMap_getLeft?.mpr h)
    have nb := not_bad_before (rootBad4 A) T ∅ Lk hr (.inl w) hwk (Finset.notMem_empty _)
    rw [Finset.empty_union] at nb
    refine nb ⟨fun q hq => ?_, hwr⟩
    rw [hL]
    exact subset_before_append _ _ hwA' q hq
  -- So the candidates read off the adversary's queries are those read off the run's.
  have hstab : ∀ {M : Type} (C : ListCommit M) (r : Bytes32), r ∈ π.roots →
      C.cands LA.toFinset (viewT T) r = C.cands L.toFinset (viewT T) r := by
    intro M C r hr'
    refine (C.stable LA.toFinset L.toFinset (viewT T) r (fun w hw => ?_) (fun w hw hwr => ?_)
      (fun y hy w hw h => ?_)).symm
    · rw [hLA]
      exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hw))
    · exact List.mem_toFinset.mpr (hroot w (List.mem_toFinset.mp hw) (hwr ▸ hr'))
    · have hyA := List.mem_toFinset.mp hy
      have hyL : y ∈ L := by rw [hLA]; exact List.mem_append_left _ hyA
      have hb := hord w (List.mem_toFinset.mp hw) y hyL (Or.inl h)
      rw [hLA, before_append_of_mem LA rest hyA] at hb
      exact List.mem_toFinset.mpr (mem_of_mem_before LA w y hb)
  rw [hstab K.CW π.rW (by simp [RootProof4.roots])] at hg
  rw [hstab K.CH π.rH (by simp [RootProof4.roots])] at hh
  rw [hstab K.CQ π.rQ (by simp [RootProof4.roots])] at hq
  rw [hstab K.CG π.rG (by simp [RootProof4.roots])] at hgg
  refine hl (trace_core4 W K L (viewT T) π g h q gg (fun y hy => ?_) hg hh hq hgg hacc hsat)
  simp only [L, Lk, hL, List.filterMap_append]
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [filterMap_six]
  exact hy

/-! ## Knowledge soundness with the adversary's transcript -/

/-- **The four-root list argument, the candidates read off the adversary's queries only.** -/
theorem knowledgeSoundness_list_adv4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (post : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (post p ch) QV) :
    Pr{let z ← (simulateQ randomOracle (advExperiment4 W A post)).run' ∅}[ListWins4 W K z] ≤
      ((Q + 6 + QV : ℕ) : ℝ≥0∞) *
        ((listFactor4 K.CW.bound K.CH.bound K.CQ.bound K.CG.bound : ℝ≥0∞) *
          (roundError P B : ℝ≥0∞) + 8 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls) (advExperiment4 W A post)
    (Q + 6 + QV) (advExperiment4_queryBound W A post Q QV hQ hV)
    (Set.range fun v : Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
    (Set.finite_range _) (ListWins4 W K) (advBad4 W K A) _ (fun S hS c t ht hcard => ?_)
    (fun T h => trace_adv4 W K A post T h)
  have hS' : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
    fun v => hS _ ⟨v, rfl⟩
  refine (prob_advBad4 W K A S hS' c t ht).trans ?_
  rw [add_comm]
  gcongr
  have : 7 * (cacheDom c).card + 10 ≤ 8 * (Q + 6 + QV) := by omega
  calc ((7 * (cacheDom c).card + 10 : ℕ) : ℝ≥0∞) ≤ ((8 * (Q + 6 + QV) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast this
    _ = 8 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) := by push_cast; ring

/-- **Knowledge soundness of the four-root reduction composed with the openings, the extractor
reading the adversary's queries only**, in mumbai's two-oracle model. -/
theorem knowledgeSoundness_composed_adv4 (A : OracleComp KeccakCalls (RootProof4 F × O))
    (openings : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (advExperiment4 W A openings)).run' ∅}[
      WitnessDoomed4 ok K z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (advExperiment4 W A openings)).run' ∅}[
      WiringDoomed4 (P := P) ok z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (advExperiment4 W A openings)).run' ∅}[
      QuotientDoomed4 ok W K z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (advExperiment4 W A openings)).run' ∅}[
        Breaks4 ok W K z] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) *
        ((listFactor4 K.CW.bound K.CH.bound K.CQ.bound K.CG.bound : ℝ≥0∞) *
          (roundError P B : ℝ≥0∞) + 8 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
  prEvent_breaks4_le ok W K εW εσ εQ _ hW hσ hQd
    (knowledgeSoundness_list_adv4 W K A openings Q QV hQ hV)

/-- **The composed statement, the extractor an explicit function of the adversary's query log
and the proof** (`adversaryExtractor4`: `W`'s Merkle tree climbed through the adversary's answers,
then `cW`'s decoder), for list commitments whose `W` one is `cW`'s Merkle commitment: the openings'
terms plus `(Q + 6 + QV) (listFactor4 · roundError + 8 (Q + 6 + QV) / 2^256)`, where
`listFactor4 = L_W L_H L_Q L_G` once the parts' lists are non-empty (`listFactor4_eq`). -/
theorem knowledgeSoundness_merkle_adv4 (cW : TableCode B.Msg₁) (hK : K.CW = cW.commit)
    (A : OracleComp KeccakCalls (RootProof4 F × O))
    (openings : RootProof4 F × O → Chals F → OracleComp KeccakCalls β) (Q QV : ℕ)
    (hQ : IsTotalQueryBound A Q) (hV : ∀ p ch, IsTotalQueryBound (openings p ch) QV)
    (εW εσ εQ : ℝ≥0∞)
    (hW : Pr{let z ← (simulateQ randomOracle (advExperiment4 W A openings)).run' ∅}[
      WitnessDoomed4 ok K z] ≤ εW)
    (hσ : Pr{let z ← (simulateQ randomOracle (advExperiment4 W A openings)).run' ∅}[
      WiringDoomed4 (P := P) ok z] ≤ εσ)
    (hQd : Pr{let z ← (simulateQ randomOracle (advExperiment4 W A openings)).run' ∅}[
      QuotientDoomed4 ok W K z] ≤ εQ) :
    Pr{let z ← (simulateQ randomOracle (advExperiment4 W A openings)).run' ∅}[
        Accepted4 (P := P) ok z ∧ ∀ g ∈ adversaryExtractor4 cW z.2 z.1.proof,
          ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)] ≤
      εW + εσ + εQ + ((Q + 6 + QV : ℕ) : ℝ≥0∞) *
        ((listFactor4 cW.bound K.CH.bound K.CQ.bound K.CG.bound : ℝ≥0∞) *
          (roundError P B : ℝ≥0∞) + 8 * ((Q + 6 + QV : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  have hb : cW.bound = K.CW.bound := by rw [hK]; rfl
  have hev : ∀ z : Run4 F O β × Transcript, (Accepted4 (P := P) ok z ∧
      ∀ g ∈ adversaryExtractor4 cW z.2 z.1.proof,
        ¬ P.Sat (W.decode z.1.proof.stmt) (P.cells g.1)) ↔ Breaks4 ok W K z := by
    intro z
    unfold Breaks4 extractor4
    rw [hK]
    rfl
  simp only [hev, hb]
  exact knowledgeSoundness_composed_adv4 ok W K A openings Q QV hQ hV εW εσ εQ hW hσ hQd

end ComposePcs
