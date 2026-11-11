-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Follows `formal/Compose/Compose/GOps.lean` of this repository (`trace_whirUG`,
-- `knowledgeSoundness_listChainU_closed128G`) with `ListChainUDoom128S.lean`'s two generalisations
-- (`trace_whirP`, `knowledgeSoundness_listChainU_closed128S`): the setup's openings' stacks read off the proof,
-- and the protocol a function of the setup's output. What does not read them is reused from both files.
import Compose.GOps
import Compose.ListChainUDoom128S

/-!
# The chain with openings of any verifier, the setup's stacks and the protocol read off the setup

`GOps.lean`'s `knowledgeSoundness_listChainU_closed128G` (openings `GOp` of any verifier) fixes a setup
opening's stack (`Tgt.setup root q₀`) and the protocol in advance; `ListChainUDoom128S.lean`'s
`knowledgeSoundness_listChainU_closed128S` reads both off the setup, for `WhirOp`s. Here both at once, for π2's
verifier on the EIP's PCS claims (`formal/RecCompose`: π1's three openings, with no stack; π2's `W` and `Q`, round
openings; π2's setup opening, its stack read off the proof's roots):

* **a setup opening's stack** is optional and read off the proof (`stk o : Option (Pf → Column o.μ)`): `some f`,
  the setup committed `f π` under the opening's root (`GOp.OKP`) and the opening's claims hold of it
  (`GOp.SetupHoldsP`); `none`, nothing is concluded of the opening (its acceptance is required, its doom charged);
* **the protocol** is `R : σ → Piop U.K M`, read at the setup's output (`sOf`, `hsOf`; `hlabel`: no query of the
  setup is a label).

**`knowledgeSoundness_listChainU_closed128SG`**: the bound of `knowledgeSoundness_listChainU_closed128G`,

`Pr[DoomFG] + Pr[PairTr tag] + N (me + (nRf + 2) N / 2^256)`, `N = QS + Q + nQ + Σ_k QO_k`,

`me` bounding `maxErrK` at every output of the setup (`hme`); the doom term is `GOps.lean`'s, on
`expLG view (preU U view (withSetupG setup fix A₀)) ops`, which `prEvent_doomFG_le` bounds.

Helpers: `gop_okp_tableCode` (a round's opening, as `gop_ok_tableCode`), `gop_okp_none` (a setup opening without
a stack), `GOp.okp_of_ok` (`GOp.OK` with the stack, if any, the target's fixed one), `gop_okp_stack` (the stack's
setup with that stack, as `gop_ok_stack`), `GOp.setupHoldsP_of_setupHolds`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

section Defs

variable {F St M Pf : Type} [SampleableType F]

/-- **What the openings need, the setup's stacks read off the proof** (`GOp.OK`, as `WhirOp.OKP`): a round's
opening as `GOp.OK`'s; a setup opening with a stack `f` (`stk o = some f`), that the setup's queries make the word
under its root the honest encoding of `f` at the proof the setup fixes; a setup opening without one, nothing. -/
def GOp.OKP {σ : Type} (tc : ℕ → TableCode M) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (stk : (o : GOp Pf F M) → Option (Pf → Column o.μ)) (o : GOp Pf F M) : Prop :=
  match o.tgt with
  | .round i read => (tc i).height = rootHeight o.μ o.R ∧
      (tc i).leafLen = 8 * 2 ^ laneFold ∧
      (∀ w q, q ∈ Candidates o.μ o.R (code₀ o.μ o.R).thr
        (wordOfMerkle (tc i).height (2 ^ laneFold) w) → read q ∈ (tc i).dec w) ∧
      ∀ π ch q, o.holds π ch q → good i π ch (some (read q))
  | .setup root _ => ∀ f, stk o = some f →
      ∀ (T : KTable) (H : Hist) (p : Pf),
        (∀ x, Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst → x ∈ H) →
          Set.InjOn (viewT T) ↑H →
            ∃ word : Word, HonestWord o.μ o.R word
                (f (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup) p)) ∧
              ∀ v < 2 ^ rootHeight o.μ o.R,
                Rom.extract (ansOf H (viewT T))
                  (ofB (root (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup) p)))
                  (rootHeight o.μ o.R) (2 ^ laneFold) v = word v

/-- **A setup opening's stack satisfies its claims**, when it has one (nothing for a round's opening or a
setup opening without a stack). -/
def GOp.SetupHoldsP (stk : (o : GOp Pf F M) → Option (Pf → Column o.μ)) (o : GOp Pf F M) (π : Pf)
    (ch : List (List F)) : Prop :=
  match o.tgt with
  | .round _ _ => True
  | .setup _ _ => ∀ f, stk o = some f → o.holds π ch (f π)

end Defs

/-! ## Helpers: the openings' `OKP`, the run with its whole transcript -/

section Helpers

variable {F St M Pf : Type} [SampleableType F]

/-- **A round's opening with the computable decoder** (`gop_ok_tableCode`): `GOp.OKP` holds once a table its
claims hold of (as the layout reads it) is `good`, whatever the stacks. -/
theorem gop_okp_tableCode {σ : Type} (L : Layout) (R : ℕ) (adm : Whir.Admissible L.logN R)
    (holds : Pf → List (List F) → Column L.logN → Prop)
    (ver : Digest → Pf → List (List F) → OracleComp KeccakCalls Bool) (QO : ℕ)
    (hq : ∀ r π ch, IsTotalQueryBound (ver r π ch) QO) (hd : ∀ r π ch, LeanVM.Rpm.DuplexVm (ver r π ch) [])
    (i : ℕ) (rd : Tab L → M) (tc : ℕ → TableCode M) (htc : tc i = tableCode L R adm rd)
    (good : ℕ → Pf → List (List F) → Option M → Prop)
    (hg : ∀ π ch q, holds π ch q → good i π ch (some (rd (tabOf L q))))
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (stk : (o : GOp Pf F M) → Option (Pf → Column o.μ)) :
    GOp.OKP tc good setup fix stk
      (⟨L.logN, R, adm, holds, ver, QO, hq, hd, .round i (fun q => rd (tabOf L q))⟩ : GOp Pf F M) :=
  gop_ok_tableCode L R adm holds ver QO hq hd i rd tc htc good hg setup fix

/-- **A setup opening without a stack**: nothing to show. -/
theorem gop_okp_none {σ : Type} (tc : ℕ → TableCode M) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (stk : (o : GOp Pf F M) → Option (Pf → Column o.μ)) (o : GOp Pf F M) (root : Pf → Bytes32)
    (q₀ : Column o.μ) (htg : o.tgt = .setup root q₀) (hn : stk o = none) :
    GOp.OKP tc good setup fix stk o := by
  unfold GOp.OKP
  rcases h : o.tgt with ⟨i, rd⟩ | ⟨root', q₀'⟩
  · rw [htg] at h
    exact absurd h (by simp)
  · intro f hf
    rw [hn] at hf
    exact absurd hf (by simp)

/-- **`GOp.OK` gives `GOp.OKP`** when a setup opening's stack, if any, is its target's fixed one. -/
theorem GOp.okp_of_ok {σ : Type} (tc : ℕ → TableCode M) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (stk : (o : GOp Pf F M) → Option (Pf → Column o.μ)) (o : GOp Pf F M)
    (h : GOp.OK tc good setup fix o)
    (hstk : ∀ root q₀, o.tgt = .setup root q₀ → ∀ f, stk o = some f → ∀ π, f π = q₀) :
    GOp.OKP tc good setup fix stk o := by
  unfold GOp.OKP
  unfold GOp.OK at h
  rcases htg : o.tgt with ⟨i, rd⟩ | ⟨root, q₀⟩
  · rw [htg] at h
    exact h
  · rw [htg] at h
    obtain ⟨word, hhon, hsw⟩ := h
    intro f hf T H p hsub hinj
    refine ⟨word, ?_, hsw T H p hsub hinj⟩
    rw [hstk root q₀ htg f hf]
    exact hhon

/-- **A setup opening of the stack's setup** (`stackSetupS`, as `gop_ok_stack`), its stack, if any, the setup's
(`hstk`): `GOp.OKP` holds when the proof carries the setup's root. -/
theorem gop_okp_stack (S : WhirShape) (holds : Pf → List (List F) → Column S.L.logN → Prop)
    (ver : Digest → Pf → List (List F) → OracleComp KeccakCalls Bool) (QO : ℕ)
    (hq : ∀ r π ch, IsTotalQueryBound (ver r π ch) QO) (hd : ∀ r π ch, LeanVM.Rpm.DuplexVm (ver r π ch) [])
    (root : Pf → Bytes32) (q₀ : Column S.L.logN) (tc : ℕ → TableCode M)
    (good : ℕ → Pf → List (List F) → Option M → Prop) (fix : Bytes32 → Pf → Pf)
    (hfix : ∀ s p, root (fix s p) = s) (stk : (o : GOp Pf F M) → Option (Pf → Column o.μ))
    (hstk : ∀ f, stk ⟨S.L.logN, S.R, S.adm, holds, ver, QO, hq, hd, .setup root q₀⟩ = some f →
      ∀ π, f π = q₀) :
    GOp.OKP tc good (stackSetupS S q₀) fix stk
      (⟨S.L.logN, S.R, S.adm, holds, ver, QO, hq, hd, .setup root q₀⟩ : GOp Pf F M) :=
  GOp.okp_of_ok tc good _ fix stk _ (gop_ok_stack S holds ver QO hq hd root q₀ tc good fix hfix)
    fun _ _ h f hf π => by
      cases h
      exact hstk f hf π

/-- **`GOp.SetupHolds` gives `GOp.SetupHoldsP`** when a setup opening's stack, if any, is its target's fixed
one. -/
theorem GOp.setupHoldsP_of_setupHolds (stk : (o : GOp Pf F M) → Option (Pf → Column o.μ))
    (o : GOp Pf F M) (π : Pf) (ch : List (List F)) (h : GOp.SetupHolds o π ch)
    (hstk : ∀ root q₀, o.tgt = .setup root q₀ → ∀ f, stk o = some f → ∀ π, f π = q₀) :
    GOp.SetupHoldsP stk o π ch := by
  unfold GOp.SetupHoldsP
  unfold GOp.SetupHolds at h
  rcases htg : o.tgt with ⟨i, rd⟩ | ⟨root, q₀⟩
  · trivial
  · rw [htg] at h
    intro f hf
    rw [hstk root q₀ htg f hf]
    exact h

variable (U : ChainSpecU F St) (view : Pf → St × List (RMsg F))

/-- The run with its whole transcript (`expLG`), its proof: the adversary's. -/
theorem expLG_eval_proof (A : OracleComp KeccakCalls Pf) (ops : List (GOp Pf F M)) (T : KTable) :
    (evalWithAnswerFn (QueryImpl.ofFn T) (expLG view (preU U view A) ops)).1.1.1 =
      evalWithAnswerFn (QueryImpl.ofFn T) A := by
  unfold expLG
  rw [(run_logged _ T).2, evalWithAnswerFn_bind, evalWithAnswerFn_map, (preU_run U view A T).2]
  rfl

/-- The run with its whole transcript (`expLG`) asks the setup's queries first. -/
theorem expLG_log_setup {σ : Type} (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A₀ : σ → OracleComp KeccakCalls Pf) (ops : List (GOp Pf F M)) (T : KTable) :
    ∃ rest, (tableQueryLog (expLG view (preU U view (withSetupG setup fix A₀)) ops) T).map
        Sigma.fst = (tableQueryLog setup T).map Sigma.fst ++ rest := by
  unfold expLG
  rw [(run_logged _ T).1, tableQueryLog_bind, (preU_run U view _ T).1,
    (withSetupG_run setup fix A₀ T).1]
  exact exists_map_append4 Sigma.fst _ _ _ _

end Helpers

/-! ## The trace -/

section Trace

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]
variable (U : ChainSpecU F St) (R : Piop U.K M) (view : Pf → St × List (RMsg F))

open Classical in
/-- **The trace, openings of any verifier, the setup's stacks read off the proof** (`trace_whirUG` with
`GOp.OKP` and `GOp.SetupHoldsP` for `GOp.OK` and `GOp.SetupHolds`, as `trace_whirP`). -/
theorem trace_whirPG {σ : Type} (ops : List (GOp Pf F M)) (tc : ℕ → TableCode M)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (stk : (o : GOp Pf F M) → Option (Pf → Column o.μ))
    (A₀ : σ → OracleComp KeccakCalls Pf)
    (hok : ∀ o ∈ ops, GOp.OKP tc good setup fix stk o)
    (hcov : ∀ i < U.K.rounds.length, (U.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, GOp.SetupHoldsP stk o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll U.K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = U.K.rounds.length →
      (∀ i (h : i < cs.length), (U.K.spec i).root → good i π ch cs[i]) →
      (∀ i (h : i < cs.length), (U.K.spec i).root = false → cs[i] = none) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (tag : List UInt8) (T : KTable)
    (hlabT : ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG setup fix A₀) T).map Sigma.fst ∧
      (U.label (view (evalWithAnswerFn (QueryImpl.ofFn T) (withSetupG setup fix A₀))).1).take 32 =
        tag ++ (viewT T w).toList.take (32 - tag.length))
    (hev : BreaksOK U.K (fun i => (tc i).commit) R view check
        (fun bs => ∀ k < ops.length, bs.getD k false = true)
        (evalWithAnswerFn (QueryImpl.ofFn T)
          (expLG view (preU U view (withSetupG setup fix A₀)) ops)).1 ∧
      ¬ DoomFG view ops (evalWithAnswerFn (QueryImpl.ofFn T)
          (expLG view (preU U view (withSetupG setup fix A₀)) ops)) ∧
      ¬ PairTr tag (evalWithAnswerFn (QueryImpl.ofFn T)
          (expLG view (preU U view (withSetupG setup fix A₀)) ops)).2) :
    FreshBad (advBadU' U (fun i => (tc i).commit) R view (withSetupG setup fix A₀)) T ∅
      ((tableQueryLog (expLG view (preU U view (withSetupG setup fix A₀)) ops) T).map
        Sigma.fst) := by
  -- The run's parts, against the table.
  obtain ⟨hsl, hse⟩ := withSetupG_run setup fix A₀ T
  obtain ⟨hpl, hpe⟩ := preU_run U view (withSetupG setup fix A₀) T
  set A := withSetupG setup fix A₀ with hAdef
  set CC : ℕ → ListCommit M := fun i => (tc i).commit with hCC
  set p := evalWithAnswerFn (QueryImpl.ofFn T) A with hp
  set ch := evalWithAnswerFn (QueryImpl.ofFn T) (U.chain hash256 (view p).1 (view p).2) with hch
  set lA := tableQueryLog A T with hlA
  set lC := tableQueryLog (U.chain hash256 (view p).1 (view p).2) T with hlC
  set lO := tableQueryLog (gopsRun view ops p ch) T with hlO
  set bs := evalWithAnswerFn (QueryImpl.ofFn T) (gopsRun view ops p ch) with hbs
  set tA : Transcript := lA.filterMap inlEntry with htA
  set Y := preU U view A >>= fun x => opsOut x <$> gopsRun view ops x.1 x.2.1 with hY
  have hYl : tableQueryLog Y T = (lA ++ lC) ++ lO := by
    rw [hY, tableQueryLog_bind, tableQueryLog_map, hpl, hpe]
  have hYe : evalWithAnswerFn (QueryImpl.ofFn T) Y = ((p, (ch, bs)), tA) := by
    rw [hY, evalWithAnswerFn_bind, evalWithAnswerFn_map, hpe]
    rfl
  obtain ⟨hLl, hLe⟩ := run_logged Y T
  have hlogL : tableQueryLog (expLG view (preU U view A) ops) T = (lA ++ lC) ++ lO := by
    rw [← hYl]
    exact hLl
  have hevalL : evalWithAnswerFn (QueryImpl.ofFn T) (expLG view (preU U view A) ops) =
      (((p, (ch, bs)), tA), ((lA ++ lC) ++ lO).filterMap inlEntry) := by
    rw [← hYl, ← hYe]
    exact hLe
  have hYU : Y = expU U view A (gopsRun view ops) := (expU_eqG view U A ops).symm
  have hlogU : tableQueryLog (expU U view A (gopsRun view ops)) T = (lA ++ lC) ++ lO := by
    rw [← hYU]
    exact hYl
  set zK := evalWithAnswerFn (QueryImpl.ofFn T) (expU U view A (gopsRun view ops)) with hzK
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
  have hBK : BreaksOK U.K CC R view check (fun bs => ∀ k < ops.length, bs.getD k false = true)
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
  have hk : ¬ FreshBad (kcBadU' U CC R) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inl h') T ∅ Lk h)
  have hr : ¬ FreshBad (rootBadK U.K view A) T ∅ Lk := fun h =>
    hnb (freshBad_mono (fun _ _ _ h' => Or.inr h') T ∅ Lk h)
  have hl : ¬ FreshBad (listBadU' U CC R) (viewT T) ∅ L := fun h =>
    hk (freshBad_kcU' U CC R T ∅ Lk (by rw [viewH_empty]; exact h))
  have hord := rf_beforeU' hl
  have hinj : Set.InjOn (viewT T) ↑L.toFinset := injOn_of_not_freshBadU' hl
  have hLk : Lk = lA.map Sigma.fst ++ ((lC ++ lO).map Sigma.fst) := by
    rw [hLkdef]
    simp only [List.map_append, List.append_assoc]
  obtain ⟨rest, hLA⟩ : ∃ rest, L = LA ++ rest :=
    ⟨_, by rw [hLdef, hLk, List.filterMap_append]⟩
  -- No fresh answer after the adversary's queries is a root it announced.
  have hroot : ∀ w ∈ L, viewT T w ∈ U.K.rootsK (view p).2 → w ∈ LA := by
    intro w hw hwr
    by_contra hwA
    have hwk : Sum.inl w ∈ Lk := mem_filterMap_getLeft?.mp hw
    have hwA' : Sum.inl w ∉ lA.map Sigma.fst := fun h => hwA (mem_filterMap_getLeft?.mpr h)
    have nb := not_bad_before (rootBadK U.K view A) T ∅ Lk hr (.inl w) hwk
      (Finset.notMem_empty _)
    rw [Finset.empty_union] at nb
    refine nb ⟨fun q hq => ?_, hwr⟩
    rw [hLk]
    exact subset_before_append _ _ hwA' q hq
  -- A history between the adversary's and the run's reads the adversary's word.
  have hstab : ∀ (H : List (List UInt8)), (∀ y ∈ LA, y ∈ H) → (∀ y ∈ H, y ∈ L) →
      ∀ r ∈ U.K.rootsK (view p).2, ∀ ht ℓ,
        merkleWord H.toFinset (viewT T) ht ℓ r = merkleWord LA.toFinset (viewT T) ht ℓ r := by
    intro H hAH hHL r hr' ht ℓ
    refine merkleWord_stable (H := LA.toFinset) (H' := H.toFinset) (T := viewT T) (r := r)
      (fun y hy => List.mem_toFinset.mpr (hAH y (List.mem_toFinset.mp hy)))
      (fun w hw hwr => List.mem_toFinset.mpr
        (hroot w (hHL w (List.mem_toFinset.mp hw)) (hwr ▸ hr')))
      (fun y hy w hw h => ?_) ht ℓ
    have hyA := List.mem_toFinset.mp hy
    have hyL : y ∈ L := by rw [hLA]; exact List.mem_append_left _ hyA
    have hb := hord w (hHL w (List.mem_toFinset.mp hw)) y hyL (U.refers_rf _ _ h)
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
  have hD : ∀ i < U.K.rounds.length, (U.K.spec i).root →
      ¬ DoomK CC view (gopW ops check good goodS) i zK := by
    intro i hi hri hDK
    obtain ⟨o, hoops, rd, htgt⟩ := hcov i hi hri
    obtain ⟨m, hm, ho⟩ := List.mem_iff_getElem.mp hoops
    obtain ⟨q, hq, hqc⟩ := hcand m hm o ho
    have hokO : GOp.OKP tc good setup fix stk o := hok o hoops
    obtain ⟨r, hmr, hrr⟩ := exists_root_of_fits U.K hfit' i hi hri
    unfold GOp.OKP at hokO
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
  -- Every setup opening's stack, when it has one, satisfies its claims.
  have hSH : ∀ o ∈ ops, GOp.SetupHoldsP stk o p ch := by
    intro o hoops
    obtain ⟨m, hm, ho⟩ := List.mem_iff_getElem.mp hoops
    obtain ⟨q, hq, hqc⟩ := hcand m hm o ho
    have hokO : GOp.OKP tc good setup fix stk o := hok o hoops
    unfold GOp.SetupHoldsP
    unfold GOp.OKP at hokO
    rcases htg : o.tgt with ⟨i, rd⟩ | ⟨root, q₀⟩
    · trivial
    · intro f hf
      rw [htg] at hokO
      have hsub : ∀ x, Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst →
          x ∈ L.toFinset := by
        intro x hx
        refine List.mem_toFinset.mpr (hLAL x (mem_filterMap_getLeft?.mpr ?_))
        rw [hsl, List.map_append]
        exact List.mem_append_left _ hx
      obtain ⟨word, hhon, hsw⟩ := hokO f hf T L.toFinset
        (evalWithAnswerFn (QueryImpl.ofFn T) (A₀ (evalWithAnswerFn (QueryImpl.ofFn T) setup)))
        hsub hinj
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
        (W' := word) fun v hv => hsw v hv
      rw [hword] at hq
      have hq₀ := candidates_honest o.adm hhon hq
      subst hq₀
      rw [← hse] at hqc
      exact hqc
  have hgS : goodS p ch := hS p ch hSH
  -- The seed: no answer of the run is the label's first 32 bytes, else a pair.
  have hseed : ∀ z ∈ ((tableQueryLog (expU U view A (gopsRun view ops)) T).map
      Sigma.fst).filterMap Sum.getLeft?,
      (viewT T z).toList ≠ (U.label (view (evalWithAnswerFn (QueryImpl.ofFn T) A)).1).take 32 := by
    obtain ⟨w, hwA, hw⟩ := hlabT
    intro z hz hzl
    rw [hlogU] at hz
    refine hnp ⟨(z, viewT T z), mem_filterMap_inlEntry T _ hsnd (mem_filterMap_getLeft?.mp hz),
      (w, viewT T w), mem_filterMap_inlEntry T _ hsnd ?_, ?_⟩
    · rw [List.map_append, List.map_append]
      exact List.mem_append_left _ (List.mem_append_left _ hwA)
    · exact hzl.trans hw
  -- The list game, then a bad fresh query.
  have hBK' := breaksK_of_breaksOKG U.K CC R view ops check good goodS zK hBK
  rcases breaksU_imp U.K CC R view (gopW ops check good goodS) (fun π ch' _ h => hfit π ch' h)
      (fun π ch' _ cs h hl' hg hn hs => hlink π ch' cs h hl' hg hn hs) zK hBK' with
    ⟨i, hi, hri, hDK⟩ | hDS | hwin
  · exact hD i hi hri hDK
  · obtain ⟨-, hng⟩ := hDS
    refine hng ?_
    show goodS zK.1.1 zK.1.2.1
    rw [hK11, hK121]
    exact hgS
  · have := trace_advU' U CC R view A (gopsRun view ops) T hseed hwin
    rw [hlogU] at this
    exact hnb this
end Trace

/-! ## Knowledge soundness, the protocol read off the setup -/

section Closed

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]
variable (U : ChainSpecU F St) (view : Pf → St × List (RMsg F))

/-- **Knowledge soundness of the chain with openings of any verifier, the setup's stacks and the protocol read
off the setup** (`knowledgeSoundness_listChainU_closed128G` with `R : σ → Piop`, read at the setup's output
`sOf π`, and `GOp.OKP`, as `knowledgeSoundness_listChainU_closed128S`): the verifier accepts while no candidate of
round `0`'s root read off the adversary's (and the setup's) queries satisfies the first round's state of the
protocol at the setup's output with probability at most

`Pr[DoomFG] + Pr[PairTr tag] + N (me + (nRf + 2) N / 2^256)`, `N = QS + Q + nQ + Σ_k QO_k`,

`me` bounding `maxErrK` at every output of the setup, when no query of the setup is a label (`hlabel`). -/
theorem knowledgeSoundness_listChainU_closed128SG {σ : Type} [Inhabited σ] (R : σ → Piop U.K M)
    (sOf : Pf → σ) (ops : List (GOp Pf F M)) (tc : ℕ → TableCode M)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (stk : (o : GOp Pf F M) → Option (Pf → Column o.μ))
    (A₀ : σ → OracleComp KeccakCalls Pf)
    (QS Q : ℕ) (hSq : IsTotalQueryBound setup QS) (hQ : ∀ s, IsTotalQueryBound (A₀ s) Q)
    (hsOf : ∀ s p, sOf (fix s p) = s)
    (hok : ∀ o ∈ ops, GOp.OKP tc good setup fix stk o)
    (hcov : ∀ i < U.K.rounds.length, (U.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, GOp.SetupHoldsP stk o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll U.K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = U.K.rounds.length →
      (∀ i (h : i < cs.length), (U.K.spec i).root → good i π ch cs[i]) →
      (∀ i (h : i < cs.length), (U.K.spec i).root = false → cs[i] = none) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ (R (sOf π)).post (view π).1 p m c)
    (hlabel : ∀ (T : KTable) (x : List UInt8),
      Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst → ∀ s, x ≠ U.label s)
    (tag : List UInt8)
    (hlab : ∀ T : KTable, ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG setup fix A₀) T).map
        Sigma.fst ∧
      (U.label (view (evalWithAnswerFn (QueryImpl.ofFn T) (withSetupG setup fix A₀))).1).take 32 =
        tag ++ (viewT T w).toList.take (32 - tag.length))
    (me : ℝ≥0∞) (hme : ∀ s, maxErrK U.K (fun i => (tc i).commit) (R s) ≤ me) :
    Pr{let z ← (simulateQ randomOracle
        (expU U view (withSetupG setup fix A₀) (gopsRun view ops))).run' ∅}[
        BreaksOK U.K (fun i => (tc i).commit) (R (sOf z.1.1)) view check
          (fun bs => ∀ k < ops.length, bs.getD k false = true) z] ≤
      Pr{let z ← (simulateQ randomOracle
          (expLG view (preU U view (withSetupG setup fix A₀)) ops)).run' ∅}[DoomFG view ops z] +
      Pr{let z ← (simulateQ randomOracle
          (expLG view (preU U view (withSetupG setup fix A₀)) ops)).run' ∅}[PairTr tag z.2] +
      ((QS + Q + U.K.nQ + (ops.map fun o => o.QO).sum : ℕ) : ℝ≥0∞) *
        (me + (((U.nRf + 2) * (QS + Q + U.K.nQ + (ops.map fun o => o.QO).sum) : ℕ) : ℝ≥0∞) /
            2 ^ 256) := by
  classical
  set A := withSetupG setup fix A₀ with hAdef
  have hA : IsTotalQueryBound A (QS + Q) :=
    isTotalQueryBound_withSetupG setup fix A₀ QS Q hSq hQ
  set CC : ℕ → ListCommit M := fun i => (tc i).commit with hCC
  set accL : List Bool → Prop := fun bs => ∀ k < ops.length, bs.getD k false = true with haccL
  set N := QS + Q + U.K.nQ + (ops.map fun o => o.QO).sum with hN
  -- The event on the run with its whole transcript.
  have h1 : Pr{let z ← (simulateQ randomOracle (expU U view A (gopsRun view ops))).run' ∅}[
        BreaksOK U.K CC (R (sOf z.1.1)) view check accL z] =
      Pr{let z ← (simulateQ randomOracle (expLG view (preU U view A) ops)).run' ∅}[
        BreaksOK U.K CC (R (sOf z.1.1.1)) view check accL z.1] := by
    rw [expLG, prEvent_run'_loggedKC _ [] ∅
      (fun w => BreaksOK U.K CC (R (sOf w.1.1)) view check accL w), expU_eqG]
  rw [h1]
  set mx := (simulateQ randomOracle (expLG view (preU U view A) ops)).run' ∅ with hmx
  refine (prEvent_mono mx _ (fun z => DoomFG view ops z ∨ PairTr tag z.2 ∨
    (BreaksOK U.K CC (R (sOf z.1.1.1)) view check accL z.1 ∧ ¬ DoomFG view ops z ∧
      ¬ PairTr tag z.2)) fun z h => ?_).trans ((prEvent_or_le _ _ _).trans ?_)
  · by_cases hd : DoomFG view ops z
    · exact Or.inl hd
    · by_cases hpt : PairTr tag z.2
      · exact Or.inr (Or.inl hpt)
      · exact Or.inr (Or.inr ⟨h, hd, hpt⟩)
  rw [add_assoc]
  refine add_le_add le_rfl ((prEvent_or_le _ _ _).trans (add_le_add le_rfl ?_))
  refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls) (expLG view (preU U view A) ops)
    N (isTotalQueryBound_expLG view (preU U view A) ops _ (isTotalQueryBound_preU U view A _ hA))
    (Set.range fun v : Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
    (Set.finite_range _) _ (fun H d T => advBadU' U CC (R (setupAt setup H T)) view A H d T) _
    (fun S hS' c t ht hcard => ?_) (fun T h => ?_)
  · -- Each fresh query: the setup's output read off the cache does not depend on the completion.
    have hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
      fun v => hS' _ ⟨v, rfl⟩
    have hagree : ∀ g g' : (d : ↥S) → KeccakCalls d.1,
        ∀ q ∈ (cacheDom c).map (Function.Embedding.subtype (· ∈ S)),
          extendTable S (completeTable c g) q = extendTable S (completeTable c g') q := by
      intro g g' q hq
      obtain ⟨d, hd, rfl⟩ := Finset.mem_map.mp hq
      obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp (mem_cacheDom.mp hd)
      show extendTable S (completeTable c g) d.1 = extendTable S (completeTable c g') d.1
      rw [extendTable_subtype, extendTable_subtype]
      simp only [completeTable, hu, Option.getD_some]
    rcases isEmpty_or_nonempty ((d : ↥S) → KeccakCalls d.1) with he | ⟨⟨g₀⟩⟩
    · exact le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _
        fun g _ => (IsEmpty.false g).elim)) bot_le
    set r₀ := setupAt setup ((cacheDom c).map (Function.Embedding.subtype (· ∈ S)))
      (extendTable S (completeTable c g₀)) with hr₀
    refine (prEvent_mono _ _ (fun g => advBadU' U CC (R r₀) view A
      ((cacheDom c).map (Function.Embedding.subtype (· ∈ S))) t.1
      (extendTable S (completeTable c g))) fun g hg => ?_).trans ?_
    · rw [hr₀, ← setupAt_congr setup _ _ _ (hagree g g₀)]
      exact hg
    refine (prob_advBadU' U CC (R r₀) view A S hS₀ c t ht).trans ?_
    have hk : U.K.rounds.length < U.K.nQ := by
      have := nSteps_ge_length U.K.rounds
      simp only [ChainSpec.nQ]
      omega
    have hNle : (cacheDom c).card + U.nRf * ((cacheDom c).card + 1) + U.K.rounds.length ≤
        (U.nRf + 2) * N := by
      have hc1 : (cacheDom c).card + 1 ≤ N := hcard
      have h2 : U.nRf * ((cacheDom c).card + 1) ≤ U.nRf * N := Nat.mul_le_mul_left _ hc1
      have h3 : U.K.rounds.length ≤ N := by omega
      nlinarith
    calc (((cacheDom c).card + U.nRf * ((cacheDom c).card + 1) + U.K.rounds.length : ℕ) :
          ℝ≥0∞) / 2 ^ 256 + maxErrK U.K CC (R r₀)
        ≤ (((U.nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256 + me :=
          add_le_add (ENNReal.div_le_div_right (Nat.cast_le.mpr hNle) _) (hme r₀)
      _ = me + (((U.nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256 := by ring
  · -- The trace, at the protocol of the setup's output against `T`.
    obtain ⟨hB, hnd, hnp⟩ := h
    set s₀ := evalWithAnswerFn (QueryImpl.ofFn T) setup with hs₀
    have hsp : sOf (evalWithAnswerFn (QueryImpl.ofFn T) (expLG view (preU U view A) ops)).1.1.1 =
        s₀ := by
      rw [expLG_eval_proof U view A ops T, hAdef, (withSetupG_run setup fix A₀ T).2, hsOf]
    rw [hsp] at hB
    have hfr := trace_whirPG U (R s₀) view ops tc (fun π ch => check π ch ∧ sOf π = s₀) good goodS
      setup fix stk A₀ hok hcov hS (fun π ch h => hfit π ch h.1)
      (fun π ch cs h hl hg hn hgS => by
        obtain ⟨p, m, c, he, hp⟩ := hlink π ch cs h.1 hl hg hn hgS
        refine ⟨p, m, c, he, ?_⟩
        rw [← h.2]
        exact hp)
      tag T (hlab T) ⟨⟨⟨hB.1, hsp⟩, hB.2.1, hB.2.2⟩, hnd, hnp⟩
    -- From the protocol at the setup's output to the one read off each history.
    obtain ⟨rest, hlog⟩ := expLG_log_setup U view setup fix A₀ ops T
    refine freshBad_transfer T _ ∅ hfr fun k hk hb => ?_
    rw [Finset.empty_union] at hb ⊢
    by_cases hkS : ((tableQueryLog setup T).map Sigma.fst).length ≤ k
    · -- The history holds the whole setup's log.
      have hsub : ∀ q ∈ (tableQueryLog setup T).map Sigma.fst,
          q ∈ (((tableQueryLog (expLG view (preU U view A) ops) T).map Sigma.fst).take
            k).toFinset := by
        intro q hq
        rw [List.mem_toFinset, hlog, List.take_append, List.take_of_length_le hkS]
        exact List.mem_append_left _ hq
      rw [setupAt_of_sub setup _ T hsub]
      exact hb
    · -- The history holds only the setup's queries: no label.
      refine advBadU'_of_noLabel U CC (R s₀) _ view A _ _ T (fun s hs => ?_) hb
      rw [List.mem_toFinset, hlog, List.take_append_of_le_length (by omega)] at hs
      exact hlabel T (U.label s) (List.mem_of_mem_take hs) s rfl
end Closed

end Compose

/-- info: 'Compose.trace_whirPG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.trace_whirPG

/-- info: 'Compose.knowledgeSoundness_listChainU_closed128SG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_listChainU_closed128SG
