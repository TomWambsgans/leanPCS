-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- `formal/Compose/Compose/ListChainKDoom.lean`'s `WhirOp` (and its `opsRun`, `WhirOp.OK`, `opW`),
-- `Final128Defs.lean`'s `expL`, `DoomF`, `ListChainUDoom128.lean`'s `trace_whirU'` and
-- `knowledgeSoundness_listChainU_closed128`, and `FirstDoom.lean`'s `prEvent_doomF_le`, step by step,
-- for openings given by any verifier: what they read of `opening::verify` is its query count, its
-- duplex discipline and its doom; here they are the opening's fields and a union hypothesis.
import Compose.ListChainUDoom128
import Compose.FirstDoom
import Compose.SeedPair
import Compose.Rpm

/-!
# The chain over any encoding with openings of any verifier

`WhirOp` fixes an opening's verifier to `opening::verify` (`ourVerifier L R`) on a layout. The EIP's PCS
claims (`crates/pcs_claim`, `WhirBridge.Pcs`) are opened by another verifier, with another seed and an
out-of-domain claim. Here an opening (`GOp`) is any verifier `ver r π ch` of the root it reads, the proof and the
challenges, at an admissible WHIR shape `(μ, R)`, with its query count `QO`, its duplex discipline and what its
claims say of a stack (`holds`); its **doom** (`GDoomed`) is `OpeningDoomed`'s: every candidate of the word under
its root, at level 0's Johnson threshold, violates `holds`.

* **`knowledgeSoundness_listChainU_closed128G`**: `ListChainUDoom128.lean`'s theorem, word for word, for such
  openings: the verifier accepts while no candidate of round `0`'s root read off the adversary's (and the
  setup's) queries satisfies the first round's state with probability at most
  `Pr[DoomFG] + Pr[PairTr tag] + N (maxErrK + (nRf + 2) N / 2^256)`, `N = QS + Q + nQ + Σ_k QO_k`.
* **`prEvent_doomFG_le`**: `FirstDoom.lean`'s, the union family a hypothesis (`GUnionSound`): if every adversary
  of `QA` queries that outputs an opening's index, a proof and challenges makes that opening accept while doomed
  with probability at most `bnd QA`, the doom at the run's end is at most `bnd (QX + Σ_k QO_k)`.
* `gop_ok_tableCode`, `gop_ok_stack`: `WhirOp.OK`'s two helpers.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics
open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open LeanVM.Protocol.Rom (romExperiment romExperiment_map romExperiment_eq)

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The openings -/

/-- **An opening of the verifier, by any verifier**: an admissible WHIR shape (the table's `μ` variables, rate
`2^-R`), what its claims say of a stack (`holds π ch`), its verifier of the root it reads (`ver r π ch`), its
query count `QO`, its duplex discipline, and what it opens. -/
structure GOp (Pf F M : Type) where
  μ : ℕ
  R : ℕ
  adm : Whir.Admissible μ R
  holds : Pf → List (List F) → Column μ → Prop
  ver : Digest → Pf → List (List F) → OracleComp KeccakCalls Bool
  QO : ℕ
  queries : ∀ r π ch, IsTotalQueryBound (ver r π ch) QO
  duplex : ∀ r π ch, LeanVM.Rpm.DuplexVm (ver r π ch) []
  tgt : Tgt Pf M μ

section Defs

variable {F St M Pf : Type} [SampleableType F]
variable (K : ChainSpec F St) (C : ℕ → ListCommit M) (R : Piop K M)
  (view : Pf → St × List (RMsg F))

/-- The root an opening reads: its round's, from the message the chain absorbed, or the setup's. -/
def GOp.root (o : GOp Pf F M) (π : Pf) : Bytes32 :=
  match o.tgt with
  | .round i _ => ((msgK view π i).1).getD (Vector.replicate 32 0)
  | .setup r _ => r π

/-- An opening's run: its verifier on the root it reads. -/
def GOp.run (o : GOp Pf F M) (π : Pf) (ch : List (List F)) : OracleComp KeccakCalls Bool :=
  o.ver (ofB (GOp.root view o π)) π ch

/-- **The verifier's openings**, one after the other: their verdicts. -/
def gopsRun : List (GOp Pf F M) → Pf → List (List F) → OracleComp KeccakCalls (List Bool)
  | [], _, _ => pure []
  | o :: os, π, ch => GOp.run view o π ch >>= fun b => (b :: ·) <$> gopsRun os π ch

/-- **An opening is doomed** in a cache: every candidate of the word extracted under its root, at level 0's
Johnson threshold, violates its claims. -/
def GDoomed (o : GOp Pf F M) (π : Pf) (ch : List (List F)) (cache : KeccakCalls.QueryCache) : Prop :=
  ∀ q ∈ Candidates o.μ o.R (code₀ o.μ o.R).thr
      (Rom.extract (fun x ↦ cache (.inl x)) (ofB (GOp.root view o π)) (rootHeight o.μ o.R) (2 ^ laneFold)),
    ¬ o.holds π ch q

/-- **What the openings need** (`WhirOp.OK`): a round's opening, that its root's decoder lists every candidate of
the word read back and that a candidate its claims hold of is `good`; a setup's opening, that the setup's queries
make the word under its root the honest encoding of its stack. -/
def GOp.OK {σ : Type} (tc : ℕ → TableCode M) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf) (o : GOp Pf F M) : Prop :=
  match o.tgt with
  | .round i read => (tc i).height = rootHeight o.μ o.R ∧
      (tc i).leafLen = 8 * 2 ^ laneFold ∧
      (∀ w q, q ∈ Candidates o.μ o.R (code₀ o.μ o.R).thr
        (wordOfMerkle (tc i).height (2 ^ laneFold) w) → read q ∈ (tc i).dec w) ∧
      ∀ π ch q, o.holds π ch q → good i π ch (some (read q))
  | .setup root q₀ => ∃ word : Word, HonestWord o.μ o.R word q₀ ∧
      ∀ (T : KTable) (H : Hist) (p : Pf),
        (∀ x, Sum.inl x ∈ (tableQueryLog setup T).map Sigma.fst → x ∈ H) →
          Set.InjOn (viewT T) ↑H → ∀ v < 2 ^ rootHeight o.μ o.R,
            Rom.extract (ansOf H (viewT T))
              (ofB (root (fix (evalWithAnswerFn (QueryImpl.ofFn T) setup) p)))
              (rootHeight o.μ o.R) (2 ^ laneFold) v = word v

/-- **A setup opening's stack satisfies its claims** (nothing for a round's opening). -/
def GOp.SetupHolds (o : GOp Pf F M) (π : Pf) (ch : List (List F)) : Prop :=
  match o.tgt with
  | .round _ _ => True
  | .setup _ q₀ => o.holds π ch q₀

/-- **The openings as `ListChainKComposed.lean`'s.** -/
def gopW (ops : List (GOp Pf F M)) (check : Pf → List (List F) → Prop)
    (good : ℕ → Pf → List (List F) → Option M → Prop) (goodS : Pf → List (List F) → Prop) :
    OpeningsK Pf F (List Bool) M where
  check π ch _ := check π ch
  acc _ _ _ bs := ∀ k < ops.length, bs.getD k false = true
  good := good
  accS _ _ bs := ∀ k < ops.length, bs.getD k false = true
  goodS := goodS

theorem breaksK_of_breaksOKG (ops : List (GOp Pf F M)) (check : Pf → List (List F) → Prop)
    (good : ℕ → Pf → List (List F) → Option M → Prop) (goodS : Pf → List (List F) → Prop)
    (z : OutK Pf F (List Bool))
    (h : BreaksOK K C R view check (fun bs => ∀ k < ops.length, bs.getD k false = true) z) :
    BreaksK K C R view (gopW ops check good goodS) z :=
  ⟨⟨h.1, fun _ _ _ => h.2.1, h.2.1⟩, h.2.2⟩

/-- The openings make at most `Σ_k QO_k` queries. -/
theorem isTotalQueryBound_gopsRun :
    ∀ (ops : List (GOp Pf F M)) (π : Pf) (ch : List (List F)),
      IsTotalQueryBound (gopsRun view ops π ch) (ops.map fun o => o.QO).sum
  | [], _, _ => trivial
  | o :: os, π, ch => by
    simp only [gopsRun, List.map_cons, List.sum_cons]
    exact isTotalQueryBound_bind (o.queries _ _ _) fun _ =>
      (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_gopsRun os π ch)

/-- **The openings follow the duplex discipline.** -/
theorem duplexVm_gopsRun : ∀ (ops : List (GOp Pf F M)) (π : Pf) (ch : List (List F)),
    LeanVM.Rpm.DuplexVm (gopsRun view ops π ch) []
  | [], _, _ => trivial
  | o :: os, π, ch => by
    refine LeanVM.Rpm.DuplexVm.bind (o.duplex _ _ _) fun b => ?_
    rw [map_eq_bind_pure_comp]
    exact LeanVM.Rpm.DuplexVm.bind (duplexVm_gopsRun os π ch) fun _ => trivial

/-- **The run with its whole Keccak-256 transcript**: `X`, then the openings, every Keccak-256 query
logged. -/
def expLG (X : OracleComp KeccakCalls (PreK Pf F)) (ops : List (GOp Pf F M)) :
    OracleComp KeccakCalls (OutK Pf F (List Bool) × Transcript) :=
  (simulateQ logImplKC (X >>= fun x => opsOut x <$> gopsRun view ops x.1 x.2.1)).run []

/-- **`expU` is the run before the openings (`preU`), then the openings.** -/
theorem expU_eqG (U : ChainSpecU F St) (A : OracleComp KeccakCalls Pf) (ops : List (GOp Pf F M)) :
    expU U view A (gopsRun view ops) =
      preU U view A >>= fun x => opsOut x <$> gopsRun view ops x.1 x.2.1 := by
  simp only [expU, verU, preU, opsOut, bind_assoc, pure_bind, map_eq_bind_pure_comp,
    Function.comp_def]

/-- **Some opening accepts while doomed at the end of the run.** -/
def DoomFG (ops : List (GOp Pf F M)) (z : OutK Pf F (List Bool) × Transcript) : Prop :=
  ∃ k, ∃ hk : k < ops.length, z.1.1.2.2.getD k false = true ∧
    GDoomed view ops[k] z.1.1.1 z.1.1.2.1 (cacheOfTr z.2)

/-- **The run with its whole transcript makes at most `QX + Σ_k QO_k` queries.** -/
theorem isTotalQueryBound_expLG (X : OracleComp KeccakCalls (PreK Pf F)) (ops : List (GOp Pf F M))
    (QX : ℕ) (hX : IsTotalQueryBound X QX) :
    IsTotalQueryBound (expLG view X ops) (QX + (ops.map fun o => o.QO).sum) := by
  unfold expLG
  exact isTotalQueryBound_loggedKC_run _ _ [] (isTotalQueryBound_bind hX fun x =>
    (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_gopsRun view ops x.1 x.2.1))

/-- **A pair of answers in the whole run's transcript**: at most `2 (QX + Σ_k QO_k)² / 2^256`. -/
theorem prEvent_pairTr_expLG_le (X : OracleComp KeccakCalls (PreK Pf F)) (ops : List (GOp Pf F M))
    (QX : ℕ) (hX : IsTotalQueryBound X QX) (tag : List UInt8) (htag : tag.length = 16) :
    Pr{let z ← (simulateQ randomOracle (expLG view X ops)).run' ∅}[PairTr tag z.2] ≤
      ((2 * (QX + (ops.map fun o => o.QO).sum) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold expLG
  exact prEvent_pairTr_le _ _ (isTotalQueryBound_bind hX fun x =>
    (isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_gopsRun view ops x.1 x.2.1))
    tag htag

end Defs

/-! ## The helpers -/

section Helpers

variable {F St M Pf : Type} [SampleableType F]

/-- **A round's opening with the computable decoder** (`tableCode` of a layout of the opening's shape):
`GOp.OK` holds once a table its claims hold of (as the layout reads it) is `good`. -/
theorem gop_ok_tableCode {σ : Type} (L : Layout) (R : ℕ) (adm : Whir.Admissible L.logN R)
    (holds : Pf → List (List F) → Column L.logN → Prop)
    (ver : Digest → Pf → List (List F) → OracleComp KeccakCalls Bool) (QO : ℕ)
    (hq : ∀ r π ch, IsTotalQueryBound (ver r π ch) QO) (hd : ∀ r π ch, LeanVM.Rpm.DuplexVm (ver r π ch) [])
    (i : ℕ) (rd : Tab L → M) (tc : ℕ → TableCode M) (htc : tc i = tableCode L R adm rd)
    (good : ℕ → Pf → List (List F) → Option M → Prop)
    (hg : ∀ π ch q, holds π ch q → good i π ch (some (rd (tabOf L q))))
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf) :
    GOp.OK tc good setup fix
      (⟨L.logN, R, adm, holds, ver, QO, hq, hd, .round i (fun q => rd (tabOf L q))⟩ : GOp Pf F M) := by
  unfold GOp.OK
  dsimp only
  rw [htc]
  exact ⟨rfl, rfl, fun w q hq => read_mem_tableCode_dec adm rd w q hq, fun π ch q h => hg π ch q h⟩

/-- **A setup opening of the stack's setup** (`stackSetupS`): `GOp.OK` holds when the proof carries the setup's
root. -/
theorem gop_ok_stack (S : WhirShape) (holds : Pf → List (List F) → Column S.L.logN → Prop)
    (ver : Digest → Pf → List (List F) → OracleComp KeccakCalls Bool) (QO : ℕ)
    (hq : ∀ r π ch, IsTotalQueryBound (ver r π ch) QO) (hd : ∀ r π ch, LeanVM.Rpm.DuplexVm (ver r π ch) [])
    (root : Pf → Bytes32) (q₀ : Column S.L.logN) (tc : ℕ → TableCode M)
    (good : ℕ → Pf → List (List F) → Option M → Prop) (fix : Bytes32 → Pf → Pf)
    (hfix : ∀ s p, root (fix s p) = s) :
    GOp.OK tc good (stackSetupS S q₀) fix
      (⟨S.L.logN, S.R, S.adm, holds, ver, QO, hq, hd, .setup root q₀⟩ : GOp Pf F M) := by
  refine ⟨LeanVM.Protocol.Whir.Complete.stackWord S.L.logN q₀, honest_stackWord _ _ q₀,
    fun T H p hsub hinj v hv => ?_⟩
  show Rom.extract (ansOf H (viewT T))
    (ofB (root (fix (evalWithAnswerFn (QueryImpl.ofFn T) (stackSetupS S q₀)) p)))
    (rootHeight S.L.logN S.R) (2 ^ laneFold) v = _
  rw [hfix]
  exact extract_wiringSetup _ _ _ (LeanVM.Protocol.Whir.Complete.wellShaped_stackWord _ q₀) T H
    hsub hinj v hv

end Helpers

/-! ## The trace of the run with its whole transcript -/

section Trace

variable {F St M Pf : Type} [SampleableType F] [Fintype F] [DecidableEq F]
variable (U : ChainSpecU F St) (R : Piop U.K M) (view : Pf → St × List (RMsg F))

open Classical in
/-- **The trace of the run with its whole transcript**: on every table of both oracles, a run that
breaks knowledge soundness while no opening is doomed at the end of the run (`DoomF`) and no two
answers of its transcript make a pair (`PairTr`) asks a bad fresh query, when the label's first 32
bytes are `tag ‖` the first bytes of an answer the adversary asked (`hlabT`). Doom read at the
run's end: an undoomed opening's candidate is read off the whole history `L`, whose word under a
root of the adversary is the adversary's (`hstab` at `H = L`). -/
theorem trace_whirUG {σ : Type} (ops : List (GOp Pf F M)) (tc : ℕ → TableCode M)
    (check : Pf → List (List F) → Prop) (good : ℕ → Pf → List (List F) → Option M → Prop)
    (goodS : Pf → List (List F) → Prop) (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A₀ : σ → OracleComp KeccakCalls Pf)
    (hok : ∀ o ∈ ops, GOp.OK tc good setup fix o)
    (hcov : ∀ i < U.K.rounds.length, (U.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, GOp.SetupHolds o π ch) → goodS π ch)
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
    have hokO : GOp.OK tc good setup fix o := hok o hoops
    obtain ⟨r, hmr, hrr⟩ := exists_root_of_fits U.K hfit' i hi hri
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

/-! ## Knowledge soundness, the seed separated by a pair of answers -/

/-- **Knowledge soundness of the chain over any encoding with WHIR openings, at `≥ 128` bits**
(`knowledgeSoundness_listChainU_closed` with no tag term and every opening's doom read at the end
of the run): the verifier accepts while no candidate of round `0`'s root read off the adversary's
(and the setup's) queries satisfies the first round's state with probability at most

`Pr[DoomF] + Pr[PairTr tag] + N (maxErrK + (nRf + 2) N / 2^256)`,
`N = QS + Q + nQ + Σ_k QO_k`,

the two events of the run with its whole Keccak-256 transcript (`expL`), when the label's first 32
bytes are `tag ‖` the first `32 − |tag|` bytes of an answer the adversary (or the setup) asked
(`hlab`). -/
theorem knowledgeSoundness_listChainU_closed128G {σ : Type} (ops : List (GOp Pf F M))
    (tc : ℕ → TableCode M) (check : Pf → List (List F) → Prop)
    (good : ℕ → Pf → List (List F) → Option M → Prop) (goodS : Pf → List (List F) → Prop)
    (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf) (A₀ : σ → OracleComp KeccakCalls Pf)
    (QS Q : ℕ) (hSq : IsTotalQueryBound setup QS) (hQ : ∀ s, IsTotalQueryBound (A₀ s) Q)
    (hok : ∀ o ∈ ops, GOp.OK tc good setup fix o)
    (hcov : ∀ i < U.K.rounds.length, (U.K.spec i).root → ∃ o ∈ ops, ∃ rd, o.tgt = .round i rd)
    (hS : ∀ π ch, (∀ o ∈ ops, GOp.SetupHolds o π ch) → goodS π ch)
    (hfit : ∀ π ch, check π ch → FitsAll U.K.rounds (view π).2)
    (hlink : ∀ π ch (cs : List (Option M)), check π ch → cs.length = U.K.rounds.length →
      (∀ i (h : i < cs.length), (U.K.spec i).root → good i π ch cs[i]) →
      (∀ i (h : i < cs.length), (U.K.spec i).root = false → cs[i] = none) → goodS π ch →
      ∃ p m c, opened cs (view π).2 ch = p ++ [(m, c)] ∧ R.post (view π).1 p m c)
    (tag : List UInt8)
    (hlab : ∀ T : KTable, ∃ w, Sum.inl w ∈ (tableQueryLog (withSetupG setup fix A₀) T).map
        Sigma.fst ∧
      (U.label (view (evalWithAnswerFn (QueryImpl.ofFn T) (withSetupG setup fix A₀))).1).take 32 =
        tag ++ (viewT T w).toList.take (32 - tag.length)) :
    Pr{let z ← (simulateQ randomOracle
        (expU U view (withSetupG setup fix A₀) (gopsRun view ops))).run' ∅}[
        BreaksOK U.K (fun i => (tc i).commit) R view check
          (fun bs => ∀ k < ops.length, bs.getD k false = true) z] ≤
      Pr{let z ← (simulateQ randomOracle
          (expLG view (preU U view (withSetupG setup fix A₀)) ops)).run' ∅}[DoomFG view ops z] +
      Pr{let z ← (simulateQ randomOracle
          (expLG view (preU U view (withSetupG setup fix A₀)) ops)).run' ∅}[PairTr tag z.2] +
      ((QS + Q + U.K.nQ + (ops.map fun o => o.QO).sum : ℕ) : ℝ≥0∞) *
        (maxErrK U.K (fun i => (tc i).commit) R +
          (((U.nRf + 2) * (QS + Q + U.K.nQ + (ops.map fun o => o.QO).sum) : ℕ) : ℝ≥0∞) /
            2 ^ 256) := by
  set A := withSetupG setup fix A₀ with hAdef
  have hA : IsTotalQueryBound A (QS + Q) :=
    isTotalQueryBound_withSetupG setup fix A₀ QS Q hSq hQ
  set CC : ℕ → ListCommit M := fun i => (tc i).commit with hCC
  set accL : List Bool → Prop := fun bs => ∀ k < ops.length, bs.getD k false = true with haccL
  set N := QS + Q + U.K.nQ + (ops.map fun o => o.QO).sum with hN
  -- The event on the run with its whole transcript.
  have h1 : Pr{let z ← (simulateQ randomOracle (expU U view A (gopsRun view ops))).run' ∅}[
        BreaksOK U.K CC R view check accL z] =
      Pr{let z ← (simulateQ randomOracle (expLG view (preU U view A) ops)).run' ∅}[
        BreaksOK U.K CC R view check accL z.1] := by
    rw [expLG, prEvent_run'_loggedKC _ [] ∅ (fun w => BreaksOK U.K CC R view check accL w),
      expU_eqG]
  rw [h1]
  set mx := (simulateQ randomOracle (expLG view (preU U view A) ops)).run' ∅ with hmx
  refine (prEvent_mono mx _ (fun z => DoomFG view ops z ∨ PairTr tag z.2 ∨
    (BreaksOK U.K CC R view check accL z.1 ∧ ¬ DoomFG view ops z ∧ ¬ PairTr tag z.2))
    fun z h => ?_).trans ((prEvent_or_le _ _ _).trans ?_)
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
    (Set.finite_range _) _ (advBadU' U CC R view A) _ (fun S hS' c t ht hcard => ?_)
    (fun T h => trace_whirUG U R view ops tc check good goodS setup fix A₀ hok hcov hS hfit
      hlink tag T (hlab T) h)
  have hS₀ : ∀ v : Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
    fun v => hS' _ ⟨v, rfl⟩
  refine (prob_advBadU' U CC R view A S hS₀ c t ht).trans ?_
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
        ℝ≥0∞) / 2 ^ 256 + maxErrK U.K CC R
      ≤ (((U.nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256 + maxErrK U.K CC R :=
        add_le_add (ENNReal.div_le_div_right (Nat.cast_le.mpr hNle) _) le_rfl
    _ = maxErrK U.K CC R + (((U.nRf + 2) * N : ℕ) : ℝ≥0∞) / 2 ^ 256 := by ring

end Trace

/-! ## The openings' doom at the run's end, charged once (`FirstDoom.lean`) -/

section First

variable {F St M Pf : Type} [SampleableType F]

/-- **Every opening replays at the openings' end**: on every outcome `(bs, c)` of the openings,
opening `k`'s run, from `c`, returns `bs[k]` without a fresh query. -/
theorem gopsRun_replayF (view : Pf → St × List (RMsg F)) :
    ∀ (ops : List (GOp Pf F M)) (π : Pf) (ch : List (List F)) (c₁ : KeccakCalls.QueryCache)
      (r : List Bool × KeccakCalls.QueryCache),
      r ∈ support ((simulateQ randomOracle (gopsRun view ops π ch)).run c₁) →
        ∀ k (hk : k < ops.length),
          (simulateQ randomOracle (GOp.run view ops[k] π ch)).run r.2 = pure (r.1.getD k false, r.2)
  | [], _, _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | o :: os, π, ch, c₁, r, hr, k, hk => by
    simp only [gopsRun] at hr
    rw [LeanVM.Protocol.Rom.run_simulateQ_bind, mem_support_bind_iff] at hr
    obtain ⟨p, hp, hr⟩ := hr
    rw [simulateQ_map, StateT.run_map, support_map] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    cases k with
    | zero =>
      exact (run_replay_of_mem_support _ _ _ hp).2 _ (run_replay_of_mem_support _ _ _ hr').1
    | succ k =>
      exact gopsRun_replayF view os π ch p.2 r' hr' k (by simpa using hk)

/-- **The run's outcome**: the cache's Keccak-256 answers are the transcript's, and every opening
replays at the run's end. -/
theorem expLG_replayF (view : Pf → St × List (RMsg F)) (X : OracleComp KeccakCalls (PreK Pf F))
    (ops : List (GOp Pf F M))
    (p : (OutK Pf F (List Bool) × Transcript) × KeccakCalls.QueryCache)
    (hp : p ∈ support ((simulateQ randomOracle (expLG view X ops)).run ∅)) :
    Consistent p.1.2 p.2 ∧ ∀ k (hk : k < ops.length),
      (simulateQ randomOracle (GOp.run view ops[k] p.1.1.1.1 p.1.1.1.2.1)).run p.2 =
          pure (p.1.1.1.2.2.getD k false, p.2) := by
  refine ⟨consistent_run_loggedKC _ [] ∅ consistent_nil p hp, ?_⟩
  obtain ⟨⟨z, tr⟩, c⟩ := p
  have hp' : (z, c) ∈ support ((simulateQ randomOracle
      (X >>= fun x ↦ opsOut x <$> gopsRun view ops x.1 x.2.1)).run ∅) := by
    rw [← map_run_loggedKC (X >>= fun x ↦ opsOut x <$> gopsRun view ops x.1 x.2.1) [] ∅,
      support_map]
    exact ⟨((z, tr), c), hp, rfl⟩
  rw [LeanVM.Protocol.Rom.run_simulateQ_bind, mem_support_bind_iff] at hp'
  obtain ⟨q, -, hq⟩ := hp'
  rw [simulateQ_map, StateT.run_map, support_map] at hq
  obtain ⟨r, hr, hqr⟩ := hq
  simp only [Prod.mk.injEq] at hqr
  obtain ⟨rfl, rfl⟩ := hqr
  intro k hk
  exact gopsRun_replayF view ops q.1.1 q.1.2.1 q.2 r hr k hk

/-- Opening `k` accepts while doomed at the run's end. -/
def GDoomAtEnd (view : Pf → St × List (RMsg F)) (ops : List (GOp Pf F M))
    (z : OutK Pf F (List Bool) × Transcript) (k : ℕ) : Prop :=
  ∃ hk : k < ops.length, z.1.1.2.2.getD k false = true ∧
    GDoomed view ops[k] z.1.1.1 z.1.1.2.1 (cacheOfTr z.2)

open Classical in
/-- **The first opening doomed at the run's end**, `0` if none. -/
noncomputable def gFirstDoom (view : Pf → St × List (RMsg F)) (ops : List (GOp Pf F M))
    (z : OutK Pf F (List Bool) × Transcript) : ℕ :=
  if h : ∃ k, GDoomAtEnd view ops z k then Nat.find h else 0

open Classical in
theorem gFirstDoom_lt (view : Pf → St × List (RMsg F)) {ops : List (GOp Pf F M)}
    (hne : ops ≠ []) (z : OutK Pf F (List Bool) × Transcript) :
    gFirstDoom view ops z < ops.length := by
  unfold gFirstDoom
  split
  · rename_i h
    obtain ⟨hk, -⟩ := Nat.find_spec h
    exact hk
  · cases ops with
    | nil => exact absurd rfl hne
    | cons o os => exact Nat.succ_pos _

open Classical in
theorem gDoomAtEnd_first (view : Pf → St × List (RMsg F)) (ops : List (GOp Pf F M))
    {z : OutK Pf F (List Bool) × Transcript} (h : DoomFG view ops z) :
    GDoomAtEnd view ops z (gFirstDoom view ops z) := by
  have h' : ∃ k, GDoomAtEnd view ops z k := h
  unfold gFirstDoom
  rw [dif_pos h']
  exact Nat.find_spec h'

/-- **The union of the openings**: a statement is an opening's index, a proof and challenges; its verifier is
that opening's run. -/
abbrev GUIn (ops : List (GOp Pf F M)) : Type := Fin ops.length × Pf × List (List F)

/-- The union's verifier. -/
def gUVer (view : Pf → St × List (RMsg F)) (ops : List (GOp Pf F M)) (w : GUIn ops) :
    OracleComp KeccakCalls Bool :=
  GOp.run view (ops.get w.1) w.2.1 w.2.2

/-- The union's event: the indexed opening doomed. -/
def GUDoomed (view : Pf → St × List (RMsg F)) (ops : List (GOp Pf F M)) (w : GUIn ops)
    (c : KeccakCalls.QueryCache) : Prop :=
  GDoomed view (ops.get w.1) w.2.1 w.2.2 c

/-- **The union is sound at the bound `bnd`**: an adversary of at most `QA` queries that outputs an opening's
index, a proof and challenges makes that opening accept while doomed with probability at most `bnd QA`. -/
def GUnionSound (view : Pf → St × List (RMsg F)) (ops : List (GOp Pf F M)) (bnd : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : OracleComp KeccakCalls (GUIn ops)) (QA : ℕ), IsTotalQueryBound A QA →
    Pr{let z ← romExperiment A (gUVer view ops)}[z.1.2 = true ∧ GUDoomed view ops z.1.1 z.2] ≤ bnd QA

/-- The union adversary's output: the first opening doomed at the run's end. -/
noncomputable def gPick (view : Pf → St × List (RMsg F)) (ops : List (GOp Pf F M)) (hne : ops ≠ [])
    (z : OutK Pf F (List Bool) × Transcript) : GUIn ops :=
  (⟨gFirstDoom view ops z, gFirstDoom_lt view hne z⟩, z.1.1.1, z.1.1.2.1)

/-- **The doom at the run's end is an event of the union's experiment.** -/
theorem prEvent_doomFG_le_union (view : Pf → St × List (RMsg F)) (ops : List (GOp Pf F M))
    (hne : ops ≠ []) (X : OracleComp KeccakCalls (PreK Pf F)) :
    Pr{let z ← (simulateQ randomOracle (expLG view X ops)).run' ∅}[DoomFG view ops z] ≤
      Pr{let z ← romExperiment (gPick view ops hne <$> expLG view X ops) (gUVer view ops)}[
        z.1.2 = true ∧ GUDoomed view ops z.1.1 z.2] := by
  rw [romExperiment_map, prEvent_map, romExperiment_eq, StateT.run'_eq, prEvent_map]
  conv_lhs => rw [← bind_pure ((simulateQ randomOracle (expLG view X ops)).run ∅)]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp ↦ ?_
  classical
  by_cases hd : DoomFG view ops p.1
  · obtain ⟨hcons, hrep⟩ := expLG_replayF view X ops p hp
    obtain ⟨hk', hacc, hdoom⟩ := gDoomAtEnd_first view ops hd
    have hv : (simulateQ randomOracle (gUVer view ops (gPick view ops hne p.1))).run p.2 =
        pure (true, p.2) := by
      show (simulateQ randomOracle (GOp.run view ops[gFirstDoom view ops p.1] p.1.1.1.1
        p.1.1.1.2.1)).run p.2 = _
      rw [hrep _ (gFirstDoom_lt view hne p.1), hacc]
    refine (prEvent_le_one _).trans (le_of_eq ?_)
    rw [hv, map_pure, prEvent_pure, if_pos]
    refine ⟨rfl, ?_⟩
    have hc : (fun x ↦ p.2 (.inl x)) = fun x ↦ cacheOfTr p.1.2 (.inl x) :=
      funext fun x ↦ (hcons x).trans (cacheOfTr_inl _ _).symm
    show GDoomed view ops[gFirstDoom view ops p.1] p.1.1.1.1 p.1.1.1.2.1 p.2
    unfold GDoomed at hdoom ⊢
    rw [hc]
    exact hdoom
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr hev ↦ ?_) bot_le
    rw [mem_support_pure_iff] at hr
    subst hr
    exact hd hev

/-- **The openings' doom at the run's end, charged once**: for openings whose union is sound at `bnd`
(`GUnionSound`), and a run before the openings of `QX` queries, some opening accepts while doomed at the run's
end with probability at most `bnd (QX + Σ_k QO_k)`. -/
theorem prEvent_doomFG_le (view : Pf → St × List (RMsg F)) (ops : List (GOp Pf F M)) (bnd : ℕ → ℝ≥0∞)
    (hU : GUnionSound view ops bnd) (X : OracleComp KeccakCalls (PreK Pf F)) (QX : ℕ)
    (hX : IsTotalQueryBound X QX) :
    Pr{let z ← (simulateQ randomOracle (expLG view X ops)).run' ∅}[DoomFG view ops z] ≤
      bnd (QX + (ops.map fun o => o.QO).sum) := by
  rcases eq_or_ne ops [] with rfl | hne
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_not _ _ fun z hz ↦ ?_) bot_le
    obtain ⟨k, hk, -⟩ := hz
    exact absurd hk (Nat.not_lt_zero _)
  · exact (prEvent_doomFG_le_union view ops hne X).trans
      (hU _ _ ((isQueryBound_map_iff _ _ _ _ _).mpr (isTotalQueryBound_expLG view X ops QX hX)))

end First

end Compose

/-- info: 'Compose.knowledgeSoundness_listChainU_closed128G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.knowledgeSoundness_listChainU_closed128G

/-- info: 'Compose.prEvent_doomFG_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_doomFG_le
