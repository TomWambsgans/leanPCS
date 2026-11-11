-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Generalizes `formal/Compose/Compose/Rpm.lean` of this repository (the experiment as a transfer game,
-- `rpmThreaded_evalDistEq`; the transcript's hashes in the adversary's cache, `adv_cache`,
-- `consistent_romPrefix`, `rom_le`; the derandomization after a public setup, `exists_det_setup`; the
-- transfer, `rpm_le_wired`) from the old composition's setup, proof and verifier to any setup output, any
-- adversary output and any verifier, which that file adapts from leanerVM (https://github.com/Verified-zkEVM/
-- leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Rpm/RpmRelabel.lean`, `Rpm/Generic.lean`,
-- `Rpm/Extract.lean`, `Rpm/Coins.lean`, `common/Common/Transfer2.lean`, `common/Common/Rerun.lean`).
import Compose.Rpm

/-!
# The random-permutation transfer, for any setup, adversary and verifier

`Compose/Rpm.lean` moves the old composition's experiment from leanerVM's random-permutation model (one
random permutation `π`, Keccak-256 its sponge) to mumbai's two-oracle model. Its proof reads nothing of the
old protocol but the types of the setup's output, the adversary's output and the verifier's: here it is
restated for any of them.

* **the game** (`rpmGameG S A V`): the setup `S` (Keccak-256 calls only, its queries logged: `tS`) over `π`;
  the adversary `A`, with coins, `π` and `π⁻¹`, given the setup's output (its queries logged: `T`); the
  verifier `V` over `π`;
* **the event** (`BreaksG E`): `E` of the setup's output, the adversary's, the verdict, and the transcript
  `tS ++ evalTr (permutationQueries T)` (the setup's log and the Keccak-256 evaluations of the adversary's
  permutation transcript), for an `E` that reads the transcript through its answers only (`LookInv`);
* **`rpm_le_romG`**: its probability is at most that of `E` in the two-oracle game of a deterministic
  adversary `A'` (one computation, of at most `QS + Q` queries: it recomputes the public setup), the event
  holding of every transcript of the cache after the adversary (`BreaksCG`), plus `(QSπ + Q + QV)² / 2^508`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace PcsKS

open Compose QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics LeanVM.Protocol.Compile
open LeanVM.Rpm (HOnly DuplexVm DuplexP hashBlocks RSpec HFSpec HFS D2Spec CSpec RR toRHF ofRHF
  cmap projLog relP logRel)

variable {σ₀ α β : Type}

/-! ## The game and the event -/

/-- **The game in the random-permutation model**: the setup over `π`, its Keccak-256 queries logged; the
adversary given its output, its queries logged; the verifier over `π`. -/
def rpmGameG (S : OracleComp KeccakCalls σ₀) (A : σ₀ → OracleComp Common.RandomPermutationOracles α)
    (V : σ₀ → α → OracleComp KeccakCalls β) :
    OracleComp Common.RandomPermutationOracles (((σ₀ × α) × β) × Transcript × Common.OracleQueryLog) :=
  simulateQ keccakCallsOverQueryPermutation (loggedKC S) >>= fun s =>
    (simulateQ Common.loggedOracles (A s.1)).run [] >>= fun p =>
      simulateQ keccakCallsOverQueryPermutation (V s.1 p.1) >>= fun v =>
        pure (((s.1, p.1), v), s.2, p.2)

/-- An event reads a transcript through its answers only. -/
def LookInv (E : σ₀ → α → β → Transcript → Prop) : Prop :=
  ∀ s a v (tr tr' : Transcript), (∀ x, lookTr tr x = lookTr tr' x) → E s a v tr → E s a v tr'

/-- **The event of an outcome**: `E` on the setup's log and the Keccak-256 evaluations of the adversary's
permutation transcript. -/
def BreaksG (E : σ₀ → α → β → Transcript → Prop)
    (z : ((σ₀ × α) × β) × Transcript × Common.OracleQueryLog) : Prop :=
  E z.1.1.1 z.1.1.2 z.1.2 (z.2.1 ++ evalTr (permutationQueries z.2.2))

/-- The event with the permutation transcript. -/
def BreaksTG (E : σ₀ → α → β → Transcript → Prop)
    (z : ((σ₀ × α) × β) × Transcript × PermutationTranscript) : Prop :=
  E z.1.1.1 z.1.1.2 z.1.2 (z.2.1 ++ evalTr z.2.2)

/-- **The game, the permutation's edges threaded.** -/
noncomputable def rpmThreadedG (S : OracleComp KeccakCalls σ₀)
    (A : σ₀ → OracleComp Common.RandomPermutationOracles α) (V : σ₀ → α → OracleComp KeccakCalls β) :
    ProbComp (((σ₀ × α) × β) × Transcript × PermutationTranscript) :=
  (simulateQ keccakCallsOverRandomPermutation (loggedKC S)).run [] >>= fun s =>
    (simulateQ loggedRandomPermutationOracles (A s.1.1)).run (s.2, []) >>= fun p =>
      (simulateQ keccakCallsOverRandomPermutation (V s.1.1 p.1)).run' p.2.1 >>= fun v =>
        pure (((s.1.1, p.1), v), s.1.2, p.2.2)

theorem map_rpmGameG (S : OracleComp KeccakCalls σ₀)
    (A : σ₀ → OracleComp Common.RandomPermutationOracles α) (V : σ₀ → α → OracleComp KeccakCalls β) :
    (fun z : ((σ₀ × α) × β) × Transcript × Common.OracleQueryLog =>
        (z.1, z.2.1, permutationQueries z.2.2)) <$>
        Common.runWithRandomPermutation (rpmGameG S A V) = rpmThreadedG S A V := by
  have hA : ∀ x E, (simulateQ loggedRandomPermutationOracles (A x)).run (E, []) =
      (fun p => (p.1.1, p.2, permutationQueries p.1.2)) <$>
        (simulateQ Common.lazyRandomPermutationOracles
          ((simulateQ Common.loggedOracles (A x)).run [])).run E := by
    intro x E
    rw [logged_run (A x) [] E]
    simp [permutationQueries_nil]
  simp only [rpmGameG, rpmThreadedG, Common.runWithRandomPermutation, simulateQ_bind, simulateQ_pure,
    StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind, map_pure, hA, bind_map_left,
    simulateQ_lazy_keccakCallsOverQueryPermutation]

theorem prEvent_rpmGameG (E : σ₀ → α → β → Transcript → Prop) (S : OracleComp KeccakCalls σ₀)
    (A : σ₀ → OracleComp Common.RandomPermutationOracles α) (V : σ₀ → α → OracleComp KeccakCalls β) :
    Pr{let z ← Common.runWithRandomPermutation (rpmGameG S A V)}[BreaksG E z] =
      Pr{let z ← rpmThreadedG S A V}[BreaksTG E z] := by
  rw [← map_rpmGameG, prEvent_map]
  rfl

/-! ## The transfer game -/

/-- The setup on bytes, its log. -/
def preBG (S : OracleComp KeccakCalls σ₀) :
    OracleComp (unifSpec + Common.roSpec (List UInt8) Common.DigestBytes) (σ₀ × Transcript) :=
  simulateQ toRH (loggedKC S)

/-- The adversary on bytes, with its transcript. -/
def advBG (A : σ₀ → OracleComp Common.RandomPermutationOracles α) (x : σ₀ × Transcript) :
    OracleComp RSpec (α × PermutationTranscript) :=
  (simulateQ logRelC (A x.1)).run []

/-- The verifier on bytes. -/
def postBG (V : σ₀ → α → OracleComp KeccakCalls β) (x : σ₀ × Transcript)
    (a : α × PermutationTranscript) :
    OracleComp HFSpec (((σ₀ × α) × β) × Transcript × PermutationTranscript) :=
  (fun v => (((x.1, a.1), v), x.2, a.2)) <$> simulateQ toRHF (V x.1 a.1)

/-- **The transfer game.** -/
def gameBG (S : OracleComp KeccakCalls σ₀) (A : σ₀ → OracleComp Common.RandomPermutationOracles α)
    (V : σ₀ → α → OracleComp KeccakCalls β) :
    OracleComp D2Spec (((σ₀ × α) × β) × Transcript × PermutationTranscript) :=
  Common.rpmGame2 (preBG S) (advBG A) (postBG V)

/-- **The game is the real world of the transfer game.** -/
theorem rpmThreadedG_evalDistEq (S : OracleComp KeccakCalls σ₀) (hS : HOnly S)
    (A : σ₀ → OracleComp Common.RandomPermutationOracles α) (V : σ₀ → α → OracleComp KeccakCalls β) :
    rpmThreadedG S A V =ᵈ
      Common.realGame2 Common.keccakPadding Common.KState.zero (gameBG S A V) := by
  rw [LeanVM.Rpm.realGame2_eq, gameBG, Common.rpmGame2, preBG,
    hEmbed2_toRH (loggedKC S) (hOnly_loggedKC_run S hS [])]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  simp only [postBG, simulateQ_map, StateT.run_map, Functor.map_map, RR,
    QueryImpl.simulateQ_compose]
  have hpre := (LeanVM.Rpm.post_relabel (loggedKC S) []).symm
  simp only [projLog, LeanVM.Rpm.logMap, List.map_nil, RR, QueryImpl.simulateQ_compose] at hpre
  rw [rpmThreadedG]
  refine EvalDistEq.trans (EvalDistEq.bind_left hpre _) ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun x => ?_
  have hadv := (adv_relabelC (A x.1.1) x.2 []).symm
  simp only [RR, QueryImpl.simulateQ_compose] at hadv
  simp only [advBG]
  refine EvalDistEq.trans (EvalDistEq.bind_left hadv _) ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun p => ?_
  have h := (LeanVM.Rpm.post_relabel' (V x.1.1 p.1.1) p.2).symm.map
    fun v => (((x.1.1, p.1.1), v), x.1.2, p.1.2)
  simp only [StateT.run'_eq, Functor.map_map, RR, QueryImpl.simulateQ_compose] at h
  simp only [StateT.run'_eq, bind_pure_comp, Functor.map_map]
  exact h

theorem duplex_postBG (V : σ₀ → α → OracleComp KeccakCalls β) (hV : ∀ s a, DuplexVm (V s a) [])
    (x : σ₀ × Transcript) (a : α × PermutationTranscript) :
    Common.Duplex Common.KState.zero Common.keccakNF (postBG V x a) [] := by
  have h := LeanVM.Rpm.duplex_toRHF _ [] (hV x.1 a.1)
  exact LeanVM.Rpm.duplex_map _ _ [] (by simpa using h)

theorem cost_advBG (A : σ₀ → OracleComp Common.RandomPermutationOracles α)
    (Q : ℕ) (hA : ∀ s, Common.QueryCostAtMost (A s) Common.permutationCallCost Q)
    (x : σ₀ × Transcript) : Common.QueryCostAtMost (advBG A x) LeanVM.Rpm.advCost Q := by
  refine Common.isWeightBound_run_simulateQ logRelC Common.permutationCallCost LeanVM.Rpm.advCost
    (fun t T => ?_) (hA x.1) []
  rcases t with n | q
  · exact Common.isWeightBound_map _ (Common.isWeightBound_query LeanVM.Rpm.advCost (.inl n))
  · simp only [logRelC, logRel, StateT.run_mk, relP]
    exact Common.isWeightBound_map _ (Common.isWeightBound_map _
      (Common.isWeightBound_query LeanVM.Rpm.advCost (.inr (.inr (permQueryToRpm q)))))

/-- **The permutation calls of the transfer game**: the setup's `QSπ`, the adversary's `Q`, the
verifier's `QV`. -/
theorem cost_gameBG (S : OracleComp KeccakCalls σ₀) (hS : HOnly S) (QSπ : ℕ)
    (hSπ : Common.QueryCostAtMost S hashBlocks QSπ)
    (A : σ₀ → OracleComp Common.RandomPermutationOracles α)
    (Q : ℕ) (hA : ∀ s, Common.QueryCostAtMost (A s) Common.permutationCallCost Q)
    (V : σ₀ → α → OracleComp KeccakCalls β) (QV : ℕ)
    (hV : ∀ s a, Common.QueryCostAtMost (V s a) hashBlocks QV) :
    Common.QueryCostAtMost (gameBG S A V)
      (Common.queryCost2 (Dg := Common.DigestBytes) Common.keccakPadding)
      (QSπ + Q + QV) := by
  have h : Common.QueryCostAtMost (gameBG S A V) LeanVM.Rpm.gameCost (QSπ + (Q + QV)) := by
    rw [gameBG, Common.rpmGame2, preBG, hEmbed2_toRH (loggedKC S) (hOnly_loggedKC_run S hS [])]
    refine (LeanVM.Rpm.isWeightBound_hfEmbed_toRHF (cost_loggedKC S QSπ hSπ [])).bind
      fun x => ?_
    refine (LeanVM.Rpm.isWeightBound_advEmbed (cost_advBG A Q hA x)).bind fun a => ?_
    rw [postBG, simulateQ_map]
    exact Common.isWeightBound_map _ (LeanVM.Rpm.isWeightBound_hfEmbed_toRHF (hV _ _))
  exact h.mono (by omega)

/-! ## The random-oracle side -/

/-- **The adversary with the simulator, on lanes, with its transcript.** -/
noncomputable def romAdvTG (A : σ₀ → OracleComp Common.RandomPermutationOracles α) (x : σ₀ × Transcript) :
    OracleComp CSpec (α × PermutationTranscript) :=
  simulateQ ofRHF (Common.advS2 Common.keccakPadding Common.KState.zero (advBG A x))

/-- **The random-oracle adversary of the transfer.** -/
noncomputable def romAdvCG (A : σ₀ → OracleComp Common.RandomPermutationOracles α) (x : σ₀) :
    OracleComp CSpec α :=
  Prod.fst <$> romAdvTG A (x, [])

/-- The verifier from the cache after the adversary, that cache kept. -/
noncomputable def gLG (V : σ₀ → α → OracleComp KeccakCalls β) (p : (σ₀ × α) × KeccakCalls.QueryCache) :
    ProbComp (((σ₀ × α) × β) × KeccakCalls.QueryCache) :=
  (fun v => ((p.1, v), p.2)) <$> (simulateQ randomOracle (V p.1.1 p.1.2)).run' p.2

/-- **The event on the cache after the adversary**: `E` of every transcript recording the cache's
Keccak-256 answers. -/
def BreaksCG (E : σ₀ → α → β → Transcript → Prop) (z : ((σ₀ × α) × β) × KeccakCalls.QueryCache) : Prop :=
  ∀ tr, Consistent tr z.2 → E z.1.1.1 z.1.1.2 z.1.2 tr

theorem advS2_advBG (A : σ₀ → OracleComp Common.RandomPermutationOracles α) (x : σ₀ × Transcript) :
    Common.advS2 Common.keccakPadding Common.KState.zero (advBG A x) =
      (fun y ↦ (y.1, y.2.2.map LeanVM.Rpm.entryOfRpm)) <$>
        (simulateQ (Common.advImplLog2 Common.keccakPadding) (simulateQ relPC (A x.1))).run
          (Common.SimState.init Common.KState.zero, []) := by
  have h := advImpl2_logRelC (A x.1) [] (Common.SimState.init Common.KState.zero)
  rw [List.map_nil] at h
  rw [← h, Functor.map_map, Common.advS2, advBG, StateT.run'_eq]
  congr 1
  funext y
  simp only [List.map_map]
  have e : LeanVM.Rpm.entryOfRpm ∘ LeanVM.Rpm.entryToRpm = id :=
    funext LeanVM.Rpm.entryOfRpm_toRpm
  rw [e, List.map_id]

/-- **The adversary's cache**: it extends the starting cache, holds every Keccak-256 evaluation of the
adversary's transcript, and no other new Keccak-256 answer. -/
theorem adv_cacheG (A : σ₀ → OracleComp Common.RandomPermutationOracles α) (x : σ₀ × Transcript)
    (c₀ : HFS.QueryCache) {z}
    (hz : z ∈ support ((simulateQ HFS.romImpl
      (Common.advS2 Common.keccakPadding Common.KState.zero (advBG A x))).run c₀)) :
    c₀ ≤ z.2 ∧ (∀ md ∈ LeanVM.Rpm.transcriptPathsB z.1.2, z.2 (.inl md.1) = some md.2) ∧
      (∀ m d, z.2 (.inl m) = some d → c₀ (.inl m) = some d ∨
        (m, d) ∈ LeanVM.Rpm.transcriptPathsB z.1.2) := by
  refine ⟨Common.le_of_mem_support_run _ c₀ hz, ?_⟩
  rw [advS2_advBG, simulateQ_map, StateT.run_map, Common.run_simulateQ_foldRO, Functor.map_map,
    support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have eT : (w.2.1.2.map LeanVM.Rpm.entryOfRpm).map
      (fun e ↦ (permQueryToRpm e.1, LeanVM.KState.toRpm e.2)) = w.2.1.2 := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id w.2.1.2]
    exact List.map_congr_left fun e _ ↦ LeanVM.Rpm.entryToRpm_ofRpm e
  have hpaths : LeanVM.Rpm.transcriptPathsB (w.2.1.2.map LeanVM.Rpm.entryOfRpm) =
      Common.pathsOf Common.keccakPadding Common.KState.zero w.2.1.2 := by
    rw [LeanVM.Rpm.transcriptPathsB, eT]
  have hrep : w.2.1.1 = Common.replay Common.KState.zero w.2.1.2 := by
    have h1 := Common.run_simulateQ_foldRO
      (Common.advImplLog2 Common.keccakPadding) (simulateQ relPC (A x.1))
      (Common.SimState.init Common.KState.zero, []) c₀
    have hz' : ((w.1, w.2.1), w.2.2) ∈ support ((simulateQ HFS.romImpl
        ((simulateQ (Common.advImplLog2 Common.keccakPadding)
          (simulateQ relPC (A x.1))).run (Common.SimState.init Common.KState.zero, []))).run
            c₀) := by
      rw [h1, support_map]
      exact ⟨w, hw, rfl⟩
    exact Common.simulator2_state_eq_replay _ _ _
      (Common.fst_mem_support_of_mem_support_ro2 hz')
  have hrel := cacheRel_run c₀ (A x.1) ((Common.SimState.init Common.KState.zero, []), c₀)
    (fun m d hd => Or.inl hd) w hw
  refine ⟨?_, fun m d hd => ?_⟩
  · simp only [hpaths]
    exact pathsOf_ideal2C _ c₀ hw
  · simp only [hpaths]
    rcases hrel m d hd with h | h
    · exact Or.inl h
    · rw [hrep] at h
      exact Or.inr h

/-- The prefix of the transfer's random-oracle game: the setup, then the adversary with the simulator. -/
noncomputable def romPrefixG (S : OracleComp KeccakCalls σ₀)
    (A : σ₀ → OracleComp Common.RandomPermutationOracles α) :
    OracleComp HFSpec ((σ₀ × Transcript) × (α × PermutationTranscript)) :=
  simulateQ (Common.hInF (E := Common.KRest) (C := Common.KCap)) (preBG S) >>= fun x =>
    (x, ·) <$> Common.advS2 Common.keccakPadding Common.KState.zero (advBG A x)

/-- **After the setup and the adversary, the cache's Keccak-256 answers are those the setup's log and the
Keccak-256 evaluations of the adversary's transcript record.** -/
theorem consistent_romPrefixG (S : OracleComp KeccakCalls σ₀) (hS : HOnly S)
    (A : σ₀ → OracleComp Common.RandomPermutationOracles α)
    {p : ((σ₀ × Transcript) × (α × PermutationTranscript)) × HFS.QueryCache}
    (hp : p ∈ support ((simulateQ HFS.romImpl (romPrefixG S A)).run ∅)) :
    Consistent (p.1.1.2 ++ evalTr p.1.2.2) (cmap p.2) := by
  rw [romPrefixG, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hp
  obtain ⟨⟨x, c₁⟩, h1, hp⟩ := hp
  rw [simulateQ_map, StateT.run_map, support_map] at hp
  obtain ⟨⟨a, c₂⟩, h2, rfl⟩ := hp
  have hc1 : Consistent x.2 (cmap c₁) := consB_run S hS [] ∅
    (by rw [LeanVM.Rpm.cmap_empty]; exact consistent_nil) (x, c₁) h1
  obtain ⟨hle, hpaths, hrel⟩ := adv_cacheG A x c₁ h2
  intro m
  show cmap c₂ (.inl m) = lookTr (x.2 ++ evalTr a.2) m
  rw [lookTr_append', lookTr_evalTr, LeanVM.Rpm.hashesOf_transcriptPaths, ← hc1 m,
    LeanVM.Rpm.cmap_inl, LeanVM.Rpm.cmap_inl]
  rcases h : c₁ (.inl m) with _ | d
  · simp only [Option.map_none]
    unfold LeanVM.Rpm.hashesOfB
    rcases hf : (LeanVM.Rpm.transcriptPathsB a.2).find? (·.1 = m) with _ | e
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

theorem romRun2_splitG (S : OracleComp KeccakCalls σ₀)
    (A : σ₀ → OracleComp Common.RandomPermutationOracles α) (V : σ₀ → α → OracleComp KeccakCalls β) :
    Common.romRun2 (simulateQ (Common.hInF (E := Common.KRest) (C := Common.KCap)) (preBG S) >>=
      fun x => Common.advS2 Common.keccakPadding Common.KState.zero (advBG A x) >>= fun a =>
        postBG V x a) =
      (simulateQ HFS.romImpl (romPrefixG S A)).run ∅ >>= fun p =>
        (simulateQ HFS.romImpl (postBG V p.1.1 p.1.2)).run' p.2 := by
  simp only [Common.romRun2, romPrefixG, simulateQ_bind, simulateQ_map, StateT.run'_eq,
    StateT.run_bind, StateT.run_map, map_bind, bind_map_left, bind_assoc]

/-- **The transfer's random-oracle game, on lanes, with the event on the cache.** -/
theorem rom_leG (E : σ₀ → α → β → Transcript → Prop) (hE : LookInv E) (S : OracleComp KeccakCalls σ₀)
    (hS : HOnly S) (A : σ₀ → OracleComp Common.RandomPermutationOracles α)
    (V : σ₀ → α → OracleComp KeccakCalls β) :
    Pr{let z ← Common.romRun2 (simulateQ (Common.hInF (E := Common.KRest) (C := Common.KCap))
        (preBG S) >>= fun x => Common.advS2 Common.keccakPadding Common.KState.zero
          (advBG A x) >>= fun a => postBG V x a)}[BreaksTG E z] ≤
      Pr{let y ← (simulateQ KeccakCalls.romImpl (simulateQ liftKC S >>= fun x =>
          (x, ·) <$> romAdvCG A x)).run ∅ >>= gLG V}[BreaksCG E y] := by
  rw [romRun2_splitG]
  have hpost : ∀ p : ((σ₀ × Transcript) × (α × PermutationTranscript)) × HFS.QueryCache,
      Pr{let z ← (simulateQ HFS.romImpl (postBG V p.1.1 p.1.2)).run' p.2}[BreaksTG E z] =
        Pr{let v ← (simulateQ randomOracle (V p.1.1.1 p.1.2.1)).run' (cmap p.2)}[
          BreaksTG E (((p.1.1.1, p.1.2.1), v), p.1.1.2, p.1.2.2)] := by
    intro p
    rw [postBG, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, prEvent_map]
    have h := (LeanVM.Rpm.run'_toRHF (V p.1.1.1 p.1.2.1) p.2).prEvent_eq
      (fun v => BreaksTG E (((p.1.1.1, p.1.2.1), v), p.1.1.2, p.1.2.2))
    rw [StateT.run'_eq, prEvent_map] at h
    exact h
  have h := LeanVM.Rpm.run_ofRHF (romPrefixG S A) ∅
  rw [LeanVM.Rpm.cmap_empty] at h
  have hX : (fun r => (r.1.1, r.2.1)) <$> simulateQ ofRHF (romPrefixG S A) =
      simulateQ liftKC S >>= fun x => (x, ·) <$> romAdvCG A x := by
    rw [romPrefixG, simulateQ_bind, preBG,
      ofRHF_hInF_toRH (loggedKC S) (hOnly_loggedKC_run S hS [])]
    conv_rhs => rw [← fst_loggedKC_run S [], simulateQ_map, bind_map_left]
    simp only [simulateQ_map, map_bind, Functor.map_map]
    refine bind_congr fun x => ?_
    simp only [romAdvCG, romAdvTG, Functor.map_map]
    rfl
  have hJ : (fun p : ((σ₀ × Transcript) × (α × PermutationTranscript)) × HFS.QueryCache =>
      ((p.1.1.1, p.1.2.1), cmap p.2)) <$>
        (simulateQ HFS.romImpl (romPrefixG S A)).run ∅ =ᵈ
      (simulateQ KeccakCalls.romImpl (simulateQ liftKC S >>= fun x =>
        (x, ·) <$> romAdvCG A x)).run ∅ := by
    rw [← hX, simulateQ_map, StateT.run_map]
    refine EvalDistEq.trans ?_ (h.symm.map _)
    rw [Functor.map_map]
    exact EvalDistEq.rfl
  calc _ ≤ Pr{let y ← (simulateQ HFS.romImpl (romPrefixG S A)).run ∅ >>= fun p =>
              gLG V ((p.1.1.1, p.1.2.1), cmap p.2)}[BreaksCG E y] := by
        refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp => ?_
        rw [hpost, gLG, prEvent_map]
        refine prEvent_mono _ _ _ fun v hv => fun tr htr => ?_
        have hcons := consistent_romPrefixG S hS A hp
        exact hE _ _ _ _ _ (fun x => (hcons x).symm.trans (htr x)) hv
    _ = _ := by
        rw [← bind_map_left]
        exact (EvalDistEq.bind_left hJ _).prEvent_eq _

/-! ## Coins do not help -/

/-- **Derandomization after a public setup**: an adversary with coins, run after the setup, does no
better than one deterministic computation, which recomputes the setup to learn its output and the cache
it leaves (`QS` more queries). -/
theorem exists_det_setupG {γ : Type} (S : OracleComp KeccakCalls σ₀) (QS : ℕ)
    (hS : IsTotalQueryBound S QS) (Y : σ₀ → OracleComp CSpec α) (Q : ℕ)
    (hY : ∀ x, Common.QueryCostAtMost (Y x) LeanVM.Rpm.hashCalls Q)
    (g : (σ₀ × α) × KeccakCalls.QueryCache → ProbComp γ) (E : γ → Prop) :
    ∃ A' : OracleComp KeccakCalls α, IsTotalQueryBound A' (QS + Q) ∧
      Pr{let y ← (simulateQ KeccakCalls.romImpl (simulateQ liftKC S >>= fun x =>
          (x, ·) <$> Y x)).run ∅ >>= g}[E y] ≤
        Pr{let y ← (simulateQ randomOracle (S >>= fun x => (x, ·) <$> A')).run ∅ >>= g}[E y] := by
  choose A₀ hA₀ hle using fun (x : σ₀) (c : KeccakCalls.QueryCache) =>
    LeanVM.Rpm.exists_det (fun p => g ((x, p.1), p.2)) E (Y x) Q (hY x) c
  refine ⟨(simulateQ cacheImpl S).run ∅ >>= fun r => A₀ r.1 r.2,
    isTotalQueryBound_bind (isTotalQueryBound_cacheRun S QS ∅ hS) fun r => hA₀ r.1 r.2, ?_⟩
  rw [simulateQ_bind, StateT.run_bind, run_liftKC, simulateQ_bind, StateT.run_bind, bind_assoc,
    bind_assoc]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp => ?_
  simp only [simulateQ_map, StateT.run_map, bind_map_left]
  rw [simulateQ_bind, StateT.run_bind, rerun_cacheImpl S ∅ hp p.2 le_rfl, pure_bind]
  exact hle p.1 p.2

theorem cost_advBG_wR (A : σ₀ → OracleComp Common.RandomPermutationOracles α) (Q : ℕ)
    (hA : ∀ s, Common.QueryCostAtMost (A s) Common.permutationCallCost Q)
    (x : σ₀ × Transcript) : Common.QueryCostAtMost (advBG A x) LeanVM.Rpm.wR Q := by
  refine Common.isWeightBound_run_simulateQ logRelC Common.permutationCallCost LeanVM.Rpm.wR
    (fun t T => ?_) (hA x.1) []
  rcases t with n | q
  · exact Common.isWeightBound_map _ (Common.isWeightBound_query LeanVM.Rpm.wR (.inl n))
  · simp only [logRelC, logRel, StateT.run_mk, relP]
    exact Common.isWeightBound_map _ (Common.isWeightBound_map _
      (Common.isWeightBound_query LeanVM.Rpm.wR (.inr (.inr (permQueryToRpm q)))))

/-- **The random-oracle adversary makes at most one oracle query per call of `π` or `π⁻¹`.** -/
theorem cost_romAdvCG (A : σ₀ → OracleComp Common.RandomPermutationOracles α) (Q : ℕ)
    (hA : ∀ s, Common.QueryCostAtMost (A s) Common.permutationCallCost Q) (x : σ₀) :
    Common.QueryCostAtMost (romAdvCG A x) LeanVM.Rpm.hashCalls Q := by
  refine Common.isWeightBound_map _ (LeanVM.Rpm.isWeightBound_simulateQ_ofRHF ?_)
  rw [Common.advS2, StateT.run'_eq]
  exact Common.isWeightBound_map _ (Common.isWeightBound_run_simulateQ _ LeanVM.Rpm.wR
    LeanVM.Rpm.wHF LeanVM.Rpm.isWeightBound_advImpl2 (cost_advBG_wR A Q hA (x, [])) _)

/-! ## The transfer -/

/-- **From the random-permutation model to mumbai's two-oracle model**, for any setup (Keccak-256 calls
only, at most `QS` queries and `QSπ` calls of `π`), adversary (at most `Q` calls of `π`, `π⁻¹`, its coins
free) and verifier (the duplex discipline, at most `QV` calls of `π`), and an event that reads the
transcript through its answers: one deterministic adversary of the two random oracles, of at most `QS + Q`
queries, makes the event hold of every transcript of its cache at least as often, less
`(QSπ + Q + QV)² / 2^508`. -/
theorem rpm_le_romG (E : σ₀ → α → β → Transcript → Prop) (hE : LookInv E)
    (S : OracleComp KeccakCalls σ₀) (hSH : HOnly S) (QS QSπ : ℕ) (hS : IsTotalQueryBound S QS)
    (hSπ : Common.QueryCostAtMost S hashBlocks QSπ)
    (A : σ₀ → OracleComp Common.RandomPermutationOracles α)
    (Q : ℕ) (hA : ∀ s, Common.QueryCostAtMost (A s) Common.permutationCallCost Q)
    (V : σ₀ → α → OracleComp KeccakCalls β) (hVd : ∀ s a, DuplexVm (V s a) []) (QV : ℕ)
    (hV : ∀ s a, Common.QueryCostAtMost (V s a) hashBlocks QV) :
    ∃ A' : OracleComp KeccakCalls α, IsTotalQueryBound A' (QS + Q) ∧
      Pr{let z ← Common.runWithRandomPermutation (rpmGameG S A V)}[BreaksG E z] ≤
        Pr{let y ← (simulateQ randomOracle (S >>= fun x => (x, ·) <$> A')).run ∅ >>= gLG V}[
          BreaksCG E y] + ((QSπ + Q + QV : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 := by
  obtain ⟨A', hA', hle⟩ := exists_det_setupG S QS hS (romAdvCG A) Q (cost_romAdvCG A Q hA)
    (gLG V) (BreaksCG E)
  refine ⟨A', hA', ?_⟩
  rw [prEvent_rpmGameG, (rpmThreadedG_evalDistEq S hSH A V).prEvent_eq]
  obtain ⟨ht, -⟩ := Common.keccak256_transfer2 (preBG S) (advBG A) (postBG V)
    (duplex_postBG V hVd) (QSπ + Q + QV) (cost_gameBG S hSH QSπ hSπ A Q hA V QV hV)
    (BreaksTG E)
  exact ht.trans (add_le_add ((rom_leG E hE S hSH A V).trans hle) le_rfl)

end PcsKS

/-- info: 'PcsKS.rpm_le_romG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsKS.rpm_le_romG
