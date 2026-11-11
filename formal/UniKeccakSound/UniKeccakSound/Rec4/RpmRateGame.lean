-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Adapted from this repository's
-- `formal/Compose/Compose/ListChainKRpmS.lean` (`rpmGameS`, `kcGameS`, `rpmThreadedS`, `map_rpmGameS`,
-- `rpmThreadedS_evalDistEq`, `duplex_postBS`, `cost_advBS`, `cost_gameBS`), itself adapted from leanerVM `mumbai`
-- (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0: `Rpm/Generic.lean`'s
-- `detRun_evalDistEq`), with the verifier in the rate model and the transfer game on `RState`.
import UniKeccakSound.Rec4.RpmRateReal

/-!
# The rate model's games, and the random-permutation game as the real world of a transfer game on `RState`

* `rpmGameSR setup fix A V`: the setup (two-oracle model, Keccak-256 over `π`, logged), the adversary with coins, `π`,
  `π⁻¹` (logged), the verifier `V` of the rate model over `π` (`keccakCallsROverQueryPermutation`);
* `kcGameSR setup fix A' V`: the same in the rate model's random-oracle world, the setup's and the adversary's
  Keccak-256 queries logged (digests);
* **`rpmThreadedSR_evalDistEq`**: the first, its permutation's edges threaded, is the real world of the transfer
  game `gameBSR` on `RState`; `duplex_postBSR`, `cost_gameBSR`: that game's discipline and calls of `π`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace UniKeccakSound.Rec4

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Common (KCap)
open Compose (TailP KeccakCallsR liftR loggedKCR Transcript loggedKC evalTr RpmOutTG)
open LeanVM.Rpm (HOnly DuplexVm AdmissibleVm StRel)

variable {Pf β σ : Type}

/-! ## The games -/

/-- **The random-permutation game with a verifier of the rate model**: the setup with Keccak-256 over `π`, its
queries logged; the adversary given its output, its queries logged (coins, `π`, `π⁻¹`); the verifier on the proof
`fix` makes, Keccak-256's last state read as the rate model's answer, Keccak-f `= π`. -/
def rpmGameSR (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A : σ → OracleComp Common.RandomPermutationOracles Pf) (V : Pf → OracleComp KeccakCallsR β) :
    OracleComp Common.RandomPermutationOracles ((Pf × β) × Transcript × Common.OracleQueryLog) :=
  simulateQ keccakCallsOverQueryPermutation (loggedKC setup) >>= fun s =>
    (simulateQ Common.loggedOracles (A s.1)).run [] >>= fun p =>
      simulateQ keccakCallsROverQueryPermutation (V (fix s.1 p.1)) >>= fun v =>
        pure ((fix s.1 p.1, v), s.2, p.2)

/-- **The rate model's game**: the setup (read on the digest) then the adversary given its output, their Keccak-256
queries logged with their digests; then the verifier. -/
def kcGameSR (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A' : σ → OracleComp KeccakCallsR Pf) (V : Pf → OracleComp KeccakCallsR β) :
    OracleComp KeccakCallsR ((Pf × β) × Transcript) :=
  loggedKCR (simulateQ liftR setup >>= fun ir => fix ir <$> A' ir) >>= fun pt =>
    V pt.1 >>= fun v => pure ((pt.1, v), pt.2)

/-- **The game, the permutation's edges threaded.** -/
noncomputable def rpmThreadedSR (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A : σ → OracleComp Common.RandomPermutationOracles Pf) (V : Pf → OracleComp KeccakCallsR β) :
    ProbComp (RpmOutTG Pf β) :=
  (simulateQ keccakCallsOverRandomPermutation (loggedKC setup)).run [] >>= fun s =>
    (simulateQ loggedRandomPermutationOracles (A s.1.1)).run (s.2, []) >>= fun p =>
      (simulateQ keccakCallsROverRandomPermutation (V (fix s.1.1 p.1))).run' p.2.1 >>=
        fun v => pure ((fix s.1.1 p.1, v), s.1.2, p.2.2)

theorem map_rpmGameSR (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A : σ → OracleComp Common.RandomPermutationOracles Pf) (V : Pf → OracleComp KeccakCallsR β) :
    (fun z : (Pf × β) × Transcript × Common.OracleQueryLog =>
        (z.1, z.2.1, permutationQueries z.2.2)) <$>
        Common.runWithRandomPermutation (rpmGameSR setup fix A V) = rpmThreadedSR setup fix A V := by
  have hA : ∀ ir E, (simulateQ loggedRandomPermutationOracles (A ir)).run (E, []) =
      (fun p => (p.1.1, p.2, permutationQueries p.1.2)) <$>
        (simulateQ Common.lazyRandomPermutationOracles
          ((simulateQ Common.loggedOracles (A ir)).run [])).run E := by
    intro ir E
    rw [logged_run (A ir) [] E]
    simp [permutationQueries_nil]
  simp only [rpmGameSR, rpmThreadedSR, Common.runWithRandomPermutation, simulateQ_bind,
    simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind, map_pure, hA,
    bind_map_left, simulateQ_lazy_keccakCallsOverQueryPermutation, simulateQ_lazy_keccakCallsROver]

theorem prEvent_rpmGameSR (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A : σ → OracleComp Common.RandomPermutationOracles Pf) (V : Pf → OracleComp KeccakCallsR β)
    (E : (Pf × β) → Transcript → Prop) :
    Pr{let z ← Common.runWithRandomPermutation (rpmGameSR setup fix A V)}[
        E z.1 (z.2.1 ++ evalTr (permutationQueries z.2.2))] =
      Pr{let z ← rpmThreadedSR setup fix A V}[E z.1 (z.2.1 ++ evalTr z.2.2)] := by
  rw [← map_rpmGameSR, prEvent_map]

/-! ## The transfer game on `RState` -/

/-- The setup on `RState`'s bytes, its log. -/
def preBSR (setup : OracleComp KeccakCalls σ) :
    OracleComp (unifSpec + Common.roSpec (List UInt8) RateBytes) (σ × Transcript) :=
  simulateQ toRHR (loggedKC setup)

/-- The adversary on `RState`, with its transcript. -/
def advBSR (A : σ → OracleComp Common.RandomPermutationOracles Pf) (x : σ × Transcript) :
    OracleComp RSpecR (Pf × PermutationTranscript) :=
  (simulateQ logRelCR (A x.1)).run []

/-- The verifier on `RState`. -/
def postBSR (fix : σ → Pf → Pf) (V : Pf → OracleComp KeccakCallsR β) (x : σ × Transcript)
    (a : Pf × PermutationTranscript) : OracleComp HFSpecR (RpmOutTG Pf β) :=
  (fun v => ((fix x.1 a.1, v), x.2, a.2)) <$> simulateQ toRHFR (V (fix x.1 a.1))

/-- **The transfer game on `RState`**: the setup, the adversary, the verifier. -/
def gameBSR (setup : OracleComp KeccakCalls σ) (fix : σ → Pf → Pf)
    (A : σ → OracleComp Common.RandomPermutationOracles Pf) (V : Pf → OracleComp KeccakCallsR β) :
    OracleComp D2SpecR (RpmOutTG Pf β) :=
  Common.rpmGame2 (preBSR setup) (advBSR A) (postBSR fix V)

/-- **The game is the real world of the transfer game on `RState`.** -/
theorem rpmThreadedSR_evalDistEq (setup : OracleComp KeccakCalls σ) (hS : HOnly setup)
    (fix : σ → Pf → Pf) (A : σ → OracleComp Common.RandomPermutationOracles Pf)
    (V : Pf → OracleComp KeccakCallsR β) :
    rpmThreadedSR setup fix A V =ᵈ Common.realGame2 keccakPaddingR RState.zero (gameBSR setup fix A V) := by
  rw [realGame2_eqR, gameBSR, Common.rpmGame2, preBSR,
    hEmbed2_toRHR (loggedKC setup) (Compose.hOnly_loggedKC_run setup hS [])]
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  simp only [postBSR, simulateQ_map, StateT.run_map, Functor.map_map, RRR, QueryImpl.simulateQ_compose]
  have hpre := (post_relabelR (simulateQ liftR (loggedKC setup)) []).symm
  simp only [projLogR, LeanVM.Rpm.logMap, List.map_nil, RRR, QueryImpl.simulateQ_compose] at hpre
  rw [rpmThreadedSR, simulateQ_keccakCallsOver_liftR]
  refine EvalDistEq.trans (EvalDistEq.bind_left hpre _) ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun x => ?_
  have hadv := (adv_relabelCR (A x.1.1) x.2 []).symm
  simp only [RRR, QueryImpl.simulateQ_compose] at hadv
  simp only [advBSR]
  refine EvalDistEq.trans (EvalDistEq.bind_left hadv _) ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun p => ?_
  have h := (post_relabelR' (V (fix x.1.1 p.1.1)) p.2).symm.map
    fun v => ((fix x.1.1 p.1.1, v), x.1.2, p.1.2)
  simp only [StateT.run'_eq, Functor.map_map, RRR, QueryImpl.simulateQ_compose] at h
  simp only [StateT.run'_eq, bind_pure_comp, Functor.map_map]
  exact h

/-! ## The transfer game's discipline and calls of `π` -/

theorem duplex_postBSR (fix : σ → Pf → Pf) (V : Pf → OracleComp KeccakCallsR β)
    (hVd : ∀ π, DuplexVmR (V π) []) (x : σ × Transcript) (a : Pf × PermutationTranscript) :
    Common.Duplex RState.zero keccakNFR (postBSR fix V x a) [] := by
  have h := duplex_toRHFR _ [] (hVd (fix x.1 a.1))
  exact duplex_mapR _ _ [] (by simpa using h)

theorem cost_advBSR (A : σ → OracleComp Common.RandomPermutationOracles Pf)
    (Q : ℕ) (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q)
    (x : σ × Transcript) : Common.QueryCostAtMost (advBSR A x) advCostR Q := by
  refine Common.isWeightBound_run_simulateQ logRelCR Common.permutationCallCost advCostR
    (fun t T => ?_) (hA x.1) []
  rcases t with n | q
  · exact Common.isWeightBound_map _ (Common.isWeightBound_query advCostR (.inl n))
  · simp only [logRelCR, logRelR, StateT.run_mk, relPR]
    exact Common.isWeightBound_map _ (Common.isWeightBound_map _
      (Common.isWeightBound_query advCostR (.inr (.inr (LeanVM.Rpm.mapQ rEquiv q)))))

/-- **The calls of `π` of the transfer game**: the setup's `QSπ`, the adversary's `Q`, the verifier's `QVπ`. -/
theorem cost_gameBSR (setup : OracleComp KeccakCalls σ) (hS : HOnly setup) (QSπ : ℕ)
    (hSπ : Common.QueryCostAtMost setup LeanVM.Rpm.hashBlocks QSπ) (fix : σ → Pf → Pf)
    (A : σ → OracleComp Common.RandomPermutationOracles Pf)
    (Q : ℕ) (hA : ∀ ir, Common.QueryCostAtMost (A ir) Common.permutationCallCost Q)
    (V : Pf → OracleComp KeccakCallsR β) (QVπ : ℕ) (hVπ : ∀ π, Common.QueryCostAtMost (V π) hashBlocksR QVπ) :
    Common.QueryCostAtMost (gameBSR setup fix A V)
      (Common.queryCost2 (Dg := RateBytes) keccakPaddingR) (QSπ + Q + QVπ) := by
  have h : Common.QueryCostAtMost (gameBSR setup fix A V) gameCostR (QSπ + (Q + QVπ)) := by
    rw [gameBSR, Common.rpmGame2, preBSR,
      hEmbed2_toRHR (loggedKC setup) (Compose.hOnly_loggedKC_run setup hS [])]
    refine (isWeightBound_hfEmbed_toRHFR (cost_liftR (Compose.cost_loggedKC setup QSπ hSπ []))).bind
      fun x => ?_
    refine (isWeightBound_advEmbedR (cost_advBSR A Q hA x)).bind fun a => ?_
    rw [postBSR, simulateQ_map]
    exact Common.isWeightBound_map _ (isWeightBound_hfEmbed_toRHFR (hVπ _))
  exact h.mono (by omega)

end UniKeccakSound.Rec4
