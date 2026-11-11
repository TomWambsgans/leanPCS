-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from the previous protocol's `E2ECompleteness/Assemble.lean`, `Final.lean`, `Done.lean`. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the duplex
-- discipline `DuplexVm` and the block cost `hashBlocks`.
import E2ECompleteness.PcsAccept
import E2ECompleteness.PcsEnd
import E2ECompleteness.PcsHashLen
import E2ECompleteness.PcsDuplex
import E2ECompleteness.PcsCost
import E2ECompleteness.PcsClaims

/-!
# `PcsQuotient.Completeness`, end to end (the PCS claims)

`deployedStaged4 stmt w` is the `Staged4` of `PcsEnd.lean` for the Statement's experiment: the raw coins
(`rawDist`), and for each draw the stages of `PcsStaging.lean` on the deployed circuit, the degenerate quadruples
`badSet` (`PcsAccept.lean`). Its `Holds`: the experiment (`completenessExperiment_eq_expH`, `expH_eq_staged`), the
duplex discipline (`duplexVm_stagedRun`), the block count (`hcost_deployed`), the hash lengths
(`hashOK_stageAG`, `hashOK_stageBG`, `hashOK_stageCG`), the density (`badSet_density`) and the grinding
(`rejectGood_of_tail`, from (Acc) and (Red), `tailAccepts`, `tailReduces`, given the honest tables' claims
`HonestClaims`). **`completeness_of_honestClaims`**: `PcsQuotient.Completeness deltaPcs` from `HonestClaims`, and
**`E2ECompleteness.completeness_end`**: `PcsQuotient.Completeness deltaPcs` with no hypothesis (`honestClaims`,
`PcsClaims.lean`), `deltaPcs < 2^-163` (`deltaPcs_lt`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash
open LeanVM.Prover (Tree)
open PcsQuotient
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-- **The deployed experiment's stages.** -/
noncomputable def deployedStaged4 (stmt : Statement) (w : Secret) : Staged4 where
  Coins := RawCoins
  α := AuxA
  β := AuxB
  γ := AuxC
  coins := rawDist
  bad c := badSet w (coinsOf c)
  A c := stageAG (setupWithH callKeccak256) (membership logRows) (cellsOf w) (coinsOf c) stmt
  B c := stageBG (membership logRows) (cellsOf w) (coinsOf c)
  C c := stageCG (membership logRows) (cellsOf w) (coinsOf c) stmt
  D c := stageDG (membership logRows) (cellsOf w) (coinsOf c) nonceFuel logRows stmt

theorem deployedStaged4_run (stmt : Statement) (w : Secret) (c : RawCoins) :
    (deployedStaged4 stmt w).run c = stagedRun stmt w (coinsOf c) := rfl

theorem deployedStaged4_experiment (stmt : Statement) (w : Secret) :
    completenessExperiment stmt w =ᵈ ((deployedStaged4 stmt w).coins >>= fun c ↦ (fun z ↦ z.1) <$>
      (simulateQ keccakCallsOverRandomPermutation ((deployedStaged4 stmt w).run c)).run' []) := by
  refine (completenessExperiment_eq_expH stmt w).trans ?_
  have e : (fun c ↦ (simulateQ keccakCallsOverRandomPermutation (expH stmt w (coinsOf c))).run' []) =
      fun c ↦ (fun z ↦ z.1) <$>
        (simulateQ keccakCallsOverRandomPermutation ((deployedStaged4 stmt w).run c)).run' [] := by
    funext c
    rw [expH_eq_staged, deployedStaged4_run, simulateQ_map, StateT.run'_eq, StateT.run'_eq,
      StateT.run_map, Functor.map_map, Functor.map_map]
  rw [e]
  rfl

/-- **`Staged4.Holds` for the deployed experiment**, from the honest tables' claims. -/
theorem deployedStaged4_holds (hC : HonestClaims) (stmt : Statement) (w : Secret)
    (hrel : Relation stmt w) :
    (deployedStaged4 stmt w).Holds stmt w (2 ^ 48) ((19 * 2 ^ 24 + 31 : ℝ≥0∞) / 2 ^ 192)
      ((2 : ℝ≥0∞)⁻¹ ^ 304) where
  experiment := deployedStaged4_experiment stmt w
  duplex c := duplexVm_stagedRun stmt w (coinsOf c)
  cost c := hcost_deployed stmt w (coinsOf c)
  hashA _ := hashOK_stageAG _ hashOK_setupWithH _ _ _ _
  hashB _ := hashOK_stageBG _ _ _
  hashC _ := hashOK_stageCG _ _ _ _
  density c := badSet_density w (coinsOf c)
  rejectGood c := rejectGood_of_tail badSet hcost_deployed
    (fun stmt w hrel coins ↦ tailAccepts hC stmt w hrel coins)
    (fun stmt w hrel coins ↦ tailReduces hC stmt w hrel coins) stmt w hrel (coinsOf c)

/-- **`PcsQuotient.Completeness deltaPcs`** from the honest tables' claims. -/
theorem completeness_of_honestClaims (hC : HonestClaims) : PcsQuotient.Completeness deltaPcs :=
  completeness_of_staged4 fun stmt w hrel ↦ ⟨deployedStaged4 stmt w, deployedStaged4_holds hC stmt w hrel⟩

end E2ECompleteness.Pcs

namespace E2ECompleteness

/-- **End-to-end completeness** of the membership proof on the EIP's PCS claims: `PcsQuotient.Completeness
deltaPcs`, with no hypothesis, `deltaPcs = (19 · 2^24 + 31) / 2^192 + 2^-304 + (2^48)² / 2^508 < 2^-163`
(`Pcs.deltaPcs_lt`). -/
theorem completeness_end : PcsQuotient.Completeness Pcs.deltaPcs :=
  Pcs.completeness_of_honestClaims Pcs.honestClaims

end E2ECompleteness

/-- info: 'E2ECompleteness.completeness_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_end

/-- info: 'E2ECompleteness.Pcs.deltaPcs_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.deltaPcs_lt
