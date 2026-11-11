-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from the previous protocol's `E2ECompleteness/Assemble.lean`, `Final.lean`, `Done.lean`. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the duplex
-- discipline `DuplexVm`, the block cost `hashBlocks` and `rpmError`.
import E2ECompleteness.PcsAccept
import E2ECompleteness.PcsEnd
import E2ECompleteness.PcsHashLen
import E2ECompleteness.PcsDuplex
import E2ECompleteness.PcsCost
import E2ECompleteness.PcsHBad

/-!
# `PcsQuotient.Completeness`, end to end (the deployed protocol)

`deployedStaged4 stmt w` is the `Staged4` of `PcsEnd.lean` for the Statement's experiment: the raw coins
(`rawDist`), and for each draw the stages of `PcsStaging.lean` on the deployed circuit, the degenerate quadruples
`H.badSet` (`PcsHHonest.lean`). Its `Holds`: the experiment (`completenessExperiment_eq_expH`, `expH_eq_staged`),
the duplex discipline (`duplexVm_stagedRun`), the block count (`hcost_deployed`), the hash lengths (`hashOK_stageAG`,
`hashOK_stageBG`, `hashOK_stageCG`), the density (`H.badSet_density`) and the grinding (`rejectGood_of_tail`, from
(Acc) and (Red), `tailAccepts`, `tailReduces`, given the honest tables' claims `H.honestClaims_badSet`).

**`E2ECompleteness.completeness_end`**: `PcsQuotient.Completeness deltaPcs` given the evaluated check on the wiring
table `H.WiringCheck`, `deltaPcs = (7 · 2^24 + 3) / 2^192 + 2 / 2^256 + 2^-304 + (2^48)² / 2^508 < 2^-163`
(`deltaPcs_lt`; about `2^-164.9`).
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
  bad c := H.badSet w (coinsOf c)
  A c := stageAG (setupWithH callKeccak256) (membership logRows) (cellsOf w) (coinsOf c) stmt
  B c := stageBG (membership logRows) (cellsOf w) (coinsOf c) stmt
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

/-- **`Staged4.Holds` for the deployed experiment**, given the evaluated check on the wiring table. -/
theorem deployedStaged4_holds (hW : H.WiringCheck) (stmt : Statement) (w : Secret) (hrel : Relation stmt w) :
    (deployedStaged4 stmt w).Holds stmt w (2 ^ 48) ((7 * 2 ^ 24 + 3 : ℝ≥0∞) / 2 ^ 192)
      ((2 : ℝ≥0∞)⁻¹ ^ 304) where
  experiment := deployedStaged4_experiment stmt w
  duplex c := duplexVm_stagedRun stmt w (coinsOf c)
  cost c := hcost_deployed stmt w (coinsOf c)
  hashA _ := hashOK_stageAG _ hashOK_setupWithH _ _ _ _
  hashB _ := hashOK_stageBG _ _ _ _
  hashC _ := hashOK_stageCG _ _ _ _
  density c := H.badSet_density hW w (coinsOf c)
  rejectGood c := rejectGood_of_tail H.badSet hcost_deployed
    (fun stmt w hrel coins ↦ tailAccepts H.badSet H.honestClaims_badSet stmt w hrel coins)
    (fun stmt w hrel coins ↦ tailReduces H.badSet H.honestClaims_badSet stmt w hrel coins) stmt w hrel (coinsOf c)

/-! ## The number -/

/-- **The deployed bound**: degenerate challenges `(7 · 2^24 + 3) / 2^192`, the two repeated challenge inputs
`2 / 2^256`, the proofs of work `2^-304`, the transfer at `2^48` block calls. -/
noncomputable def deltaPcs : ℝ≥0∞ :=
  (7 * 2 ^ 24 + 3 : ℝ≥0∞) / 2 ^ 192 + 2 / 2 ^ 256 + (2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48)

theorem deltaPcs_lt : deltaPcs < (2 : ℝ≥0∞)⁻¹ ^ 163 := by
  have h1 : (7 * 2 ^ 24 + 3 : ℝ≥0∞) / 2 ^ 192 ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ 166 := by
    calc (7 * 2 ^ 24 + 3 : ℝ≥0∞) / 2 ^ 192 ≤ (2 * 2 ^ 26) / 2 ^ 192 := by
          gcongr; norm_num
      _ = 2 * (2 ^ 26 * (2 : ℝ≥0∞)⁻¹ ^ (166 + 26)) := by
          rw [← ENNReal.inv_pow, mul_div_assoc, div_eq_mul_inv]
      _ = 2 * (2 : ℝ≥0∞)⁻¹ ^ 166 := by rw [E2ECompleteness.two_pow_mul_inv_pow]
  have h0 : (2 : ℝ≥0∞) / 2 ^ 256 ≤ (2 : ℝ≥0∞)⁻¹ ^ 166 := by
    calc (2 : ℝ≥0∞) / 2 ^ 256 = 2 ^ 1 * (2 : ℝ≥0∞)⁻¹ ^ (255 + 1) := by
          rw [← ENNReal.inv_pow, pow_one, div_eq_mul_inv]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 255 := E2ECompleteness.two_pow_mul_inv_pow 1 255
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 166 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have h2 : (2 : ℝ≥0∞)⁻¹ ^ 304 ≤ (2 : ℝ≥0∞)⁻¹ ^ 166 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have h3 : rpmError (2 ^ 48) ≤ (2 : ℝ≥0∞)⁻¹ ^ 166 := by
    calc rpmError (2 ^ 48) = 2 ^ (48 * 2) * (2 : ℝ≥0∞)⁻¹ ^ (412 + 48 * 2) := by
          rw [rpmError, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ENNReal.div_eq_inv_mul,
            ← ENNReal.inv_pow, mul_comm]
      _ = (2 : ℝ≥0∞)⁻¹ ^ 412 := E2ECompleteness.two_pow_mul_inv_pow _ 412
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 166 := E2ECompleteness.inv_pow_le_inv_pow (by norm_num)
  have hsum : deltaPcs ≤ 5 * (2 : ℝ≥0∞)⁻¹ ^ 166 := by
    unfold deltaPcs
    calc _ ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ 166 + (2 : ℝ≥0∞)⁻¹ ^ 166 + (2 : ℝ≥0∞)⁻¹ ^ 166 + (2 : ℝ≥0∞)⁻¹ ^ 166 :=
          add_le_add (add_le_add (add_le_add h1 h0) h2) h3
      _ = 5 * (2 : ℝ≥0∞)⁻¹ ^ 166 := by ring
  refine lt_of_le_of_lt hsum ?_
  calc 5 * (2 : ℝ≥0∞)⁻¹ ^ 166 < 2 ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ (163 + 3) := by
        rw [mul_comm 5, mul_comm ((2 : ℝ≥0∞) ^ 3)]
        exact ENNReal.mul_lt_mul_right (by simp) (by simp) (by norm_num)
    _ = (2 : ℝ≥0∞)⁻¹ ^ 163 := E2ECompleteness.two_pow_mul_inv_pow 3 163

/-- **`PcsQuotient.Completeness deltaPcs`**, given the evaluated check on the wiring table. -/
theorem completeness_of_wiringCheck (hW : H.WiringCheck) : PcsQuotient.Completeness deltaPcs :=
  completeness_of_staged4 fun stmt w hrel ↦ ⟨deployedStaged4 stmt w, deployedStaged4_holds hW stmt w hrel⟩

end E2ECompleteness.Pcs

namespace E2ECompleteness

/-- **End-to-end completeness** of the membership proof on the EIP's PCS claims: `PcsQuotient.Completeness
deltaPcs`, `deltaPcs = (7 · 2^24 + 3) / 2^192 + 2 / 2^256 + 2^-304 + (2^48)² / 2^508 < 2^-163`
(`Pcs.deltaPcs_lt`), given `WiringCheck`, the evaluated check on the deployed circuit's wiring table (its entry
`2^24 − 2` nonzero; `lake exe membership-wiring-check`). -/
theorem completeness_end (hW : Pcs.H.WiringCheck) : PcsQuotient.Completeness Pcs.deltaPcs :=
  Pcs.completeness_of_wiringCheck hW

end E2ECompleteness

/-- info: 'E2ECompleteness.completeness_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_end

/-- info: 'E2ECompleteness.Pcs.deltaPcs_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.deltaPcs_lt
