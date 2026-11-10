-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Follows `formal/UniComplete/UniComplete/Rec3Prob.lean` (`stagedU3_holds`, `uniCompletenessRec3_of_core`) at the
-- Keccak verifier's π1-rec3 shape. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the proof-of-work miss probability `missProb`, `rpmError`.
import UniKeccakComplete.K.Rec3ProbGrind
import UniKeccakComplete.K.ProbK

/-!
# Completeness of the Keccak verifier at π1-rec3's shape, from the named hypotheses

π1-rec3 draws **two** chained bus answers after `C1`'s root (`c`, with `α = (c, c², c⁴, c⁸)`, then `β`; then `γ`, and
Flock's first coordinate, then Flock's coset values are absorbed), so the staged premise `KStagedK` of
`UniKeccakComplete/End.lean` (five chained answers, the main line's) cannot describe its experiment: the fifth
answer would be a query the experiment never makes. The staged form here is `Rec3.KStaged3` (`Rec3ProbStaged.lean`,
two chained answers), whose bound has no `6 / 2^256` term:

  `δ₃ = (2^22 − 1)/2^192 + (2^15/2^192 + 2^-200) + 2^-304 + rpmError (2^48) ≤ deltaK` (`delta3_le_deltaK`).

**`uniCompletenessKeccakRec3_of_core`**: `UniCompletenessKeccakRec3 keccakFlockSpec D (uniProverRec3RP flock D)
deltaK` from Flock's prover's commutation (`FlockCommutes`, giving `FlockSimCommutes`), π1-rec3's prover's commutation
and discipline (`ProverCommutes3`, `ProverDuplex3`), the block counts (setup `Ns`, prover `NP`, verifier `NV` on
streams of at most `S` bytes, `Ns + (NP + NV) ≤ 2^48`), the deterministic core (`CoreAccepts3`,
`CoreFailsOnlyAtPow3`), the bad sets' counts (the main line's `BadFpCard`, `BadTCard`) and `t`'s freshness
(`TQueryFresh3`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile.Rom (missProb)
open UniStatement UniKeccak
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Rec3

open UniKeccakComplete.Prob (FlockSimCommutes BadFpCard BadTCard BadT flockSimCommutes_of_commutes deltaK)

variable (flock : FlockProverH) (D : KDeployment)

/-- **π1-rec3's staged run's conditions at `deltaK`'s numbers**, from the named hypotheses. -/
theorem stagedU3_holds {Ns NP S NV : ℕ} (hc : ProverCommutes3 flock D) (hf : FlockSimCommutes flock)
    (hdup : ProverDuplex3 flock D)
    (hset : Common.QueryCostAtMost (setupTreeKWithH callKeccak256 callKeccakF1600 D) hashBlocks Ns)
    (hcost : ProverCost3 flock D NP) (hstream : ProverStreamSize3 flock D S) (hvcost : VerifierCost3 D S NV)
    (htot : Ns + (NP + NV) ≤ 2 ^ 48) (hacc : CoreAccepts3 D flock) (hpow : CoreFailsOnlyAtPow3 D flock)
    (hbad : BadFpCard D (2 ^ 22 - 1)) (hbadT : BadTCard D.shape (2 ^ 15))
    (htf : TQueryFresh3 flock D ((2 : ℝ≥0∞)⁻¹ ^ 200)) (hpiv : 32 ≤ D.programIv.length)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    (stagedU3 flock D input rows q).Holds D (uniProverRec3RP flock D) input rows q
      (BadFp (honestTrace D input rows q)) (BadT D.shape) (2 ^ 22 - 1) (2 ^ 15) (2 ^ 48)
      ((2 : ℝ≥0∞)⁻¹ ^ 200) ((2 : ℝ≥0∞)⁻¹ ^ 304) := by
  have hQ := cost_stagedU3 flock D hset hcost hstream hvcost input rows q hfit hrel
  refine ⟨experiment_staged3 flock D hc input rows q, duplexVm_stagedU3 flock D hdup input rows q hfit hrel,
    hQ.mono htot, fun a ↦ Prob.firstInput_length hfit.1 a.2, hashA_stagedU3 flock D hpiv input rows q,
    hbad input rows q hfit hrel, hbadT, htf input rows q hfit hrel, ?_⟩
  refine (rejectGood3 flock D hc hf hacc hpow input rows q hfit hrel hQ).trans ?_
  calc ((Ns + (NP + NV) : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel
      ≤ ((2 ^ 48 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel := by
        gcongr
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 304 := E2ECompleteness.grinding_le

/-- **π1-rec3's bound is at most `deltaK`** (it lacks the main line's `6 / 2^256`). -/
theorem delta3_le_deltaK :
    ((2 ^ 22 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (((2 ^ 15 : ℕ) : ℝ≥0∞) / 2 ^ 192 + (2 : ℝ≥0∞)⁻¹ ^ 200) +
      (2 : ℝ≥0∞)⁻¹ ^ 304 + rpmError (2 ^ 48) ≤ deltaK := by
  unfold deltaK
  gcongr
  exact le_self_add

/-- **Completeness of the Keccak π1 at π1-rec3's shape**, `deltaK < 2^-169`, from the named hypotheses. -/
theorem uniCompletenessKeccakRec3_of_core {Ns NP S NV : ℕ} (hflock : FlockCommutes flock)
    (hc : ProverCommutes3 flock D) (hdup : ProverDuplex3 flock D)
    (hset : Common.QueryCostAtMost (setupTreeKWithH callKeccak256 callKeccakF1600 D) hashBlocks Ns)
    (hcost : ProverCost3 flock D NP) (hstream : ProverStreamSize3 flock D S) (hvcost : VerifierCost3 D S NV)
    (htot : Ns + (NP + NV) ≤ 2 ^ 48) (hacc : CoreAccepts3 D flock) (hpow : CoreFailsOnlyAtPow3 D flock)
    (hbad : BadFpCard D (2 ^ 22 - 1)) (hbadT : BadTCard D.shape (2 ^ 15))
    (htf : TQueryFresh3 flock D ((2 : ℝ≥0∞)⁻¹ ^ 200)) (hpiv : 32 ≤ D.programIv.length) :
    UniCompletenessKeccakRec3 KeccakFlock.keccakFlockSpec D (uniProverRec3RP flock D) deltaK := by
  have h := uniCompletenessKeccakRec3_of_staged3 (F := KeccakFlock.keccakFlockSpec) (D := D)
    (P := uniProverRec3RP flock D) fun input rows q hfit hrel ↦
      ⟨stagedU3 flock D input rows q, _, _,
        stagedU3_holds flock D hc (flockSimCommutes_of_commutes hflock) hdup hset hcost hstream hvcost htot hacc
          hpow hbad hbadT htf hpiv input rows q hfit hrel⟩
  exact fun input rows q hfit hrel ↦ (h input rows q hfit hrel).trans delta3_le_deltaK

end UniKeccakComplete.Rec3

/-- info: 'UniKeccakComplete.Rec3.uniCompletenessKeccakRec3_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.uniCompletenessKeccakRec3_of_core
