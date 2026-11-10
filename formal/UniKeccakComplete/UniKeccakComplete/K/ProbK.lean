-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Follows `formal/UniComplete/UniComplete/Prob.lean` (`stagedU_holds`, `uniCompleteness_of_core`,
-- `uniCompleteness_reference`) at the Keccak verifier's staged premise (`UniKeccakComplete/Staged.lean`, `End.lean`).
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the proof-of-work miss probability `missProb`.
import UniKeccakComplete.K.ProbGrind
import UniKeccakComplete.End

/-!
# The Keccak verifier's staged premise (main line), from the named hypotheses

**`kStagedK_of_core`**: `KStagedK D keccakMain (uniProverRP flock D)` (the premise of `uniCompletenessKeccak_end`, at
`deltaK`'s numbers: `Nbad = 2^28 − 1`, `ct = 3 · 2^17`, `N = 2^48`, `εt = 2^-200`, `εpow = 2^-304`) from:

* Flock's prover's commutation `FlockCommutes flock` (giving `ProverCommutes`, `ProverDuplex`, `FlockSimCommutes`);
* the block counts: the setup's `Ns`, the prover's `NP` (`ProverCost`), the verifier's `Nv` on streams of at most `S`
  bytes (`ProverStreamSize S`), with `Ns + (NP + Nv) ≤ 2^48`;
* the deterministic core `CoreAccepts`, `CoreFailsOnlyAtPow`;
* the bad sets' counts `BadFpCard D (2^28 − 1)`, `BadTCard D.shape (3 · 2^17)`, and `t`'s freshness
  `TQueryFresh flock D 2^-200`.

The staged run is `stagedU` (`ProbExp.lean`); its conditions are `experiment_staged`, `duplexVm_stagedU`,
`cost_stagedU`, `firstInput_length`, `hashA_stagedU`, `rejectGood_uni`, as in `UniComplete`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile.Rom (missProb)
open UniStatement UniKeccak
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Prob

open UniComplete

variable (flock : FlockProverH) (D : KDeployment)

/-- **The staged run's conditions at `deltaK`'s numbers**, from the named hypotheses. -/
theorem stagedU_holds {Ns NP S Nv : ℕ} (hc : ProverCommutes flock D) (hf : FlockSimCommutes flock)
    (hdup : ProverDuplex flock D)
    (hset : Common.QueryCostAtMost (setupTreeKWithH callKeccak256 callKeccakF1600 D) hashBlocks Ns)
    (hver : ∀ roots input (π : KeccakProof), π.stream.size ≤ S →
      Common.QueryCostAtMost (KDeployment.verifierWithH callKeccak256 callKeccakF1600 D keccakMain roots input π)
        hashBlocks Nv)
    (hcost : ProverCost flock D NP) (hstream : ProverStreamSize flock D S) (htot : Ns + (NP + Nv) ≤ 2 ^ 48)
    (hacc : CoreAccepts D flock) (hpow : CoreFailsOnlyAtPow D flock) (hbad : BadFpCard D (2 ^ 22 - 1))
    (hbadT : BadTCard D.shape (2 ^ 15)) (htf : TQueryFresh flock D ((2 : ℝ≥0∞)⁻¹ ^ 200)) (hpiv : 32 ≤ D.programIv.length)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    (stagedU flock D input rows q).Holds D keccakMain (uniProverRP flock D) input rows q
      (BadFp (honestTrace D input rows q)) (BadT D.shape) (2 ^ 22 - 1) (2 ^ 15) (2 ^ 48)
      ((2 : ℝ≥0∞)⁻¹ ^ 200) ((2 : ℝ≥0∞)⁻¹ ^ 304) := by
  have hQ := cost_stagedU flock D hset hver hcost hstream input rows q hfit hrel
  refine ⟨experiment_staged flock D hc input rows q, ?_⟩
  refine ⟨duplexVm_stagedU flock D hdup input rows q hfit hrel, hQ.mono htot, fun a ↦ firstInput_length hfit.1 a.2,
    hashA_stagedU flock D hpiv input rows q, hbad input rows q hfit hrel, hbadT, htf input rows q hfit hrel, ?_⟩
  refine (rejectGood_uni flock D hc hf hacc hpow input rows q hfit hrel hQ).trans ?_
  calc ((Ns + (NP + Nv) : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel
      ≤ ((2 ^ 48 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel := by
        gcongr
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 304 := E2ECompleteness.grinding_le

/-- **The Keccak verifier's staged premise (main line)**, from the named hypotheses. -/
theorem kStagedK_of_core {Ns NP S Nv : ℕ} (hflock : FlockCommutes flock)
    (hset : Common.QueryCostAtMost (setupTreeKWithH callKeccak256 callKeccakF1600 D) hashBlocks Ns)
    (hver : ∀ roots input (π : KeccakProof), π.stream.size ≤ S →
      Common.QueryCostAtMost (KDeployment.verifierWithH callKeccak256 callKeccakF1600 D keccakMain roots input π)
        hashBlocks Nv)
    (hcost : ProverCost flock D NP) (hstream : ProverStreamSize flock D S) (htot : Ns + (NP + Nv) ≤ 2 ^ 48)
    (hacc : CoreAccepts D flock) (hpow : CoreFailsOnlyAtPow D flock) (hbad : BadFpCard D (2 ^ 22 - 1))
    (hbadT : BadTCard D.shape (2 ^ 15)) (htf : TQueryFresh flock D ((2 : ℝ≥0∞)⁻¹ ^ 200)) (hpiv : 32 ≤ D.programIv.length) :
    KStagedK D keccakMain (uniProverRP flock D) := fun input rows q hfit hrel ↦
  ⟨stagedU flock D input rows q, _, _,
    stagedU_holds flock D (proverCommutes_of_flock hflock D) (flockSimCommutes_of_commutes hflock)
      (proverDuplex_of_flock hflock D) hset hver hcost hstream htot hacc hpow hbad hbadT htf hpiv input rows q hfit hrel⟩

/-- **Completeness of the Keccak verifier (main line)**, `deltaK < 2^-169`, from the named hypotheses. -/
theorem uniCompletenessKeccak_of_core {Ns NP S Nv : ℕ} (hflock : FlockCommutes flock)
    (hset : Common.QueryCostAtMost (setupTreeKWithH callKeccak256 callKeccakF1600 D) hashBlocks Ns)
    (hver : ∀ roots input (π : KeccakProof), π.stream.size ≤ S →
      Common.QueryCostAtMost (KDeployment.verifierWithH callKeccak256 callKeccakF1600 D keccakMain roots input π)
        hashBlocks Nv)
    (hcost : ProverCost flock D NP) (hstream : ProverStreamSize flock D S) (htot : Ns + (NP + Nv) ≤ 2 ^ 48)
    (hacc : CoreAccepts D flock) (hpow : CoreFailsOnlyAtPow D flock) (hbad : BadFpCard D (2 ^ 22 - 1))
    (hbadT : BadTCard D.shape (2 ^ 15)) (htf : TQueryFresh flock D ((2 : ℝ≥0∞)⁻¹ ^ 200)) (hpiv : 32 ≤ D.programIv.length) :
    UniCompletenessKeccak KeccakFlock.keccakFlockSpec D (uniProverRP flock D) deltaK :=
  uniCompletenessKeccak_end D _
    (kStagedK_of_core flock D hflock hset hver hcost hstream htot hacc hpow hbad hbadT htf hpiv)

end UniKeccakComplete.Prob

/-- info: 'UniKeccakComplete.Prob.uniCompletenessKeccak_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.uniCompletenessKeccak_of_core
