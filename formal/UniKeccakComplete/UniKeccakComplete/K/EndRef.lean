-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Follows `formal/UniComplete/UniComplete/Prob.lean`'s `uniCompleteness_reference` and `Rec3Prob.lean`'s
-- `uniCompletenessRec3_reference` at the Keccak verifier's reference shape.
import UniKeccakComplete.K.Rec3ProbK
import UniKeccakComplete.K.FlockCost
import UniKeccakComplete.K.Rec3ProverCost
import UniKeccakComplete.K.Rec3ProverSim
import UniKeccakComplete.K.Rec3ProverDuplex
import UniKeccakComplete.K.BadFpCount
import UniKeccakComplete.K.ProbBadT
import UniKeccakComplete.K.ProbTFresh
import UniKeccakComplete.K.Rec3ProbTFresh

/-!
# Completeness of the Keccak verifier at the reference shape, from the core's hypotheses

At the reference shape (`UniKeccakSound.keccakRefShape`, 128 signatures) and a program IV of at most `2^16` bytes, for
Flock's honest prover on the Keccak-f block (`flockProveH`), the prover-side and cost hypotheses of `ProbK.lean` and
`Rec3ProbK.lean` are discharged: Flock's commutation (`flockCommutes_flockProveH`), the setup's, the prover's (`2^47`)
and the verifier's block counts, the streams (`2^14` bytes), their total below `2^48` (`totalCostK_le`,
`totalCostK3_le`), π1-rec3's prover's commutation and discipline, the bad sets' counts (`badFpCard_keccakRef`,
`badTCard_reference`) and `t`'s freshness (`tQueryFresh_reference`, `tQueryFresh3_reference`). What is left is the
deterministic core (`CoreAccepts`, `CoreFailsOnlyAtPow`, resp. `CoreAccepts3`, `CoreFailsOnlyAtPow3`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open UniStatement UniKeccak
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete

open Prob (CoreAccepts CoreFailsOnlyAtPow BadFpCard BadTCard TQueryFresh deltaK uniProverRP)
open Rec3 (CoreAccepts3 CoreFailsOnlyAtPow3 TQueryFresh3 uniProverRec3RP)

/-- **Completeness of the Keccak verifier (main line) at the reference shape**, `deltaK < 2^-169`, from the core's
named hypotheses. -/
theorem uniCompletenessKeccak_ref (D : KDeployment) (hD : D.shape = UniKeccakSound.keccakRefShape)
    (hiv : D.programIv.length ≤ 2 ^ 16) (hpiv : 32 ≤ D.programIv.length) (hacc : CoreAccepts D flockProveH)
    (hpow : CoreFailsOnlyAtPow D flockProveH) :
    UniCompletenessKeccak KeccakFlock.keccakFlockSpec D (uniProverRP flockProveH D) deltaK :=
  Prob.uniCompletenessKeccak_of_core flockProveH D flockCommutes_flockProveH (Cost.cost_setupTreeKWithH D)
    (fun roots input π h ↦ Cost.cost_verifierWithH_main D roots input π _ h)
    (Prob.proverCost_flockProveH D hD hiv) (Prob.proverStreamSize_flockProveH D hD) (totalCostK_le D hD hiv)
    hacc hpow (BadFp.badFpCard_keccakRef_22 D hD) (hD ▸ Prob.badTCard_keccakRef_15) (Prob.tQueryFresh_reference D hD hpiv) hpiv

/-- **Completeness of the Keccak π1 at π1-rec3's shape, at the reference shape**, `deltaK < 2^-169`, from the core's
named hypotheses. -/
theorem uniCompletenessKeccakRec3_ref (D : KDeployment) (hD : D.shape = UniKeccakSound.keccakRefShape)
    (hiv : D.programIv.length ≤ 2 ^ 16) (hpiv : 32 ≤ D.programIv.length) (hacc : CoreAccepts3 D flockProveH)
    (hpow : CoreFailsOnlyAtPow3 D flockProveH) :
    UniCompletenessKeccakRec3 KeccakFlock.keccakFlockSpec D (uniProverRec3RP flockProveH D) deltaK :=
  Rec3.uniCompletenessKeccakRec3_of_core flockProveH D flockCommutes_flockProveH
    (fun impl input rows q ↦ Rec3.simulateQ_rec3_flockProveH impl D input rows q)
    (fun input rows q _ _ ↦ Rec3.disc_rec3_flockProveH D input rows q) (Cost.cost_setupTreeKWithH D)
    (fun input rows q hfit hrel ↦ Rec3.cost_rec3_flockProveH D hD hiv input rows q hfit hrel)
    (fun input rows q hfit hrel π hπ ↦ Rec3.streamSize_rec3_flockProveH D hD input rows q hfit hrel π hπ)
    (fun roots input π h ↦ Cost.cost_verifierWithH_rec3 D roots input π _ h) (totalCostK3_le D hD hiv)
    hacc hpow (BadFp.badFpCard_keccakRef_22 D hD) (hD ▸ Prob.badTCard_keccakRef_15) (Rec3.tQueryFresh3_reference D hD hpiv) hpiv

end UniKeccakComplete

/-- info: 'UniKeccakComplete.uniCompletenessKeccak_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.uniCompletenessKeccak_ref

/-- info: 'UniKeccakComplete.uniCompletenessKeccakRec3_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.uniCompletenessKeccakRec3_ref
