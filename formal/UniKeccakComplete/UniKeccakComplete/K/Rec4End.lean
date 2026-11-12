-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's completeness at the reference shape:
-- `EndClosed.lean`'s `uniCompletenessKeccakRec3_closed` for π1-rec4's verifier (`KDeployment.verifierWith4`) and
-- prover (`Rec4Prover.lean`'s `uniProverRec4RP`).
import UniKeccakComplete.K.Rec4Core
import UniKeccakComplete.K.Rec4TFresh
import UniKeccakComplete.K.Rec4CostBound
import UniKeccakComplete.K.Rec4Duplex
import UniKeccakComplete.K.Rec3ProbK
import UniKeccakComplete.K.BadFpCount
import UniKeccakComplete.K.ProbBadT

/-!
# Completeness of the Keccak π1 at π1-rec4

At the reference shape (`UniKeccakSound.keccakRefShape`, 128 signatures) and a program IV of `32 … 2^16` bytes, the
honest prover `Rec4.uniProverRec4RP D` (the Lean prover `uniProverRec4With` over the random permutation: Keccak-256 and
its rate the sponge over `π`) is rejected by π1-rec4's deployed verifier (`KDeployment.verifierWith4`, `keccakRec4`)
with probability at most `deltaK < 2^-169`, for every input, row counts that fit and `KvHonest` witness
(**`uniCompletenessKeccakRec4_closed`**, no further hypothesis).

The pieces: `Rec4ProbK.uniCompletenessKeccakRec4_of_core` with the deterministic core (`Rec4.coreAccepts4_reference`,
`Rec4.coreFailsOnlyAtPow4`), the block count (`Rec4.expCost4_reference`, `2^48`), the duplex discipline
(`Rec4.expDuplex4`), the bad sets' sizes (`BadFp.badFpCard_keccakRef_22`, `Prob.badTCard_keccakRef_15`), the point
draw's freshness (`Rec4.tQueryFresh4_reference`, `2^-200`); the bound is π1-rec3's (`Rec3.delta3_le_deltaK`).
-/

open UniKeccak
open scoped ENNReal

namespace UniKeccakComplete

/-- **Completeness of the Keccak π1 at π1-rec4's shape**, at the reference shape, `deltaK < 2^-169`, given the point
draw's freshness (`TQueryFresh4` at `2^-200`). -/
theorem uniCompletenessKeccakRec4_of_tFresh (D : KDeployment) (hD : D.shape = UniKeccakSound.keccakRefShape)
    (hiv : D.programIv.length ≤ 2 ^ 16) (hpiv : 32 ≤ D.programIv.length)
    (htf : Rec4.TQueryFresh4 D ((2 : ℝ≥0∞)⁻¹ ^ 200)) :
    UniCompletenessKeccakRec4 KeccakFlock.keccakFlockSpec D (Rec4.uniProverRec4RP D) Prob.deltaK := by
  intro input rows q hfit hrel
  refine (Rec4.uniCompletenessKeccakRec4_of_core D (Rec4.coreAccepts4_reference D hD) (Rec4.coreFailsOnlyAtPow4 D)
    (Rec4.expCost4_reference D hD hiv) le_rfl (Rec4.expDuplex4 D) (BadFp.badFpCard_keccakRef_22 D hD)
    (hD ▸ Prob.badTCard_keccakRef_15) htf hiv hpiv input rows q hfit hrel).trans ?_
  exact Rec3.delta3_le_deltaK

/-- **Completeness of the Keccak π1 at π1-rec4's shape**, closed: no hypothesis beyond the deployment's shape and its
program IV's length (at least a digest's `32` bytes, at most `2^16`); `deltaK < 2^-169` (`Prob.deltaK_lt`). -/
theorem uniCompletenessKeccakRec4_closed (D : KDeployment) (hD : D.shape = UniKeccakSound.keccakRefShape)
    (hiv : D.programIv.length ≤ 2 ^ 16) (hpiv : 32 ≤ D.programIv.length) :
    UniCompletenessKeccakRec4 KeccakFlock.keccakFlockSpec D (Rec4.uniProverRec4RP D) Prob.deltaK :=
  uniCompletenessKeccakRec4_of_tFresh D hD hiv hpiv (Rec4.tQueryFresh4_reference D hD hiv hpiv)

end UniKeccakComplete

/-- info: 'UniKeccakComplete.uniCompletenessKeccakRec4_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.uniCompletenessKeccakRec4_closed

/-- info: 'UniKeccakComplete.uniCompletenessKeccakRec4_of_tFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.uniCompletenessKeccakRec4_of_tFresh
