-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Follows `formal/UniComplete/UniComplete/End.lean` (`uniCompleteness_end`) at the Keccak verifier.
import UniKeccakComplete.K.EndRef
import UniKeccakComplete.K.Core

/-!
# Completeness of the Keccak verifier (main line), closed

At the reference shape (`UniKeccakSound.keccakRefShape`, 128 signatures) and a program IV of at most `2^16` bytes, the
honest prover `uniProverRP flockProveH D` (the Lean prover `uniProverWith` over the random permutation's two calls,
Flock's honest prover on the Keccak-f block) is rejected by the deployed Keccak verifier (`keccakMain`) with
probability at most `deltaK < 2^-169`, for every input, row counts that fit and `KvHonest` witness: `EndRef.lean`'s
theorem with the deterministic core (`Core.coreAccepts_reference`, `Core.coreFailsOnlyAtPow`).
-/

open UniKeccak
open scoped ENNReal

namespace UniKeccakComplete

/-- **Completeness of the Keccak verifier (main line)**, closed: no hypothesis beyond the deployment's shape and its
program IV's length. -/
theorem uniCompletenessKeccak_closed (D : KDeployment) (hD : D.shape = UniKeccakSound.keccakRefShape)
    (hiv : D.programIv.length ≤ 2 ^ 16) :
    UniCompletenessKeccak KeccakFlock.keccakFlockSpec D (Prob.uniProverRP flockProveH D) Prob.deltaK :=
  uniCompletenessKeccak_ref D hD hiv (Core.coreAccepts_reference D hD) (Core.coreFailsOnlyAtPow D)

end UniKeccakComplete

/-- info: 'UniKeccakComplete.uniCompletenessKeccak_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.uniCompletenessKeccak_closed
