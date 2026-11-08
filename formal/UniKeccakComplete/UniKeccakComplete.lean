-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniKeccakComplete.Chain
import UniKeccakComplete.Staged
import UniKeccakComplete.End

/-!
# UniKeccakComplete: completeness of the Keccak VM's univariate verifier

`UniKeccak.UniCompletenessKeccak` and `UniCompletenessKeccakRec3` at the Keccak-f block, `deltaK < 2^-163`, from the
staged premise `KStagedK` (`End.lean`); the probability layer (`Staged.lean`, `Chain.lean`). See `README.md`.
-/

/-- info: 'UniKeccakComplete.Prob.uniCompletenessKeccak_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.uniCompletenessKeccak_end

/-- info: 'UniKeccakComplete.Prob.uniCompletenessKeccakRec3_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.uniCompletenessKeccakRec3_end

/-- info: 'UniKeccakComplete.Prob.uniCompletenessKeccak_of_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.uniCompletenessKeccak_of_staged

/-- info: 'UniKeccakComplete.Prob.deltaK_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.deltaK_lt
