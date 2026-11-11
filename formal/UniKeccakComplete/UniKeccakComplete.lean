-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniKeccakComplete.Chain
import UniKeccakComplete.Staged
import UniKeccakComplete.End
import UniKeccakComplete.K.EndClosed
import UniKeccakComplete.K.Rec4End

/-!
# UniKeccakComplete: completeness of the Keccak VM's univariate verifier

`UniKeccak.UniCompletenessKeccak`, `UniCompletenessKeccakRec3` and `UniCompletenessKeccakRec4` at the Keccak-f block,
`deltaK < 2^-169`, for the explicit Lean honest provers (`K/`: the placed trace, the bus, the quotients, the batch,
Flock's prover on the Keccak-f block, three WHIR openings; π1-rec4's wide draws), closed at the reference shape
(`K/EndClosed.lean`, `K/Rec4End.lean`). See `README.md`.
-/

/-- info: 'UniKeccakComplete.uniCompletenessKeccak_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.uniCompletenessKeccak_closed

/-- info: 'UniKeccakComplete.uniCompletenessKeccakRec3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.uniCompletenessKeccakRec3_closed

/-- info: 'UniKeccakComplete.uniCompletenessKeccakRec4_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.uniCompletenessKeccakRec4_closed

/-- info: 'UniKeccakComplete.Rec4.honest_openings4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.honest_openings4

/-- info: 'UniKeccakComplete.Prob.deltaK_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.deltaK_lt

/-- info: 'UniKeccakComplete.Prob.uniCompletenessKeccak_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.uniCompletenessKeccak_end

/-- info: 'UniKeccakComplete.Prob.uniCompletenessKeccakRec3_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.uniCompletenessKeccakRec3_end

/-- info: 'UniKeccakComplete.Prob.uniCompletenessKeccak_of_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Prob.uniCompletenessKeccak_of_staged

/-- info: 'UniKeccakComplete.Rec3.uniCompletenessKeccakRec3_of_staged3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.uniCompletenessKeccakRec3_of_staged3
