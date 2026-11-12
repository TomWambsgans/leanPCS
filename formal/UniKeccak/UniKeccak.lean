-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniKeccak.Terminal
import UniKeccak.Walk
import UniKeccak.Verifier
import UniKeccak.Opening
import UniKeccak.Pcs
import UniKeccak.Mapping
import UniKeccak.Security

/-!
# UniKeccak: the univariate verifier for the Keccak VM

π1's verifier (`crates/leanvm/univariate/src/verifier.rs`, `KECCAK.md`) transcribed as computable Lean
(`reduceWithK`, `runK`, `verifyWithK`: the main line `keccakMain` and π1-rec3's shape `keccakRec3`; its claims the
EIP's PCS claims, `pcsClaimsK`, each opened by `formal/WhirBridge`'s `pcsVerifyWithHash`), and its end
statements against the Keccak VM's relation `KeccakVm.KvHolds F` (`UniKnowledgeSoundnessKeccak`,
`UniKnowledgeSoundnessKeccakRec3`, `UniCompletenessKeccak`, `UniCompletenessKeccakRec3`), the Keccak-f block `F` a
parameter. Statements only: nothing is proved about them. See `README.md`.

The guards below check that the verifier and every statement rest on Lean's three axioms only.
-/

/-- info: 'UniKeccak.structuredTerminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.structuredTerminal

/-- info: 'UniKeccak.runK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.runK

/-- info: 'UniKeccak.verifyWithK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.verifyWithK

/-- info: 'UniKeccak.pcsClaimsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.pcsClaimsK

/-- info: 'UniKeccak.contractIvK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.contractIvK

/-- info: 'UniKeccak.uniExtractorK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.uniExtractorK

/-- info: 'UniKeccak.UniKnowledgeSoundnessKeccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.UniKnowledgeSoundnessKeccak

/-- info: 'UniKeccak.UniKnowledgeSoundnessKeccakRec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.UniKnowledgeSoundnessKeccakRec3

/-- info: 'UniKeccak.UniCompletenessKeccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.UniCompletenessKeccak

/-- info: 'UniKeccak.UniCompletenessKeccakRec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.UniCompletenessKeccakRec3

/-- info: 'UniKeccak.KeccakFlockFits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.KeccakFlockFits

/-- info: 'UniKeccak.runK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.runK4

/-- info: 'UniKeccak.verifyWithK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.verifyWithK4

/-- info: 'UniKeccak.UniKnowledgeSoundnessKeccakRec4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.UniKnowledgeSoundnessKeccakRec4

/-- info: 'UniKeccak.UniCompletenessKeccakRec4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.UniCompletenessKeccakRec4
