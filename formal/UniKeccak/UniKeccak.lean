-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
module

public import UniKeccak.Terminal
public import UniKeccak.Walk
public import UniKeccak.Verifier
public import UniKeccak.Opening
public import UniKeccak.Mapping
public import UniKeccak.Security

/-!
# UniKeccak: the univariate verifier for the Keccak VM

`Blake2s::Keccak`'s verifier (`crates/leanvm_univariate/src/verifier.rs`, `KECCAK.md`) transcribed as computable Lean
(`reduceWithK`, `runK`, `verifyWithK`: the main line `keccakMain` and π1-rec3's shape `keccakRec3`), and its end
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

/-- info: 'UniKeccak.pcsCallsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccak.pcsCallsK

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
