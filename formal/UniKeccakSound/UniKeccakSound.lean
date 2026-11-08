-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniKeccakSound.FlockInterfaceK
import UniKeccakSound.PiopK
import UniKeccakSound.PiopSoundK
import UniKeccakSound.FsK
import UniKeccakSound.FinalK
import UniKeccakSound.PiopK3
import UniKeccakSound.PiopSoundK3
import UniKeccakSound.FinalK3
import UniKeccakSound.EndK
import UniKeccakSound.EndRefK
import UniKeccakSound.EndClosedK

/-!
# UniKeccakSound: knowledge soundness of the Keccak VM's univariate verifier

See `README.md`.
-/

/-- info: 'UniKeccakSound.uniPiopK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniPiopK

/-- info: 'UniKeccakSound.uniKnowledgeSoundnessK_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniKnowledgeSoundnessK_bits

/-- info: 'UniKeccakSound.uniPiopK3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniPiopK3

/-- info: 'UniKeccakSound.uniKnowledgeSoundnessK3_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniKnowledgeSoundnessK3_bits

/-- info: 'UniKeccakSound.uniKnowledgeSoundnessKeccak_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniKnowledgeSoundnessKeccak_of

/-- info: 'UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_of

/-- info: 'UniKeccakSound.uniKnowledgeSoundnessKeccak_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniKnowledgeSoundnessKeccak_ref

/-- info: 'UniKeccakSound.uniKnowledgeSoundnessKeccak_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniKnowledgeSoundnessKeccak_closed

/-- info: 'UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_closed
