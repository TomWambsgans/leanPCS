-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniKeccakSound.FlockInterfaceK
import UniKeccakSound.PiopK
import UniKeccakSound.PiopSoundK
import UniKeccakSound.FsK
import UniKeccakSound.FinalK

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
