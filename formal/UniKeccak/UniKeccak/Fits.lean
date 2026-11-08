-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniKeccak.Mapping
import KeccakFlock

/-!
# The Keccak-f block fits the verifier

`formal/KeccakFlock`'s inhabitant `KeccakFlock.keccakFlockSpec` has the port words and the constant wire the
verifier reads (`KeccakFlockFits`): input lane `l` at word `4l + 2`, output lane `l` at word `4l`, the constant at
position 64. (A non-module file: `KeccakFlock` is not a module.)
-/

namespace UniKeccak

theorem keccakFlockFits_keccakFlockSpec : KeccakFlockFits KeccakFlock.keccakFlockSpec := by
  refine ⟨fun l ↦ ?_, fun l ↦ ?_, ?_⟩ <;> decide +revert

end UniKeccak

/-- info: 'UniKeccak.keccakFlockFits_keccakFlockSpec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms UniKeccak.keccakFlockFits_keccakFlockSpec
