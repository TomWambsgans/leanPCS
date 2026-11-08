-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniKeccakSound.Ids.Remaining
import UniKeccakSound.IdsMain.Main
import UniKeccakSound.IdsMain.Constraints

/-!
# Three bridges of the Keccak identity model, discharged

* `MainOfPolysK D Fl` (`mainOfPolysK`), `CvecOkK D` (`cvecOkK`) under the deployment's facts `MainDeployK D`
  (`HeapGood`, `FunctionalsCorrect h_SHA3`, `2 ≤ h_SHA3`, `r_W ≤ 24`, heights `< 24`) and, for `CvecOkK`, the lanes'
  slots `LaneSlotsK`;
* `KvConstraintsK D` (`kvConstraintsK`), at every shape.

**`idsRemainingK_of`**: `IdsRemainingK` from what is left of it: `KvRealizesK`, `DiffsEvalK`, `DegBoundK`,
`RelCountK`, the lanes' slots and the deployment's facts.
-/

namespace UniKeccakSound.Ids

open UniKeccak

/-- **The three bridges**, from the deployment's facts and the lanes' slots. -/
theorem idsMainBridges (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : UniKeccak.KeccakVariant}
    (Fl : KFlockSound F κ v) (hd : MainDeployK D) (hL : LaneSlotsK) :
    MainOfPolysK D Fl ∧ CvecOkK D ∧ KvConstraintsK D :=
  ⟨mainOfPolysK D Fl hd, cvecOkK D hd.functionals hd.rW hL, kvConstraintsK D⟩

/-- **What remains of the identity model**, from `KvRealizesK`, `DiffsEvalK`, `DegBoundK`, `RelCountK`, the lanes'
slots and the deployment's facts. -/
theorem idsRemainingK_of (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) {κ : ℕ} {v : UniKeccak.KeccakVariant}
    (Fl : KFlockSound F κ v) {d n : ℕ} (hd : MainDeployK D) (hL : LaneSlotsK) (hR : KvRealizesK D)
    (hE : DiffsEvalK D Fl) (hDeg : DegBoundK D Fl d) (hRel : RelCountK D Fl n) : IdsRemainingK F D Fl d n where
  heapGood := hd.heap
  kvRealizes := hR
  kvConstraints := kvConstraintsK D
  cvecOk := cvecOkK D hd.functionals hd.rW hL
  functionals := hd.functionals
  height2 := hd.height2
  laneSlots := hL
  diffsEval := hE
  mainOfPolys := mainOfPolysK D Fl hd
  degBound := hDeg
  relCount := hRel

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.idsMainBridges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.idsMainBridges

/-- info: 'UniKeccakSound.Ids.idsRemainingK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.idsRemainingK_of
