-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The recursive verifier's end theorems at the real
-- deployment (`RealDeployment.lean`'s `realDeployment`): `FsClosed.lean`'s soundness with its deployment, circuits and
-- view check built from the evaluated checks (completeness there: `CompleteKeccakEnd.lean`).
import RecCompose.FsClosed
import RecCompose.RealDeployment

/-!
# The recursive verifier's end theorems at the real deployment

The Keccak VM's recursion at the 128-signature reference (`realDeployment prog hprog`: π1-rec3 at
`RecGraphKeccak.Pi1.keccak128`, π2's circuit the Lean compiler's on the emitted π1-rec3 graph at every IV). The inputs
left are the evaluated checks of `RealDeployment.lean` (`GraphsAgree`, `DigestChecked`, `SetupRootChecked`,
`IvChecked`, the last checked at three IVs and assumed at the others) and, for soundness, `Q`'s out-of-domain binding
(`QOodBinding δBind`, `FsBind.lean`):

* **`recKnowledgeSoundness_reduction_real`**: `FsClosed.recKnowledgeSoundness_reduction` there. Knowledge soundness
  against the Keccak VM's `KvHolds`, as an explicit reduction, with no Fiat–Shamir premise but the binding's: the break is at most
  `pi2Bound Q ≤ 2^-64` (for `Q ≤ 2^64`) plus the probabilities that two explicit adversaries (`A` then π2's
  extractor) break π1-rec3 at Keccak-f[1600] or hit its merge hazard.
* **`recCompleteness_real_K_fs_bits`** (`CompleteKeccakEnd.lean`): completeness of the composed honest prover, error
  `δ1 + δh + 2^-164` under the two premises about π1-rec3's honest run at Keccak-f[1600].
-/

namespace RecCompose

open RecStatement
open scoped ENNReal

/-- **Knowledge soundness of the recursive verifier at the real deployment, as an explicit reduction**: from the
evaluated checks and `Q`'s out-of-domain binding (`QOodBinding δBind`, `FsBind.lean`),
`RecKnowledgeSoundnessReduction (realDeployment prog hprog) pi2Bound`, and
`pi2Bound Q ≤ 2^-64` for `Q ≤ 2^64`. -/
theorem recKnowledgeSoundness_reduction_real (prog : KeccakVm.Program)
    (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize) (hg : GraphsAgree) (hd : DigestChecked)
    (hs : SetupRootChecked) (hiv : IvChecked) (hB : QOodBinding δBind) :
    RecKnowledgeSoundnessReduction (realDeployment prog hprog) pi2Bound ∧
      ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  recKnowledgeSoundness_reduction _ (realDeployment_real prog hprog hg hd hs) hB (pi2Circuits_real prog hprog hg hiv) rfl
    hg (pi2ViewChecked_real prog hprog hg hiv)

end RecCompose

/-- info: 'RecCompose.recKnowledgeSoundness_reduction_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_reduction_real
