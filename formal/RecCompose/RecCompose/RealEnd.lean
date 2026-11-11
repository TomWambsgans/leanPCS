-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The recursive verifier's end theorem of soundness at the
-- real deployment (`RealDeployment.lean`'s `realDeployment`): `Final.lean`'s with the circuit, its facts and its
-- corollary built from the evaluated checks (`RealCircuit.lean`).
import RecCompose.Final
import RecCompose.RealCircuit

/-!
# The recursive verifier's end theorem of soundness at the real deployment

The Keccak VM's recursion at the 128-signature reference (`realDeployment prog hprog`: π1-rec4 at
`RecGraphKeccak.Pi1.keccak128`, π2v4's circuit the Lean compiler's on π1-rec4's recorded graph at every π1 setup
commitment, π1's three claims hashed in π2's circuit and declared in the frame of PCS claims). The inputs left are the
evaluated checks (`RecGraphKeccak.GraphsAgreeK4`, `DigestChecked`, `SetupRootChecked`, `IvChecked`, the last evaluated
at the reference setup commitment's reference, zero and all-ones IVs and assumed at the others); `Q`'s out-of-domain
binding is proved (`FsBind.qOodBinding`, the point read off Keccak-256 over the permutation):

* **`recKnowledgeSoundness_reduction_real`**: knowledge soundness against the Keccak VM's `KvHolds`, as an explicit
  reduction, with no Fiat–Shamir or collision-resistance premise: the break is at most `pi2Bound Q ≤ 2^-64` (for
  `Q ≤ 2^64`, 128.93 bits as `Q/ε2`) plus the probabilities that three explicit adversaries (`A`, then π2's
  extractor) break π1-rec4 at Keccak-f[1600], hit its merge hazard, or output a Keccak-256 collision.
-/

namespace RecCompose

open RecStatement
open scoped ENNReal

/-- **Knowledge soundness of the recursive verifier at the real deployment, as an explicit reduction**: from the
evaluated checks, `RecKnowledgeSoundnessReduction (realDeployment prog hprog) pi2Bound`, and `pi2Bound Q ≤ 2^-64` for
`Q ≤ 2^64`. -/
theorem recKnowledgeSoundness_reduction_real (prog : KeccakVm.Program)
    (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize) (hg : RecGraphKeccak.GraphsAgreeK4)
    (hd : DigestChecked) (hs : SetupRootChecked) (hiv : IvChecked) :
    RecKnowledgeSoundnessReduction (realDeployment prog hprog) pi2Bound ∧
      ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64 :=
  ⟨recKnowledgeSoundnessReduction_final _ (realDeployment_real prog hprog hg hd hs)
      (pi2Circuits_real prog hprog hg hiv) (pi2Facts_real prog hprog hg hd hs hiv)
      (pi2Circuits_real_rootsAt prog hprog hg hiv) (pi2CircuitAccepts_real prog hprog hg hd hs hiv) hg,
    pi2Bound_le_bits⟩

end RecCompose

/-- info: 'RecCompose.recKnowledgeSoundness_reduction_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_reduction_real
