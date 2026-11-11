-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Part1
import RecCompose.Part2
import RecCompose.CallsPure
import RecCompose.Couplings
import RecCompose.RunShape
import RecCompose.OpeningsAgree
import RecCompose.RunOpenings
import RecGraphKeccak.Sim.Final4

/-!
# The end theorems of soundness, from π2's layers

* **`recKnowledgeSoundness2_of_real`** (π2's part, in the random-permutation model): with π2's layers
  (`Pi2Layers D ε2`), `RecKnowledgeSoundness2 D ε2` (the declared claims are three: `declaredClaims`).
* **`recKnowledgeSoundnessReduction_end`** (end to end, against the Keccak VM's `KvHolds`, as an explicit reduction):
  `RecKnowledgeSoundnessReduction D ε2`, from Part 1, the couplings (`experimentsAgree`, `hazardCoupling`,
  `collisionCoupling`, `pi1Coupling` with `declaredGood` and `pi1OpeningsAgree`) and
  `RecGraphKeccak.Sim.pi1GraphIsVerifierK4`. No Fiat–Shamir or collision-resistance hypothesis: the bound is `ε2 Q`
  plus π1-rec4's, the hazard's and the collision's experiments for the derived adversaries `pi1Adversary A`,
  `hazardAdversary A`, `collisionAdversary A`. The one evaluated input is `GraphsAgreeK4` (the Lean recording of
  π1-rec4's verifier is the emitted graph: the claims' word counts).
* **`recKnowledgeSoundness_end`** (its Prop-premise corollary): `RecKnowledgeSoundness D ε2 ε1 εh εc` for every `ε1`,
  `εh`, `εc`.

The π1 of these theorems is the Keccak VM's verifier at π1-rec4's Fiat–Shamir shape (`UniKeccak.runK4`, `keccakRec4`)
at the 128-signature reference shape (`RecGraphKeccak.Pi1.keccak128`, which `RecDeployment.Real` pins).
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol
open scoped ENNReal

/-- **π2's part**: from π2's layers, `RecKnowledgeSoundness2 D ε2`. -/
theorem recKnowledgeSoundness2_of_real (D : RecDeployment) {ε2 : ℕ → ℝ≥0∞} (L : Pi2Layers D ε2) :
    RecKnowledgeSoundness2 D ε2 :=
  recKnowledgeSoundness2_of_layers L (declaredClaims D)

/-- **The recursive verifier is knowledge sound end to end, as an explicit reduction**, against the Keccak VM's relation
(`KvHolds D.flock`), at a deployment of the reference shape: `RecKnowledgeSoundnessReduction D ε2`. For every adversary
`A` of `Q` queries, the derived adversaries `pi1Adversary D A`, `hazardAdversary D A`, `collisionAdversary D A` make at
most `Q` queries, and the contract accepts while `recExtractor` fails with probability at most `ε2 Q` plus the
probabilities that they break π1-rec4 at Keccak-f[1600], hit the merge hazard on a stream π1-rec4's graph accepts, and
output a Keccak-256 collision. The couplings and graph = verifier are proved; the inputs are π2's layers `L` and the
evaluated `GraphsAgreeK4`. -/
theorem recKnowledgeSoundnessReduction_end (D : RecDeployment) (hD : D.pi1.shape = RecGraphKeccak.Pi1.keccak128)
    (hg : RecGraphKeccak.GraphsAgreeK4) {ε2 : ℕ → ℝ≥0∞} (L : Pi2Layers D ε2) :
    RecKnowledgeSoundnessReduction D ε2 :=
  recKnowledgeSoundnessReduction_of_part1 (recKnowledgeSoundness2_of_real D L) (experimentsAgree D)
    (hazardCoupling D) (collisionCoupling D)
    (pi1Coupling D (declaredGood D) (pi1OpeningsAgree D hD pi1RunShape pi1RunOpenings hg))
    RecGraphKeccak.Sim.pi1GraphIsVerifierK4

/-- **The recursive verifier is knowledge sound end to end, the Prop-premise corollary**: `RecKnowledgeSoundness D ε2 ε1
εh εc` for every `ε1`, `εh`, `εc` (under `Pi1GraphIsVerifierK4`, proved, `Pi1FsKeccak ε1`, `Pi1HazardKeccak εh`,
`Keccak256CR εc`, the last three false as stated for unbounded adversaries). -/
theorem recKnowledgeSoundness_end (D : RecDeployment) (hD : D.pi1.shape = RecGraphKeccak.Pi1.keccak128)
    (hg : RecGraphKeccak.GraphsAgreeK4) {ε2 : ℕ → ℝ≥0∞} (L : Pi2Layers D ε2) (ε1 εh εc : ℕ → ℝ≥0∞) :
    RecKnowledgeSoundness D ε2 ε1 εh εc :=
  recKnowledgeSoundness_of_reduction (recKnowledgeSoundnessReduction_end D hD hg L) ε1 εh εc

/-- **The same under the hypotheses alone** (`Pi1GraphIsVerifierK4` proved): the explicit extractor `recExtractor`
fails while the contract accepts with probability at most `ε2 Q + ε1 Q + εh Q + εc Q`. -/
theorem recKnowledgeSoundness_end_fs (D : RecDeployment) (hD : D.pi1.shape = RecGraphKeccak.Pi1.keccak128)
    (hg : RecGraphKeccak.GraphsAgreeK4) {ε2 : ℕ → ℝ≥0∞} (L : Pi2Layers D ε2) (ε1 εh εc : ℕ → ℝ≥0∞)
    (h1 : Pi1FsKeccak D ε1) (hh : Pi1HazardKeccak D εh) (hc : Keccak256CR D εc) :
    RecKnowledgeSoundnessWith D (recExtractor D) fun Q ↦ ε2 Q + ε1 Q + εh Q + εc Q :=
  recKnowledgeSoundness_end D hD hg L ε1 εh εc RecGraphKeccak.Sim.pi1GraphIsVerifierK4 h1 hh hc

end RecCompose

/-- info: 'RecCompose.recKnowledgeSoundness2_of_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness2_of_real

/-- info: 'RecCompose.recKnowledgeSoundnessReduction_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundnessReduction_end

/-- info: 'RecCompose.recKnowledgeSoundness_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_end

/-- info: 'RecCompose.recKnowledgeSoundness_end_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness_end_fs
