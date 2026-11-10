-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecStatement.Basic
import RecStatement.Data
import RecStatement.Spec
import RecStatement.Core
import RecStatement.Verifier
import RecStatement.Calls
import RecStatement.Security
import RecStatement.Reduction
import RecStatement.Lemmas.Main
import RecStatement.Lemmas.SpecLink

/-!
# RecStatement: π2's verifier, transcribed, and the recursive verifier's statements

`crates/leanvm/rec`'s π2 verifier (`pi2/verifier.rs`, `contract.rs`; `PI2.md` §2, §8–§9) as computable Lean
(`README.md` here: the reading order, the correspondence with the Rust, what is tested):

* **the verifier** (`run`, `runWith`): the seed of π2's IV (`iv`: π1's contract IV, the setup root, the circuit's
  digest, the layout words), the public data in the stream, `W`'s root then `α, β, γ`, `Q`'s root then `t`, the 17
  values then `ρ`, and the arithmetic at `t` (`CoreSpec.run`, over any field), its constants `Spec.of` of the
  circuit's tables (`Data`, emitted by the Rust); the six claims word for word (`pcsCalls`);
* **the verifier-arithmetic lemmas** (`Lemmas`), over any field of characteristic two, under `SpecOf` (the constants
  are `RecPiop`'s circuit's on a Cantor basis): the indicators' closed form (`ind_eval_closed`), the zero coset's
  (`coset_closed`), the siblings' fold (`cellsList_eq_cellsOf`), `W`'s fold (`foldW_eq_foldAt`), the push side
  (`push_side`), the public side (`publicSide_eq`), the one inversion's two nonzero conditions (`all_ne_zero_iff`), and
  **`checks_claims_iff`**/**`checks_claims_iff_post2`**: the checks pass and the claims hold iff `t ∉ V_{m+2}`,
  `c_h + c_q ≠ 0` and `RecPiop.Post2`;
* **the end statements** (`Security`, `Reduction`), for the recursion of the **Keccak VM** (π1 is `formal/UniKeccak`'s
  verifier at π1-rec3's shape `keccakRec3`, the 128-signature reference `RecGraphKeccak.Pi1.keccak128`): π2's, in the
  random-permutation model (`RecKnowledgeSoundness2`, `RecCompleteness2`: the contract accepts only if the Keccak
  π1-rec3's recorded graph `RecGraphKeccak.Pi1.pi1GraphK`, run with Keccak-f[1600], accepts a stream π2's extractor
  outputs, its calls the contract's); end-to-end knowledge soundness against the Keccak VM's relation
  (`KeccakVm.KvHolds`, the Keccak-f block the deployment's `flock`) as an **explicit reduction**
  (`RecKnowledgeSoundnessReduction`: the break is bounded by π2's error plus π1-rec3's and the merge hazard's
  experiments at Keccak-f[1600] for two explicit derived adversaries, `pi1Adversary`, `hazardAdversary`, of `A`'s
  queries); and the end-to-end corollaries (`RecKnowledgeSoundness`, `RecCompleteness`) under named hypotheses about
  π1-rec3 at Keccak-f[1600] (`Pi1FsKeccak`, `Pi1HazardKeccak`, false as stated for unbounded adversaries: the
  Fiat–Shamir heuristic for bounded ones; `Pi1CompletenessKeccak`, `Pi1HazardKeccakHonest`) and RecGraphKeccak's
  target (`RecGraphKeccak.Pi1GraphIsVerifierK`, proved there); stated, not proved.

The build fails if a headline definition or theorem uses an axiom beyond Lean's three standard ones.
-/

/-- info: 'RecStatement.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.run

/-- info: 'RecStatement.pcsCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.pcsCalls

/-- info: 'RecStatement.pi1Iv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.pi1Iv

/-- info: 'RecStatement.RecDeployment.setupTreesWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecDeployment.setupTreesWith

/-- info: 'RecStatement.RecDeployment.verifierWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecDeployment.verifierWith

/-- info: 'RecStatement.recExtractor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.recExtractor

/-- info: 'RecStatement.RecDeployment.Real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecDeployment.Real

/-- info: 'RecStatement.recExtractor2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.recExtractor2

/-- info: 'RecStatement.RecKnowledgeSoundness2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecKnowledgeSoundness2

/-- info: 'RecStatement.Pi1FsKeccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.Pi1FsKeccak

/-- info: 'RecStatement.Pi1HazardKeccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.Pi1HazardKeccak

/-- info: 'RecStatement.Pi1HazardAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.Pi1HazardAccepted

/-- info: 'RecStatement.pi1Adversary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.pi1Adversary

/-- info: 'RecStatement.hazardAdversary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.hazardAdversary

/-- info: 'RecStatement.RecKnowledgeSoundnessReduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecKnowledgeSoundnessReduction

/-- info: 'RecStatement.RecKnowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecKnowledgeSoundness

/-- info: 'RecStatement.RecCompleteness2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecCompleteness2

/-- info: 'RecStatement.Pi1CompletenessKeccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.Pi1CompletenessKeccak

/-- info: 'RecStatement.Pi1HazardKeccakHonest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.Pi1HazardKeccakHonest

/-- info: 'RecStatement.RecCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.RecCompleteness

/-- info: 'RecStatement.ind_eval_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.ind_eval_closed

/-- info: 'RecStatement.cellsList_eq_cellsOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.cellsList_eq_cellsOf

/-- info: 'RecStatement.foldW_eq_foldAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.foldW_eq_foldAt

/-- info: 'RecStatement.push_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.push_side

/-- info: 'RecStatement.phiAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.phiAt_eq

/-- info: 'RecStatement.phiPoly_eval_port' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.phiPoly_eval_port

/-- info: 'RecStatement.run_quotientValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.run_quotientValue

/-- info: 'RecStatement.run_pushesValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.run_pushesValue

/-- info: 'RecStatement.all_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.all_ne_zero_iff

/-- info: 'RecStatement.checks_claims_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.checks_claims_iff

/-- info: 'RecStatement.checks_claims_iff_post2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.checks_claims_iff_post2

/-- info: 'RecStatement.run_u' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.run_u

/-- info: 'RecStatement.digitsScale_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.digitsScale_eq

/-- info: 'RecStatement.pairZ_eq_zHat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.pairZ_eq_zHat

/-- info: 'RecStatement.normConsts_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecStatement.normConsts_of_spec
