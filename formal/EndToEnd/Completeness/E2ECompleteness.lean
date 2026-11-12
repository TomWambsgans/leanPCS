-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Library root of the membership proof's completeness on the EIP's PCS claims (`E2ECompleteness.Pcs*`), built on
-- the shared layers `Chain`, `Transfer`, `Regular`, `Grinding`, `End` (leanerVM `mumbai` 6175f1a0, MIT OR Apache-2.0).
import E2ECompleteness.Regular
import E2ECompleteness.Transfer
import E2ECompleteness.PcsDone

/-!
# `PcsQuotient.Completeness`, end to end, for the deployed protocol

The completeness statement of `formal/Statement` (`PcsQuotient.Completeness δ`: the setup, uniform coins, the
honest `prover` (the witness table `W`, the quotient table `T` with `A₀, A₁, B₀, B₁`, sixteen random rows, the
blinding of `h` with `b₂` solved, three one-point claims, one opening a claim) and the `verifier`, in one random
permutation) with an explicit `δ`:

* `PcsWithHash`, `PcsExperiment`, `PcsStaging`: the Statement's prover and verifier at functions `H`, `F`, and the
  experiment staged by the four challenges `(α, β, t, ρ)` (`completenessExperiment_eq_expH`, `expH_eq_staged`);
* `PcsChain`: the four challenges in the two-call random-oracle model, fresh by their lengths (`prEvent_staged4_le`);
* `Transfer`, `PcsDuplex`, `PcsCost`, `PcsHashLen`: the random permutation is two random oracles up to
  `N² / 2^508` (`rpm_le_rom`), the run following the duplex discipline (`duplexVm_stagedRun`) with at most `2^48`
  blocks (`hcost_deployed`);
* `PcsGrinding`, `PcsAccept`, `PcsOpening`, `PcsEnd`: the three openings' grinding (`rejectGood_of_tail`,
  `2^-304`) given the honest claims (`HonestClaims`), `completeness_of_staged4`;
* the honest algebra: `PcsKc3` (F1's honest second message is consistent and accepted), `PcsKc3Claims` (accepted
  tables satisfy the deployed claims), `PcsNovel`, `PcsNovelDiv` (the novel basis, `mulX`, `divX`, the division by
  `w_m`), `PcsHBasis`, `PcsHInstance`, `PcsHCells` (the deployed instance, F0's `sat_honest`), `PcsHDefs`,
  `PcsHCoset`, `PcsHArrays`, `PcsHParts`, `PcsHQuot` (the prover's arrays are F1's polynomials, `q = Q₀ + b₂ E` with
  `(q /ₘ Z)(0) = 0`), `PcsHTable`, `PcsHSlots` (the quotient table holds the honest second message), `PcsHValues`
  (`valuesAt`), `PcsHDeg`, `PcsHHonest` (**`H.honestClaims_badSet`**), `PcsHBad` (**`H.badSet_density`**,
  `(7 · 2^24 + 3) / 2^192`, given the evaluated `H.WiringCheck`);
* `PcsDone`: **`completeness_end`**, `PcsQuotient.Completeness deltaPcs` given `H.WiringCheck`,
  `deltaPcs < 2^-163`.

See the completeness section of `formal/README.md`.
-/

/-- info: 'E2ECompleteness.challengeOf_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.challengeOf_regular

/-- info: 'E2ECompleteness.rpm_le_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.rpm_le_rom

/-- info: 'E2ECompleteness.Pcs.prEvent_staged4_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.prEvent_staged4_le

/-- info: 'E2ECompleteness.Pcs.completenessExperiment_eq_expH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.completenessExperiment_eq_expH

/-- info: 'E2ECompleteness.Pcs.expH_eq_staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.expH_eq_staged

/-- info: 'E2ECompleteness.Pcs.duplexVm_stagedRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.duplexVm_stagedRun

/-- info: 'E2ECompleteness.Pcs.hcost_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.hcost_deployed

/-- info: 'E2ECompleteness.Pcs.H.badSet_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.H.badSet_density


/-- info: 'E2ECompleteness.Pcs.rejectGood_of_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.rejectGood_of_tail

/-- info: 'E2ECompleteness.Pcs.completeness_of_staged4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.completeness_of_staged4

/-- info: 'E2ECompleteness.Pcs.deltaPcs_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.deltaPcs_lt

/-- info: 'E2ECompleteness.Pcs.tailReduces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.tailReduces

/-- info: 'E2ECompleteness.Pcs.tailAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.tailAccepts

/-- info: 'E2ECompleteness.Pcs.H.honest_claims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.H.honest_claims

/-- info: 'E2ECompleteness.Pcs.H.honestClaims_badSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.H.honestClaims_badSet

/-- info: 'E2ECompleteness.Pcs.completeness_of_wiringCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.completeness_of_wiringCheck

/-- info: 'E2ECompleteness.completeness_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_end
