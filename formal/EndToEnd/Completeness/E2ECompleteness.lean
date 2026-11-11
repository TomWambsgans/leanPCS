-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Library root of the membership proof's completeness on the EIP's PCS claims (`E2ECompleteness.Pcs*`), built on
-- the shared layers `Chain`, `Transfer`, `Regular`, `Grinding`, `End` (leanerVM `mumbai` 6175f1a0, MIT OR Apache-2.0).
import E2ECompleteness.Regular
import E2ECompleteness.Transfer
import E2ECompleteness.PcsDone

/-!
# `PcsQuotient.Completeness`, end to end, on the PCS claims

The completeness statement of `formal/Statement` (`PcsQuotient.Completeness δ`: the setup, uniform coins, the
honest `prover` (four commitments with out-of-domain answers, `H`, `Q`, `G`, sixteen random rows, the blinding of
`h`, six one-point claims, one opening a claim) and the `verifier`, in one random permutation) with an explicit `δ`:

* `PcsWithHash`, `PcsExperiment`, `PcsStaging`: the Statement's prover and verifier at functions `H`, `F`, and the
  experiment staged by the four challenges `(α, β, t, ρ)` (`completenessExperiment_eq_expH`, `expH_eq_staged`);
* `PcsChain`: the four challenges in the two-call random-oracle model, fresh by their lengths (`prEvent_staged4_le`);
* `Transfer`, `PcsDuplex`, `PcsCost`, `PcsHashLen`: the random permutation is two random oracles up to
  `N² / 2^508` (`rpm_le_rom`), the run following the duplex discipline (`duplexVm_stagedRun`) with at most `2^48`
  blocks (`hcost_deployed`);
* `PcsBad`, `PcsGrinding`, `PcsEnd`: the degenerate challenges (`badP4_fraction_le`, `(19 · 2^24 + 31) / 2^192`),
  the six openings' grinding (`rejectGood_of_tail`, `2^-304`), `completeness_of_staged4`, `deltaPcs_lt`;
* `PcsHonest`, `PcsTable`, `PcsTables`, `PcsCoset`, `PcsCells`, `PcsQuotient`, `PcsQuotientTable`, `PcsCircuit`,
  `PcsValues`, `PcsStatement`, `PcsClaims`: the honest parts are F1's blinded honest second message
  (`quotientsOfTable_honest`) and the six claims are true (`honestClaims`); `PcsAccept`, `PcsOpening`: accepted;
* `PcsDone`: **`completeness_end`**, `PcsQuotient.Completeness deltaPcs` with no hypothesis, `deltaPcs < 2^-163`.

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

/-- info: 'E2ECompleteness.Pcs.badP4_fraction_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.badP4_fraction_le

/-- info: 'E2ECompleteness.Pcs.badSet_density' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.badSet_density

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

/-- info: 'E2ECompleteness.Pcs.quotientsOfTable_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.quotientsOfTable_honest

/-- info: 'E2ECompleteness.Pcs.honestClaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.honestClaims

/-- info: 'E2ECompleteness.Pcs.completeness_of_honestClaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.completeness_of_honestClaims

/-- info: 'E2ECompleteness.completeness_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.completeness_end
