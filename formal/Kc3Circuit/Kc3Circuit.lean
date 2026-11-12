-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Kc3Circuit.Membership
import Kc3Circuit.BridgeBuild
import Kc3Circuit.Wiring
import Kc3Circuit.Closed
import Kc3Circuit.Rows
import Kc3Circuit.Pole
import Kc3Circuit.Cells
import Kc3Circuit.Words
import Kc3Circuit.Sound
import Kc3Circuit.Honest
import Kc3Circuit.Transport

/-!
# `Kc3Circuit`: the deployed membership circuit as `Kc3` data

`PcsQuotient.membership 22` (`formal/Statement/PcsQuotient/Circuit.lean`) on the cells of a Cantor basis
(`Kc3.Params.ofCantor`): `Kc3Deployed.deployedParams B hm`, its pole condition proved
(`Kc3Deployed.poleCondition_deployed`), and cells satisfying it spelling a secret of the statement
(`Kc3Deployed.relation_of_sat_deployed`), and the honest prover's cells satisfying it
(`Kc3Deployed.sat_honest`, `Kc3Deployed.sat_honest_of_relation`).
-/

/-- info: 'Kc3Closed.pole_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3Closed.pole_idx

/-- info: 'Kc3Closed.relation_of_sat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3Closed.relation_of_sat

/-- info: 'Kc3Deployed.poleCondition_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3Deployed.poleCondition_deployed

/-- info: 'Kc3Deployed.relation_of_sat_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3Deployed.relation_of_sat_deployed

/-- info: 'Kc3Deployed.sat_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3Deployed.sat_honest

/-- info: 'Kc3Deployed.sat_honest_of_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Kc3Deployed.sat_honest_of_relation
