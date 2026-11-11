-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import PcsBridge.Parts
import PcsBridge.Claims

/-!
# Bridges of the new membership protocol (PCS claims)

* `PcsBridge/Parts.lean`: the quotient table from its three committed parts (`assemble`, `mle_assemble`);
* `PcsBridge/Claims.lean`: the Statement's six claims through `Compose.Reduce.reduce` (`claimsAt_eq`).
-/

/-- info: 'PcsBridge.mle_assemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsBridge.mle_assemble

/-- info: 'PcsBridge.claimsAt_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsBridge.claimsAt_eq
