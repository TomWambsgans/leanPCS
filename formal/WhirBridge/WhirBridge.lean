-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import WhirBridge.Opening
import WhirBridge.Sound
import WhirBridge.Table
import WhirBridge.Hidden
import WhirBridge.Layouts
import WhirBridge.Variant
import WhirBridge.Family
import WhirBridge.Verifier
import WhirBridge.Gaps
import WhirBridge.Large
import WhirBridge.Pcs
import WhirBridge.PcsBindingCoords
import WhirBridge.PcsOracle

/-!
# The WHIR bridge

`opening::verify` of `crates/membership/quotient/src/opening.rs` under leanerVM `mumbai`'s theorems: its
Fiat-Shamir soundness in the random-oracle model for every valid layout (`opening_sound`) and for
the protocol's witness, wiring and quotient layouts at every supported size (`ours_sound`), in
table terms (`Layout.holds_iff`, `Table::read` for the hidden layouts; the hidden layouts' gadget,
one more stack claim of value zero, `gadget_holds_iff`); and the EIP's PCS opening, version 1
(`crates/pcs_claim`; `WhirBridge/Pcs.lean`: `pcs_sound`, `pcs_sound_any`, the binding of the
out-of-domain answer `two_openings_one_polynomial`, `ood_binding`, `ood_binding_rom`, and
`ood_binding_coords` with the point read off Keccak-256 coordinate by coordinate), and its
soundness with the out-of-domain point read off Keccak-256 by the verifier, as deployed
(`WhirBridge/PcsOracle.lean`: `pcs_sound_oracle`, `pcs_sound_any_oracle`). The headline
theorems use only `propext`, `Classical.choice` and `Quot.sound`.
-/

/-- info: 'WhirBridge.isMultiaffine_layoutClaimWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.isMultiaffine_layoutClaimWeight

/-- info: 'WhirBridge.isMultiaffine_gadgetWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.isMultiaffine_gadgetWeight

/-- info: 'WhirBridge.gadget_holds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.gadget_holds_iff

/-- info: 'WhirBridge.Layout.joint_of_not_doom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Layout.joint_of_not_doom

/-- info: 'WhirBridge.layouts_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.layouts_shape

/-- info: 'WhirBridge.Layout.check_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Layout.check_eq

/-- info: 'WhirBridge.holds_iff_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.holds_iff_hidden

/-- info: 'WhirBridge.Layout.holds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Layout.holds_iff

/-- info: 'WhirBridge.layouts_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.layouts_valid

/-- info: 'WhirBridge.layouts_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.layouts_ok

/-- info: 'WhirBridge.family_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.family_sound

/-- info: 'WhirBridge.openingVerify_imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.openingVerify_imp

/-- info: 'WhirBridge.opening_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.opening_sound

/-- info: 'WhirBridge.opening_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.opening_bound_le

/-- info: 'WhirBridge.ours_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.ours_sound

/-- info: 'WhirBridge.Pcs.split_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.split_eq

/-- info: 'WhirBridge.Pcs.couple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.couple

/-- info: 'WhirBridge.Pcs.sim_verifierO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.sim_verifierO

/-- info: 'WhirBridge.Pcs.pcs_sound_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.pcs_sound_oracle

/-- info: 'WhirBridge.Pcs.pcs_sound_any_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.pcs_sound_any_oracle

/-- info: 'WhirBridge.Pcs.pcs_oracle_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.pcs_oracle_bound_le
