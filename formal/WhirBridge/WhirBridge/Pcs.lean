-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import WhirBridge.PcsClaim
import WhirBridge.PcsBinding
import WhirBridge.PcsBindingRom

/-!
# The EIP's PCS opening, version 1

`crates/pcs_claim` (`docs/PCS_CLAIM.md`): the claim `version ‖ n ‖ root ‖ ood ‖ point ‖ value`, its
opening seeded by `keccak256(PCS_claim)` alone, proving `f(z) = ood` and `f(point) = value` at one
random combination with leanVM's WHIR (deployed ladder, rate `1/2`).

* `PcsClaim.lean`: the transcription (`claimBytes`, `oodPoint`, `pcsVerifyWithHash`), its reading
  as mumbai's stacked opening of two claims (`check_eq`, `prog_eq`, `pcsVerify_imp`), and its
  Fiat-Shamir soundness `pcs_family_sound`, `pcs_sound` (`openingBound QA`, `≤ 2^-63` for
  `QA ≤ 2^64`) at one `n`, `pcs_sound_any` for an adversary choosing `n` (`14 · openingBound QA`,
  `≤ 2^-59`);
* `PcsBinding.lean`: the out-of-domain answer binds: `two_openings_one_polynomial` (two openings of
  one commitment, neither doomed, the root's list separated at `z`: one polynomial), the
  Schwartz-Zippel count over a list `card_not_sepAt_le`, and `ood_binding` for lists fixed in
  advance (`Q · C(L, 2) · n / 2^192`);
* `PcsBindingRom.lean`: `ood_binding_rom`, the same with the lists extracted from the final
  Keccak-256 answers, the adversary holding Keccak-256, Keccak-f[1600] and the out-of-domain
  oracle (`Q · C(L, 2) · n / 2^192 + Q (Q + 1) / 2^256`).

The headline theorems use only `propext`, `Classical.choice` and `Quot.sound`.
-/

/-- info: 'WhirBridge.Pcs.claimBytes_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.claimBytes_injective

/-- info: 'WhirBridge.Pcs.check_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.check_eq

/-- info: 'WhirBridge.Pcs.holds_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.holds_iff

/-- info: 'WhirBridge.Pcs.pcsVerify_imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.pcsVerify_imp

/-- info: 'WhirBridge.Pcs.pcs_family_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.pcs_family_sound

/-- info: 'WhirBridge.Pcs.pcs_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.pcs_sound

/-- info: 'WhirBridge.Pcs.pcs_sound_any' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.pcs_sound_any

/-- info: 'WhirBridge.Pcs.pcs_any_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.pcs_any_bound_le

/-- info: 'WhirBridge.Pcs.pcs_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.pcs_bound_le

/-- info: 'WhirBridge.Pcs.colEval_eq_evalMle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.colEval_eq_evalMle

/-- info: 'WhirBridge.Pcs.card_not_sepAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.card_not_sepAt_le

/-- info: 'WhirBridge.Pcs.two_openings_one_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.two_openings_one_polynomial

/-- info: 'WhirBridge.Pcs.ood_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.ood_binding

/-- info: 'WhirBridge.Pcs.ood_binding_candidates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.ood_binding_candidates

/-- info: 'WhirBridge.Pcs.binding_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.binding_bound_le

/-- info: 'WhirBridge.Pcs.extract_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.extract_stable

/-- info: 'WhirBridge.Pcs.ood_binding_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.ood_binding_rom

/-- info: 'WhirBridge.Pcs.δood_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.δood_le
