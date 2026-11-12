-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import PcsBridge.Kc3Claims
import PcsBridge.Kc3Accepts
import PcsBridge.Kc3Deployed

/-!
# Bridges of the deployed membership protocol (`pcs-quotient-kc3`, the EIP's PCS claims)

* `PcsBridge/Kc3Claims.lean`: the deployed `claimsAt`'s three claims, explicitly (`claimsAt_spec`);
* `PcsBridge/Kc3Accepts.lean`: the claims hold of tables only if F1's verifier (`Kc3.Params.Accepts`) accepts the
  tables' polynomials, for parameters matching the statement's constants (`Matches`, `accepts_of_claims`);
* `PcsBridge/Kc3Deployed.lean`: F1's Cantor instance matches them (`matches_ofCantor`: `Z = w_24`, `Z_R` the
  statement's rows' polynomial, σ's polynomial a carrying table's); a table's cells are its polynomial at the cells'
  points (`cells_witnessOfTable`).

`PcsBridge/{Parts,Claims}.lean` are the previous protocol's (the quotient table in three parts, six claims), no
longer imported here: `formal/EndToEnd/Completeness`'s previous files still read them.
-/

/-- info: 'PcsBridge.Kc3.accepts_of_claims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsBridge.Kc3.accepts_of_claims

/-- info: 'PcsBridge.Kc3.matches_ofCantor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsBridge.Kc3.matches_ofCantor

/-- info: 'PcsBridge.Kc3.cells_witnessOfTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsBridge.Kc3.cells_witnessOfTable
