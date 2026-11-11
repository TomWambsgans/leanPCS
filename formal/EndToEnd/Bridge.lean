-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Bridge.Circuit
import Bridge.Circuit.Secret
import Bridge.Circuit.Outputs
import Bridge.Opening
import Bridge.Chain
import Bridge.Verifier
import Bridge.Claims.Constants
import Bridge.Claims.Tau
import Bridge.Ntt
import Bridge.Setup

/-!
# The bridge: the statement's definitions are the proof layers'

`formal/Statement` (`PcsQuotient`) states the end theorems about its own transcriptions of the Rust;
the proofs (`formal/Circuit`, `QuotientSecurity`, `WhirBridge`, `Compose`, `Completeness`,
`Implementation`) are about theirs. Each file here proves a part of the statement's definitions equal
to the proofs', for general arguments (nothing of the `2^22`-row circuit or of a `2^24`-entry table is
ever evaluated). The membership protocol's own bridges for the EIP's PCS claims are in `PcsBridge`;
the files here are what that protocol and the leanVM line (`formal/Uni*`, `formal/Rec*`, `Heap`) share.

* `Bridge/Circuit.lean` (`Bridge/Circuit/*.lean`): the statement's `membership 22` is F0b's
  `PcsCircuit.membership` (`membership_eq`), proved builder step by builder step; the secret the
  input rows' bits spell is F0b's (`Circuit/Secret.lean`, `secretMatches`); the computation and the
  inputs of a secret are F0b's (`Circuit/Outputs.lean`, `outputs_eq`, `membership_cells`,
  `membershipInputs_eq`, `secretOfInputs_membershipInputs`).
* `Bridge/Opening.lean`: the statement's layout opening is F2's (`WhirBridge`): the layouts, the
  stack weights (`stackWeight_eq`, `gadgetWeight_eq`), the seed's bytes (`encoding_eq`,
  `claimBytes_eq`, `openingPrefix_eq`), the check itself (`openingWith_eq`,
  `openingWith_eq_ourVerifier`); `Bridge/Verifier.lean`: the same in the form the callers use
  (`openingWith_eq_ourVerifier'`, `toStmt_claims_of`, `ofB_toB`).
* `Bridge/Chain.lean`: the statement's transcript words are F4's (`toB_toList`, `beWord_eq`,
  `challengeOf_eq`).
* `Bridge/Claims/Constants.lean`, `Bridge/Claims/Tau.lean`: `Compose.Reduce.reduce`'s constants as the
  statement computes them (`statementConsts`), the basis checked by kernel evaluation
  (`betaAt_eq_deployedBasis`, `isCantor_statementConsts`), the rows' polynomial at `2^22` rows one
  elimination step at a time.
* `Bridge/Ntt.lean`: the statement's additive transform evaluates and interpolates F1's novel-basis
  table polynomial on the Cantor points, for every size (`values_getD_K`, `tablePoly_coefficients`).
* `Bridge/Setup.lean`: the statement's WHIR commitment is mumbai's tree (`commitWith_eq`,
  `stackWordFast_eq_columnOf`).

The previous membership protocol's bridges (its claims, extractor and the facts its soundness theorem
took) were removed with that protocol; they are in the git history.

**Building.** Lib `Bridge` of this package; on a machine with the leanerVM checkout at
`formal/leanervm` (see the lakefile): `lake build Bridge`.
-/
