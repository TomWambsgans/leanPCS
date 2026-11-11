-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import SoundPcs.Stages
import SoundPcs.Tables
import SoundPcs.Deployed
import SoundPcs.Trace
import SoundPcs.Opening
import SoundPcs.Claims
import SoundPcs.Final
import SoundPcs.Axioms

/-!
# `SoundPcs`: the deployed composition of the EIP's PCS claims

Knowledge soundness of the deployed membership verifier of the EIP's PCS claims (four commitments, each a root
and its out-of-domain answer; six one-point PCS openings), in leanerVM `mumbai`'s two-oracle model `KeccakCalls`:
**`SoundPcs.knowledgeSoundness_deployed_pcs`** (`Final.lean`).

* `Stages.lean`: a run of openings, each stage logged from the start; its doom an event of `romExperiment`;
* `Tables.lean`: a committed column as F1 reads it, its table code, the quotient table from its three parts;
* `Deployed.lean`: the opening interface (`OpenSpec`), the setup (`setupPcs`: the wiring table's tree and
  out-of-domain answer), the deployed run (`dExp`: setup and adversary, `chainWith4`, `claimsAt`, six gated
  openings), each opening's doom and the binding event bounded;
* `Trace.lean`: an accepted run whose extracted list holds no witness, no opening doomed and `H`'s list separated,
  asks a bad fresh query (`trace_dExp`);
* `Opening.lean`: the deployed opening `pcsVerifierO` (`WhirBridge.PcsOracle`) as an `OpenSpec` (`pcsOpen`);
* `Claims.lean`: the claims, through `PcsBridge.claimsAt_eq` and `Compose.Reduce`, are F1's (`claimsMatch`);
* `Final.lean`: the theorem and its bound (`deployedBound`); `Axioms.lean`: the axiom guards.
-/
