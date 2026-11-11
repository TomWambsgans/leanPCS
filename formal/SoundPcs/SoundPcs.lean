-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import SoundPcs.Stages
import SoundPcs.Tables
import SoundPcs.Deployed
import SoundPcs.Trace
import SoundPcs.Opening
import SoundPcs.Final
import SoundPcs.Axioms

/-!
# `SoundPcs`: the deployed composition of the EIP's PCS claims

Knowledge soundness of the deployed membership verifier (`pcs-quotient-kc3`: two commitments, each a root and its
out-of-domain answer; three one-point PCS openings), in leanerVM `mumbai`'s two-oracle model `KeccakCalls`:
**`SoundPcs.knowledgeSoundness_deployed_pcs_of`** (`Final.lean`).

* `Stages.lean`: a run of openings, each stage logged from the start; its doom an event of `romExperiment`;
* `Tables.lean`: a committed column as F1 reads it, its table code, the certified lists at `24` and `28` variables;
* `Deployed.lean`: the opening interface (`OpenSpec`), the setup (`setupPcs`: the wiring table's tree and
  out-of-domain answer), the deployed run (`dExp`: setup and adversary, `chainWith2`, `claimsAt`, three gated
  openings), each opening's doom and the binding events (`EBn 24`, `EBn 28`) bounded;
* `Trace.lean`: the two commitments' pins (`ClaimsMatch.KP`: candidate columns with the out-of-domain answer, read
  off the `46`-byte inputs); an accepted run whose extracted list holds no witness, no opening doomed and both
  roots' lists separated at their points, asks a bad fresh query of `ComposePcs.advBad2P` (`trace_dExp`);
* `Opening.lean`: the deployed opening `pcsVerifierO` (`WhirBridge.PcsOracle`) as an `OpenSpec` (`pcsOpen`);
* `Final.lean`: the theorem and its bound (`deployedBound`: three opening terms, two binding terms, the chain at
  `2^-164` a query), for any wiring table and any match of the claims to F1's decision (`ClaimsMatch`);
  `Axioms.lean`: the axiom guards. The claims' match at the deployed instance is `PcsBridge`'s.
-/
