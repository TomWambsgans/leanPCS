-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The main line's `FsCouple.lean` (`uniGameLeV_of`)
-- for π1-rec3's experiment (`UniStatement.uniSoundnessExperimentRec3`, `Deployment.verifierRec3With`).
import UniSound.Rec3.FsGame3
import UniSound.FsCouple

/-!
# π1-rec3's experiment and the composed game, coupled

**`uniGameLeV3_of`**: the coupling `UniGameLeV3` from three bridge facts, as `FsCouple.lean`'s:

* **`UniSetupBridge`** (the setup, unchanged: `FsCouple.lean`'s, proved by `uniSetupBridge_of_small`);
* **`UniVerifierBridge3`** (the verifier): from any state of the lazily sampled permutation, the Statement's
  `verifyWithFs … .rec3 true` (the run on the stream, its early stops, the three `PCS_OPEN` calls) accepts at most
  as often as the composed verifier (the chain on `rec3Rounds`, the three openings) satisfies `uniCheck3` and all
  three openings accept;
* **`UniExtractBridge3`** (the extractor's reading, at π1-rec3's view of the stream): a candidate of `C1`'s root
  that the composed extractor reads off the setup's log and the adversary's transcript, satisfying the relation,
  makes the Statement's `uniExtractor` (unchanged) find a stack satisfying it.

The proof is `FsCouple.lean`'s: the common prefix (`prefixU`), then both verifiers first compute π1-rec3's IV, the
same Keccak-256 call (`ivRec3With_eq`), then `step_le3`.
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack

/-! ## The bridge facts -/

/-! ## The experiments, a common prefix then the verifiers -/

/-! ## The verifiers, outcome by outcome -/

/-! ## The coupling -/

end UniSound

