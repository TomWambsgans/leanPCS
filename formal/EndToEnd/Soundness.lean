-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Soundness.PcsDeployed

/-!
# Knowledge soundness of the deployed membership proof (`pcs-quotient-kc3`, the EIP's PCS claims), end to end

**`Soundness.knowledgeSoundness : PcsQuotient.KnowledgeSoundness Soundness.ksBound`** (`Soundness/PcsDeployed.lean`):
the end statement of `formal/Statement` (`PcsQuotient/Security.lean`: the setup over one random permutation `π`, the
adversary given the circuit's commitment, its queries logged, the verifier over `π`), for the Statement's explicit,
computable extractor (`PcsQuotient.extractor`), proved with **no hypothesis**, on `propext`, `Classical.choice` and
`Quot.sound` only. For an adversary of at most `Q` calls of `π`, `π⁻¹`:

`ksBound Q = deployedBound (2^20 + 24 + Q) + (setupPermCalls + Q + verifierPermCalls)² / 2^508`,

`deployedBound` `SoundPcs`'s: three opening terms (F2's `pcs_sound_oracle`, `2^-128` a query each: the witness
claim on `W`, the wiring claim on the circuit's commitment, the copy claim on `T`); the binding of the two roots'
lists at their out-of-domain points (`ood_binding_coords` at `24` and `28` variables, `δc 24 ≤ 2^-165`,
`δc 28 ≤ 2^-169`); the two-root chain at `2^-164` a query (F1's round error `2^-165`, each challenge bounded for the
one candidate pair the out-of-domain answers pin, `ComposePcs.Chain2`); `setupPermCalls = 5 · 2^19 + 24`,
`verifierPermCalls = 8 + 3 · 121480`: about `2^-105.4` at `Q = 0`, `2^-86.4` at `Q = 2^40`, `2^-62.4` at `Q = 2^64`,
`126.4` bits as `Q/ε` (the three opening terms dominate).

| File | What |
|---|---|
| `PcsVH.lean`, `PcsVHDuplex.lean`, `PcsVHCost.lean` | The Statement's setup and verifier with Keccak-256 and Keccak-f a call (`VH.verifyWithH`, `VH.setupWithH`), their discipline and their cost (`8 + 3 · vOpen` calls of `π`). |
| `PcsRpm.lean` | `Compose/Rpm.lean`'s random-permutation transfer for any setup, adversary and verifier (`rpm_le_romG`). |
| `PcsDExp.lean` | `SoundPcs.dExp`'s stages' logs dropped (`map_dExp`); the two-oracle game bounded by `dExp` given an outcome-by-outcome comparison (`le_dExp`). |
| `PcsOpenBridge.lean` | The Statement's opening check is F2's `pcsVerifyWithHashO` in any lawful monad (`pcsOpeningWithH_eq_O`). |
| `PcsChain.lean` | The wire (`pcsWire2`); the Statement's reduction is `ComposePcs.chainWith2` then `claimsAt` (`reduceWithH_eq_chain2`). |
| `PcsVerifier.lean` | The Statement's verifier is `dExp`'s chain and three gated openings (`verifyWithH_eq_contD`), or rejects (`verifyWithH_reject`). |
| `PcsF1.lean`, `PcsExtract.lean` | `StackRel`; the event on transcripts (`ExtractsT`, `EvK`); `SoundPcs`'s extractor list holds a witness only where the extraction succeeds (`extracts_of_mem`), and there the Statement's extractor finds a secret (`extractor_of_extracts`). |
| `PcsSetup.lean` | The Statement's setup is `SoundPcs.setupPcs` of its wiring table (`setupPcs_eq`). |
| `PcsGame.lean` | The Statement's experiment is a function of the transfer game and breaks only where its event holds (`prEvent_soundness_le`). |
| `PcsFinal.lean` | **`knowledgeSoundness_of`**: for any F1 parameters with sound rounds, a claims match, `StackRel` and σ's size; `ksBound`. |
| `PcsMatch.lean` | The claims match F1's verifier (`claimsMatchK`, from `PcsBridge.Kc3.accepts_of_claims`); `knowledgeSoundness_of_matches`. |
| `PcsDeployed.lean` | F0's deployed instance (`Kc3Deployed.deployedParams`): its match (`matches_deployed`), `StackRel` (`stackRel_deployed`, from `relation_of_sat_deployed`), σ's size, its pole condition (F0's `poleCondition_deployed`); **`knowledgeSoundness`**. |

`Soundness/{EarlyStop,Cost,TreeLog,MerkleWord,Replay,Extract,Final}.lean` are the previous protocol's modules pruned
to what the leanVM line imports (`TreeLog`, `MerkleWord`, `Replay`, `Extract` serve here too).
-/

/-- info: 'Soundness.knowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.knowledgeSoundness

/-- info: 'Soundness.knowledgeSoundness_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.knowledgeSoundness_of

/-- info: 'PcsKS.Deployed.matches_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsKS.Deployed.matches_deployed

/-- info: 'PcsKS.Deployed.stackRel_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsKS.Deployed.stackRel_deployed
