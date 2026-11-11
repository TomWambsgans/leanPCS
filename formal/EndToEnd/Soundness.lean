-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Soundness.PcsFinal

/-!
# Knowledge soundness of the deployed membership proof (the EIP's PCS claims), end to end

**`Soundness.knowledgeSoundness : PcsQuotient.KnowledgeSoundness Soundness.ksBound`** (`Soundness/PcsFinal.lean`):
the end statement of `formal/Statement` (`PcsQuotient/Security.lean`: the setup over one random permutation `π`, the
adversary given the circuit's commitment, its queries logged, the verifier over `π`), for the Statement's explicit,
computable extractor (`PcsQuotient.extractor`), proved with no hypothesis, on `propext`, `Classical.choice` and
`Quot.sound` only. For an adversary of at most `Q` calls of `π`, `π⁻¹`:

`ksBound Q = deployedBound (2^20 + 24 + Q) + (setupPermCalls + Q + verifierPermCalls)² / 2^508`,

`deployedBound` `SoundPcs`'s (six opening terms; the binding of the four roots' lists at their out-of-domain points,
`δc 25 + δc 27 + δc 28 ≤ 2^-166.5` a query; the four-root chain at `2^-164` a query, each challenge bounded for the one
candidate tuple the out-of-domain answers pin, `ComposePcs.Pinned4`), `setupPermCalls = 5 · 2^19 + 24`,
`verifierPermCalls = 10 + 6 · 121480`: about `2^-104.4` at `Q = 0`, `2^-85.4` at `Q = 2^40`, `2^-61.4` at
`Q = 2^64`, `125.4` bits as `Q/ε` (the six opening terms, `2^-128` a query each, dominate).

| File | What |
|---|---|
| `PcsRpm.lean` | `Compose/Rpm.lean`'s random-permutation transfer for any setup, adversary and verifier (`rpm_le_romG`): the game over `π` to mumbai's two oracles against one deterministic adversary, plus `(QSπ + Q + QV)² / 2^508`. |
| `PcsDExp.lean` | `SoundPcs.dExp`'s stages' logs dropped (`map_dExp`); the two-oracle game bounded by `dExp` given an outcome-by-outcome comparison (`le_dExp`). |
| `PcsOpenBridge.lean` | The Statement's opening check is F2's `pcsVerifyWithHashO` in any lawful monad (`pcsOpeningWithH_eq_O`). |
| `PcsChain.lean` | The wire (`pcsWire`); the Statement's reduction is `ComposePcs.chainWith4` then `claimsAt` (`reduceWithH_eq_chain4`). |
| `PcsVerifier.lean` | The Statement's verifier is `dExp`'s chain and six gated openings (`verifyWithH_eq_contD`), or rejects (`verifyWithH_reject`). |
| `PcsF1.lean` | A satisfying first message proves membership (`provesMembership_of_sat`, F0 with its random rows) and its stack spells a secret (`relation_of_sat`). |
| `PcsExtract.lean` | The event on transcripts (`ExtractsT`, `EvK`); `SoundPcs`'s extractor list holds a witness only where the extraction succeeds (`extracts_of_mem`); where it succeeds the Statement's extractor finds a secret (`extractor_of_extracts`). |
| `PcsDeployedM.lean` | `SoundPcs.knowledgeSoundness_deployed_pcs` for any committed wiring table and claims match (`knowledgeSoundness_deployed_pcsM`). |
| `PcsSetup.lean` | The Statement's setup is `SoundPcs.setupPcs` of its wiring table (`setupPcs_eq`), which carries the deployed σ (`wcol_carries`); the claims match (`claimsMatchK`). |
| `PcsGame.lean` | The Statement's experiment is a function of the transfer game and breaks only where its event holds (`soundnessExperiment_eq`, `prEvent_soundness_le`). |
| `PcsFinal.lean` | The comparison outcome by outcome (`hcmpK`), **`knowledgeSoundness`** and `ksBound`. |

`Soundness/{EarlyStop,Cost,TreeLog,MerkleWord,Replay,Extract,Final}.lean` are the previous protocol's modules pruned
to what the leanVM line imports (`TreeLog`, `MerkleWord`, `Replay`, `Extract` serve here too);
`Soundness/{Defs,Hypotheses,F1Step,RpmV}.lean` are the previous protocol's and no longer build (git history).
-/

/-- info: 'Soundness.knowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Soundness.knowledgeSoundness
