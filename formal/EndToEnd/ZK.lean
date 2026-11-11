-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import ZK.PcsTrace
import ZK.PcsProc
import ZK.PcsReplay
import ZK.PcsRoot
import ZK.PcsHybrid
import ZK.PcsCoins
import ZK.PcsEnd
import ZK.PcsFresh
import ZK.PcsPhaseF
import ZK.PcsExtract
import ZK.PcsStream
import ZK.PcsPhi
import ZK.PcsIdealC
import ZK.PcsBad
import ZK.PcsAdds
import ZK.PcsNF
import ZK.PcsInj
import ZK.PcsBadQ
import ZK.PcsBadOod
import ZK.PcsBadPhase
import ZK.PcsFSClosed
import ZK.PcsAxioms

/-!
# Zero knowledge, end to end (the EIP's PCS claims)

`PcsQuotient.ZeroKnowledgeWith` (`formal/Statement`, `Security.lean`) for the simulator `PcsQuotient.zkSimulator`
(`Zk.lean`), assuming a zero-knowledge PCS (`docs/membership/PROTOCOL.md`, "Zero knowledge"):

**`PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed`** (`ZK/PcsFSClosed.lean`):
`PcsZeroKnowledge sim εpcs → RevealedUniform εr →
ZeroKnowledgeWith sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + εr + εfs₀)`, `εfs₀ ≤ 2^-163` (`εfs₀_le`),
from `zeroKnowledge_pcs` (`ZK/PcsEnd.lean`, with `FiatShamirUniform εfs` as a hypothesis) and
`fiatShamirUniform_closed`.

* `ZK/PcsTrace.lean`: the adaptivity argument for any program of black-box steps and reveal queries (`RProg`):
  answering the reveals by a function of the coins (`c ← μ`) or by fresh uniform draws differs, on every event,
  by at most the probability that the ideal run's log of reveals is not good (`trace_le`).
* `ZK/PcsProc.lean`: the Statement's `challengePhase` as such a program (`phaseProg`); its log's queries are
  `revealQueries` of the challenges it returns.
* `ZK/PcsReplay.lean`, `ZK/PcsRoot.lean`, `ZK/PcsHybrid.lean`: the hybrid prover (`proveWithPcs` with the ideal
  PCS) is the challenge phase with the prover's answers, then the openings (`hybrid_run_eq`): the reduction's
  chain, recomputed twice by the prover, replays in the lazily sampled permutation; the roots read back are the
  prover's (`rootOfHalves_rootHalves`).
* `ZK/PcsCoins.lean`: the model's coins (the prover's randomness, uniform elements of `E`) as `ProbComp`.
* `ZK/PcsEnd.lean`: the end theorem under `FiatShamirUniform`; `ZK/PcsAxioms.lean`: the axioms.
* The Fiat–Shamir term (`fiatShamirUniform_closed`, `ZK/PcsFSClosed.lean`): `ZK/PcsFresh.lean` (the lazily
  sampled permutation against independent uniform answers on tracked queries: `close`, the cost `badB` along the
  ideal run), `ZK/PcsPhaseF.lean` (the challenge phase with its `58` permutation calls tracked: `W`'s and `T`'s out-of-domain points, `24`
  and `28`, and the chain's `α, β, μ, t` one call each and `ρ` two), `ZK/PcsExtract.lean`,
  `ZK/PcsStream.lean`, `ZK/PcsPhi.lean`, `ZK/PcsIdealC.lean` (the ideal run's challenges are uniform:
  `ideal_challenges`), `ZK/PcsBad*.lean`, `ZK/PcsAdds.lean`, `ZK/PcsNF.lean`, `ZK/PcsInj.lean` (each tracked input is
  injective in a value drawn just before it, among at most `5 · 2^19 + 90` edges: `phase_bound`).

`ZK/ProverBridge{Eager,Hom,Param}.lean` (random-permutation lemmas kept from the hidden-layout protocol's proof,
which was removed) are not imported here; `RecCompose` imports `ZK/ProverBridgeEager.lean` and
`ZK/ProverBridgeParam.lean` directly.
-/
