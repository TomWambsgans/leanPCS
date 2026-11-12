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
import ZK.PcsSlack
import ZK.PcsSpan
import ZK.PcsIdeal
import ZK.PcsGroup1Alg
import ZK.PcsGroup1Weights
import ZK.PcsGroup1W
import ZK.PcsGroup1Map
import ZK.PcsGroup1Unif
import ZK.PcsGroup1Span
import ZK.PcsGroup1Rows
import ZK.PcsGroup1Onto
import ZK.PcsGroup1Prob
import ZK.PcsAxioms

/-!
# Zero knowledge, end to end (the EIP's PCS claims)

`PcsQuotient.ZeroKnowledgeWith pcs` (`formal/Statement`, `Security.lean`: the protocol with its two secret tables
committed and opened by the PCS `pcs`, a program of the model) for the simulator `PcsQuotient.zkSimulator`
(`Zk.lean`), for every zero-knowledge PCS `pcs` (`docs/membership/PROTOCOL.md`, "Zero knowledge"). The deployed PCS
(`realPcs`, leanVM's WHIR) is not zero-knowledge and not an instance.

**The end theorem, `PcsQuotient.EndToEnd.zeroKnowledge_of_pcs`** (`ZK/PcsGroup1Prob.lean`), for every `pcs` and `sim`:
`PcsZeroKnowledge pcs sim εpcs → ZeroKnowledgeWith pcs sim.s₀ (zkSimulator sim) sim.oracle
(fun Q ↦ εpcs Q + εgroup1 + εslack + εfs₀)`, `εgroup1 ≤ 2^-124`, `εslack ≤ 2^-126`, `εfs₀ ≤ 2^-163`: the PCS's zero
knowledge its only hypothesis. It composes the pieces below.

**`PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed`** (`ZK/PcsFSClosed.lean`), for every `pcs` and `sim`:
`PcsZeroKnowledge pcs sim εpcs → RevealedUniform εr δr →
ZeroKnowledgeWith pcs sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + εr + δr + εfs₀)`, `εfs₀ ≤ 2^-163`
(`εfs₀_le`), from `zeroKnowledge_pcs` (`ZK/PcsEnd.lean`, with `FiatShamirUniform εfs` as a hypothesis) and
`fiatShamirUniform_closed`. `RevealedUniform εr δr` is statistical: outside `εr` of the challenges the revealed
scalars are within `δr` of uniform.

* `ZK/PcsTrace.lean`: the adaptivity argument for any program of black-box steps and reveal queries (`RProg`):
  answering the reveals by a function of the coins (`c ← μ`) or by fresh uniform draws differs, on every event,
  by at most the uniform run's expected shortfall of the coins' mass of its logged answers (`trace_le_approx`).
* `ZK/PcsProc.lean`: the Statement's `challengePhase` as such a program (`phaseProg`); its log's queries are
  `revealQueries` of the challenges it returns, its answers the output's revealed scalars (`answersOf`).
* `ZK/PcsReplay.lean`, `ZK/PcsRoot.lean`, `ZK/PcsHybrid.lean`: the hybrid prover (`proveWithPcs` with the ideal
  PCS) is the challenge phase with the prover's answers, then the openings (`hybrid_run_eq`): the reduction's
  chain, recomputed by the prover, replays in the lazily sampled permutation; the roots read back are the
  prover's (`rootOfHalves_rootHalves`).
* `ZK/PcsCoins.lean`: the model's coins (the prover's randomness, uniform elements of `E`) as `ProbComp`.
* `ZK/PcsEnd.lean`: the end theorem under `FiatShamirUniform`; `ZK/PcsAxioms.lean`: the axioms.
* The Fiat–Shamir term (`fiatShamirUniform_closed`, `ZK/PcsFSClosed.lean`): `ZK/PcsFresh.lean` (the lazily
  sampled permutation against independent uniform answers on tracked queries: `close`, the cost `badB` along the
  ideal run), `ZK/PcsPhaseF.lean` (the challenge phase with its `58` permutation calls tracked: `W`'s and `T`'s
  out-of-domain points, `24` and `28`, and the chain's `α, β, μ, t` one call each and `ρ` two; its five revealed
  scalars drawn, `FProg.r`), `ZK/PcsExtract.lean`, `ZK/PcsStream.lean`, `ZK/PcsPhi.lean`, `ZK/PcsIdealC.lean` (the
  ideal run's challenges and revealed scalars are independent and uniform: `ideal_joint`), `ZK/PcsBad*.lean`,
  `ZK/PcsAdds.lean`, `ZK/PcsNF.lean`, `ZK/PcsInj.lean` (each tracked input is injective in a value drawn just before
  it, among at most `5 · 2^19 + 90` edges: `phase_bound`).

**The slack words** (`ZK/PcsSlack.lean`): `T`'s out-of-domain answer is the answer without the four slack words
plus their contribution `slackMap z`, its weights functions of `T`'s out-of-domain point `z` alone (`oodT_eq`);
where they span `E` over `K` (`SlackSpan`) that contribution is uniform (`slackMap_uniform`), so the revealed
scalars' mass is uniform as soon as group 1's is (`rMass_eq`, `uniformWithin_zero`).
**`revealedUniform_of_group1`**: `Group1Uniform ε1 → RevealedUniform (ε1 + spanFail) 0`, and
**`zeroKnowledge_pcs_group1`**: zero knowledge from `PcsZeroKnowledge` and `Group1Uniform` alone, within
`εpcs Q + ε1 + spanFail + εfs₀`. `Group1Uniform` (`W`'s answer, `C`, `V + Y`, `X` exactly uniform at all but `ε1` of
the challenges: the 32 random-row words' map onto `E⁴`) is proved below.

**The span failure, bounded** (`ZK/PcsSpan.lean`): the slack's weights are `C(z) · {1, u₀, u₁, u₂}` times
`(1+z₀)(1+z₁)(1+z₂)`, `u_j = z_j/(1+z_j)` (`weight_closed`), so they span `E` once `C(z) ≠ 0`, `u₀ ∉ K` and `u₁` or
`u₂` lies outside `K + K·u₀` (`span3`, `slackSpan_of`); over `T`'s 28 independent uniform coordinates
**`spanFail_le`**: `spanFail ≤ εslack = 27 · 2^-192 + 2^64 · 2^-192 + (2^128 · 2^-192)² ≤ 2^-126` (`εslack_le`).
**`zeroKnowledge_pcs_slack`**: zero knowledge over every `pcs` from `PcsZeroKnowledge pcs sim εpcs` and
`Group1Uniform ε1` alone, within `εpcs Q + ε1 + εslack + εfs₀`.

**The PCS hypothesis is satisfiable** (`ZK/PcsIdeal.lean`): the model's ideal PCS `PcsOps.idealOf simO` (uniform roots,
the tables' out-of-domain answers, openings any program `simO` of the commitment and the claim) meets it with
`εpcs = 0` for `PcsSimulator.ofOpen simO` (**`pcsZeroKnowledge_idealOf`**; the protocol's experiment over it is the
hybrid, `pcsExperiment_idealOf`, through the prover read through a monad morphism, `proveWithPcs_hom`), so
**`zeroKnowledge_idealOf`** is zero knowledge over it within `ε1 + εslack + εfs₀` under `Group1Uniform ε1`.

**Group 1, proved** (`ZK/PcsGroup1*.lean`, namespace `PcsQuotient.EndToEnd.Group1`):
* `PcsGroup1Alg.lean`: `E` over `K` (`finrank_KE = 3`; a root of a monic quadratic over `K` lies in `K`,
  `mem_K_of_quad`; `indep3_inv`: `1/(s + γᵢ)` independent for `s ∉ K`, distinct `γᵢ ∈ K`; planes, `kernel4`).
* `PcsGroup1Weights.lean`: the cells' weights, by an interpolation identity on the grid of digits (`sum_prod_gen`):
  `W`'s answer `Σ_i vᵢ Π_b (1 + (1 + z_b) B(⌊i/2^b⌋))` (`tableEval_coefficients`), the cells' polynomial at `x ∈ E`
  `Σ_i vᵢ Λᵢ(x)`, `Λᵢ(x) (x + B(i)) = w₂₄(x)` (`nov_coefficients_eval`, `lam_mul`); the values at `t` are it at `t`,
  `t + θ`, `t + 1` plus `t + θ + 1` (`valuesAt_cells`).
* `PcsGroup1Map.lean`: **`group1_eq`**, group 1 a constant plus `Lsum` of the random words (`sum_cells_decomp`).
* `PcsGroup1Unif.lean`: **`group1At_of_surj`**, uniform where the words' map `Lmap` is onto `E⁴`.
* `PcsGroup1W.lean`, `PcsGroup1Span.lean`, `PcsGroup1Rows.lean`, `PcsGroup1Onto.lean`: the words' weights in closed
  form off `K`, `surj_of_steps`, `W`'s weights by quarter of rows (`RW_W`), and **`onto_of_good`**.
* `PcsGroup1Prob.lean`: the good event fails with probability at most `εgroup1 = (9 · 2^64 + 42) · 2^-192 ≤ 2^-124`
  (`prEvent_notGood`, `εgroup1_le`); **`group1Uniform : Group1Uniform εgroup1`**; `revealedUniform_closed`;
  **`zeroKnowledge_of_pcs`**: zero knowledge over every `pcs` from `PcsZeroKnowledge pcs sim εpcs` alone, within
  `εpcs Q + εgroup1 + εslack + εfs₀`; **`zeroKnowledge_ideal`**: over the model's ideal PCS, with no hypothesis.

`ZK/ProverBridge{Eager,Hom,Param}.lean` (random-permutation lemmas kept from the hidden-layout protocol's proof,
which was removed): `Hom` and `Param` are imported here only through `ZK/PcsIdeal.lean` (`MHom`, `keccak256With_hom`),
`Eager` not; `RecCompose` imports `ZK/ProverBridgeEager.lean` and `ZK/ProverBridgeParam.lean` directly.
-/
