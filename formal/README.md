<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# formal/: Lean 4 proofs of the membership proof and of the leanVM recursion

## Status

Both lines state and prove the deployed protocols (main `7e6d353c`):

- **membership**: the deployed protocol ([`docs/membership/PROTOCOL.md`](../docs/membership/PROTOCOL.md), transcript
  `pcs-quotient-kc3`: three one-point claims on two commitments `W`, `T` and the circuit's, the gate `V = Y + C + X·C`,
  the public words pinned, `x h` in the quotient table). The previous protocol's (`f96a7938`, six claims on four
  commitments: [`docs/HISTORY.md`](../docs/HISTORY.md)) proof layers that the leanVM line still imports stay built
  (`QuotientSecurity`'s old F1 and F0, `Compose`, `formal/Circuit`, `WhirBridge`'s layout openings).
- **recursion**: **the deployed π2v4 over π1-rec4** (π1's three claims declared in the frame of PCS claims and hashed
  in π2's circuit, [`docs/leanvm/rec/SPEC-REC.md`](../docs/leanvm/rec/SPEC-REC.md)): π1-rec4's verifier
  (`UniKeccak.reduceWithK4`, tested against the Rust on the real π1-rec4 proofs), its recorded graph and graph =
  verifier at every setup commitment, its knowledge soundness (`UniKeccakSound.uniKnowledgeSoundnessKeccakRec4_closed`),
  its completeness (`UniKeccakComplete.uniCompletenessKeccakRec4_closed`), π2v4's statement, PIOP, circuit compiler and
  contract model, and the recursion's knowledge soundness at the real deployment
  (`RecCompose.recKnowledgeSoundness_reduction_real`) and completeness (`RecCompose.Pi1K.recCompleteness_real`, under
  two premises at Keccak-f[1600]).

What the port leaves is [`docs/LEAN_PORT.md`](../docs/LEAN_PORT.md). Both lines' Lean-facing files (AGENTS.md,
"Lean-facing outputs") are current: the Rust's writers write what the Lean states. Lean comments still cite the design
notes by their names at `f96a7938` (`docs/HISTORY.md` maps them).

Every end theorem below is sorry-free, without `native_decide`, on `propext`, `Classical.choice` and `Quot.sound` only
(`#guard_msgs` in each library).

## Provenance

Toolchain and dependencies are leanerVM `mumbai`'s (commit `6175f1a0`; Lean `v4.34.1`, Mathlib `d13f23b7`, VCVio
`afa6593f`, CompPoly `572f9973`, ArkLib `4dae3acf`), so its results are imported rather than reproved:
Keccak-256 and Keccak-f[1600], the random-permutation model, the WHIR verifier `verifyStackedOpening` and its
soundness, the prover's pieces, the list decoder. `QuotientSecurity` starts from leanVM's `formal/quotient` (branch
`PCS-openings-aggregation`, `651453c6`); `Lv42` is adapted from leanerVM `f0393df4`. Each adapted file says so in its
header.

## Membership: the end theorems

[`Statement/`](Statement/README.md) states the relation (Keccak-256 Merkle membership over the deployed Keccak-256),
the proof format, the verifier (computable, differential-tested against the Rust), the honest prover, the explicit
straight-line extractor and the simulator, in one random permutation; `EndToEnd/` proves them.

- **Knowledge soundness, no hypotheses.** `Soundness.knowledgeSoundness : PcsQuotient.KnowledgeSoundness
  Soundness.ksBound` (`EndToEnd/Soundness/PcsDeployed.lean`). `ksBound Q = deployedBound (2^20 + 24 + Q) +
  (5·2^19 + 24 + Q + 8 + 3·121480)^2/2^508`: about `2^-105.4` at `Q = 0`, `2^-86.4` at `2^40`, `2^-62.4` at `2^64`
  (126.4 bits as `Q/ε`). `deployedBound` (`SoundPcs`) is the three openings (`WhirBridge.Pcs.pcs_sound_oracle`, the
  out-of-domain point read off Keccak-256: the witness on `W`, 24 variables; the wiring on the circuit's commitment,
  24; the copy claim on `T`, 28; `2^-128` a query each, which dominate), the binding of the two roots' lists at their
  points (`ood_binding_coords` at 24 and 28 variables: `δc 24 ≤ 2^-165`, `δc 28 ≤ 2^-169`) and the two-root chain
  (`ComposePcs/Chain2.lean`, each challenge bounded for the one candidate pair the out-of-domain answers pin:
  `2^-164` a query, from F1's round error `2^-165`). The extractor `PcsQuotient.extractor` is explicit and computable.
  Stand-alone, not simulation-extractability. The layers:
  - **F1** (`formal/Kc3`, the reduction as polynomials, ideal commitments): `Kc3.Params.card_round1_le` (a first
    message whose cells fail the relation admits a consistent second message for at most `8 n q²` triples
    `(α, β, μ)`: the cells' denominators, `d d'(0) = 0`, the sum forced by the layout (`consistent_sum`: `I(0) = d
    d'(0) B₀(0)`, then `h = P / x` of degree `≤ n − 2` sums to zero over the cells, `Params.hSum`), the pole lemma
    (`Kc3.card_pole_le`: an error at a cell whose predecessor carries none has a pole of its own, by the circuit's
    `PoleCondition`), then the logarithmic derivatives), `card_round2_le` (the identity's degree, `≤ 4n − 1`),
    `card_round3_le` (`Conic.lean`: the witness claim's conic spans its plane, so a wrong value passes at most two `ρ`),
    `roundError_deployed` (`2^-165`), and the instance `Params.ofCantor` (`hSum` proved from the Cantor basis).
  - **F0** (`formal/Kc3Circuit`): the deployed circuit `PcsQuotient.membership 22` as `Kc3Deployed.deployedParams`;
    `poleCondition_deployed` (proved from the rows and the wiring, not evaluated); `relation_of_sat_deployed` (cells
    satisfying the gates, copies and pins spell a secret of the statement: Keccak's gadget on the swapped roles, the
    Horner packing of the public words, the anchors).
  - **The claims** (`EndToEnd/PcsBridge`: `Kc3Claims.claimsAt_spec`, `Kc3Accepts.accepts_of_claims`,
    `Kc3Deployed.matches_ofCantor`): the three claims hold of tables only if F1's verifier accepts their polynomials.
  - **The composition**: `ComposePcs/Chain2.lean` (two roots, `roundsSound_of`), `SoundPcs` (the deployed run, three
    openings), `Soundness/Pcs*.lean` (the random-permutation transfer, the extraction, `knowledgeSoundness_of_matches`).
- **Completeness, under one evaluated check.** `E2ECompleteness.completeness_end (hW : Pcs.H.WiringCheck) :
  PcsQuotient.Completeness Pcs.deltaPcs` (`EndToEnd/Completeness/E2ECompleteness/PcsDone.lean`), `deltaPcs =
  (7·2^24 + 3)/2^192 + 2/2^256 + 2^-304 + rpmError 2^48`, `deltaPcs_lt : deltaPcs < 2^-163` (about `2^-165`): the
  degenerate challenges (`β = 0`, a cell's denominator, `γ = 0` for `b₂`, `t` a root of `claimsAt`'s denominators,
  `ρ` the conic's), the openings' proofs of work, the permutation as two random oracles. `WiringCheck` is the wiring's
  coefficient `n − 2` nonzero (`Index::new`'s assert; `γ = 0` then holds for at most one `α` a `β`), evaluated by
  `lake exe membership-wiring-check` (it holds: coefficient `2^24 − 2` is `17280478925055366306`); the kernel cannot
  run a transform of `2^24` points. The honest prover's tables are proved to hold F1's honest messages (the quotient
  `q = q₀ + b₂ E` on the coset of `4 n` points, `mulX`/`divX` the products and quotients by `x` in the novel basis,
  `Kc3Deployed.sat_honest` for the randomized cells). For the Statement's prover; the deployed Rust prover is trusted
  for completeness.
- **Zero knowledge of the protocol over any zero-knowledge PCS, with `PcsZeroKnowledge` its only hypothesis.**
  `PcsQuotient.EndToEnd.zeroKnowledge_of_pcs (pcs : PcsOps (OracleComp RandomPermutationOracles) Hd)
  (sim : PcsSimulator) : PcsZeroKnowledge pcs sim εpcs → ZeroKnowledgeWith pcs sim.s₀ (zkSimulator sim) sim.oracle
  (fun Q ↦ εpcs Q + εgroup1 + εslack + εfs₀)` (`EndToEnd/ZK/PcsGroup1Prob.lean`; the experiment
  `pcsExperiment pcs` and `ZeroKnowledgeWith pcs` in `Statement/PcsQuotient/Security.lean`, the simulator and
  `PcsZeroKnowledge` in `Statement/PcsQuotient/Zk.lean`), `εgroup1 = (9·2^64 + 42)·2^-192 ≤ 2^-124`,
  `εslack = 2^-127 + 27·2^-192 ≤ 2^-126` and `εfs₀ = 58 · δq L ≤ 2^-163` proved (`Group1.εgroup1_le`, `spanFail_le`,
  `εfs₀_le`, `fiatShamirUniform_closed`). The theorem is for the
  protocol whose two secret tables are committed and opened by the PCS `pcs`, any program of the model (coins and
  `π`, `π⁻¹`, no programming of `π`); `PcsZeroKnowledge pcs sim εpcs` says that protocol is within `εpcs Q` of its
  hybrid over the ideal PCS (roots uniform and independent of the tables, the tables' out-of-domain answers, the
  openings `sim.simOpen`'s, which see only the commitment and the claim and may program `π`): the EIP's ZK-WHIR
  assumption in the prover's use of the PCS, not a stand-alone PCS game. It is satisfiable:
  `PcsParam.pcsZeroKnowledge_idealOf` proves it with `εpcs = 0` for the model's ideal PCS `PcsOps.idealOf simO` (uniform
  roots, any opening program `simO` of the commitment and the claim) and `PcsSimulator.ofOpen simO`, the protocol's
  experiment over it being its hybrid (`pcsExperiment_idealOf`), so `zeroKnowledge_ideal simO` is zero knowledge over
  that PCS within `εgroup1 + εslack + εfs₀`, with no hypothesis (`EndToEnd/ZK/PcsIdeal.lean`,
  `EndToEnd/ZK/PcsGroup1Prob.lean`). That ideal PCS is hiding but not binding: it
  shows the hypothesis consistent, so the theorem has content; that a sound ZK-WHIR satisfies it is not proved
  ([`docs/LEAN_PORT.md`](../docs/LEAN_PORT.md)). **The deployed PCS is not an instance**:
  `realPcs` (leanVM's WHIR: Merkle roots of the tables' words, opened leaves in the clear) is not zero knowledge, and no
  theorem states zero knowledge for the deployed prover (`realExperiment = pcsExperiment (realPcs …)`); soundness,
  completeness and the EVM theorem are about `realPcs`. The revealed scalars are proved uniform off
  `εgroup1 + εslack` of the challenges (`Group1.revealedUniform_closed : RevealedUniform (εgroup1 + εslack) 0`), in two
  groups ([`PROTOCOL.md`](../docs/membership/PROTOCOL.md), "Zero knowledge"):
  - **group 1** (`Group1.group1Uniform : Group1Uniform εgroup1`, `EndToEnd/ZK/PcsGroup1*.lean`): `W`'s answer and `X`,
    `C`, `V + Y` are a constant plus a `K`-linear map of the 32 random words (`group1_eq`: each a sum over the cells,
    `W`'s weights `Π_b (1 + (1 + z_b) B(⌊i/2^b⌋))` and the values' the Lagrange weights `w₂₄(t)/(t + δ + B(i))`, from the
    novel basis by an interpolation identity on the grid of digits), uniform where that map is onto `E⁴`
    (`group1At_of_surj`). It is onto (`onto_of_good`) when `w₂(t) ∉ K`, `t² + θt ∉ K` (then the select/pass rows'
    `s`-words reach `X + C + (V + Y)`, the sum rows' `V + Y`, the `r`-words `C`, through `1/(s + γᵢ)`, `γᵢ ∈ K`
    distinct, three of which span `E` over `K` as `[E : K] = 3`) and `W`'s point avoids one value of each of 42
    coordinates' events and `|K|` values of three (each quarter's `C`-blind combination of `r`-words reaches `W`'s
    answer through a nonzero product of affine factors in `z₀ … z₅`; the halves' planes, then the two halves, are
    separated by `z₄`, `z₅`: a plane mapped into itself by `ρ ∉ K` would be an `E`-line). Each event fixes one
    coordinate given the others (`prEvent_hit`, resampling it), or makes `t` a root of a degree-4 or degree-2
    polynomial.
  - **group 2**: `T`'s answer, uniform given everything else through the quotient table's four slack words, whose
    weights depend on `T`'s out-of-domain point alone (`revealedUniform_slack`, `εslack`).
  The general `zeroKnowledge_pcs_closed` takes `RevealedUniform εr δr` itself, `zeroKnowledge_pcs_slack`
  `Group1Uniform ε1`. Single proof, the distinguisher's queries after it.
- **The EVM contract is the verifier.** `Evm.evm_accepts_iff_verifyWith` (`EndToEnd/Evm/Contract.lean`): on a
  statement's and proof's calldata (273 bytes, no selector), the contract's recorded graph (`Implementation/Graph.lean`:
  537 nodes, 39 output words, three claims checked declared), with the stored index commitment and what the block
  proves of a declared claim modelled by `pcsOpen` (`Evm/PcsOpen.lean`), accepts exactly when `PcsQuotient.verifyWith`
  accepts at π = Keccak-f[1600]; `Evm.evm_accepts_iff_exists`: over all calldata, the contract accepts exactly the
  calldata of an accepted proof. `Implementation/` proves the graph computes `reduce` (`run_calldata`).

## leanVM by recursion: the end theorems

The Keccak VM is leanVM `42422001` with leanVM `9d50c92a3`'s `SHA3` (one Keccak-f[1600] step a row). π1 is the
univariate PIOP for its statement, π1-rec4 its variant for the recursion (wide Fiat–Shamir draws); π2 (π2v4) proves that
π1-rec4's recorded verifier graph at π1's setup commitment accepts and that its three claims hash to the words the
transaction's frame of PCS claims declares; the contract runs π2's verifier (its seed over the three frame words) and
checks seven claims (π1's `C1`, `C2`, setup `F` as declared; π2's `W`, setup, and `Q`'s identity and pushes' claims),
each the EIP draft's PCS claim, opened alone by `WhirBridge.Pcs`'s transcription of `verify_claim`. The reference is
128 signatures: `UniKeccakSound.keccakRefShape` = `RecGraphKeccak.Pi1.keccak128`: heights `15 16 15 16 14 15`, memory
`2^20`, bytecode `2^18`; `C1` `2^27` words, `C2` `2^26`, the setup `2^23`; π2's `W` `2^24`, its setup `2^25`, `Q`
`2^28`.

- **The statement.** `KeccakArith.kvSoundness` (under `Admissible prog s` and `SentinelSafe prog`, a stack satisfying
  `KvHolds F prog s input q` represents a `KeccakVm.ValidExecution`), `KeccakArith.kvCompleteness` (an execution with
  at most `2^32` instructions of every opcode has an honest stack), `KeccakFlushes.flushesSha3_eq`; the block
  `KeccakFlock.keccakFlockSpec` (`step_of_holds`, `holds_gen`, `in_gen`) and its structured terminal
  (`Core.structuredTerminal_eq_bilinear`).
- **π1, knowledge soundness**, in one random permutation, for the explicit extractor `uniExtractorK`:
  `UniKeccakSound.uniKnowledgeSoundnessKeccak_closed` (at `keccakRefShape` and the deployed program IV; `≤ 2^-64` for
  `Q ≤ 2^64`, `2^-64.87` at `2^64`, 128.87 bits as `Q/ε`), `uniKnowledgeSoundnessKeccakRec3_closed` (π1-rec3,
  128.49 bits) and `uniKnowledgeSoundnessKeccakRec4_closed` (π1-rec4, the recursion's: `uniBound128 (2^35/|E|)`, at most
  `2^-64` at `Q ≤ 2^64`). The three openings are charged once at `269 · 2^-137` (`WhirBridge.Pcs.pcs_union_sound`).
- **π1, completeness**: `UniKeccakComplete.uniCompletenessKeccak_closed`, `uniCompletenessKeccakRec3_closed` and
  `uniCompletenessKeccakRec4_closed` (π1-rec4, the prover `Rec4.uniProverRec4RP`), for an explicit Lean honest prover, error `Prob.deltaK < 2^-169` (`deltaK_lt`), under `D.shape = keccakRefShape`,
  `D.programIv.length ≤ 2^16` and **`32 ≤ D.programIv.length`** (the deployed IV has 32 bytes).
- **π1-rec4's graph.** `RecGraphKeccak/Emitted.lean` is the π1-rec4 graph the Rust recorded (10,840 nodes, 59
  Keccak-256 calls, 10 `wide` nodes, 3 claims); `RecGraphKeccak.Sim.pi1GraphIsVerifierK4`, no hypothesis: for every
  permutation, the Lean recording `pi1GraphK4` computes π1-rec4's verifier (`UniKeccak.runWithK4`) off the merge
  hazard (`MergeHazardK4`: challenges 45 and 46); `GraphsAgreeK4` (`pi1GraphK4 = Emitted.graph`) evaluated;
  `hazard_probK`: at most `2^16` hazardous `t` per `p_0` (`2^-176`); `graphAtSetup` and
  `pi1GraphIsVerifierK4At`: the graph at every π1 setup commitment. π1-rec3's program and `pi1GraphIsVerifierK` are
  kept.
- **π2's circuit.** `RecCircuit.Compiled.compile_sound_end` (`EndStatement`: the statement port, the zero ports, and
  each `ClaimHash` port carrying the Keccak-256 of its claim's encoding); `RecGraphKeccak.pi1rec4K_end`,
  `pi1rec4K_claimHashes` at the emitted graph, π1's three claims hashed; the Lean compiler's circuit is the Rust's byte
  for byte (`rec-circuit-diff`, `rec-circuit-keccak`).
- **π2's PIOP** (`RecPiop`, π2v4): the copy argument, the identity's claim `I(t) = 0` with `I = D²H + xZDq + x²Z³G +
  xDR` and the layout lemma (`I = 0`, `D(0) ≠ 0` give `H = x h`, `Σ_V h = 0`, `h D + R = 0` on `V_m`), the pushes'
  claim, round-by-round sound (`Rounds.lean`).

### The recursion's end theorems

Statements in `RecStatement/Security.lean` and `Reduction.lean`, proofs in [`RecCompose/`](RecCompose/README.md).
π2's circuit computes π1-rec4's Fiat–Shamir with the real Keccak-f[1600], while π1-rec4's theorems are in the
random-permutation model, so the end theorems meet at Keccak-f[1600].

```lean
theorem RecCompose.recKnowledgeSoundness_reduction_real (prog : KeccakVm.Program)
    (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize) (hg : RecGraphKeccak.GraphsAgreeK4)
    (hd : DigestChecked) (hs : SetupRootChecked) (hiv : IvChecked) :
    RecKnowledgeSoundnessReduction (realDeployment prog hprog) pi2Bound ∧
      ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64
```

- **Knowledge soundness as an explicit reduction, no Fiat–Shamir or collision-resistance premise**: Pr[the contract
  accepts ∧ `recExtractor` finds no `KvHolds` witness] ≤ `pi2Bound Q` + Pr[`pi1Adversary` breaks π1-rec4 at
  Keccak-f[1600]] + Pr[`hazardAdversary` hits the merge hazard] + Pr[`collisionAdversary` outputs a Keccak-256
  collision], the three adversaries explicit (the adversary, then π2's extractor; same query count). `pi2Bound`:
  π2's Fiat–Shamir and the seven openings, charged once (`WhirBridge.Pcs.UnionO.pcs_union_sound_oracle`), `Q`'s two
  claims bound to one table by its out-of-domain answer (`RecCompose.qOodBinding`, `2^-156` a query): `2^-64.93` at
  `2^64`, 128.93 bits as `Q/ε`. `recExtractor` decodes `W`, reads π1's stream off the first candidate on which
  π1-rec4's graph at the setup commitment accepts with claims hashing to the declared ones, then runs `uniExtractorK`;
  π1's claims being named by their hashes, a candidate whose claims differ from the declared ones is a Keccak-256
  collision (`collisionCoupling`).
- **Completeness**: `RecCompose.recCompleteness_end` (`CompleteCouplings`): `RecCompletenessWith D (composeProver D P1
  P2) (δ1 + δh + δ2)` from π2's part `RecCompleteness2 D P1 P2 δ2`, `Pi1CompletenessKeccak δ1`,
  `Pi1HazardKeccakHonest δh`. Proved for it: π1's prover in the recursion, `RecCompose.Pi1K.pi1Rec4ProverK` (π1-rec4's
  Lean prover, its Fiat–Shamir over Keccak-f[1600], its trees and openings over `π`), and the four facts π2's part takes
  of it (`pi1ProverFactsK4`: over `π` it is its two-call program, disciplined, at most `2^47` blocks, every hash input
  shorter than `2^26` bytes); `pi1CompletenessKeccak_iff4` and the random-permutation reading of `Pi1CompletenessKeccak`
  (`pi1CompletenessFs4_rpm`, `deltaK < 2^-169`, from `uniCompletenessKeccakRec4_closed`); π2's Lean prover agrees with
  the Rust's on 3/3 vectors and the contract accepts its proof off `BadCopy`, `BadT`, `BadRho` at the real deployment
  (`RecCompose.Pi2E.pi2_accepts_real`, its witness and π1's openings from π1-rec4's graph verifier accepting); π2's
  error (`Pi2Sim.recCompleteness2_pi2_closed`: `RecCompleteness2` for π2's Lean prover, `delta2Closed ≤ 2^-164`, about
  `2^-164.4`; the copy argument's `2N|E|²` bad triples, `t`'s `10N + 1` bad points, `ρ`'s one, `α`'s and `t`'s inputs
  fresh, the proofs of work, the permutation as random oracles). **The end theorem**:

  ```lean
  theorem RecCompose.Pi1K.recCompleteness_real (prog) (hprog) (hg : GraphsAgreeK4) (hd : DigestChecked)
      (hs : SetupRootChecked) (hiv : IvChecked) (δ1 δh : ℝ≥0∞)
      (h1 : Pi1CompletenessKeccak (realDeployment prog hprog) (pi1Rec4ProverK _) δ1)
      (hh : Pi1HazardKeccakHonest (realDeployment prog hprog) (pi1Rec4ProverK _) δh) :
      RecCompletenessWith (realDeployment prog hprog)
        (composeProver _ (pi1Rec4ProverK _) (realPi2Prover prog hprog hg hd hs hiv)) (δ1 + δh + 2⁻¹ ^ 164)
  ```

  for the composed Lean provers (the deployed Rust provers are trusted for completeness); `h1` and `hh` are about the
  honest π1-rec4 run at the real Keccak-f[1600] (the Fiat–Shamir heuristic for one fixed honest prover; `h1`'s
  random-permutation reading is proved at `deltaK < 2^-169`).
- Also `recKnowledgeSoundness2_final` (π2's part alone) and the Prop-premise corollary `recKnowledgeSoundness_final`,
  whose premises `Pi1FsKeccak`, `Pi1HazardKeccak`, `Keccak256CR` are **false as stated** for unbounded adversaries
  (they grind Keccak-f[1600] offline): read them as the Fiat–Shamir heuristic and collision resistance.
- **Evaluated, not proved** (the hypotheses of `recKnowledgeSoundness_reduction_real`): `GraphsAgreeK4`
  (`RecGraphKeccakTest/Pi1Check.lean`), `DigestChecked`, `SetupRootChecked` (`rec-real-check`), `IvChecked` over
  `(roots, iv)` at the reference setup commitment and the reference, zero and all-ones IVs (`rec-real-check`,
  `rec-view-check`), assumed elsewhere.

**What the recursion's hypotheses and model amount to.** (a) `IvChecked` is in effect an **assumption** where the
theorems use it: they apply it at π1's setup commitment as the honest setup computes it over `π`, which is almost never
the reference commitment `realRoots`, and `ivCheck` is evaluated only at `realRoots` × three IVs (reference, zero,
all-ones); its uniformity in the IV and in the setup commitment is assumed (plausible: the commitment enters the
compiled circuit only through π1's contract IV and the hashed `F` claim's root and answer words; `PatchChecked`, not
proved, would give the IV half). (b) **The frame of PCS claims is modelled as the declared claims themselves**: the
contract model reads the claims, not Keccak-256 payloads it would match against them, so Keccak-256's collision
resistance on the frame's payloads (π2's four claims included) is built into the model; the reduction's
`collisionAdversary` covers only the in-circuit hash of π1's three claims. (c) `DigestChecked` and `SetupRootChecked`
pin the model's `σ`, `κ` to the deployed contract's constants; they carry no proof weight. (d) There is no Lean
differential run of π2's verifier against the Rust's (its outputs, the claims' points and values and `all`, on the real
proof): π2's Lean prover is tested against the Rust's (3/3 vectors), and the contract's bytecode equals the Rust
verifier by the Rust's tests, but the Lean verifier's agreement with the Rust verifier rests on the transcription and
on `RecStatement/Data.lean` being the Rust's data.

## Trusted, tested, not covered

| | Membership | Recursion |
|---|---|---|
| Trusted | the Lean kernel and three axioms; Keccak-f[1600] a random permutation, Keccak-256 its sponge; mumbai's definitions (Keccak, the model, `verifyStackedOpening`, the decoders); the prover's randomness uniform (deployed: a Keccak-256 KDF, `Randomness::derive`, so computational ZK) | the same; the deployed Rust provers for completeness |
| Tested against the Rust (main `7e6d353c`) | the Statement (`membership-differential`: 121 reductions, 18 honest and tampered proofs at `2^17` rows, the small, toy and membership circuits' commitments, all agreeing); the Statement's prover (the reduction's stream at `2^17` rows, and its proof accepted); the circuit's rows and σ (`kc3-dump-circuit`, SHA-256 `7b73dc3b…`); bytecode = graph (`graph_lean_is_current`, `Implementation/Diff.lean` on 1000 calldata); `FIELD_MUL` = `mulE` by vectors; `pcs_claim::verify` = `pcsOpening` (`WhirBridge/Test/CheckPcs.lean`) | π1's verifier (`UniKeccakTest/Runner.lean`: 134/134 verifier and 14/14 terminal vectors, the real π1-rec4 proofs among them); the verifier's tables, the block's rows and terminal, `sha3Step`; the circuit compiler on π1-rec4's graph (`rec-circuit-diff`, `rec-circuit-keccak`: the Rust's circuit byte for byte; `padCounts` on 202 cases); π2's Lean prover on 3/3 vectors (roots, IV, stream); `RecStatement/Data.lean` is what the Rust emits (`keccak_statement_data_is_current`); the bytecode is π2's Rust verifier by the Rust's tests (`parity`) |
| Evaluated, not proved | `WiringCheck` (completeness's hypothesis: the wiring's coefficient `n − 2` nonzero, `membership-wiring-check`) | `GraphsAgreeK4`, `DigestChecked`, `SetupRootChecked`, `IvChecked` (at the reference setup commitment and three IVs) |
| Not covered | simulation-extractability; ZK with queries before the proof, or for several proofs; the RPM theorems and the EVM one do not formally compose; `StatementBinds` (immediate, not proved); pruned Merkle paths | the model gap (π1-rec4 in the RPM, π2's circuit at Keccak-f[1600]); `PatchChecked` and `IvChecked` at other setup commitments; other shapes than the reference; no Lean differential run of π2's verifier |

## Libraries

| Library | What |
|---|---|
| [`Statement`](Statement/README.md) (`PcsQuotient`) | membership: definitions and end statements only |
| `EndToEnd` | the Lake workspace; libraries `Soundness`, `E2ECompleteness`, `ZK`, `Evm` (membership end theorems), `PcsBridge` (the claims as F1's verifier), `Bridge`, `Shared` (shared with the leanVM line) |
| [`Kc3`](Kc3/) | F1 of the deployed protocol: the reduction as polynomials, its three rounds, the Cantor instance |
| `Kc3Circuit` | F0 of the deployed circuit: its rows and wiring, the pole condition, the relation, the honest cells, the dump test |
| `Circuit`, `Field` | the previous protocol's circuit (its Keccak definitions are the leanVM line's); `F192` |
| [`QuotientSecurity`](QuotientSecurity/README.md) | the previous protocol's F1 and F0 (their generic parts serve `Kc3`; the leanVM line imports them) |
| `QuotientRpm` | F4a: the reduction's Keccak-256 chain, ROM then RPM |
| [`WhirBridge`](WhirBridge/README.md) | F2: the PCS claim (version 1) and the layout openings, under mumbai's WHIR soundness |
| [`Compose`](Compose/README.md), `ComposePcs`, `SoundPcs` | F4b: the composition with real commitments; the deployed protocol's two-root chain (`ComposePcs/Chain2.lean`) and run (`SoundPcs`) |
| `Completeness` | the previous protocol's completeness layers the leanVM line imports |
| `Implementation` | F5: the contract's recorded graph and its interpreter |
| `Lv42` | leanVM `42422001`'s instruction set, machine, tables and M3 instance (from leanerVM `f0393df4`) |
| [`KeccakVm`](KeccakVm/README.md) | the Keccak VM's instruction set and relation `KvHolds` |
| [`KeccakArith`](KeccakArith/README.md), `KeccakFlushes` | the arithmetization's soundness and completeness; the `SHA3` flushes |
| [`KeccakFlock`](KeccakFlock/README.md) | the Keccak-f block `keccakFlockSpec` and its terminal |
| [`UniStatement`](UniStatement/README.md), `UniSound`, [`UniComplete`](UniComplete/README.md) | the univariate verifier's generic layers: statement, soundness, honest prover |
| `FlockSound` (`FlockSoundUni`), `Heap` | Flock's verifier soundness; the product heap |
| [`UniKeccak`](UniKeccak/README.md) | π1's verifier at the Keccak VM, and its statements |
| [`UniKeccakSound`](UniKeccakSound/README.md), [`UniKeccakComplete`](UniKeccakComplete/README.md) | π1's knowledge soundness; its honest prover and completeness |
| [`RecGraph`](RecGraph/README.md), [`RecGraphKeccak`](RecGraphKeccak/README.md) | recorded graphs (π1-rec4's `wide` nodes); π1-rec4's and π1-rec3's graph = verifier, the hazard |
| [`RecCircuit`](RecCircuit/README.md), `RecPiop` | π2's circuit compiler (π1-rec4's `wide` nodes, hashed claims); π2's PIOP (π2v4) |
| [`RecStatement`](RecStatement/README.md) | π2's verifier (π2v4), the contract's seven claims, the recursion's end statements |
| [`RecCompose`](RecCompose/README.md) | their proofs |

## Building

On h1, under `/root/pcs-quotient-fv/` only (AGENTS.md, "Lean builds"): copy the repository there (rsync, without
`.lake`), link `formal/leanervm` to `/root/pcs-quotient-fv/leanervm` (a built leanerVM `6175f1a0`), then:

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=12G lake build Soundness E2ECompleteness Evm ZK      # membership end theorems
systemd-run --scope -p MemoryMax=12G lake build Kc3 Kc3Circuit PcsBridge SoundPcs ComposePcs Implementation \
  PcsQuotient                                                                          # their layers
systemd-run --scope -p MemoryMax=12G lake exe membership-wiring-check                 # WiringCheck
systemd-run --scope -p MemoryMax=32G lake exe membership-differential vectors.txt     # against statement_vectors' vectors
systemd-run --scope -p MemoryMax=12G lake exe kc3-dump-circuit OUT                    # against dump_circuit's
systemd-run --scope -p MemoryMax=12G lake build KeccakVm KeccakArith KeccakFlushes KeccakFlock UniKeccak UniKeccak.Fits \
  UniStatement.KeccakTables UniKeccakSound UniKeccakComplete RecGraphKeccak RecCircuit rec-circuit-keccak RecStatement \
  RecPiop RecCompose                                                                   # the leanVM line
systemd-run --scope -p MemoryMax=12G lake env lean ../RecGraphKeccak/RecGraphKeccakTest/Pi1Check.lean   # GraphsAgreeK4
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check               # DigestChecked, ivCheck at three IVs
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check --setup-only  # SetupRootChecked
systemd-run --scope -p MemoryMax=12G lake exe rec-view-check               # viewCheck
```

A build of many libraries at once runs many `lean` processes, each mapping several GB of imported `.olean`s; under a
memory cap, limit lake's workers (`LEAN_NUM_THREADS=3 lake build …`).

`#guard_msgs` in each library checks the axioms. The differential tests' commands are in the package READMEs; both
lines' vectors are the deployed Rust's.

## Remaining

1. **The model gap.** π2's circuit computes π1-rec4's Fiat–Shamir with the real Keccak-f[1600]; π1-rec4's theorems are
   in the random-permutation model, so the soundness reduction's π1 and hazard terms and the two completeness premises
   are left to the Fiat–Shamir heuristic for Keccak-f[1600], its collision term to Keccak-256's collision resistance.
2. **The evaluated checks** are Props checked by running Lean, not kernel proofs: membership's `WiringCheck`; the
   recursion's `GraphsAgreeK4`, `DigestChecked`, `SetupRootChecked`, `IvChecked`. `IvChecked` (over π1's setup
   commitment and IV) is evaluated at the reference commitment's three IVs and assumed at the others:
   `IvUniform.ivChecked_of_patchChecked` reduces it, at each commitment, to `PatchChecked`, not proved (a relational
   simulation of about 1,200 lines of the builder).
3. **Other shapes**: π1's closed bounds are at the reference shape.
4. **Membership**: `WiringCheck` by a kernel proof; zero knowledge with a pre-proof phase;
   simulation-extractability; a few lemmas duplicated between the soundness and completeness lines
   (`Soundness/PcsVH*.lean`, `tableEval_eq_mle`, `tau_systemL`).
5. Declarations in the shared libraries that no end theorem uses (the previous protocol's F1 and F0 in
   `QuotientSecurity`, its layout openings in `WhirBridge`, `Compose`'s `knowledgeSoundness_deployed_rust`,
   `ComposePcs`'s four-root chain, `formal/Circuit`): still built, as the leanVM line imports them.
