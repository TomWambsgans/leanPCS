<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# formal/: Lean 4 proofs of the membership proof and of the leanVM recursion

## Status

- **membership**: the deployed protocol ([`docs/membership/PROTOCOL.md`](../docs/membership/PROTOCOL.md), transcript
  `pcs-quotient-kc3`: three one-point claims on two commitments `W`, `T` and the circuit's, the gate `V = Y + C + X·C`,
  the public words pinned, `x h` in the quotient table). The previous protocol's (`f96a7938`, six claims on four
  commitments: [`docs/HISTORY.md`](../docs/HISTORY.md)) proof layers that the leanVM line still imports stay built
  (`QuotientSecurity`'s old F1 and F0, `Compose`, `formal/Circuit`, `WhirBridge`'s layout openings).
- **recursion**: π2 (π2v3) over π1-rec3, π1's three claims encoded by the contract, the protocols of `f96a7938`;
  deployed: π2 over π1-rec4, π1's three claims hashed in π2's circuit
  ([`docs/leanvm/rec/SPEC-REC.md`](../docs/leanvm/rec/SPEC-REC.md)); the port is [`docs/LEAN_PORT.md`](../docs/LEAN_PORT.md).
  Until it lands, do not regenerate the leanVM line's Lean-facing files (`crates/leanvm/rec/tests/lean_*.rs`).

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
- **Zero knowledge, under two hypotheses.** `PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed : PcsZeroKnowledge sim εpcs
  → RevealedUniform εr δr → ZeroKnowledgeWith sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + εr + δr + εfs₀)`
  (`EndToEnd/ZK/PcsFSClosed.lean`; hypotheses and simulator in `Statement/PcsQuotient/Zk.lean`), `εfs₀ = 58 · δq L ≤
  2^-163` proved (`fiatShamirUniform_closed`). `PcsZeroKnowledge` is the EIP's ZK-WHIR assumption (the reference
  openings are not zero knowledge). `RevealedUniform εr δr` (outside `εr` of the challenges, the five revealed scalars
  are within statistical distance `δr` of uniform) is not proved: group 1 (`W`'s answer, `X`, `C`, `V + Y`) is
  `K`-affine in the random rows with a linear part fixed by the challenges, exact at full rank; group 2 (`T`'s
  answer) is `K`-affine in the six blinding words with a linear part that depends on the random rows (through
  `d d'` and `b₂`), rank-deficient on a nonempty zero set of minors, so `δr ≈ 2^-59` (reasoned, not proved;
  [`PROTOCOL.md`](../docs/membership/PROTOCOL.md), "Zero knowledge"). Single proof, the distinguisher's queries after it.
- **The EVM contract is the verifier.** `Evm.evm_accepts_iff_verifyWith` (`EndToEnd/Evm/Contract.lean`): on a
  statement's and proof's calldata (273 bytes, no selector), the contract's recorded graph (`Implementation/Graph.lean`:
  537 nodes, 39 output words, three claims checked declared), with the stored index commitment and what the block
  proves of a declared claim modelled by `pcsOpen` (`Evm/PcsOpen.lean`), accepts exactly when `PcsQuotient.verifyWith`
  accepts at π = Keccak-f[1600]; `Evm.evm_accepts_iff_exists`: over all calldata, the contract accepts exactly the
  calldata of an accepted proof. `Implementation/` proves the graph computes `reduce` (`run_calldata`).

## leanVM by recursion: the end theorems

The Keccak VM is leanVM `42422001` with leanVM `9d50c92a3`'s `SHA3` (one Keccak-f[1600] step a row). π1 is the
univariate PIOP for its statement, π1-rec3 its variant for the recursion at `f96a7938`; π2 proves that π1-rec3's
recorded verifier graph accepts; the contract runs π2's verifier and checks eight claims declared (π1's `C1`, `C2`,
setup `F`; π2's `W`, setup, and `Q`'s identity, pushes' and sum claims), each the EIP draft's PCS claim, opened alone by
`WhirBridge.Pcs`'s transcription of `verify_claim`. The reference is 128 signatures: `UniKeccakSound.keccakRefShape` =
`RecGraphKeccak.Pi1.keccak128` (`RecCompose.Pi1K.keccak128_eq_refShape`): heights `15 16 15 16 14 15`, memory
`2^20`, bytecode `2^18`; `C1` `2^27` words, `C2` `2^26`, the setup `2^23`; π2's `W` `2^24`, its setup `2^25`, `Q`
`2^28`.

- **The statement.** `KeccakArith.kvSoundness` (under `Admissible prog s` and `SentinelSafe prog`, a stack satisfying
  `KvHolds F prog s input q` represents a `KeccakVm.ValidExecution`), `KeccakArith.kvCompleteness` (an execution with
  at most `2^32` instructions of every opcode has an honest stack), `KeccakFlushes.flushesSha3_eq`; the block
  `KeccakFlock.keccakFlockSpec` (`step_of_holds`, `holds_gen`, `in_gen`) and its structured terminal
  (`Core.structuredTerminal_eq_bilinear`).
- **π1, knowledge soundness**, in one random permutation, for the explicit extractor `uniExtractorK`:
  `UniKeccakSound.uniKnowledgeSoundnessKeccak_closed` (at `keccakRefShape` and the deployed program IV; `≤ 2^-64` for
  `Q ≤ 2^64`, `2^-64.87` at `2^64`, 128.87 bits as `Q/ε`) and `uniKnowledgeSoundnessKeccakRec3_closed` (π1-rec3,
  128.49 bits). The three openings are charged once at `269 · 2^-137` (`WhirBridge.Pcs.pcs_union_sound`).
- **π1, completeness**: `UniKeccakComplete.uniCompletenessKeccak_closed` and `uniCompletenessKeccakRec3_closed`, for an
  explicit Lean honest prover, error `Prob.deltaK < 2^-169` (`deltaK_lt`), under `D.shape = keccakRefShape`,
  `D.programIv.length ≤ 2^16` and **`32 ≤ D.programIv.length`** (the deployed IV has 32 bytes).
- **π1-rec3's graph.** `RecGraphKeccak/Emitted.lean` is the graph the Rust recorded (10,850 nodes, 69 Keccak-256 calls,
  3 claims); `RecGraphKeccak.Sim.pi1GraphIsVerifierK`, no hypothesis: for every permutation, the graph computes
  π1-rec3's verifier off the merge hazard; `hazard_probK`: at most `2^16` hazardous `t` per `p_0` (`2^-176`);
  `pi1rec3K_end`: a witness satisfying π2's circuit carries the graph's outputs.

### The recursion's end theorems

Statements in `RecStatement/Security.lean` and `Reduction.lean`, proofs in [`RecCompose/`](RecCompose/README.md).
π2's circuit computes π1-rec3's Fiat–Shamir with the real Keccak-f[1600], while π1-rec3's theorems are in the
random-permutation model, so the end theorems meet at Keccak-f[1600].

```lean
theorem RecCompose.recKnowledgeSoundness_reduction_real (prog : KeccakVm.Program)
    (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize) (hg : GraphsAgree) (hd : DigestChecked)
    (hs : SetupRootChecked) (hiv : IvChecked) :
    RecKnowledgeSoundnessReduction (realDeployment prog hprog) pi2Bound ∧
      ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64
```

- **Knowledge soundness as an explicit reduction, no Fiat–Shamir premise**: Pr[the contract accepts ∧
  `recExtractor` finds no `KvHolds` witness] ≤ `pi2Bound Q` + Pr[`pi1Adversary` breaks π1-rec3 at Keccak-f[1600]] +
  Pr[`hazardAdversary` hits the merge hazard], the two adversaries explicit (the adversary, then π2's extractor; same
  query count). `pi2Bound`: π2's Fiat–Shamir and the eight openings, charged once
  (`WhirBridge.Pcs.UnionO.pcs_union_sound_oracle`), `Q`'s three claims bound to one table by its out-of-domain answer
  (`RecCompose.qOodBinding`, `2^-156` a query): `2^-64.93` at `2^64`, 128.93 bits as `Q/ε`. `recExtractor` decodes `W`,
  reads π1's stream off the first candidate π1-rec3's graph accepts, then runs `uniExtractorK`.
- **Completeness**: `RecCompose.Pi1K.recCompleteness_real_K_fs_bits`, error `δ1 + δh + 2^-164` for the Lean provers
  (π2's part `recCompleteness2_pi2_rec3_K`, `δ2 ≤ 2^-164`), under `Pi1CompletenessKeccak D … δ1` (its
  random-permutation reading is proved, `pi1CompletenessFs_rpm`, `deltaK < 2^-169`) and `Pi1HazardKeccakHonest D … δh`
  (motivated by `hazard_probK`, not proved), both about the honest π1-rec3 run at Keccak-f[1600].
- Also `recKnowledgeSoundness2_closed` (π2's part alone) and the Prop-premise corollaries `recKnowledgeSoundness_closed`,
  `recKnowledgeSoundness_closed_fs`, whose premises `Pi1FsKeccak`, `Pi1HazardKeccak` are **false as stated** for
  unbounded adversaries (they grind Keccak-f[1600] offline): read them as the Fiat–Shamir heuristic.
- **Evaluated, not proved** (the hypotheses of `recKnowledgeSoundness_reduction_real`): `GraphsAgree`
  (`RecGraphKeccakTest/Pi1Check.lean`), `DigestChecked`, `SetupRootChecked`, `IvChecked` at the reference, zero and
  all-ones IVs (`rec-real-check`), `viewCheck` at two IVs (`rec-view-check`).

## Trusted, tested, not covered

| | Membership | Recursion |
|---|---|---|
| Trusted | the Lean kernel and three axioms; Keccak-f[1600] a random permutation, Keccak-256 its sponge; mumbai's definitions (Keccak, the model, `verifyStackedOpening`, the decoders); the prover's randomness uniform (deployed: a Keccak-256 KDF, `Randomness::derive`, so computational ZK) | the same; the deployed Rust provers for completeness |
| Tested against the Rust | the Statement (`membership-differential`: 121 reductions, 18 honest and tampered proofs at `2^17` rows, the small, toy and membership circuits' commitments, all agreeing); the Statement's prover (the reduction's stream at `2^17` rows, and its proof accepted); the circuit's rows and σ (`kc3-dump-circuit`, SHA-256 `7b73dc3b…`); bytecode = graph (`graph_lean_is_current`, `Implementation/Diff.lean` on 1000 calldata); `FIELD_MUL` = `mulE` by vectors; `pcs_claim::verify` = `pcsOpening` (`WhirBridge/Test/CheckPcs.lean`) | π1's verifier (`UniKeccakTest/Runner.lean`: 90/90 verifier and 14/14 terminal vectors, the real proofs among them); the verifier's tables, the block's rows and terminal, `sha3Step`; the circuit compiler (`rec-circuit-keccak`, `padCounts` on 202 cases); π2's Lean prover on two small circuits; `RecStatement/Data.lean` is what the Rust emitted at `f96a7938`; the bytecode is π2's Rust verifier by the Rust's tests (`parity`) |
| Evaluated, not proved | `WiringCheck` (completeness's hypothesis: the wiring's coefficient `n − 2` nonzero, `membership-wiring-check`) | `GraphsAgree`, `DigestChecked`, `SetupRootChecked`, `IvChecked` |
| Not covered | simulation-extractability; `RevealedUniform` (stated, reasoned at `δr ≈ 2^-59`, not proved); ZK with queries before the proof, or for several proofs; the RPM theorems and the EVM one do not formally compose; `StatementBinds` (immediate, not proved); pruned Merkle paths | the model gap (π1-rec3 in the RPM, π2's circuit at Keccak-f[1600]); `PatchChecked`; other shapes than the reference; no Lean differential run of π2's verifier |

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
| [`RecGraph`](RecGraph/README.md), [`RecGraphKeccak`](RecGraphKeccak/README.md) | recorded graphs; π1-rec3's graph = its verifier, the hazard |
| [`RecCircuit`](RecCircuit/README.md), `RecPiop` | π2's circuit compiler; π2's PIOP (π2v3) |
| [`RecStatement`](RecStatement/README.md) | π2's verifier, the eight claims, the recursion's end statements |
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
  RecCompose                                                                           # the leanVM line
systemd-run --scope -p MemoryMax=12G lake env lean ../RecGraphKeccak/RecGraphKeccakTest/Pi1Check.lean   # GraphsAgree
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check               # DigestChecked, ivCheck at three IVs
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check --setup-only  # SetupRootChecked
systemd-run --scope -p MemoryMax=12G lake exe rec-view-check               # viewCheck at two IVs
```

A build of many libraries at once runs many `lean` processes; under a memory cap, restrict its CPUs (`taskset -c 0-3
lake build …`).

`#guard_msgs` in each library checks the axioms. The differential tests' commands are in the package READMEs; the
leanVM line's vectors are `f96a7938`'s (see Status).

## Remaining

1. **The leanVM port** to the deployed recursion ([`docs/LEAN_PORT.md`](../docs/LEAN_PORT.md)).
2. **The model gap.** π2's circuit computes π1-rec3's Fiat–Shamir with the real Keccak-f[1600]; π1-rec3's theorems are
   in the random-permutation model, so the soundness reduction's last two terms and the two completeness premises are
   left to the Fiat–Shamir heuristic for Keccak-f[1600].
3. **The evaluated checks** are Props checked by running Lean, not kernel proofs: membership's `WiringCheck`; the
   recursion's `GraphsAgree`, `DigestChecked`, `SetupRootChecked`, `IvChecked` (evaluated at three IVs and assumed at the
   others: `IvUniform.ivChecked_of_patchChecked` reduces it to `PatchChecked`, not proved).
4. **Other shapes**: π1's closed bounds are at the reference shape.
5. **Membership**: `RevealedUniform εr δr` proved (group 1 from a determinant's degree; group 2's `δr`, about `2^-59`
   with blinding words in `K`, from the minors' degree in the random rows); zero knowledge with a pre-proof phase;
   simulation-extractability; a few lemmas duplicated between the soundness and completeness lines
   (`Soundness/PcsVH*.lean`, `tableEval_eq_mle`, `tau_systemL`).
6. Declarations in the shared libraries that no end theorem uses (the previous protocol's F1 and F0 in
   `QuotientSecurity`, its layout openings in `WhirBridge`, `Compose`'s `knowledgeSoundness_deployed_rust`,
   `ComposePcs`'s four-root chain, `formal/Circuit`): still built, as the leanVM line imports them.
