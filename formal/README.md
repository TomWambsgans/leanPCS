<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# formal/: Lean 4 proofs of the membership proof and of the leanVM recursion

## Status

Everything in `formal/` states and proves the protocols of commit **`f96a7938`**, not the deployed Rust
(`git log f96a7938..main -- formal` is empty):

- **membership**: six one-point claims on four commitments (`W`, `H`, `Q`, `G`), the masks, the gate `V = X + C + Y·C`
  ([`docs/HISTORY.md`](../docs/HISTORY.md), "Membership at f96a7938"); deployed: three claims on two commitments and
  the circuit's ([`docs/membership/PROTOCOL.md`](../docs/membership/PROTOCOL.md));
- **recursion**: π2 (π2v3) over π1-rec3, π1's three claims encoded by the contract; deployed: π2 over π1-rec4, π1's
  three claims hashed in π2's circuit ([`docs/leanvm/rec/SPEC-REC.md`](../docs/leanvm/rec/SPEC-REC.md)).

What the port needs is [`docs/LEAN_PORT.md`](../docs/LEAN_PORT.md). **Do not regenerate the Lean-facing files until
the port**: the Rust now writes the deployed protocols, so `UPDATE_LEAN=1` runs (`crates/membership/evm/src/lean.rs`,
`crates/leanvm/rec/tests/lean_statement_keccak.rs`, the other writers AGENTS.md lists under "Lean-facing outputs")
would overwrite `f96a7938`'s `Implementation/Graph.lean` and `RecStatement/RecStatement/Data.lean` with files the Lean
does not state; their `*_is_current` tests are ignored and stale. Lean comments still cite the design notes by their
names at `f96a7938` (`docs/HISTORY.md` maps them).

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
the proof format, the verifier (computable, differential-tested against `f96a7938`'s Rust), the honest prover, the
explicit straight-line extractor and the simulator, in one random permutation; `EndToEnd/` proves them.

- **Knowledge soundness, no hypotheses.** `Soundness.knowledgeSoundness : PcsQuotient.KnowledgeSoundness
  Soundness.ksBound` (`EndToEnd/Soundness/PcsFinal.lean`). `ksBound Q = SoundPcs.deployedBound (2^20 + 24 + Q) +
  (5·2^19 + 24 + Q + 728890)^2/2^508`: about `2^-104.4` at `Q = 0`, `2^-85.4` at `2^40`, `2^-61.4` at `2^64` (125.4
  bits as `Q/ε`). `deployedBound` (`SoundPcs.knowledgeSoundness_deployed_pcs`) is the six openings
  (`WhirBridge.Pcs.pcs_sound_oracle`, the out-of-domain point read off Keccak-256 by the verifier; `2^-128` a query
  each, which dominate), the binding of the four roots' lists at their points (`ood_binding_coords` at `25`, `27`,
  `28` variables) and the chain (`ComposePcs/Pinned4.lean`): each root absorbed with its out-of-domain answer, each
  challenge is bounded for the one candidate tuple the answers pin (`prEvent_pinned_le`: `2^-164` a query, not the
  union over `< 2^50` tuples). The extractor `PcsQuotient.extractor` is explicit and computable (hash-map replay,
  Merkle inversion, fast path, Gao's unique decoder, Guruswami–Sudan last). Stand-alone, not
  simulation-extractability.
- **Completeness, no hypotheses.** `E2ECompleteness.completeness_end : PcsQuotient.Completeness Pcs.deltaPcs`
  (`EndToEnd/Completeness/E2ECompleteness/PcsDone.lean`), `deltaPcs = (19·2^24 + 31)/2^192 + 2^-304 + (2^48)²/2^508 ≈
  2^-163.75` (`deltaPcs_lt`: `< 2^-163`): degenerate challenges `(α, β, t, ρ)`, the openings' proofs of work, the
  permutation as two random oracles. For the Statement's prover; the deployed Rust prover is trusted for completeness.
- **Zero knowledge, under two hypotheses.** `PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed : PcsZeroKnowledge sim εpcs
  → RevealedUniform εr → ZeroKnowledgeWith sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + εr + εfs₀)`
  (`EndToEnd/ZK/PcsFSClosed.lean`; hypotheses and simulator in `Statement/PcsQuotient/Zk.lean`). `PcsZeroKnowledge`
  is the EIP's ZK-WHIR assumption (the reference openings are not zero knowledge); `RevealedUniform` (the ten revealed
  scalars uniform at all but `εr` of the challenges) is tested in the Rust (`hiding.rs`), not proved: at `f96a7938` a
  random row's value enters the gate's quotient `GF(2)`-linearly. `εfs₀ = 113 · δq L ≤ 2^-162` is proved
  (`fiatShamirUniform_closed`). Single proof, the distinguisher's queries after the proof.
- **The EVM contract is the verifier.** `Evm.evm_accepts_iff_verifyWith` (`EndToEnd/Evm/Contract.lean`): on a
  statement's and proof's calldata, the contract's recorded graph (`Implementation/Graph.lean`, `f96a7938`'s: 665
  nodes, six claims checked declared), with the stored index commitment and what the block proves of a declared claim
  modelled by `pcsOpen` (`Evm/PcsOpen.lean`), accepts exactly when `PcsQuotient.verifyWith` accepts at
  π = Keccak-f[1600]; `Evm.evm_accepts_iff_exists`: over all calldata, the contract accepts exactly the calldata of an
  accepted proof. `Implementation/` proves the graph computes `reduce` (`run_calldata`).

The chain of layers: F0 the circuit and F1 the reduction ([`QuotientSecurity/`](QuotientSecurity/README.md)), F2 the
openings ([`WhirBridge/`](WhirBridge/README.md)), F4 the composition ([`Compose/`](Compose/README.md), `ComposePcs/`,
`SoundPcs/`), F5 the implementation (`Implementation/`), then `EndToEnd/`'s bridges (`Bridge`, `PcsBridge`) to the
Statement's definitions.

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
| Tested against the Rust (at `f96a7938`) | the Statement (`PcsQuotientTest/Differential.lean`: reductions, honest and tampered proofs at `2^17` rows, circuit commitments); the Statement's prover (the reduction's stream at `2^17` rows); bytecode = graph (`contract_is_the_verifier`, `random_calldata_agrees`); `FIELD_MUL` = `mulE` by vectors; `pcs_claim::verify` = `pcsOpening` | π1's verifier (`UniKeccakTest/Runner.lean`: 90/90 verifier and 14/14 terminal vectors, the real proofs among them); the verifier's tables, the block's rows and terminal, `sha3Step`; the circuit compiler (`rec-circuit-keccak`, `padCounts` on 202 cases); π2's Lean prover on two small circuits; `RecStatement/Data.lean` is what the Rust emitted at `f96a7938`; the bytecode is π2's Rust verifier by the Rust's tests (`parity`) |
| Not covered | simulation-extractability; ZK without its two hypotheses, with queries before the proof, or for several proofs; the RPM theorems and the EVM one do not formally compose; `StatementBinds` (immediate, not proved); pruned Merkle paths | the model gap (π1-rec3 in the RPM, π2's circuit at Keccak-f[1600]); `PatchChecked`; other shapes than the reference; no Lean differential run of π2's verifier |

## Libraries

| Library | What |
|---|---|
| [`Statement`](Statement/README.md) (`PcsQuotient`) | membership: definitions and end statements only |
| `EndToEnd` | the Lake workspace; libraries `Soundness`, `E2ECompleteness`, `ZK`, `Evm` (membership end theorems), `Bridge`, `PcsBridge`, `Shared` |
| `Circuit`, `Field` | F0: the deployed circuit's wiring and `F192` |
| [`QuotientSecurity`](QuotientSecurity/README.md) | F1 (the reduction with ideal commitments) and F0's theorems |
| `QuotientRpm` | F4a: the reduction's Keccak-256 chain, ROM then RPM |
| [`WhirBridge`](WhirBridge/README.md) | F2: the PCS claim (version 1) and the layout openings, under mumbai's WHIR soundness |
| [`Compose`](Compose/README.md), `ComposePcs`, `SoundPcs` | F4b: the composition with real commitments; on the PCS claims, `knowledgeSoundness_deployed_pcs` |
| `Completeness` | the membership completeness layers |
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
systemd-run --scope -p MemoryMax=12G lake build WhirBridge ComposePcs SoundPcs PcsBridge Bridge Completeness \
  QuotientSecurity Implementation PcsQuotient                                          # their layers
systemd-run --scope -p MemoryMax=12G lake build KeccakVm KeccakArith KeccakFlushes KeccakFlock UniKeccak UniKeccak.Fits \
  UniStatement.KeccakTables UniKeccakSound UniKeccakComplete RecGraphKeccak RecCircuit rec-circuit-keccak RecStatement \
  RecCompose                                                                           # the leanVM line
systemd-run --scope -p MemoryMax=12G lake env lean ../RecGraphKeccak/RecGraphKeccakTest/Pi1Check.lean   # GraphsAgree
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check               # DigestChecked, ivCheck at three IVs
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check --setup-only  # SetupRootChecked
systemd-run --scope -p MemoryMax=12G lake exe rec-view-check               # viewCheck at two IVs
```

`#guard_msgs` in each library checks the axioms. The differential tests' commands are in the package READMEs; their
vectors are `f96a7938`'s (see Status).

## Remaining

1. **The port** to the deployed protocols ([`docs/LEAN_PORT.md`](../docs/LEAN_PORT.md)).
2. **The model gap.** π2's circuit computes π1-rec3's Fiat–Shamir with the real Keccak-f[1600]; π1-rec3's theorems are
   in the random-permutation model, so the soundness reduction's last two terms and the two completeness premises are
   left to the Fiat–Shamir heuristic for Keccak-f[1600].
3. **The evaluated checks** are Props checked by running Lean, not kernel proofs; `IvChecked` is evaluated at three IVs
   and assumed at the others: `IvUniform.ivChecked_of_patchChecked` reduces it to `PatchChecked`, not proved (a
   relational simulation of about 1,200 lines of the builder).
4. **Other shapes**: π1's closed bounds are at the reference shape.
5. **Membership**: `RevealedUniform` proved rather than tested; zero knowledge with a pre-proof phase;
   simulation-extractability.
6. Declarations in the shared libraries that no end theorem uses (the previous protocol's layout openings,
   `Compose`'s `knowledgeSoundness_deployed_rust`, `Completeness`'s `completeness_deployed_*`): still built, as the
   end theorems import those libraries.
