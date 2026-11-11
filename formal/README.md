<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# Formal verification of `crates/membership/quotient`

> **The Lean lags the Rust.** Everything in `formal/` states and proves the protocols of commit `f96a7938`, not the
> current Rust (`git log f96a7938..main -- formal` is empty). Membership: `f96a7938`'s six claims on four commitments
> (`docs/membership/EIP_CLAIMS.md`), where the deployed protocol has three claims on two commitments and the
> circuit's ([`docs/membership/PERF_GAS2.md`](../docs/membership/PERF_GAS2.md), on
> [`PERF_GAS.md`](../docs/membership/PERF_GAS.md)). The recursion: π2 (π2v3) over π1-rec3, π1's three claims encoded
> by the contract, where the deployed π2 proves π1-rec4 and hashes π1's three claims in its circuit
> ([`docs/leanvm/rec/PERF_GAS2.md`](../docs/leanvm/rec/PERF_GAS2.md), on
> [`PERF_GAS.md`](../docs/leanvm/rec/PERF_GAS.md)). What the port needs is in those files, "What the Lean needs". The
> Lean-facing files the Rust writes are `f96a7938`'s accordingly: `Implementation/Graph.lean` and
> `RecStatement/RecStatement/Data.lean` (their `*_is_current` tests are ignored and stale).

Knowledge soundness, completeness and zero knowledge (assuming a zero-knowledge PCS) of the membership proof that
`crates/membership/quotient` builds and `crates/membership/evm` verifies, on the EIP draft's PCS claims
(`docs/membership/EIP_CLAIMS.md`: four commitments with out-of-domain answers, six one-point claims, random rows, the
blinding of `h`), in Lean 4. **The statement** is [`Statement/`](Statement/README.md), a Lake
package of definitions and end statements only, on leanerVM `mumbai`'s `Statement/`: the relation, the proof
format, the verifier (computable, differential-tested against the Rust), the honest prover, the extractor and
the simulator, and `KnowledgeSoundness`, `Completeness`, `ZeroKnowledgeWith` in the random-permutation model.
The extractor is an explicit, computable definition in the statements, so that a reviewer can check what it
reads and that it is efficient; the simulator the zero-knowledge theorem covers is named in its statement
(`zkSimulator`, built on a PCS simulator given as a parameter). Lean has no running-time theorem; the convention is
leanerVM's: a fixed straight-line extractor, its cost read off its loops. Here the extractor reads the
statement, the proof, the adversary's transcript and the public setup tree (the circuit commitment's Merkle
tree). **The proofs** of the statements are in [`EndToEnd/`](#end-to-end-theorems), from the layers F0–F5 below.

Toolchain and dependency revisions are leanerVM `mumbai`'s (Lean `v4.34.1`, Mathlib `d13f23b7`, VCVio
`afa6593f`, CompPoly `572f9973`, ArkLib `4dae3acf`), so its results can be imported rather than reproved. The
starting point is leanVM's `formal/quotient` (branch `PCS-openings-aggregation`), whose README is kept as
[`README.upstream.md`](README.upstream.md): sorry-free proofs of the reduction for the upstream
full-adder circuit, with ideal commitments.

**leanVM proofs by recursion, for the Keccak VM** (`crates/leanvm/{univariate,rec}`; leanVM `9d50c92a3`'s `SHA3`
table, the 128-signature reference, every commitment and claim the EIP draft's PCS claim), in libraries of
`EndToEnd/`: the Keccak VM's statement and the soundness and completeness of its arithmetization; π1's univariate
verifier transcribed and differential-tested, with its knowledge soundness and completeness proved at the reference
shape with no hypothesis; π1-rec3's recorded graph proved equal to
that verifier off a merge hazard (`2^-176` for a uniform `t`), and π2's circuit for the graph; and the recursive
verifier's end theorems: knowledge soundness as an explicit reduction, with no Fiat–Shamir premise, to two experiments
on π1-rec3 at the real Keccak-f[1600], and completeness under two premises about π1-rec3's honest run there
([below](#leanvm-by-recursion-the-keccak-vm)).

## End-to-end theorems

`EndToEnd/` (a Lake workspace, `EndToEnd/lakefile.toml`) proves the Statement's end statements about the
Statement's own definitions. Every theorem below is sorry-free and depends only on `propext`,
`Classical.choice` and `Quot.sound`, checked by `#guard_msgs` in each library (so no `native_decide`).

- **Knowledge soundness: proved, no hypotheses, on the PCS claims.** `Soundness.knowledgeSoundness :
  PcsQuotient.KnowledgeSoundness Soundness.ksBound` (`EndToEnd/Soundness/PcsFinal.lean`, library `Soundness`). In
  one random permutation π: the setup computes the circuit's commitment (root and out-of-domain answer) over π; the
  adversary is given it, makes at most `Q` calls of π and π⁻¹ (its coins free), and outputs a statement and a
  proof. The probability that the verifier accepts while `PcsQuotient.extractor` returns no secret satisfying
  `PcsQuotient.Relation` is at most `ksBound Q = SoundPcs.deployedBound (2^20 + 24 + Q) + (5·2^19 + 24 + Q +
  728890)^2/2^508`: about `2^-104.4` at `Q = 0`, `2^-85.4` at `2^40`, `2^-61.4` at `2^64` (`125.4` bits as `Q/ε`).
  `deployedBound` (`formal/SoundPcs`, `knowledgeSoundness_deployed_pcs`, mumbai's two-oracle model) is six opening
  terms (`WhirBridge.Pcs.pcs_sound_oracle`: each opening sound with the out-of-domain point read off Keccak-256 by the
  verifier; `2^-128` a query each, which dominate), the binding of the four roots' lists at their out-of-domain points
  (`ood_binding_coords` at `25` (`W`, `G`), `27` (`H`) and `28` (`Q`) variables: `δc 25 ≤ 2^-167`, `δc 27 ≤ 2^-168`,
  `δc 28 ≤ 2^-169` a query, plus `N (N + 1)/2^256` each), and the chain (`ComposePcs/ComposePcs/Pinned4.lean`): each root is
  absorbed with its out-of-domain answer, so each challenge after it is bounded for **the one candidate tuple the
  answers pin** (`prEvent_pinned_le`: the answers at the `46`-byte out-of-domain inputs fix it, asked or not, and the
  round's answers are uniform and independent of them), F1's round error `2^-164` a query instead of the union over
  `7908 · 4473 · 3564 · 7908 < 2^50` tuples (`2^-114`, `ListChain4.lean`, kept). Chain and binding together:
  `2^-163.8` a query. No challenge is drawn between a root and its answer (both are in one chain input,
  `commitWords`), so the binding applies at every round; the out-of-domain points may be asked late (after the
  challenges, by the verifier), which the bad events allow: the fresh-query engine lets them read the whole table.
  The extractor is unchanged in kind (hash-map replay, Merkle inversion, interpolation,
  Gao's decoder, Guruswami–Sudan last), on the witness table, which a PCS commitment holds as it is. The proof: the
  Statement's experiment to the two-oracle model (`rpm_le_romG`), the Statement's verifier to `SoundPcs`'s run
  (`le_dExp`: `reduceWithH_eq_chain4`, `pcsOpeningWithH_eq_O`), the claims through `PcsBridge.claimsAt_eq` and the
  quotient table assembled from its parts (`PcsBridge.mle_assemble`), F1, and F0 with the random rows
  (`relation_of_sat`).
- **Completeness: proved, no hypotheses, on the PCS claims.** `E2ECompleteness.completeness_end :
  PcsQuotient.Completeness Pcs.deltaPcs` (`EndToEnd/Completeness/E2ECompleteness/PcsDone.lean`, library
  `E2ECompleteness`). For every statement and secret of the relation, the Statement's honest prover (four
  commitments with out-of-domain answers, the parts `H`, `Q`, `G`, random rows, the blinding of `h`, six one-point
  claims) with uniform coins, then the verifier, in one random permutation, rejects with probability at most
  `deltaPcs = (19 · 2^24 + 31)/2^192 + 2^-304 + (2^48)²/2^508 ≈ 2^-163.75` (`deltaPcs_lt`: `< 2^-163`): degenerate
  challenges `(α, β, t, ρ)` (`2^-163.75`, `badP4_fraction_le`; the four challenges fresh by their lengths,
  `prEvent_staged4_le`), the six openings' proofs of work (`2^-304`, `rejectGood_of_tail`), the permutation as two
  random oracles (`2^-412`; at most `2^48` block calls, `hcost_deployed`). The honest parts are F1's blinded honest
  second message (`quotientsOfTable_honest`) and the six claims are true (`honestClaims`). The prover is the
  Statement's; the deployed Rust prover is trusted for completeness (below). The `Pcs*` files replace the earlier
  protocol's proof, which was removed ([below](#completeness)).
- **Zero knowledge: proved assuming a zero-knowledge PCS** (`docs/membership/HIDING.md`).
  `PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed : PcsZeroKnowledge sim εpcs → RevealedUniform εr →
  ZeroKnowledgeWith sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + εr + εfs₀)` (`EndToEnd/ZK/PcsFSClosed.lean`,
  library `ZK`; the hypotheses and the simulator are in `Statement/PcsQuotient/Zk.lean`). The simulator's oracle is
  mumbai's lazily sampled permutation, which a PCS simulator may program; `zkSimulator` reads no witness: uniform
  roots, the ten revealed scalars (four out-of-domain answers, `a₀..a₃`, `Q`'s and `G`'s values) uniform, the public
  rest computed (the circuit's commitment, `next`, the chain's challenges, the claims, `H`'s value), the wiring
  claim opened by the real prover, the five secret claims by `sim.simOpen`. The two hypotheses are explicit:
  **`PcsZeroKnowledge sim εpcs`**, the PCS is zero-knowledge for the prover's use of it (the real experiment within
  `εpcs Q` of the hybrid, whose secret tables are committed with uniform roots and opened by the PCS simulator), and
  **`RevealedUniform εr`**, the protocol's randomness hides its revealed scalars (at uniform challenges outside a set
  of probability `εr`, the ten scalars are uniform when the masks, random rows and blinding are; `HIDING.md`'s rank
  conditions). `εfs₀ = 113 · δq L ≤ 2^-162` (`εfs₀_le`) is proved: the simulator's 113 Fiat–Shamir challenges are
  within `εfs₀` of uniform (`fiatShamirUniform_closed`). The proof: real ≈ hybrid (first hypothesis); in the hybrid
  the revealed scalars are functions of the randomness at the challenges (`hybrid_run_eq`), and uniformity at every
  good challenge tuple makes the adaptively derived scalars uniform (`RProg.trace_le`). **`RevealedUniform` is not
  proved**: a random row's value `v` enters the gate's quotient as `v·M·(Y + C) + v²·M²` (`M = L_{4k+1} + L_{4k+2}`),
  which is `GF(2)`-linear rather than `K`-affine, so the Rust rank test (`hiding.rs`, finite differences at random
  challenges) does not establish it. Single-proof.
- **The EVM contract is the Statement's verifier.** `Evm.evm_accepts_iff_verifyWith` (`EndToEnd/Evm/Contract.lean`,
  library `Evm`): on the calldata of a statement and proof, the contract's recorded operation graph (F5), with the
  stored index commitment (root, out-of-domain answer) and what the block proves of a declared PCS claim modelled by
  an explicit definition (`pcsOpen`, `Evm/PcsOpen.lean`: the claim's bytes `1 ‖ n ‖ root ‖ ood ‖ point ‖ value` read
  as the block reads them, then `PcsQuotient.pcsOpening` with the proof's opening of that claim), accepts exactly
  when `PcsQuotient.verifyWith` accepts at π = Keccak-f[1600]. `Evm.evm_accepts_iff_exists` (`Evm/Calldata.lean`):
  over all calldata, the contract accepts exactly the calldata of a proof that `PcsQuotient.verify` accepts. So the
  contract runs the verifier the three theorems above are about, up to the tested links below; their probabilities
  are over a random permutation and do not formally transfer to the real Keccak-f[1600] ("Scope", below).

**What is trusted.**

- The Lean kernel and the three standard axioms.
- **The models**: Keccak-f[1600] is one random permutation, and Keccak-256 is its sponge; every hash of the protocol
  is over that one π (the chain, the Merkle trees, the openings' duplex, the circuit's commitment), and the relation
  is over the deployed Keccak-256. The prover's randomness is uniform. As deployed (`Randomness::derive`,
  `crates/membership/quotient/src/protocol.rs`): a key is Keccak-256 of a tag, a 32-byte OS seed, the transcript's label (the
  circuit's commitment, the statement) and a digest of the witness's cells; the masks, the random rows' values and
  the blinding of `h` are the words of Keccak-256(tag ‖ key ‖ k), `k = 0, 1, …`. Deployed zero knowledge is
  therefore computational in that generator.
- **Scope**: the three theorems are about the Statement's `verifyWith` in the random-permutation model; the EVM
  theorem holds at the real Keccak-f[1600]. They do not formally compose: a probability over a random
  permutation does not transfer to a fixed hash.
- **mumbai's definitions** that the Statement reuses: Keccak-256 and Keccak-f[1600], the random-permutation model,
  the WHIR verifier `verifyStackedOpening` (mumbai tests it against leanVM's), its prover's pieces, the list decoder.
- **Tested, not proved**:
  - the Statement's definitions are the Rust (`Statement/PcsQuotientTest/Differential.lean`: reductions at `2^16`
    to `2^23` rows, whole proofs honest and tampered verified at `2^17` rows, the circuit commitments; the Rust's
    pruned Merkle paths expanded to the Statement's full ones);
  - the Statement's prover against the Rust's: the reduction's stream of nine scalars, at `2^17` rows on a small
    circuit only (the openings are not compared);
  - the EVM bytecode computes the recorded graph (`crates/membership/evm`'s tests: `contract_is_the_verifier`,
    `random_calldata_agrees`); `FIELD_MUL` and `KECCAK256` are the Lean operations (`mulE` is proved to be
    `F192`'s product; the Rust's `F192` arithmetic by test vectors);
  - what the block proves of a declared claim (`crates/membership/evm/src/machine.rs`) is the Rust
    `pcs_claim::verify`, which is `PcsQuotient.pcsOpening` (the differential test);
  - the extractor's cost table (read off its loops), and Gao's decoder recovering every word within its radius
    (`PcsQuotientTest/Decoder.lean`; the soundness proof does not need it).
- **Outside the theorems**: the block's aggregated proof, which must prove all of one declared claim's claims in
  one opening; the index root in the contract's storage (the theorems hold for whatever root is stored; a fixed owner
  may change it). The Rust prover is not trusted for soundness. Completeness and zero knowledge are about the
  Statement's prover; the deployed Rust prover is trusted for completeness (the tests above are its only link).
- **Not covered**: simulation-extractability; zero knowledge without its two hypotheses (`PcsZeroKnowledge`: the
  reference openings, leanVM's WHIR, are not zero knowledge; `RevealedUniform`, not proved, above), against a
  distinguisher that queries `π` before the proof, or for several proofs under one `π` (the theorem is
  single-proof); `StatementBinds` (immediate, not proved in Lean).

**Building.** As [`WhirBridge/`](WhirBridge/README.md#building), against a built leanerVM `6175f1a0` at
`formal/leanervm` (on h1 a link to `/root/pcs-quotient-fv/leanervm`):

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=12G lake build Soundness E2ECompleteness Evm ZK   # the end theorems; #guard_msgs checks their axioms
systemd-run --scope -p MemoryMax=12G lake build WhirBridge ComposePcs SoundPcs PcsBridge Bridge Completeness \
  QuotientSecurity Implementation PcsQuotient                                       # the layers' roots and their axiom guards
```

## leanVM by recursion: the Keccak VM

The Keccak VM (`docs/leanvm/univariate/KECCAK.md`) is leanVM 42422001 with its hash instruction (opcode `g^5`)
replaced by leanVM `9d50c92a3`'s `SHA3` (one Keccak-f[1600] step a row). π1 is a univariate PIOP for its statement,
π1-rec3 its variant for the recursion as of `f96a7938` (the deployed recursion proves π1-rec4, which the Lean does not
state); π2 proves that π1-rec3's recorded verifier graph accepts; the contract runs π2's verifier,
then checks eight claims declared, each the EIP draft's PCS claim (`crates/pcs_claim`, version 1: a root, its
out-of-domain answer, one point, a value; π1's `C1`, `C2`, setup `F`; π2's `W`, setup, and `Q`'s identity, pushes' and
sum claims), each opened alone by `WhirBridge.Pcs`'s transcription of `verify_claim`. The reference is 128 signatures:
`UniKeccakSound.keccakRefShape` = `RecGraphKeccak.Pi1.keccak128` (`RecCompose.Pi1K.keccak128_eq_refShape`) =
`keccakShapeOf 721598 [24260, 36229, 24626, 35812, 15509, 17712]`: heights `15 16 15 16 14 15`, memory `2^20`, bytecode
`2^18`; `C1` has `2^27` words, `C2` `2^26`, the setup `2^23`; π2's `W` `2^24`, its setup `2^25`, `Q` `2^28`. Every
library below is one of `EndToEnd/`; every theorem cited is sorry-free, without `native_decide`, on `propext`,
`Classical.choice`, `Quot.sound` (each root's `#guard_msgs`).

| Library | What |
|---|---|
| [`KeccakVm`](KeccakVm/README.md) | the instruction set and the relation `KvHolds F prog s input q`: `M3Holds` of Lv42's instance with the `SHA3` table (86 columns, every lane committed), and `KeccakAux` (the Keccak-f region: each block satisfies the block's R1CS, each executed row's lanes are its block's ports, `END_BIT` on `in_16`); the block `F : KeccakFlockSpec` a parameter |
| [`KeccakArith`](KeccakArith/README.md), `KeccakFlushes` | the arithmetization's soundness and completeness; the verifier's `SHA3` flushes are the instance's |
| [`KeccakFlock`](KeccakFlock/README.md) | the block of `crates/vendor/flock-42422001/src/keccak.rs` as `keccakFlockSpec`, and its lincheck terminal |
| [`UniKeccak`](UniKeccak/README.md) | π1's verifier as computable Lean (`reduce` at a `Variant`, `KECCAK_MAIN` and `KECCAK_REC3` (π1-rec3); the contract's IV, its three claims), and its statements `UniKnowledgeSoundnessKeccak{,Rec3}`, `UniCompletenessKeccak{,Rec3}` |
| [`UniKeccakSound`](UniKeccakSound/README.md) | π1's knowledge soundness |
| [`UniKeccakComplete`](UniKeccakComplete/README.md) | an explicit Lean honest prover, and π1's completeness |
| [`RecGraphKeccak`](RecGraphKeccak/README.md) | π1-rec3's recorded graph, graph = verifier off the merge hazard, the hazard's probability, π2's circuit for the graph |
| [`RecCircuit`](RecCircuit/README.md), [`RecPiop`](RecPiop) | the circuit compiler transcribed, and a satisfied compiled circuit carries the graph's outputs; π2's PIOP (π2v3) |
| [`RecStatement`](RecStatement/README.md) | π2's verifier (π2v3), the contract's eight PCS claims and their openings, the recursion's end statements |
| [`RecCompose`](RecCompose/README.md) | their proofs |

They build on older shared libraries: `Lv42` (leanVM 42422001's instruction set without its hash instruction: five
instructions, the machine, the five shared tables, the M3 instance, with the bytecode guarantee
`Lv42.Arithmetization.EntryOk`: an entry decodes, or has opcode `g^5`, the Keccak VM's `SHA3`), `UniStatement`,
`UniSound`, `UniComplete` (the honest prover's generic layers, [`UniComplete/README.md`](UniComplete/README.md)),
`FlockSound`, `FlockSoundUni`, `Heap`, `RecGraph`: the generic verifier, PIOP, Fiat–Shamir and Flock layers the Keccak
line instantiates.


### The statement, the arithmetization, the Keccak-f block

- **`KeccakArith.kvSoundness`**: for every block `F`, under `Admissible prog s` (the verifier's announcement check)
  and `SentinelSafe prog`, a stack satisfying `KvHolds F prog s input q` represents a `KeccakVm.ValidExecution prog
  input t`. **`KeccakArith.kvCompleteness`**: a `ValidExecution` with at most `2^32` instructions of every opcode has a
  stack satisfying `KvHonest F prog s input q`. Lv42's arithmetization proofs, ported.
- **`KeccakFlushes.flushesSha3_eq`**: on every row, the verifier's `SHA3` flush forms (`UniStatement.flushesSha3`)
  are the instance's (`KeccakVm.Sha3Table.flushes`), in order.
- **The block** `KeccakFlock.keccakFlockSpec : KeccakVm.KeccakFlockSpec`, no hypothesis: soundness `step_of_holds` (a
  satisfying block holds `keccakF1600` of its input port at its output port; leanerVM's `keccakF1600`), completeness
  `holds_gen`, `in_gen`. The terminal identities `Terminal.walkedTerminal_eq_bilinear`,
  `Core.structuredTerminal_eq_walked`, `Core.structuredTerminal_eq_bilinear`: the Rust's structured lincheck terminal
  is the block matrices' bilinear form. `UniKeccak.keccakFlockFits_keccakFlockSpec`: the block fits the verifier's
  ports.

### π1: knowledge soundness and completeness at the reference

```lean
theorem UniKeccakSound.uniKnowledgeSoundnessKeccak_closed (D : KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv = UniStatement.programIv) :
    UniKnowledgeSoundnessKeccak KeccakFlock.keccakFlockSpec D
        (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64
-- uniKnowledgeSoundnessKeccakRec3_closed: the same for UniKnowledgeSoundnessKeccakRec3, at 2 ^ 35
theorem UniKeccakComplete.uniCompletenessKeccak_closed (D : KDeployment)
    (hD : D.shape = UniKeccakSound.keccakRefShape) (hiv : D.programIv.length ≤ 2 ^ 16) :
    UniCompletenessKeccak KeccakFlock.keccakFlockSpec D (Prob.uniProverRP flockProveH D) Prob.deltaK
theorem UniKeccakComplete.uniCompletenessKeccakRec3_closed (D : KDeployment)
    (hD : D.shape = UniKeccakSound.keccakRefShape) (hiv : D.programIv.length ≤ 2 ^ 16) :
    UniCompletenessKeccakRec3 KeccakFlock.keccakFlockSpec D (Rec3.uniProverRec3RP flockProveH D) Prob.deltaK
theorem UniKeccakComplete.Prob.deltaK_lt : deltaK < (2 : ℝ≥0∞)⁻¹ ^ 169
```

- In one random permutation (π1's Fiat–Shamir, its Merkle trees, its three WHIR openings), against `KvHolds` at
  `keccakFlockSpec`, for the explicit extractor `uniExtractorK`; no hypothesis beyond the deployment's.
- **The soundness error** is `2^-64.87` at `Q = 2^64` for the main line (128.87 bits as `Q/ε`,
  `UniSound.uniBound128_le_bits`) and `2^-64.49` for π1-rec3 (128.49 bits, `uniBound128_le_bits35`). The three
  openings are charged once at `269 · 2^-137`; the setup's `2^23`-word opening is certified in
  `UniKeccakSound/Fs/Whir23.lean`.
- **The honest prover** is `UniComplete`'s ported to the Keccak VM (`UniKeccakComplete/K/`), with Flock's honest prover
  on the block; the `SHA3` table's padding rows' lanes are `q_flock`'s port words (`+ END_BIT` on `in_16`), as the
  Rust's `trace.rs`. `deltaK ≈ 2^-169.99`; its terms are in
  [`UniKeccakComplete/README.md`](UniKeccakComplete/README.md).

### π1-rec3's recorded graph and π2's circuit

- `RecGraphKeccak/Emitted.lean` is the graph the Rust records (10,850 nodes, 69 Keccak-256 calls, 14 zero checks, 3
  claims of `30`, `29`, `26` words), data only; `RecGraphKeccak.Pi1.pi1GraphK` is the Keccak verifier as a `RecGraph.Prog` program in
  the Rust's operation order. `RecCompose.GraphsAgree : pi1GraphK = Emitted.graph`.
- **`RecGraphKeccak.Sim.pi1GraphIsVerifierK : Pi1GraphIsVerifierK`**, no hypothesis: for every permutation, IV, input
  and stream off the merge hazard (`MergeHazardK`: the run draws `t`, challenge 52, a root of `Z_bad(p_0)`, `p_0`
  challenge 45), the graph's outputs are `UniKeccak.runWithK`'s at `keccakRec3`, its calls and zero checks
  (`verifierOutputsWithK`).
- **`RecGraphKeccak.hazard_probK`**: for every `p_0`, at most `2^16` hazardous `t`, so `≤ 2^16/|E| = 2^-176`.
- **`RecGraphKeccak.pi1rec3K_end`**: RecCircuit's `Compiled.compile_sound_end` at the emitted graph. If the Lean
  compiler accepts the graph at an IV, every witness satisfying π2's circuit carries the graph's outputs (statement,
  roots, zero checks, the claims word for word) on the stream its free bits encode. That the compiler
  accepts the graph is a run (`rec-circuit-keccak`, below).

### The recursion's end theorems (`RecCompose`)

The statements are `RecStatement/Security.lean`'s and `Reduction.lean`'s ([`RecStatement/README.md`](RecStatement/README.md)).
π2's circuit computes π1-rec3's Fiat–Shamir with the real Keccak-f[1600], while π1-rec3's theorems are in the
random-permutation model; no circuit computes a random permutation, so the end theorems meet at Keccak-f[1600].

**Knowledge soundness, as an explicit reduction, with no Fiat–Shamir premise** (`RealEnd.lean`, `FsClosed.lean`):

```lean
theorem RecCompose.recKnowledgeSoundness_reduction_real (prog : KeccakVm.Program)
    (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize) (hg : GraphsAgree) (hd : DigestChecked)
    (hs : SetupRootChecked) (hiv : IvChecked) :
    RecKnowledgeSoundnessReduction (realDeployment prog hprog) pi2Bound ∧
      ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64
theorem RecCompose.recKnowledgeSoundness_reduction (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) (hg : GraphsAgree) (hchk : Pi2ViewChecked C) :
    RecKnowledgeSoundnessReduction D pi2Bound ∧ ∀ Q ≤ 2 ^ 64, pi2Bound Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64

def RecStatement.RecKnowledgeSoundnessReduction (D : RecDeployment) (ε2 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    (∀ roots evals, QueryCostAtMost (pi1Adversary D A roots evals) permutationCallCost Q) ∧
    (∀ roots evals, QueryCostAtMost (hazardAdversary D A roots evals) permutationCallCost Q) ∧
    Pr{let z ← recSoundnessExperiment D A}[RecBreaksKnowledgeSoundness D (recExtractor D) z] ≤
      ε2 Q +
        Pr{let z ← pi1KeccakSoundnessExperiment D (pi1Adversary D A)}[
          UniKeccak.KBreaksKnowledgeSoundness D.flock D.pi1 (UniKeccak.uniExtractorK D.flock D.pi1) z] +
        Pr{let z ← pi1HazardExperiment D (hazardAdversary D A)}[Pi1HazardAccepted z.1 z.2.1 z.2.2]
```

- **The break**: the contract accepts and `recExtractor` finds no witness of `KvHolds` at `D.flock` (which `D.Real` pins to `keccakFlockSpec`).
  `recExtractor` is explicit: π2's extractor decodes `W` (fast path, unique decoder, list decoder), reads π1's stream off
  the first candidate on which π1-rec3's graph at Keccak-f[1600] accepts with the contract's π1 openings, then runs
  `uniExtractorK` on it.
- **`pi2Bound Q`**: π2's Fiat–Shamir layer and its eight PCS openings in the random-permutation model, at most `2^-64`
  for `Q ≤ 2^64` (`pi2Bound_le_bits`; `2^-64.93` at `2^64`, 128.93 bits as `Q/ε2`). The eight openings (π1's `2^27`,
  `2^26`, `2^23`, π2's `2^24`, `2^25`, `2^28`) are charged once, at `269 · 2^-137` (`FsOps.prEvent_doomH_le`, through
  `WhirBridge.Pcs.UnionO.pcs_union_sound_oracle`); the contract reads the out-of-domain point of `W`'s and `Q`'s claims
  off Keccak-256 over the permutation (`RecStatement.pcsOpenKO`; the deployed `ood_point` at the real Keccak-f[1600],
  `pcsOpenKO_keccakF1600`), so `Q`'s three claims on one commitment have one candidate, except with `2^-156` a query
  (`RecCompose.qOodBinding`, from `WhirBridge.Pcs.ood_binding_coords` at `n = 28`): `pi2OpenErr = 269 · 2^-137 +
  2^-156`, no hypothesis. π2's rounds: round 1 is `(4N − 1)/|F|` with `Q`'s empty slots (`RecPiop`: `h` below `2N`,
  `S` read as `P(t) + S(t)/Z_V(t)`, the sum claim `Σ_V (h + c_3 S) = 0`), `2^-140.92` with the lists.
- **The other two terms** are experiments at the real Keccak-f[1600]: π1-rec3's knowledge soundness and its merge
  hazard on an accepted stream, for `pi1Adversary D A` and `hazardAdversary D A`: `A`, its queries logged, then π2's
  extractor, of at most `A`'s `Q` queries. Lean bounds neither (below, "What remains").
- `realDeployment prog hprog` is π1 at `keccak128` and leanVM's program IV for any program `prog` of that bytecode
  size, π2's circuit at each IV the Lean compiler's on the emitted graph. `realDeployment_real`, `pi2Circuits_real`
  and `pi2ViewChecked_real` build `D.Real`, `C` and `Pi2ViewChecked C` from the four evaluated checks.
- Also: **`recKnowledgeSoundness2_closed`** (π2's part, random-permutation model: `RecKnowledgeSoundness2 D pi2Bound`,
  if the contract accepts, π2's extractor outputs a π1 stream on which π1-rec3's graph at Keccak-f[1600] accepts, its
  three calls the contract's), and the Prop-premise corollaries **`recKnowledgeSoundness_closed`**,
  **`recKnowledgeSoundness_closed_fs`** (`RecKnowledgeSoundnessWith D (recExtractor D) (pi2Bound Q + ε1 Q + εh Q)`
  under `Pi1FsKeccak D ε1` and `Pi1HazardKeccak D εh`). Those two premises quantify over every adversary and count
  only its calls of `π`, so they are **false as stated** for unbounded adversaries, which grind Keccak-f[1600] offline:
  read them as the Fiat–Shamir heuristic for bounded Keccak-f[1600] work, motivated by
  `uniKnowledgeSoundnessKeccakRec3_closed` and `hazard_probK`.

**Completeness** (`CompleteKeccakEnd.lean`), with `D = realDeployment prog hprog`:

```lean
theorem RecCompose.Pi1K.recCompleteness_real_K_fs_bits (prog : KeccakVm.Program)
    (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize) (hg : GraphsAgree) (hd : DigestChecked)
    (hs : SetupRootChecked) (hiv : IvChecked) (δ1 δh : ℝ≥0∞)
    (h1 : Pi1CompletenessKeccak D (pi1Rec3ProverK D) δ1)
    (hh : Pi1HazardKeccakHonest D (pi1Rec3ProverK D) δh) :
    RecCompletenessWith D (composeProver D (pi1Rec3ProverK D) (pi2Prover D …)) (δ1 + δh + (2 : ℝ≥0∞)⁻¹ ^ 164)
```

- **The provers** are Lean's: `pi1Rec3ProverK D` is UniKeccakComplete's π1-rec3 prover with its Fiat–Shamir the pure
  `keccak256` (over the real Keccak-f[1600], as the graph's), its trees and openings over `π`; `pi2Prover` is π2's
  honest prover (`Pi2Prover.lean`).
- **π2's part**: `RecCompose.Pi1K.recCompleteness2_pi2_rec3_K`, `RecCompleteness2 D (pi1Rec3ProverK D) (pi2Prover …)
  δ2` with `δ2 ≤ 2^-164` (`Pi2Alpha.delta2_alpha_le`), in the random-permutation model, from `pi1ProverFactsK` (the
  π1 prover's duplex discipline, at most `2^47` block calls, hash inputs below `2^26` bytes, transferred from
  UniKeccakComplete's prover).
- **The two premises**, both about this one honest prover at the real Keccak-f[1600] (no adversary grinds there):
  `Pi1CompletenessKeccak`, which `pi1CompletenessKeccak_iff` identifies with π1-rec3's completeness with its
  Fiat–Shamir over Keccak-f[1600]; its random-permutation reading `pi1CompletenessFs_rpm : Pi1CompletenessFs D
  queryPermutation Prob.deltaK` is proved (`deltaK < 2^-169`). `Pi1HazardKeccakHonest`: the honest run avoids the
  merge hazard, motivated by `hazard_probK` (`2^-176` for a uniform `t`), a count; its random-permutation reading is not
  proved.

### Tested or evaluated, not proved

- **Transcriptions against the Rust**: `UniStatementTest/KeccakTables.lean` (the verifier's tables, 261 lines of
  `tables_keccak()`), `KeccakVmTest/Isa.lean` (`sha3Step` against SHA3-256), `KeccakFlockTest/{Rows,Honest,Terminal}.lean`
  (the block's rows, honest column and terminals); `UniKeccakTest/Runner.lean`: π1's verifier agrees with the Rust on
  every value of 90/90 verifier vectors (the three real Keccak proofs among them, the 128-signature π1-rec3 one
  included, with every claim word for word) and 14/14 terminal vectors; `RecStatement/Data.lean` is what the Rust emitted at `f96a7938` (`keccak_statement_data_is_current`,
ignored, is stale since: the current circuit hashes π1's claims);
  the Lean compiler's circuit for the emitted graph is the Rust's, identical (`rec-circuit-keccak`, `rec-circuit-diff`),
  `padCounts` on 202 cases (`RecCircuitTest/PadCounts.lean`); π2's Lean prover writes the Rust's setup, `W` and `Q`
  roots, their out-of-domain answers and its stream, and recomputes the Rust's IV v3, on two small circuits
  (`RecComposeTest/Pi2Prover.lean`, 2/2 on the regenerated vectors). No Lean differential run of π2's verifier on Keccak
  vectors exists (`RecStatement/README.md`).
- **Evaluated Props** (run in compiled Lean, not kernel proofs): `GraphsAgree` (`RecGraphKeccakTest/Pi1Check.lean`);
  `DigestChecked`, `SetupRootChecked`, `ivCheck` at the reference, zero and all-ones IVs (`rec-real-check`); `viewCheck`
  at the reference and zero IVs (`rec-view-check`); the compiler accepting the emitted graph (`rec-circuit-keccak`).
- **Trusted for completeness**: the deployed Rust provers. UniKeccakComplete's π1 prover has no differential runner
  against the Rust's; π2's is compared on two small circuits only.
- **The deployed bytecode** is π2's Rust verifier by the Rust's tests (`crates/leanvm/rec/src/pi2/contract.rs`'s
  `parity`), not by a Lean proof.

### What remains

1. **The model gap.** π2's circuit computes π1-rec3's Fiat–Shamir with the real Keccak-f[1600]; π1-rec3's theorems are
   in the random-permutation model. So the soundness reduction's last two terms and the two completeness premises
   (`Pi1CompletenessKeccak`, `Pi1HazardKeccakHonest`) are not bounded in Lean: that is the Fiat–Shamir heuristic for
   Keccak-f[1600], applied to two explicit adversaries and to one honest prover.
2. **The evaluated checks** (`GraphsAgree`, `DigestChecked`, `SetupRootChecked`, `IvChecked`'s instances,
   `viewCheck`) are Props checked by running Lean (`Pi1Check.lean`, `rec-real-check`, `rec-view-check`), not kernel
   proofs.
3. **`IvChecked`** is evaluated at three IVs (the reference, zero, all-ones) and assumed at the other 32-byte IVs.
   `IvUniform.ivChecked_of_patchChecked` reduces it to `PatchChecked` (the compiler's IV factorization: every IV's
   circuit is the all-ones IV's with `κ` removed at the IV's zero bits' seed positions), which is not proved: it needs a
   relational simulation of the builder (about 1,200 lines of monadic code) and of the checker
   (`RealDeployment.lean`'s docstring).
4. **Other shapes.** The closed bounds of π1 are at the reference shape; most layers are shape-generic, the numbers
   (stack sizes, bad sets' counts, costs, the coordinate functionals at `h_SHA3`) are decided there.

### Building

```sh
cd formal/EndToEnd   # as in AGENTS.md, "Lean builds" (formal/leanervm linked to a built leanerVM 6175f1a0)
systemd-run --scope -p MemoryMax=12G lake build KeccakVm KeccakArith KeccakFlushes KeccakFlock UniKeccak UniKeccak.Fits \
  UniStatement.KeccakTables UniKeccakSound UniKeccakComplete RecGraphKeccak RecCircuit rec-circuit-keccak RecStatement \
  RecCompose                                                         # #guard_msgs checks the axioms
systemd-run --scope -p MemoryMax=12G lake env lean ../RecGraphKeccak/RecGraphKeccakTest/Pi1Check.lean   # GraphsAgree
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check               # DigestChecked, ivCheck at three IVs
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check --setup-only  # SetupRootChecked
systemd-run --scope -p MemoryMax=12G lake exe rec-view-check               # viewCheck at two IVs
```

The differential tests' vectors and commands are in the package READMEs (`UniKeccak`, `KeccakFlock`, `KeccakVm`,
`RecGraphKeccak`, `RecCircuit`, `RecStatement`, `RecCompose`).

## Layers

The end theorems are proved from these layers; each is sorry-free, on `propext`, `Classical.choice` and
`Quot.sound` only, without `native_decide`.

| | What | Source | Status |
|---|---|---|---|
| F0 | The circuit: a Lean definition of the deployed wiring (`quotient::circuit::membership`), proof that a satisfying assignment is its computation and that this computation is Keccak-256 membership; the constants (Cantor basis, `τ`, `b`, the bit weights) as computable definitions whose hypotheses are checked | new (needed because `Instance.soundness` holds for every wiring, so for a degenerate one it says nothing) | **done** (F0a for a circuit given as a parameter: `CircuitLayout.lean`, `Pinning.lean`, `Statement.lean`): `Instance.soundness_circuit`: for an instance whose wiring lays a loop-free χ circuit `C` (`Laid`: input cells on the cycle of what they read, word 5's 128 bits on the zero's cycle, word 4's bit 0 the one's anchor and its other bits on the zero's) and whose weights are `coordinate_weight`'s (`bit_weight(j)` = `x^j`, `Y x^(j-64)`, with `x ≠ 1`, `Y ≠ 1`), an accepted proof of `statementWords x Y y root` (`statement::halves` of `y`, `root`, then `(1, 0, 0, 0)`) holds `C`'s computation on some input bits with public words 0–3 the halves of `(y, root)`, except with probability `(Q + 3) / 2^128`; `soundness_circuit_bits`: with the 128 bit weights independent over `GF(2)`, its public bits are the bytes' bits as `circuit::public_words` reads them. Derived from `Instance.soundness` and `cells_determined` (bridged by `Instance.cells_determined`; zero then one pinned by `zero_pinned`, `one_pinned`); the cone of both reaches the circuit argument. Not vacuous: `wiringOf C` meets `Laid` (`laid_wiringOf`) and the cells of every computation of `C` satisfy the relation on it (`relation_wiringOf`, `relation_statementWords`). **The deployed circuit** (F0b, `Circuit/`, `QuotientSecurity/Deployed.lean`; F0c, `Field/`, `QuotientSecurity/DeployedConcrete.lean`): `soundness_membership_deployed`: an accepted proof's cells are a computation of the deployed `2^22`-row circuit (off its `16` random rows, `X` reading the row's own output, `Y` one, `C` zero, read by no other row: `ChiCircuit.isRandom`, `Laid.pubRows`, `Computes`) whose input bits give `x` and a path with `y = H(x ‖ 0x11..)` and the path from `H(x ‖ 0x22..)` ending at `root`, except with `(Q + 3) / 2^128`; Keccak-256 checked against mumbai's spec (`keccak256_bits`); `soundness_membership_deployed_concrete`: the same over `primitives`' `F192` (CompPoly's `BF64.Ext3`) with `x`, `Y`, the bit and coordinate weights and `statement::halves` transcribed and proved equal to the theorem's, no field hypothesis left. Sorry-free, on `propext`, `Classical.choice`, `Quot.sound`, no `native_decide`. σ equals the Rust's by a hash of both dumps (with the random rows: SHA-256 `41c92f12…6655`, 2026-11-10); completeness with the random rows' `X` and `V` cells holding any values: `Completeness.honest_relation_deployed_random` (and the Statement's circuit is F0b's, `EndToEnd/Bridge/Circuit.lean`'s `membership_eq`) |
| F1 | The reduction (five field elements → claims): round-by-round knowledge soundness, completeness, honest-verifier ZK, Fiat–Shamir in the ROM, **ideal commitments** | ported from leanVM `formal/quotient` and adapted ([below](#the-port-to-this-protocol-f1)): `2^22` rows, the χ gate on bits (degree 2), degree bounds, the circuit argument (bits, no carries) | **done** (`QuotientSecurity/`): `Instance.soundness`, `zero_knowledge`, `completeness` for every wiring; `soundness_circuit` (F0) for a wiring that lays a χ circuit. Its honest-verifier zero knowledge is for ideal hiding commitments; the end theorem's zero knowledge takes the PCS's as a hypothesis (`PcsZeroKnowledge`) |
| F2 | WHIR openings, Fiat–Shamir sound in mumbai's two-oracle model (some member of the root's level-0 list satisfies the claims) | leanerVM `mumbai`, `lean_vm` `Whir/Sound` | **done** in [`WhirBridge/`](WhirBridge/README.md). **The EIP's PCS claim, version 1** (`crates/pcs_claim`; `WhirBridge/PcsClaim.lean` …): `verify_claim` transcribed (`pcsVerifyWithHash`: the IV `H(PCS_claim)`, the root checked, two stack claims `(z, ood)` and `(point, value)`), **`pcs_sound`** at every `15 ≤ n ≤ 28` (`openingBound QA ≤ 2^-63` for `QA ≤ 2^64`), **`pcs_sound_oracle`** with the out-of-domain point read off Keccak-256 by the verifier (`pcsVerifierO`), **`pcs_union_sound`**, **`pcs_union_sound_oracle`** (claims of several sizes charged once; what `UniKeccakSound` and `RecCompose` charge their openings with), and the binding of a root's list at its out-of-domain point, **`ood_binding_coords`** (`δc n = C(L, 2)/2^192` a query: `≤ 2^-167` at `25`, `2^-168` at `27`, `2^-169` at `28` variables). The level-0 lists, certified: `L₀` = 9,952 / 7,908 / 6,296 / 4,473 / 3,564 at `log_n` = 24 .. 28. The layout openings of version 2 (`ours_sound` at the previous protocol's layouts, `ours_sound_public` for every `Layout::new` layout at `2^24 ..= 2^28` words) stay proved; the Statement's `openingWith` and parts of the leanVM line use them. Not covered: pruned paths, the Rust being the Lean mirror (test evidence: `Test/CheckPcs.lean` runs the Lean `verify_claim` on the Rust's openings, honest and mutated) |
| F4 | Composition: commitments as Merkle trees over Keccak-256 in the random-permutation model, the reduction's Keccak-256 chain, the openings' duplex; extraction from the adversary's transcript (`mumbai`'s Guruswami–Sudan decoder) | `mumbai` `common` (sponge indifferentiability, ROM→RPM), `lean_vm` extraction | **done.** F4a, the chain with ideal commitments: [`QuotientRpm/`](#the-keccak-256-chain-f4a). F4b, real commitments: [`Compose/`](Compose/README.md) (the list chain, the Merkle extraction, the two-oracle model, the random-permutation transfer `rpm_le_wired`, the `k`-round chain with openings of any verifier `knowledgeSoundness_listChainU_closed128G`, which the leanVM line composes through), then for the PCS claims `ComposePcs/` and `SoundPcs/` ([below](#the-composition-on-the-pcs-claims-f4b)): **`SoundPcs.knowledgeSoundness_deployed_pcs`**, which `Soundness.knowledgeSoundness` transfers to the Statement. Compose's composition of the previous protocol's three layout openings (`knowledgeSoundness_deployed_rust`) is still built, for the pieces the PCS composition reuses |
| F5 | The implementation is the model: the EVM contract and the Rust verifier are generated from one recorded operation graph (`crates/membership/evm/src/record.rs`); emit that graph as a Lean term too and prove it computes the Statement's verifier | new | **done** in [`Implementation/`](Implementation.lean) (sorry-free, no `native_decide`; end theorems on `propext`, `Classical.choice`, `Quot.sound`), for the EIP's PCS claims: `Implementation/Graph.lean` is `f96a7938`'s contract's recorded graph (665 nodes, 50 output words, 1 nonzero check, 6 PCS claims checked declared), written by `crates/membership/evm/src/lean.rs` (`graph_lean_is_current`, now ignored, is stale: the deployed contract checks three claims); `Interp.lean` interprets it on calldata as `codegen.rs` compiles each node (EVM words, `XOR`, `FIELD_MUL` = `mulE`, Keccak-256 of `MSTORE`d words, `CALLDATALOAD` and shifts, the circuit's commitment from storage) and packs each claim as `evm_link`'s `Item::DeclaredClaim`. Proved: a Lean transcription of `reduce` over node indices finds every node it asks for and gives exactly the six claims' words and the nonzero check (`Program.reduceIds_eq`, kernel evaluation); on `Primitives.F192` with its Rust limbs (`isF192_primitives`, `mul64_eq`: Rust's shift-fold `reduce` of the carry-less product is CompPoly's, structurally) those nodes hold the Statement's `claimsAt` (`reduceIds_spec`, `Formula.claimsAt_eq`), the graph's constants being the Statement's (`Constants.lean`, `Tau.lean`); on `quotient.rs`'s calldata the leaves are the Statement's chain byte for byte (`leafOK_calldata`, `reduce_eq`); so **`run_calldata`**: the contract reaches its checks iff `PcsQuotient.reduce` accepts, and checks declared exactly the encodings `pcsClaimBytes` of its six claims on their commitments. **Tested, not proved**: bytecode = graph (`crates/membership/evm`'s tests); the interpreter = the Rust verifier (`Implementation/Diff.lean`, 300 random calldata, 0 disagreements); the Rust's `F192` arithmetic = `mulE`; what the block proves of a declared claim is `pcs_claim::verify`, which is `PcsQuotient.pcsOpening` (the Statement's differential test). **To the Statement's verifier**: `EndToEnd/Evm` (`evm_accepts_iff_verifyWith`, `evm_accepts_iff_exists`) |

F3, the hiding openings of the previous protocol's hidden layouts (`QuotientSecurity/Hiding`), and their
zero-knowledge proof (`formal/QuotientZk`, `zeroKnowledge_closed`) were removed with that design: zero knowledge now
assumes a zero-knowledge PCS ([below](#zero-knowledge-endtoendzk)).

## The Keccak-256 chain (F4a)

`QuotientRpm/` (library `QuotientRpm`, which needs leanerVM `mumbai`'s `statement` and `common` packages,
pinned in `lakefile.toml`) lifts the reduction's knowledge soundness from an abstract random oracle on
`(statement, messages)` to a Keccak-256 transcript of `crates/membership/quotient/src/transcript.rs`'s form: the
previous protocol's chain (two roots, no out-of-domain answers), whose lemmas the four-root chain of `ComposePcs`
(`chainWith4`, [below](#the-composition-on-the-pcs-claims-f4b)) reuses.

- **The chain** (`Bytes.lean`, `Chain.lean`): the seed is Keccak-256 of the label `pcs-quotient-kc1 ‖
  index_root ‖ y ‖ root` (112 bytes); each challenge is Keccak-256 of the state and of the scalars sent since
  the last one, each a 32-byte big-endian word (`[0; 8] ‖ c2 ‖ c1 ‖ c0`, `scalarWord`), and is the state's low
  192 bits (`stateLimbs`: limb `i` is bytes `24 − 8i .. 32 − 8i`, big-endian); a root is two scalars, its
  128-bit halves read as little-endian words (`rootScalars`), i.e. sixteen zero bytes and the half reversed
  (`rootWords_eq`). The verifier (`Wire.verifyWith`, over any hash in any monad): root, `α`, `β`, `γ`, root,
  `t`, five values, `ρ`, as in `reduce`. A `Wire` holds what the chain reads besides the proof: the circuit's
  commitment, how the statement's 64 bytes are read as `Params`' statement, the field's limbs, and the two
  messages' encodings. **Commitments are ideal**: the proof carries the polynomials and the root the chain
  absorbs is Keccak-256 of an injective encoding of them, binding up to a collision (counted).
- **Random oracle on transcripts** (`ChainRom.lean`, `FreshBad.lean`, `Uniform.lean`): against a random oracle
  `H : bytes → 32 bytes`, a fresh query is bad (`chainBad`) when its answer collides with an earlier answer or
  sits where an earlier input holds a state or a root (`Coll`, at most `(3|H| + 2)/2^256`), or when it is a
  chain input whose challenge(s) turn the round's state from lost to won (`FirstBad`, `SecondBad`,
  `ThirdBad`: the first round's three hashes are treated as one triple of uniform states; the parse is unique
  given a collision-free history, so the three are exclusive, each at most `roundError`). The low 192 bits of
  a uniform state are uniform (`prEvent_chal`, every limb triple having `256^8` states). An accepted proof of
  cells that fail the relation makes a fresh query bad (`trace_chainBad`, through `bad_of_accepts` of
  `Joint.lean`); with an eager-table lemma whose bad events see the history (`prEvent_randomOracle_le_of_freshBad`,
  after VCVio's `prEvent_randomOracle_le_of_bad_queries`): **`knowledgeSoundness_chain`**, at most
  `(Q + 8)(roundError + 3(Q + 8)/2^256)` for `Q` adversary queries (the verifier's eight hashes counted).
- **The random-permutation model** (`Rpm.lean`): the experiment `rpmExperiment` has the adversary (coins, `π`,
  `π⁻¹`) and the verifier hashing with Keccak-256 over the same `π`; `common`'s `runK_expand`, `runK_relabel`
  and `keccak256_transfer` move it to the ROM against `advS` (cost `Q²/2^509`, `Q` the permutation calls of
  the whole game), leanerVM's derandomization removes the simulator's coins (`exists_det`).
  **`knowledgeSoundness_rpm`**: `(Q + 8)(roundError + 3(Q + 8)/2^256) + Q²/2^509`; at the protocol's sizes
  (`roundError_le`: `≤ 2^-163`, the identities' degree `2^29` over `2^192`) **`knowledgeSoundness_rpm_bits`**
  and, for every circuit, **`Instance.soundness_rpm`**: `(Q + 8)(2^-163 + 3(Q + 8)/2^256) + Q²/2^509`.

## The composition on the PCS claims (F4b)

`Compose/` ([README](Compose/README.md)) composes F1 with real commitments whose openings are only list-sound;
`ComposePcs/` and `SoundPcs/` do it for the EIP's PCS claims, where each of the four commitments is a root and its
out-of-domain answer.

- **`ComposePcs/`** (library `ComposePcs`). The four-root chain (`ListChain4.lean`, `chainWith4`, the Statement's
  `reduceWith`): the label (the circuit's commitment, the statement), `W`'s commitment then `α, β, γ`, the
  commitments of `H`, `Q`, `G` then `t`, the five values then `ρ`; each challenge union-bounded over the four roots'
  lists (`Bits4.lean`, `listError4_le_certified`: `7908 · 4473 · 3564 · 7908 < 2^50` tuples, `2^-114` a query), in
  mumbai's two-oracle model (`TwoOracle4.lean`, `knowledgeSoundness_list_kc4`), the extractor reading the adversary's
  log only (`AdversaryLog4.lean`, `adversaryExtractor4`), the openings any computation after the chain
  (`Openings4.lean`). **`Pinned4.lean`**: each root is absorbed with its out-of-domain answer, so each challenge is
  bounded for the one candidate tuple the answers pin (`prEvent_pinned_le`), F1's round error `2^-164` a query
  instead of the union.
- **`SoundPcs/`** (library `SoundPcs`). The deployed composition in mumbai's two-oracle model,
  **`knowledgeSoundness_deployed_pcs`** (`Final.lean`): the setup computes the circuit's commitment with the oracle
  (`setupPcs`: the wiring table's tree and out-of-domain answer); the run `dExp` is the adversary, `chainWith4`,
  `claimsAt` and six gated openings (`pcsVerifierO`, F2); the four roots' lists are separated at their points except
  with `ood_binding_coords`'s probability; the claims are F1's (`claimsMatch`, through `PcsBridge.claimsAt_eq`); the
  bound is `deployedBound`.
- **`EndToEnd/Soundness/Pcs*.lean`**: the Statement's experiment to `SoundPcs`'s (`rpm_le_romG`, `le_dExp`), the
  Statement's verifier, setup and extractor to the composition's; the file table is in `EndToEnd/Soundness.lean`.
  `PcsBridge` (`EndToEnd/PcsBridge/`) proves the Statement's six claims are `Compose.Reduce.reduce`'s
  (`claimsAt_eq`) and the quotient table the assembly of its three parts (`mle_assemble`); `Bridge`
  (`EndToEnd/Bridge/`) proves the Statement's circuit, transcript words, constants, transform and commitment the
  proof layers' (shared with the leanVM line).

## Zero knowledge (`EndToEnd/ZK`)

The Statement states zero knowledge for a simulator given as a parameter, `PcsQuotient.ZeroKnowledgeWith s₀ sim
simOracle ζ` (`Statement/PcsQuotient/Security.lean`). `Statement/PcsQuotient/Zk.lean` defines the PCS simulator
interface (`PcsSimulator`), the hybrid experiment with the ideal PCS (`hybridExperiment`: the secret tables committed
with uniform roots and opened by the PCS simulator), the hypotheses `PcsZeroKnowledge`, `RevealedUniform` and
`FiatShamirUniform`, and the simulator `zkSimulator`: the Statement's challenge phase (`challengePhase`) with the
revealed scalars answered uniformly (`uniformReveal`), then the openings (`finishOpenings`). The proof, library `ZK`:

- `ZK/PcsTrace.lean`: the adaptivity argument for any program of black-box steps and reveal queries (`RProg`):
  answering the reveals by a function of the coins or by fresh uniform draws differs, on every event, by at most the
  probability that the ideal run's log of reveals is not good (`RProg.trace_le`).
- `ZK/PcsProc.lean`: the challenge phase as such a program (`phaseProg`), its log's queries `revealQueries`.
- `ZK/PcsReplay.lean`, `ZK/PcsRoot.lean`, `ZK/PcsHybrid.lean`: the hybrid prover is the challenge phase with the
  prover's answers, then the openings (`hybrid_run_eq`); `ZK/PcsCoins.lean`: the prover's coins as `ProbComp`.
- `ZK/PcsEnd.lean`: `zeroKnowledge_pcs`, the end theorem with `FiatShamirUniform εfs` as a hypothesis.
- `ZK/PcsFSClosed.lean`: that hypothesis proved, **`fiatShamirUniform_closed`** (`εfs₀ = 113 · δq L ≤ 2^-162`,
  `εfs₀_le`), from `ZK/PcsFresh.lean` (the lazily sampled permutation against independent uniform answers on tracked
  queries), `ZK/PcsPhaseF.lean` (the challenge phase with its `113` challenge calls tracked), `ZK/PcsExtract.lean`,
  `ZK/PcsStream.lean`, `ZK/PcsPhi.lean`, `ZK/PcsIdealC.lean` (the ideal run's challenges are uniform), `ZK/PcsBad*.lean`,
  `ZK/PcsAdds.lean`, `ZK/PcsNF.lean`, `ZK/PcsInj.lean` (each tracked input is injective in a value drawn just before
  it); and **`zeroKnowledge_pcs_closed`**. `ZK/PcsAxioms.lean` guards the axioms.

`RevealedUniform` is the open part ([above](#end-to-end-theorems)): `HIDING.md`'s rank conditions are tested in the
Rust (`hiding.rs`), not proved, and the random rows enter the gate's quotient `GF(2)`-linearly. `PcsZeroKnowledge`
is the EIP's assumption of a ZK-WHIR; the reference openings, leanVM's WHIR, are not zero knowledge.

## Completeness

- **`Completeness/`** (package and library `Completeness`, built like `Compose/` against leanerVM `mumbai`'s
  `lean_vm`): the layer the end theorem's pieces come from: the circuit (`Circuit.lean`, `honest_relation`; with
  the random rows' cells holding any values, `honest_relation_deployed_random`), the reduction (`Reduction.lean`,
  `honest_accepts`), the novel-basis tables and quotients over `K` (`Tables.lean`, `Honest.lean`, `Read.lean`),
  mumbai's WHIR completeness (`Opening.lean`, `honestOpen_accepts`), and the deployed circuit, σ, weights and basis
  (`Membership.lean`, `QuotientSecurity/DeployedHonest.lean`, `QuotientSecurity/DeployedBasis.lean`). Its own end
  theorems (`completeness_deployed_concrete`, `completeness_deployed_keccak`) are the previous protocol's, with its
  three layout openings (`HiddenOpenings.lean`); they still build, as the PCS proof imports the library.
- **`EndToEnd/Completeness/`** (library `E2ECompleteness`): `PcsQuotient.Completeness deltaPcs`, no hypothesis
  (`completeness_end`, `E2ECompleteness/PcsDone.lean`; the numbers in the bullet [above](#end-to-end-theorems)).
  `PcsWithHash`, `PcsExperiment`, `PcsStaging`: the Statement's prover and verifier at explicit hash functions, the
  experiment staged by the four challenges (`completenessExperiment_eq_expH`, `expH_eq_staged`); `PcsChain`: the four
  challenges fresh by their lengths in the two-call random-oracle model (`prEvent_staged4_le`); `Transfer`,
  `PcsDuplex`, `PcsCost`, `PcsHashLen`: the random permutation as two random oracles (`rpm_le_rom`), the duplex
  discipline, at most `2^48` blocks (`hcost_deployed`); `PcsBad`, `PcsGrinding`, `PcsEnd`: the degenerate challenges
  (`badP4_fraction_le`), the six openings' grinding (`rejectGood_of_tail`), `completeness_of_staged4`,
  `deltaPcs_lt`; `PcsHonest` … `PcsClaims`: the honest parts are F1's blinded honest second message
  (`quotientsOfTable_honest`) and the six claims hold (`honestClaims`); `PcsAccept`, `PcsOpening`: accepted. The
  shared layers `Chain`, `Regular`, `Transfer`, `Grinding`, `End`, `Cost`, `Duplex`, `HashLen`, `WithHash`,
  `ProverOpening` are the previous protocol's, pruned to what this proof uses.

## The port to this protocol (F1)

`README.upstream.md` describes leanVM's circuit; this protocol differs in three ways, and the Lean files now
describe this one.

- **The gate** (`Protocol.lean`'s `gate`, `quotient::protocol`'s `gate`): `V + X + C + Y·C`, that is
  `V = X ⊕ (C ∧ ¬Y)` on bits (Keccak's χ), of degree 2, with no `θ` and no carries. `θ = β_1` stays in `Params`:
  it places a row's four cells at `x, x + 1, x + θ, x + θ + 1`.
- **The circuit argument** (`Circuit.lean`): `ChiCircuit` replaces `AdderCircuit`. An input row reads its own
  output in `X`, `Y` and `C` (`quotient::circuit::Builder::input`), so its gate is `v + v + v + v·v = v^2 + v`
  and `input_is_bit`: it holds `0` or `1`; every other row reads constants or rows of lower rank, and
  `gate_output`: on bits the gate gives `V = chiOf X Y C`, a bit. `ChiCircuit.determined`: two assignments, in
  any field of characteristic 2, that satisfy every gate and agree on the inputs agree everywhere, and every
  output is a bit (no `GF(4)`). `cells_determined`, `copy_iterate`, `word_pins`, `Wired` are as before, on bits.
- **The size**: `2^22` rows, cells named by `m = 24` bits (`22 + 2`, the opaque `le24`), `N = 2^24` cells;
  the tables have `m + 1 = 25` (witness), `m = 24` (wiring) and `m + 6 = 30` (quotient) variables, as
  `claims_iff_accepts_ofCantor` states them (the WHIR stacks of `opening::Layout` are not modelled: a table
  of the layout is a table whose other chunks are zero). The PCS protocol commits the quotient table in three
  parts, `H`, `Q`, `G` (`PcsBridge.mle_assemble`: the table is their assembly).

**The bounds, re-derived** (`Degrees.lean`, `Concrete.lean`, `Bits.lean`). `Bounds.identity` is the largest
of the bounds on the terms of the two identities (upstream summed them): with the gate of degree 2 it is
`max (max (2 * denominator) cells + max cells rows + quotient) (2 * denominator + max (pub + cell) (2 * cell))`
(the terms `D D' h`, `v_cells q`, `v_rows (D D' q_gate + v_cells j)`, `pub w D D'`, `D D' gate`; it bounds the
product the verifier inverts too). At the instance's table sizes
(witness polynomials `2^23`, quotients `2^26`, wiring and cells `2^24`, rows `2^22`, public weight
`2^24 + 9 * 2^10`): a cell's polynomial `4 * 2^23 + 3`, a denominator `3 * 2^24 + 4`, and
`Params.ofCantor_identity_eq`: the identities' degree is at most `11 * 2^24 + 8` (`11 N` and a little, the copy
identity's `D D' h`; the sum was `2^28 + 2^22 + 9230`), so `Params.ofCantor_identity_le_margin`: at most `2^28`
(and `Params.ofCantor_identity`: at most `2^29`). The public weight's degree (`natDegree_membershipPub_le`) is
`Σ_{11 ≤ j < 24} 2^j + 11 * 2^10 = 2^24 + 9 * 2^10`. The three round errors over `q = 2^192`
(`rbrError_le`): the copy argument `(4 N + 8) / q = (2^26 + 8) / 2^192`, about `2^-166` (was
`(2 N^2 + 4 N + 8) / q`, about `2^-143`; below), the identities `(11 * 2^24 + 8) / 2^192 < 2^-164`, the last
`3 / 2^192`; each `≤ 2^-128`, so `knowledgeSoundness_bits`, `knowledgeSoundness_ofCantor`,
`knowledgeSoundness_membership`, `Instance.soundness` give `(Q + 3) / 2^128`.

*The first challenge, tight* (`card_consistent_le`, `card_copy_le`, `LogDerivative.lean`). Upstream excluded
`2 N^2` values of `β` (any two poles meeting) and `2 N q^2` triples with a vanishing denominator. Now, if the
copy from `x₁` to `σ x₁` fails: a consistent triple has, at every cell, both denominators zero or neither
(`consistent_denominators`: the copy identity at a cell is `D D' h = D + D' + pub w D D'`), and where none
vanishes the sum of logarithmic derivatives meets the target. The pole `w(σ x₁) + β σ x₁` of the first term of
`σ x₁` is cancelled only by the first term of another cell (`N - 1` values of `β`) or the second term of a
cell other than `x₁` (`N - 1` values; the second term of `x₁` has the same label and another value): outside
these `2 N - 2` values (`poleBetas`) the cleared polynomial in `α` is not zero and of degree at most `2 N`, and
every consistent `α` is a root of it (one at which a cell's two denominators vanish together too). So at most
`(2 N - 2) q + 2 N q` pairs `(α, β)` per `γ`, and with the other cases (a gate fails: `2 N q^2`; a word fails:
`(2 N + words) q^2`) at most `(4 N + words) q^2` triples. This also beats an earlier bound, `(6 N + 8) / q`,
which still counted the triples with a vanishing denominator apart.

*The margin for WHIR's lists* (`rbrError_mul_sq_le`, `rbrError_list_margin`, `rbrError_list_margin_ofCantor`,
`roundError_mul_sq_le`; used by the union bounds of `Compose` and of `ComposePcs/ListChain4.lean`, while the end
theorem's chain is pinned by the out-of-domain answers instead, `Pinned4.lean`). With WHIR without an out-of-domain
sample at level 0, each challenge is
union-bounded over the level-0 Johnson lists involved: `L` for `(α, β, γ)` and for `ρ`, `L^2` for `t`. For any
`L ≤ 2^18` (leanerVM's generic list hypothesis; its certified parameters give `L ≤ 7908`) and identities of
degree at most `2^28`, every round error times `L^2` stays at most `2^-128`: on the instance
`2^36 (2^26 + 8) / 2^192`, about `2^-130`, `2^36 (11 * 2^24 + 8) / 2^192`, about `2^-128.5`, and
`3 * 2^36 / 2^192`. Both tightenings are needed: upstream's first round times `2^18` is `2^-125`, and the
summed degree `2^28 + 2^22 + 9230` times `2^36` exceeds `2^-128`.
Zero knowledge: `zkError = (2 N + 4 * 2^22) / q = 3 * 2^24 / 2^192` (`zkError_le`, the mask's vanishing
polynomial `w_22` in the row variable). The honest messages (`honest_legal`, for a first message of degree
`2^22 + 2`): copy quotient at most `3 * 2^24 + 9249`, gate quotient at most `7 * 2^22 + 22`, both within the
quotient table's `2^26`. Completeness's uncounted rejection (`1 + w_k(t) = 0` for some `k ≤ m + 1`) is now
about `2^26 / q`.

**The claims against the Rust `reduce`.** Reviewed coordinate by coordinate for this protocol: the witness,
wiring and quotient claims' points and values, the sum claim, the cells of the row of `t`, the gate, the
public weight's product, the target, the rows' polynomial and the rejection; the comparison is written out
above `claims_iff_accepts_ofCantor` (`Concrete.lean`). No mismatch; `reduce` is leanVM's but for the gate,
which is the model's `gate` on `cellAt`.
