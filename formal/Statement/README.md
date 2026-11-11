<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The structure follows leanerVM's `Statement/README.md` (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0). -->

# Statement

> **Of `f96a7938`'s protocol, not the deployed one.** This package states the membership protocol of commit
> `f96a7938`: six one-point claims on four commitments ([`docs/HISTORY.md`](../../docs/HISTORY.md), "Membership at
> f96a7938"). The deployed Rust has three claims on two commitments and the circuit's, the gate `V = Y + C + X·C`,
> `x h` in the quotient table ([`docs/membership/PROTOCOL.md`](../../docs/membership/PROTOCOL.md)); the port is
> [`docs/LEAN_PORT.md`](../../docs/LEAN_PORT.md). "The Rust" below is `f96a7938`'s.

What `crates/membership/quotient` is proved to be, in the files a reviewer reads: **definitions and end statements
only**, no proof, one Lake package (`pcs-quotient-statement`, library `PcsQuotient`) of fifteen files,
`PcsQuotient/<Name>.lean`. It depends on leanerVM's `Statement/` package (`statement`, branch `mumbai`, commit
`6175f1a0`), whose definitions it reuses rather than restates: `K = GF(2^64)`, `E = GF(2^192)`, Keccak-f[1600] and
Keccak-256 over any permutation, the random-permutation model, leanVM's WHIR verifier and the pieces of its prover, the
extractor's Merkle inversion and list decoder (toolchain `leanprover/lean4:v4.34.1`). The proofs are in
`formal/EndToEnd` ([`../README.md`](../README.md), "Membership: the end theorems"). `PcsQuotientTest/` is the
differential test, not the statement.

**The model.** Every end statement with an adversary is in mumbai's random-permutation model: one uniformly random
permutation `π` of the 1600-bit Keccak state, queried forward and inverse by every party, Keccak-256 the sponge over
`π`. Deployed, one Keccak-256 serves the reduction's chain, the WHIR Merkle trees, the openings' duplex, the circuit's
commitment and the relation; in the model each of these is Keccak-256 over the one `π`, the circuit's commitment
computed by a **setup** before the adversary runs. The **relation** is over the deployed Keccak-256 (which the circuit
computes on bits), independent of `π`. Each PCS opening seeds its transcript with the Keccak-256 of the claim's bytes
(`pcsClaimBytes`), and the verifier derives each commitment's out-of-domain point from its root with Keccak-256 over
`π` (`oodPointWith`); `formal/WhirBridge` proves the opening sound so (`pcs_sound_oracle`). The adversary is classical,
its code fixed before `π` is sampled.

**The sources.** Each definition cites the Rust it transcribes (`protocol.rs`, `opening.rs`, `circuit.rs:N`, …) of
`crates/membership/quotient` at `f96a7938`, and each file names what it takes from leanerVM in its first lines.

## Reading order

1. [`Relation.lean`](PcsQuotient/Relation.lean): `Statement` (`y`, `root`), `Secret` (`x`, `32` siblings and
   directions), **`Relation`**: `y = H(x ‖ 0x11^32)` and the path from `H(x ‖ 0x22^32)` folds to `root`. Keccak-256
   membership itself, not a circuit's satisfiability.
2. [`Domain.lean`](PcsQuotient/Domain.lean): the Cantor basis, the cells' points, `w_k`, the constants the verifier
   reads with their defining properties (`IsCantorBasis`, `CoordinatesRead`, `RowVanishingProperty`), the additive
   transform (`values`, `coefficients`).
3. [`Transcript.lean`](PcsQuotient/Transcript.lean): the reduction's Keccak-256 chain over a permutation `F`.
4. [`Reduction.lean`](PcsQuotient/Reduction.lean): the reduction's proof (four commitments `W`, `H`, `Q`, `G`, each
   its root's big-endian halves and its out-of-domain answer, the four row values, `next`, `Q`'s and `G`'s values:
   nineteen scalars), the **six claims** (witness, wiring, `H`, `Q`, `G`, sum), `quotientParts`, `statementWords`,
   `Supported` (`2^13` to `2^22` rows), and **`reduceWith`**, `claimsAt` (`reduce` line by line).
5. [`Opening.lean`](PcsQuotient/Opening.lean): the earlier layout opening (version 2), kept for the leanVM line's
   PIOPs; the membership verifier does not use it.
6. [`PcsOpening.lean`](PcsQuotient/PcsOpening.lean): **the PCS claim, version 1** (`crates/pcs_claim`,
   [`docs/PCS_CLAIM.md`](../../docs/PCS_CLAIM.md)): `tableEval`, `commitWith`, `commitmentWith` (root and the answer at
   `oodPointWith`), `pcsClaimBytes`, and **`pcsOpeningWith`** (IV `keccak256(PCS_claim)`, the root as the proof's
   first scalars, `verifyStackedOpening` of `f(z) = ood` and `f(point) = value`, rate `1/2`).
7. [`Verifier.lean`](PcsQuotient/Verifier.lean): `Proof` (the reduction's proof and six openings) and **`verifyWith`**.
8. [`Circuit.lean`](PcsQuotient/Circuit.lean): the circuit (gate `V = X + C + Y·C`, Keccak-f[1600] on wires,
   `membership`, the public rows, the 16 random rows, `σ`) and **its commitment** (`Circuit.indexCommitmentWith`, its
   tree `Circuit.indexTreeWith`, `Tree.evaluations`).
9. [`LayoutsProver.lean`](PcsQuotient/LayoutsProver.lean): the layout opening's prover, kept for the leanVM line.
10. [`Prover.lean`](PcsQuotient/Prover.lean): **the honest prover** (`proveWith`, `proverWith`; `proveWithPcs` over
    abstract PCS operations, `realPcs`): `Coins` (masks, random rows' values, the blinding of `h`), its tables, its
    openings by mumbai's WHIR prover pieces.
11. [`Replay.lean`](PcsQuotient/Replay.lean), 12. [`Decoder.lean`](PcsQuotient/Decoder.lean),
    13. [`Extractor.lean`](PcsQuotient/Extractor.lean): the transcript's evaluations and Merkle inversion; Gao's unique
    decoder; **the extractor** (`transcriptExtractorFor`).
14. [`Security.lean`](PcsQuotient/Security.lean): the deployed system (`setupWith`, `deployedIndex`,
    `deployedVerifier`), `sampleCoins`, the experiments, **`KnowledgeSoundness`, `Completeness`,
    `ZeroKnowledgeWith`**, `StatementBinds`, collected in `Theorems`.
15. [`Zk.lean`](PcsQuotient/Zk.lean): the ideal PCS, the hybrid experiment, **`PcsZeroKnowledge`, `RevealedUniform`**,
    `FiatShamirUniform`, and `zkSimulator`.

**The circuit and its commitment are named data**: `PcsQuotient.membership 22`, transcribed from
`quotient::circuit::membership`; `setupWith F` its wiring table's PCS commitment over `F`; `deployedIndex ()` the same
over Keccak-f[1600], equal to the Rust's by the differential test (`--index`). `formal/EndToEnd/Bridge/Circuit.lean`
proves `membership` equal to F0b's (`membership_eq`). Nothing in the statements quantifies over the circuit, the
wiring or the constants.

## The end statements

As written in [`Security.lean`](PcsQuotient/Security.lean): `KnowledgeSoundness ε` (for every adversary of `Q`
permutation calls, given the setup's commitment, Pr[the verifier accepts ∧ `extractor` returns no secret satisfying
`Relation`] ≤ `ε Q`), `Completeness δ` (for every statement and secret of the relation, the honest prover with
`sampleCoins` then the verifier rejects with probability ≤ `δ`), `ZeroKnowledgeWith s₀ sim simOracle ζ` (real and ideal
experiments within `ζ Q` both ways, for a distinguisher of `Q` calls quantified after the statement and witness),
`StatementBinds` (two secrets of one statement have one `x` or a pair collision). **Zero knowledge is for one proof**:
from an empty, lazily sampled `π`, the prover goes first and the distinguisher queries only after it has the proof.
`sampleCoins` is twelve mask words, the sixteen random rows' values and twenty-four blinding words of `h`, each uniform
in `K`, in the order the Rust's KDF derives them.

The bounds are parameters; the end theorems fix them:

* `ε = Soundness.ksBound`: `SoundPcs.deployedBound (2^20 + 24 + Q) + (5 · 2^19 + 24 + Q + 728890)² / 2^508`,
  `deployedBound` the six openings' `openingBound x = (x + 10122)(2^-128 + 5 (x + 10122) / 2^256)`, the four roots'
  binding (`N · (δc 25 + δc 27 + δc 28)` and three `N (N + 1) / 2^256`) and the chain `N (2^-164 + 8 N / 2^256)`. About
  `2^-104.4` at `Q = 0`, `2^-85.4` at `2^40`, `2^-61.4` at `2^64`.
* `δ = E2ECompleteness.Pcs.deltaPcs ≈ 2^-163.75` (`deltaPcs_lt`: `< 2^-163`).
* `ζ Q = εpcs Q + εr + εfs₀`, `εfs₀ ≤ 2^-162` proved (`εfs₀_le`).

Knowledge soundness needs no collision clause (an extracted secret satisfies the relation exactly). `StatementBinds`
holds outright (a pigeonhole on `y`'s preimages) and is not proved in Lean.

## The extractor

`extractor stmt setupEvals T proof` is `transcriptExtractorFor (membership 22)`. It reads the statement, the proof's
first two scalars (the witness root), the adversary's transcript `T` and the Keccak-256 evaluations of the circuit
commitment's tree, nothing else (no queries, no rewinding). It replays the evaluations whose whole sponge path the
adversary queried (hash maps), inverts the witness table's Merkle tree under the root (`2^20` leaves of `64` words, each
lane a Reed–Solomon word of `n = 2^20` symbols for messages of `k = 2^19`), then decodes in three stages, each only if
the earlier give no witness: the fast path (interpolation from the first `2^19` columns), Gao's unique decoder (up to
`2^18` wrong columns a lane), the Guruswami–Sudan list decoder (the Johnson threshold, `741549` columns). A candidate
stack is the witness table; the extractor reads the input rows' `V` cells as bits and returns the first candidate's
secret satisfying the relation. Its cost (read off its loops, `Extractor.lean`'s table): about `2^31.4` operations for
the fast path, `2^34.3` to `2^45.7` for the unique decoder, the list decoder infeasible (`≈ 2^98.3`) but reached only by
a word beyond the unique-decoding radius. Gao's theorem is tested (`PcsQuotientTest/Decoder.lean`), not proved; the
soundness proof does not need it.

## The simulator

Zero knowledge assumes a zero-knowledge PCS ([`docs/membership/PROTOCOL.md`](../../docs/membership/PROTOCOL.md),
"Zero knowledge", for the deployed protocol; the deployed openings, leanVM's WHIR, are not zero knowledge).

* **`PcsSimulator`**: its state and an opening simulator `simOpen`, which sees only the commitment and the claim and may
  program the permutation (mumbai's lazily sampled permutation, `edgeOracle`).
* **The hybrid** (`hybridExperiment`): the honest prover, its four secret tables committed with uniform roots and opened
  by `simOpen` (`idealPcs`); the circuit's commitment and the wiring opening real.
* **`PcsZeroKnowledge sim εpcs`**: real and hybrid within `εpcs Q`. **`RevealedUniform εr`**: outside challenge tuples
  of probability `εr`, the ten revealed scalars (four out-of-domain answers, four `a_j`, `Q`'s and `G`'s values) are
  uniform when the prover's randomness is; tested in the Rust (`hiding.rs`), not proved.
* **`zkSimulator sim`** reads no witness: the circuit committed, uniform secret roots, uniformly drawn revealed scalars,
  the chain run on them, the wiring claim opened by the real WHIR prover, the five secret claims by `simOpen`.
* **`FiatShamirUniform`**: proved at `εfs₀ ≤ 2^-162` (`fiatShamirUniform_closed`).

## Deviations from the Rust

* WHIR proofs in mumbai's format, one full Merkle path per query; the Rust ships pruned paths (expansion not
  formalized).
* The reduction's proof is a structure of nineteen scalars (`ReductionProof.ofStream` reads a stream).
* The verifier inverts denominators one by one after checking none is zero; the Rust inverts their product by the norm
  (same values). The target is a fold over `statementWords` (same value).
* The prover's randomness is uniform; the deployed prover derives it by a Keccak-256 KDF (`Randomness::derive`), so
  deployed zero knowledge is computational in it.
* The EVM contract: F5 and `formal/EndToEnd/Evm` (`evm_accepts_iff_verifyWith`), what the block proves of a claim
  modelled by `pcsOpen`.

## Building and testing (the differential test is `f96a7938`-only)

```sh
lake build                                   # the statement: PcsQuotient
lake build PcsQuotientTest differential      # constants' properties, unique decoder, inversion, the test
```

The vectors must come from a checkout of `f96a7938`: at `main`, `examples/statement_vectors.rs` writes the deployed
protocol's vectors (two commitments, three claims), which this package does not state. At `f96a7938`:

```sh
cargo run --release -p quotient --example statement_vectors -- vectors.txt --index   # --full: also whole 2^22 proofs
.lake/build/bin/differential vectors.txt     # Lean's verdicts, claims, commitments and streams vs Rust's
.lake/build/bin/differential --self-test     # the extractor's inversion and decoding
```

The test checks: on random and honest nineteen-scalar streams at `2^12` to `2^23` rows, that `reduce` gives the Rust's
four commitments and six claims or rejects as it does (`R`); on whole proofs of a `2^17`-row circuit, honest and
tampered seventeen ways, that `verify` gives the Rust's verdict (`P`); that the Lean builder and commitment give the
Rust circuits' sizes, inputs and commitments, the membership circuit's with `--index` (`I`); that the Lean prover, given
the Rust prover's inputs and derived randomness, sends the Rust's reduction stream and its proof is accepted (`Q`, at
`2^17` rows; the openings are not compared). The test checks the constants' properties by `native_decide`; the proofs
check the ones they use by kernel evaluation.
