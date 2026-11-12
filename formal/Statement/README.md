<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The structure follows leanerVM's `Statement/README.md` (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0). -->

# Statement

What `crates/membership/quotient` is proved to be, in the files a reviewer reads: **definitions and end statements
only**, no proof, one Lake package (`pcs-quotient-statement`, library `PcsQuotient`) of fifteen files,
`PcsQuotient/<Name>.lean`, of the deployed protocol ([`docs/membership/PROTOCOL.md`](../../docs/membership/PROTOCOL.md):
transcript `pcs-quotient-kc3`, three claims on two commitments and the circuit's). It depends on leanerVM's
`Statement/` package (`statement`, branch `mumbai`, commit `6175f1a0`), whose definitions it reuses rather than
restates: `K = GF(2^64)`, `E = GF(2^192)`, Keccak-f[1600] and Keccak-256 over any permutation, the
random-permutation model, leanVM's WHIR verifier and the pieces of its prover, the extractor's Merkle inversion and
list decoder (toolchain `leanprover/lean4:v4.34.1`). The proofs are in `formal/EndToEnd`
([`../README.md`](../README.md), "Membership: the end theorems"). `PcsQuotientTest/` is the differential test, not
the statement.

**The model.** Every end statement with an adversary is in mumbai's random-permutation model: one uniformly random
permutation `π` of the 1600-bit Keccak state, queried forward and inverse by every party, Keccak-256 the sponge over
`π`. Deployed, one Keccak-256 serves the reduction's chain, the WHIR Merkle trees, the openings' duplex, the circuit's
commitment and the relation; in the model each of these is Keccak-256 over the one `π`, the circuit's commitment
computed by a **setup** before the adversary runs. The **relation** is over the deployed Keccak-256 (which the circuit
computes on bits), independent of `π`. Each PCS opening seeds its transcript with the Keccak-256 of the claim's bytes
(`pcsClaimBytes`), and the verifier derives each commitment's out-of-domain point from its root with Keccak-256 over
`π` (`oodPointWith`). The adversary is classical, its code fixed before `π` is sampled.

**The sources.** Each definition cites the Rust it transcribes (`protocol.rs`, `opening.rs`, `circuit.rs`, …) of
`crates/membership/quotient`, and each file names what it takes from leanerVM in its first lines.

## Reading order

1. [`Relation.lean`](PcsQuotient/Relation.lean): `Statement` (`y`, `root`), `Secret` (`x`, `32` siblings and
   directions), **`Relation`**: `y = H(x ‖ 0x11^32)` and the path from `H(x ‖ 0x22^32)` folds to `root`. Keccak-256
   membership itself, not a circuit's satisfiability.
2. [`Domain.lean`](PcsQuotient/Domain.lean): the Cantor basis, the cells' points, `w_k`, the constants the verifier
   reads with their defining properties (`IsCantorBasis`, `CoordinatesRead`, `RowVanishingProperty`), the additive
   transform (`values`, `coefficients`).
3. [`Transcript.lean`](PcsQuotient/Transcript.lean): the reduction's Keccak-256 chain over a permutation `F`.
4. [`Reduction.lean`](PcsQuotient/Reduction.lean): the reduction's proof (two commitments `W`, `T`, each its root's
   big-endian halves and its out-of-domain answer; `X`, `C`, `V + Y` at `t`; `next`: ten scalars), the **three
   claims** (witness on the row polynomials' conic, wiring, copy on `T`), the pins (`pinPoints`, `pinWeights`,
   `anchorValues`, `Statement.words`), `rowValues`, `witnessConic`, `witnessWeights`, `copyPoint`, `tableSlot`,
   `Supported` (`2^13` to `2^22` rows), and **`reduceWith`**, `claimsAt` (`reduce` line by line).
5. [`Opening.lean`](PcsQuotient/Opening.lean): the earlier layout opening (version 2), kept for the leanVM line's
   PIOPs; the membership verifier does not use it.
6. [`PcsOpening.lean`](PcsQuotient/PcsOpening.lean): **the PCS claim, version 1** (`crates/pcs_claim`,
   [`docs/PCS_CLAIM.md`](../../docs/PCS_CLAIM.md)): `tableEval`, `commitWith`, `commitmentWith` (root and the answer at
   `oodPointWith`), `pcsClaimBytes`, and **`pcsOpeningWith`** (IV `keccak256(PCS_claim)`, the root as the proof's
   first scalars, `verifyStackedOpening` of `f(z) = ood` and `f(point) = value`, rate `1/2`).
7. [`Verifier.lean`](PcsQuotient/Verifier.lean): `Proof` (the reduction's proof and three openings) and
   **`verifyWith`**.
8. [`Circuit.lean`](PcsQuotient/Circuit.lean): the circuit (gate `V = Y + C + X·C`, Keccak-f[1600] on wires,
   `membership`; `finish`: the packing rows of the eight public `K`-words, the eleven anchors, the sixteen random rows
   of three shapes, `σ`), `Circuit.cells`, `errorsHaveTheirOwnPoles` (`Index::new`'s check), and **its commitment**
   (`Circuit.indexCommitmentWith`, its tree `Circuit.indexTreeWith`, `Tree.evaluations`).
9. [`LayoutsProver.lean`](PcsQuotient/LayoutsProver.lean): the layout opening's prover, kept for the leanVM line.
10. [`Prover.lean`](PcsQuotient/Prover.lean): **the honest prover** (`proveWith`, `proverWith`; `proveWithPcs` over
    abstract PCS operations, `realPcs`): `Coins` (the random rows' words, the blinding `b₀, b₁` of `h`, the quotient
    table's four slack words), the random
    rows filled (`randomizeCells`), the witness table, the quotient table (`quotientParts`: `h`, the quotient on a
    coset of `4 n` points with `b₂` solved; `quotientTable`: `A₀`, `A₁ = Q_h / x` by `divX`, `B₀ = x h_low` by `mulX`,
    `B₁ = (b₀, b₁, b₂)`, the slack words `(s, s, 0, s)` in limbs 0 to 3 of four of `A₀`'s coefficients, which read
    zero), the values at `t` (`valuesAt`), its openings by mumbai's WHIR prover pieces.
11. [`Replay.lean`](PcsQuotient/Replay.lean), 12. [`Decoder.lean`](PcsQuotient/Decoder.lean),
    13. [`Extractor.lean`](PcsQuotient/Extractor.lean): the transcript's evaluations and Merkle inversion; Gao's unique
    decoder; **the extractor** (`transcriptExtractorFor`).
14. [`Security.lean`](PcsQuotient/Security.lean): the deployed system (`setupWith`, `deployedIndex`,
    `deployedVerifier`), `sampleCoins`, the experiments (`pcsExperiment pcs`: the protocol over a PCS),
    **`KnowledgeSoundness`, `Completeness`, `ZeroKnowledgeWith pcs`**, `StatementBinds`; the first two (for the
    deployed PCS) collected in `Theorems`.
15. [`Zk.lean`](PcsQuotient/Zk.lean): the ideal PCS (the hybrid's, and `PcsOps.idealOf`, a PCS of the model), the
    hybrid experiment, **`PcsZeroKnowledge pcs`, `RevealedUniform`**, `FiatShamirUniform`, and `zkSimulator`.

**The circuit and its commitment are named data**: `PcsQuotient.membership 22`, transcribed from
`quotient::circuit::membership`; `setupWith F` its wiring table's PCS commitment over `F`; `deployedIndex ()` the same
over Keccak-f[1600], equal to the Rust's by the differential test (`I` lines). Nothing in the statements quantifies over
the circuit, the wiring or the constants.

## The end statements

As written in [`Security.lean`](PcsQuotient/Security.lean): `KnowledgeSoundness ε` (for every adversary of `Q`
permutation calls, given the setup's commitment, Pr[the verifier accepts ∧ `extractor` returns no secret satisfying
`Relation`] ≤ `ε Q`), `Completeness δ` (for every statement and secret of the relation, the honest prover with
`sampleCoins` then the verifier rejects with probability ≤ `δ`), `ZeroKnowledgeWith s₀ sim simOracle ζ` (real and ideal
experiments within `ζ Q` both ways, for a distinguisher of `Q` calls quantified after the statement and witness),
`StatementBinds` (two secrets of one statement have one `x` or a pair collision). **Zero knowledge is for one proof**:
from an empty, lazily sampled `π`, the prover goes first and the distinguisher queries only after it has the proof.
`sampleCoins` is the thirty-two random rows' words, the six blinding words of `h` (`b₀, b₁` of each limb) and the
four slack words, each uniform in `K`, in the order the Rust's KDF derives them. The bounds are parameters; the end theorems fix them
([`../README.md`](../README.md)).

Knowledge soundness needs no collision clause (an extracted secret satisfies the relation exactly). `StatementBinds`
holds outright (a pigeonhole on `y`'s preimages) and is not proved in Lean.

## The extractor

`extractor stmt setupEvals T proof` is `transcriptExtractorFor (membership 22)`. It reads the statement, the proof's
first two scalars (the witness root), the adversary's transcript `T` and the Keccak-256 evaluations of the circuit
commitment's tree, nothing else (no queries, no rewinding). It replays the evaluations whose whole sponge path the
adversary queried (hash maps), inverts the witness table's Merkle tree under the root (`2^19` leaves of `64` words, each
lane a Reed–Solomon word of `n = 2^19` symbols for messages of `k = 2^18`), then decodes in three stages, each only if
the earlier give no witness: the fast path (interpolation from the first `2^18` columns), Gao's unique decoder (up to
`2^17` wrong columns a lane), the Guruswami–Sudan list decoder. A candidate stack is the witness table; the extractor
reads the input rows' `V` cells as bits and returns the first candidate's secret satisfying the relation. Its cost:
`Extractor.lean`'s table. Gao's theorem is tested (`PcsQuotientTest/Decoder.lean`), not proved; the soundness proof does
not need it.

## The simulator

Zero knowledge is stated for the protocol over a PCS `pcs` (`pcsExperiment pcs`, `ZeroKnowledgeWith pcs`: its two
secret tables committed and opened by `pcs`, a program of the model) and proved for every zero-knowledge `pcs`
([`docs/membership/PROTOCOL.md`](../../docs/membership/PROTOCOL.md), "Zero knowledge"). The deployed PCS (`realPcs`,
leanVM's WHIR) is not zero knowledge and is not an instance: `realExperiment` is `pcsExperiment (realPcs …)`, about which
no zero-knowledge theorem is stated.

* **`PcsSimulator`**: its state and an opening simulator `simOpen`, which sees only the commitment and the claim and may
  program the permutation (mumbai's lazily sampled permutation, `edgeOracle`).
* **The hybrid** (`hybridExperiment`): the honest prover, its two secret tables committed with uniform roots and opened
  by `simOpen` (`idealPcs`); the circuit's commitment and the wiring opening real.
* **`PcsZeroKnowledge pcs sim εpcs`**: the protocol over `pcs` and the hybrid within `εpcs Q` (the PCS's roots hiding,
  its openings simulated by `simOpen`, in the prover's use of it). Satisfiable: `PcsOps.idealOf simO` (uniform roots,
  openings any program `simO` of the commitment and the claim) meets it at `εpcs = 0` with `PcsSimulator.ofOpen simO`
  (`formal/EndToEnd/ZK/PcsIdeal.lean`). **`RevealedUniform εr`**: outside challenge tuples
  of probability `εr`, the five revealed scalars (two out-of-domain answers, `X`, `C`, `V + Y` at `t`) are uniform when
  the prover's randomness is (`PROTOCOL.md`'s two rank conditions).
* **`zkSimulator sim`** reads no witness: the circuit committed, uniform secret roots, uniformly drawn revealed scalars,
  the chain run on them, the wiring claim opened by the real WHIR prover, the two secret claims by `simOpen`.
* **`FiatShamirUniform`**: the simulator's challenges near-uniform, proved in `formal/EndToEnd/ZK`.

## Deviations from the Rust

* WHIR proofs in mumbai's format, one full Merkle path per query; the Rust ships pruned paths (expansion not
  formalized).
* The reduction's proof is a structure of ten scalars (`ReductionProof.ofStream` reads a stream).
* The verifier inverts denominators one by one after checking none is zero; the Rust inverts their product by the norm
  (same values).
* The prover computes the quotient on a coset of `4 n` points, where `w_1 d d'` (degree `2 n`) is exact, and solves
  `b₂` there; the Rust uses `2 n` points and corrects the top coefficient (same coefficients). The inverses are taken one
  by one (`0⁻¹ = 0`), which differs only at a challenge where a denominator vanishes.
* The prover's randomness is uniform; the deployed prover derives it by a Keccak-256 KDF (`Randomness::derive`), so
  deployed zero knowledge is computational in it.
* The EVM contract: `formal/Implementation` and `formal/EndToEnd/Evm` (`evm_accepts_iff_verifyWith`), what the block
  proves of a claim modelled by `pcsOpen`.

## Building and testing

The library builds in `formal/EndToEnd` (`lake build PcsQuotient`); the differential test is its executable
`membership-differential` (`formal/EndToEnd/lakefile.toml`):

```sh
cargo run --release -p quotient --example statement_vectors -- vectors.txt --index   # --full: also whole 2^22 proofs
lake build membership-differential
.lake/build/bin/membership-differential vectors.txt     # Lean's verdicts, claims, commitments and streams vs Rust's
.lake/build/bin/membership-differential --self-test     # the extractor's inversion and decoding
```

The test checks: on random and honest ten-scalar streams at `2^12` to `2^23` rows, that `reduce` gives the Rust's two
commitments and three claims or rejects as it does (`R`); on whole proofs of a `2^17`-row circuit, honest and tampered
seventeen ways, that `verify` gives the Rust's verdict (`P`); that the Lean builder and commitment give the Rust
circuits' sizes, inputs and commitments, the membership circuit's with `--index` (`I`); that the Lean prover, given the
Rust prover's inputs and derived randomness, sends the Rust's reduction stream and its proof is accepted (`Q`, at `2^17`
rows; the openings are not compared). `PcsQuotientTest/Constants.lean` checks the constants' properties by
`native_decide` (a test, outside the proofs, which check the ones they use by kernel evaluation).
