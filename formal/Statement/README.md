<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The structure follows leanerVM's `Statement/README.md` (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0). -->

# Statement

What `crates/membership/quotient` is proved to be, in the files a reviewer reads: **definitions and end
statements only**, no proof, one Lake package (`pcs-quotient-statement`, library `PcsQuotient`) of fifteen
files, `PcsQuotient/<Name>.lean` (Lean modules `PcsQuotient.<Name>`). It depends on leanerVM's
`Statement/` package (`statement`, branch `mumbai`, commit `6175f1a0`), whose definitions it reuses
rather than restates: `K = GF(2^64)` and `E = GF(2^192)`, Keccak-f[1600] and Keccak-256 over any
permutation, the random-permutation model, leanVM's WHIR verifier and the pieces of its prover, and its
extractor's Merkle inversion and list decoder. Mathlib, VCVio and CompPoly come through it, at mumbai's
revisions (the toolchain is `leanprover/lean4:v4.34.1`).

The extractor is an **explicit, computable definition** referenced by the statements, so that a reviewer
can check what it reads and that it is efficient (Lean has no running-time theorem; the convention is
mumbai's: a fixed straight-line extractor reading only the adversary's transcript, its cost read off its
loops). The simulator the zero-knowledge theorem covers, `zkSimulator` (`Zk.lean`), is named in the theorem's
statement; it is built on a PCS simulator given as a parameter ("The simulator", below). The extractor is not
F1's (`formal/QuotientSecurity`), which reads the proof's polynomials in the ideal model and is `noncomputable`. The proofs are in `formal/EndToEnd` (`formal/README.md`, "End-to-end
theorems"): knowledge soundness and completeness are proved with no hypotheses, zero knowledge under two named
hypotheses, a zero-knowledge PCS and the uniformity of the revealed scalars ("What is proved", below). `PcsQuotientTest/` is the differential test, not the
statement.

**The model.** Every end statement with an adversary is in mumbai's random-permutation model: one
uniformly random permutation `π` of the 1600-bit Keccak state, which every party queries forward (`π x`)
and inverse (`π⁻¹ y`), Keccak-256 the sponge over `π`. Deployed, **one Keccak-256** serves the reduction's
chain, the WHIR Merkle trees (`hash_pair` is byte for byte the relation's `pair`), the openings' duplex,
the circuit's commitment and the relation. In the model every hash of the protocol is Keccak-256 over the
one `π` (there is no private oracle), the circuit's commitment computed over `π` by a **setup** before the
adversary runs (deployed, the verifier holds it as a constant computed over Keccak-f[1600]); the
**relation** is over the deployed Keccak-256, which the circuit computes on bits, independent of `π` in the
model (mumbai's convention for leanVM's `KECCAK` instruction), with a **collision clause** where a statement
reads more than the relation (`StatementBinds`, as mumbai's `DigestBinds`). Each PCS opening seeds its
transcript with the Keccak-256 of the claim's bytes alone (`pcsClaimBytes`: the commitment's root and
out-of-domain answer, the point, the value), and the verifier derives each commitment's out-of-domain point from
its root with Keccak-256 over `π` (`oodPointWith`); `formal/WhirBridge` proves the opening sound with that
seeding and that point (`pcs_sound_oracle`). That the deployed Keccak-f[1600]
behaves as a random permutation is the assumption. The adversary is classical, its code fixed before `π`
is sampled.

**The sources.** Each definition cites the Rust it transcribes (`protocol.rs`, `opening.rs`,
`circuit.rs:N`, …) of `crates/membership/quotient` at `main` `abe22812` (the EIP's PCS claims,
`docs/membership/EIP_CLAIMS.md`), and each file names what it takes from leanerVM in its first lines.

## Reading order

1. [`Relation.lean`](PcsQuotient/Relation.lean): the statement (`Statement`: `y`, `root`), the secret
   (`Secret`: `x`, the `32` siblings, the `32` directions), and **`Relation`**: `y = H(x ‖ 0x11^32)` and
   the path from `H(x ‖ 0x22^32)` folds to `root`, `H` the deployed Keccak-256 of a 64-byte block
   (`statement.rs`). This is Keccak-256 membership itself, not a circuit's satisfiability.
2. [`Domain.lean`](PcsQuotient/Domain.lean): the Cantor basis `β₀ … β₂₇` of `K` (computed as the Rust
   computes it), the cells' points `B(i)`, the subspace polynomials `w_k = S^k`, the constants the
   verifier reads (`coordinates`, `rowVanishing`) **with their defining properties** (`IsCantorBasis`,
   `CoordinatesRead`, `RowVanishingProperty`, decidable, checked in `PcsQuotientTest/Constants.lean`), and
   the additive transform between a polynomial's novel-basis coefficients and its values on a coset
   (`values`, `coefficients`) that the prover and the extractor use (`domain.rs`).
3. [`Transcript.lean`](PcsQuotient/Transcript.lean): the reduction's Fiat–Shamir transcript, a
   Keccak-256 chain over a permutation `F` (`transcript.rs`).
4. [`Reduction.lean`](PcsQuotient/Reduction.lean): **the reduction's proof** (`ReductionProof`: four
   commitments `W`, `H`, `Q`, `G`, each its root's big-endian halves (`rootHalves`) and its out-of-domain answer,
   the four row values, `next`, then `Q`'s and `G`'s values: nineteen scalars), the **commitment** (`Commitment`:
   root, out-of-domain answer), the **six claims** (`Claims`: witness, wiring, `H`, `Q`, `G`, sum), the quotient
   table's parts (`quotientParts`), the statement embedding (`statementWords`), the sizes (`Supported`: `2^13` to
   `2^22` rows), the label (`label`: the name, the index commitment, the statement) and the reduction's verifier
   (`reduceWith`, `claimsAt`: `reduce` of `protocol.rs` line by line; `H`'s value derived from `Q`'s and `G`'s).
5. [`Opening.lean`](PcsQuotient/Opening.lean): **the previous protocol's layout opening**, kept unchanged for the
   leanVM line's PIOPs (`formal/UniStatement`, ...); the membership verifier does not use it. It also holds the
   constants `laneFold`, `logInvRate`, `zeroDigest`.
6. [`PcsOpening.lean`](PcsQuotient/PcsOpening.lean): **the EIP's PCS claim, version 1** (`crates/pcs_claim`,
   `docs/PCS_CLAIM.md`): a table's polynomial (`tableEval`), its commitment (`commitWith`, `commitmentWith`: the
   WHIR Merkle root and the out-of-domain answer at the point `oodPointWith` derives from the root with
   Keccak-256), the claim's bytes (`pcsClaimBytes`) and **the opening check** (`pcsOpeningWith`: the IV
   `keccak256(PCS_claim)`, the root as the proof's first scalars, mumbai's `verifyStackedOpening` of the two stack
   claims `f(z) = ood`, `f(point) = value`, WHIR at rate `1/2`).
7. [`Verifier.lean`](PcsQuotient/Verifier.lean): **the proof** (`Proof`: the reduction's proof and six openings)
   and **the verifier** (`verifyWith`): the reduction, then the six PCS openings in the order of `Claims::all`.
8. [`Circuit.lean`](PcsQuotient/Circuit.lean): **the circuit** (the gate `V = X + C + Y·C`, the builder,
   Keccak-f[1600] on wires, the membership statement `membership`, the public rows, the 16 **random rows**, the
   wiring `σ`), its cells from the inputs, and **its commitment** (`Circuit.indexCommitmentWith`: the wiring table's
   PCS commitment over `F`; its tree `Circuit.indexTreeWith`, and the tree's Keccak-256 evaluations
   `Tree.evaluations`, which the extractor reads).
9. [`LayoutsProver.lean`](PcsQuotient/LayoutsProver.lean): the previous layout opening's prover, kept for the
   leanVM line.
10. [`Prover.lean`](PcsQuotient/Prover.lean): **the honest prover** (`proveWith`, `proverWith`; over abstract PCS
    operations `proveWithPcs`, the real ones `realPcs`): its randomness (`Coins`: masks, random rows' values, the
    blinding of `h`), its tables as functions (`witnessTable`, `quotientTables`, `rowValues`), its PCS openings by
    mumbai's WHIR prover pieces (`pcsOpeningScript`, `proveClaimWith`), run against the verifier's program.
11. [`Replay.lean`](PcsQuotient/Replay.lean): the transcript's Keccak-256 evaluations and the Merkle inversion.
12. [`Decoder.lean`](PcsQuotient/Decoder.lean): **the unique decoder** (`UniqueDecoding.uniqueStacks`).
13. [`Extractor.lean`](PcsQuotient/Extractor.lean): **the extractor** (`transcriptExtractorFor`): the witness
    table's word under its root, decoded; a candidate stack is the table itself.
14. [`Security.lean`](PcsQuotient/Security.lean): the deployed system (`setupWith`: the circuit's commitment and
    tree; `verifier`, `deployedIndex`, `deployedVerifier`), the prover's coins (`sampleCoins`), the experiments, and
    **`KnowledgeSoundness`, `Completeness`, `ZeroKnowledgeWith`**, `StatementBinds`, collected in `Theorems`.
15. [`Zk.lean`](PcsQuotient/Zk.lean): **zero knowledge assuming a zero-knowledge PCS**: the ideal PCS, the hybrid
    experiment, and the two hypotheses the zero-knowledge theorem takes (`PcsZeroKnowledge`, `RevealedUniform`).

## The circuit and its commitment are named data

The deployed circuit is `PcsQuotient.membership logRows` (`Circuit.lean`, `logRows = 22`), a definition
transcribed from `quotient::circuit::membership`; its commitment is **a definition**, not a hypothesis:
`setupWith F = commitmentWith F (cellVars logRows) (membership logRows).wiringTable` (the wiring table's PCS
commitment over `F`, its root and out-of-domain answer, with its Merkle tree), and the deployed verifier's
constant is `deployedIndex ()`, `setupWith`'s commitment over Keccak-f[1600], which the differential test finds
equal to the Rust's (its `I` line for the membership circuit, `--index`). Layer F0 (a χ-circuit end theorem with the zero
and one pinned and the statement embedding `statementWords`; `formal/Circuit`'s `membership` proved to
compute Keccak-256 membership) plugs in here: `formal/EndToEnd/Bridge/Circuit.lean` proves this `membership`
equal to F0b's (`membership_eq`). Nothing in the statements quantifies over the circuit, the wiring or the
constants: they are the computed ones.

## How the proofs plug in

The package stays proof-free and imports only mumbai's `statement` (Mathlib, VCVio, CompPoly through it); the
proofs in `formal/EndToEnd` import it and prove its statements about its definitions (`formal/EndToEnd/Bridge`
proves each definition here equal to the proof layers' own):

* **The circuit**: F0b's `formal/Circuit` `membership` is a second transcription of the same builder (its
  wiring checked against the Rust's by hash); this package's `PcsQuotient.membership` is checked against the
  Rust's by the circuit's commitment. `formal/EndToEnd/Bridge/Circuit.lean` proves the two equal
  (`membership_eq`, builder step by builder step), so F0b's theorem speaks about `setupWith`'s circuit.
* **The extractor**: `transcriptExtractorFor` is mumbai's replay, `committedLeaves` and decoders on the
  witness table (with hash maps, and the unique decoder between the fast path and the list decoder), then
  the cells of the candidate table. `formal/EndToEnd/Soundness` proves `KnowledgeSoundness` for it
  (`Soundness.knowledgeSoundness`): its hash maps compute mumbai's lists where it reads them
  (`Soundness/Replay.lean`), and its last stage, the list decoder, lists every Johnson candidate, so a witness in
  the composition's extractor's list is one it returns (`Soundness/Extract.lean`, `Soundness/PcsExtract.lean`:
  `extractor_of_extracts`); nothing is needed of the first two stages.
* **The simulator**: zero knowledge is stated for any simulator, `ZeroKnowledgeWith s₀ sim simOracle ζ`
  (a simulator `Statement → StateT S ProbComp (Option Proof)`, its oracle
  `QueryImpl RandomPermutationOracles (StateT S ProbComp)`, its initial state `s₀`). The end theorem
  (`PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed`, `formal/EndToEnd/ZK/PcsFSClosed.lean`) proves it for
  `zkSimulator sim` (`Zk.lean`) with the oracle `sim.oracle` and the state `sim.s₀`, `sim` any PCS simulator
  (`PcsSimulator`), under the hypotheses `PcsZeroKnowledge sim εpcs` and `RevealedUniform εr`, both defined in
  `Zk.lean`; so the simulator the theorem covers is named in the theorem's statement.

## The end statements

As written in [`Security.lean`](PcsQuotient/Security.lean) (`PcsQuotient` namespace; `logRows = 22`):

```lean
noncomputable def soundnessExperiment (A : Adversary) : ProbComp Outcome :=
  runWithRandomPermutation do
    let (tree, index) ← setupWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles (A index)).run []
    let accepted ← verifier queryPermutation index z.1 z.2
    return ((z, accepted), Tree.evaluations tree, transcript)

def BreaksKnowledgeSoundness (z : Outcome) : Prop :=
  z.accepted ∧ ¬ ∃ w, extractor z.statement z.setupEvaluations z.transcript z.proof = some w ∧
    Relation z.statement w

def KnowledgeSoundness (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : Adversary) (Q : ℕ), (∀ index, QueryCostAtMost (A index) permutationCallCost Q) →
    Pr{let z ← soundnessExperiment A}[BreaksKnowledgeSoundness z] ≤ ε Q

noncomputable def completenessExperiment (stmt : Statement) (w : Secret) : ProbComp Bool :=
  runWithRandomPermutation do
    let (_, index) ← setupWith queryPermutation
    let coins ← sampleCoins
    match ← prover queryPermutation stmt w coins with
    | none => return false
    | some proof => verifier queryPermutation index stmt proof

def Completeness (δ : ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
    Pr{let v ← completenessExperiment stmt w}[v = false] ≤ δ

noncomputable def realExperiment (stmt : Statement) (w : Secret) (D : Distinguisher) :
    ProbComp Bool :=
  runWithRandomPermutation do
    let coins ← sampleCoins
    D (← prover queryPermutation stmt w coins)

def idealExperimentWith {S : Type} (s₀ : S) (sim : Statement → StateT S ProbComp (Option Proof))
    (simOracle : QueryImpl RandomPermutationOracles (StateT S ProbComp)) (stmt : Statement)
    (D : Distinguisher) : ProbComp Bool :=
  (do
    let proof ← sim stmt
    simulateQ simOracle (D proof)).run' s₀

def ZeroKnowledgeWith {S : Type} (s₀ : S) (sim : Statement → StateT S ProbComp (Option Proof))
    (simOracle : QueryImpl RandomPermutationOracles (StateT S ProbComp)) (ζ : ℕ → ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
  ∀ (D : Distinguisher) (Q : ℕ), (∀ proof, QueryCostAtMost (D proof) permutationCallCost Q) →
    Pr{let b ← realExperiment stmt w D}[b = true] ≤
        Pr{let b ← idealExperimentWith s₀ sim simOracle stmt D}[b = true] + ζ Q ∧
      Pr{let b ← idealExperimentWith s₀ sim simOracle stmt D}[b = true] ≤
        Pr{let b ← realExperiment stmt w D}[b = true] + ζ Q

def StatementBinds : Prop :=
  ∀ w w' : Secret, w.statement = w'.statement →
    w.x = w'.x ∨ PairCollision (w.x, Vector.replicate 32 yPad) (w'.x, Vector.replicate 32 yPad)
```

`Adversary` is `Commitment → OracleComp RandomPermutationOracles (Statement × Proof)`: given the setup's
commitment (the circuit's root and out-of-domain answer; it could recompute it with `π`), with coins, `π` and
`π⁻¹`;
`Distinguisher` is `Option Proof → OracleComp RandomPermutationOracles Bool`, quantified after the
statement and the witness (non-adaptive zero knowledge). **Zero knowledge is for one proof**:
`realExperiment` starts from an empty, lazily sampled `π`, the prover goes first, and the distinguisher
queries `π` and `π⁻¹` only after it has the proof. Not covered: oracle queries before the proof (a
distinguisher's precomputation or auxiliary input that depends on `π`), and several proofs under one `π`.
`sampleCoins` is the prover's coins (`Coins`): twelve mask words, the sixteen random rows' values and the
twenty-four blinding words of `h`, each uniform in `K`, in the order the Rust's KDF derives them.
`QueryCostAtMost`, `permutationCallCost`, `runWithRandomPermutation`, `loggedOracles`, `queryPermutation`
are mumbai's (`RandomPermutation.lean`). `PairCollision a b` is `a ≠ b ∧ pair a.1 a.2 = pair b.1 b.2`.

**Knowledge soundness needs no collision clause**: an extracted secret satisfies the relation exactly (the
circuit computes the deployed Keccak-256). `StatementBinds` is the clause a consumer needs who reads from a
statement that `y` names one `x`; it holds outright (it is a pigeonhole on `y`'s preimages), and is not
proved in Lean.

**The bounds are parameters**, `ε`, `δ`, `ζ` (a statement at `ε = 1` says nothing). The end theorems fix
them:

* `ε = Soundness.ksBound` (`formal/EndToEnd/Soundness/PcsFinal.lean`, the EIP's PCS claims):
  `ksBound Q = SoundPcs.deployedBound (2^20 + 24 + Q) + (5 · 2^19 + 24 + Q + 728890)² / 2^508`, `deployedBound`
  the six openings' terms `openingBound x = (x + 10122)(2^-128 + 5 (x + 10122) / 2^256)` (F2's term for one
  opening), the binding of the four roots' lists at their out-of-domain points (`N · (δc 25 + δc 27 + δc 28)` and
  three `N (N + 1) / 2^256`), and the chain `N (2^-164 + 8 N / 2^256)`, `N` the run's Keccak-256 queries; the
  constants count the setup's and the verifier's own calls. About `2^-104.4` at `Q = 0`, `2^-85.4` at `2^40`,
  `2^-61.4` at `2^64`.
* `δ = E2ECompleteness.Pcs.deltaPcs = (19 · 2^24 + 31)/2^192 + 2^-304 + (2^48)²/2^508`, about `2^-163.75`
  (`deltaPcs_lt`: `< 2^-163`; `formal/EndToEnd/Completeness/E2ECompleteness/PcsEnd.lean`): degenerate challenges
  `(α, β, t, ρ)` (`2^-163.75`), the six openings' proofs of work (`2^-304`), the permutation as two random oracles
  (`2^-412`).
* `ζ Q = εpcs Q + εr + εfs₀` (`formal/EndToEnd/ZK/PcsFSClosed.lean`): `εpcs` and `εr` the two hypotheses'
  errors (`PcsZeroKnowledge sim εpcs`, `RevealedUniform εr`), `εfs₀ ≤ 2^-162` (`εfs₀_le`) the distance of the
  simulator's `113` Fiat–Shamir challenges from uniform, proved.

## The extractor

`extractor stmt setupEvals T proof` (`Security.lean`) is `transcriptExtractorFor (membership logRows)`
(`Extractor.lean`). **The extractor reads the adversary's transcript and the public setup's tree**: the
statement, the proof's first two scalars (the witness table's root), the adversary's transcript `T`, and
the Keccak-256 evaluations of the circuit commitment's Merkle tree (`setupEvals = Tree.evaluations tree`,
a pure function of the tree the setup computed: each leaf's bytes and each node's two children with
their digests), and nothing else: it neither queries `π`, nor sees the verifier's queries, nor runs the
adversary again. (The setup is public; reading its tree lets the extractor climb a witness tree that
reuses the commitment's nodes, which the composed proof in `formal/Compose` needs: its extractor reads
the setup's and the adversary's queries.) From `T`'s forward queries it replays the Keccak-256
evaluations whose whole sponge path the adversary queried, as mumbai's `keccakEvaluationsOfTranscript`
does but with hash maps, keeping those of the two input lengths the witness tree hashes (64 and 512 bytes,
`Replay.transcriptEvaluations`); it indexes the setup's and those evaluations (`Replay.preimageIndex`: each
input's first answer, then a digest and a length to the inputs it answers) and inverts the witness table's
Merkle tree under the root (`Replay.leavesUnder`, mumbai's `committedLeaves` read off the index: `2^20`
leaves of `64` words, each of its `64` lanes a Reed–Solomon word of `n = 2^20` symbols for messages of
`k = 2^19`). It decodes the word in three stages, each run only if the stages before give no witness:

1. **the fast path** (mumbai's `fastStacks`): each lane interpolated from its first `2^19` columns, for a
   word without errors there (an honest proof's);
2. **the unique decoder** (`UniqueDecoding.uniqueStacks`, `Decoder.lean`): Gao's decoder on each lane, which
   recovers the lane's polynomial whenever at most `⌊(n − k)/2⌋ = 2^18` of its columns are wrong, so the
   stack whenever the word agrees with the stack's encoding on at least `(n + k)/2 = 786432` columns;
3. **the list decoder** (mumbai's `decodeStacks`): every stack whose encoding agrees with the word on at
   least the Johnson threshold (`741549` columns), CompPoly's Guruswami–Sudan list decoder over `K` lane by
   lane with prefix pruning (at most `2^18` candidates).

A candidate stack **is** the witness table (a PCS commitment commits the table as it is): the extractor takes
its first `2^m` entries, the cells' polynomial, to the cells' values (`Domain.values`), reads the input rows'
`V` cells as bits, and returns the first candidate's secret that satisfies the relation.

**Its cost** (`Extractor.lean`'s table; read off its loops, not proved), in operations of `K`, `Q` the
transcript's queries, `N` the evaluations read (the setup's `2^20 − 1` and the transcript's):

| Step | Cost |
| --- | --- |
| replay and evaluations | `Q` steps of `O(1)` expected hash-map operations on `200`-byte states, at most `680` bytes copied each; at most two paddings of at most `544` bytes compared per chain |
| index and inversion | `N` insertions keyed by inputs of at most `512` bytes and `N` by digests; `2^20 − 1` node and `2^20` leaf lookups |
| fast path | `64` inverse transforms of `2^19` and forward of `2^20`: about `2^31.4` |
| unique decoder, if the fast path gives no witness | about `2^28.3` per lane plus about `2^21.5` per wrong column of the lane (Gao's Euclid stops after `deg v ≤ e` divisions): about `2^34.3` for a word with few wrong columns, at most `2^45.7` |
| list decoder, if neither gives a witness | multiplicity `1149`, `Y`-degree `1625`, `2^39.3` interpolation conditions per lane; Mulders–Storjohann's reduction `(ℓ+1)³(m'n)² ≈ 2^92.3` per lane (`2^98.3` for the `64`), then Roth–Ruckenstein: infeasible |
| per candidate | one transform of `2^24`, `33` Keccak-256 |

**The list decoder is the worst case only**: it runs only on a word whose every witness stack's encoding
agrees with it on fewer than `786432` of its `2^20` columns (beyond the unique-decoding radius, within the
Johnson radius); an honest proof's word takes the fast path, a word with a few wrong leaves the unique
decoder. That the unique decoder recovers every word within its radius is Gao's theorem, tested
(`PcsQuotientTest/Decoder.lean`) and not proved here; the soundness proof does not need it.

## The simulator

**Zero knowledge assumes a zero-knowledge PCS** (`Zk.lean`, `docs/membership/HIDING.md`): a commitment's root and
an opening reveal nothing beyond the commitment's out-of-domain answer and the claim, and the protocol makes
everything else it reveals uniform with its randomness (the masks, the random rows, the blinding of `h`). The
deployed openings, leanVM's WHIR, are not zero-knowledge: this is a statement about the protocol over an ideal
PCS.

* **A PCS simulator** (`PcsSimulator`): its own state (`Aux`, from `aux₀`) and an opening simulator `simOpen`,
  which sees only the commitment and the claim and may read and program the permutation's edges. Its oracle
  (`PcsSimulator.oracle`) is mumbai's lazily sampled permutation on the state's edges (`edgeOracle`), programmed
  only where `simOpen` writes.
* **The ideal PCS** (`PcsSimulator.idealPcs`): a commitment's root uniform and independent of the table, its
  out-of-domain answer the table's polynomial at the root's point (`oodPointWith` over the simulator's
  permutation), an opening the opening simulator's. **The hybrid experiment** (`hybridExperiment`): the honest
  prover with the witness, its four secret tables committed and opened by the ideal PCS (`proveWithPcs`), the
  circuit's commitment and the wiring opening real.
* **`PcsZeroKnowledge sim εpcs`**: the real experiment and the hybrid differ by at most `εpcs Q` for a
  distinguisher of `Q` calls.
* **`RevealedUniform εr`**: for every witness, outside a set of challenge tuples (`Challenges`: the four
  out-of-domain points and `α, β, γ, t, ρ`) of probability at most `εr`, the ten revealed scalars (`revealed`: the
  four out-of-domain answers, the four `a_j`, `Q`'s and `G`'s values) are uniform when the prover's randomness is
  (`HIDING.md`'s rank conditions). Not proved: the Rust tests the rank conditions (`hiding.rs`).
* **The simulator** (`zkSimulator sim`) reads the statement, never the witness. Its challenge phase
  (`challengePhase` with `uniformReveal`) commits to the circuit (real, public), draws each secret root uniformly
  and computes its out-of-domain point with the model's permutation, draws each revealed scalar uniformly where the
  prover computes it, and runs the reduction's chain on them, `next` the public wiring value (`wiringValue`); then
  `finishOpenings` opens the wiring claim with the real WHIR prover (public table) and the five secret claims with
  `simOpen`. Its cost is the circuit's commitment, four uniform roots and their out-of-domain points, ten
  uniform elements, the chain, one WHIR opening of the public wiring table, and the PCS simulator's five openings.
* **`FiatShamirUniform εfs`**: in the simulator's challenge phase the challenges are within `εfs` of uniform
  (`sampleChallenges`) on every event; a property of the model and the transcript's encoding, **proved** at
  `εfs₀ ≤ 2^-162` (`fiatShamirUniform_closed`, `formal/EndToEnd/ZK/PcsFSClosed.lean`).

The end theorems: `PcsQuotient.EndToEnd.zeroKnowledge_pcs` (`formal/EndToEnd/ZK/PcsEnd.lean`) under the three
propositions, `ζ Q = εpcs Q + εr + εfs`; **`zeroKnowledge_pcs_closed`** under `PcsZeroKnowledge` and
`RevealedUniform` only, `ζ Q = εpcs Q + εr + εfs₀`. A PCS simulator with an oracle of its own (an
indifferentiability simulator answering fresh queries specially, say) is not covered: the simulator's oracle is
the model's permutation, which `simOpen` may only program.

## What is assumed, and what remains

**Trusted**, as in mumbai: the Lean kernel; mumbai's definitions this package reuses (Keccak-256, the
model, `verifyStackedOpening` as leanVM's WHIR verifier, its prover's pieces, its extractor's decoder;
mumbai tests its verifier against leanVM's on mutated proofs); that the deployed Keccak-f[1600] behaves
as a random permutation. **Tested, not proved**, that these definitions are the Rust: the differential
test (below). The test checks the constants' properties by compiled evaluation (`native_decide`); the proofs
check the ones they use by kernel evaluation (`isCantor_statementConsts`,
`formal/EndToEnd/Bridge/Claims/Constants.lean`; `rowVanishing_24_lanes`, `Bridge/Claims/Tau.lean`;
`rowVanishingProperty`, `formal/EndToEnd/Completeness/E2ECompleteness/PcsConstants.lean`).

**Deviations from the Rust**, each documented where it is:

* The WHIR proofs are in mumbai's format, one full Merkle path per query (the raw form of
  `verifier::MerkleOpenings`); the Rust prover ships pruned paths, which the Rust verifier expands. The
  expansion is not formalized (as in mumbai).
* The reduction's proof is a structure of nineteen scalars rather than a stream (`ReductionProof.ofStream`
  reads one); a stream of another length, or a root that is not two halves (rejected by the Rust), is no proof.
* The verifier inverts its denominators one by one after checking that none is zero; the Rust inverts
  their product by the norm to `K` (same values). The target `Σ_J γ^J word_J` is a fold over
  `statementWords`; the Rust writes it out (same value).
* The statement's prover takes its randomness uniform (`sampleCoins`); the deployed prover derives the same
  words from a fresh 32-byte seed by a Keccak-256 key derivation only (`Randomness::derive`, `protocol.rs`: a key
  binding the seed, the label and a digest of the cells, then the words of Keccak-256(tag ‖ key ‖ k)), so deployed
  zero knowledge is computational in that derivation; the test hands the Lean prover the Rust's derived words (`Q`).
* The EVM contract (`crates/membership/evm`) computes the reduction and checks its claims declared; F5 and
  `formal/EndToEnd/Evm` prove that its recorded graph accepts exactly when `verifyWith` does
  (`evm_accepts_iff_verifyWith`), with what the block proves of a claim an explicit definition (`pcsOpen`).

**What is proved** (`formal/README.md`, "End-to-end theorems"; each on `propext`, `Classical.choice`,
`Quot.sound`):

* `KnowledgeSoundness Soundness.ksBound`: **proved, no hypotheses** (`Soundness.knowledgeSoundness`,
  `formal/EndToEnd/Soundness/PcsFinal.lean`), from the circuit (F0: `membership`'s satisfying assignments are its
  computation of Keccak-256 membership, with its random rows; the embedding `statementWords`), the reduction's
  round-by-round soundness (F1), the PCS opening's soundness and the binding of each root's list at its
  out-of-domain point (F2, `formal/WhirBridge`: `pcs_sound_oracle`, `ood_binding_coords`), the composition in the
  model with extraction from the transcript (F4, `formal/Compose`, `formal/ComposePcs`, `formal/SoundPcs`:
  `knowledgeSoundness_deployed_pcs`), and the bridges from these definitions to the layers'
  (`formal/EndToEnd/Bridge`, `formal/EndToEnd/PcsBridge`). Stand-alone knowledge soundness, not
  simulation-extractability.
* `Completeness E2ECompleteness.Pcs.deltaPcs`: **proved, no hypotheses** (`E2ECompleteness.completeness_end`,
  `formal/EndToEnd/Completeness/E2ECompleteness/PcsDone.lean`): the honest parts are F1's blinded honest second
  message and the six claims hold, its PCS openings are accepted (mumbai's completeness of its WHIR prover), with
  the proofs of work, the four challenges in the random-oracle model, and the transfer from the permutation. It is
  about this package's `prover`, which the differential test compares with the Rust prover only on the
  reduction's stream at `2^17` rows (`Q`, below): the deployed Rust prover is trusted for completeness.
* `ZeroKnowledgeWith sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + εr + εfs₀)`: **proved under two
  hypotheses**, `PcsZeroKnowledge sim εpcs` and `RevealedUniform εr` (`PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed`,
  `formal/EndToEnd/ZK/PcsFSClosed.lean`; "The simulator", above). Single-proof zero knowledge: from an empty `π`,
  the distinguisher's queries after the proof; no query before the proof and no second proof under the same `π`.
  The structure `Theorems` (`Security.lean`) holds the other two and `StatementBinds`.
* Scope: the three are about `verifyWith` in the random-permutation model; the EVM theorem below holds at the
  real Keccak-f[1600]. They do not formally compose: a probability over a random permutation does not transfer
  to a fixed hash.
* `StatementBinds`: a pigeonhole, immediate; not proved in Lean.
* The EVM contract: `formal/EndToEnd/Evm` (`evm_accepts_iff_verifyWith`, `evm_accepts_iff_exists`); the
  bytecode equal to the recorded graph, and what the block proves of a declared claim (`pcs_claim::verify`) equal
  to `pcsOpening`, by tests.

## Building and testing

On a machine with the dependencies (Mathlib and the rest at mumbai's revisions):

```sh
lake build                                   # the statement: PcsQuotient
lake build PcsQuotientTest differential      # the constants' properties, the unique decoder's
                                             # and the hash-map inversion's tests, the test

# vectors from the Rust (from the repository root): reductions, whole proofs (honest and tampered),
# circuit commitments, the honest prover's streams; --index adds the membership circuit's commitment,
# --full also its whole proofs
cargo run --release -p quotient --example statement_vectors -- vectors.txt --index
.lake/build/bin/differential vectors.txt     # Lean's verdicts, claims, commitments and streams vs Rust's
.lake/build/bin/differential --self-test     # the extractor's inversion and decoding
```

The test (`PcsQuotientTest/Differential.lean`) checks, line by line: on random nineteen-scalar streams at
`2^12` to `2^23` rows (some of other lengths, some with a root that is not two halves, some at sizes the
commitments do not take) and on honest streams, that `reduce` gives the Rust's four commitments and six claims
or rejects as it does (`R`); on whole proofs of a small circuit (`2^17` rows), honest and tampered seventeen ways
(values, roots and out-of-domain answers, the statement, the circuit commitment, WHIR scalars, a truncated or
extended stream, leaves, siblings, missing, extra and short paths), that `verify` gives the Rust's verdict on the
six openings in their raw form (`P`); that the Lean builder and commitment give the Rust circuits' sizes, inputs
and commitments (root, out-of-domain answer), the membership circuit's at `2^22` rows included with `--index`
(`I`); and that the Lean prover, given the Rust prover's input bits and derived randomness (masks, random rows,
blinding), sends the Rust prover's reduction stream and its whole proof is accepted by the Lean verifier (`Q`, at
`2^17` rows on small circuits: the openings are not compared with the Rust's, and the check was not run at
`2^22`). `--self-test` runs the extractor's Merkle inversion through a transcript (a small tree: mumbai's replay
is quadratic) and its fast-path decoding of an honest witness table back to the input bits.
