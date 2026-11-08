<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The structure follows formal/UniStatement/README.md. -->

# UniKeccak: the univariate verifier for the Keccak VM

The Keccak VM (`crates/leanvm_univariate/KECCAK.md`, `formal/KeccakVm`) is leanVM 42422001 with `BLAKE2S` replaced
by leanVM `9d50c92a3`'s `SHA3`. This library holds:

- **its verifier as computable Lean**, `reduce` with `Blake2s::Keccak(variant)` of `crates/leanvm_univariate/src/
  verifier.rs`, for the main line (`KECCAK_MAIN`) and π1-rec3's shape (`KECCAK_REC3`), with the contract's IV and its
  three `PCS_OPEN` calls (`contract.rs`);
- **the end statements**, against the Keccak VM's relation `KeccakVm.KvHolds F`: knowledge soundness and completeness
  of the main line and of π1-rec3's shape. `F : KeccakVm.KeccakFlockSpec` (the Keccak-f block) is a parameter.

The statements are not proved. There is no `sorry` and no `native_decide`. The root's guards (`UniKeccak.lean`) check
that the verifier and every statement rest on Lean's three axioms.

It is a library of `formal/EndToEnd` (`UniKeccak`, `srcDir = "../UniKeccak"`, `warningAsError`). It reuses
`UniStatement` (its verifier's unchanged steps, `Rec.lean`'s Fiat–Shamir shapes, `KeccakTables.lean`'s tables, the
openings, the model) and `KeccakVm` (the relation).

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only, with formal/leanervm linked
systemd-run --scope -p MemoryMax=10G lake build UniKeccak         # the library; #guard_msgs checks the axioms
# the vectors (from the repository root, on the Mac; an absolute path: cargo runs tests in the crate's directory)
KECCAK_VECTORS_OUT=$PWD/keccak_vectors.txt cargo test --release -p leanvm_univariate --test lean_keccak_vectors -- --ignored --nocapture
KECCAK_VECTORS=<path>/keccak_vectors.txt lake env lean ../UniKeccak/UniKeccakTest/Runner.lean   # the runner
```

## Reading order

1. [`Terminal.lean`](UniKeccak/Terminal.lean): the Keccak-f block's structured lincheck terminal
   (`keccak_flock::structured_terminal`, `structuredTerminal`), with its constants (`rc`, `rho`, `source`,
   `shiftOffsets`, `grouped`, `constantColumn`).
2. [`Walk.lean`](UniKeccak/Walk.lean): the block's forward walk (`keccak_flock::row_values`, `keccakRowValues`) and
   the walked terminal on it (`walkedTerminalK`), the structured terminal's reference. The verifier does not use them.
3. [`Verifier.lean`](UniKeccak/Verifier.lean): the variant (`KeccakVariant`, `keccakMain`, `keccakRec3`), Flock on the
   Keccak-f block (`frontK`, `verifyWalkedK`), `Q_W` with the lanes' copies (`constraintRelationK`), the stacks
   (`layoutsK`, `Shape.c2ColumnsK`, `layoutsOfK`), a claim's weight (`weightAtK`), the batch (`batchK`), and
   **`reduceWithK`**, `runWithK`, `runK`.
4. [`Opening.lean`](UniKeccak/Opening.lean): the variant's bytes (`variantBytesK`), the layout words
   (`layoutWordsK`), the contract's IV (`contractIvKWith`, `contractIvK`), the calls (`pcsCallsK`), a proof
   (`KeccakProof`), **`verifyWithK`** (the run, then three calls), the measured shapes (`keccakRuns`, `keccak400`).
5. [`Mapping.lean`](UniKeccak/Mapping.lean): **`C1` read as the Keccak VM's stack** (`kvColumn`, `kvStack`), the
   setup's table (`setupStackK`), and what the verifier fixes of the block (`KeccakFlockFits`).
6. [`Security.lean`](UniKeccak/Security.lean): the deployment (`KDeployment`), the setup (`setupTreeKWith`), the
   extractor (`uniExtractorK`), the experiments, **`UniKnowledgeSoundnessKeccak`**,
   **`UniKnowledgeSoundnessKeccakRec3`**, **`UniCompletenessKeccak`**, **`UniCompletenessKeccakRec3`**.

## Rust → Lean

| Rust (`crates/leanvm_univariate`, `crates/leanvm_flock_gas`, working tree of 2026-11-08) | Lean (`UniKeccak.`) |
|---|---|
| `keccak_flock.rs`: `structured_terminal`, `shift_offsets`, `grouped`, `RC`, `RHO`, `SOURCE`, `CONSTANT_COLUMN`, `X_QUAD` | `structuredTerminal`, `shiftOffsets`, `grouped`, `rc`, `rho`, `source`, `constantColumn`, `xQuad` |
| `keccak_flock.rs`: `row_values`, `t_word`; `flock_min.rs`: `walked_terminal_with::<S, KeccakWalked>`, `known_weights_with` | `keccakRowValues`, `tWord`, `walkedTerminalK` |
| `flock_min.rs`: `front_with(log_n, variant, 17)`, `verify_walked_with::<S, Keccak>` | `frontK`, `verifyWalkedK` (the zerocheck `Flock.zerocheckFs`, the ring switch `Flock.ringEnd`: `UniStatement`'s) |
| `verifier.rs`: `Blake2s::Keccak(variant)`, `KECCAK_MAIN`, `KECCAK_REC3` | `KeccakVariant` (skip, Fiat–Shamir shape; slices `TowerWalk`), `keccakMain`, `keccakRec3` |
| `verifier.rs`: `reduce` with `Blake2s::Keccak` | `reduceWithK` (steps 0, 4, 6 `UniStatement`'s `countBits`, `tablePart`, `heapRelations`; α by `drawRun`) |
| `verifier.rs`: step 5 with `qflock_slot(true, ·)`, `keccak_slot_offset` | `constraintRelationK` (`keccakSlot`, `keccakSlotOffset` of `UniStatement/KeccakTables.lean`) |
| `verifier.rs`: `vm_tables(true)`, `qflock_row_bits(true)`, `stack_layouts_for(·, ·, true)`, `layouts_for(·, Keccak)` | `tablesKeccak`, `qflockRowBits`, `layoutsK`, `layoutsOfK` (`C2`'s columns `Shape.c2ColumnsK`) |
| `verifier.rs`: `weight_at` (slot bits `= q_flock`'s variables − the point's) | `weightAtK` |
| `verifier.rs`: `batch` (no pending matrices, no bit-slice claim) | `batchK` (rounds as `UniStatement.batchFs`: `sumcheckDrawn`, `sumcheckPairsDrawn`) |
| `contract.rs`: `rust_verifier_with` | `runWithK`, `runK` |
| `contract.rs`: `variant_bytes(Keccak)`, `layout_words_for(·, Keccak)`, `contract_iv_for(·, Keccak, ·, ·)`, `calls` | `variantBytesK`, `layoutWordsK`, `contractIvKWith`/`contractIvK`, `pcsCallsK` |
| the Keccak contract's three calls (`C1`, `C2`, setup) | `verifyWithK` |
| `tests/keccak_vm.rs`: `KECCAK_RUNS`, `KECCAK_LOG_BYTECODE`; `leanvm_rec/tests/keccak_vm_rec.rs`: `KECCAK_400` | `keccakRuns`, `keccakLogBytecode`, `keccakShapeOf`, `keccakShapeNamed`, `keccak400` |

**Deviations**, none changing a value:

- The variant is the skip and the Fiat–Shamir shape. The Rust's `Variant` also has `slices`, which `Blake2s::Keccak`
  asserts is `TowerWalk`; Lean leaves it out.
- The batch has no pending matrices and no bit-slice claim, the arguments the Rust passes as `None` here.
- The ring switch's end is always `End::Ring`, so the `End::Combination` arm of step 7, which the Keccak verifier
  never reaches, adds nothing.
- `structuredTerminal` computes the 40 correlations directly, where the Rust memoises the partial correlations
  (`partial`). Its sums are in list order, where the Rust's `S::sum` sums are in iterator order. Field arithmetic
  is exact, so the values are the same.
- The rest is `UniStatement`'s deviations: lists for vectors, `0` on an out-of-range read where the Rust would panic,
  `ℕ` degrees saturating as `degree` does, no `EqCache`.

## What is tested

`UniKeccakTest/Runner.lean`, run with `lake env lean` (the interpreter on the compiled definitions, not the kernel),
reads the vectors of `crates/leanvm_univariate/tests/lean_keccak_vectors.rs`:

- **14 terminal vectors**: `structuredTerminal` on random inputs at every skip `0..6` (two each), against the Rust's
  `structured_terminal`. The writer also asserts that it equals the walked terminal
  (`walked_terminal_with::<KeccakWalked>`). Lean's walk (`walkedTerminalK`) is checked against the Rust's walked
  terminal. A control checks that another `α` changes the value.
- **74 verifier vectors**:
  - the main line at 32 signatures in both claim modes (point and weighted), the main line at 400 signatures, and
    π1-rec3's shape at 400 and at 32 signatures. Each has 15 vectors: 2 random streams, 2 accepting streams (one
    under another program IV), 2 accepting streams announcing other row counts that fit (none, one, `leastRows`, a
    full table, `2^h − 1`, random), 1 count out of range, 3 mutations, 1 truncated stream and 1 extended stream;
  - the main line at 128 and 1,000 signatures: random, accepting and mutated streams;
  - **the two real Keccak proofs** (`tests/vectors/keccak.txt`, main line at 32 signatures; `keccak_rec3.txt`,
    π1-rec3 at 400 signatures), with the contract's `PCS_OPEN` inputs, and three mutations each. Their IV binds their
    own setup root `F` (`SETUPROOTS`, as `tests/evm_vectors.rs` builds their contract).
- On every vector, the Lean and the Rust agree on **every value**: the result (and its error), every challenge
  (narrow ones as drawn), every value required to be zero (the counts' range checks, Flock's structured terminal,
  the batch's terminal), the verdict, the number of relations, each stack's variables, every opening (point claims:
  point and value; weighted claims: points, terms in order, value, relations), no matrices; the row counts the stream
  announces; the five Keccak layout words; the Keccak contract's IV (`contractIvK` of the program's IV and the
  vector's roots); the run's layouts are `layoutsOfK` of the shape. On the real proofs, **every `PCS_OPEN` input the
  contract calls with**, word for word (`pcsCallsK`).
- Self-tests: every Keccak run's shape is valid; `C1` holds `q_flock` at `h_SHA3 + 11` variables and the `SHA3`
  table's 86 columns; `source` is a permutation of the lanes with `rho`'s rotations; there are 40 shift offsets;
  `C1` is `2^28` words at 400 signatures.

**Results** (h1, 2026-11-08, on the Rust working tree of that day):
- **74/74 vectors agree on every value**: 26 accepted by both and 48 rejected by both. By kind (accepted/rejected):
  accept 12/0, counts 10/0, badcount 0/5, random 0/12, mutate 2/15, truncate 0/5, extend 0/5, real 2/0, real-mutate
  0/6. The two accepted mutations are weighted-mode streams mutated after the last check: weighted mode collects no
  batch terminal, so only `PCS_OPEN` would reject them.
- 14/14 terminal vectors agree: the structured terminal, the Rust's walk and Lean's walk.
- All 6 self-tests hold.
- The vectors take 428 s; the whole run takes about 30 minutes, most of it the 14 Lean walks of the `2^17`-position
  block in the interpreter.

**Defined, not tested**: `PCS_OPEN`'s WHIR (the Rust has only a mock), the setup's commitment, `kvColumn`/`kvStack`,
`setupStackK`, the extractor, the experiments, the Props. `verifyWithK`'s run and calls are the tested `runK` and
`pcsCallsK`'s claims.

## The statements (`Security.lean`)

```lean
structure KDeployment where
  prog : KeccakVm.Program
  shape : Shape
  programIv : List UInt8
  a0Root : Digest
  b0Root : Digest
  valid : shape.Valid
  logBytecode_eq : shape.logBytecode = prog.logSize

def KDeployment.Relation (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (rows : List ℕ)
    (input : Vector UInt8 32) (q : D.Stack rows) : Prop :=
  KeccakVm.KvHolds F D.prog (D.sizes rows) (publicInputOf input.toList) q

noncomputable def keccakSoundnessExperiment (D : KDeployment) (v : KeccakVariant) (A : KAdversary) :
    ProbComp KOutcome :=
  runWithRandomPermutation do
    let tree ← setupTreeKWith queryPermutation D
    let roots := D.setupRoots tree
    let (z, transcript) ← (simulateQ loggedOracles (A roots)).run []
    let accepted ← D.verifierWith queryPermutation v roots z.1 z.2
    return ((z, accepted), PcsQuotient.Tree.evaluations tree, transcript)

def UniKnowledgeSoundnessKeccakWith (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (v : KeccakVariant)
    (ext : KExtractor D) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : KAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← keccakSoundnessExperiment D v A}[KBreaksKnowledgeSoundness F D ext z] ≤ ε Q

def UniKnowledgeSoundnessKeccak (F) (D) (ε) : Prop := UniKnowledgeSoundnessKeccakWith F D keccakMain (uniExtractorK F D) ε
def UniKnowledgeSoundnessKeccakRec3 (F) (D) (ε) : Prop := UniKnowledgeSoundnessKeccakWith F D keccakRec3 (uniExtractorK F D) ε

def UniCompletenessKeccakWith (F) (D) (v) (P : KProver D) (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation F rows input q →
    Pr{let b ← keccakCompletenessExperiment D v P input rows q}[b = false] ≤ δ
def UniCompletenessKeccak (F) (D) (P) (δ) : Prop := UniCompletenessKeccakWith F D keccakMain P δ
def UniCompletenessKeccakRec3 (F) (D) (P) (δ) : Prop := UniCompletenessKeccakWith F D keccakRec3 P δ
```

- `KAdversary := SetupRoots → OracleComp RandomPermutationOracles (Vector UInt8 32 × KeccakProof)`.
- `KeccakProof` is the stream and three opening proofs (`C1`, `C2`, the setup).
- `D.Stack rows := Column (keccakIsaμ D.prog (D.sizes rows))`, and `D.HonestRelation F` is `KvHonest F`.
- **The setup** is one WHIR commitment, of `setupStackK`. `A0`, `B0` are not committed: their roots `a0Root`,
  `b0Root` are deployment constants that the contract's IV hashes, because `contract_iv_for` keeps the BLAKE2s
  preimage. The verifier never opens them.
- **The extractor** `uniExtractorK F` is `uniExtractor` on the Keccak `C1` (`c1LayoutK`, `2^μ` words), each candidate
  read as the Keccak VM's stack (`kvStack`), the first satisfying `KvHolds F`. `KvHolds` is decidable, so the
  extractor is computable for a computable `F`.
- **`F` is a parameter.** The verifier fixes some of `F`'s fields: the port words `4l + 2` and `4l`, and the
  constant wire `64`. `KeccakFlockFits F` states this. The block's R1CS is the one whose lincheck terminal
  `structuredTerminal` computes; no Lean R1CS of the block is used here. An end theorem would be about `F`'s
  inhabitant, with `KeccakFlockFits` and the terminal's identity as its lemmas.

**The map** (`Mapping.lean`). `C1`'s `memory k`, `bytecodeFinal` and `table t i` are the Keccak VM's columns in basis
`B`. Every `SHA3` column is committed, the 50 lanes included, so no column of the Keccak VM is read off `QFLOCK`,
unlike Lv42's `BLAKE2S` limbs. `qflock` holds values: the Keccak VM's block `x` (cells `w + 2^11 x`) is `C1`'s block
`rowPosition x`. Rows follow `rowPosition`, as in `UniStatement`. `inverse t` has no counterpart. `Q_W`'s copy
identities are what `KeccakAux`'s copy clause states.

## Needed changes outside this library (reported, not made)

- `UniStatement.weightAt` fixes a slot term's bits at 8. The Rust reads them as `q_flock`'s variables minus the point's.
  `weightAtK` is the Rust's; `UniStatement` could take it, and then `batchFs` would serve both VMs.
- `UniStatement.Flock.front` and `zerocheckFs` take the lincheck's rounds from BLAKE2s's `lincheckRounds`. A
  parameter there would make `frontK` unnecessary.
- `contract_iv_for(·, Keccak, ·, ·)` hashes the `A0`, `B0` roots and their layout words, which the Keccak contract
  never uses (`KDeployment.a0Root`, `b0Root`). Dropping them would be a Rust change, and the vectors would change too.
- `KECCAK.md` says there is no Keccak prover. The real proofs of `tests/vectors/keccak*.txt` exist, so it is out of
  date.

## What remains

- **Proofs**: the statements' soundness and completeness. They need:
  - the Keccak-f block's inhabitant of `KeccakFlockSpec` and `KeccakFlockFits` for it (`formal/KeccakFlock`);
  - the structured terminal's identity with the block's matrices' sum;
  - `UniSound`'s and `UniComplete`'s layers redone on the Keccak tables (11 slot bits, the `END_BIT` constant in
    `Q_W`, three openings);
  - the Keccak VM's arithmetization (`formal/KeccakArith`).
