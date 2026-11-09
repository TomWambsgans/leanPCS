<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The structure follows formal/Statement/README.md. -->

# UniStatement

The univariate PIOP's verifier (`crates/leanvm/univariate`, `docs/leanvm/univariate/SPEC.md`) as computable Lean: the
transcript, the domain, the tables, the heap, the claims, Flock's verifier, the stacks, the batch, the shape class,
the run on calldata, `PCS_OPEN` and the contract's IV, the commitments' encodings and the deployment. It was written
for leanVM 42422001 (iteration 2, `leanvm-univariate` `ad49e74`) and is now the shared part of the Keccak VM's
verifier: [`formal/UniKeccak`](../UniKeccak/README.md) instantiates it (the `Variant`, the `SHA3` table of
`KeccakTables.lean`) and states the end theorems against `KeccakVm.KvHolds`. No `sorry`, no
`native_decide`; the root's guards (`UniStatement.lean`) check the verifier's axioms.

It is a library of `formal/EndToEnd` (`UniStatement`, `srcDir = "../UniStatement"`), sharing that workspace's built
`lean_vm` packages (leanerVM `6175f1a0`), `Lv42` and `PcsQuotient` (`formal/Statement`), whose definitions it reuses:
`K`, `E`, Keccak-256 over a permutation, the random-permutation model, the WHIR opening (`PcsQuotient.openingWith`)
and commitment (`commitWith`), Merkle inversion and decoders.

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=10G lake build UniStatement        # the library; the axiom guards
lake env lean ../UniStatement/UniStatementTest/KeccakTables.lean    # the Keccak tables against the Rust's
```

## Reading order

1. [`Basic.lean`](UniStatement/Basic.lean): `E::new`, `E::pow`, `eq_kernel`, `multilinear_eval`, `poly_eval`,
   `Scalar::bits` (`intBits`).
2. [`Transcript.lean`](UniStatement/Transcript.lean): the contract's Keccak-256 chain over calldata
   (`KeccakChannel`), over a permutation `F` in any monad; the packed integers (`nextInteger`); `sumcheck`; the
   checks collected.
3. [`Domain.lean`](UniStatement/Domain.lean): the Cantor basis, the digits, the coordinate functionals, the
   vanishing polynomials, **the active rows at fixed cosets** and their `Z_act` from a count's bits.
4. [`TablesBase.lean`](UniStatement/TablesBase.lean), [`Tables.lean`](UniStatement/Tables.lean): the five shared tables,
   their flushes as `Form`s, their counters (the Keccak VM's sixth, `SHA3`, is item 16).
5. [`Heap.lean`](UniStatement/Heap.lean): the product heap's blocks.
6. [`Claims.lean`](UniStatement/Claims.lean): columns, relations, `combine` (the powers of `ρ`, the prefix merge).
7. [`FlockBase.lean`](UniStatement/FlockBase.lean), [`Flock.lean`](UniStatement/Flock.lean): Flock's verifier (`flock_min::verify`,
   `verify_deferred`, `Pending`), the ring map in tower order (`ring_tower.rs`), which `UniKeccak` runs on the Keccak-f
   block.
8. [`Stacks.lean`](UniStatement/Stacks.lean): the stacks' layouts and a claim's weight at a point (the ring-switch
   term by its map).
9. [`Batch.lean`](UniStatement/Batch.lean) (**swappable**): the batching sumcheck to point claims, with Flock's
   matrices' reduction as its `λ³` term.
10. [`Verifier.lean`](UniStatement/Verifier.lean): `Shape` (the shape class) and `Shape.validate`, `Shape.Valid`,
    `Shape.RowsFit`, the quotients' sizes from the shape (`Shape.c2Columns`, `layoutsOf`), and **`reduceWith`**,
    `verifier.rs`'s `reduce`.
11. [`Run.lean`](UniStatement/Run.lean): the run on calldata (`runWith`, `run`), the verdict, the row counts a
    stream announces (`rowsOf`, `rowsBytes`), the setup constants (the measured shapes, the program's IV).
12. [`Opening.lean`](UniStatement/Opening.lean): the layout words, the contract's IV (`contractIvWith`), the
    reference setup roots, `PCS_OPEN` as the Statement's opening and its inputs word for word (`pcsCalls`), and
    **`verifyWith`**, the whole verifier (the main line: the run, then five calls).
13. [`Mapping.lean`](UniStatement/Mapping.lean): basis `B` ↔ values, the rows' order (`rowPosition`), the setup's tables.
14. [`Security.lean`](UniStatement/Security.lean), [`RecSecurity.lean`](UniStatement/RecSecurity.lean): the deployment, the
    setup and its IV, `c1RootOf`, the adversary's types (the end statements are `UniKeccak`'s).
15. [`Rec.lean`](UniStatement/Rec.lean) (π1-rec3's Fiat–Shamir shape; not imported by `UniStatement.lean`):
    **`FsShape`** (`main`, `rec1`, `rec2`, `rec3`: the Rust's `Main`, `Rec`, `Rec2`, `Rec3`), the draws it changes
    (`drawRun`, `Flock.zerocheckFs`; `batchFs` with the narrow challenges `sampleNarrow` and the paired rounds
    `sumcheckPairsDrawn`, `pairPoint`, `cantorBeta1`), `main` the default, at which each is the original
    (`zerocheckFs_main`, `batchFs_main`). `UniKeccak` uses them at `.rec3` for the Keccak VM's π1-rec3 (`keccakRec3`).
16. [`KeccakTables.lean`](UniStatement/KeccakTables.lean) (the Keccak VM, `docs/leanvm/univariate/KECCAK.md`; not
    imported by `UniStatement.lean`): `tablesKeccak` (the `SHA3` table at opcode `5`: `sha3Columns`,
    `flushesSha3`, on `formal/KeccakVm`'s cell layout `KeccakVm.sha3CellLanes`), `keccakSlot`, `keccakSlotOffset`,
    `keccakR1csLogSize`. `UniStatementTest/KeccakTables.lean` checks every table, column, slot, offset and flush form
    against the Rust's `tables_keccak()` (`crates/leanvm/statement/tests/lean_keccak_tables.rs`). the `Variant`'s
    verifier is `formal/UniKeccak`'s.

## Rust → Lean

| Rust (`crates/leanvm/univariate` and `crates/leanvm/statement` at `ad49e74`) | Lean (`UniStatement.`) |
|---|---|
| `transcript.rs`: `KeccakChannel::{next_scalar, next_root, next_integer, sample, finish}`, `keccak_seed`, `challenge_of` | `nextScalar`, `nextRoot`, `nextInteger`, `sample`, `finish`, `seedWith`, `PcsQuotient.Transcript.challengeOf` |
| `transcript.rs`: `Checks::Collect`, `require_zero`; `scalar.rs`: `Scalar::bits` | `Chan.zeros`, `requireZero`; `intBits` |
| `transcript.rs`: `sumcheck`, `sumcheck_round_poly` | `sumcheck`, `roundPoly` |
| `multilinear.rs`: `eq_kernel`, `eq_eval`, `multilinear_eval`, `poly_eval`, `log2_ceil`, `dot` | `eqKernel`, `eqEval`, `multilinearEval`, `polyEval`, `log2Ceil`, `dot` |
| `domain.rs`: `beta`, `point`, `point_e`, `digits`, `coordinate_functionals`, `coordinates_at`, `prefix_vanishing`, `suffix_vanishing`, `vanishing_ratio`, `prefix_vanishing_from_bits`, `coset_offset`, `active_positions`, `is_active`, `active_vanishing_from_bits` | the same names in camel case |
| `layout.rs`: `Form`, `Flushes::{pair, state_derived, state_step, counted, bytecode, memory, memory_cols}`, `flushes_*`, `tables`, `count_columns`, `SEP_*` | `Form`, `Flushes.*`, `flushes*`, `tables`, `Table.countColumns`, `sep*` |
| `heap.rs`: `HeapLayout::new`, `Leaves`, `Block` | `HeapLayout.new`, `Leaves`, `Block` |
| `claims.rs`: `Commitment`, `Column` (and `id`), `Term`, `Relation`, `Combined`, `Relations::{push, equal, combine}` | the same; `combine` |
| `stacks.rs`: `StackLayout::{new, words, limbs}`, `EqCache::{row, row_from, selector}`, `limb_basis`; `verifier.rs`: `weight_at`, `RING_TWIST` | `StackLayout.new`, `words`, `limbs`, `rowEq`, `selector`, `limbBasis`, `weightAt` (no cache, no shared work; the same values), `ringTwist` |
| `flock_min.rs`: `verify`, `verify_deferred`, `front`, `ring_end`, `known_weights`, `Pending::{new, rounds, has_slices, terminal, combination}`, `zerocheck`, `row_low_weights`, `reduce_terminal`, `Variant`, `Slices` (with `Tower`), `End` | `Flock.verify`, `Flock.verifyDeferred`, `Flock.front`, `Flock.ringEnd`, `Flock.knownWeights`, `Flock.Pending.*`, `Flock.zerocheck`, … |
| `flock.rs`: `phi`, `fixed_challenges`, `lagrange_weights`, `ring_map`, `ring_switch_weight` (leanVM's order) | `Flock.phi`, …, `Flock.ringMap`, `Flock.ringSwitchCoefficients` |
| `ring_tower.rs`: `ring_map`, `Tower::{theta, leaves}`, `conjugate`, `into_subfield`, `target`, `coefficients`, `weight_at` | `Flock.towerRingMap`, `Flock.towerTheta`, `Flock.towerLeaves`, `Flock.conjugate`, `Flock.intoSubfield`, `Flock.towerTarget`, `Flock.towerCoefficients`, `Flock.towerWeightAt` |
| `verifier.rs`: `Shape` (`heights`, `heap`, `constraint_vars`, `validate`, `least_rows`), `degree`, `factor_columns`, `sent_columns`, `linearise`, `tuple_degree`, `chunks`, `quotient_terms`, `table_part`, `layouts`, `stack_layouts`, `batch`, `reduce`, `Reduced`, `Opening`, `Claims`, `FLOCK_*` | `Shape` (the heights), `Shape.validate`, `Shape.leastRows`, `degree`, `factorColumns`, `sentColumns`, `linearise`, `tupleDegree`, `chunks`, `quotientTerms`, `tablePart`, `layoutsOf`, `layouts`, `batch`, **`reduceWith`** (its steps 0, 5 and 6 as `countBits`, `constraintRelation`, `heapRelations`), `Reduced`, `Opening`, `ClaimsMode`, `flock*` |
| `contract.rs`: `rust_verifier`, `NAME`, `SetupRoots::REFERENCE`, `shape_bytes`, `layout_word`, `layout_words`, `contract_iv`, `calls` (`opening_words`, `combined_words`); `machine.rs`: `element_word`; `shapes.rs`: `WORKLOADS`, `PROGRAM_IV`, `Shape::of` | `runWith`/`run`, `name`, `referenceRoots`, `shapeBytes`, `layoutWord`, `layoutWords`, `contractIvWith`/`contractIv`, `pcsCalls` (`openingWords`, `combinedWords`), `elementWord`; `workloads`, `programIv`, `shapeOf`/`shapeWith` |
| `machine.rs`: `PCS_OPEN`'s ABI (mocked, `attesting_all`) | `pcsOpenWith` = `PcsQuotient.openingWith` on `plainLayout` (the layout word's `vars`) |
| `contract.rs`: the five calls (C1, C2, setup, A0, B0) | `verifyWith` |

Deviations, none changing a value: a `List`/`Array` stands for a `Vec`, an out-of-range read gives `0` where the
Rust would panic (it never does on the tables and valid shapes); the degrees are `ℕ`, whose subtraction saturates
as the Rust's `degree` does (F5); `EqCache` and lever 1c's shared work are not transcribed (`weightAt` computes the
same products term by term, the twisted points once per point: field arithmetic is exact, so the regrouping gives
the same values); lever 1b's `XOR` network is code generation (`towerTarget` adds each leaf's slices directly, the
sums the network computes); `End::Ring`'s `weight` of `Slices::InContract`, which the univariate verifier never
reads, is not computed; a row count is an `ℕ` (the Rust holds it in a scalar's low limb). **The shape is the
contract's class** (iteration 2, F1): `Shape` holds the memory, the bytecode and the heights (the Rust's `Shape`
holds row counts, of which only `⌈log₂ rows⌉` is read: `shapeWith`); the row counts are the stream's.


## The setup constants as data

* The measured shapes (`measured`, `workloads`: 32 to 2,000 signatures; the Keccak VM's reference shape is
  `UniKeccakSound.keccakRefShape`), the program's IV
  (`programIv`), the transcript's name (`name`), the bytecode's `2^19` instructions.
* The layouts (`layoutsOf shape`: `C1`, `C2`, setup; `C2`'s columns `Shape.c2Columns`) and the heap
  (`Shape.heap`) are functions of the shape, as in the Rust; the test compares the run's with them, their
  variables with the Rust's, their words through the layout words, and their offsets through every claim.
* The contract's constants (F2): the reference setup roots (`referenceRoots`, `SetupRoots::REFERENCE`'s bytes
  read as digests: `digestBytes` gives the Rust's bytes back), the five layout words (`layoutWords`) and the
  contract's IV (`contractIv`), each compared with the Rust's.
* The setup's tables (`Mapping.lean`): `setupStack` (the bytecode's 16 tuple slots in basis `B`, slot `s` of
  coefficient `k` at word `s + 16 k`, and the addresses `g^i`) and `matrixStack` (Flock's `A0`, `B0`,
  `2^28` words); their roots are the WHIR commitments over `π` (`setupTreesWith`), the IV their binding with
  leanVM's program IV, the shape and the layout words (`Deployment.ivWith`).

## What is tested

The verifier is tested through `UniKeccak`'s runner (`UniKeccakTest/Runner.lean`, 90/90 vectors of
`crates/leanvm/univariate/tests/lean_keccak_vectors.rs` agree with the Rust on every value, the real Keccak proofs'
`PCS_OPEN` inputs word for word) and `UniStatementTest/KeccakTables.lean` (the Keccak VM's tables against
`tables_keccak()`).

## Open points

1. **`PCS_OPEN`'s WHIR instance is a choice**: the Rust mocks the precompile; the statements take the
   Statement's opening (label, version, layout identifier, rate `1/2`) on the plain layout of each stack, its
   size the call's layout word's `vars` (byte 24). The word's `placed` (the words the blocks fill) and code are
   bound by the contract's IV, not read by this opening (the Rust's precompile reads `placed` to know the
   committed lanes). The root word's reading (here: the two halves as `digestOfScalars` for the stream's roots,
   the bytes as `digestOfBytes32` for the reference setup roots) is the Rust's: its prover sends a root as its two
   WHIR scalars (`prove::halves`, `hash_to_scalars`; a prover sending the
   hash's bytes would name another root under this reading), and the setup roots are the commitments' hashes
   (`prover::setup::roots`). The extensions
   (weighted claims, the bit-slice claim) have no opening here; `verifyWith` is the main line's.
2. **The row counts and the shape class** (F1): the verifier accepts any count `c ≤ 2^h`, `0` included; the
   quotients are sized for `leastRows h = 2^(h−1) + 1`, so an honest prover needs `c ≥ leastRows h`
   (`Shape.RowsFit`, completeness's hypothesis), and soundness must hold at every `c ≤ 2^h` (a table's
   `τ` may then be below `h`).
3. **The public input's byte order**: it is read as big-endian words (the contract's, documented at `ad49e74`);
   leanVM's digest is little-endian. One function (`publicWordsOf`, which `publicInputOf` shares) changes when the
   contract does.
4. **Weighted mode with Flock's bit-slice end or no Flock argument** makes no check in the contract (every
   stream of the right length with counts in range is accepted; `PCS_OPEN` checks all), the point-claim ABI with
   the bit-slice end (extension B) leaves its batch terminal to the bit-slice claim (lever 5a), and every check of
   the main line is affine in the scalar read just before it: sound only with the openings.
