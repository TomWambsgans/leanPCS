<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# RecGraphKeccak: the Keccak VM's π1-rec3 recorded graph, and graph = verifier

The recursion's π2 proves a circuit compiled from the **recorded operation graph** of π1's verifier. This library is
`formal/RecGraph` for the Keccak VM (`crates/leanvm_univariate/KECCAK.md`): its π1 verifier (`Blake2s::Keccak`,
`KECCAK_REC3`: skip 3, `FsShape::Rec3`, `Slices::TowerWalk`, point claims) at the reference workload, the Keccak VM
at **128 signatures** (leanVM 9d50c92a3; rows XOR, MUL, SET, DEREF, JUMP, SHA3 `[24260, 36229, 24626, 35812, 15509,
17712]`, 721,598 memory cells: memory `2^20`, bytecode `2^18`; `Pi1.keccak128 = UniKeccak.keccakShapeOf 721598 [..]`,
the Rust emitter's `KECCAK_128`, both from `tests/keccak_vm.rs`'s `KECCAK_RUNS` / `UniKeccak.keccakRuns`).

It is a library of `formal/EndToEnd` (`RecGraphKeccak`, `srcDir = "../RecGraphKeccak"`, `warningAsError`).

```sh
cd formal/EndToEnd   # on h1
systemd-run --scope -q -p MemoryMax=12G lake build RecGraphKeccak      # the library and its axiom guards
systemd-run --scope -q -p MemoryMax=12G lake env lean ../RecGraphKeccak/RecGraphKeccakTest/Pi1Check.lean
# the emitted graph (from the repository root):
UPDATE_LEAN=1 cargo test --release -p leanvm_rec --test lean_graph_keccak   # rewrites Emitted.lean
cargo test --release -p leanvm_rec --test lean_graph_keccak                 # fails while it is stale
```

## Files

- [`Emitted.lean`](RecGraphKeccak/Emitted.lean): **the Keccak π1-rec3 graph**, written by
  `crates/leanvm_rec/tests/lean_graph_keccak.rs` (a self-contained renderer on `leanvm_univariate::contract::
  {record_verifier, calls, Recorded}` and `leanvm_flock_gas::evm::{record::Node, codegen::Word}`): 10,848 nodes (9,871
  additions and products, 69 Keccak-256 calls), 14 zero checks, no nonzero check, 1 ring-weight kernel, 3 `PCS_OPEN`
  calls of 31, 30, 27 words, a stream of 9,232 bytes (`C1`'s root at 24, `C2`'s at 3,752). Data only. Builds in about
  7 s.
- [`Pi1/Flock.lean`](RecGraphKeccak/Pi1/Flock.lean), [`Pi1/Verifier.lean`](RecGraphKeccak/Pi1/Verifier.lean): **the
  Keccak verifier as a `RecGraph.Prog` program**, in the Rust's operation order: `frontK` (the lincheck's 11 rounds),
  `structuredTerminalS` (`keccak_flock::structured_terminal`, its memoised partial correlations, lazy `S::sum`s,
  `from_fn`s; cut into `packS`, `corrS`, `kernelsS`, `rcS`, `gS` at statement boundaries), `verifyWalkedK`,
  `constraintRelationK` (the `SHA3` lanes' copies, `END_BIT`), `weightAtK` (11 slot bits, `EqCache::row_from`),
  `batchK`, `reduceK`, `pi1Rec3K`, `callsOfK`, `pi1GraphK`. RecGraph's generic helpers (`Pi1/Ops`, the zerocheck, the
  ring end, `tablePart`, `combine`, `heapRelations`) are reused.
- [`RecGraphKeccakTest/Pi1Check.lean`](RecGraphKeccakTest/Pi1Check.lean): `pi1GraphK = Emitted.graph`, node for node.
- [`Main.lean`](RecGraphKeccak/Main.lean): the target. `verifierOutputsWithK` (`UniKeccak.runWithK` at `keccakRec3`,
  `pcsCallsK`, the zeros), `MergeHazardK` (`Z_bad(t) = 0` at `keccak128`, `t` the challenge 52, `p_0` the challenge 45),
  **`Pi1GraphIsVerifierK`**, `Pi1SimK`, `pi1GraphIsVerifierK_of_sim`.
- `Sim/`: the simulation of `UniKeccak.reduceWithK` by the program, in `RecGraph.Sim`'s framework (`Sim`, `PH`,
  `PSim`, `SimE`):
  - `TerminalE.lean`: `UniKeccak.structuredTerminal`'s pieces as definitions, `structuredTerminal_eq` (by `rfl`);
  - `TerminalBase.lean`, `TerminalKern.lean`, `Terminal.lean`: **`structuredTerminal_ph`**;
  - `Flock.lean`: `frontK_sim`, `verifyWalkedK_sim`, **`flockSpecK`**;
  - `ComposeSpec.lean`: the parts' interface (`TableSpecK`, `ConstraintSpecK`, `DegreeSpecK`, `HeapSpecK`,
    `TailSpecK`, `ShapeSpecK`), `relsUniK`, `c2UniK`, `NoHazardAtK`, `RedRK`;
  - `Compose.lean`: **`reduce_simQK`** (`reduceK` against `reduceWithK` from the parts); `Top.lean`: `calls_eqK`,
    **`pi1SimK_of_reduce`**; `End.lean`: **`pi1GraphIsVerifierK_of_parts`**, `KeccakSimParts`,
    `pi1GraphIsVerifierK_of_simParts`;
  - `Tables.lean`: **`tableSpecK`**; `ConstraintFold.lean`: `constraintRelationK_eq`, **`degreeSpecK`**;
    `Constraint.lean`: **`constraintSpecK`**; `Heap.lean`: `heap_keccak128`, **`heapSpecK`**.

## What is proved, what is left

Proved (sorry-free, on Lean's three axioms: the root's guards): the program records the Rust's graph (by the check,
compiled evaluation); the structured terminal, Flock, the tables' parts, `Q_W`'s identity and its degree, the heap's
relations; the composition: `Pi1GraphIsVerifierK` from the parts' statements.

Left (`KeccakSimParts`, with the representations of `Tables`/`Constraint`/`Heap` fixed): `TailSpecK` (the claims'
combination and the batch with `weightAtK`, against `UniKeccak.batchK`: RecGraph's `Claims.lean` weight part and
`Batch.lean` with 11 slot bits) and `ShapeSpecK` (`reduceWithK`'s relations satisfy the tail's conditions off the
hazard: RecGraph's `Shape.lean` at `keccak128`), and the hazard's probability (`RecGraph.Hazard`'s `hazard_card` at
height 15: `UniSound.Ids.zBad_ne_zero` needs `FunctionalsCorrect 15`).
