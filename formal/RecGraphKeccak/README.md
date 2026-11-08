<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# RecGraphKeccak: the Keccak VM's π1-rec3 recorded graph, and graph = verifier

The recursion's π2 proves a circuit compiled from the **recorded operation graph** of π1's verifier. This library is
the Keccak VM's instance of `formal/RecGraph` (the graphs, the recorder, the shared verifier pieces and the simulation
framework; the BLAKE2s VM's graph and proof, which this was ported from, are removed) for the Keccak VM
(`docs/leanvm/univariate/KECCAK.md`): its π1 verifier (`Blake2s::Keccak`,
`KECCAK_REC3`: skip 3, `FsShape::Rec3`, `Slices::TowerWalk`, point claims) at the reference workload, the Keccak VM
at **128 signatures** (leanVM 9d50c92a3; rows XOR, MUL, SET, DEREF, JUMP, SHA3 `[24260, 36229, 24626, 35812, 15509,
17712]`, 721,598 memory cells: memory `2^20`, bytecode `2^18`; `Pi1.keccak128 = UniKeccak.keccakShapeOf 721598 [..]`,
the Rust's `leanvm_rec::REFERENCE` = `leanvm_statement::shapes::reference()`, and `UniKeccak.keccakRuns`' 128-signature run).

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
  `crates/leanvm/rec/tests/lean_graph_keccak.rs` (a self-contained renderer on `leanvm_univariate::contract::
  {record_verifier, calls, Recorded}` and `leanvm_statement::evm::{record::Node, codegen::Word}`): 10,848 nodes (9,871
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

- [`Hazard.lean`](RecGraphKeccak/Hazard.lean), [`Functionals15.lean`](RecGraphKeccak/Functionals15.lean): the merge
  hazard's probability at `keccak128`.
- [`Circuit.lean`](RecGraphKeccak/Circuit.lean): **`pi1rec3K_end`**, `RecCircuit.Compiled.compile_sound_end` at the
  Keccak graph: if the compiler accepts `RecGraphKeccak.Emitted.graph`, π2's satisfying witnesses carry its outputs.
  [`RecGraphKeccakTest/Circuit.lean`](RecGraphKeccakTest/Circuit.lean) (`lake exe rec-circuit-keccak GRAPH`) is the
  run: on the graph `crates/leanvm/rec/tests/lean_circuit_keccak.rs` writes (h1, 2026-11-08) it checks the file is
  `Emitted.graph` (the reference's setup roots `Pi1.referenceRootsK`), compiles it in Lean (16,133 expanded nodes,
  1,219 s under load, 2.9 GB) and prints a circuit **identical** to the Rust's (`diff`: 20,930 lines; `N = 2^24`, 14
  regions, 21 blocks, 36 ports, 20,623 `κ`).

```sh
LEAN_CIRCUIT_OUT=out cargo test --release -p leanvm_rec --test lean_circuit_keccak -- --ignored --nocapture
lake build rec-circuit-keccak && .lake/build/bin/rec-circuit-keccak out/keccak_pi1_rec3.graph > k.circuit
diff out/keccak_pi1_rec3.circuit k.circuit
```

## What is proved, what is left

Proved (sorry-free, on Lean's three axioms: the root's guards): the program records the Rust's graph (by the check,
compiled evaluation), and **`Sim.pi1GraphIsVerifierK : Pi1GraphIsVerifierK`**, with no hypothesis: the structured
terminal and Flock (`flockSpecK`), the tables' parts (`tableSpecK`), `Q_W`'s identity and degree (`constraintSpecK`,
`degreeSpecK`), the heap's relations (`heapSpecK`), the tail (`tailSpecK`: `Sim/WeightsK.lean`'s `weightAtK` algebra,
`Sim/ClaimsK.lean`'s `weightAtK_phc`, `termPK_eq`, `combine_weightK`, `Sim/BatchK.lean`'s `sim_batchK`), the relations'
shape off the hazard (`shapeSpecK`, `Sim/ShapeK.lean`), composed (`reduce_simQK`, `pi1SimK_of_reduce`).

The hazard's probability (`Hazard.lean`): `hazard_cardK` (for every `p_0`, at most `2^16` hazardous `t`) and
`hazard_probK` (`≤ 2^16/|E| = 2^-176`), from `Functionals15.lean`'s `functionalsCorrect15` (`FunctionalsCorrect 15`: 15
Gauss–Jordan steps checked by `decide +kernel` from printed words, as `UniSound.Ids.functionalsCorrect18`; 241 s, 10 GB).
