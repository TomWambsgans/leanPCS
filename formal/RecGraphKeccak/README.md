<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# RecGraphKeccak: the Keccak VM's π1-rec4 recorded graph, and graph = verifier

The recursion's π2 proves a circuit compiled from the **recorded operation graph** of π1's verifier. This library is
the Keccak VM's instance of `formal/RecGraph` (the graphs, the recorder, the shared verifier pieces and the simulation
framework; the VM: `docs/leanvm/univariate/KECCAK.md`): its π1 verifier at **π1-rec4** (`KECCAK_REC4`: skip 3,
`FsShape::Rec4`, `Slices::TowerWalk`, point claims; `docs/leanvm/univariate/SPEC.md` §14.4), and at π1-rec3
(`KECCAK_REC3`, kept: its program and proofs still build), at the reference workload, the Keccak VM at **128
signatures** (leanVM 9d50c92a3; rows XOR, MUL, SET, DEREF, JUMP, SHA3 `[24260, 36229, 24626, 35812, 15509, 17712]`,
721,598 memory cells: memory `2^20`, bytecode `2^18`; `Pi1.keccak128 = UniKeccak.keccakShapeOf 721598 [..]`, the
Rust's `leanvm_rec::REFERENCE` = `leanvm_statement::shapes::reference()`, and `UniKeccak.keccakRuns`' 128-signature
run).

It is a library of `formal/EndToEnd` (`RecGraphKeccak`, `srcDir = "../RecGraphKeccak"`, `warningAsError`).

```sh
cd formal/EndToEnd
systemd-run --scope -q -p MemoryMax=16G lake build +RecGraphKeccak       # the root module and its axiom guards
systemd-run --scope -q -p MemoryMax=16G lake env lean ../RecGraphKeccak/RecGraphKeccakTest/Pi1Check.lean
UPDATE_LEAN=1 cargo test --release -p leanvm_rec --test lean_graph_keccak   # (repository root) rewrites Emitted.lean
```

`lake build RecGraphKeccak` (the whole library) also builds `Circuit.lean`, which imports `formal/RecCircuit`; that
library does not yet handle `RecGraph.Node.wide` (π1-rec4's), so build the root module (`+RecGraphKeccak`), which does
not import `Circuit.lean`.

## Files

- [`Emitted.lean`](RecGraphKeccak/Emitted.lean): **the Keccak π1-rec4 graph**, written by
  `crates/leanvm/rec/tests/lean_graph_keccak.rs` (a self-contained renderer on `leanvm_univariate::contract::
  {record_verifier, calls, Recorded}` and `leanvm_statement::evm::{record::Node, codegen::Word}`): 10,840 nodes (59
  Keccak-256 calls, 10 `wide` nodes), 14 zero checks, no nonzero check, 1 ring-weight kernel, 3 claims (calls of 30, 29,
  26 words: each claim's root, out-of-domain answer, point and value, `pcsClaimWordsK`), a stream of 9,280 bytes. Data
  only.
- [`Pi1/Flock.lean`](RecGraphKeccak/Pi1/Flock.lean), [`Pi1/Verifier.lean`](RecGraphKeccak/Pi1/Verifier.lean): **the
  Keccak verifier at π1-rec3 as a `RecGraph.Prog` program**, in the Rust's operation order: `frontK` (the lincheck's 11
  rounds), `structuredTerminalS` (`keccak_flock::structured_terminal`, its memoised partial correlations, lazy
  `S::sum`s, `from_fn`s; cut into `packS`, `corrS`, `kernelsS`, `rcS`, `gS` at statement boundaries), `verifyWalkedK`,
  `constraintRelationK` (the `SHA3` lanes' copies, `END_BIT`), `weightAtK` (11 slot bits, `EqCache::row_from`),
  `batchK`, `reduceK`, `pi1Rec3K`, `callsOfK`, `pi1GraphK`. RecGraph's generic helpers are reused.
- [`Pi1/Verifier4.lean`](RecGraphKeccak/Pi1/Verifier4.lean): **π1-rec4's program**: `zerocheck4`, `frontK4`,
  `verifyWalkedK4` (the zerocheck's first coordinate given; no ring end after the slices), `batchK4` (`λ` given),
  `reduceK4` (the three wide draws `Pi1.sampleWide 4`, `5`, `4`; the ring switch's target after the last), `pi1Rec4K`,
  `pi1GraphK4`.
- [`RecGraphKeccakTest/Pi1Check.lean`](RecGraphKeccakTest/Pi1Check.lean): `pi1GraphK4 = Emitted.graph`, node for node
  (passes: the 10,840 nodes, the zeros, the kernel, the calls and the stream length are equal).
- [`Main4.lean`](RecGraphKeccak/Main4.lean): π1-rec4's target. `verifierOutputsWithK4` (`UniKeccak.runWithK4` at
  `keccakRec4`, `pcsClaimWordsK`, the zeros), **`MergeHazardK4`** (`Z_bad(t) = 0` at `keccak128`, `t` the challenge 46,
  `p_0` the challenge 45), **`Pi1GraphIsVerifierK4`**, `Pi1SimK4`, `pi1GraphIsVerifierK4_of_sim`, **`GraphsAgreeK4`**
  (`pi1GraphK4 = Emitted.graph`, evaluated by `Pi1Check.lean`) and `emitted_isVerifierK4` (the statement for
  `Emitted.graph`, from it).
- [`Main.lean`](RecGraphKeccak/Main.lean): π1-rec3's (`verifierOutputsWithK`, `MergeHazardK` at challenges 45 and 52,
  `Pi1GraphIsVerifierK`). `Emitted.lean` is no longer π1-rec3's recording.
- `Sim/`: the simulation of `UniKeccak.reduceWithK4` (and `reduceWithK`) by the programs, in `RecGraph.Sim`'s framework
  (`Sim`, `PH`, `PSim`, `SimE`):
  - `TerminalE.lean`, `TerminalBase.lean`, `TerminalKern.lean`, `Terminal.lean`: **`structuredTerminal_ph`**;
  - `Flock.lean`: `frontK_sim`, `verifyWalkedK_sim`, `flockSpecK` (π1-rec3); `Flock4.lean`: `zerocheck4_sim`,
    `frontK4_sim`, **`verifyWalkedK4_sim`** (π1-rec4: 3,696 bytes, 42 challenges, the 42nd Flock's point's first
    coordinate);
  - `ComposeSpec.lean`: the parts' interface (`TableSpecK`, `ConstraintSpecK`, `DegreeSpecK`, `HeapSpecK`,
    `TailSpecK`, `ShapeSpecK`), `relsUniK`, `c2UniK`, `NoHazardAtK`, `RedRK`;
  - `Compose.lean`: `reduce_simQK` (π1-rec3); `Compose4.lean`: **`reduce_simQK4`** (π1-rec4, from the same parts but
    the tail, `TailSpecK4`; `NoHazardAtK4`, `Mono.sampleWide`, `Mono.batchK4`);
  - `Top.lean`, `End.lean`, `Final.lean`: `pi1SimK_of_reduce`, `pi1GraphIsVerifierK` (π1-rec3); `Final4.lean`:
    `pi1SimK4_of_reduce`, `pi1GraphIsVerifierK4_of_parts`, **`pi1GraphIsVerifierK4`**;
  - `Tables.lean`: `tableSpecK`; `ConstraintFold.lean`: `constraintRelationK_eq`, `degreeSpecK`; `Constraint.lean`:
    `constraintSpecK`; `Heap.lean`: `heap_keccak128`, `heapSpecK`; `BatchK.lean`: `sim_batchK`, `tailSpecK`;
    `BatchK4.lean`: `sim_batchK4`, **`tailSpecK4`**; `ShapeK.lean`: `shapeSpecK`. The tables', constraint, heap and
    shape parts serve both: π1-rec4 states π1-rec3's relations.
- [`Sim/AtSetup4.lean`](RecGraphKeccak/Sim/AtSetup4.lean): **at every setup commitment** (π2's circuit is compiled
  from the graph at the deployment's setup commitment): `Pi1.callsOfKAt roots`, `Pi1.recordedGraphKAt roots` (at
  `referenceRootsK`: `callsOfK`, `recordedGraphK`), `atSetupCall`, **`graphAtSetup g roots`** (each call starting with
  two constant words gets `roots`' root and answer, `RecGraph.Pi1.beNat` of their bytes), `graphAtSetup_recorded`,
  **`Sim.pi1GraphIsVerifierK4At`** (`evalGraph (graphAtSetup pi1GraphK4 roots) = verifierOutputsWithK4 … roots …` off
  `MergeHazardK4`, every `roots`), `Sim.emitted_isVerifierK4At` (the same for `Emitted.graph`, given `GraphsAgreeK4`).
- [`Hazard.lean`](RecGraphKeccak/Hazard.lean), [`Functionals15.lean`](RecGraphKeccak/Functionals15.lean): the merge
  hazard's probability at `keccak128`: `hazard_cardK`, `hazard_probK` (the polynomial is the same at π1-rec3 and
  π1-rec4; only the challenges' indices differ).
- [`Circuit.lean`](RecGraphKeccak/Circuit.lean): `pi1rec3K_end`, `RecCircuit.Compiled.compile_sound_end` at
  `Emitted.graph`. Not in the root: `formal/RecCircuit` does not yet compile `wide` nodes (the π2 port's).

## What is proved, what is left

Proved (sorry-free, on Lean's three axioms: the root's guards):

- **`Sim.pi1GraphIsVerifierK4 : Pi1GraphIsVerifierK4`**, with no hypothesis: for every permutation `π`, IV, public
  input and stream off `MergeHazardK4`, `evalGraph (fun s ↦ pure (π s)) Pi1.pi1GraphK4 iv input stream` equals the
  outputs of `UniKeccak.runWithK4 … keccakRec4 .point` (its three PCS claims' words and the values it collects as
  zeros). From `sim_sampleWide` (the `wide` nodes), `verifyWalkedK4_sim`, `tailSpecK4`, π1-rec3's tables', constraint,
  heap and shape parts, composed (`reduce_simQK4`, `pi1SimK4_of_reduce`); and at every setup commitment,
  **`Sim.pi1GraphIsVerifierK4At`**.
- `Sim.pi1GraphIsVerifierK : Pi1GraphIsVerifierK` (π1-rec3's), unchanged.
- The hazard: `hazard_cardK` (for every `p_0`, at most `2^16` hazardous `t`) and `hazard_probK` (`≤ 2^16/|E| =
  2^-176`), from `Functionals15.lean`'s `functionalsCorrect15`.

Evaluated, not proved: `GraphsAgreeK4` (`Pi1Check.lean`). With it, `emitted_isVerifierK4` states graph = verifier for
the Rust's graph.
