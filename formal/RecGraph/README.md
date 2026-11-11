<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# RecGraph: recorded verifier graphs, their meaning, and the recorder

The recursion (`crates/leanvm/rec`) proves π1's verifier inside π2: π2's circuit is compiled from the **recorded
operation graph** of π1's verifier (π1-rec3: `FsShape::Rec3`, the point-claim ABI). Compiler correctness splits in
two:

1. a satisfied compiled circuit's ports are the graph's evaluation on the stream its free bits encode
   (`formal/RecCircuit`);
2. **the graph's evaluation is π1's verifier**: this library's generic half (the graphs, their meaning, the recorder,
   "recording commutes with evaluation", the verifier's shared pieces as recorder programs and their simulation
   framework), and, for the Keccak VM at the 128-signature reference, `formal/RecGraphKeccak` (the emitted graph, the
   Keccak verifier as a program, `pi1GraphIsVerifierK`, the hazard's probability).

It is a library of `formal/EndToEnd` (`RecGraph`, `srcDir = "../RecGraph"`), as `UniStatement` is.

```sh
cd formal/EndToEnd
systemd-run --scope -q -p MemoryMax=10G lake build RecGraph          # the library and its axiom guards
lake env lean ../RecGraph/RecGraphTest/SimAxioms.lean                # the simulation's lemmas' axioms
```

## Files

- [`Node.lean`](RecGraph/Node.lean): `leanvm_statement::evm::record`'s `Node` (`const`, `statement`, `input` at a byte
  offset with a length, `add`, `mul`, `seed`, `hash` of a state and a run of stream bytes, `low`, `narrow` (π1-rec2's
  160-bit challenges), `bits`, `ringWeight`), `codegen::Word` (`node`, `const`, `stream`), `Graph` (nodes, zero and
  nonzero checks, kernels, the claims' words, stream length). The pair derivation is additions and products: no new
  kinds.
- [`Semantics.lean`](RecGraph/Semantics.lean): **`evalGraph F g iv publicInput stream`**, over a permutation `F` of the
  Keccak state in any monad (the random-permutation model's style, as `UniStatement`'s verifier is written): every
  node's value (`stepNode`, `eval.rs`'s, on `UniStatement`'s own readers: `beWordAt`, `seedWith`, `keccak256With`,
  `challengeOf`, `narrowE`, `intBits`, `Flock.towerWeightAt`), then the outputs: each call's bytes, the zeros, the
  nonzeros; none on a stream of another length.
- [`Record.lean`](RecGraph/Record.lean): **the recorder in Lean** (`RecState`: `Sym::new`'s hash-consing by a
  `HashMap`, `Sym`'s smart constructors `constant`, `add`, `mul`, `bits`, `ringWeight` as `record.rs` has them,
  `Recorder`'s `start`, `input`, `sample` (low or narrow), `statement`), and **programs** over it (`Prog`, a free monad
  whose scalars are node indices): `Prog.record` (the graph), `Prog.run` (the program on `E`, each node evaluated as
  it is made).
- [`Commute.lean`](RecGraph/Commute.lean): **recording commutes with evaluation**, for every program.
- [`Values.lean`](RecGraph/Values.lean): **every operation's node has the operation's meaning** (`op_val`), folds, dropped zeros and ones, `x + x = 0`
  and hash-consed nodes included.
- [`Pi1/`](RecGraph/Pi1): the verifier's shared pieces as recorder programs (`Ops`: the transcript's reads and
  draws, sums, products, `eqKernel`, the sumchecks, the digits, `Z_act`; `Flock`: the Lagrange weights, the zerocheck,
  the ring switch's end in tower order; `Verifier`: terms and relations on nodes, `linearise`, `tablePart`,
  `quotientTerms`, `combine` by node, the heap's relations), and `Main`'s `evalGraph_recorded`: a recorded graph's
  evaluation is its program's run on `E`.
- [`Sim/`](RecGraph/Sim): the simulation framework (`Chan`, `Pure`, `Transcript`: the judgment `Sim` against a
  channel monad and the transcript; `FlockBase`, `FlockNet`, `FlockPure`, `FlockTower`, `Flock`: the `PH` judgment,
  the loop rules, Flock's shared parts; `Tables`, `TablePart`, `Relations`, `Claims`, `Batch`, `Shape`: the tables'
  parts, the relations, `combine` (by node against by value), the batch's framework, the relations' shape;
  `ComposeBase`, `ComposeSpec`, `Compose`, `Calls`: `SimQ`, `Mono`, the shared representations, the calls' bytes),
  from which `formal/RecGraphKeccak/RecGraphKeccak/Sim` proves the Keccak VM's π1-rec3.
- [`RecGraphTest/SimAxioms.lean`](RecGraphTest/SimAxioms.lean): the simulation's lemmas use the three standard axioms.
- `formal/UniStatement/UniStatement/Rec.lean`: `UniStatement`'s Fiat–Shamir shapes (`FsShape`); the Keccak VM's
  verifier at them is `formal/UniKeccak`'s.

## The theorems (proved, sorry-free, on Lean's three axioms: `RecGraph.lean`'s guards)

- `Commute.lean`: **`run_vals`** (for every program, pure permutation, IV, public input and stream, running the
  program evaluates exactly the nodes it records, and keeps `KInv`), **`record_eval`** (`evalNodes` of the recorded
  graph is the program's run on `E`).
- `Values.lean`: **`op_val`** (for a recorder state with `RecInv` and an operation whose operands it holds, `OpOK`, the
  operation's node has the operation's meaning on `E`: the constant, the public word, the stream's bytes at the
  cursor, the challenge of Keccak-256 over `π`, narrow or not, the sum, the product, the bit field,
  `ring_tower::weight_at`; folds, dropped zeros and ones, `x + x = 0` and hash-consed nodes included), `op_inv`,
  `op_lt`, `record_inv`, `start_inv`, and per operation `new_val`, `constant_val`, `add_val`, `mul_val`, `bits_val`,
  `input_val`, `statement_val`, `sample_val`, `ringWeight_val` with their `…_inv`.

## Graph = verifier

For the Keccak VM, at the 128-signature reference: `formal/RecGraphKeccak` (`README.md` there). The recorded graph
merges equal points, and a point into a longer one it is a prefix of, by node, while the verifier on `E` compares
values; so graph = verifier holds off the merge hazard (`MergeHazardK`), whose probability is bounded there
(`hazard_probK`).
