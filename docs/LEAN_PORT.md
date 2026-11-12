# The Lean port

Both lines are ported. `formal/` states and proves the deployed **membership** protocol
([`membership/PROTOCOL.md`](membership/PROTOCOL.md): three claims on two commitments and the circuit's;
[`../formal/README.md`](../formal/README.md), "Membership: the end theorems") and the deployed **recursion**
([`leanvm/rec/SPEC-REC.md`](leanvm/rec/SPEC-REC.md): π2v4 over π1-rec4, π1's three claims hashed in π2's circuit, the
copy sum forced by `Q`'s layout; "leanVM by recursion: the end theorems"). This is what each port leaves; the
intermediate protocols of `866ba889` were never ported.

## Membership

Ported (`lean/membership`). What remains:

- **The PCS's zero knowledge.** Zero knowledge is proved for the protocol over any PCS `pcs` with
  `PcsZeroKnowledge pcs sim εpcs` its only hypothesis (`zeroKnowledge_of_pcs`; the revealed scalars' uniformity,
  `Group1Uniform` included, is proved: [`membership/PROTOCOL.md`](membership/PROTOCOL.md), "Zero knowledge"). That
  hypothesis is stated in the protocol's experiment (the protocol over `pcs` against its hybrid over the ideal PCS) and
  is satisfiable (the model's ideal PCS, `εpcs = 0`; hiding but not binding, so it shows the hypothesis
  consistent, not that a sound PCS meets it). Not done: a stand-alone PCS zero-knowledge game
  implying it, and a ZK-WHIR PCS proved to meet it; the deployed openings (plain WHIR) do not.
- **`WiringCheck`** (completeness's evaluated hypothesis: the wiring's coefficient `n − 2` nonzero) by a kernel proof.
- Deduplication between the soundness and completeness lines (`Soundness/PcsVH*.lean` copy
  `E2ECompleteness.Pcs{WithHash,Duplex,Cost}`; `tableEval_eq_mle`, `tau_systemL`).

## leanVM

Ported (branch `lean/leanvm`: `lean/pi2`, `lean/pi1-rec4`, `lean/pi2-witness`, `lean/pi2-circuit` merged): π1-rec4's
verifier, graph = verifier at every setup commitment, knowledge soundness (`uniKnowledgeSoundnessKeccakRec4_closed`) and
completeness (`uniCompletenessKeccakRec4_closed`); π2v4's statement and verifier (`RecStatement`, `Data.lean`
regenerated), PIOP (`RecPiop`), the compiler (`RecCircuit`, identical to the Rust's on π1-rec4's graph;
`RecGraphKeccak.pi1rec4K_end`, `pi1rec4K_claimHashes`), the contract model, π2's Fiat–Shamir layer and tables, and
**`RecCompose.recKnowledgeSoundness_reduction_real`** at the real deployment (`pi2Bound ≤ 2^-64` at `Q ≤ 2^64`, 128.93
bits). For completeness: π2's Lean prover (3/3 vectors agree with the Rust's), `Pi2E.pi2_accepts_real` (the contract
accepts its proof off `BadCopy`, `BadT`, `BadRho`, its witness and π1-openings hypotheses discharged:
`Pi2W.pi2WitnessExists_real`, `Pi2W.pi1Openings_of_verifierH`, `Pi2W.nonhole_real`), π1-rec4's prover in the
recursion (`Pi1K.pi1Rec4ProverK`: its Fiat–Shamir over Keccak-f[1600], its trees and openings over `π`) with the four
facts π2's completeness takes (`Pi1K.pi1ProverFactsK4`), and the random-permutation reading of
`Pi1CompletenessKeccak` (`Pi1K.pi1CompletenessFs4_rpm`, `deltaK`), π2's completeness error (the probability layer
`Pi2Prob*`, `Pi2Alpha*`, `Pi2Sim*`, `Pi2TFresh*`, `Pi2RhoFresh`, `Pi2Holds3`, `Pi2Chain`, `Pi2Run*`, `Pi2Closed`:
`Pi2Sim.recCompleteness2_pi2_closed`, `delta2Closed ≤ 2^-164`) and **`RecCompose.Pi1K.recCompleteness_real`** at the
real deployment (`δ1 + δh + 2^-164`, the premises `Pi1CompletenessKeccak δ1`, `Pi1HazardKeccakHonest δh` at
Keccak-f[1600]). The π2v3 and π1-rec3 files of `RecCompose` are retired.

Left:

- **The evaluated checks** at other setup commitments and IVs (`IvChecked` over `(roots, iv)`; `PatchChecked`).

## Lean-facing files

The Rust at main writes the deployed protocols, and both lines' writers are current: their outputs are the Lean's
inputs.

| writer | Lean file | state |
|---|---|---|
| `crates/membership/evm/src/lean.rs` (`graph_lean_is_current`) | `formal/Implementation/Graph.lean` | the deployed graph: 537 nodes, 39 output words, three claims |
| `crates/membership/quotient/examples/statement_vectors.rs` | `formal/Statement`'s `membership-differential` | the deployed protocol's streams and three claims |
| `crates/membership/quotient/examples/dump_circuit.rs` | `formal/Kc3Circuit`'s `kc3-dump-circuit` | the deployed circuit's rows and σ |
| `crates/membership/quotient/tests/{whir_bridge_vector,whir_large_params}.rs` | `formal/WhirBridge/Test/CheckPcs.lean`'s input | version-1 PCS claims |
| `crates/leanvm/rec/tests/lean_statement_keccak.rs` (`keccak_statement_data_is_current`, ignored: slow) | `formal/RecStatement/RecStatement/Data.lean` | **π1-rec4's** circuit (regenerated; the test passes) |
| `crates/leanvm/rec/tests/lean_graph_keccak.rs` | `RecGraphKeccak/Emitted.lean` | **π1-rec4's** (`GraphsAgreeK4` holds) |
| `crates/leanvm/univariate/tests/lean_keccak_vectors.rs` | `UniKeccakTest/Runner.lean`'s input | writes π1-rec4's vectors too (`keccak_rec4`, the real `keccak{128,}_rec4.txt`) |
| `crates/leanvm/rec/tests/lean_circuit_keccak.rs` (`keccak_pi1_rec4`) | `RecCircuit`'s `rec-circuit-diff`, `rec-circuit-keccak` | **π1-rec4's** (identical to the Rust's) |
| `crates/leanvm/rec/tests/lean_pi2_prover.rs` | `RecCompose`'s `RecComposeTest/Pi2Prover.lean` | **π2v4's** (3/3 vectors agree) |

**Lean comments** of the leanVM line cite the design documents by their names at `f96a7938` (`SPEC-FLOCK.md`,
`SPEC-POINTS.md`, `flock/KECCAK.md`); [`HISTORY.md`](HISTORY.md), "Old document names", maps them. Update them with
the port.

**Legacy layers still built** that no end theorem uses, kept because the leanVM line imports them: WhirBridge's
version-2 layout openings (`ours_sound`, `ours_sound_public`, the `Large*` layout parts), `Compose`'s
`knowledgeSoundness_deployed_rust` and its `Deployed*`, `Claims.lean`, the previous protocol's F1 and F0
(`QuotientSecurity`, `formal/Circuit`), `ComposePcs`'s four-root chain, `Statement`'s `Opening.lean` and
`LayoutsProver.lean`.
