# The Lean port

`formal/` states and proves membership at commit `f96a7938` (six claims on four commitments,
[`HISTORY.md`](HISTORY.md), "Membership at f96a7938") and, for the recursion, the deployed π2v4 over π1-rec4. The deployed ones are [`membership/PROTOCOL.md`](membership/PROTOCOL.md) (three claims on two commitments
and the circuit's) and [`leanvm/rec/SPEC-REC.md`](leanvm/rec/SPEC-REC.md) (π2v4 over π1-rec4, π1's three claims hashed
in π2's circuit, the copy sum forced by `Q`'s layout). This is what the port needs; the intermediate protocols of `866ba889` were never ported.

## Membership

- **`formal/Statement/PcsQuotient.lean`**:
  - `Circuit`, `Relation`: the gate `V = Y + C + X·C` (roles swapped from `f96a7938`'s `V = X + C + Y·C`); the public
    values as eight `K`-words packed by Horner rows `(3, b, acc)`, the eleven anchors and the constant `3`; the free
    cells of the three random-row shapes `(0, r, s, r + s)`, `(s, r, 0, r)`, `(1, r, s, r)`; no masks.
  - `Domain`, `Reduction`, `Verifier`, `Transcript`: the stream (two roots, two answers, `X`, `C`, `V + Y`, `next`;
    `μ` for `γ`, no part values); `T`'s layout (`table_slot`, digits read through `ζ = Z x`); the witness claim's
    conic point and weights; the copy claim's digit coordinate `ζ / (1 + ζ)`, kind coordinate and value
    `t R / (ζ + d d')`; the pins' interpolation and `Z_P`; the batched inversion's denominators; no sum claim.
  - `Prover`, `LayoutsProver`: no masks; the blinding `b_0 + b_1 X_1 + b_2 X_2` with `b_2` solved; the one quotient
    on `2n` points; `B_0 = x h_low`; the novel basis's `mul_x`, `mul_w1`, `div_x`.
  - `Extractor`, `Replay`, `Opening`, `PcsOpening`: two commitments and three claims.
  - `Security`, `Zk`: `RevealedUniform` over the new revealed scalars, now two rank conditions (ranks 12 and 3, both
    groups affine), provable from a determinant's degree. At `f96a7938` it is not provable as is (a random row's value
    enters the gate's quotient `GF(2)`-linearly).
- **`formal/EndToEnd`**:
  - `Soundness.knowledgeSoundness`, `ksBound`: three openings, two lists; `ComposePcs.prEvent_pinned_le` and
    `trace_core4P` in two-root versions; `WhirBridge.Pcs.ood_binding_coords` at 24 and 28 variables.
  - The new identity steps: the pins by interpolation inside `g`; `g` merged into `q` by the pole lemma and the
    circuit's condition (`errors_have_their_own_poles`, met by the membership circuit by computation); the sum from
    the layout (`I(0) = d d'(0) B_0(0)`, then the degree); the conic binding of the witness claim (a non-degenerate
    conic spans its plane). The pole lemma is the one step that needs a property of the circuit beyond its being
    wired and loop-free.
  - `E2ECompleteness.completeness_end`: the honest prover, with `b_2`'s existence (given `σ_{n−2} ≠ 0`, met by
    computation).
  - `ZK`, `PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed`: the simulator's revealed scalars and the hypotheses.
- **`formal/QuotientSecurity`** (F1: `PublicWeight`, `Pinning`, `Tables`, `Degrees`, `LogDerivative`,
  `ZeroKnowledge`, `Circuit`, `CircuitLayout`, `Concrete`): the swapped gate and the one table with `x h`; its
  identities, degrees and the claims' comparison above `claims_iff_accepts_ofCantor` need redoing, as far as the end
  theorems still use them ([`../formal/QuotientSecurity/README.md`](../formal/QuotientSecurity/README.md)).
- **`formal/Implementation`**: `Graph.lean` regenerated (`UPDATE_LEAN=1 cargo test -p evm graph_lean_is_current`,
  ignored until then); `Calldata` (273 bytes, no selector, statement words of 8 bytes, two roots, six scalars);
  `Evm.evm_accepts_iff_verifyWith` against the new graph (three declared claims).
- **`formal/Circuit`**: the dump format (`examples/dump_circuit.rs`: sources `0` zero, `1` one, `2` three, `3` free,
  `4 + r` row) and `CircuitTest/Dump.lean`'s public words, with the swapped roles.

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
`Pi1CompletenessKeccak` (`Pi1K.pi1CompletenessFs4_rpm`, `deltaK`). The π2v3 and π1-rec3 files of `RecCompose` are
retired.

Left:

- **π2's completeness error** `δ2` (`RecCompleteness2` for π2's Lean prover): the probability layer (`Pi2Prob*`,
  `Pi2Alpha*`, `Pi2Sim*`, `Pi2TFresh*`, `Pi2Chain`, `Pi2RunCost`, `Pi2RunDuplex`, `Pi2Closed`, at π2v3 on this
  branch; branch `lean/pi2-prob`, not yet building). Its interface is fixed: `Pi2Sim.recCompleteness2_pi2_closed`,
  `recCompleteness_pi2_closed_fs`, `delta2Closed_le`. Then **`RecCompose/CompleteReal.lean`** (written, waiting for
  it) closes the end theorem `Pi1K.recCompleteness_real`: at `realDeployment prog hprog`, the composed Lean prover
  (`pi1Rec4ProverK`, then `realPi2Prover`) rejected with probability at most `δ1 + δh + 2^-164`, from the evaluated
  checks and the premises `Pi1CompletenessKeccak δ1`, `Pi1HazardKeccakHonest δh`; then `RecCompose.lean` imports it
  and the library goes back to `globs`.
- **The evaluated checks** at other setup commitments and IVs (`IvChecked` over `(roots, iv)`; `PatchChecked`).

## Lean-facing files

The Rust at main writes the deployed protocols. The recursion's writers are current (the Lean states π2v4 over
π1-rec4); until the membership's port, do not rerun the membership's with `UPDATE_LEAN=1` or feed their output to the
Lean: it would overwrite `f96a7938`'s data.

| writer | Lean file | state |
|---|---|---|
| `crates/membership/evm/src/lean.rs` (`graph_lean_is_current`, ignored) | `formal/Implementation/Graph.lean` | `f96a7938`'s graph: 665 nodes, 50 output words, six claims |
| `crates/membership/quotient/examples/statement_vectors.rs` | `formal/Statement`'s `differential` | writes 11-scalar streams and three claims; the Lean expects `f96a7938`'s nineteen-scalar streams and six claims (generate from a checkout of `f96a7938`) |
| `crates/membership/quotient/tests/whir_bridge_vector.rs` | `formal/WhirBridge/Test/Check.lean` | see below |
| `crates/membership/quotient/tests/whir_large_params.rs` (`large_public_openings`) | `formal/WhirBridge/Test/CheckLarge.lean` | see below |
| `crates/leanvm/rec/tests/lean_statement_keccak.rs` (`keccak_statement_data_is_current`, ignored: slow) | `formal/RecStatement/RecStatement/Data.lean` | **π1-rec4's** circuit (regenerated; the test passes) |
| `crates/leanvm/rec/tests/lean_graph_keccak.rs` | `RecGraphKeccak/Emitted.lean` | **π1-rec4's** (`GraphsAgreeK4` holds) |
| `crates/leanvm/univariate/tests/lean_keccak_vectors.rs` | `UniKeccakTest/Runner.lean`'s input | writes π1-rec4's vectors too (`keccak_rec4`, the real `keccak{128,}_rec4.txt`) |
| `crates/leanvm/rec/tests/lean_circuit_keccak.rs` (`keccak_pi1_rec4`) | `RecCircuit`'s `rec-circuit-diff`, `rec-circuit-keccak` | **π1-rec4's** (identical to the Rust's) |
| `crates/leanvm/rec/tests/lean_pi2_prover.rs` | `RecCompose`'s `RecComposeTest/Pi2Prover.lean` | **π2v4's** (3/3 vectors agree) |

**WhirBridge's vector checks disagree with their writers.** `whir_bridge_vector.rs` (`--ignored`) writes four vectors
of the EIP's PCS claims (`public`, a `2^15`-word table; `witness`, `wiring`, `copy`, the three openings of a
membership proof at `2^17` rows), each with `pcsclaim`, `root`, `claim`, `stream` and `open` lines, and
`large_public_openings` writes PCS-claim openings. `Test/Check.lean` (which the Rust test's header still names) and
`Test/CheckLarge.lean` read the version-2 layout vectors: three vectors, each with a `new` or `hidden` layout line and
a `prefix` line, plus 18 `layoutprefix` lines; on the current file `Check.lean` stops at the first vector ("no
layout") and finds 4 vectors where it expects 3. The PCS-claim check is `Test/CheckPcs.lean`, on
`crates/pcs_claim/examples/lean_vector.rs`'s format (`n`, `claimbytes`, `payload`, `root`, `ood`, `point`, `value`,
`oodpoint`, `stream`, `open`). The port either writes these vectors in `CheckPcs.lean`'s format, or retires
`Check.lean` and `CheckLarge.lean` with the layout openings.

**Lean comments** cite the design documents by their names at `f96a7938` (`HIDING.md`, `SPEC-FLOCK.md`,
`SPEC-POINTS.md`, `flock/KECCAK.md`); [`HISTORY.md`](HISTORY.md), "Old document names", maps them. Update them with
the port.

**Legacy layers still built** that no end theorem uses (candidates for removal at the port): WhirBridge's version-2
layout openings (`ours_sound`, `ours_sound_public`, the `Large*` layout parts), `Compose`'s
`knowledgeSoundness_deployed_rust` and its `Deployed*`, `Claims.lean`, `Completeness`'s `completeness_deployed_*`
and `HiddenOpenings.lean`, `Statement`'s `Opening.lean` and `LayoutsProver.lean` (also used by the leanVM line's older
PIOP layers).
