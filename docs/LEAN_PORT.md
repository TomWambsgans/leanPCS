# The Lean port

`formal/` states and proves the protocols of commit `f96a7938`: membership with six claims on four commitments
([`HISTORY.md`](HISTORY.md), "Membership at f96a7938"), and π2v3 over π1-rec3 with π1's three claims encoded by the
contract. The deployed ones are [`membership/PROTOCOL.md`](membership/PROTOCOL.md) (three claims on two commitments
and the circuit's) and [`leanvm/rec/SPEC-REC.md`](leanvm/rec/SPEC-REC.md) (π2v3 over π1-rec4, π1's three claims hashed
in π2's circuit). This is what the port needs; the intermediate protocols of `866ba889` were never ported.

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

The bounds' arithmetic carries over but for one port.

- **π1-rec4** (`UniKeccak`, `UniKeccakSound`, `UniKeccakComplete`; only `keccakMain` and `keccakRec3` are transcribed,
  `UniStatement`'s `FsShape` stops at `rec3`): the transcript's wide draws (the rate's output, challenge `k` at lanes
  `1 + 3k …`; `β`, `γ` and the zerocheck's `c` with `α`), the ring map drawn in two parts (`f_0 … f_3` with `t`,
  `f_4, f_5` with `ρ`: [`leanvm/univariate/SPEC.md`](leanvm/univariate/SPEC.md) §14.4), `λ` with `ρ`. A query's error
  is the sum of its challenges'; the cap `2^35/|E|` holds, so `uniKnowledgeSoundnessKeccakRec3_closed`'s arithmetic
  carries over (128.49 bits). Completeness keeps its hypotheses `32 ≤ D.programIv.length ≤ 2^16`. The transcription
  tests (`UniKeccakTest/Runner.lean`) on `keccak128_rec4.txt`, `keccak_rec4.txt`. `UniStatement.weightAt` fixes a slot
  term's bits at 8; `UniKeccak.weightAtK` is the Rust's.
- **The graph** (`RecGraphKeccak`; `Emitted.lean` is `f96a7938`'s π1-rec3 graph, the hazard `MergeHazardK` π1-rec3's):
  the `Wide` node; `pi1GraphIsVerifierK` and `GraphsAgree` for π1-rec4.
- **The compiler** (`RecCircuit`, `rec-circuit-keccak`): `Wide` packings; D16v's trimmed last round (a template per
  plane count, the unmade outputs, the free ends of `A_22`); the hashed claims' sections (message bits, copy units,
  the free bits of an element with their packing and zero check, the digest's `ClaimHash` port); the fallback that
  drops the last hashed claim (`compile_keeping`); a claim still encoded reads its narrow elements as 20 bytes;
  `DigestChecked`, `SetupRootChecked`, `IvChecked` re-evaluated.
- **The statement data** (`RecStatement/Data.lean`, `f96a7938`'s circuit: π1-rec3, 22 blocks, 134 pairs, 38 public
  terms): the reads (`Read.narrow`, 20 bytes; `Read.frame p`, four scalars from the frame), the `ClaimHash` ports and
  their terms, π1's calls (none encoded at 128 and 400 signatures), the digest and setup root, the seed over the frame
  words.
- **The contract model** (`RecCompose`): no selector; the seed over three frame words (payloads 0 … 2); π2's five
  claims at payloads 3 … 7 (`Ending::Claims`, each claim with its payload); no π1 element or root in calldata. `pi1rec3K_end` extended to "a
  satisfied π2 circuit carries the Keccak-256s of the graph's three claims"; the extractor of
  `recKnowledgeSoundness_reduction_real` then names π1's claims by their hashes, with a Keccak-256 collision term (or
  the frame's binding as an assumption, as for every declared claim). The copy argument's round in `pi2Bound`:
  `(4N + 4)/|E|` (the statement and three hashes) against `(4N + 3)/|E|`; 128.93 bits unchanged.

## Lean-facing files

The Rust at main writes the deployed protocols. Until the port, do not rerun these with `UPDATE_LEAN=1` or feed their
output to the Lean: it would overwrite `f96a7938`'s data. The tests that compare them are ignored.

| writer | Lean file | state |
|---|---|---|
| `crates/membership/evm/src/lean.rs` (`graph_lean_is_current`, ignored) | `formal/Implementation/Graph.lean` | `f96a7938`'s graph: 665 nodes, 50 output words, six claims |
| `crates/membership/quotient/examples/statement_vectors.rs` | `formal/Statement`'s `differential` | writes 11-scalar streams and three claims; the Lean expects `f96a7938`'s nineteen-scalar streams and six claims (generate from a checkout of `f96a7938`) |
| `crates/membership/quotient/tests/whir_bridge_vector.rs` | `formal/WhirBridge/Test/Check.lean` | see below |
| `crates/membership/quotient/tests/whir_large_params.rs` (`large_public_openings`) | `formal/WhirBridge/Test/CheckLarge.lean` | see below |
| `crates/leanvm/rec/tests/lean_statement_keccak.rs` (`keccak_statement_data_is_current`, ignored) | `formal/RecStatement/RecStatement/Data.lean` | `f96a7938`'s circuit |
| `crates/leanvm/rec/tests/lean_{graph_keccak,circuit_keccak,pi2_prover}.rs` | `RecGraphKeccak`, `RecCircuit`, `RecCompose`'s `RecComposeTest` | π1-rec3's and `f96a7938`'s |

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
