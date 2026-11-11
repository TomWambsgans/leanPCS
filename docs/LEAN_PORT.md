# The Lean port

`formal/` states and proves the deployed **membership** protocol ([`membership/PROTOCOL.md`](membership/PROTOCOL.md):
three claims on two commitments and the circuit's; [`../formal/README.md`](../formal/README.md), "Membership: the end
theorems"). The **leanVM** line still states the protocols of commit `f96a7938`: π2v3 over π1-rec3 with π1's three
claims encoded by the contract; the deployed one is [`leanvm/rec/SPEC-REC.md`](leanvm/rec/SPEC-REC.md) (π2v4 over
π1-rec4, π1's three claims hashed in π2's circuit, the copy sum forced by `Q`'s layout). This is what the port still
needs; the intermediate protocols of `866ba889` were never ported.

## Membership

Ported (`lean/membership`). What remains:

- **`Group1Uniform ε1`** (zero knowledge's hypothesis besides the PCS's; `T`'s part is proved through the slack
  words, `εslack ≤ 2^-126`): the random rows' `K`-linear map to `W`'s answer and `X`, `C`, `V + Y` of rank 12 but on a
  small set of challenges ([`membership/PROTOCOL.md`](membership/PROTOCOL.md), "Zero knowledge").
- **`WiringCheck`** (completeness's evaluated hypothesis: the wiring's coefficient `n − 2` nonzero) by a kernel proof.
- Deduplication between the soundness and completeness lines (`Soundness/PcsVH*.lean` copy
  `E2ECompleteness.Pcs{WithHash,Duplex,Cost}`; `tableEval_eq_mle`, `tau_systemL`).

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
  plane count, the unmade outputs, the free ends of `A_22`); the hashed claims' sections (message bits, copy units, the
  free bits of an element with their packing and zero check, the digest's `ClaimHash` port); the claims hashed by π1's
  shape (`compile::hashed_claims`: none, `[0]`, `[0, 1, 2]`), a circuit past `2^24` refused; a claim still encoded reads
  its narrow elements as 20 bytes; `DigestChecked`, `SetupRootChecked`, `IvChecked` re-evaluated.
- **The statement data** (`RecStatement/Data.lean`, `f96a7938`'s circuit: π1-rec3, 22 blocks, 134 pairs, 38 public
  terms): the reads (`Read.narrow`, 20 bytes; `Read.frame p`, four scalars from the frame), the `ClaimHash` ports and
  their terms, π1's calls (none encoded at 128 and 400 signatures), the digest and setup root, the seed over the frame
  words.
- **The contract model** (`RecCompose`): no selector; the seed over three frame words (payloads 0 … 2); π2's four
  claims at payloads 3 … 6 (`Ending::Claims`, each claim with its payload; seven openings charged once by
  `pcs_union_sound_oracle`, `qOodBinding` over `Q`'s two claims); no π1 element or root in calldata. `pi1rec3K_end` extended to "a
  satisfied π2 circuit carries the Keccak-256s of the graph's three claims"; the extractor of
  `recKnowledgeSoundness_reduction_real` then names π1's claims by their hashes, with a Keccak-256 collision term (or
  the frame's binding as an assumption, as for every declared claim). The copy argument's round in `pi2Bound`:
  `(4N + 4)/|E|` (the statement and three hashes) against `(4N + 3)/|E|`; 128.93 bits unchanged.

- **π2v4, the copy sum from `Q`'s layout** ([`leanvm/rec/PI2.md`](leanvm/rec/PI2.md) §2, §7):
  - `RecStatement` (the statement and verifier): the transcript name `leanvm-rec-pi2v4`; `Q`'s slots (`H = x h` at
    `(0, 0)`, `q`'s digits at `(1, 0)`, `(0, 1)`, `G` at `(1, 1)`; at limb code 3 `P`, `q_P`'s digits, `S`); the digits
    to `w_m`; the inversion of `R_d Y_1 Y_2 B w_m Y_3 · c_h D_n`; the identity's claim at `(u_0 … u_{m-1}, t w_m / Y_1,
    t w_m² / Y_2, y_0, y_1)` and its value, the pushes' at `(u_0 … u_{m-1}, ρ, ρ w_m / Y_3, 1, 1)` and its value; no sum
    claim; `Calls.lean`: seven claims.
  - `RecPiop` (soundness): the pushes' claim as a polynomial of degree 2 in `ρ` binding `P(t) = s`, the definition and
    `S(t) = 0`; the identity's claim as `I(t) = 0`, `I = D² H + x Z D A + x² Z³ G + x D R` (below `5N`), and the lemma
    "`I = 0` and `D(0) ≠ 0` give `H(0) = 0`, `h = H / x` of degree below `N − 1`, `Σ_V h = 0`, `h D + R = 0` on `V_m`",
    replacing the sum claim and the empty slots' argument; `Rounds.lean`'s `err` at `t` `(5N − 1)/|E|`, at `ρ` `2/|E|`
    for `Q` (`pi2Bound` stays 128.93 bits).
  - `RecCompose` completeness: the honest `Q` (`H` by `mul_x`, the slots, `G = S = 0`: `Pi2Prover*`, `Pi2Honest*`) and
    the nonvanishing of `Y_1`, `Y_2`, `Y_3` (`Pi2Complete*`).
  - Vectors: `tests/lean_pi2_prover.rs`, `tests/lean_statement_keccak.rs` regenerated with the port.

## Lean-facing files

The Rust at main writes the deployed protocols. The membership line's writers are current (their outputs are the
Lean's inputs); for the leanVM line's, until its port, do not rerun these with `UPDATE_LEAN=1` or feed their output
to the Lean: it would overwrite `f96a7938`'s data. The tests that compare them are ignored.

| writer | Lean file | state |
|---|---|---|
| `crates/leanvm/rec/tests/lean_statement_keccak.rs` (`keccak_statement_data_is_current`, ignored) | `formal/RecStatement/RecStatement/Data.lean` | `f96a7938`'s circuit |
| `crates/leanvm/rec/tests/lean_{graph_keccak,circuit_keccak,pi2_prover}.rs` | `RecGraphKeccak`, `RecCircuit`, `RecCompose`'s `RecComposeTest` | π1-rec3's and `f96a7938`'s |

**Lean comments** of the leanVM line cite the design documents by their names at `f96a7938` (`SPEC-FLOCK.md`,
`SPEC-POINTS.md`, `flock/KECCAK.md`); [`HISTORY.md`](HISTORY.md), "Old document names", maps them. Update them with
the port.

**Legacy layers still built** that no end theorem uses, kept because the leanVM line imports them: WhirBridge's
version-2 layout openings (`ours_sound`, `ours_sound_public`, the `Large*` layout parts), `Compose`'s
`knowledgeSoundness_deployed_rust` and its `Deployed*`, `Claims.lean`, the previous protocol's F1 and F0
(`QuotientSecurity`, `formal/Circuit`), `ComposePcs`'s four-root chain, `Statement`'s `Opening.lean` and
`LayoutsProver.lean`.
