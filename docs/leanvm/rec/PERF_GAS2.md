<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# The recursion's gas, round 2 (branch `perf2/leanvm-gas`)

> Below, `main` is commit `866ba889` (after [`PERF_GAS.md`](PERF_GAS.md)'s round), and "this branch" the branch this
> note describes; every figure is measured on h3 (AMD EPYC 9355P) unless marked modelled.

Benchmark 2 of the EIP draft: π2's contract verifying π1 of 128 leanXMSS signatures, as an EIP-8141 frame transaction
under EIP-7976's floor, with its frame of PCS claims (`1 + 32` bytes a claim) and the PCS gas (`5,000 + 1,000` a claim)
on both sides. On `main` the floor binds: `64 · (941 + 257) + 13,000 = 89,672`. The last round hashed π1's claim on
`C1` inside π2's circuit; hashing `C2`'s and `F`'s too did not fit `2^24` positions. This branch makes the room and
hashes all three.

## Results

`tests/pi2_real.rs` (`real_end_to_end`, `real_gas`; `PI2_VECTOR=keccak_rec4` at 400 signatures):

| | calldata | execution | standard / floor | with the frame and PCS gas |
|---|---:|---:|---:|---:|
| `main`, 128 signatures | 941 B (8 zero) | 37,406 | 52,366 / 60,224 | **89,672** (floor) |
| this branch, 128 signatures | **577 B** (4 zero) | 31,524 | 40,708 / 36,928 | **66,376** (floor; standard 57,820) |
| `main`, 400 signatures | 961 B | 42,308 | 57,612 / 61,504 | 90,952 |
| this branch, 400 signatures | 577 B (5 zero) | 35,761 | 44,933 / 36,928 | 66,376 (floor; standard 62,033) |

**−23,296 gas (−26.0%)** at the reference shape, −24,576 at 400 signatures. The floor still binds, with 8,556 gas of
execution to spare at 128 signatures (4,343 at 400).

- **Calldata now** (577 B): π1's public input (32), `W`'s and `Q`'s commitments (2 × 56), the 18 values at `t` (432),
  the frame's index (1). Gone: `C2`'s root (32), its out-of-domain answer (24), the 13 narrow challenges (260), `C2`'s
  and `F`'s values (48): −364 B. The stream holds no public data of π1 any more: π2's public words are the statement
  and the three claims' Keccak-256s, which the contract reads from the frame (payloads 0, 1, 2) into the seed.
- **The contract**: 14,513 B of code at 128 signatures (17,185 on `main`), 16,472 B at 400 (19,425), under EIP-170's
  24,576; 786 `FIELD_MUL`s (910), 176 selector pairs (205; 232 at 400, 266 on `main`). It encodes five claims (π2's)
  and finds them at payloads 3 … 7. Execution by phase (128 signatures): indicators 8,784 + 904, push formulas 8,551,
  the claims written, hashed and checked 4,013, identity and claims 2,574, the fold 2,337, the inversion 1,208, digits
  920, transcript 797, calldata reads 776, ports 510, setup 124, entry 26.
- **π2's circuit**: 16,413,312 of `2^24` positions (97.8%; `main` 98.2% with `C1`'s claim alone) at 128 signatures,
  16,684,592 (99.4%) at 400.
- **The prover** (8 threads, `bench.sh`'s protocol): unchanged, 2.62 s a proof on both (§6).
- **Soundness** (§5): π1-rec4 128.79 bits as `Q/ε` at `Q = 2^64` (π1-rec3's 128.79), π2 128.93, the recursion 127.86
  (`main`: the same three figures).

## 1. Where π2's positions go, and what was needed

π2's circuit is π1's verifier: on `main` at 128 signatures, 116 Keccak-f for π1's transcript, 6 for `C1`'s claim,
the rest (free bits, packings, `E` units, XORs, ports) about 0.51M positions; a Keccak-f is 130,944. Hashing `C2`'s
claim (`82 + 24 · 26` bytes: 6 Keccak-f) and `F`'s (`82 + 24 · 23`: 5) takes 11 more permutations and their bits:
17,972,736 positions, **1,195,520 over `2^24`** (`2^25` puts `Q`, sixteen slots of `N`, at `2^29` words, past WHIR's
certified `2^28`). Two changes free 1.56M:

| | π1's transcript | positions at 128 signatures, three claims hashed |
|---|---:|---:|
| `main`'s transcript and gadget | 116 Keccak-f | 17,972,736 (107.1%) |
| π1-rec4 (§2): −10 Keccak-f | 106 | 16,664,192 (99.3%) |
| and D16v's trimmed last rounds (§3): −256 `k1` rows a digest | 106 | **16,413,312 (97.8%)** |

## 2. π1-rec4: one Keccak-f for the challenges no message separates (`FsShape::Rec4`)

π1-rec3's transcript (`tests/counts.rs`, `transcript_shape`; bytes each call absorbs besides the 32-byte state):
`80 | 0 0 0 | 192 | 48 ×41 | 1536 | 0 ×5 | 56 | 2832 | 0 | 192 ×13 | 48`, plus the seed: 70 calls, 116 Keccak-f. Nine
calls absorb nothing (`β`, `γ`, the zerocheck's `c`; the ring map's `f_1 … f_5`; the batch's `λ`): a whole
permutation for 192 bits each, while a Keccak-f's rate holds 1,088.

**The wide draw** (`Channel::sample_wide`, `transcript::keccak256_rate`): one Keccak-256 of the state and the bytes
since the last challenge, as `sample` hashes them, but read past its digest: the sponge's whole rate after its last
permutation (136 bytes; its first 32 are `keccak256` of the input, which stays the chain's next state). Challenge `k`
is the rate's bytes `8 + 24k .. 32 + 24k` read as `challenge_of` reads the state's `8 .. 32`, so challenge 0 is
`sample`'s and a draw gives up to five (`WIDE_MAX`). In π2's circuit a challenge `k` is three more lanes of the same
permutation's output (lanes `1 + 3k … 3 + 3k`), packed as `Low`'s.

**π1-rec4's transcript** (the stream is π1-rec3's byte for byte; only the challenges' derivation changes):

| call | absorbs | Keccak-f | draws |
|---|---:|---:|---|
| the seed | name, IV, public input | 1 | — |
| after `C1`'s commitment | row counts, `C1`'s root and answer (80 B) | 1 | `α`'s `c`, `β`, `γ`, the zerocheck's `c` (wide, 4) |
| the skip, the zerocheck's and lincheck's rounds | as π1-rec3 (192 B, 41 × 48 B) | 2 + 41 | one each |
| after `C2`'s commitment | the slices (1,536 B) and `C2`'s root and answer (56 B) | 12 | `t`, the ring map's `f_0 … f_3` (wide, 5) |
| after the values at `t` | 2,832 B | 22 | `ρ`, the batch's `λ`, `f_4`, `f_5` (wide, 4) |
| the batch | 13 pairs × 192 B, 48 B | 26 + 1 | one each (narrow) |
| | | **106** (π1-rec3: 116) | 60 calls (70) |

Moving the slices into `t`'s call costs nothing (`32 + 1,592 + 1 = 1,625` bytes fill 12 blocks, as `32 + 1,536`
did alone) and saves the map's own call. At 400 signatures: 108 against 118. The minimum for any sponge on this
stream, every message absorbed before the challenge that follows it, is 105 (the values at `t` are 9 bytes past 21
blocks with the 32-byte state; a duplex without it would save that one).

**Code.** `leanvm_statement`: `FsShape::Rec4` (its code 4 in π1's contract IV, which binds the variant), the channels'
`sample_wide` (`KeccakChannel`, `KeccakWriter`, the prover's `Replay`, the recorder: `record::Node::Wide(hash, k)`,
challenge 0 a `Node::Low`), `flock_min::verify_walked_deferred` (Flock without its map, the zerocheck's first
coordinate given) and `ring_end_at`. `leanvm_univariate`: `verifier::reduce` and the prover draw as the table says
(`KECCAK_REC4`); `batch` takes `λ` drawn. The EVM's `KECCAK256` gives the digest alone, so π1-rec4 has no contract of
its own (`codegen` refuses a `Wide` node): its vectors are checked against the Rust verifier (`tests/evm_vectors.rs`,
`tests/prove_real.rs`), and π2's circuit runs it. `leanvm_rec::PI1 = KECCAK_REC4`; π1-rec3 stays (the Lean's, its
vectors, its contract).

**Vectors.** `crates/leanvm/univariate/tests/vectors/keccak128_rec4.txt` (the reference trace) and `keccak_rec4.txt`
(400 signatures: a trace dumped by leanVM `9d50c92a3` with `dump_keccak`, rows `[73288, 110893, 75762, 109932, 48157,
55316]`, the committed shape), written by `tests/prove_real.rs` (`WRITE_VECTORS`, `VECTOR_FILE`), not by hand.

## 3. D16v's last round makes the lanes read alone

A permutation's caller reads its digest (lanes 0 … 3) at the end of a Keccak-256, the state after a later block's
absorption otherwise. Round 23's χ rows of plane `y` make lanes `5y … 5y + 4`, so a permutation that ends a call needs
only plane 0's (64 `k0` rows), not the 256 `k1` rows of planes 1 … 4: `Permutation::permute` takes the lanes read,
`Sponge::keccak256_lanes` asks for 25 in a later block and the caller's in the last (4, or `4 + 3k` for a wide draw's
challenge `k`: planes 0 … 2 or 0 … 3). The planes not made leave their outputs `UNMADE`; their inputs (round 22's
`A_22` lanes they would read) end at free ends, and `D_23[x][z]`, which every lane `x` of plane 0 reads, still ends at
its `k0` row. Rounds 0 … 22 are whole, since `C_23` and so `D_23` read every lane of `A_22`; the round-23 rows made
are a whole permutation's rows, so every lane made is Keccak-f's.

126,848 positions a digest's permutation instead of 130,944; at 128 signatures π2 has 60 of them (57 of π1's calls,
the three claims') and three wide draws (2, 1 and 2 planes fewer): 245 planes, −250,880 positions. The witness plan (`circuit::plan`) has four templates (a whole permutation; last rounds
of 1, 3 and 4 planes) instead of one, and skips the unmade outputs' slots. `circuit::tests::d16_rate_lanes_on_random_inputs`
checks the rate's lanes against the native sponge at 13, 16 and 17 lanes, one block and several.

## 4. π1's three claims hashed in π2's circuit (`compile::HASHED_CLAIMS = [0, 1, 2]`)

As `C1`'s claim on `main` (`PERF_GAS.md` §3), now `C2`'s and `F`'s too: each claim's encoding (`version ‖ n ‖ root ‖
ood ‖ point ‖ value`) as message bits, its Keccak-256 in the circuit, the digest a four-limb port
(`Source::ClaimHash(j)`), read by π2's verifier from payload `j` of the frame of PCS claims (`Read::Frame`) and hashed
into the seed. `C2`'s root and out-of-domain answer are the stream's bits, `F`'s are constants; the coordinates and
values are free bits packed into limbs checked equal to the elements'. The contract checks π2's five claims at
payloads 3 … 7.

**The fallback** (`compile_keeping`): a circuit that does not fit `2^24` with the three hashes drops the last and tries
again (`[0, 1]`, `[0]`, `[]`): the recursion's capacity (π1's `C1` at `2^28` near 470 signatures) is kept, the bytes
are not. At 400 signatures all three fit (99.4%); π1-rec3's circuit (the Lean's) at 128 signatures falls back to
`C1`'s alone (96.5%, `tests/circuit.rs`, `keccak_rec3_128_d16v`).

## 5. Soundness

**π1-rec4 against π1-rec3.** The stream, the statement, the relations, the claims and every challenge's role are π1-rec3's;
three things differ.

1. *Several challenges from one query.* In the random-permutation model a fresh Keccak-f query's output is uniform
   (up to `Q/2^1600`), so the five 192-bit challenges of a wide draw are uniform and independent, and independent of
   the digest that becomes the next state (other lanes); the capacity stays Keccak-256's 512 bits. Drawing `β`, `γ` and
   the zerocheck's `c` from `α`'s query instead of three queries on the digest with no message between them changes no
   distribution the analysis uses: the bus needs `c` and `β` independent and uniform (SPEC-REC §1.4), and they are.
   The Fiat–Shamir composition (`formal/UniSound/UniSound/Fs128.lean`, `uniBound128`) charges every query the error of
   the round it may hit; a wide query may hit any of its challenges, so its error is their sum
   (`params/leanvm_univariate_params.py`, `rounds(.., "rec4")`).
2. *The ring map after `C2`'s commitment, `f_0 … f_3` with `t` and `f_4, f_5` after the values at `t`.* The ring switch's
   relation is `Σ_u W_f(u) q_flock(u) = target_f(s)`, a function of `q_flock` (in `C1`, bound by its root and answer
   before `α`), the slices `s` and the point `p` (in the stream before the map) and the map `f` alone: nothing the
   prover sends after the slices enters it, so drawing `f` later, and in two parts, leaves it a function of values
   fixed before `f`. For a dishonest `s` it is a nonzero polynomial `P(f_0, …, f_5)` of degree 1 in each `f_j` (the
   map's stages in tower order; 6/|E| in one draw). In two draws: write `P = Σ_m c_m(f_0 … f_3) f_4^{m_4} f_5^{m_5}`;
   some `c_m` is a nonzero polynomial of degree ≤ 4, so a `t`-query makes it vanish with probability ≤ 4/|E|, and
   otherwise a `ρ`-query makes `P` vanish with probability ≤ 2/|E|. The calculator charges the whole 6/|E| to both
   queries, over `C1`'s and `C2`'s lists. `t`'s identities do not involve the map.
3. *`λ` with `ρ`, `f_4`, `f_5`.* `ρ` combines relations that are all fixed when it is drawn but the ring relation's
   target, which `f_4, f_5` fix; those are independent of `ρ` (other lanes), so conditioned on them the combination
   errs with probability ≤ (relations − 1)/|E| as before. `λ` combines the three combined claims, fixed by `ρ`;
   conditioned on `ρ` it is uniform.

At the reference shape (`python3 -I params/leanvm_univariate_params.py`), bits after the lists:

| query | error | π1-rec3 | π1-rec4 |
|---|---|---:|---:|
| `α`'s call | bus `16 · side`, `γ` 60, zerocheck `2^22 − 1` (summed in π1-rec4) | 154.3, 174.0, 157.9 | 154.1 |
| `t`'s call | the identities' `Σ deg` (+ the map's 6 in π1-rec4) | 143.2 | 143.2 |
| `ρ`'s call | `ρ` 115 (+ `λ` 2 + the map's 6) | 160.4 (λ: 166.3, the map 177.3) | 160.3 |
| the batch's pairs | `8/2^160` | **132.3** | **132.3** |

The weakest is the batch's narrow pairs in both; with the three openings charged once (`269 · 2^-137` a query),
**128.79 bits as `Q/ε` at `Q = 2^64`** for both (400 signatures: 128.86). The Lean's uniform cap (every query's error
≤ `2^35/|E|`, lists `9,952²`, 128.49 bits) holds for π1-rec4's summed queries too (the largest, the batch's pairs, is
`2^35/|E|`; the `α` query's sum is below `2^26/|E|`).

**π2.** Its rounds are `main`'s: `N = 2^24`, `W`'s and `Q`'s lists, now four four-limb ports (the statement and the three
claim hashes; `(4N + 4)/|E|` in the copy argument instead of `4N + 3`). **128.93 bits** as `Q/ε` (`t`, the weakest:
140.92 after the lists, charged `4N/|E|` for the prover-filled empty slots of `Q`, `PI2.md` §2; 141.33 at `(3N − 1)/|E|`
as first computed). `params/leanvm_rec_params.py`.

**The circuit.** (a) The trimmed last round (§3) leaves every lane the caller reads constrained exactly as a whole
permutation constrains it: the χ formula of plane `y` reads only round 22's outputs `A_22` of the lanes `π` sends to
plane `y` and `D_23`, which rounds 0 … 22 (whole) and the D units constrain; the unmade planes' values are never read
(`Sponge` asserts the lanes asked for are made). (b) A wide challenge's packing reads three output lanes of the same
permutation, as `Low` reads three of the digest. (c) The three claims' hashes: a satisfied circuit carries the
Keccak-256 of each of π1's claims as the graph computes it, at Keccak-f[1600]; the contract binds each hash to its
payload, and a payload binds its claim by Keccak-256's collision resistance, which the frame of PCS claims assumes for
every declared claim (the EIP's own assumption), as for `C1`'s on `main`.

**The recursion**: π2's bound + π1-rec4's + the merge hazard (`2^16/|E|` a query): **127.86 bits** as `Q/ε` (127.70
with the Lean's cap on π1's rounds), as on `main`: two bounds near `2^-128.9` a query each, summed. It is below 128
because WHIR's `269 · 2^-137` a query is charged twice, once in π2's bound (which covers all eight openings) and again inside π1's; charged once, the sum would be 128.79 bits: a tighter composition proof, no code change.

## 6. The prover, A/B on h3

`tests/pipeline.rs` (`LEANVM_TRACE` the 128-signature trace, `PIPELINE_REPEAT=5`) through `bench.sh`'s protocol (8
threads, `LEANVM_NUM_THREADS=8 taskset -c 0-7`, under the bench lock, after `waitidle.sh`), `main`
(`/root/pcs-perf/final/all`) and this branch interleaved, 2026-11-11; each run's median of 5 passes:

| | `main` (runs 1–4) | this branch (runs 1–4) | median of the runs |
|---|---|---|---:|
| π1, proof to its stream | 0.861 0.863 0.863 0.863 | 0.863 0.862 0.862 0.871 | 0.863 → 0.862 |
| π1, its openings (π2's witness replayed meanwhile) | 0.184 0.184 0.185 0.184 | 0.178 0.177 0.178 0.184 | 0.184 → 0.178 |
| π2, its witness replayed | 0.014 0.009 0.014 0.014 | 0.014 0.009 0.014 0.014 | 0.014 → 0.014 |
| π2, proof | 0.789 0.791 0.789 0.793 | 0.790 0.791 0.789 0.791 | 0.790 → 0.790 |
| π2, openings | 0.785 0.785 0.788 0.789 | 0.786 0.790 0.787 0.788 | 0.787 → 0.788 |
| total | 2.622 2.628 2.627 2.631 | 2.617 2.620 2.621 2.647 | **2.628 → 2.621** |

Peak RSS 15.05 and 15.06 GB.

π1's prover draws differently (the same work); π2's proof and openings are at the same `N` with fewer selector pairs.
The witness plan has four templates instead of one; its replay stays near 0.01 s.

## Not taken, and why

- **A duplex sponge for π1's transcript** (the state kept in the permutation, no 32-byte state re-absorbed): 105
  Keccak-f against π1-rec4's 106 (only the values at `t`, 9 bytes past 21 blocks, gain), at the cost of leaving
  Keccak-256's chain, which π1's main line, its contract and the Lean's model share.
- **Narrow (160-bit) ring-map challenges, six in one rate**: would save no permutation over drawing `f_4, f_5` with `ρ`,
  and would weaken the ring switch.
- **More from the Keccak-f gadget.** `k1`'s spare role 15 (one position in 16) holds the constants; using it for other
  units needs two roles. Folding a later block's XOR into the round-0 χ rows needs 15 cells for 5 lanes (state, message,
  `D`), leaving no room for the `k1` rows' partial sums: about 0.1M positions at most (`xor` is 113,840 positions).
  The room π1-rec4 and the trimming make is enough.
- **A `Q` packing for `N = 2^25`.** `Q` is twelve nonzero slots of `N` (`h` 3, `q` 6, `P` 1, `q_P` 2): at `2^25` that is
  `2^28.58` words, and eight slots would need `q` below `N` or `h` without limbs. Not pursued: the room above suffices
  and `2^25` doubles π2's prover.
- **Shared absorption of the claims' encodings.** The claims share their point (`F`'s 23 coordinates are a prefix of
  `C2`'s 26, of `C1`'s 27), but each encoding starts with its own root and answer, so no Keccak state is shared; the
  coordinates' free bits could be shared across the three claims (about 28K positions), not needed.
- **D8v** (8 values at `t`: −192 B, −12.3K gas): a Keccak-f in rows of 8 needs about twice D16v's positions
  (`PI2.md` §9).
- **Fewer claims on `Q`**, **the frame's index byte**: as `PERF_GAS.md`.

What remains in calldata is π2's own (its commitments and values at `t`) and the statement: the next levers are
structural (fewer values at `t`, fewer claims).

## What the Lean would need (not updated on this branch)

`formal/` proves the protocols of `f96a7938` (π1-rec3; π2 with π1's three claims encoded by the contract). Beyond
`PERF_GAS.md`'s list (narrow reads, no selector, `C1`'s claim hashed):

- **π1-rec4** (`formal/UniKeccak*`, `UniKeccakSound`, `UniKeccakComplete`): the transcript's wide draws (the model's
  Keccak-256 with its rate's output, the challenges at lanes `1 + 3k …`), the ring map drawn with `t` and with `ρ`
  (the two-part Schwartz–Zippel of §5), `λ` with `ρ`, `β`, `γ` and the zerocheck's `c` with `α`; the per-query error
  is a sum (the cap `2^35/|E|` still holds, so `uniKnowledgeSoundnessKeccakRec3_closed`'s arithmetic carries over).
  The verifier transcription tests (`UniKeccakTest/Runner.lean`) on the rec4 vectors.
- **The graph** (`RecGraphKeccak`): the `Wide` node, `pi1GraphIsVerifierK` and `GraphsAgree` for π1-rec4.
- **The compiler** (`RecCircuit`, `rec-circuit-keccak`): `Wide` packings (rate lanes), the trimmed last round (a
  template per plane count, the unmade outputs, the free ends of `A_22`), three hashed claims and the fallback that
  drops the last; `DigestChecked`, `SetupRootChecked`, `IvChecked` re-evaluated.
- **The contract model** (`RecCompose`): the seed over three frame words, payloads 3 … 7 checked, no π1 element or
  root in calldata; `pi1rec3K_end` extended to the three claims' Keccak-256s, the extractor naming π1's claims by their
  hashes (with a collision term, or the frame's binding as an assumption). `pi2Bound` gains one port in the copy
  argument (`4N + 4`).
- `tests/lean_*.rs`'s outputs (graph, circuit, statement, π2's prover vectors) are π1-rec3's and stay so until then.
