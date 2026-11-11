# History

Superseded protocols and figures, by line and commit, newest first within each. The current ones are in
[`../AGENTS.md`](../AGENTS.md), "Numbers", and the design documents ([`README.md`](README.md)). The documents as they
were before this file was written (the per-round `PERF_*.md`, `EIP_CLAIMS.md`, `HIDING.md`, `SPEC-POINTS.md`,
`SPEC-FLOCK.md`, `flock/KECCAK.md`) are in git at `bbb0255c`; they hold every A/B table and per-phase timing that is
only summed up here.

Gas is without the 21,000 base; "frame transaction" is EIP-8141 under EIP-7976's floor without the per-frame costs;
"with the frame" adds the frame of PCS claims (`1 + 32` B a claim) and `pcs_gas` (5,000 + 1,000 a claim).

## Membership

| | hidden layouts | `f96a7938` (six claims; `formal/` proves it) | `866ba889` (four claims) | now (three claims) |
|---|---|---|---|---|
| commitments | 2 (`2^25`, `2^28`) + index | 4 (`W` `2^25`, `H` `2^27`, `Q` `2^28`, `G` `2^25`) + index | 2 (`W` `2^24`, `T` `2^28`) + index | 2 (`W` `2^24`, `T` `2^28`) + index |
| claims | 4, in 3 declared (claims on a layout) | 6 | 4 (W, wiring, copy and sum on `T`) | 3 (W, wiring, copy on `T`) |
| calldata | 253 B | 461 B (selector `0xde12c640`) | 301 B | 273 B (no selector) |
| frame of PCS claims | | 193 B | 129 B | 97 B |
| execution | 14,831 | 18,899 | 16,414 | 15,753 |
| standard price | | 40,315 | 32,270 | 29,649 |
| transaction (EIP-8141, `pcs_gas` in the floor) | 30,400 (with `PCS_OPEN`) | 52,856 (`64 · (461 + 193) + 11,000`) | 36,520 | 31,680 |
| code / deployment | | 6,667 B / 1,536,984 gas | 5,304 B / 1,242,838 gas | 4,866 B / 1,149,640 gas |
| prover | 1.7–2.2 s (M4 Max) | 2.8 s M4 Max (reduction 1.71, openings 1.08), 8.6 GiB; 2.29 s on 8 threads (1.49, 0.79); 0.91 s on 64 | 1.23 s on 8 threads (0.60, 0.62), 6.0 GiB; 0.63 s on 64 | 1.01 s on 8 threads |
| openings' sizes | | 291 / 278 / 313 / 335 / 288 / 311 KiB | 279 / 279 / 335 / 335 KiB | 278 / 276 / 336 KiB |
| soundness as `Q/ε` | | 125.4 bits (proved) | 126.0 bits | 126.4 bits |

At `f96a7938`, checking the claims declared cost 61 gas once (the frame's mode and scheme) and 43 a claim beyond its
`KECCAK256` (not re-measured; [`PCS_CLAIM.md`](PCS_CLAIM.md) gives the per-claim gas now).

### Membership at f96a7938

The protocol `formal/` proves (formerly `docs/membership/EIP_CLAIMS.md`): the first fit to the EIP's claims, one
point a claim, each a plain point evaluation of the whole committed multilinear. `m = log_rows + 2` (24 at `2^22`
rows):

| commitment | variables | data | claims |
|---|---|---|---|
| `W`, the witness (row polynomials, then their masks) | `m + 1` | `2^m + 16` | 1 |
| the wiring (public; root and out-of-domain answer in storage) | `m` | `2^m` | 1 |
| `H`: `h`'s limbs, with their blinding | `m + 3` | `3 (2^m + 8)` | 2 (the quotient point, the sum point) |
| `Q`: the copy quotient's limbs, `4·2^m` coefficients each | `m + 4` | `12·2^m` | 1 |
| `G`: the gate quotient | `m + 1` | `≈ 1.75·2^m` | 1 |

The quotient table `T` had `m + 6` variables (a coefficient, then a chunk's digit, kind (`h`, `q`, gate) and limb,
two bits each), over WHIR's `2^28` words, so it was committed as three subcubes of its nonzero chunks: `H` (kind `h`,
digit's high bit 0), `Q` (kind `q`), `G` (kind gate, limb 0, digit's high bit 0). A claim on `T` at `P` was
`w_H(P) H(P_H) + w_Q(P) Q(P_Q) + w_G(P) G(P_G)` (`protocol::quotient_parts`); the proof carried `Q`'s and `G`'s values
after `ρ`, the verifier derived `H`'s. Every commitment's out-of-domain answer was absorbed right after its root.
Further: the gate `V + X + C + Y C` (roles before the swap), `a_0..a_3` all revealed and batched by `ρ`; the public
bits in `h`'s sum through a `γ`-weighted indicator of 2,048 cells, so the copy quotient had four digits and the gates
their own quotient `G`; masks (multiples of `X_n`, the witness of degree `n + 15`) with random rows; `h` blinded by
eight coefficients a limb; seven revealed scalars past the roots. Zero knowledge: three groups of revealed scalars,
two affine and of full rank, the third not affine (the masks of `X` and `V` meeting in `G` through `Y·C`) and measured
over `GF(2)` (`hiding::group_a_*`, since removed), not argued.

**Before it, the hidden layouts**: claims on a layout with a gadget made the openings hide, checked by a `PCS_OPEN`
precompile; the EIP's format has no claims on a layout. `formal/`'s F3 (`QuotientSecurity/Hiding`, `formal/QuotientZk`)
went with them.

### Membership at 866ba889

From `f96a7938` (52,856 → 36,520 gas): the public values as eight pinned `K`-words by Horner rows and eleven anchors
(`γ` gone); no masks, 16 random rows of free cells; `h` blinded by two coefficients a limb; one quotient
`q = (h d d' + d + d') / Z + μ g`; one table `T` (`m + 4` variables) read by two claims, copy and sum (`h`'s top
coefficient, zero). The pole condition became structural here (anchors `(0, 1, 1)`, `(0, 3, 3)`; `Index::new`
asserts it): before, zero-knowledge rows carried soundness. ZK ranks 15 of 15 and 3 of 3. To now (36,520 → 31,680):
the sum's claim replaced by `T`'s layout (`x h` through `ζ = Z x`, −3,048), the gate's roles swapped so one witness
claim on a conic binds three row values (−1,536), no selector (−256).

## leanVM

| | before the PCS claims (π2v2, `PCS_OPEN`) | `f96a7938` (`formal/` states it) | `866ba889` | `bbb0255c` (π2v3) | now (π2v4) |
|---|---:|---:|---:|---:|---:|
| inner proof | π1-rec3 | π1-rec3 | π1-rec3 | π1-rec4 | π1-rec4 |
| π1's claims | encoded by the contract | encoded by the contract (24-byte challenges, selector) | `C1`'s hashed in π2's circuit (20-byte challenges, no selector) | all three hashed | all three hashed |
| π2's claims | | 5 | 5 | 5 (`W`, setup, `Q`'s identity, pushes, sum) | 4 (`W`, setup, `Q`'s identity, pushes) |
| calldata | 1,004 B (59 zero) | 1,101 B (61 zero) | 941 B (8 zero) | 577 B (4 zero) | 577 B (4 zero) |
| execution | 27,641 | 32,794 (33,740 at 400) | 37,406 | 31,524 (35,761 at 400) | 31,212 (35,452 at 400) |
| standard / floor | 42,997 (EIP-7623) / 64,256 | 49,678 / 70,464 | 52,366 / 60,224 | 40,708 / 36,928 | 40,396 / 36,928 |
| with the frame | | 99,912 | 89,672 (90,952 at 400) | 66,376 | 63,328 |
| contract | 13,219 B | 13.2 KB | 17,185 B, 205 selector pairs | 14,513 B, 176 pairs | 14,328 B, 176 pairs |
| π2's positions of `2^24` | 15,668,416 (93.4%) | | 16,482,912 (98.2%) | 16,413,312 (97.8%) | 16,413,312 (97.8%) |
| prover | 2.06 s M4 Max; 0.59 s on 64 threads | 3.7 s M4 Max (π1-rec3 1.41, π2 0.95, openings 1.25), 14.3 GB; 2.82 s on 8 threads | 2.62 s on 8 threads | 2.52 s on 8 threads | 2.29 s on 8 threads (π2's openings 0.73 → 0.51 s) |

The `866ba889` round, step by step from `f96a7938`: narrow challenges as 20 bytes (`Read::Narrow`, −56 B, 96,328),
no selector (−4 B, 96,072), `C1`'s claim hashed (`HASHED_CLAIMS = [0]`, −100 B, 89,672). Then (`perf2/leanvm-gas`,
−23,296 gas): π1-rec4, D16v's trimmed last rounds, all three claims hashed; the three hashes needed 17,972,736
positions (107.1%) with `866ba889`'s transcript, 16,664,192 with π1-rec4, 16,413,312 with the trimmed rounds.

π2v3 → π2v4 (`perf3/leanvm-claims`, −3,048 gas): `Q`'s sum claim (`h`'s top coefficient at `(1^m, 0, 0, y_0, y_1)`)
replaced by `Q`'s layout (`H = x h` in one slot, `q`'s digits on the slot bits' anti-diagonal, the fourth slot read
through `x² Z_V³`; `PI2.md` §7), one Q opening fewer. π2v3's slots: `h` at `(0, 0)`, its second digit (zero) at `(1,
0)`, `q`'s digits at `(0, 1)`, `(1, 1)`; `S` (zero) at limb code 3's `(0, 0)`, `P` at `(1, 0)`, `q_P` at `(0, 1)`,
`(1, 1)`; the identity's claim at the digit ratio `w_m` and kind ratio `ρ' = w_m / (c_h + w_m)`, the pushes' at
`(u, ρ, 1, 1)` (degree 1 in `ρ`); its empty slots argued at `4N/|E|` (`t`: 140.9 bits). Examined and not possible in
this PIOP: one claim for `Q`'s identity and pushes, fewer values at `t` (`PI2.md` §9).

### π1

- **π1-rec3 → π1-rec4** (2026-11-11): π1-rec3 drew every challenge by its own Keccak-256 call (70 calls, 116
  Keccak-f, 9,280 B of stream); π1-rec4 draws the challenges no message separates from one Keccak-f (60 calls, 106
  Keccak-f, the same 9,280 B), at the same 128.79 bits. π1-rec3 stays in the code (the Lean states it; its vectors and
  contract remain). Earlier shapes: π1-rec (`FsShape::Rec`: `α` and the zerocheck's eq point as powers), π1-rec2
  (narrow batch challenges), π1-rec3 (the batch two variables a round: 14 challenges instead of 27; π1's claims 408 B
  of calldata instead of 720, 744 at 400 signatures).
- **π1 alone as a contract with `PCS_OPEN`** (claims on layouts; `c` the price of a claim): 7,828 B / 222,928 at 32
  signatures, 8,020 B / 230,985 (358,957 transaction at `c = 0`) at 128, 8,116 B / 236,976 at 400; 1,000 signatures
  (infeasible, `C1` over `2^28`) 8,308 B / 247,340. A linker (since removed) cut the 400-signature contract into four
  EIP-170 contracts (252,591 execution).
- **π1's prover** before the 8-thread figures: M4 Max, π1-rec3 at 128 signatures 2.72 s cold (6.75 GB), 3.65 s warm;
  the main line at 400 signatures 6.61 → 4.69 s with the round-1 table kernel (14.4 GB); EPYC 9355P on 64 threads 0.94
  → 0.40 s (2026-11-09). leanVM `9d50c92a3`'s own prover: 0.28 s on the Mac at 128 signatures, 0.19 s on the EPYC.
- **Opening versions.** Version 2 (the layout openings) and version 3 (the recursion's WHIR ladder: deeper levels at
  rates `1/4, 1/8, …`, about half the opening time of version 1, proofs about 27% longer) were removed with the PCS
  claims, whose one version is leanVM's ladder.

### π2

- **π2v2 with `PCS_OPEN`**: claims checked by a precompile, encoded as `root word, layout word, k, k × (point, value)`;
  π2's three stacks opened once each (the claims on one commitment in one opening). 21 blocks, 133 selector pairs at
  128 signatures; the one-digit greedy block padding gave 70 blocks and 429 pairs before the look-ahead `pad_counts`.
  The prover on 64 threads: prove 0.196 s, open 0.104 s (0.048 s at version 3), pipeline 0.69 s (0.59 s at version 3).
- **π2v1** (transcript `leanvm-rec-pi2v1`, up to commit `0c6fcf3`, opening version 2): the ports' fingerprints pushed
  to outside tags inside the copy argument, `P` kept inside `d_push` (identity below `5N`, `q` below `4N`), `Q` of
  `15N` words (`m + 5` variables), no `s`; 980 B, 28,325 execution, 128.93 bits as π2v2. π2v1 → π2v2: prove 0.321 →
  0.255 s, peak 8.5 → 7.3 GB, 24 B more calldata, 684 less execution.
- **D32v** (rows of 32, 51,200 positions a Keccak-f): implemented, then removed; 1,388 B and 51,940 execution on the
  real 128-signature π1-rec3 before the PCS claims.

## Provers

All on the AMD EPYC 9355P (h3) unless said otherwise; every speedup kept the proofs byte for byte
([`PERF_PROVER.md`](PERF_PROVER.md)).

| branch (base) | membership | leanVM pipeline |
|---|---|---|
| `perf/membership-prover`, `perf/leanvm-prover` (`f96a7938`) | 0.91 → 0.53 s on 64 threads, 1.34 → 0.81 s on 16, M4 Max 2.74 → 2.19 s; peak 8.71 → 6.83 GiB | 0.91 → 0.85 s on 64, 1.55 → 1.40 s on 16, M4 Max 3.7 → 3.29 s |
| `perf/provers-combined` | 0.52 s (64), 0.83 s (16) | 0.84 s (64), 1.41 s (16) |
| `perf2/provers` (`866ba889`, 8 threads) | 1.235 → 1.158 s (four claims) | 2.629 → 2.511 s, peak 15.05 → 15.59 GB |
| `perf2/provers-main` (`fd525b68`, 8 threads) | 1.033 → 1.006 s | 2.617 → 2.501 s |

Before the PCS claims the pipeline took 2.06 s on the M4 Max and 0.59 s on 64 threads; π2 on the M4 Max before the
prover's optimisations, 4.4 s + 1.7 s openings and 3.8 s of witness, 9.8 GB.

## Removed lines

- **SLH-DSA proof of concept** (`crates/slh_dsa`, `SPEC-FAST.md` in git): the Keccak-f Flock block and its structured
  terminal were designed for it (milestones M1, M3; the lane circuits of its §4.3, kept in
  `crates/membership/quotient/src/circuit.rs` and used by nothing else, were removed later). Its §4.5 linked the block's ports to a membership-style witness by a quotient `Q_link`; the Keccak VM
  uses `Q_W`'s copy identities instead.
- **The BLAKE2s VM** (leanVM `42422001`'s BLAKE2s block and π1 over it): removed from the Rust and from `formal/`
  (`Lv42`, `UniStatement` keep comments of that era). `formal/README.upstream.md` (deleted) was leanVM's
  `formal/quotient` README for the upstream full-adder circuit, `QuotientSecurity`'s starting point.
- **`formal/Compose`'s layout-opening statements** and `Completeness`'s own end theorems stay built, superseded for the
  end theorems by `SoundPcs.knowledgeSoundness_deployed_pcs` and `EndToEnd`.

## Old document names

Lean comments (not edited) and some committed vectors' headers cite the documents by their names at `f96a7938`:

| old | now |
|---|---|
| `docs/membership/HIDING.md` | [`membership/PROTOCOL.md`](membership/PROTOCOL.md), "Zero knowledge" (of the current protocol; `f96a7938`'s: above) |
| `docs/membership/EIP_CLAIMS.md` | "Membership at f96a7938", above |
| `docs/membership/PERF_GAS.md`, `PERF_GAS2.md` | [`membership/PROTOCOL.md`](membership/PROTOCOL.md), [`LEAN_PORT.md`](LEAN_PORT.md) |
| `docs/leanvm/univariate/SPEC-FLOCK.md`, `docs/leanvm/flock/KECCAK.md` (§4.2, §4.5, M1, M3) | [`leanvm/univariate/FLOCK.md`](leanvm/univariate/FLOCK.md) ("The block", "The ports", "The structured terminal") |
| `docs/leanvm/rec/SPEC-POINTS.md` (§2.4, §6) | [`leanvm/univariate/SPEC.md`](leanvm/univariate/SPEC.md) §14 (§14.3); [`leanvm/rec/SPEC-REC.md`](leanvm/rec/SPEC-REC.md) §12 item 8 |
| `docs/leanvm/rec/PERF_GAS.md`, `PERF_GAS2.md` | [`leanvm/rec/SPEC-REC.md`](leanvm/rec/SPEC-REC.md) (§2.4.1, §2.4.5, §2.4.6, §5, §12); π1-rec4: [`leanvm/univariate/SPEC.md`](leanvm/univariate/SPEC.md) §14.4 |
| `docs/membership/PERF_PROVER.md`, `docs/PERF_PROVER2.md`, `docs/leanvm/rec/PERF_PROVER.md` | [`PERF_PROVER.md`](PERF_PROVER.md) |
