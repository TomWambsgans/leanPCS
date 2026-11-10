# The membership line under the EIP's PCS claims: design and cost

Status: design analysis (Phase D), **not implemented**. The code still has the hidden layouts of
[`HIDING.md`](HIDING.md). This note says what moving the membership proof to the EIP draft's claims would take:
`version || n || commitment(root, ood) || point || value`, one point per claim, a plain point evaluation of the whole
committed multilinear, no layout ([`docs/PCS_CLAIM.md`](../PCS_CLAIM.md)). It finds that, at the circuit's
`2^22` rows, keeping the openings zero-knowledge costs far more than the "about 2×" first estimated. A decision is
needed before implementing.

## 1. What the reduction leaves today

`m = log_rows + 2 = 24` (`n = 2^24` cells), `protocol::reduce`:

| table | variables | data | claims today |
|---|---|---|---|
| witness `T_w` (cells, then 16 mask words) | `m + 1 = 25` | `2^24 + 16` | 1 |
| wiring (public, the index) | `m = 24` | `2^24` | 1 |
| quotient `T_q` | `m + 6 = 30` | ≈ `13.75 n` ≈ `2^27.78` | 2 (the quotient point, the sum point) |

`T_q`'s 64 chunks of `2^m` are indexed by 6 bits: digit `d` (2), kind (2: `h`, `q`, gate), limb `e` (2). Seventeen
are nonzero (`quotient_chunks`):
- `h_e` (3 chunks);
- `q_{d,e}` for `d < 3`, plus the spill `q_{3,e}` of 9,280 words (3 × 4);
- the gate's `g_0` (`n`) and `g_1` (`3n/4 + 64`).

The claim at the quotient point weighs chunk `c` by `eq(digit, kind, limb coordinates; c)` (coordinates `u_m,
u_{m+1}`, `w_m/copy`, `ρ`, and the constants `y_0, y_1`). Its value is computed by the verifier from public data.
That is the point: no evaluation of `h`, `q` or the gate quotient is ever revealed on its own.

## 2. Hiding forces a quarter, and the quarter does not fit

[`HIDING-v2`] shows that with point claims a random half leaks, wherever its Boolean coordinate sits. The smallest
fix is a random **quarter**: two Boolean coordinates, lane bit 0 and the top in-lane bit, with `T` on the `1` side
of both. A committed `f` then has `n_T + 2` variables. WHIR (and `pcs_claim`) commits at most `2^28` words, so a
hidden table holds at most `2^26` words of data.
- `T_w`: 2^25 slots, so 2^27 committed. Fits.
- `T_q`: 2^27.78 words of data, ×4 = 2^29.8. It must be **split**. As a point-evaluable table it is 2^30 slots, so
  even its slots exceed the limit.

## 3. Splitting `T_q` reveals each part's value, which breaks zero knowledge

A part is a committed table, and its claim's value is public. Today one combined value of `T_q` is revealed, and it
is a function of public data. After a split, every part reveals its own:
- `h(t)`;
- a digit chunk `q_d(t)`, or a limb `q_e(t)`;
- `g_0(t)`, `g_1(t)`.

These are fresh evaluations of witness-dependent polynomials at a random point, so not simulatable. The witness masks
only randomize `T_w`'s `a_j`. **Any split of `T_q` without a PIOP change is sound but not zero-knowledge.** (This
was the open item "masking of any split part's claim value" of the draft. It fails.)

### The fix: blinding with overlap

The fix is standard PLONK-style blinding:
- `h_e' = h_e + Ŵ_m·b_e`. Here `Ŵ_m = X_n` in the novel basis vanishes on the cells, and `b_e` is 3 random
  coefficients. `q` absorbs the change.
- The chunks of `q` and of the gate quotient overlap by 3 coefficients: `q_d' = q_d − β_d + X_n β_{d+1}`.

Then every part's value is uniform subject to the one public linear relation the verifier checks, so the parts are
simulatable. But a chunk now holds `n + 3` coefficients, so every chunk table has `m + 1` variables, and a hidden part
(≤ 2^26 data) holds two chunk tables. The verifier combines the parts with explicit weights (`X_{dn}(t)`, the limb
and kind weights) instead of `T_q`'s `eq` structure. So any two chunk tables may share a part, at the cost of one
`E` division per part, batched into the reduction's one inversion.

## 4. The designs, and what they cost

Measured: one `pcs_claim` commitment and opening of `2^28` words on the M4 Max takes 1.02 s + 1.48 s, with a peak
RSS of 7.4 GiB (`cargo run --release -p pcs_claim --example open_timing -- 28`); at `2^26`, 0.38 s + 0.36 s and
1.9 GiB. Gas per claim:
- 1,000 `PCS_CLAIM_GAS`;
- about 500 for packing and `KECCAK256` (`docs/PCS_CLAIM.md`: 501 at n = 22, 597 at 28);
- 32 bytes of frame data;
- 56 bytes of calldata for each proof commitment's root and OOD answer.

Under EIP-8141 the floor (64 gas a byte of calldata and frame data, plus `pcs_gas`) binds once calldata passes about
1 KB.

| | today | A: EIP claims, **not ZK** | B: EIP claims, ZK (quarter + blinding) |
|---|---|---|---|
| proof commitments | 2 (`2^25`, `2^28`) | 4: `T_w` `2^25`, `H` `2^26`, `Q` `2^28` (all `q`), `G` `2^25` | 9: `T_w` `2^27`, 7 parts `2^28`, a spill part `2^18` |
| claims | 4 in 3 | 6 (witness, wiring, `H`, `Q`, `G`, sum on `H`) | 12 (witness, wiring, 8 quotient parts, sum on 2 parts) |
| prover, openings (est.) | 0.76 s | ≈ 4 s (`Q` 2.5 s, `H` 0.7 s, `T_w` and `G` 0.4 s each) | ≈ 21 s, and > 55 GiB if every codeword is kept to the end (it does not fit in 48 GB, so recommit at opening: ≈ 29 s) |
| calldata | 253 B | ≈ 470 B (+3 commitments, 3 part values) | ≈ 1,000 B |
| transaction gas (est., EIP-8141 with `pcs_gas` in the floor) | 30.4 k (floor-bound: (253 + 97) · 64 + 8,000) | ≈ 53 k (floor-bound: ≈ 663 B · 64 + 11,000) | ≈ 105 k (floor-bound) |
| zero knowledge | yes (HIDING.md, Lean) | **no** | yes, new argument (HIDING-v2 §5 plus the blinding), Lean to redo |

A's split, with parts as aligned subcubes of `T_q`'s chunk space:
- `H` = kind `h`, digit 0, free limb bits, 3 chunks: `2^26`.
- `Q` = kind `q`, free digit and limb bits, 12 slots including the spill: `2^28`.
- `G` = kind gate, free digit bit 0: `2^25`.

The verifier recombines with `eq` weights and takes the parts' values from calldata, one of them derived. Soundness is
as today, with the OOD answers binding each commitment.

## 5. Options

1. **B** keeps the EIP's format and zero knowledge. It is about 4× today's gas, with a prover of about 20–30 s that
   needs about 50 GB or recommitting. It is a PIOP change (the blinding), a new hiding proof (HIDING-v2 §5 extended
   to the blinded parts) and a new Lean ZK proof.
2. **A** keeps the format and drops zero knowledge for membership: about 1.75× gas, prover about 4–5 s. The benchmark
   row is then "Merkle membership", not "zero-knowledge membership".
3. **A smaller ZK statement** that fits B cheaply: a shallower tree or fewer rows. Each halving of the rows halves
   every table.
4. **Keep a layout in the claim** (the variant the user declined): today's hidden layouts, about today's costs.

[`HIDING-v2`]: the draft at `scratchpad/HIDING-v2.md` in the session that wrote this note. Its §5 (the quarter's
proof) is reusable for B's parts. Its §7 (cost) understated the problem, because it did not account for the per-part
values.
