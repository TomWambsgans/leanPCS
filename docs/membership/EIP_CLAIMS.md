# The membership line under the EIP's PCS claims

The membership proof's claims are the EIP draft's: `version || n || commitment(root, ood) || point || value`, one
point a claim, each a plain point evaluation of the whole committed multilinear (`crates/pcs_claim`,
[`docs/PCS_CLAIM.md`](../PCS_CLAIM.md)). This note records how the protocol was fitted to them and what it costs.

## Tables and claims

`m = log_rows + 2` (`m = 24` at `2^22` rows):

| commitment | variables | data | claims |
|---|---|---|---|
| `W`, the witness (row polynomials, then their masks) | `m + 1` | `2^m + 16` | 1 |
| the wiring (public; its root and out-of-domain answer in the contract's storage) | `m` | `2^m` | 1 |
| `H`: `h`'s limbs, with their blinding | `m + 3` | `3 (2^m + 8)` | 2 (the quotient point, the sum point) |
| `Q`: the copy quotient's limbs, `4·2^m` coefficients each | `m + 4` | `12·2^m` | 1 |
| `G`: the gate quotient | `m + 1` | `≈ 1.75·2^m` | 1 |

The quotient table `T` has `m + 6` variables: a coefficient, then a chunk's digit, kind (`h`, `q`, gate) and limb,
two bits each. Its slots exceed WHIR's `2^28` words, so it is committed as three subcubes of its nonzero chunks:
- `H` fixes the kind to `h` and the digit's high bit to 0;
- `Q` fixes the kind to `q`;
- `G` fixes the kind to gate, the limb to 0 and the digit's high bit to 0.

A claim on `T` at `P` is `w_H(P) H(P_H) + w_Q(P) Q(P_Q) + w_G(P) G(P_G)`. Each part's point is the free coordinates
of `P`, and its weight the `eq` of the fixed ones (`protocol::quotient_parts`). The proof carries `Q`'s and `G`'s
values after `ρ`. The verifier derives `H`'s from the relation, at the cost of two more inverses in its one batched
inversion. Every commitment's out-of-domain answer is absorbed into the transcript right after its root.

Revealing `Q`'s and `G`'s values on their own, instead of one combination, needs randomness of their own. The random
rows and the blinding of `h` provide it ([`HIDING.md`](HIDING.md)).

## Cost

Measured on the M4 Max (load average about 7 during the runs: another build was running):

| | before (hidden layouts) | now |
|---|---|---|
| commitments | 2 (`2^25`, `2^28`) + index | 4 (`2^25`, `2^27`, `2^28`, `2^25`) + index |
| claims | 4, in 3 declared | 6 |
| prover | 1.7–2.2 s | 7.4 s (median of 3: reduction 4.1 s, openings 3.3 s), 8.6 GiB |
| calldata | 253 B | 461 B |
| execution | 14,831 | 18,899 |
| transaction (EIP-8141, `pcs_gas` in the floor) | 30,400 | **52,856** (floor-bound: `64 · (461 + 193) + 11,000`) |

The openings are plain leanVM WHIR, standing in for the EIP's ZK-WHIR. The hidden layouts that made them hide need
claims on a layout, which the EIP's format does not have.
