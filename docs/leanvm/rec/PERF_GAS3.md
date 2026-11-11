<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# The recursion's gas, round 3: the copy sum from `Q`'s layout (branch `perf3/leanvm-claims`)

> Below, `main` is commit `bbb0255c` (after [`PERF_GAS2.md`](PERF_GAS2.md)'s round and the prover rounds), and "this
> branch" the branch this note describes. Every figure is measured on h3 (AMD EPYC 9355P) unless marked modelled. The
> Lean in `formal/` is not updated (it proves `f96a7938`'s protocol): see "What the Lean needs".

Benchmark 2 of the EIP draft: π2's contract verifying π1-rec4 of 128 leanXMSS signatures, as an EIP-8141 frame
transaction under EIP-7976's floor, with its frame of PCS claims (`1 + 32` bytes a claim) and the PCS gas (`5,000 +
1,000` a claim) on both sides. The floor binds: `64 · (calldata + frame) + 5,000 + 1,000 · claims`, so a claim costs
`64 · 32 + 1,000 = 3,048` gas and a value of `E` revealed `64 · 24 = 1,536`. On `main`: `64 · (577 + 257) + 13,000 =
66,376`, eight claims (π1's three, π2's five: `W`, the setup, and three on `Q`: the identity, the pushes, the copy
argument's sum).

This branch removes `Q`'s sum claim: π2 is **π2v4** (transcript `leanvm-rec-pi2v4`), whose `Q` is laid out so that the
identity's claim alone forces `Σ_V h = 0`. The two other levers examined (one claim for `Q`'s identity and pushes,
fewer values at `t`) are not possible in this PIOP; the reasons are below.

## Results

`tests/pi2_real.rs` (`real_end_to_end`, `real_gas`; `PI2_VECTOR=keccak_rec4` at 400 signatures):

| | calldata | execution | standard / floor (PIOP frame alone) | claims | with the frame and PCS gas |
|---|---:|---:|---:|---:|---:|
| `main`, 128 signatures | 577 B (4 zero) | 31,524 | 40,708 / 36,928 | 8 | **66,376** (floor; standard 57,820) |
| this branch, 128 signatures | 577 B (4 zero) | **31,212** | 40,396 / 36,928 | **7** | **63,328** (floor; standard 55,996) |
| `main`, 400 signatures | 577 B (5 zero) | 35,761 | 44,933 / 36,928 | 8 | 66,376 (floor; standard 62,033) |
| this branch, 400 signatures | 577 B (5 zero) | 35,452 | 44,624 / 36,928 | 7 | 63,328 (floor; standard 60,224) |

**−3,048 gas (−4.6%)** at both shapes: `64 · (577 + 225) + 12,000 = 63,328`, the frame `1 + 7 · 32 = 225` bytes. The
floor still binds, with 7,332 gas of execution to spare at 128 signatures (3,104 at 400).

| gas at 128 signatures | `main` | this branch |
|---|---:|---:|
| statement (32 B), frame index (1 B), frame header (1 B), `5,000` | 7,176 | 7,176 |
| `W`'s and `Q`'s commitments (2 × 56 B) | 7,168 | 7,168 |
| values at `t` (18 × 24 B: 16 fold values, `ξ`, `s`) | 27,648 | 27,648 |
| π1's three claims (frame word and `1,000` each) | 9,144 | 9,144 |
| π2's claims | 5: 15,240 | **4: 12,192** |
| **total** | **66,376** | **63,328** |

- **The contract**: 14,328 B of code at 128 signatures (14,513 on `main`), 16,287 B at 400 (16,472), under EIP-170's
  24,576; 798 `FIELD_MUL`s. It encodes four claims (π2's) and finds them at payloads 3 … 6. Execution by phase (128
  signatures, `real_gas`): indicators 8,812 + 913, push formulas 8,558, the claims written, hashed and checked 3,422
  (one claim fewer), identity and claims 2,897 (the two claims' new coordinates), the fold 2,336, the inversion
  1,208, digits 832 (`w_{m+1}` no longer needed), transcript 797, calldata reads 776, ports 512, setup 123, entry 26.
- **The prover** (8 threads, `bench.sh`'s protocol): §4. One opening of `Q` (`2^28` words) fewer; one pass of
  `quotient::protocol::mul_x` over `h`'s three limbs more.
- **Soundness** (§3; `params/leanvm_rec_params.py`): π2 **128.93 bits** as `Q/ε` at `Q = 2^64` (`main`: 128.93), its
  weakest round `t` at 140.60 bits after the lists (`main`: 140.92); the recursion 127.86 (`main`: 127.86).

## 1. The layout: `H = x h`, `q`'s digits on the anti-diagonal

`Q` is sixteen slots of `N = 2^m` words, a point of its stack `(u_0 … u_{m-1}, z_0, z_1, y_0, y_1)`: the position
coordinates, two slot bits `b_0, b_1`, the limb's two bits. With `u_l = w_l / (1 + w_l)` (`w_l` the Cantor digits of
`t`) a slot holding a polynomial `f` of degree below `N` (novel basis) is worth `(t / Z) f(t)`, `Z = w_m(t)` (`Z_V =
w_m`); the slot bits weigh `(1 + z_j, z_j)`, ratio `r_j = z_j / (1 + z_j)`; the limbs `(y_0, y_1)` of
`verifier::extension` weigh limb code `l` by `scale · Y^l`, so limbs 0..2 make an element of `E` and limb code 3 weighs
`Y³`.

| slot `b_0 + 2 b_1 + 4 limb` | limbs 0..2 (`E`) | limb code 3 (`K`) |
|---|---|---|
| `(0, 0)`: slots `0, 4, 8` / `12` | `H = x h` (one digit) | `P` |
| `(1, 0)`: slots `1, 5, 9` / `13` | `q`'s digit 0 | `q_P`'s digit 0 |
| `(0, 1)`: slots `2, 6, 10` / `14` | `q`'s digit 1 | `q_P`'s digit 1 |
| `(1, 1)`: slots `3, 7, 11` / `15` | `G`, zero | `S`, zero |

(`main`: `h` at `(0, 0)`, its second digit (zero) at `(1, 0)`, `q`'s digits at `(0, 1)`, `(1, 1)`; `S` (zero) at limb
code 3's `(0, 0)`, `P` at `(1, 0)`, `q_P` at `(0, 1)`, `(1, 1)`. `verifier::{h_slot, q_slot, P_SLOT, QP_SLOT,
EMPTY_SLOTS}`.) A two-digit polynomial's digits are contiguous slots (`4 l + 1`, `4 l + 2`), as the prover's transforms
write them.

**The identity's claim** (no randomness but `t`): the copy identity at `t` is `c_h h(t) + Z q(t) = R(t)`, `c_h =
d_pull(t) d_push(t)`, `R = (1 + 1_S)(d_pull + d_push) + T` (`R(t) = num_1 / R_d`, PI2.md §2). Times `t / c_h`:
`H(t) + a q(t) = (t / c_h) R(t)` with `a = t Z / c_h`. The claim takes `r_0 = a`, `r_1 = b = a Z`, so that `q`'s digits
weigh `a` and `a Z` (`a q(t)`), `H` weighs 1, and `G` weighs `a b = t² Z³ / c_h²`. At limb code 3 the same ratios
weigh `P + a q_P(t) + a b S(t)`. Its point is `(u, z_0, z_1, y_0, y_1)`, `z_0 = t Z / Y_1`, `z_1 = t Z² / Y_2`, `Y_1 =
c_h + t Z`, `Y_2 = c_h + t Z²` (so `1 + z_0 = c_h / Y_1`, `1 + z_1 = c_h / Y_2`), and its value (`G`, `S` zero, `P(t) =
s`, `Z q_P(t) = s + P_v(t) = num_3 / B`):

`scale · t · c_h · (t num_1 B + Y³ R_d (c_h s B + t num_3)) / (Z Y_1 Y_2 R_d B)`.

**The pushes' claim** (randomness `ρ`, drawn after `s`): limb code 3 alone (`y = (1, 1)`), `z_0 = ρ`, `z_1 = ρ Z / Y_3`,
`Y_3 = 1 + ρ + ρ Z`: ratios `a' = ρ / (1 + ρ)` and `b' = a' Z`, so it reads `P(t) + a' q_P(t) + a' b' S(t)`; its value
`t (1 + ρ)((1 + ρ) Z s B + ρ num_3) / (Z² B Y_3)`.

The verifier (`verifier::reduce`) inverts `R_d Y_1 Y_2 B Z Y_3 · c_h D_n` once (required nonzero; `main`: `R_d Y w_{m+1}
B · c_h D_n`), and the digits' inverses down from `1/Z`; `w_{m+1}` is no longer computed.

**The honest prover** (`prover::prove`): `h` as before, into `G`'s slots meanwhile (its values, then its coefficients,
which `quotient_on_extension` reads for `q` as before); then `H = x h` by `quotient::protocol::mul_x` (the novel basis'
product by `x`, no multiplication: coefficient `j ≥ 1` is `h[j − 1] + h[j + low(j) − 1]`), its coefficient `N` (`h`'s
top one, zero since `Σ_V h = 0`) dropped, and `G`'s slots zeroed. `q`, `P`, `q_P` as before. **No fix-up and no new
completeness condition**: unlike the membership's `x h` ([`../../membership/PERF_GAS2.md`](../../membership/PERF_GAS2.md)
§1), no polynomial must have a coefficient zeroed, because `q` and `q_P` are read through `Z` itself (their digits on
the anti-diagonal), not through `Z x`.

## 2. What `t` and `ρ` establish

Fix `W`'s list element `w` (committed before `α, β, γ`), `α, β, γ`, and `Q`'s list element: sixteen polynomials of
degree below `N`, all the prover's. Name them `H_l, A_{0,l}, A_{1,l}, G_l` (limb `l < 3`, slots `4 l … 4 l + 3`), `P,
B_0, B_1, S` (slots `12 … 15`); `H = Σ Y^l H_l`, `A = A_0 + Z_V A_1` (degree below `2N`), `G = Σ Y^l G_l`, `q_P = B_0 +
Z_V B_1`. Let `D = (α + w + βx)(α + P + κ + βσ)` and `R = (1 + 1_S)(d_pull + d_push) + T` with `d_push = α + P + κ +
βσ`, as polynomials (`P` the committed one). Every one is fixed before `t`.

1. **`W`'s claim and the setup's** are `main`'s: the row's cells are `w`'s at `t` (but with probability `15/|E|` over
   `ρ`), and `ξ = κ(t) + β σ(t)` (the setup honest, fixed before `β`).
2. **The pushes' claim.** Times `(Z / t) Y_3` (nonzero: the verifier requires `Y_3 ≠ 0`) it reads `(1 + ρ)² e_1 + ρ (1 +
   ρ) e_2 + ρ² e_3 = 0`, `e_1 = P(t) − s`, `e_2 = q_P(t) − (s + P_v(t)) / Z`, `e_3 = Z S(t)`: a polynomial in `ρ` of
   degree 2 whose coefficients are `e_1`, `e_2`, `e_1 + e_2 + e_3`. The `e_i` are fixed before `ρ` (`s` and the cells
   are sent before it), so unless all three are zero it holds with probability at most `2/|E|`. So `P(t) = s`,
   `Z q_P(t) = P(t) + P_v(t)` and `S(t) = 0`.
3. **The identity's claim.** With 2., its limb code 3 share is the verifier's (`P(t) + a q_P(t) + a b · 0`), and
   `c_h = d_pull(t)(α + s + ξ) = D(t)`, `R`'s value the verifier's `num_1 / R_d = R(t)`. What remains is `H(t) + a
   A(t) + a b G(t) = (t / c_h) R(t)`, `a = t Z / c_h`, `a b = t² Z³ / c_h²` (the verifier requires `c_h ≠ 0`); times
   `c_h²`: `I(t) = 0` for the polynomial

   `I = D² H + x Z_V D A + x² Z_V³ G + x D R`  (characteristic 2),

   of degree below `5N` (`D` below `2N − 1`, `H` below `N`, `A` below `2N`, `G` below `N`, `R` below `2N`).
4. **`t`.** `I` and `J = Z_V q_P + P + P_v` (degree below `3N`) are fixed before `t`; both vanish at `t` (3. and 2.). If
   either is not the zero polynomial, that happens with probability at most `5N/|E|` (the larger degree; `main`: `4N`).
   So `I = 0` and `J = 0` as polynomials.
5. **The sum.** `J = 0` gives `P = P_v` on `V_m`, in particular `P(0) = P_v(0)`. At `x = 0`, `I = 0` reads `D(0)² H(0)
   = 0`. `D(0) = (α + w(0))(α + P_v(0) + κ(0) + β σ(0))` is the product of the copy argument's pull and push
   denominators at position `0 = ω_0` (at a hole, `P_v(0) = w(0)`, `κ(0) = 0`: the same linear form), which the copy
   argument's round already requires nonzero (PI2.md §7: "a denominator on `V_m` vanishes", `2N/|E|` of its `(4N +
   4)/|E|`). So `H(0) = 0`: `h = H / x` is a polynomial of degree at most `N − 2`, and a polynomial of degree below `N −
   1` sums to zero on the `F_2`-subspace `V_m` of `N` points (only `x^(N−1)` has a nonzero sum). **`Σ_V h = 0`.**
6. **The identity on `V_m`.** `I / x = D² h + Z_V D A + x Z_V³ G + D R = 0`; on `V_m` (`Z_V = 0`) `D (D h + R) = 0`, and
   `D ≠ 0` on `V_m` (as 5.), so `h D + R = 0` on `V_m`: `h = R / D` there.

5. and 6. are exactly what `main`'s identity's and sum's claims gave (the identity `h D + R = q Z_V` as polynomials, so
`h = R / D` on `V_m`, and `Σ_V h = 0`), with the committed `h` replaced by `H / x`: PI2.md §7's ports' lemma and the
copy argument's soundness apply unchanged from there (they use `h` on `V_m` and its sum only).

**Why `G` must weigh `x² Z_V³`, not `Z_V`** (the negative control). The fourth `E` slot is the prover's, whatever the
layout. If `q`'s two digits sat at one slot bit (contiguous slots of one kind, as `main`'s `q`), `H` and `G` would sit
at the other, and `G` would weigh `Z` against `H`: `I' = D H + x Z_V A + D Z_V G + x R`. Then a dishonest port (`Σ_V h =
σ ≠ 0`, `h D + R = q Z_V` kept) passes: `H = x h + σ Z_V` (`x h` without its coefficient `N`; it is `x` times `h + σ
L_0`, `L_0 = (Z_V / x)` the Lagrange polynomial of `0`, `(Z_V / x)(0) = w_m'(0) = 1`) and `G = σ` give `I' = x(h D + q
Z_V + R) + σ D Z_V + σ D Z_V = 0`. In this layout `G` weighs `x² Z_V³ / D` against `H`, so the same `G` leaves `I = σ
Z_V (D + x Z_V)² ≠ 0`; in general `x² Z_V³ G` vanishes to order 1 in `x` past `Z_V`'s, so `G` moves neither `H(0)` nor
`h` on `V_m`. (This is the membership's point that the digit-1 slot must be read through `Z x`, reached without a
second digit for `H`: the slot that would be `H`'s second digit is `G`, at `a b`.)

**The other weights.** `H` must be one slot (a second digit of `H` would add `Z_V H_1 / x`-terms that move `h(0)`, as the
membership's rejected `x h` read through `Z`); `q`'s digits must have ratio `Z` (they are read whole); `q`'s ratio to
`H` is `a = t Z / c_h`. Three entries of the rank-one `2 × 2` slot-bit tensor are thereby fixed, and the fourth is
`G`'s, `a b`. The anti-diagonal is the only placement of `q`'s digits that leaves `G` diagonal to `H`.

**Error terms** (`params/leanvm_rec_params.py`, `pi2_rounds`; `N = 2^24`, lists `L_W` 9,952, `L_Q` 3,564; bits alone,
then after the union):

| round | `main` (π2v3) | this branch (π2v4) |
|---|---|---|
| the copy argument `(α, β, γ)` | `(4N + 4)/2^192`: 166.0, 152.7 | unchanged (`D(0) ≠ 0` is among its denominators) |
| `t`: the identities | `4N` (with the prover-filled empty slots): 166.0, 140.9 | **`5N`** (`I` above): 165.7, **140.6** |
| `ρ`: `W`'s fold | `15`: 188.1, 163.0 | unchanged |
| `ρ`: `Q`'s ρ claim | `3` (the identity, pushes, definition): 190.4, 165.3 | `2` (pushes, definition, `S`): 191.0, 165.9 |
| the openings, charged once | `269 · 2^-137` a query (eight) | the same (seven) |

π2: **128.93 bits** as `Q/ε` at `Q = 2^64` (the openings dominate, as on `main`); the recursion (π2 + π1-rec4 + the
merge hazard): **127.86** (127.69 with the Lean's cap on π1's rounds; `main` 127.70). `main`'s "empty slots" argument
(PI2.md §2: `h`'s second digit absorbed into the quotient, `S` at `P`'s kind forced zero by `w_m`'s degree) is replaced
by 2.–6.: `G` is absorbed by `I`, `S(t) = 0` is part of the pushes' claim.

**Completeness.** The honest `Q` meets every claim exactly; the verifier's nonzero requirement adds `Y_1 = (D + x
Z_V)(t)` and `Y_2 = (D + x Z_V²)(t)` (nonzero polynomials of degree below `2N + 2`: `2^-166` each) and `Y_3 = 1 + ρ(1
+ Z)` (one `ρ`, or none), and drops `Y = c_h + Z` and `w_{m+1}`: about `2^-165` in all, as before.

## 3. Adversarial tests

`tests/pi2.rs`, `the_copy_sum_from_the_layout` (D16v synthetic circuit, `2^11` positions), with
`prover::prove_cheating` and its `Cheat`s:

- **On a witness** the cheats that act on the sum (`None`, `AbsorbInG`, `OverflowInQ`) are the honest proof: every
  claim holds, and both layouts' relations hold (the control for the next two).
- **A dishonest port** (a public element changed; the prover keeps `h D + R = q Z_V`, `h = T / (d_pull d_push)` at the
  hole, so `Σ_V h ≠ 0`): with `x h`'s coefficient `N` dropped (`None`, which is `h(0)` moved by `σ`), kept in `q`'s
  second digit (`OverflowInQ`), or dropped with `σ` in `G` (`AbsorbInG`), the claims are `[true, true, false, true]`
  (`W`, setup, identity, pushes): the identity's claim, the only one that sees the sum, is false.
- **The negative control** (`identity_relations`): from `Q`'s slots read one by one at `t`'s position coordinates, the
  relation the identity's claim checks (`E_00 + a E_10 + b E_01 + a b E_11 = target`) and the one the other layout's
  claim would (`E_00 + Z E_11 + a E_10 + b E_01 = target`, `G` at `Z`): `AbsorbInG` meets the other layout's relation
  and not this one's; the other cheats meet neither.
- **Slots an honest `Q` leaves zero**: `G` filled: `[true, true, false, true]`; `S` filled: `[true, true, false,
  false]` (both claims read it); `s` sent off `P(t)` (`ShiftS`): the pushes' claim is false.
- Unchanged and still passing: `small_d16v`'s random witness mutations (some claim false), a changed public element or
  input (now `[true, true, false, true]`), flipped stream bytes, the interface example; the contract's parity with the
  Rust verifier word for word, and on the real proofs (`pi2_real`) every calldata byte flipped at two bits, the frame
  attacks (seven claims: swapped payloads, each claim's value, point, out-of-domain answer changed, a claim missing,
  another frame index or mode).
- `prover::tests::quotient_slots_are_their_bits`: the slots where their bits say.

## 4. The prover, A/B on h3

PROVER_TABLE

## 5. Not possible in this PIOP, and why

**Lever 2: one claim for `Q`'s identity and pushes** (−3,048 more). A claim whose position coordinates read `Q` at `t`
weighs the sixteen slots by a rank-one tensor: slot bits `(1 + z_0, z_0) ⊗ (1 + z_1, z_1)` times the limbs'. The limbs'
coordinates are fixed (`E`'s polynomials `h`, `q` must be read as elements: limb weights `∝ (1, Y, Y²)`, limb code 3 then
`Y³`), so a claim is a rank-one `2 × 2` tensor over four "super-slots", each an `E` polynomial plus `Y³` times a `K`
one. The identity involves three `E` polynomials (`H` and `q`'s two digits, or `h` and the digits on `main`) with
fixed ratios (`1 : a : a Z`): three entries of the `2 × 2` tensor, which then has no free coordinate. A claim carrying
the identity is pinned by `t` and `s`; combining it with `P(t) = s` and the definition needs a coordinate drawn after
`s`. Pinned, the prover solves for `s`: with `p = P(t)` and an error `ε` in the identity at `p`, the claim's equation is
`ε + (s − p) β(s) = 0`, `β` of degree 1 in `s` (it is `d_pull h(t) + 1 + c_3 (1 + Z d_pull (α + s + ξ))` on `main`):
a quadratic the prover can solve about half the time. Ways around it, each ruled out:

- **`q` below `N`** (the identity two super-slots, a coordinate left free): the identity is below `3N` (`h`, `d_pull`,
  `d_push` each below `N`).
- **The copy argument split** (`a = 1/d_pull`, `b = 1/d_push` committed apart, two identities below `2N`, `q_a`, `q_b`
  below `N`: four `E` polynomials): rank one forces the two identities' ratios equal (rows) or their square roots'
  product (diagonals) — no free coordinate — and the push identity still multiplies `b(t)` by `P(t)`.
- **`d_push` from `P_v` (π2v1: no `P`, no `s`)**: `q` below `4N`, five `E` polynomials against four super-slots; 32
  slots are `2^29` words, past WHIR's certified `2^28` (and the prover's coset doubles).
- **`P`, `q_P` in `W`** (functions of `w`, so before `α, β`): `W`'s claim reads the row's fold at `ρ⃗`, not `P(t)`;
  another point of `W` is another claim.
- **A product `b P` committed**: `b(t) P(t)` is checked bilinearly again.

So two claims on `Q` (and one on each other commitment) is this PIOP's minimum.

**Lever 3: fewer of the 18 values at `t`** (1,536 a value).

- **The 16 fold values.** The verifier needs `P_v(t) = v_0 + Z A / B`, `A = Σ_g (N_g / D_g)(E_g(v ⊕ k_g) + v_0)`, and the
  ports' `E_g`: a quadratic form of the row's 16 cells whose coefficients (the groups' indicator sums at `t`) the
  prover learns with `t`. The formulas' products (χ's `(1 + b_{x+1}) b_{x+2}`, the `E` units' limb products) read
  every cell at some role (each role permutes the cells by `XOR k`), so the form involves all 16 cells and its value is
  not a linear function of fewer than 16 values. The membership's trick (one rank-one claim binding three revealed
  forms on a conic) needed the forms to span a plane meeting the Segre variety in a conic; here the needed span is the
  whole 16-dimensional space, which `W`'s claim already covers with `eq(ρ⃗, ·)`. (D8v, 8 values: a Keccak-f in rows of 8
  needs about twice D16v's positions, PI2.md §9.)
- **`ξ`**: the setup claim's value; `d_push` and `P`'s definition need it, and a claim's value must be the verifier's.
  Committing `P̃ = P + κ + β σ` instead of `P` (after `β`) moves `ξ` from `d_push` into the definition (`Z q_P = s̃ + ξ +
  P_v`), not out.
- **`s`**: the identity is bilinear in `h(t)` and `P(t)` (lever 2); one of them must be revealed.
- **The out-of-domain answers** (2 × 24 B): the EIP's claim format.

**The membership's fix-up layout** (`H`'s second digit a constant `b` solving `q`'s coefficient `N` to zero, the digit
coordinate `Z x`): in π2 the digit coordinate is shared with `q_P` (at limb code 3), whose coefficient `N` no free
parameter reaches (`q_P = (P + P_v) / Z_V` is a function of `w`; a second digit of `P` would lift `d_push` to `2N` and
the identity to `4N`). This layout needs no fix-up.

**The frame's index byte** (−64): kept, the convention π2 shares with the membership contract (`evm_link::declared`).

## What the Lean needs

`formal/` proves `f96a7938`'s protocol (π1-rec3; π2v3 with π1's three claims encoded by the contract); beyond
[`PERF_GAS.md`](PERF_GAS.md)'s and [`PERF_GAS2.md`](PERF_GAS2.md)'s lists, π2v4 changes:

- **`formal/RecStatement`** (the statement and verifier): the transcript name `leanvm-rec-pi2v4`; `Q`'s slots
  (`H = x h` at `(0, 0)`, `q`'s digits at `(1, 0)`, `(0, 1)`, `G` and `S` at `(1, 1)`, `P` at limb code 3's `(0, 0)`,
  `q_P`'s at `(1, 0)`, `(0, 1)`); the verifier's digits to `w_m`, the inversion of `R_d Y_1 Y_2 B Z Y_3 · c_h D_n`, the
  identity's claim at `(u_0 … u_{m-1}, t Z / Y_1, t Z² / Y_2, y_0, y_1)` and its value, the pushes' at `(u_0 …
  u_{m-1}, ρ, ρ Z / Y_3, 1, 1)` and its value, no sum claim; `Calls.lean`: seven claims; `Data.lean` regenerated
  (`tests/lean_statement_keccak.rs`).
- **`formal/RecPiop`** (the PIOP's soundness): the stack's sixteen polynomials as above, all the prover's; the pushes'
  claim as a degree-2 polynomial in `ρ` binding `P(t) = s`, `q_P`'s definition and `S(t) = 0` (§2 item 2); the
  identity's claim as `I(t) = 0`, `I = D² H + x Z D A + x² Z³ G + x D R` of degree below `5N`, and the lemma "`I = 0`
  and `D(0) ≠ 0` give `H(0) = 0`, `h = H / x` of degree below `N − 1`, `Σ_V h = 0`, and `h D + R = 0` on `V_m`" (§2
  items 5, 6), replacing the sum claim and the empty slots' argument; `Rounds.lean`'s `err` at `t`: `(5N − 1)/|E|` (or
  coarser), at `ρ`: `2/|E|` for `Q`.
- **`formal/RecCompose`**: the contract model (payloads 3 … 6, seven claims, `pcs_union_sound_oracle` over seven
  openings), `qOodBinding` over `Q`'s two claims; `pi2Bound`'s arithmetic (still 128.93 bits; the `t` round's numerator
  `5N`); completeness: the honest prover's `Q` (`H` by `mul_x`, the slots, `G = S = 0`; `Pi2Prover*`, `Pi2Honest*`) and
  the nonvanishing of `Y_1`, `Y_2`, `Y_3` (`Pi2Complete*`).
- **Vectors**: `tests/lean_pi2_prover.rs` (π2's Lean prover: the stream and `Q`'s root change), `tests/lean_statement_keccak.rs`
  (the verifier's data), both regenerated by their tests.
