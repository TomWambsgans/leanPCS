<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# π1's claims' points on chain: the paired batch

π1's claims are the only part of π1's proof the recursion's contract carries: their point is a run of π1's
challenges, computed inside π2 and never on chain. This file says why that point cannot be dropped, and how π1-rec3
generates it from 14 challenges instead of one a coordinate: the batching sumcheck two variables a round
(`FsShape::Rec3`, `leanvm_univariate::KECCAK_REC3`).

- The core is `leanvm_statement::transcript::{sumcheck_pairs, sumcheck_pairs_drawn, pair_point, cantor_beta1}`; π1's
  verifier calls it in `verifier::batch`, its prover is `prover::batch::prove_pairs`, π2's compiler maps the pairs'
  coordinates to their challenges (`circuit::compile::pair_coordinate`, `CallWord::Pair`).
- Every number is marked **measured** or **modelled**.

```sh
RUSTFLAGS="-C target-cpu=native" cargo test --release -p leanvm_statement --lib transcript -- --nocapture
RUSTFLAGS="-C target-cpu=native" cargo test --release -p leanvm_univariate --lib domain
```

## 0. Summary

- **What the contract carries.** π1's three claims (`C1`, `C2`, setup `F`) are at the batching sumcheck's point `r`,
  whose coordinates are the largest stack's variables (27 at the reference shape, 128 signatures; 28 at 400). With
  the 3 values, one element a coordinate would be 30 elements (720 B).
- **Why `r` stays.** `C1` carries Flock's ring switch, a claim on `q_flock` at 64 Frobenius twists of a point that
  Flock's sumchecks drew. With point claims only (`machine.rs`'s encoding), a sumcheck over `q_flock`'s variables is
  the only reduction of that claim, so its point needs fresh challenges.
  - DEEP does not remove that sumcheck, so it saves no coordinate.
  - Gemini, Zeromorph and the univariate sumcheck give each coordinate back as a claim's value, or worse (§2).
- **What changes:** how many challenges generate `r`. The batch runs two variables a round, on `V_2`'s coordinate
  functionals. Then `r` is pairs `(y_0(z_j), y_1(z_j))` (and one plain coordinate at an odd count): **14 narrow
  challenges** and the 3 values, 17 elements, 408 B. This costs no Keccak-f (§2.4). Three variables a round would cost
  18 more Keccak-f, which π2 cannot hold.
- **Gas** (measured, §4): the recursion's calldata is 1,004 B (π2v2); the pairs save 13 elements (312 B) at the reference shape.

## 1. The claims and their points (measured)

| | π1-rec3, the Keccak VM |
|---|---|
| π1's claims | `C1`, `C2`, `F`, each at `r`'s prefix of its commitment's variables |
| `r` | the batch's point: 27 coordinates at 128 signatures (13 pairs, one plain round), 28 at 400 (14 pairs) |
| their public elements | 14 narrow challenges and 3 values: 408 B |
| calldata / execution / EIP-7623 `c = 0` (128 signatures) | 1,004 B / 27,641 / 42,997 (π2v2) |

The Keccak VM's π1 commits no Flock matrices (`A0`, `B0`): its lincheck terminal is the structured one, computed by
π1's verifier. So `r` is the whole problem.

## 2. Why the batch's point stays

### 2.1 The ring switch needs a sumcheck over `q_flock`

Flock (a′)'s ring switch is one of `C1`'s relations:

`Σ_u Φ(eq(P, u)) q_flock(u) = target`, with `Φ(eq(P, ·)) = Σ_(k<64) c_k eq(P^(2^k), ·)`.

`P = (χ_in', χ_rest)` holds challenges of Flock's lincheck and zerocheck rounds.

- A declared claim holds point claims (`E`-linear evaluations), so this 64-point claim must become point claims on `C1`.
- The 64 values `q̂(P^(2^k))` are not known. Sending them would make 64 claims and 64 values on chain.
- So it is reduced by a sumcheck over `q_flock`'s variables. Binius's ring switch ends the same way.
- A sumcheck's challenge must be drawn after its round's message. A challenge known earlier lets the prover answer
  any claim.
- That sumcheck is the batch, whose point every other relation shares at no extra coordinate.

Even if Flock's own rounds were paired (§2.4), `P` would be fresh elements, and its twists still 64 points.

### 2.2 DEEP and interleaved layouts

The other relations are at points derived from `t` and `c`:

- columns at `t`, `t + 1`, `s(t)`;
- the heap's restrictions at mixed points;
- `Q_W`'s copies at `y(t)`;
- `F`'s point `(α, w(t))`.

DEEP could fold the univariate ones into one quotient `G` in a new commitment `C3`, with claims at a fresh `z`. With a
group's column index as the low coordinates, `Σ_j eq(w_(<c)(x), j) col_j(w_c(x))` is the interleaved polynomial's
value at `x`: one point claim for each height group. But:

- **It saves no coordinate.** The batch stays for `q_flock` (§2.1), and its point already carries every other claim.
- **It costs π2 more than π2 has.** Every column's value at every point must be sent: about 90 more values (the tables'
  153 columns, of which 64 are sent), 2.1 KB of π1's stream, about 16 Keccak-f, or 2.1M positions (modelled). π2
  has 1.11M positions left at the reference shape and 0.84M at 400 signatures.
- **It costs a commitment and claims.** `C3` is E-valued, up to the columns' size, and its list joins the union bound.
  Each height group needs its own claim, because its DEEP identity has its own denominator: at least 4 on `C1`.
- **The heap's restrictions are not univariate evaluations of `T`.** They are multilinear claims at
  `(w_(<r)(t) + w_(<r)(o), w_(≥r)(o))`. Per-table heaps would turn them into `T_b(β_r + t)`, but that means
  rewriting π1's prover.

### 2.3 Gemini, Zeromorph, the univariate sumcheck

Each would replace `q_flock`'s claim at a fresh point `r_q` by univariate evaluations at one random `z`.

- **Gemini in characteristic 2.** The additive fold is `F_(j+1)(s(x)) = F_j(x) + (x + r_j)(F_j(x) + F_j(x + 1))`, since
  `s(x) = s(x + 1)`.
  - It commits `F_1 …`, E-valued, about as many words again as `q_flock`.
  - It needs `F_j` at `w_j(z)` and at `w_j(z) + 1`: two claims at each level, at different points.
  - That is about two values on chain for each coordinate saved.
- **Zeromorph.** It writes `q̂(u) − v = Σ_l (u_l + r_l) q̂_l(u_(>l))`. In basis `B` that is
  `q(x) − v = Σ_l (w_l(x) + r_l) Q_l(w_(l+1)(x))`, each `Q_l` read at the digits of `w_(l+1)(z)`.
  - Zeromorph merges the `Q_l` through its commitment's homomorphism (KZG). WHIR's Merkle roots have none.
  - One stack can hold every `Q_l` at the positions whose lowest set bit is `l`. At `digits(z)` it gives
    `Σ_l Π_(j<l)(1 + w_j(z)) w_l(z) Q_l(w_(l+1)(z))`: one combination, with weights fixed by `z`.
  - The identity needs the weights `w_l(z) + r_l`, which carry `r`. So each `Q_l(w_(l+1)(z))` is its own claim:
    about one value for each coordinate saved.
- **The univariate sumcheck over `q_flock`'s values.** It writes `q̂(r) = Σ_(x ∈ V_n) E_r(x) Q(x)`.
  - It needs an E-valued quotient of `2^n` points, three words a point: a new commitment.
  - `E_r(z)` is a sum of `2^n` terms, for π2 to evaluate.

In each case the coordinates come back as claim values, at least as many of them.

### 2.4 What can change: the challenges per round

A round of `k` variables on `V_k`'s coordinate functionals works as follows:

- The functionals satisfy `y_l(ω_i) = i_l` (`docs/leanvm/univariate/SPEC.md`).
- The round sends the summand restricted to the curve `u = y(X)`: a polynomial `G` of degree `2 · k · 2^(k-1)` when
  the summand has degree 2 in each variable.
- Then `Σ_(x ∈ V_k) G(x)` is the sum over the round's `2^k` corners.
- One challenge `z` gives the `k` coordinates `y_l(z)`.
- No curve does better. A curve through the `2^k` corners on `2^k` points has coordinates of
  degree at least `2^(k-1)`: each takes two values there, so the vanishing polynomial divides `y(y + 1)`.

π2 hashes that data. Over 27 variables (modelled; Keccak-256's rate is 136 bytes; π2's positions at 130,944 a
Keccak-f):

| rounds of | challenges | scalars | Keccak-f | π2 |
|---|---:|---:|---:|---|
| 1 variable | 27 | 54 | 27 | |
| **2 variables (π1-rec3)** | **14** | 106 | **27** | **+0 Keccak-f** |
| 3 variables | 9 | 216 | 45 | +18 (2.36M positions) |
| 4 variables | 7 | 408 | 77 | +50 |
| 3 triples, 9 pairs | 12 | 144 | 33 | +6 (0.79M positions) |

- **Pairs cost no permutation.** A plain round's 2 scalars and the 32-byte state are 80 bytes, which fit in one block.
  A pair's 8 scalars and the state are 224 bytes: one hash of two blocks, where two plain rounds take two hashes of
  one block.
- **Triples do not pay.** Against pairs, each triple costs 2 more permutations and saves half a challenge. π2 has
  0.84M positions left at 400 signatures (6.4 permutations), so 12 challenges would take nearly all of it, to save
  48 bytes.

## 3. The design: the batch two variables a round

- **The rounds** (`transcript::sumcheck_pairs`). A pair is `(u_(2j), u_(2j+1))`, low variables first. Its
  polynomial is `G_j(X) = Σ_rest Σ_k λ^k W_k(·) C_k(·)`, read at `(r_(<2j), y_0(X), y_1(X), rest)`. It has degree 8.
  - `V_2 = {0, 1, β_1, 1 + β_1}` is `GF(4)` (`β_1² + β_1 = 1`). So `Σ_(x ∈ V_2) x^e` is 1 for `e ∈ {3, 6}` and 0 for
    every other `e ≤ 8`.
  - The stream holds `c_0, c_1, c_2, c_4, …, c_8`, and `c_3 = claim + c_6`.
  - One challenge `z_j` gives `r_(2j) = y_0(z_j) = z_j + β_1 y_1` and `r_(2j+1) = y_1(z_j) = z_j² + z_j`.
  - 27 variables are 13 pairs, then one plain round, with `r_26 = z_13`; 28 variables are 14 pairs.
  - Every challenge is narrow, 160 bits (`Channel::sample_narrow`).
- **What stays.** The rest of π1 is unchanged: the weights `W_k(r)`, the three values, and the claims at `r`'s prefixes.
  Only the rounds and their challenges change.
- **The Fiat–Shamir shape** is `FsShape::Rec3`: π1-rec's derived runs (`Rec`), narrow batch challenges (`Rec2`), and
  the paired rounds. π1's contract IV binds it (`variant_bytes`).
- **π2.** The circuit is compiled from the recorded verifier. Its public elements are the 14 `z_j` and the 3 values. A
  pair's two call words are `y_0`, `y_1` of a port, not ports themselves (`CallWord::Pair`); the map
  `z ↦ (y_0(z), y_1(z))` is injective (`y_0 + β_1 y_1 = z`), so binding the `z_j` binds `r`. `public_from_calls`
  recovers `z` and checks both coordinates.
- **The contract.** It reads the 14 `z_j` and derives the coordinates of π1's three claims: a pair costs one
  squaring, one product by `β_1` and two additions. `r` is written once for the three claims (`PI2.md` §9, lever 3b).

**Measured** (`leanvm_statement` `transcript::tests`, `leanvm_univariate` `domain::tests`):

- the paired sumcheck is complete on honest product sums of 1, 2 and 3 tables, at odd and even variable counts;
- a wrong claim, and each flipped scalar, ends on a claim the tables do not give;
- `pair_point` is `V_2`'s coordinate functionals, and `cantor_beta1` is `domain::beta()[1]`;
- recorded over 27 variables at degree 2: 27 Keccak-f either way, 14 challenges against 27, and 278 E operations
  against 135.

End to end, the real π1-rec3 proofs (`keccak128_rec3.txt`, `keccak_rec3.txt`) are accepted by π1's verifier and
contracts, and by the recursion's contract through π2 (`SPEC-REC.md` §11).

## 4. Calldata and gas (measured; EIP-7623 `c = 0`, without the base)

| | 128 signatures | 400 signatures |
|---|---:|---:|
| π1's claims in calldata: 14 challenges and 3 values | 408 B | 408 B |
| with one element a coordinate (27 or 28, and 3 values) | 720 B | 744 B |
| saved | 312 B | 336 B |
| the recursion's calldata / execution / EIP-7623 (π2v2) | 1,004 B / 27,641 / 42,997 | 1,004 B / 28,421 / 43,753 |
| EIP-7976 | 64,256 | 64,256 |

- **What a byte is worth.** At the reference shape the standard price binds (`16 B + execution`, 4.6K above the
  floor), so a nonzero byte costs 16: the 312 B are worth about 5.0K there, 12.5K at the floor's 40 a byte, and 20.0K
  under EIP-7976 (64 a byte).
- **The execution** has 13 fewer ports and reads, and 312 bytes fewer in π2's first hash; the pairs' derivation costs
  a few products each.
- **Claims.** The claims and the calls are unchanged (7 claims, 6 calls), so `c > 0` adds the same.

## 5. Soundness

- **A pair's error.** Its polynomial has degree 8, so its Schwartz–Zippel error with a narrow challenge is `8/2^160`
  (a plain round's `2/2^160`). It is drawn after `C2`, over `C1`'s and `C2`'s lists.
- **The batch.** Each of the 14 rounds and `λ` is a round of its own, unioned over `C1`'s and `C2`'s lists (4,473 and
  6,296 at 128 signatures). A pair keeps 157.0 bits alone and 132.3 after the lists, π1-rec3's weakest round
  (`params/leanvm_univariate_params.py`; the main line's weakest is `t`, 143.2). Summed over the 14 rounds, as an
  interactive protocol would count them, about 128.5; with Fiat–Shamir over `Q` queries the per-round figure is the
  one that counts (`docs/leanvm/univariate/SPEC.md` §9). The Lean bound caps each round at `2^35/|E|`, a pair's
  `8/2^160` exactly.
- **The point is not uniform.** Each pair of coordinates lies on a curve. Neither argument needs uniformity: the
  sumcheck makes one Schwartz–Zippel step a round, in `z_j`, and WHIR's openings are sound at every point.
- **No new list.** There is no new commitment, and the openings are the same 6 (π1's 3, π2's 3).

## 6. What the pairs cost π2

- **Keccak-f: unchanged** (recorded: 27 permutations for 27 variables either way).
- **Positions:** more stream scalars (a pair sends 8 where two plain rounds send 4: free bits and packings), fewer
  challenge packings, one later block a pair, and about twice the batch's `E` operations (278 against 135, recorded).
  Not measured on its own; the totals below include it.
- **π2's verifier** has 13 fewer ports.
- The whole Keccak VM π1-rec3 in π2: 15,668,416 positions (93.4% of `2^24`) at 128 signatures, 15,940,800 (95.0%) at
  400 (`SPEC-REC.md` §10.3). `Q = 12N` stays `2^27.58` (π2v2).

## 7. The prover (`prover::batch::prove_pairs`)

- **A pair round takes nine sums.** For each piece of the weights and each group of four words, it takes
  `Σ W(a, b, ·) C(a, b, ·)` for `a, b ∈ {0, 1, ∞}`. These are the coefficients of `G̃`, and then
  `G = G̃(y_0, y_1)`. It folds the tables at the pair's two coordinates.
- **As built** it reuses `Weight::round` and `Weight::fold`: each pair binds its low variable at 0, 1 and `β_1` on
  clones of the weights, then takes one round on the high variable; four passes a pair instead of two. A two-variable
  kernel in `weight.rs` (factored, dense and twisted pieces) would read the stacks once a pair.
- **No extra memory, no new commitment.**
- **Measured** (π1-rec3 at 128 signatures, Mac Apple M4 Max): the whole prover 2.72 s cold with its checks (6.75 GB);
  warm, median of 3, 3.65 s (6.86 GB).

## 8. Status

Built: π1-rec3 is the recursion's π1.

1. **π1's verifier.** `verifier::batch` calls `sumcheck_pairs_drawn(channel, target, 2, vars, true)` under
   `FsShape::Rec3`; `contract_iv` binds the shape.
2. **π1's prover.** `prover/batch.rs` sends a pair's 8 coefficients and folds at `pair_point(z)` (§7), with the last
   variable a plain round at an odd count. The committed vectors `keccak128_rec3.txt` and `keccak_rec3.txt` are
   π1-rec3 proofs.
3. **π2.** `circuit::compile` takes each pair's challenge as the port, in place of its two coordinates;
   `circuit::spec`'s call words have `CallWord::Pair`; `pi2::verifier` computes `pair_point` of the public scalars;
   `pi2::contract` derives the coordinates before the calls.
4. **Tests.** The paired batch against an honest prover at every shape (`transcript::tests`); the contract equal to
   the Rust verifier, word for word; flipped calldata bytes rejected end to end (`tests/pi2_real.rs`).
