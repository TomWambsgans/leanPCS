# Cutting the membership proof's gas, round 2: three claims, six scalars

Branch `perf2/membership-gas`, from `main` at `866ba889` ("main" below). The ZK Keccak-256 Merkle membership proof
(benchmark 1 of the EIP draft) goes from **36,520 to 31,680 gas** (−4,840, −13.3%). The PCS claim format
(`docs/PCS_CLAIM.md`, version 1) and the EIP draft are unchanged; the circuit has the same rows (3,878,615 of
`2^22`). The Lean in `formal/` is **not** updated: it proves `f96a7938`'s protocol (see "What the Lean needs").

## Where the gas goes

The transaction is floor-bound (EIP-8141 with EIP-7976's floor, `pcs_gas` in it): `64 · (calldata + frame) + 5,000 +
1,000 · claims`, the frame `1 + 32` bytes a claim. A calldata byte costs 64 gas, a claim `32 · 64 + 1,000 = 3,048`,
a revealed element of `E` (24 B) 1,536.

| | main | this branch |
|---|---|---|
| fixed: selector, statement, frame index, frame header, 5,000 | 9,480 | **9,224** (no selector) |
| commitments in calldata (W, T: root and out-of-domain answer) | 7,168 | 7,168 |
| claims | 4 (W, wiring, copy and sum on T): 12,192 | **3** (W, wiring, copy on T): 9,144 |
| revealed scalars past the roots and answers | 5 (`a_0..a_3`, `next`): 7,680 | **4** (`X`, `C`, `V + Y` at `t`, `next`): 6,144 |
| **transaction gas** | **36,520** | **31,680** |
| calldata | 301 B | 273 B |
| frame of PCS claims | 129 B | 97 B |
| execution (does not bind) | 16,414 | 15,753 |
| standard price (does not bind) | 32,258 | 29,649 |
| `FIELD_MUL`s | — | 343 |
| contract code / deployment | 5,304 B / 1,242,838 gas | 4,866 B / 1,149,640 gas |

`cargo test --release -p evm -- --ignored --nocapture --exact quotient::tests::gas_report`. The standard price stays
2,031 gas under the floor (execution may grow by that much before it binds). In the EIP draft's table the row would
read 273 bytes, PIOP 20,097 gas (the PIOP frame's `max(standard, floor)`: standard `16 · 271 + 4 · 2 + 15,753 =
20,097` binds, the floor `64 · 273 = 17,472`), 3 claims, 31,680 gas.

## What changed

Three changes, independent of each other.

### 1. The sum checked by the table's layout: `x h` read through `ζ = Z x` (−3,048)

On main, `T` holds `q` (kind 0) and `h` (kind 1), each `F_0 + Z F_1` (digit 0, digit 1), and two claims read it: the
copy claim at `t`, and a sum claim at `h`'s coefficient `n − 1` (zero, since `Σ_cells h` is that coefficient times a
nonzero constant). The sum claim is now gone. `T` holds, in each kind's two digits, polynomials read as
`F_0 + ζ F_1` with **`ζ = Z x`** (the claim's digit coordinate is `ζ / (1 + ζ)` where it was `Z / (1 + Z)`):

- kind 0: `q = A_0 + Z x A_1`;
- kind 1: **`P = x h = B_0 + Z x B_1`**, `B_0 = x h_low`, `B_1` the blinding `ε = b_0 + b_1 X_1 + b_2 X_2`
  (`h = h_low + Z ε`).

The copy claim's kind coordinate weighs `P / t` against `q`, so its value is the same identity as before, times `t`:
`(1 + κ) q + κ P = t (d + d' + μ Z g) / (Z t + d d')`, `κ = d d' / (Z t + d d')`.

**Why it is sound.** Fix `W`, `α, β, μ` and `T`; let `q = A_0 + Z x A_1` and `P = B_0 + Z x B_1` be the
`E`-polynomials `T` holds (its four `K`-limbs, the fourth of weight `Y^3`, as on main), and
`R = d + d' + μ Z g` (a polynomial: `Z_R | Z` and `Z_P | Z`). The claim at `t` holds iff `I(t) = 0`,

  `I = x Z q + d d' P + x R`  (characteristic 2),

whenever the claim's denominators (`1 + w_k`, `1 + ζ`, `Z t + d d'`) are not zero. `deg I ≤ 4n`, so if `I ≢ 0` the
claim holds with probability at most `4n / |E| ≈ 2^-166` over `t` (drawn after `T`). If `I ≡ 0`:

1. At `x = 0`: `d d'(0) · P(0) = 0`, and `P(0) = B_0(0)` (the `Z x` term vanishes there). `d(0) = α + w(0)` and
   `d'(0) = α + w(0) + β σ(0)`, with `w` committed before `α, β` and `σ` public: both are nonzero but with
   probability `2 / |E|`. So `B_0(0) = 0`.
2. `h := P / x = B_0 / x + Z B_1` is then a polynomial, `B_0 / x` of degree at most `n − 2` (`B_0` has `n`
   coefficients). On the cells `h = B_0 / x`, and a polynomial of degree at most `n − 2` sums to zero over an
   `F_2`-subspace of `n` points (only `x^(n-1)` has a nonzero sum). So **`Σ_cells h = 0`**.
3. Dividing `I` by `x`: **`Z q + d d' h = R`** as polynomials.

These are exactly the two facts main's two claims gave (the identity at `t`, and `h`'s coefficient `n − 1` zero), so
the rest of the argument is main's unchanged (`PERF_GAS.md`, "Why the merged quotient is sound": on a cell `h` is the
logarithmic derivative plus `μ e / (d d')`; the sum vanishes at random `α, β, μ` only if every error is zero, by the
pole lemma and the circuit's condition `errors_have_their_own_poles`, still asserted in `Index::new`; then the
copies hold).

The digit-1 slot is what main's attempt of `x h` (`PERF_GAS.md`, "Tried, and rejected") failed on: read through `Z`,
the digit-1 part `Z B_1` is divided by `x` too: `h = B_0 / x + (Z / x) B_1`, and `Z / x` is not zero at the cell 0,
so `h(0)`, hence the sum, moves with `B_1(0)`, freely. Read through `Z x`, the digit-1 part is `Z B_1` after the
division, zero on every cell, whatever the prover puts there.

**The honest prover's price: `q` must fit.** `{A_0 + Z x A_1}` is not every polynomial of degree `≤ 2n`: writing
`q = q_low + Z Q_h`, it needs `Q_h(0) = 0`, `q`'s coefficient `n` zero (`X_j(0) = 0` for `j ≥ 1`). The prover
spends one of the three blinding coefficients (`ε = b_0 + b_1 X_1 + b_2 X_2`; `b_0, b_1` drawn, as main's two):
`b_2` adds `b_2 E` to `q`, `E = w_1 d d'` (`w_1 = X_2`), and `Z w_1 b_2` to `h` (nothing on the cells). So the
quotient's pass runs with `b_2 = 0` (`q` then of degree `< 2n`), and then `b_2 = q^(0)_n / γ`, `γ` the high part of
`E` at 0. Why `X_2` and not `X_0`: `d d' = α^2 + α β (x + σ) + w^2 + β w (x + σ) + β^2 x σ`, and only the `α β σ` term
carries `α`; `σ`'s top coefficient is zero for every permutation (`Σ_cells σ(x) = Σ_cells x = 0`), so the response of
`q_n` to `b_0` or `b_1` is a polynomial in `β` and `w` alone, which a witness could make vanish, while the response to
`b_2` is `γ = (d d')_{n−2} = α β σ_{n−2} + (terms without α)`: nonzero but for one `α` (drawn after `W`) when
`σ_{n−2} ≠ 0` (`σ_{n−2}` is `Σ_cells x σ(x)` up to a constant, nonzero for the membership and toy wirings;
`Index::new` asserts it, a completeness condition). Completeness error `≤ 2/|E|`.

The correction needs `E`'s coefficients: the pass also writes `w_1 w^2` and `w_1 w (x + σ)` on the coset (two `K`
columns, in `T`'s empty limb-3 slots; `w_1 w^2` has degree `2n`, its coefficient `w_top^2`, and `X_{2n} = Z^2 + Z` is
1 on the quotient's coset, offset `β_{m+1}`, so the pass subtracts it), transforms them back with `q`, and the prover
adds `b_2 (α^2 w_1 + α β w_1 (x + σ) + w_1 w^2 + β w_1 w (x + σ) + β^2 w_1 x σ)` to `q`'s coefficients, the
circuit's parts `w_1 (x + σ)`, `w_1 x σ` made per proof by [`mul_x`] and [`mul_w1`]. `E`'s coefficient `2n` puts
`b_2 w_top^2 (X_0 + X_n)` into `Q_h`. Then `A_1 = Q_h / x`.

Products and quotients by `x` in the novel basis need no multiplication (`protocol::mul_x`, `div_x`): with
`F = F_e(w_1) + x F_o(w_1)` and `x^2 = w_1 + x`, `x F`'s coefficient `j ≥ 1` is `f[j−1] + f[j + low(j) − 1]`, and the
quotient runs the same relation back along `j ↦ j + low(j)` (a Fenwick tree's update path), level by level (the
levels below `2^12` block by block, in cache); `w_1 F` is `mul_x` one level up on the even and odd coefficients.

### 2. The gate's roles swapped: one witness claim binds three row values (−1,536)

The verifier needs the row of `t` only through the copy argument's `w(t)` and the gate at `t`. On main the gate is
`V + X + C + Y C`, which needs `X`, `Y`, `C` and `V + X + C`: four linear forms of the row polynomials' values
`a = (a_0..a_3)` at `t`, all four `a_j` revealed. The gate is now **`V + Y + C + X C`** (`circuit.rs`: χ's inputs
`(X, Y, C) = (a[x+1], a[x], a[x+2])`, XOR `(0, a, b)`, NOT `(0, 1, a)`, packing `(3, b, acc)`, random rows
`(0, r, s, r+s)`, `(s, r, 0, r)`, `(1, r, s, r)`), the same bits. The product is now of `X`, which the copy argument
reads anyway, and `C`: the verifier needs **`X`, `C` and `V + Y`**, three forms, and the proof reveals those three
values (`protocol::row_values`).

One claim on `W` binds them. The claim's point `(z_0, z_1, u_2, ...)` weighs `a` by the rank-one tensor
`e = (1 + z_0, z_0) ⊗ (1 + z_1, z_1)`. In `a`-coordinates (`w = a_0 + x a_1 + w_1 (a_2 + x a_3)`, `τ = t`,
`ω = w_1(t)`, `θ = β_1`):

- `X = (1, τ, ω, τ ω)`, `C = (1, τ + θ, ω + 1, (τ + θ)(ω + 1))`, `V + Y = (0, θ, 1, τ + θ ω + θ + 1)`.

Their span `S` is the plane `n · e = 0`, `n = (τ + θ ω, 1, θ, 0)`. A plane meets the Segre quadric of rank-one
tensors (`e_00 e_11 = e_10 e_01`) in a conic, degenerate (two lines) exactly when `n` is itself rank one,
`n_0 n_3 = n_1 n_2`; here `n_0 n_3 = 0 ≠ θ = n_1 n_2`, for every `t`. So the verifier draws `ρ`, sets `z_0 = ρ`, and
solves `n · e = 0` for `z_1 = a / (a + b)`, `a = (τ + θ ω)(1 + ρ) + ρ`, `b = θ (1 + ρ)` (`protocol::witness_conic`);
`e = λ_X X + λ_C C + λ_VY (V + Y)` with `λ` from `witness_weights`, and the claim's value is
`λ · (X, C, V + Y)` times the higher coordinates' normalisation.

**Why it binds.** `(a + b) e(ρ)` is a vector of quadratics in `ρ` tracing the non-degenerate conic, which spans `S`,
so its three coordinates in the basis `(X, C, V + Y)` are linearly independent polynomials of degree at most 2. If
the revealed values differ from the committed table's by `Δ ≠ 0`, the claim holds only where `λ(ρ) · Δ = 0`: at
most 2 values of `ρ` (drawn after the values), plus `a + b = 0` (1 value, rejected as degenerate): `3 / |E|`. The
direction of `a` outside `S` is neither revealed nor used. `tests::the_witness_claim_is_on_the_conic` checks the
weights and the independence; `claims_hold_exactly_for_a_witness` that a changed row value leaves a false claim.

Two values would not do: a two-dimensional span that one rank-one claim binds must be a line of the quadric, i.e.
two cells with the same `w_1` (`{X, Y}` or `{C, V}`), and a gate on two cells computes nothing.

### 3. No selector (−256)

As π2's contract: the verifier's entry is calldata of exactly 273 bytes and no value; `setIndexCommitment` keeps its
selector and its 68 bytes. The frame's index byte stays (the convention π2 shares, `evm_link::declared`).

## Soundness

- **Openings dominate**: three (`2^24`, `2^24`, `2^28` words) where there were four: `3 · 2^-128` a query, **126.4
  bits as `Q/ε`** (main: 126.0). Scaling main's accounting by `3/4`: about `2^-105.4` at `Q = 0`, `2^-86.4` at
  `2^40` queries, `2^-62.4` at `2^64`.
- **Binding**: the same commitments (`W`, `T`, the index) and the same out-of-domain answers.
- **The reduction's terms**, a query: the copy round `(6n + 8)/|E| ≈ 2^-163.4` and `≈ 2^-169` for `B` (main's);
  the identity at `t`, `≤ 4n/|E| ≈ 2^-166` (main's); new: `d d'(0) = 0`, `2/|E|`; the witness claim's conic,
  `3/|E|` (main's `ρ` batch was `3/|E|`). All far below the openings'.
- **Structural conditions**: `errors_have_their_own_poles` (main's, asserted in `Index::new`) holds for the swapped
  roles, with no random row needed (`membership_is_a_wired_loop_free_circuit`). Nothing new is needed for
  soundness; completeness needs `σ_{n−2} ≠ 0`, which `Index::new` asserts too (and that `σ_{n−1} = 0`, a theorem).
- **Adversarial tests** (`protocol::tests::absorbed_errors_fail_the_copy_claim`): a prover absorbing a bad witness's
  errors into `h` after `μ` (its quotient then a polynomial, its sum over the cells not zero) passes the witness and
  wiring claims and fails the copy claim, whether it drops `x h`'s coefficient `n`, puts it in digit 1, or zeroes the
  sum at one cell; for a gate's error, a pin's, a copy's, a copy alone, and two equal gate errors. The negative
  control (two `X` cells made a 2-cycle, which `Index::new` refuses) passes every claim with those two errors.
  `claims_hold_exactly_for_a_witness`: an honest prover on bad witnesses, and changed row values.
  `the_quotient_table_is_laid_out`: `B_0(0) = 0`, the blinding in digit 1, `q`'s digits full, the limb-3 slots empty.
  `products_by_x_in_the_novel_basis`: `mul_x`, `div_x` against evaluation.

## Zero knowledge

Assuming a zero-knowledge PCS (ZK-WHIR), as before. The revealed scalars are `W`'s and `T`'s out-of-domain answers
and `X`, `C`, `V + Y` at `t`; `next` is public, and the three claims' values are computed from them. Both groups are
affine and of full rank:

- **W**: the three row values and `W`'s answer, `K`-linear in the cells, affine in the 32 random-row words: rank 12
  of 12 (was 15 of 15);
- **T**: `T`'s answer, affine in the free blinding `b_0, b_1` (6 words), `b_2` solved and affine in them (it makes
  `q`'s coefficient `n` zero, a linear condition): rank 3 of 3.

`hiding::revealed_scalars_are_uniform` (toy circuit) and `revealed_scalars_are_uniform_on_membership` (`2^22` rows,
ignored by default; passed on h3 in 46 s) check both ranks and that both maps are additive and `K`-linear. Root hiding in
the random-oracle model keeps its margins: `W` 2,048 bits of random rows against 12 elements (768 bits) revealed;
`T` 384 bits of free blinding against 192 revealed.

## Prover

`/root/pcs-perf/r2-membership-gas/bench.sh` on h3 (`final/bench.sh`'s protocol: 8 threads, `LEANVM_NUM_THREADS=8
taskset -c 0-7`, the shared lock, the idle check), main and this branch interleaved, five runs each, medians:

| | main | this branch |
|---|---|---|
| reduction (two commitments) | 0.596 s | 0.667 s |
| openings | 0.616 s (four) | **0.338 s** (three) |
| prover total (witness .. openings) | 1.228 s | **1.021 s** (−17%) |
| peak memory | 6.01 GiB | 6.01 GiB |

The reduction pays 71 ms: the pass's two extra columns (`w_1 w^2`, `w_1 w (x + σ)`: products, leaf and upper
transforms, about 25 ms), and the tables (`x h`, `b_2`'s correction, `A_1 = Q_h / x`, clearing the scratch, about
45 ms). The sum's opening on `T` (`2^28` words) was 0.28 s. The rows are main's (3,878,615 of `2^22`). Under the EIP
draft's metric (measured time plus 0.1 s a claim) the branch also saves 0.1 s for the claim it drops.

## Tried, and rejected

- **A wiring the verifier evaluates itself** (lever 1: −4,584 gas, and the two `SLOAD`s). The verifier would compute
  `σ(t)` as `Σ_pieces 1_piece(t) · A_piece(t)`, each piece a coset of a subspace on which `σ` is `F_2`-affine
  (`1_piece = c Z / (L(x) + L(c))`, `L` the subspace's linearized vanishing polynomial; the affine map a linearized
  polynomial of `q`-degree below the subspace's dimension, so that the product stays below degree `n`): about four
  constant multiplications and an inversion slot a piece. The budget is the execution the standard price leaves under
  the floor, about 6,000 gas (300 multiplications by constants; past about 11,000 the gas exceeds main's). Keccak's
  wiring does not fit:
  - **Rotations are not affine in any encoding**: a rotation of 64 bits by an odd amount is a 64-cycle, and an affine
    map of `F_2^6` has order at most 63 (2-power orders need a unipotent Jordan block, of order at most 8 in
    dimension 7). Per-array encodings move rotations but cannot remove them: θ's `c[x+1][z−1]` closes a cycle
    `c → d → c` with net rotation 5, odd; χ's three reads per plane close about 30 independent cycles of nonzero net
    rotation. Each rotated edge class costs its carry pattern's pieces (up to 7).
  - **Lanes are 25, and their maps (`x ± 1`, `x ± 2 mod 5`, π) are not affine on any 5-bit encoding**: a piece per
    lane per edge class. Together about 150 pieces or more, 600+ multiplications: the standard price binds.
  - **No room to pad**: the circuit fills 92.5% of `2^22` rows (34 permutations × 24 rounds × about 4,800 rows), and
    `T` caps it there (`q` and `h` take `9n` words, `T` has `8n` at `2^23` rows). Power-of-two blocks for the
    instances (34 → 64, 24 → 32) or for a round (4,800 → 8,192 rows), or copy layers that route rotations, need far
    more rows than the 7.5% left.
- **Revealing `Q_h(0)` instead of fixing it with `b_2`** (no correction): 24 bytes, −1,512 gas net of the sum
  claim's 3,048 where the correction saves all of it.
- **Solving with `b_0`** (`γ = (d d')_n`, no `X_{2n}` term): `σ`'s top coefficient is zero for every wiring, so
  `γ = (w^2)_n + β (w (x + σ))_n` has no `α` and a witness's random rows decide whether it vanishes: a completeness
  error near `2^-128` at best, unproven. `b_2`'s `γ` carries `α β σ_{n−2}`.
- **Two blinding coefficients, one solved**: `T`'s out-of-domain answer keeps rank 3, but its root's min-entropy past
  the answer would be 192 bits of blinding against 192 revealed.
- **Two revealed row values**: no degree-2 gate on two cells (above).
- **A claim fewer**: `W` and `T` are committed in different rounds (`α, β, μ` between them) and the index is fixed, so
  three commitments take three claims; two needs the succinct wiring.
- **The frame's index byte** (−64): kept, as in π2 (a fixed index constrains the transaction's frames).

## What the Lean needs

`formal/` proves `f96a7938`'s protocol (six claims on four commitments); main's (`PERF_GAS.md`) was not ported
either. Porting to this one means, beyond `PERF_GAS.md`'s list:

- **`formal/Statement/PcsQuotient`**: `Circuit`, `Relation`: the gate `V + Y + C + X C` and the builder's swapped
  roles, the random rows' shapes; `Verifier`, `Reduction`, `Transcript`, `Domain`: the stream (three row values),
  the witness claim's conic point and weights, the copy point's digit coordinate `ζ / (1 + ζ)`, `ζ = Z t`, its kind
  coordinate and value (`t R / (ζ + d d')`), the batched inversion's denominators (`1 + ζ`, `ζ + d d'`, `a + b`), no
  sum claim; `Prover`: `B_0 = x h_low`, `b_2` solved, `w_1 d d'`, the `X_{2n}` term, `A_1 = Q_h / x`, and the
  novel basis's `mul_x` / `mul_w1` / `div_x`; `Opening`, `PcsOpening`, `Extractor`: three claims.
- **`formal/EndToEnd`**: `Soundness`: the sum from the layout (the argument above: `I(0) = d d'(0) B_0(0)`, then
  degree), and the conic binding of the witness claim (a non-degenerate conic spans its plane, so `λ(ρ) · Δ` is a
  nonzero quadratic); `ksBound` with three openings; `E2ECompleteness`: `b_2`'s existence (`γ ≠ 0` but at one
  value of `α`, given `σ_{n−2} ≠ 0`, which the membership circuit meets by computation); `ZK`: `RevealedUniform` over
  the new revealed scalars (two rank conditions).
- **`formal/Implementation`**: `Graph.lean` regenerated (`UPDATE_LEAN=1 cargo test -p evm graph_lean_is_current`,
  ignored until the port), `Calldata` (273 bytes, no selector, six scalars), `Evm.evm_accepts_iff_verifyWith`.
- **`formal/Circuit`**: the dump (`examples/dump_circuit.rs`) and `CircuitTest/Dump.lean` with the swapped roles.
- **Vectors**: `examples/statement_vectors.rs` (ten-scalar streams, three openings), `tests/whir_bridge_vector.rs`,
  the evm `write_lean_vectors`, all regenerated by their tests.

## Files

- `crates/membership/quotient/src/circuit.rs`: the gate `V + Y + C + X C`, the builder's roles, the random rows.
- `crates/membership/quotient/src/protocol.rs`: `mul_x`, `mul_w1`, `div_x`, `row_values`, `witness_conic`,
  `witness_weights`, the prover (`x h`, the products `w_1 w^2` and `w_1 w (x + σ)`, `b_2`, `A_1`), `reduce`, three
  claims, the tests; `Index::new` asserts `σ_{n−2} ≠ 0`.
- `crates/membership/quotient/src/hiding.rs`: ranks 12 and 3.
- `crates/membership/evm/src/{codegen,quotient,adversarial,lean}.rs`: no selector, 273 bytes, three claims; the
  pinned bytecode digests.
