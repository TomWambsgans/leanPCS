# The membership protocol

A zero-knowledge proof of Keccak-256 Merkle membership (depth 32: `y = H(x | 0x11..)`, a path from
`H(x | 0x22..)` to `root`), reduced to **three PCS claims on two commitments and the circuit's** by six field
elements and no sumcheck (`crates/membership/quotient`, `protocol.rs`; transcript name `pcs-quotient-kc3`). The
claims are the EIP draft's ([`../PCS_CLAIM.md`](../PCS_CLAIM.md), version 1), each opened by one opening of leanVM's
WHIR. The verifier is `protocol::reduce`, generic in its scalar, so the same code is the EVM contract
(`crates/membership/evm`).

The Lean in `formal/` states and proves this protocol ([`../../formal/README.md`](../../formal/README.md),
"Membership: the end theorems"): knowledge soundness with no hypothesis, completeness under one evaluated check, zero
knowledge under the ZK-PCS assumption and `RevealedUniform`, the contract = the verifier.

Notation: `K = GF(2^64)`, `E = GF(2^192)`, `m = log_rows + 2` (`m = 24` at `2^22` rows), `n = 2^m` cells, the cells
the additive subspace of the domain (`domain.rs`), `X_j` the subspace polynomials of the novel basis, `Z = X_n` the
cells' vanishing polynomial, `w_1 = X_2`. A multilinear claim at a point built from one element `t` is a univariate
evaluation (`domain.rs`), so the protocol is a gate-and-copy argument on the subspace.

## Circuit

`circuit.rs`. A row has four cells `X, Y, C, V` and one gate, **`V = Y + C + X·C`**. On bits it is `Y ⊕ (C ∧ ¬X)`:
Keccak's χ with `(X, Y, C) = (a[x+1], a[x], a[x+2])`, an XOR with `(0, a, b)`, a NOT with `(0, 1, a)`. A free input
bit is a row whose three inputs are wired to its own output (`v = v + v + v^2`, so `v^2 = v`); every other row reads
constants or earlier rows, so every cell is a bit. The product is of `X`, the cell the copy argument reads at `t`,
and `C`: the verifier needs a row only through `X`, `C` and `V + Y`.

- **The statement**: 34 Keccak-256 (the leaf, 32 path steps, `y`), 3,878,615 of `2^22` rows.
- **Public values** as eight pinned `K`-words (`Statement::words`, eight bytes big-endian each), each packed from
  its 64 bits by 63 rows of Horner's rule, `(X, Y, C) = (3, b, acc)`, `V = b + 2·acc` (`2` the generator of `K`'s
  polynomial basis), built after every other row.
- **Anchors**: the first `PUBLIC_ROWS = 11` rows. Anchor `k` is `(0, 0, s_k)`, its `C` cell (`anchor_cell(k) =
  4k + 2`) on the cycle of `s_k`: the packed word `k` for `k < 8`, then the constants `0`, `1`, `3`. The anchors of
  `1` and `3` are `(0, 1, 1)` and `(0, 3, 3)`, reading their constant twice (for the pole condition below). The
  verifier pins the eleven `C` cells by interpolation, which pins every cell on their cycles.
- **Random rows** (`RANDOM_ROWS = 16`, `RandomShape`): idle rows made rows of two free cells, each its own cycle
  (`Src::Free`), in three shapes `(X, Y, C, V) = (0, r, s, r + s)`, `(s, r, 0, r)`, `(1, r, s, r)`. The gate holds
  for any `r, s` and every cell is affine in them. The prover draws two words a row (32 words).
- **The pole condition** (`Circuit::errors_have_their_own_poles`): every cycle of the wiring with more than one cell
  holds a cell that is neither a row's first (`X`) cell nor a pin, the random rows left out of the count. It holds
  by the structure: a row's output cycle holds its `V` cell, a packed word's its last packing row's `V` cell, the
  zero's the anchors' `Y` cells, the one's and the three's their anchors' `Y` cells. `Index::new` asserts it, so no
  circuit that fails it can be indexed. `Index::new` also asserts the wiring's coefficient `n − 2` nonzero, which the
  honest prover needs (below); its coefficient `n − 1` is zero for every permutation.

The `Index` keeps σ's values on the quotient's coset (`2n` points, 256 MiB at `2^22` rows), which every proof reads.

## Tables and claims

Two committed tables and the circuit's, each a commitment (root and out-of-domain answer, [`../PCS_CLAIM.md`](../PCS_CLAIM.md)):

| table | variables (at `2^22` rows) | content | claims |
|---|---|---|---|
| `W`, the witness | `m` (24) | the cells' polynomial `w` (`deg < n`): the four row polynomials interleaved, `w = a_0 + x a_1 + w_1 (a_2 + x a_3)` | 1 |
| the wiring (public; root and answer in the contract's storage) | `m` (24) | σ's coefficients | 1 |
| `T`, the quotient table | `m + 4` (28) | the quotient `q` and `x h` | 1 |

**The identity.** With `d = α + w + β x`, `d' = α + w + β σ` and `g = gate / Z_R + (w + v) / Z_P` (`Z_R` vanishing on
the rows' first cells, `Z_P` on the eleven pins, `v` the public values' interpolant on them; `g` is a polynomial
exactly when every gate and every pin holds, since `Z_R` and `Z_P` have no common root):

  `Z q + d d' h = d + d' + μ Z g`  and  `Σ_cells h = 0`,

`h` the copy argument's sum polynomial (its logarithmic derivative, blinded), `μ` drawn after `W` with `α, β`. The
gates and the pins are checked through the sum: there is one quotient, no separate gate quotient, no `γ`.

**`T`'s layout** (`protocol::table_slot`): word `i + n (digit + 2 limb + 8 kind)`; each `(kind, limb)` holds two
polynomials of `n` coefficients over `K`, digit 0 and digit 1, read as `F_0 + ζ F_1` with **`ζ = Z x`**:

- kind 0, limb `e < 3`: limb `e` of `q = A_0 + ζ A_1` (`deg q ≤ 2n`, two digits);
- kind 1, limb `e < 3`: limb `e` of `P = x h = B_0 + ζ B_1`, `B_0 = x h_low`, `B_1` the blinding
  `ε = b_0 + b_1 X_1 + b_2 X_2` (`h = h_low + Z ε`, `H_BLIND = 3`);
- limb 3 of either kind: zero (a prover may fill it; it is read as a fourth limb of weight `Y^3`).

**The three claims** (`Claims`):

- **witness**, on `W` at a point of the row polynomials' conic that binds `X`, `C`, `V + Y` at `t`
  (`witness_point`, `witness_conic`, `witness_weights`): its low coordinates `(z_0, z_1) = (ρ, a / (a + b))`,
  `a = (t + θ ω)(1 + ρ) + ρ`, `b = θ (1 + ρ)`, `ω = w_1(t)`, `θ = β_1`; its value `λ · (X, C, V + Y)` times the higher
  coordinates' normalisation;
- **wiring**, on the circuit's table at `t`: `next = σ(t)`;
- **copy**, on `T` at `t` (`copy_point`): digit coordinate `ζ / (1 + ζ)`, kind coordinate `κ = d d' / (ζ + d d')`,
  value `(1 + κ) q + κ P = t (d + d' + μ Z g) / (Z t + d d')` up to public scales. The verifier computes it; no
  table value is sent.

**The honest prover.** `{A_0 + Z x A_1}` is not every polynomial of degree `≤ 2n`: writing `q = q_low + Z Q_h`, it
needs `Q_h(0) = 0`, `q`'s coefficient `n` zero. The prover spends `b_2`: it runs the quotient's pass with `b_2 = 0`,
then sets `b_2 = q_n / γ`, `γ` the high part of `E = w_1 d d'` at 0, which adds `b_2 E` to `q` and `Z w_1 b_2` to `h`
(nothing on the cells). `γ = (d d')_{n−2} = α β σ_{n−2} + (terms without α)`, nonzero but for one `α` when
`σ_{n−2} ≠ 0` (which `Index::new` asserts): completeness error `≤ 2/|E|`. The correction needs `E`'s coefficients,
so the pass also writes `w_1 w^2` and `w_1 w (x + σ)` on the coset (in `T`'s empty limb-3 slots), and the prover
adds `b_2 (α^2 w_1 + α β w_1 (x + σ) + w_1 w^2 + β w_1 w (x + σ) + β^2 w_1 x σ)` to `q`'s coefficients. Then
`A_1 = Q_h / x`. Products and quotients by `x` in the novel basis need no multiplication (`mul_x`, `div_x`,
`mul_w1`): with `x^2 = w_1 + x`, `x F`'s coefficient `j ≥ 1` is `f[j−1] + f[j + low(j) − 1]`, and the quotient runs
the relation back along `j ↦ j + low(j)`, level by level.

## Transcript

A Keccak-256 chain (`transcript.rs`): a challenge is the Keccak-256 of the state and of every scalar sent since the
last challenge (256-bit big-endian words); its digest is the new state and its low 192 bits the challenge. The seed
is the Keccak-256 of `label` (136 bytes): the name `pcs-quotient-kc3`, the circuit's root and out-of-domain answer,
`y`, `root`. A commitment rides the stream as its root's two halves, then its answer.

  `W` (root, answer) → `α, β, μ` → `T` (root, answer) → `t` → `X, C, V + Y` at `t`, `next` → `ρ`.

The stream is two roots and six elements of `E`. The verifier does one batched inversion (of every `1 + w_k`,
`1 + ζ`, `ζ + d d'`, the rows' polynomial, every `t + p_k` of the pins, and `a + b`) and checks one nonzero product
(`VerifyError::Degenerate` otherwise).

## Soundness

**The sum, by the layout.** Fix `W`, `α, β, μ`, `T`; let `R = d + d' + μ Z g`. The copy claim at `t` holds iff
`I(t) = 0`, `I = x Z q + d d' P + x R` (characteristic 2), whenever its denominators are nonzero. `deg I ≤ 4n`, so if
`I ≢ 0` the claim holds with probability `≤ 4n/|E| ≈ 2^-166` over `t`. If `I ≡ 0`:

1. at `x = 0`, `d d'(0) P(0) = 0` and `P(0) = B_0(0)`; `d(0)`, `d'(0)` are nonzero but with probability `2/|E|`
   (`w` committed before `α, β`), so `B_0(0) = 0`;
2. `h := P / x = B_0 / x + Z B_1` is a polynomial, `B_0 / x` of degree `≤ n − 2`; a polynomial of degree `≤ n − 2`
   sums to zero over an `F_2`-subspace of `n` points, so `Σ_cells h = 0`;
3. dividing by `x`: `Z q + d d' h = R` as polynomials.

Read through `Z` instead of `Z x`, digit 1 would be divided by `x` too, `Z / x` is not zero at the cell 0, and the sum
would move freely with `B_1(0)`; through `Z x` digit 1 is `Z B_1` after the division, zero on every cell.

**The pole lemma.** On a cell the identity sets `h(x) = 1/d(x) + 1/d'(x) + μ e(x) / (d d')(x)`, `e(x)` the gate's
error at a row's first cell or the pin's at a pinned cell, times a nonzero constant. So
`Σ_cells h = A(α, β) + μ B(α, β)`, `A` the logarithmic derivatives' sum, `B = Σ_x e(x) / (d d')(x)`.

- If `B ≢ 0`, the sum vanishes with probability `≤ 2|L|/|E| + 1/|E|` (`L` the error cells, `|L| ≤ n/4 + 11`):
  about `2^-169`.
- `B ≡ 0` forces every error to zero under the pole condition. The pole of `1/d(x)` on the line
  `α + w(x) + β x = 0` is shared only with the term of `x`'s predecessor on its cycle. Walk each cycle from a cell
  outside `L`: the first error cell's pole is its term's alone, so its error is zero, and so on. A free cell has a
  double pole that nothing cancels. Without the condition a cycle of rows' first cells lets two errors cancel.
- Then `A = 0` gives the copies.

**The witness claim binds three values** (the conic). In `a`-coordinates, `X = (1, τ, ω, τ ω)`,
`C = (1, τ + θ, ω + 1, (τ + θ)(ω + 1))`, `V + Y = (0, θ, 1, τ + θ ω + θ + 1)`. Their span is the plane `n · e = 0`,
`n = (τ + θ ω, 1, θ, 0)`, which meets the Segre quadric of rank-one tensors in a conic, non-degenerate since
`n_0 n_3 = 0 ≠ θ = n_1 n_2`. `(a + b) e(ρ)` traces the conic and spans the plane, so its coordinates in the basis
`(X, C, V + Y)` are independent quadratics in `ρ`: a revealed `Δ ≠ 0` passes at most 2 values of `ρ`, plus
`a + b = 0`: `3/|E|`. Two values would not do: a two-dimensional span one rank-one claim binds is a line of the
quadric, two cells with the same `w_1`, and a gate on two cells computes nothing.

**One bound table each.** `W`, `T` and the index bind to one table each by their out-of-domain answers
([`../PCS_CLAIM.md`](../PCS_CLAIM.md), "Why the out-of-domain answer binds").

**Bounds, a query.** The three openings (`2^24`, `2^24`, `2^28` words), `3 · 2^-128`, dominate: **126.4 bits as
`Q/ε`**, about `2^-105.4` at `Q = 0`, `2^-86.4` at `2^40` queries, `2^-62.4` at `2^64`. The reduction's terms: the
copy round `(6n + 8)/|E| ≈ 2^-163.4` and `≈ 2^-169` for `B`; the identity at `t`, `≤ 2^-166`; `d d'(0) = 0`, `2/|E|`;
the conic, `3/|E|`.

**Tests.** `protocol::tests::absorbed_errors_fail_the_copy_claim`: a prover absorbing a bad witness's errors into `h`
after `μ` passes the witness and wiring claims and fails the copy claim, whether it drops `x h`'s coefficient `n`,
puts it in digit 1, or zeroes the sum at one cell; for a gate's error, a pin's, a copy's, and two equal gate errors.
The negative control (two idle rows' `X` cells made a 2-cycle, which `Index::new` refuses) passes every claim with
those two errors. `claims_hold_exactly_for_a_witness`, `the_witness_claim_is_on_the_conic`,
`the_quotient_table_is_laid_out`, `products_by_x_in_the_novel_basis`, `membership_is_a_wired_loop_free_circuit`.

## Zero knowledge

**Assuming a zero-knowledge PCS opening** (ZK-WHIR), as the EIP does. The reference openings are leanVM's WHIR,
which reveals Merkle rows and sumcheck messages: **not** zero knowledge. What the protocol provides on its own is
that everything public besides the openings is simulatable from the statement.

**What is public**: the two commitments (root, out-of-domain answer), `X`, `C`, `V + Y` at `t`, and `next` (the
public wiring's value). The claims' values add nothing: the witness claim's is a combination of the three row
values, the wiring's is `next`, the copy claim's a function of the row values, `next`, the challenges and the
statement.

**The randomness**: the 16 random rows (32 words, `Randomness::rows`) and the blinding `b_0, b_1` (6 words,
`Randomness::blind`); `b_2` is solved by a linear condition, hence affine in `b_0, b_1` (the witness fixed). There
are no masks: `w` keeps degree `< n`, which the quotient's degree needs.

**The argument.** Fix the challenges. Each group is affine in its randomness once the one before is fixed:

1. `X`, `C`, `V + Y` and `W`'s answer are `K`-linear in the cells, hence affine in the 32 random-row words, rank 12
   (all their `K`-coordinates);
2. `T`'s answer is affine in the 6 free blinding words: the blinding enters `x h`'s digit 1 directly and `q` through
   `b d d'`, and `μ g` does not depend on it. Rank 3.

So the revealed scalars are uniform at the challenges where both ranks are full. Group 1's rank falls short only
where a determinant of the challenges vanishes: probability at most its degree over `2^192` (not written out). Group
2's does not depend on the challenges alone: the blinding reaches `q` through `(b_0 + b_1 X_1 + b_2 X_2) d d'` and
`b_2 = q_n / γ`, both functions of `w`, hence of the random rows `R`, so its `K`-linear map `L_R` (6 words to `T`'s
answer, 3 `K`-coordinates) is rank-deficient on the zero set of its `3 × 3` minors in `R`, which over `K` is
nonempty in general. The revealed scalars are therefore uniform only up to a statistical distance `δr`, about
`2 Pr_R[rank L_R < 3 or γ = 0] ≲ 28 / 2^64 ≈ 2^-59` per proof (the minors' degree in `R` over `|K|`; reasoned, not
proved): the formal statement (`formal/Statement/PcsQuotient/Zk.lean`, `RevealedUniform εr δr`) carries it, and it
dominates the zero-knowledge error. Blinding words drawn in `E` (or a rank-3 path of `b` independent of `R`) would
bring it to about `deg / 2^192`. The
**simulator** samples the out-of-domain answers and the row values uniformly, computes the claims' values, and
simulates the openings with the ZK-PCS simulator.

**Tested**: `hiding::revealed_scalars_are_uniform` fixes the challenges and the out-of-domain points (test hooks in
`transcript.rs`, `opening.rs`), changes one randomness word at a time on the toy circuit (`2^17` rows), and checks
both ranks (12, 3) over `K` and that both maps are additive and `K`-linear. `revealed_scalars_are_uniform_on_membership`
does the same at `2^22` rows (ignored by default, about 50 s on 64 threads:
`cargo test --release -p quotient --lib hiding -- --ignored`).

**The roots** hide in the random-oracle model while each table keeps min-entropy given what is revealed: `W` 2,048
bits of random rows against 12 `K`-coordinates (768 bits), `T` 384 bits of blinding against 192. With salted leaves
(a ZK-WHIR) the roots hide regardless.

**Not covered**: the openings (above); a pre-proof phase and several proofs (single-proof ZK). Deployed randomness
is a Keccak-256 KDF (`Randomness::derive`: the random rows' words, then the blinding), so zero knowledge is
computational.

## Where the gas goes

The transaction is floor-bound (EIP-8141 with EIP-7976's floor, `pcs_gas` in it): `64 · (calldata + frame) + 5,000 +
1,000 · claims`, the frame `1 + 32` bytes a claim. A calldata byte costs 64 gas, a claim `32 · 64 + 1,000 = 3,048`, a
commitment in calldata (root and answer, 56 B) 3,584, a revealed element of `E` (24 B) 1,536.

| | |
|---|---|
| fixed: statement, frame index, frame header, 5,000 | 9,224 |
| commitments in calldata (`W`, `T`) | 7,168 |
| claims: 3 (witness, wiring, copy) | 9,144 |
| revealed scalars past the roots and answers: 4 (`X`, `C`, `V + Y`, `next`) | 6,144 |
| **transaction gas** | **31,680** |
| calldata / frame of PCS claims | 273 B / 97 B |
| execution (does not bind) | 15,753 (343 `FIELD_MUL`s; two cold `SLOAD`s) |
| standard price (does not bind) | 29,649 |
| contract code / deployment | 4,866 B / 1,149,640 gas |

`cargo test --release -p evm -- --ignored --nocapture --exact quotient::tests::gas_report`. The standard price stays
2,031 gas under the floor. In the EIP draft's table: 273 bytes, PIOP 20,097 gas (the PIOP frame's
`max(standard, floor)`: standard `16 · 271 + 4 · 2 + 15,753 = 20,097` binds, floor `64 · 273 = 17,472`), 3 claims.

**The ABI** (`evm/src/quotient.rs`): `(bytes32 y, bytes32 root, bytes proof)` packed, no selector, then the frame's
index: exactly 273 bytes (`y`, `root`, the two roots, six 24-byte scalars, the index byte). The contract checks that
the named frame is a dependency verification frame of scheme `PCS_SCHEME` whose payloads `0 .. 2` are the three
claims' hashes, in order, and returns the word 1; it reverts on value, on another length, and on a rejected or
degenerate proof. `setIndexCommitment(bytes32, bytes32)` keeps its selector (68 bytes); the constructor takes the
index root, its answer and the owner.

## Integration

- **The owner.** The contract holds the circuit's commitment only and cannot check the pole condition. The owner of
  `setIndexCommitment` (and the deployer) can install any commitment, one of a circuit that fails the condition
  included, and with it accept false statements. Install only commitments of circuits indexed by `Index::new`, and
  deploy with no owner (owner 0, which fixes the commitment for good) in production.
- **No application context.** A proof binds only `(y, root)`, no sender, action or nullifier domain: a proof seen in
  the mempool can be resubmitted by anyone. An application that uses `y` as a nullifier needs a signal of its own in
  the statement.
- **No `DELEGATECALL`.** The contract reads its index commitment from storage slots 0 and 1: `CALL` or `STATICCALL`
  it (it writes nothing).

## Rejected alternatives

- **A separate claim for `g`** (beside `q` in `T`): 39,568 gas at the four-claim stage, 3,048 more than merging.
- **`h` committed first** (`W`, `H`, `μ`, `q + μ g`): the textbook order, sound for any circuit, three commitments,
  44,688 gas. The pole lemma lets `h` share `q`'s table.
- **One claim on `T` for two independent identities**: two free coordinates, five high bits, `2^29` words, past
  WHIR's `2^28`.
- **The public bits as a `γ`-weighted sum** in `h`: a weight of degree about `n`, `q` of four digits, `q` and `h` no
  longer fit `2^28` words. Pinning the 1,024 bits instead costs 1,024 inverses; packing them into words costs 504
  rows.
- **`x h` read through `Z`**: the digit-1 word moves the sum freely (above); `ζ = Z x` fixes it.
- **A wiring the verifier evaluates itself** (−4,584 gas and the two `SLOAD`s): σ piecewise `F_2`-affine on cosets
  of subspaces, about four constant multiplications a piece, within the about 6,000 gas the floor leaves. Keccak's
  wiring needs about 150 pieces or more: a 64-bit rotation by an odd amount is a 64-cycle, which no affine map of
  `F_2^6` is; the lanes' maps (`x ± 1`, `x ± 2 mod 5`, π) are affine on no 5-bit encoding; and the circuit fills
  92.5% of `2^22` rows, leaving no room to pad to power-of-two blocks.
- **A row-level (column) layout**, a gate quotient of degree `n/4`: three more revealed values and a quotient a
  column, nothing saved.
- **Revealing `Q_h(0)` instead of fixing it with `b_2`**: 24 bytes, saves 1,512 net where `b_2` saves all 3,048.
- **Solving with `b_0`**: σ's top coefficient is zero for every wiring, so `γ` would carry no `α` and the random rows
  would decide whether it vanishes. `b_2`'s `γ` carries `α β σ_{n−2}`.
- **Two blinding coefficients, one solved**: `T`'s root would keep 192 bits of blinding against 192 revealed.
- **Two revealed row values**: no degree-2 gate on two cells. **A claim fewer**: three commitments in different
  rounds take three claims; two would need the succinct wiring.
- **Dropping the frame's index byte** (−64 gas): kept, as in π2.

## Files

- `crates/membership/quotient/src/circuit.rs`: the gate, the builder, anchors and packing rows, `Src::{Three, Free}`,
  `RandomShape`, `Circuit::randomize`, `Circuit::errors_have_their_own_poles`.
- `crates/membership/quotient/src/protocol.rs`: `Index` (its asserts), the prover (`x h`, the products `w_1 w^2` and
  `w_1 w (x + σ)`, `b_2`, `A_1`), `reduce`, `table_slot`, `copy_point`, `witness_conic`, `witness_weights`,
  `row_values`, `pins`, `mul_x`, `mul_w1`, `div_x`, the tests.
- `crates/membership/quotient/src/{statement,transcript,opening,domain,ntt}.rs`: `Statement::words`, the Keccak-256
  chain, the PCS claims and their openings, the domain, the transforms.
- `crates/membership/quotient/src/hiding.rs`: the rank and affinity tests.
- `crates/membership/evm/src/{codegen,quotient,contract,record,machine,adversarial,lean}.rs`: the contract, its ABI and
  deployment, the gas report, the adversarial tests, `formal/Implementation/Graph.lean`'s renderer.
- Prover measurements: [`../PERF_PROVER.md`](../PERF_PROVER.md); figures: [`../../AGENTS.md`](../../AGENTS.md),
  "Numbers".
