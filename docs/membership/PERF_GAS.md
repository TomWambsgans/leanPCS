# Cutting the membership proof's gas: one quotient, one table

Branch `perf/membership-gas`. The ZK Keccak-256 Merkle membership proof (benchmark 1 of the EIP draft) goes from
**52,856 to 36,520 gas** (−30.9%), with a prover that is 32% faster and uses 25% less memory. The PCS claim format
(`docs/PCS_CLAIM.md`) and the EIP draft are unchanged. The Lean in `formal/` is **not** updated on this branch:
it still proves the previous protocol (see "What the Lean needs" below).

## Where the gas goes

The transaction is floor-bound (EIP-8141 with EIP-7976's floor, `pcs_gas` in it):
`64 · (calldata + frame) + 5,000 + 1,000 · claims`, the frame `1 + 32` bytes a claim. So a calldata byte costs 64
gas, a claim `32 · 64 + 1,000 = 3,048`, a commitment in calldata (root and out-of-domain answer, 56 B) 3,584, and a
revealed element of `E` (24 B) 1,536.

| | main | this branch |
|---|---|---|
| fixed: selector, statement, frame index, frame header, 5,000 | 9,480 | 9,480 |
| commitments in calldata | 4 (W, H, Q, G): 14,336 | **2** (W, T): 7,168 |
| claims | 6: 18,288 | **4**: 12,192 |
| revealed scalars past the roots and answers | 7 (`a_0..a_3`, `next`, `Q`'s and `G`'s values): 10,752 | **5** (`a_0..a_3`, `next`): 7,680 |
| **transaction gas** | **52,856** | **36,520** |
| calldata | 461 B | 301 B |
| frame of PCS claims | 193 B | 129 B |
| execution (does not bind) | 18,899 | 16,414 |
| standard price (does not bind) | 40,315 | 32,270 |
| contract code / deployment | 6,667 B / 1,536,984 gas | 5,304 B / 1,242,838 gas |

`cargo test --release -p evm -- --ignored --nocapture --exact quotient::tests::gas_report`. The execution stays
4,226 gas below where the standard price would bind (`48 · 430`). In the EIP draft's table the row would read 301
bytes, PIOP 19,264 gas (`64 · 301`), 4 claims, 36,520 gas.

## What changed

Five changes, each needed by the next.

1. **Public values as pinned words, not a weighted sum.** The circuit packs `y` and `root` into eight `K`-words
   (`Statement::words`, eight bytes big-endian each) by 63 rows of Horner's rule each (`(X, Y, C) = (b, 3, acc)`,
   `V = b + 2·acc`, `2` the generator of `K`'s polynomial basis). Eleven **anchor** rows `(0, 0, s_k)` put a cell
   (`C`, cell `4k + 2`) on the cycle of each word and of the constants `0`, `1`, `3`. The verifier pins those eleven
   cells to the statement's words and the constants by interpolation: `g = gate / Z_R + (w + v) / Z_P` is a
   polynomial exactly when every gate holds and every pin holds, since `Z_R` (the rows' first cells) and `Z_P`
   (the pins, `C` cells) have no common root. The verifier evaluates `g(t)` with eleven more inverses in its one
   batched inversion. Before, the public bits entered the copy argument's sum polynomial `h` through a weight of
   degree about `n`, which made the copy quotient of degree about `3n`. Now `h` is the logarithmic derivative alone,
   and `γ` is gone.
2. **No masks: random rows of free cells.** The witness is the cells' polynomial alone (degree `< n`, a table of
   `2^m` words, not `2^(m+1)`). Its randomness is 16 random rows of three shapes, `(r, 0, s, r+s)`, `(r, s, 0, r)`,
   `(r, 1, s, r)`, whose cells are each their own cycle (`Src::Free`). Every cell is affine in the row's two words.
   Before, the masks (multiples of `X_n`) raised `w` to degree `n + 15`.
3. **`h` blinded by two coefficients a limb** (`X_n (b_0 + b_1 X_1)`, was eight). With 1 and 2,
   `deg(h d d') ≤ (n + 1) + (2n − 2)`, so the quotient has degree `< 2n`: two digits.
4. **One quotient.** `μ` is drawn after `W`, with `α` and `β`, and the identity is
   `Z q + d d' h = d + d' + μ Z g`, so `q = (h d d' + d + d') / Z + μ g` (`d = α + w + β x`, `d' = α + w + β σ`,
   `Z = X_n`). The gates and the pins are checked through the sum, below.
5. **One table `T`** of `m + 4` variables (`2^28` words at `2^22` rows), word `i + n (digit + 2 limb + 8 kind)`
   (`protocol::table_slot`): kind 0 holds `q`'s three limbs, and kind 1 holds `h`'s three limbs with their blinding
   at digit 1. Limb 3 of both kinds is empty. Two claims read it:
   - **copy** at `(u, u_m, y_0, y_1, κ)`: `(1 + κ) q + κ h`. With `κ = d d' / (Z + d d')` this is
     `(d + d' + μ Z g) / (Z + d d')`. The verifier computes it from `a_j`, `next` and the pins, and no table value
     is sent.
   - **sum** at `h`'s top coefficient (kind 1, digit 0, all-ones): zero.

The claims are W at the row polynomials' point (four `a_j` combined by `ρ`, as before), the wiring at `t` (as
before), and the two on `T`. The transcript is W, `α`, `β`, `μ`, T, `t`, `a_0..a_3`, `next`, `ρ`.

### Why the merged quotient is sound

`h` is committed after `μ` and, from the copy claim at a random `t`, satisfies the identity as polynomials. On a
cell `x` the identity sets `h(x) = 1/d(x) + 1/d'(x) + μ e(x) / (d d')(x)`, where `e(x)` is the gate's error at a
row's first cell, or the pin's at a pinned cell, times a nonzero constant (`(Z/Z_R)(x)` or `(Z/Z_P)(x)`). So `h`
absorbs the errors, and only the sum claim can catch them: `Σ_cells h = A(α, β) + μ B(α, β)`, with `A` the
logarithmic derivatives' sum and `B = Σ_x e(x) / (d d')(x)`.

- If `B ≢ 0`, the sum vanishes with probability at most `2|L| / |E| + 1/|E|` (`L` the error cells, `|L| ≤ n/4 + 11`):
  about `2^-169`.
- `B ≡ 0` (as a rational function of `α, β`) forces every error to zero, provided **every cycle of the wiring with
  more than one cell holds a cell that is neither a row's first cell nor a pin**. The pole of `1/d(x)` on the line
  `α + w(x) + β x = 0` is shared only with the term of `x`'s predecessor on its cycle (through `d'`, when the two
  values agree). Walk each cycle from a cell outside `L`: the first error cell's pole is its term's alone, so its
  error is zero, and so on along the run. A free cell (its own cycle) has a double pole that nothing cancels.
- The membership circuit and the toy circuit meet the condition. `Circuit::errors_have_their_own_poles` checks it,
  in `circuit::tests::membership_is_a_wired_loop_free_circuit` and `protocol::tests::claims_hold_exactly_for_a_witness`.
  Every cycle holds the `V` cell of the row it carries, or, for the constants, `Y` and `C` readers. Without the
  condition it fails: a cycle made only of rows' first cells lets two errors cancel each other's poles.
- If `B ≡ 0`, then `A = 0` gives the copies, as before.

## Prover

The quotient lives on a coset of `2n` points, where it was on `4n`, and there is one quotient where there were two.
The witness table is `2^24` words, where it was `2^25`. One `2^28` commitment replaces `2^27 + 2^28 + 2^25`. There are
four openings (`2^24`, `2^24`, `2^28`, `2^28`), where there were six.

`/root/pcs-perf/bench-h3.sh <dir> membership` on h3 (AMD EPYC 9355P, 64 threads, shared; load 5–15). The runs were
interleaved, two each, and the numbers are means:

| | main | this branch |
|---|---|---|
| reduction | 0.649 s (four tables) | **0.376 s** (two tables) |
| openings | 0.255 s (six) | **0.237 s** (four) |
| prover total (witness .. openings) | 0.912 s | **0.625 s** (−31%) |
| peak memory | 8.71 GiB | **6.58 GiB** |
| openings' sizes | 291 / 278 / 313 / 335 / 288 / 311 KiB | 279 / 279 / 335 / 335 KiB |

The M4 Max was not re-measured, to spare the Mac. Under the EIP draft's prover metric (measured time plus 0.1 s a
claim) the branch also saves 0.2 s for the two claims it drops.

## Soundness

- **The openings still dominate.** They are four where there were six, so their union is `4 · 2^-128` a query:
  126 bits as `Q/ε`, against 125.4. The same accounting as `AGENTS.md`'s, scaled by `4/6`, gives about `2^-105.0`
  at `Q = 0`, `2^-86.0` at `2^40` queries and `2^-62.0` at `2^64`.
- **Binding.** Two commitments bind to one table each by their out-of-domain answers, where there were four, so
  there are fewer lists to separate.
- **The reduction's own terms**, a query, each far below the openings':
  - the copy round (`α, β, μ`): `(6n + 8)/|E| ≈ 2^-163.4` for the copies, as before, plus `≈ 2^-169` for `B`;
  - the identity at `t`: degree `≤ 4n` for a cheating table, `≤ 2^-166`;
  - the batching `ρ` of the `a_j`: `3/|E|`.
- **New arguments for the Lean.** Four steps are new: the pins by interpolation inside `g`, `g`'s merge into `q`
  with the pole lemma and the circuit's condition, the copy claim's fixed `κ`, and the sum claim on `T`. Each is a
  polynomial-identity or residue argument, but none is proved in Lean yet. The pole lemma is the one argument that
  needs a property of the circuit beyond its being wired and loop-free.

## Zero knowledge

ZK still assumes a zero-knowledge PCS opening (ZK-WHIR), as the EIP does. The revealed scalars are now W's and T's
out-of-domain answers and the four `a_j`. `next` is public, and the four claims' values are computed from the
revealed scalars. Both groups are affine in their randomness:
- `a_0..a_3` and W's answer are affine in the 32 random-row words, with rank 15 of 15;
- T's answer is affine in the 6 blinding words, the rows fixed, with rank 3 of 3. The blinding moves `q` by
  `b d d'`, and `μ g` does not depend on it.

`hiding::revealed_scalars_are_uniform` checks the ranks and also that both maps are additive and `K`-linear. The
non-affine group of main is gone. That group was the masks of `X` and `V` meeting in `G`, and the random rows'
`v²`; it was measured over `GF(2)`, not argued, and its tests are removed. The argument is therefore stronger than
on main: `RevealedUniform` is now two rank conditions, provable from a determinant's degree. Root hiding in the
random-oracle model has less margin for T: 384 bits of blinding against 192 revealed leave 192 bits, where main had
960. W keeps 2,048 bits of randomness against 960 revealed. With a salted ZK-WHIR the roots hide regardless.
`HIDING.md` has the details.

## Tried, and rejected

- **A separate claim for `g`** (the first step on this branch: `g` as `T`'s limb 3 beside `q`, read by a claim of
  its own). It costs 39,568 gas, 3,048 more than merging `g` into `q`.
- **Merging with `h` committed first** (`W`, `H`, `μ`, `Q* = q + μ g`). This is the textbook order, sound for any
  circuit, but it takes three commitments: 44,688 gas. The pole lemma lets `h` share the quotient's table.
- **One claim on `T` for two independent identities.** This needs two free coordinates, one weighing `h` against
  `q` and one, random, weighing `g` against the copy identity. With the limbs' two bits and the digit that is five
  high bits: `2^29` words, past WHIR's `2^28`.
- **Keeping the `γ`-weighted public sum.** The public weight is an indicator of 2,048 cells among `n`, so its degree
  is about `n`. Then `q` has degree about `3n + 9,216` (four digits), and `q` and `h` cannot share `2^28` words.
  Pinning 1,024 bit cells instead costs the verifier 1,024 inverses. Packing the bits into words costs 504 rows of
  4.2 M.
- **Dropping the sum claim** (3,048 gas). `Σ_cells h = 0` is `h`'s coefficient `n − 1` being zero, and a tensor
  layout cannot leave out one coefficient. Committing `x h` instead, so that the identity forces `(xh)(0) = 0` and
  the degree bound gives the zero sum, fails on the blinding's digit: the word at `X_n` moves the sum by
  `c_0 · r(0)` and is free.
- **A succinct wiring** (claim and `next`: 4,584 gas). Keccak's wiring (θ's columns, ρ, π, χ's `x+1, x+2 mod 5`) has
  no structure on the additive domain that would let the verifier evaluate `σ(t)` cheaply. It would need the circuit
  laid out on the domain's algebra, and was not attempted.
- **A row-level (column) layout**, for a gate quotient of degree `n/4`. It needs four wiring evaluations (three more
  revealed values) and a quotient per column, which saves nothing net.
- **Dropping the selector** (4 B, 256 gas). This is possible, dispatching on calldata length, but it changes the
  contract's ABI for 0.7%, and was left out.

## What the Lean needs

`formal/` still states and proves the six-claim protocol. Porting it means changing:
- **`formal/Statement/PcsQuotient`**:
  - `Circuit`, `Relation`: the public words packed by Horner rows, the anchors and the constant `3`, and the free
    cells of the three random-row shapes;
  - `Domain`, `Reduction`, `Verifier`: the transcript (`μ` for `γ`, no part values), `T`'s layout and the two
    claims' points and values, the pins' interpolation and `Z_P`, the batched inversion's new denominators;
  - `Prover`, `LayoutsProver`: no masks, two blinding coefficients a limb, the one quotient on `2n` points, `T`;
  - `Extractor`, `Replay`, `Transcript`, `Opening`, `PcsOpening`: two commitments and four claims;
  - `Security`, `Zk`: `RevealedUniform` over the new revealed scalars, now provable from two rank conditions.
- **`formal/EndToEnd`**:
  - `Soundness.knowledgeSoundness`, `ksBound`: four openings, two lists. `ComposePcs.prEvent_pinned_le` and
    `trace_core4P` become two-root versions, and `WhirBridge.Pcs.ood_binding_coords` is used at 24 and 28 variables;
  - the new identity steps (above), with the pole lemma and the circuit's condition, which the membership circuit
    meets by computation, as `errors_have_their_own_poles` checks it;
  - `E2ECompleteness.completeness_end`: the honest prover;
  - `ZK`, `PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed`: the simulator's revealed scalars, and the hypotheses.
- **`formal/Implementation`**: `Graph.lean`, regenerated with `UPDATE_LEAN=1 cargo test -p evm graph_lean_is_current`
  (that test is `#[ignore]`d on this branch until the port). Also `Calldata` (301 bytes, two roots, seven scalars,
  statement words of 8 bytes) and `Evm.evm_accepts_iff_verifyWith` against the new graph.
- **`formal/Circuit`**: the dump format (`examples/dump_circuit.rs`: sources `0` zero, `1` one, `2` three, `3` free,
  `4 + r` row) and `CircuitTest/Dump.lean`'s public words.
- **`formal/QuotientSecurity`** (`PublicWeight`, `Pinning`, `Tables`, `Degrees`, `LogDerivative`, `ZeroKnowledge`,
  `Circuit`, `CircuitLayout`), as far as the end theorems still use it.
- **The differential vectors**, all regenerated through their tests: `examples/statement_vectors.rs` (eleven-scalar
  streams, four openings), `tests/whir_bridge_vector.rs` (four openings), and the evm `write_lean_vectors`.

## Files

- `crates/membership/quotient/src/circuit.rs`: anchors, packing rows, `Src::{Three, Free}`, `RandomShape`,
  `Circuit::randomize`, `Circuit::errors_have_their_own_poles`.
- `crates/membership/quotient/src/protocol.rs`: the prover and `reduce`; `table_slot`, `copy_point`, `sum_point`,
  `pins`.
- `crates/membership/quotient/src/hiding.rs`: the two rank conditions and affinity.
- `crates/membership/quotient/src/statement.rs`: `Statement::words`.
- `crates/membership/evm/src/{codegen,quotient,contract,record,adversarial,lean}.rs`: the statement as 8-byte words,
  two roots, seven scalars, four claims; the pinned bytecode and proof digests updated.
