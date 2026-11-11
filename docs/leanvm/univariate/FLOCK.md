<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# Flock on the Keccak-f block

Flock proves that `C1`'s `q_flock` holds a valid witness of the Keccak-f[1600] block of `flock::keccak`
(`crates/vendor/flock-42422001/src/keccak.rs`) at every `SHA3` row: one permutation a block of `2^17` bits, every
round's state materialised, `C = I`. `q_flock` packs 64 bits a `K`-word, so a block is `2^11` words and the zerocheck
runs over `log_n = 17 + h_SHA3` variables (32 at 128 signatures). The verifier is
`leanvm_statement::flock_min::verify_walked::<_, keccak_flock::Keccak>` and `ring_end`, with the block's structured lincheck
terminal (`crates/leanvm/statement/src/keccak_flock.rs`); the prover is `leanvm_univariate::prover::flock::prove` on
leanVM `42422001`'s Flock prover (`crates/vendor/flock-42422001`) with the skip module `flock::zerocheck::skip`
([`PROVER.md`](PROVER.md), "The skip kernels"). [`SPEC.md`](SPEC.md) §7 places Flock in π1.

## The block

**Why not leanVM's block.** leanVM `9d50c92a3`'s Flock block packs three permutations into `2^17` slots and commits
only the χ products. Its matrices are dense in the θ cascade, so its lincheck terminal is a walk of the whole circuit
(leanVM's `bilinear_walk`): about 1.3M additions a permutation, unaffordable in a contract and about 10M of π2's
positions. This block materialises every round, so the terminal factors (below).

**Rows.** Flock proves `A z ∘ B z = z` (`C = I`) per block; every slot of `z` is the output of one row (the constant
wire, a free input, a lin-id `(form)·1`, or a product). In round `j` (24 rounds), `b = πρθ(A_{j-1})` is linear (each
bit 11 bits of `A_{j-1}`):

- product rows `t_j[X,Y,Z] = (1 + b[X+1]) · b[X+2]`;
- lin-id rows `A_j = (b[X] + t_j + RC_j)·1`. With `C = I`, `A_j` must be its own slot; otherwise the cascade makes
  `A_j`'s forms dense and the terminal unaffordable.

**Layout** (64-bit words `w < 2048`; bit `z` of a lane is bit `z` of its word, the packing position; lanes `x + 5y`):

| words | content | rows |
|---|---|---|
| `4q + 0`, `q < 25` | `A_23[q]` (X = output lane `q`) | lin-id: round 23's form `b[X] + t_23 + RC_23` |
| `4q + 1`, all `q < 32` | the K-word `1` (Y): bit 0 = 1, bits 1..63 = 0 | bit 0 constant (`A = B = [1]`); others empty |
| `4q + 2`, `q < 25` | `A_{-1}[q]` (C = input lane `q`) | free input |
| `4q + 3`, `q < 25` | `A_23[q]` (V) | lin-id copy of word `4q` |
| `100, 101, 102, 103` (quad 25) | `(x, 1, 0, x)`, `x` = bit 1 | bit 1 of 100 and 103 constant rows |
| `4q..4q+3`, `26 ≤ q < 32` | `(0, 1, 0, 0)` | |
| `64(j + 2) + l`, `j < 24`, `l < 25` | `t_j[l]` | product `(1 + b[x+1]) · b[x+2]` |
| `64(j + 2) + 32 + l`, `j < 23` | `A_j[l]` | lin-id `b[x] + t_j + RC_j` (`RC` on lane 0 only) |
| words 25..31 of each 32-word run; bits `[104,000, 131,072)` | 0 | empty (the suffix is Flock's `PaddingSpec`, 104,000 useful bits) |

- **The rounds' runs are aligned** (`t_j` at `64(j+2) + l`, `A_j` at `64(j+2) + 32 + l`), not packed, so that the slot
  index factors as `(z: 6, lane: 5, kind: 1, round + 2: 5)` bit fields and the round factor is a shift between
  consecutive values of a 5-bit field; a packed layout (83,393 bits, 64%) would cost the terminal a sum a round (about
  20K more `E` products). The useful prefix is 104,000 bits (79%), which the zerocheck's bit passes and the lincheck's
  fold pay.
- **The constant wire is quad 0's Y bit** (slot 64; the lincheck's `const_pin_col`): every Y word needs its bit 0
  pinned to 1 anyway; the others are constant rows from it. Quad 25's `x` words are both constant rows; empty bits are
  empty rows.
- 80,034 slots are constrained; about 1.39M nonzeros a block. The prover's lincheck fold
  (`LincheckCircuit::fold_alpha_batched`) is a backward walk of the block circuit, once, after the fold over blocks.
- **A denser block** (`k_log = 16`, 40,000 bits) would need `C` a general matrix (`c = A_j + b[X] + RC`, 12 nonzeros),
  so Flock's zerocheck and lincheck would carry `Cz` (a third fold, `v_c` sent). It would put `2^10` words a
  permutation in `q_flock` ([`KECCAK.md`](KECCAK.md), "Capacity"). Not built.

## The ports

The port quads are words `4q .. 4q + 3`: `(X, Y, C, V) = (A_23[q], 1, A_{-1}[q], A_23[q])` for `q < 25` (output lane
`q`, the constant, input lane `q`, output lane `q` again); quad 25 is `(x, 1, 0, x)`; quads 26–31 are `(0, 1, 0, 0)`.
The Keccak VM reads its `SHA3` lanes there: input lane `l` at word `4l + 2`, output lane `l` at word `4l`
(`layout::keccak_slot`). `Q_W`'s copy identities bind the table's 50 lane columns to these words, `in_16` with
`END_BIT` added ([`SPEC.md`](SPEC.md) §6, [`KECCAK.md`](KECCAK.md), "The statement").

## The protocol, as the verifier reads it

The parameters are `flock_min::Variant { skip, fs }`; every Keccak variant takes `skip = 3`.

1. **Zerocheck** of `Az ∘ Bz + Cz = 0` (`C = I`) on the `2^log_n` bits.
   - The eq point: leanVM's seven fixed coordinates, then `log_n - k - 7` coordinates drawn one by one
     (`FsShape::Main`) or as `c, c², c⁴, …` of one challenge (`Rec3`, `Rec4`).
   - A univariate skip over `k = 3` of the 6 packing bits: `P` vanishes on `Λ = φ(0..2^k)`, and its `2^k` values on
     the coset `φ(2^k..2^(k+1))` are sent; the verifier interpolates at its challenge `z`.
   - `log_n - k` rounds of 2 scalars, the eq factor split off.
   - `v_a`, `v_b` (2 scalars). `v_c` is derived.
2. **Lincheck** of `v_a + α v_b + α² v_c + α³` (the constant's pin): 11 rounds of 2 scalars on the block's slot bits
   after its 6 packing bits, then the 64 slices `s_i = ẑ(i, p)`, `i < 64` the packing bits and `p` the words'
   coordinates (the lincheck's challenges reversed, then the instance bits).
3. **The terminal**, checked on the slices: `terminal + r_lc = 0` (`VerifierError::FlockMatrixTerminal`), with
   `terminal = Σ_(row, col) e(row) (Â0 + α B̂0)(row, col) w(col) + α² eq(χ_in, χ_in') Σ_z E_z s_z + α³
   eq(bits(const), χ_in') s_const`, `e = E ⊗ eq(χ_in, ·)`, `E` the skip's Lagrange weights ⊗ `eq(row_low, ·)`, and
   `w = s ⊗ eq(χ_in', ·)`. Two implementations compute it (`flock_min::WalkedCircuit`): the walk (`KeccakWalked`,
   `keccak_flock::row_values`, the trait's default `walked_terminal_with`), about `24 · 25 · 64 · 12` additions, the
   reference; and the structured terminal (`Keccak`, below), which π1 runs.
4. **Ring switch.** Six map challenges `f_0..f_5`, the target `T = Σ_i x^i Φ(s_i)` with the map's stages in tower
   order (`ring_tower::target`; [`SPEC.md`](SPEC.md) §13, entries 2 and 3), and the claim `⟨Φ(eq(p, ·)), q_flock⟩ = T`
   on `C1`. π1-rec4 draws the map after `C2`'s commitment (`flock_min::ring_end_at`, SPEC.md §14.4).
   - Point claims (the main line): the weight is one term of `C1`'s relations (`RING_TWIST`), evaluated at the
     batching sumcheck's point by `ring_tower::weight_at` (in the contract, the hand-scheduled kernel of SPEC.md §13,
     entry 11): the 64 twisted eq products, then the map's stages from the inside.
   - Weighted claims (extension W): 64 Frobenius-twisted eq terms with coefficients `ring_tower::coefficients(map)`.

Flock reads `2^k + 2 (log_n - k) + 2 + 2 · 11 + 64` scalars (`Variant::scalars_with`): 154 at 128 signatures, 150 at
32, 156 at 400. It leaves one claim on `C1`; nothing is committed for it besides `q_flock`, and no matrix is opened.

## The structured terminal

`keccak_flock::structured_terminal`, exactly the walk's value:

1. **Packing weights.** `E = L(z_skip) ⊗ eq(row_low)` is split at bit `p = max(k, 3)` into `E_low ⊗ E_high`
   (`8 + 8` entries at skip 3).
2. **The 40 correlations** `Corr[off] = Σ_z E_z s_(z − off)`, `off` ∈ ρ's rotations ∪ (rotations + 1), the offsets
   θ's `z − 1` adds. They go through 8 partial correlations of length 8, `Q[ol][m] = Σ_zl E_low[zl] s_(8m + zl − ol)`
   (512 products), then `Corr[off] = Σ_zh E_high[zh] Q[off mod 8][zh − off/8]` (320). `Corr[0]` is also the `C = I`
   claim's `Σ e_i s_i`.
3. **Eq factors.** `eq(chi, word) = Lr[lane] · Kd[kind] · Rd[round + 2]`, on both sides (four 5-variable tables). A
   port word `4q + r` is lane field `4(q & 7) + r` in group `q >> 3`.
4. **b's terms.** For each of the 25 lanes `i` of `b`, a row weight `U_i = Kd0 (Lr[x−1] + α Lr[x−2]) + Kd1 Lr[i]`
   covers the t rows' left and right and the A row. It is scaled by the round factor `Σ_(j=1..22) Rd[j+2] Rh[j+1]`
   (rounds 1..22 are identical but for `RC_j`), plus round 23's (its A row is a port X word) and round 0's (its columns
   are the port C words). It is spread over `b[i]`'s two offsets by θ's column sums of `Lh` (or of the C words' column
   weights): 50 coefficients `G[off]`, then `Σ G[off] Corr[off]`.
5. **Corrections**: the constant column, `s_0 eq(word 1, chi')`, times the t rows' `1`, ι's bits (`E` at
   `z = 2^m − 1`), the 34 constant rows and every `B = [1]` (using `Σ_z E_z = 1`), plus the pin's `α³`; the free
   inputs, the V copies and the A rows' `t` term, times `Corr[0]`. Lanes 25..31 and the suffix have no term.

**Operations** (measured: the recorder's `Mul` and `Add` nodes, `structured_terminal_ops`):

| skip | products (by a constant) | sums | **`E` ops** | where they go |
|---|---:|---:|---:|---|
| 3 | 1,510 (8) | 1,509 | **3,019** | partial correlations ≈ 960, correlations 600, eq tables ≈ 250, lane loop ≈ 575 |
| 6 | 3,449 (64) | 3,350 | 6,799 | correlations `40 · 64` ≈ 5.1K, 64 Lagrange weights |

The walk it replaces records 563,462 operations at skip 3 (the recorder shares common subterms).

**Flock alone for 4,096 Keccak-f** (measured, `flock_keccak_verifier_fragment`: recorded, compiled, run on revm;
`log_n = 29`):

| shape | scalars (B) | Keccak-256 | Keccak-f | `FIELD_MUL` (live) | recorded products / sums | execution (of it the terminal) |
|---|---:|---:|---:|---:|---:|---:|
| **skip 3, `Rec3`** | **148 (3,552)** | **47** | **59** | **2,239** | 2,266 / 2,622 | 74,374 (42,145) |
| skip 6, `Rec3` | 198 (4,752) | 44 | 66 | 4,446 | 4,641 / 4,563 | 129,704 (87,926) |

Keccak-f counts each hash's `⌈(32 + absorbed bytes + 1) / 136⌉` blocks.

## Why the slices are sent

**They enter the terminal linearly**, and the contract checks the terminal. The alternative would leave one
combination `Σ_i μ_i ẑ(i, p)` to the opening, which is not an `E`-linear claim. Since `q_flock(u) = Σ_i z(i, u) x^i`:
- `Σ_i μ_i ẑ(i, p) = Σ_u eq(p, u) ℓ(q_flock(u))`, with `ℓ(y) = Σ_i μ_i bit_i(y) = Σ_(k<64) ν_k y^(2^k)`;
- that is `Σ_k ν_k Frob^k(q̂_flock(Frob^(-k) p))`.

A WHIR claim, weighted or not, is an `E`-linear form of the words, `y ↦ ν y` on each: one of the 64 `E`-dimensions of
the `GF(2)`-linear maps `K → E`. So the combination is 64 claims at Frobenius-twisted points whose values are unknown:
ring switching's 64 values cannot be compressed with `E`-linear claims alone (its message is an element of `E ⊗ K`, as
in leanVM's ring switch and Diamond–Posen's). A claim type that ring-switches inside the opening would remove the
slices from calldata; the declared claims have none.

**The ring map's cost** is inherent once the contract computes `T`: a map with fewer Frobenius powers would leave a
nonzero `δ ∈ E ⊗ K` that it sends to zero. The tower order brings it from `64 · 63` squarings to `6 · 64` squarings
and `3 · 63` products.

## The skip's size

A skip over `k` bits sends `2^k` values and leaves `log_n - k` rounds; the row's other `6 - k` packing bits become
ordinary rounds. π1 takes `k = 3`:
- the scalars: `2^k + 2 (log_n - k)` is `2 log_n + 2` at 3, against `2 log_n + 52` at leanVM's 6;
- the structured terminal is cheaper at 3 (3,019 `E` operations against 6,799), its correlations factoring over the
  packing bits above the skip;
- the prover's skip kernels cover `3 ≤ k ≤ 6` (`skip::MIN_SKIP`: a group is a whole byte); below 3 would save at most
  2 scalars.

The verifier's soundness is unchanged by the skip's size: its error is `(2^(k+1) - 1)/|E|`, and the seven fixed
coordinates still see Boolean values (`hfixed`). leanerVM's `Flock.flock` ties the skip to the packing (`s = 6` for
both), so `k < 6` needs that parameter split.

## The messages

- **Every round is minimal.** A round sends 2 scalars: the zerocheck's after its eq factor is split off, the
  lincheck's with `c_1` derived from the claim.
- **One skip value could go.** `deg P ≤ 2^(k+1) - 2` and `P` vanishes on `Λ`, so `2^k - 1` values determine it. One
  scalar; not done.
- **`v_b` cannot go.** `α` must come after both `v_a` and `v_b`. A `v_b` derived after `α` lets the prover fit the
  batched claim (leanerVM's `alphaDraw_noConst_one_le` is the same point for the pin).
- **Within Flock nothing batches.** The zerocheck and the lincheck are sequential: `α` comes after `v_a`, `v_b`, and
  the lincheck's row weights are at the zerocheck's point. Merging the lincheck into the batching sumcheck is circular:
  the lincheck's point is the ring switch's, an input of the batch.

## Soundness notes

- Every Flock challenge is drawn after `C1`'s commitment and before `C2`'s, so its error is multiplied by `C1`'s
  Johnson list `L_1` ([`SPEC.md`](SPEC.md) §9); π1-rec4's ring map, drawn after `C2`, by both lists (SPEC.md §14.5).
- The terms: the skip's `(2^(k+1) - 1)/|E|` (15 at `k = 3`), a degree-3 zerocheck round and a degree-2 lincheck round
  each, the lincheck's batching `α` (degree 3), and the ring map's `6/|E|` in tower order (leanVM's order: `2^31/|E|`
  by Schwartz–Zippel). In all about `2^7/|E|` at these sizes.
- With π1-rec3 and π1-rec4 the zerocheck's sampled coordinates are successive squares of one challenge, so their eq
  polynomial has degree `2^(log_n - k - 7) - 1` in it (`docs/leanvm/rec/SPEC-REC.md` §1.4): 157.9 bits after `L_1` at
  128 signatures (SPEC.md §9), within the Lean bound (`formal/UniKeccakSound`).
- **The terminal must be checked.** leanerVM proves that dropping it loses all security
  (`linEnd_unchecked_no_security`, mumbai `f0393df4`, `ToArkLib/Flock/Security.lean`). Here the contract checks it on
  the sent slices; the slices are then bound to `q_flock` by the ring switch's claim, which the `C1` opening proves.
- **The structured terminal is the walk's value.** `formal/KeccakFlock` proves `structuredTerminal_eq_bilinear` (it
  equals the matrices' bilinear form), and the tests below check the two implementations equal.

## Tests

- `crates/leanvm/statement/tests/keccak_terminal.rs`: the structured terminal equals `walked_terminal_with::<_,
  KeccakWalked>` at random points, challenges and slices at every skip 0..6 (24 trials at skips 3 and 6), and for each
  of the 64 packing positions alone (`s = e_i`, unit and random weight) at skips 3 and 6; its `E` operations; and
  (ignored) the Flock-for-Keccak verifier recorded, compiled and run on revm. The eq points of the `Rec` shapes do not
  enter the terminal's inputs, which are the zerocheck's and lincheck's round challenges.
- `crates/leanvm/univariate/tests/flock_keccak.rs`: the verifier's walk is the prover's; `prover::flock::prove`'s
  stream is accepted by both terminals (which must agree) at skips 3 and 6 and both eq points, with the slices the
  witness's at the verifier's point; a flipped state bit and a changed slice are rejected (128 blocks; 4,096 blocks
  ignored, with a benchmark).
- `crates/vendor/flock-42422001/tests/keccak.rs`: the block against RustCrypto's Keccak-f on random states; the
  witness satisfies every row of every block, its port quads hold what "The ports" says, its lincheck stripes are
  `z`'s transpose; every flipped witness bit breaks a row; the non-empty rows are exactly the layout's slots; the
  backward walk is the forward walk's transpose.
- `crates/leanvm/univariate/tests/flock_skip.rs`: the skip kernels ([`PROVER.md`](PROVER.md), "The skip kernels").
