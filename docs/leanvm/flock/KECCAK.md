<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# The Keccak-f[1600] Flock block

The Flock block of `src/keccak.rs` (one Keccak-f permutation per `2^17` slots, every round's state materialised) and
its verifier's structured lincheck terminal (`crates/leanvm/statement/src/keccak_flock.rs`). The Keccak VM of
`docs/leanvm/univariate/KECCAK.md` proves its `SHA3` table with them.

They were designed and built for an SLH-DSA proof-of-concept that has since been removed from the repository (its
milestones M1 and M3, `crates/slh_dsa/SPEC-FAST.md` in the history). This file keeps that spec's sections on the block,
unchanged but for this header. In them:
- "the glue" and "π1" are that proof-of-concept's;
- the port quads `(X, Y, C, V)` are the block's input and output port words, which the Keccak VM reads as its `SHA3`
  lanes (input lane `l` at word `4l + 2`, output lane `l` at word `4l`).

### 4.2 Keccak-f as a Flock block

Flock (`crates/vendor/leanvm-42422001/flock`) proves `A z ∘ B z = z` (`C = I`, baked into zerocheck and lincheck) per block, the blocks
batched; every z slot is the output of one row (constant wire, free input, lin-id `(form)·1`, product).

- **Rows of round j** (24 rounds): `b = πρθ(A_{j-1})` is linear (each bit 11 bits of `A_{j-1}`).
  - Product rows: `t_j[X,Y,Z] = (1 + b[X+1]) · b[X+2]`.
  - Lin-id rows: `A_j = (b[X] + t_j + RC_j)·1`.
  - With `C = I`, `A_j` must be its own slot. Otherwise the cascade makes `A_j`'s forms dense and the verifier's
    terminal unaffordable (§4.2, terminal).
  - So a round is 3,200 slots.
- **Block layout** (`k_log = 17`): the port region (32 quads × 4 words = 8,192 bits, §4.5), then `t_0..t_23` and
  `A_0..A_22` (75,200 bits), the constant wire; `A_{-1}` and `A_23` sit in the port quads. 83,393 of 131,072 bits
  (64%); padding slots are forced to 0 by empty rows (`PaddingSpec`). 4,096 blocks (3,959 used, the rest
  Keccak-f(0)): **log_n = 29, 2^23 K-words**.
- **Why not `k_log = 16`**: 40,000 bits would fit if `C` were a general matrix (`c = A_j + b[X] + RC` with 12
  nonzeros). That needs lv42_flock's zerocheck and lincheck to carry `Cz` (a third fold, `v_c` sent): a stretch
  optimisation (half the bits, −0.1 s), not on the critical path.
- **The prover's lincheck fold** (`LincheckCircuit::fold_alpha_batched`): a backward walk of the block circuit,
  ≈ 2.5M nonzeros, once (the z fold over blocks comes first). ≈ 20 ms [E].
- **The verifier's terminal**: `Σ_rows eq(r, row) (A + αB)(row, (ρ, i))` for the 64 packing positions `i`. A walk
  of the circuit would cost ≈ 1.3M additions, about 10M of π2's positions, so do not walk. Use the structure:
  - rows and columns factor into (round, kind, lane, z); the 64 packing bits are Keccak's `z`;
  - the round factor is a shift MLE (`O(5)`);
  - the lane factor is `eq` over 25 lanes;
  - each ρ rotation is a cyclic shift of the 64-entry `eq(r_z, ·)` table;
  - group the (lane, lane′) pairs by rotation offset (≤ 50 distinct, θ's `z − 1` included), then do 64 multiply-adds
    per offset;
  - rounds 0 and 23 (the port quads) and the ι constants are corrections.
  
  Estimate: ≈ 10K `E` ops [E]; built (M3): 3,019 [M], equal to the walk (M3 notes, after §4.5).


### 4.5 The link

**Port quad** `q` of block `b`: W row `R0 + 32b + q` with cells

`(X, Y, C, V) = (O_q, 1, I_q, O_q)`,

with `O_q` output lane `q` (X wired to its own V: free), and `I_q` input lane `q` (C wired to its source). The gate
holds (`V = X + C + C = X`).

`q_flock`'s block `b` holds the same four words at words `4q..4q+3`. Flock places `A_23[q]` twice (one lin-id
copy) and a `1` word, and `A_{-1}[q]` at `4q + 2`. Quad 25 is `(x, 1, 0, x)`; quads 26–31 are `(0, 1, 0, 0)`.

So W's cells on the aligned coset `o + V_19` (2^17 rows × 4) equal `q_flock`'s port region
(`(word < 128, block)`, 19 variables), word for word.

**Identity**: `W_R(z) + ℓ_q(z) = Q_link(z) · Z_19(z)`, where:
- `W_R` is the restriction of W's polynomial to the coset. It is one claim at a mixed point (`SPEC.md` §2, in
  `crates/membership/quotient`'s novel basis).
- `ℓ_q(z) = q̂_port(y_0(z), …, y_18(z))`, with `y_l` the coordinate functionals (`domain::coordinate_functionals`).
  It is one claim on `q_flock`'s values, for 19² products.
- `deg ℓ_q ≤ 19 · 2^18`, so `Q_link` has ≈ 4.46M words.
- No challenge precedes it, so `Q_link` goes in C1.
- It is checked at the quotient's `t` with 2 sent values.

Prover: `ℓ_q` on 10 cosets of 2^19 by shifted-cube folds (`O(19 · 2^19)` each, leanvm_univariate's `copy_j`
code) and one inverse NTT, ≈ 0.1 s [E].


### M1 notes (as built: `lv42_flock::keccak`)

The port quads are as above; two things inside the block differ from §4.2, neither visible to the glue.

**Block layout** (64-bit words `w < 2048`; bit `z` of a lane is bit `z` of its word, the packing position; lanes
`x + 5y`):

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

**Changes from §4.2, and why**:
1. *The rounds' runs are aligned* (`t_j` at `64(j+2) + l`, `A_j` at `64(j+2) + 32 + l`) instead of packed
   (`t_0..t_23, A_0..A_22` contiguous, 83,393 bits). §4.2's structured terminal needs the slot index to factor as
   `(z: 6, lane: 5, kind: 1, round + 2: 5)` bit fields, so that the round factor is a shift between consecutive
   values of a 5-bit field; a packed layout (`128 + 25(2j + kind) + l`) does not factor and would cost the terminal
   a sum per round (≈ 20K more `E` products). Cost: the useful prefix is 104,000 bits (79%) instead of 83,393
   (64%), which the zerocheck's bit passes and the lincheck's fold pay (measured below).
2. *The constant wire is quad 0's Y bit* (slot 64) instead of a slot after `A_22`: every Y word needs its bit 0
   pinned to 1 anyway; quad 0's is the wire (lincheck's `const_pin_col`), the others are constant rows from it.
3. Quad 25's `x` words are both constant rows (not a copy of each other); empty bits are empty rows.

80,034 slots are constrained; ≈ 1.39M nonzeros a block.

**Measured** [M] (h1, `RUSTFLAGS="-C target-cpu=native"`, `FsShape::Rec`, walked terminal; `cargo test --release -p
leanvm_univariate --test flock_keccak -- --ignored --nocapture`): 4,096 blocks (3,959 random states, Keccak-f(0)
padding), `log_n = 29`, median of 3:

| skip | witness | prove | runs | stream |
|---|---:|---:|---|---:|
| 3 | 0.023 s | **0.189 s** | 0.181 / 0.189 / 0.192 | 3,552 B |
| 6 | 0.023 s | **0.132 s** | 0.132 / 0.120 / 0.148 | 4,752 B |

At skip 3 the zerocheck is ≈ 0.17 s of it (round 1 0.021, bit passes 0.073 / 0.039 / 0.016, storing 0.013, table
rounds 0.012), the lincheck (walk, fold, 11 rounds) ≈ 0.015 s. Within §4.9's 0.18 s and M1's 0.3 s target. The verifier's reference walk (generic `Scalar`) is
`leanvm_statement::keccak_flock` (`flock_min::verify_walked_with::<_, Keccak>`); the prover's entry is
`leanvm_univariate::prover::flock::prove_keccak` (walked terminal only).

**For M3 (the structured terminal)**: the terminal is `Σ_rows e(row) (Â0 + α B̂0)(row, col) w(col)` with
`e = L(z_skip) ⊗ eq(row_low) ⊗ eq(chi_in)` (6 + 11 bits) and `w = s ⊗ eq(chi_in')`, plus `α² eq(chi_in, chi_in')
Σ e_i s_i` and the pin `α³ eq(word(64) = 1, chi_in') s_0`. Every round `j` reads only `A_{j-1}` (round 0 the C
words `4q + 2`) and writes `t_j` and `A_j` (round 23 the X words `4q`); rounds 1..22 are identical but for `RC_j`.
Corrections beyond the shifted rounds: round 0's reads (port C words), round 23's writes (X words) and the V copies
(`A = [word 4q, same z]`), the constant rows (34 slots: Y bits, quad 25's two `x` bits), the free inputs
(`A = [slot]`), the constant's column (every lin-id and free row's `B`, every product row's `A` has it, ι's bits),
and the empty lanes 25..31 of each run. The forward walk to check against is `keccak_flock::row_values`.

### M3 notes (as built: `leanvm_statement::keccak_flock::structured_terminal`)

`Keccak`'s `WalkedCircuit::terminal` is now the structured one (`verify_walked_with::<_, Keccak>`); `KeccakWalked` keeps
M1's walk as the reference (the trait's default terminal, `walked_terminal_with`). The algorithm:

1. **Packing weights.** `E = L(z_skip) ⊗ eq(row_low)` is split at bit `p = max(k, 3)` into `E_low ⊗ E_high`
   (`8 + 8` entries at skip 3).
2. **The 40 correlations** `Corr[off] = Σ_z E_z s_(z − off)`, `off` ∈ ρ's rotations ∪ (rotations + 1), the offsets
   θ's `z − 1` adds. They go through 8 partial correlations of length 8, `Q[ol][m] = Σ_zl E_low[zl] s_(8m + zl − ol)`
   (512 products), then `Corr[off] = Σ_zh E_high[zh] Q[off mod 8][zh − off/8]` (320). `Corr[0]` is also the
   `C = I` claim's `Σ e_i s_i`.
3. **Eq factors.** `eq(chi, word) = Lr[lane] · Kd[kind] · Rd[round + 2]`, on both sides (four 5-variable tables).
   A port word `4q + r` is lane field `4(q & 7) + r` in group `q >> 3`.
4. **b's terms.** For each of the 25 lanes `i` of `b`, a row weight `U_i = Kd0 (Lr[x−1] + α Lr[x−2]) + Kd1 Lr[i]`
   covers the t rows' left and right and the A row. It is scaled by the round factor
   `Σ_(j=1..22) Rd[j+2] Rh[j+1]` (rounds 1..22), plus round 23's (its A row is a port X word) and round 0's (its
   columns are the port C words). It is spread over `b[i]`'s two offsets by θ's column sums of `Lh` (or of the C
   words' column weights): 50 coefficients `G[off]`, then `Σ G[off] Corr[off]`.
5. **Corrections**:
   - the constant column, `s_0 eq(word 1, chi')`, times the t rows' `1`, ι's bits (`E` at `z = 2^m − 1`), the 34
     constant rows and every `B = [1]` (using `Σ_z E_z = 1`), plus the pin's `α³`;
   - the free inputs, the V copies and the A rows' `t` term, times `Corr[0]`.

   Lanes 25..31 and the suffix have no term.

**Tests** [M]: `crates/leanvm/statement/tests/keccak_terminal.rs` (run on h1 and on a Mac).
- It is equal to `walked_terminal_with::<_, KeccakWalked>` at random points, challenges and slices at every skip
  0..6, with 24 trials at skips 3 and 6.
- It is equal for each of the 64 packing positions alone (`s = e_i`, unit and random weight) at skips 3 and 6.
- The eq points of `FsShape::Rec`/`Rec3` do not enter the terminal's inputs, which are the zerocheck's and lincheck's
  round challenges.
- The end-to-end test (`leanvm_univariate/tests/flock_keccak.rs`) now checks every verdict with both terminals and
  asserts they agree. On a Mac (M-series):
  - at 128 blocks, skips 3 and 6, `Rec` and `Main`, the proofs are accepted and a changed slice and a flipped state
    bit are rejected;
  - at 4,096 blocks (ignored test), the proofs at skips 3 and 6 are accepted and a flipped output bit is rejected;
    prove 0.181 s at skip 3 and 0.125 s at skip 6 (not comparable to h1's).

**Op count** [M] (the recorder's `Mul` and `Add` nodes, `structured_terminal_ops`):

| skip | products (by a constant) | sums | **`E` ops** | where they go |
|---|---:|---:|---:|---|
| 3 | 1,510 (8) | 1,509 | **3,019** | partial correlations ≈ 960, correlations 600, eq tables ≈ 250, lane loop ≈ 575 |
| 6 | 3,449 (64) | 3,350 | 6,799 | correlations `40 · 64` ≈ 5.1K, 64 Lagrange weights |

Target ≤ 15K. The walk it replaces records 563,462 ops at skip 3 (255,704 products, 307,758 sums; the recorder
shares common subterms).

**Flock for 4,096 Keccak-f, structured terminal** [M] (`flock_keccak_verifier_fragment`: recorded, compiled, run on
revm; log_n 29):

| shape | scalars (B) | Keccak-256 | Keccak-f | `FIELD_MUL` (live) | recorded products / sums | execution (of it the terminal) |
|---|---:|---:|---:|---:|---:|---:|
| **skip 3, `Rec3`** (= `Rec` for Flock) | **148 (3,552)** | **47** | **59** | **2,239** | 2,266 / 2,622 | 74,374 (42,145) |
| skip 6, `Rec3` | 198 (4,752) | 44 | 66 | 4,446 | 4,641 / 4,563 | 129,704 (87,926) |

Keccak-f counts each hash's `⌈(32 + absorbed bytes + 1) / 136⌉` blocks.

**π2 positions.** The proof-of-concept's estimate (§4.7 there) is superseded by the measurement on the Keccak VM's
whole π1 (`docs/leanvm/rec/SPEC-REC.md` §10.3): π1-rec3 at 128 signatures records 116 Keccak-f and 8,476 `E`
products / 6,633 linear operations, and its π2 circuit (D16v) uses 15,668,416 positions, 93.4% of `2^24`.

