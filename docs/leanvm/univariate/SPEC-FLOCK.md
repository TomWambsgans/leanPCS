<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# Flock in π1 (the Flock section of `SPEC.md`)

**Scope.** Flock proves that `C1`'s `q_flock` holds a valid witness of the Keccak-f[1600] block of
`lv42_flock::keccak` (`docs/leanvm/flock/KECCAK.md`) at every `SHA3` row: one permutation a block of `2^17` bits,
every round's state materialised, `C = I`. `q_flock` packs 64 bits a `K`-word, so a block is `2^11` words and the
zerocheck runs over `log_n = 17 + h_SHA3` variables (32 at the reference workload, 128 signatures). The verifier is
`leanvm_statement::flock_min::verify_walked_with::<_, keccak_flock::Keccak>`; its prover is
`leanvm_univariate::prover::flock::prove` on leanVM 42422001's Flock prover (`crates/vendor/leanvm-42422001/flock`)
with the skip module `lv42_flock::zerocheck::skip`. This document states what π1 runs, why, and the soundness notes
that apply.

## The protocol, as the verifier reads it

The parameters are `flock_min::Variant { skip, fs }`: `KECCAK_MAIN` and `KECCAK_REC3` both take `skip = 3`.

1. **Zerocheck** of `Az ∘ Bz + Cz = 0` (`C = I`) on the `2^log_n` bits.
   - The eq point: leanVM's seven fixed coordinates, then `log_n - k - 7` coordinates drawn one by one
     (`FsShape::Main`) or as `c, c², c⁴, …` of one challenge (`FsShape::Rec3`).
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
   `w = s ⊗ eq(χ_in', ·)`. Two implementations compute it (`flock_min::WalkedCircuit`):
   - the walk (`KeccakWalked`, `keccak_flock::row_values`): `A0 w` and `B0 w` by one forward walk of the block, about
     `24 · 25 · 64 · 12` additions; the reference;
   - the structured terminal (`Keccak`, `keccak_flock::structured_terminal`), which π1 runs: eq factors over a word's
     `(lane, kind, round)` fields, ρ and θ as cyclic shifts through 40 correlations `Σ_z E_z s_(z - off)`, one shared
     factor for rounds 1..22, and corrections for the constant column, the free inputs and the copies. 3,019 `E`
     operations at a skip of 3, 6,799 at 6 (`docs/leanvm/flock/KECCAK.md`, M3 notes).
4. **Ring switch.** Six map challenges `f_0..f_5`, the target `T = Σ_i x^i Φ(s_i)` with the map's stages in tower
   order (`ring_tower::target`; `SPEC.md` §13, entries 2 and 3), and the claim `⟨Φ(eq(p, ·)), q_flock⟩ = T` on `C1`.
   - Point claims (the main line): the weight is one term of `C1`'s relations (`RING_TWIST`), evaluated at the
     batching sumcheck's point by `ring_tower::weight_at` (in the contract, the hand-scheduled kernel of
     `SPEC.md` §13, entry 11): the 64 twisted eq products, then the map's stages from the inside.
   - Weighted claims (extension W): 64 Frobenius-twisted eq terms with coefficients `ring_tower::coefficients(map)`.

Flock reads `2^k + 2 (log_n - k) + 2 + 2 · 11 + 64` scalars (`Variant::scalars_with`): 154 at 128 signatures, 150 at
32, 156 at 400. It leaves one claim on `C1`; nothing is committed for it besides `q_flock`, and no matrix is opened.

## Why the slices are sent

**They enter the terminal linearly**, and the terminal is checked by the contract. The alternative would leave one
combination `Σ_i μ_i ẑ(i, p)` of them to the opening. That combination is not an `E`-linear claim. Since
`q_flock(u) = Σ_i z(i, u) x^i`:
- `Σ_i μ_i ẑ(i, p) = Σ_u eq(p, u) ℓ(q_flock(u))`, with `ℓ(y) = Σ_i μ_i bit_i(y) = Σ_(k<64) ν_k y^(2^k)`;
- that is `Σ_k ν_k Frob^k(q̂_flock(Frob^(-k) p))`.

A WHIR claim, weighted or not, is an `E`-linear form of the words, `y ↦ ν y` on each: one of the 64 `E`-dimensions
of the `GF(2)`-linear maps `K → E`. So the combination is 64 claims at Frobenius-twisted points whose values are
unknown: ring switching's 64 values cannot be compressed with `E`-linear claims alone (its message is an element of
`E ⊗ K`, as in leanVM's ring switch and Diamond–Posen's). A `PCS_OPEN` claim type that ring-switches inside the
opening would remove the slices from calldata; `PCS_OPEN` has none, so the 64 values stay.

**The ring map's cost** is inherent once the contract computes `T`: a map with fewer Frobenius powers would leave a
nonzero `δ ∈ E ⊗ K` that it sends to zero. The tower order brings it from `64 · 63` squarings to `6 · 64` squarings
and `3 · 63` products.

## The skip's size

A skip over `k` bits sends `2^k` values and leaves `log_n - k` rounds; the row's other `6 - k` packing bits become
ordinary rounds. π1 takes `k = 3`:
- the scalars: `2^k + 2 (log_n - k)` is `2 log_n + 2` at 3, against `2 log_n + 52` at leanVM's 6;
- the structured terminal is cheaper at 3 (3,019 `E` operations against 6,799), its correlations factoring over
  the packing bits above the skip;
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
  the lincheck's row weights are at the zerocheck's point. Merging the lincheck into the batching sumcheck is
  circular: the lincheck's point is the ring switch's, an input of the batch.

## Soundness notes

- Every Flock challenge is drawn after `C1`'s root and before `C2`'s, so its error is multiplied by `C1`'s Johnson
  list `L_1` (`SPEC.md` §9).
- The terms: the skip's `(2^(k+1) - 1)/|E|` (15 at `k = 3`), a degree-3 zerocheck round and a degree-2 lincheck round
  each, the lincheck's batching `α` (degree 3), and the ring map's `6/|E|` in tower order (leanVM's order:
  `2^31/|E|` by Schwartz–Zippel). In all about `2^7/|E|` at these sizes.
- With π1-rec3 the zerocheck's sampled coordinates are successive squares of one challenge, so their eq polynomial has
  degree about `2^(log_n - k - 7)` in it (`docs/leanvm/rec/SPEC-REC.md` §1.4; analysis there, not proven).
- **The terminal must be checked.** leanerVM proves that dropping it loses all security
  (`linEnd_unchecked_no_security`, mumbai `f0393df4`, `ToArkLib/Flock/Security.lean`). Here the contract checks it on
  the sent slices; the slices are then bound to `q_flock` by the ring switch's claim, which the `C1` opening proves.
- **The structured terminal is the walk's value.** `formal/KeccakFlock` proves `structuredTerminal_eq_bilinear` (it
  equals the matrices' bilinear form), and `crates/leanvm/statement/tests/keccak_terminal.rs` checks the two
  implementations equal at every skip `0..=6`.

## Tests

- `crates/leanvm/univariate/tests/flock_keccak.rs`: the verifier's walk is the prover's; `prover::flock::prove`'s
  stream is accepted by both terminals at skips 3 and 6 and both eq points, with the slices the witness's at the
  verifier's point; a flipped state bit and a changed slice are rejected (128 blocks; 4,096 blocks ignored, with a
  benchmark).
- `crates/leanvm/statement/tests/keccak_terminal.rs`: the structured terminal against the walk, its `E` operations,
  and (ignored) the Flock-for-Keccak verifier recorded, compiled and run on revm.
- `crates/leanvm/univariate/tests/flock_skip.rs`: the skip kernels (`PROVER.md`, "The skip kernels").
