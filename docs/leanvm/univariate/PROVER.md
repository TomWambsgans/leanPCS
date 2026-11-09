<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# The prover of the univariate PIOP

`src/prover/` proves `SPEC.md`'s statement on executions of the Keccak VM (leanVM `9d50c92a3`, `KECCAK.md`), from
the trace `src/prover/dump_keccak/` makes leanVM write. It writes the stream `verifier::reduce` reads (through the
contract's Keccak-256 chain) and one WHIR opening per commitment (`C1`, `C2`, the setup `F`). It proves both variants,
`KECCAK_MAIN` and `KECCAK_REC3`, with point claims; weighted claims (extension W) have no opening prover.

## Status

On real executions (32, 128 and 400 signatures) and both variants: the Rust verifier accepts; the three WHIR
openings verify; the straight contract and the deployable one (`crates/evm_link`, parts of at most 24,576 bytes)
accept the real calldata, word for word with the Rust verifier, with `PCS_OPEN` attesting exactly the claims the
openings prove; both reject a flipped byte and any call left unattested; five stream mutations are rejected by the
Rust verifier. The real proofs' gas is in `KECCAK.md` ("The real proofs' gas").

**Rust→EVM test vectors.** `tests/vectors/` holds three real proofs: `keccak.txt` (32 signatures, `KECCAK_MAIN`),
`keccak128_rec3.txt` (128 signatures, `KECCAK_REC3`: the reference workload, the recursion's inner proof) and
`keccak_rec3.txt` (400 signatures, `KECCAK_REC3`). Each holds the calldata, the `PCS_OPEN` inputs the contract calls
with, the committed roots, the verdict and the gas, straight and deployed. `tests/evm_vectors.rs` replays them with no
prover and no trace, the contract binding the vector's own `F` (its third call's root): both builds accept at the
recorded gas, call `PCS_OPEN` with exactly the recorded inputs, and revert on 13 mutations each (a row count, `C1`'s
root, two scalars, a batching round, the last byte or the public input flipped; each call left unattested; each
attested value flipped). `tests/lean_keccak_vectors.rs` turns the real proofs and solved sample streams into the Lean
transcription's differential vectors.

## How it runs

1. **Traces** (`src/prover/dump_keccak/`). `sh src/prover/dump_keccak/apply.sh <tree>` patches a leanVM `9d50c92a3`
   tree (`git -C <leanVM checkout> archive 9d50c92a3 | tar -x -C <tree>`). A proof leanVM starts with
   `LEANVM_TRACE_DUMP=<dir>` then runs the program again **without its fill blocks**, writes the run to `<dir>` and
   exits:

   ```sh
   cd <tree> && LEANVM_TRACE_DUMP=<dir>/xmss128 cargo leanvm aggregate --xmss 128 --log-inv-rate 1
   ```

   - **The fill.** leanVM `9d50c92a3` brings every table to a power of two by executing fill cycles after the halt,
     `SHA3` to a quarter rule with a zero-state dummy on every fourth row (its three-steps-a-block Flock layout). The
     univariate PIOP has its own padding rows, so the dump is the program's own run: `program.filler` emptied, the
     interpreter halts at the sentinel. The tables hold exactly `Stats::base_counts` rows, and the memory's and the
     bytecode's final counts are those of the rows dumped.
   - The interpreter still reorders the `SHA3` rows when their count is a multiple of four
     (`hash_flock::interleave_dummies`): a permutation of executed rows, which the bus does not see.
   - The files: `meta.txt` (the sizes, the rows, the public cells, the columns), `columns.bin` (the memory, the
     bytecode's final counts, each table's columns over its executed rows), `bytecode.bin` (the stacked bytecode).
     `q_flock` is not dumped.
   - The dump takes 0.1–0.3 s. The traces are deterministic.
2. **Loading and placement** (`Trace::load`, `Trace::place`; `SPEC.md` §13, F1 and F1b). `Trace::load` pads each
   table to `2^ceil(log2 rows)` with its padding row: zero but for a `SHA3` row's output lanes, which hold
   `step(0) = Keccak-f(END_BIT·e₁₆)`, so that `Q_W`'s copy identities hold on padding rows too. `Trace::place` moves
   each table's active rows to the fixed cosets of its count's bits (`domain::active_positions`) and sets the padding
   rows' counters to 1. Only the moved rows are copied.
3. **The Keccak-f blocks** (`Trace::keccak_flock`): one block a `SHA3` row of the placed table, padding rows
   included, block `i` at row `i`. Its input port is the row's input lanes with `END_BIT` added to lane 16, so its
   output port is the row's output lanes (`step(in) = Keccak-f(in ⊕ END_BIT·e₁₆)`). The witness (`z`, `A z`, `B z`, the
   lincheck's stripes) is `flock::keccak::generate_witness_with_ab_packed_and_lincheck`'s; `C1` commits `z` from
   it (`Stack::put_k_words`), and the trace keeps no copy.
4. **Proving and checking.** Build with `RUSTFLAGS="-C target-cpu=native"`, as leanVM's own `.cargo/config.toml`
   does (without it the field is about 25× slower), and set `LEANVM_TRACE=<dir of a dump_keccak trace>`:

   ```sh
   cargo test --release -p leanvm_univariate --test prove_real -- --ignored --nocapture --test-threads 1
   ```

   - `proves_and_verifies_keccak` (`KECCAK_MAIN`) and `proves_and_verifies_keccak_rec3` (`KECCAK_REC3`): the proof,
     the quotients' degrees, every combined claim against its stack, the Rust verifier, the WHIR openings, the
     straight and deployable contracts on the real calldata (word-for-word parity with the Rust verifier), each call's
     input against the claim its opening proves, and the mutations. With `WRITE_VECTORS=<dir>` each writes its test
     vector (`VECTOR_FILE` names it).
   - `identities_hold_on_the_domain` (the bus balance, the copies on every row, the counters), `setup_roots` (the
     trace's `F` root), `unused_words_are_not_relied_on` (below).
   - `keccak_prover_benchmark`: warm passes with a cooldown between them, as leanVM's benchmark runs (`PI1_REPEAT`,
     default 3; `PI1_COOLDOWN`, default 2 s; `PI1_VARIANT=rec3` for `KECCAK_REC3`), the median of each phase; each
     pass's proof is checked to be the first's.

   Without a trace: `flock_skip` and `flock_keccak` (the skip kernels, Flock on the Keccak-f block), `evm_vectors`
   (the committed vectors). `prove_quotients` (the quotients alone at fixed challenges, `sha3_leaf`), `prove_kernels`
   (the transforms) and `prove_openings` (one opening alone) are ignored timing tests.

## The prover, phase by phase (`src/prover/prove.rs`)

1. **`C1` and the setup** (`columns.rs`, `stack.rs`, `setup.rs`): every column through the inverse additive NTT to
   its novel coefficients (`crates/membership/quotient/src/ntt.rs`, vectorized), then by subset sums to basis `B`
   straight into the stack; the counter inverses `z_T = 1/Π c_j` on every row; `q_flock` as values, from the Flock
   witness. The setup `F`: the bytecode's 16 tuple slots interleaved and the memory's addresses. Then leanVM's WHIR
   commits of both. The prover checks that the contract's `F` root is the one it commits (`setup::f_root`).
   `PI1_LOW_MEMORY=1` commits `C1` without keeping its codeword (twice its stack), so that its opening re-encodes the
   rows its queries open: the same proof, a lower peak.
2. **The seed** is `keccak(name ‖ contract_iv(shape, variant, program IV, roots) ‖ public input)` (`SPEC.md` §13,
   F2). The stream starts with the six row counts, then `C1`'s root as its two WHIR scalars (`prove::halves`).
3. **The challenges** `α, β, γ`; with π1-rec3 `α = (c, c², c⁴, c⁸)`, squared in `E` as the verifier squares it.
4. **Flock** (`flock.rs`, behind one call): the zerocheck at a skip of 3 (`flock::zerocheck::skip`, below; with
   π1-rec3 its sampled eq coordinates are successive squares, `EqPoint::Squares`), the lincheck at the row weights the
   skip leaves, the 64 slices, then the ring map's six challenges. The slices' point is checked against the one the
   verifier derives. Flock's witness is freed after it.
5. **The heap** (`bus.rs`, `heap_of`): a leaf per row, the ratio on active rows (`domain::is_active`) and 1 on
   padding rows, the fingerprints eight rows at a time (`prints.rs`, padding runs skipped); every block's leaves in one
   dispatch, a task `2^10` rows of one block (its fingerprints, one inversion by Montgomery's trick, the ratios),
   written straight to the heap's positions; the heap's novel coefficients limb by limb, and each block's (`R`) the
   blocks of one height together. The heap's root is checked against the state boundary's ratio.
6. **The quotients** (`quotients.rs`, on `crates/membership/quotient/src/ntt.rs`). Each leaf quotient is sized as the
   verifier sizes it, for its height's fewest rows (`Shape::least_rows`).
   - Each numerator is evaluated on the first `T` points of an extension coset `D_M = ω_{2^M} + V_M` (outside the
     domain), `T = Σ 2^{e_j}` the verifier's count rounded up to `2^{r-2}`, in binary: blocks of points
     `ω_{s_j} + V_{e_j}`. `SHA3`'s leaf (degree about `54.5 n`) takes 54.5 pieces of `n` points, not a power-of-two
     coset's 64; XOR's, MUL's, DEREF's and JUMP's 8.5. Over the vanishing polynomial, the values give the novel
     coefficients (`ntt::interpolate_prefix`): with `R_j = Q_j + w_{e_j} R_{j+1}` (`R_0 = Q`), `w_{e_j}` is a constant
     `λ_j` on block `j`, whose inverse NTT is `U_j = Q_j + λ_j R_{j+1}`, and `λ_j + 1` on the later blocks, where
     `R_{j+1} = R_j + U_j`; then `Q_j = U_j + λ_j R_{j+1}` from the last block back.
   - The tables' six leaves and `Q_W`'s six tables' parts are made together, every stage of all twelve in the same
     dispatches (`quotients::prefix_quotients`): their columns (and `R`'s three limbs) packed eight at a time; their
     pieces (at most `2^15` points) in one dispatch, a task one batch (or, with five columns or fewer, one column) on
     one piece by one worker, or a piece's values at 512 of its points (eight at a time, `prints.rs`, `Z_act` and
     `Z_pad` as their cosets' factors' products there) as soon as its transforms are done; a piece's transforms are
     handed out while at most 256 MiB of them are held, and freed once its values are; then all the interpolations (`ntt::interpolate_prefix_many`:
     every block's inverse transform, the blocks of one size together, then the earlier blocks' folds, then the back
     substitution) and all the checks (`ntt::on_coset_prefix_each`). One quotient at a time, its short dispatches left
     most of 64 threads idle (the tables' leaves and `Q_W`'s parts 85–90 → 60 ms, 128 signatures). The memory's and
     the bytecode's leaves and `Q_W`'s public part, whose columns are `2^18`–`2^20`, go one at a time by `ntt`'s
     whole transforms (`quotients::prefix_quotient`). Where `quotient::ntt`'s lanes are portable code (aarch64), each
     push fingerprint is derived from its pull's sum (`prints::PullPush`).
   - `Q_W` is the sum of each table's part `Σ γ^i W_i / w_r` and the public input's, each on its own points.
     `SHA3`'s 50 lane copies are combined by their powers first: `Σ g_j copy_j` is one E-column, and `Σ g_j ℓ_j` the
     multilinear of the combined slot table (11 slot bits a row), one shifted cube a piece; `in_16`'s constant
     `END_BIT` is folded into the slot table.
   - A numerator that does not vanish on its domain is caught on one more block of points, where its value over the
     vanishing polynomial's is checked against the interpolant's: the quotient is then reported at full degree, and
     every quotient's degree is checked below the verifier's count.
   - `C1`'s polynomials are freed after the quotients, before `C2`'s commitment.
7. **`C2`**: the heap and every quotient's chunks (`Q = Q_0 + w_{e_0}(Q_1 + w_{e_1} Q_2)`, slices of the novel
   coefficients since `X_{2^e + k} = w_e X_k`), put in basis `B` limb by limb in place in the stack; leanVM's WHIR
   commit; then **`t`** and the values at `t`, in the verifier's order.
8. **`ρ`, and the combined claims** (`replay.rs`): the verifier's own `reduce` in weighted mode on the stream so far
   (weighted mode reads nothing after `ρ`; the claims are the point mode's, the ring switch's weight as its 64
   twisted terms instead of one). The verifier's checks on the stream so far are required to hold. Then each claim's
   weight on its stack (`weight.rs`, `Weight::with_slot_bits`: eq tensors, one table per several-point column,
   `q_flock`'s slot terms with 11 slot bits, the ring switch's map).
9. **The batching sumcheck** (`batch.rs`): `Σ_k λ^k Σ_u W_k(u) C_k(u)` over the longest stack, the others
   zero-extended. `batch::prove` (`KECCAK_MAIN`) sends two scalars a round, low variable first: its first 6 rounds
   read the stacks' words and the weights' pieces, then the folded stacks and weights are written out and folded on.
   `batch::prove_pairs` (`KECCAK_REC3`) runs two variables a round with narrow challenges; a stack shorter than the
   batch with an odd number of variables (the setup's `2^23` against `2^25`, say) zero-extends itself past its words'
   rounds. Then the stacks' values at the end point.
10. **The openings** (`opening.rs`): one point claim per commitment, leanVM's WHIR (vendored from c445e3d5) at rate
    `1/2`, its transcript seeded by a prefix that binds `PCS_OPEN`'s 32-byte layout word (version 2), whose `vars`
    and `placed` the verifier reads.

## The skip kernels (`crates/vendor/flock-42422001/src/zerocheck/skip.rs`)

leanVM's zerocheck prover hard-codes a skip of 6 in its round-1 kernel; its bit and table rounds were written for
rows of 8 bytes or more. The skip module proves the zerocheck for any `3 ≤ k ≤ 6`:

- **round 1**: `P(λ) = Σ_x eq(r, x)(â b̂ + ĉ)(λ, x)` on `Λ = φ_8(2^k + i)`. The seven fixed coordinates keep leanVM's
  small/medium structure (`eq(r_small, K) = C_s φ_8(X^K)`, asserted), so the 8 groups of a small run combine in
  `F_8`. At `k = 3` a word's 8 groups extend in one `gf2p8affine` (`round1_bytes`, x86 with GFNI); without GFNI (the
  Mac's aarch64) a medium position's AB row `Σ_K X^K â b̂` is 8 lookups of 8 tables `T_K[a ‖ b]` of `2^16` words
  (4 MB, built once: `round1_table`) and its C row an 8×8 bit transpose, instead of 128 byte products in software
  (400 signatures, `2^33` bits: 2.14 → 0.16 s on the Mac). At 4 and 5 a group's bytes are one affine each
  (`round1_words`); the 16 medium positions are one `BitFold` of 16-byte rows; the C part is computed on `S` and
  extended to `Λ`, as leanVM does;
- **bit rounds**: leanVM's pair kernels at levels `0, 2, ..` on rows of `2^(k + t)` bits, extended to rows of 1, 2,
  4 bytes (`BitFold`, GFNI included); at `k = 3`, level 0 is GF(2) matrix products on GFNI where it is available
  (`bytes_gfni`, no table or gathers), and otherwise reads its products from the table of all 65,536 byte
  products (`multilinear::bit_round_pair_bytes`); the pair passes at levels 2 and 4 multiply straight from the GFNI
  fold's limb-major registers (`fold_quads`, `pair_lanes`); on aarch64 (`bit_round_pair_bytes_scaled`) the quads' two lowest eq
  coordinates are in 4 such tables (6 MiB, `e_s[la] T[x] T[y]`), so a group of 4 quads sums its 8 slots by lookups and
  pays 8 products by eq, a quarter of the products (128 signatures, 16 threads: level 0 0.168 → 0.107 s); the
  storing pass at the level whose rows are 64 or 128 bytes;
- **table rounds**: leanVM's, copied.

Tested (`tests/flock_skip.rs`):

- at `k = 6`, round 1 equals leanVM's optimized kernel's message, and the whole zerocheck writes leanVM's stream, byte
  for byte;
- at `k = 3..6` on honest witnesses: the verifier's checks of the zerocheck hold, and its claims are the witness's
  evaluations;
- every fast kernel against the generic one: `round1_bytes`, `round1_words`, `round1_folded` against
  `round1_generic`; `bit_round_pair_bytes` against `bit_round_pair`, `bit_round_pair_bytes_scaled` (scales 1 to 3)
  against `bit_round_pair_bytes`; `BitFold` at every row width against its
  definition.

Flock end to end on the Keccak-f block is `tests/flock_keccak.rs` (`SPEC-FLOCK.md`, "Tests").

## Measured

**The reference workload, 128 signatures, `KECCAK_REC3`**, on the Mac (Apple M4 Max, 16 cores, 48 GiB, aarch64),
`RUSTFLAGS="-C target-cpu=native"`, 2026-11-08, with other agents' jobs on the machine (load average 9–14):
- one cold run with the checks (`proves_and_verifies_keccak_rec3`): 2.72 s, peak RSS 6.75 GB;
- warm, the median of 3 passes (`keccak_prover_benchmark`, `PI1_VARIANT=rec3`, 3 s cooldown): **3.65 s** (passes
  3.60, 3.65, 3.66 s), peak RSS 6.86 GB.

| phase (medians) | s |
|---|---:|
| the Keccak-f blocks: `q_flock` and Flock's witness | 0.03 |
| `C1` and setup: inverse NTTs to basis `B` | 0.05 |
| `C1` and setup: WHIR commits | 0.45 |
| Flock: zerocheck, lincheck, slices | 1.15 |
| heap: leaves, products, inverse NTT | 0.04 |
| quotient: tree | 0.06 |
| quotients: leaves | 0.44 |
| quotient: constraints `Q_W` | 0.08 |
| `C2`: chunks in basis `B` | 0.03 |
| `C2`: WHIR commit | 0.22 |
| values at `t`, claims, weights | 0.02 |
| batching sumcheck | 0.38 |
| openings: WHIR (3) | 0.66 |
| **total** | **3.65** |

**On an AMD EPYC 9355P** (Zen 5, 32 cores / 64 threads, AVX-512 with GFNI and VPCLMULQDQ; 2026-11-09, load 13–16,
median of 5 warm passes; the same proof), after the speedups of that day, against the same benchmark before them:

| phase (medians) | before | after |
|---|---:|---:|
| the Keccak-f blocks | 0.008 | 0.007 |
| `C1` and setup: inverse NTTs to basis `B` | 0.036 | 0.008 |
| `C1` and setup: WHIR commits | 0.074 | 0.038 |
| Flock: zerocheck, lincheck, slices | 0.196 | 0.090 |
| heap | 0.019 | 0.013 |
| quotient: tree | 0.032 | 0.014 |
| quotients: leaves | 0.269 | 0.069 |
| quotient: constraints `Q_W` | 0.078 | 0.025 |
| `C2`: chunks in basis `B` | 0.027 | 0.005 |
| `C2`: WHIR commit | 0.021 | 0.016 |
| values at `t`, claims, weights | 0.011 | 0.010 |
| batching sumcheck | 0.087 | 0.040 |
| openings: WHIR (3) | 0.085 | 0.065 |
| **total** | **0.94** | **0.40** |

On 64 threads most phases were bound by the pool's dispatches rather than by arithmetic: transforms of `2^14`–`2^16`
points a dispatch each, `parallel::for_each_mut`'s 64 items a task, one-thread memsets, per-worker accumulators reduced
on the dispatcher. Each piece's transform now runs on one worker, a round of them a dispatch, and columns share
dispatches. Columns near `2^25` words (the 8 CCDs' L3 together) read rows another CCD wrote last under shared task
claims; the thread-affine dispatches (`parallel::for_each_affine`, `affine`) give each worker the same range every
call (a `2^25`-point inverse transform 9.8 → 4.4–5.5 ms).

Then the tables' leaves and `Q_W`'s parts in shared dispatches and the heap's leaves in one (`prefix_quotients`,
`heap_of`; same machine, load 12–24, interleaved with the binaries before): the leaves and `Q_W` 0.083–0.098 → 0.063
s, the tree 0.015 → 0.013 s, π1 0.387–0.397 → 0.356–0.361 s; the pipeline (`tests/pipeline.rs`) 0.693 → 0.662 s a
proof; π1's peak RSS 7.2 → 7.8 GB (the pipeline's 13.8 → 14.5 GB).

The 400-signature phase table, the h1 figures and leanVM `9d50c92a3`'s own prover on the same machines are in
`KECCAK.md` ("Measured").

## The stacks' unused words

WHIR commits a stack's whole lanes that carry data; the words past the columns' blocks inside them are the
prover's. The verifier relies on nothing there: `unused_words_are_not_relied_on` fills them with pseudo-random words
(`Stack::fill_unused`, `Config::garbage`), and the proof is accepted by the verifier and the contract that bind the
resulting `F` root (garbage in the setup's unused words makes another `F`).

## Notes for the verifier

What the verifier's interface leaves to the prover, and how this one copes:

- **The combined claims are not exposed in point mode.** The prover needs each commitment's combined claim (terms,
  points, value) to write the batching sumcheck's weights; `reduce` returns them only in weighted mode. The prover
  replays point mode's stream through weighted mode (`replay.rs`), which relies on the two modes stating the same
  relations in the same order at the same challenges. A `reduce` that returned its combined claims in point mode too
  (before `batch`) would remove the replay.
- **The setup roots**: `record_verifier`, `parity` and `rust_verifier` bind `SetupRoots::REFERENCE` (the
  128-signature shape's `F`) whatever the shape; `record_verifier_with`, `parity_with` and `rust_verifier_with` take a
  shape's own roots. The prover's tests verify every shape against the contract that binds its own `F`.
- The shape's bytes are hashed twice into the IV (directly and in every layout word): harmless, left.
