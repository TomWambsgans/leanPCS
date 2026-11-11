<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# The prover of the univariate PIOP

`src/prover/` proves [`SPEC.md`](SPEC.md)'s statement on executions of the Keccak VM (leanVM `9d50c92a3`,
[`KECCAK.md`](KECCAK.md)), from the trace `src/prover/dump_keccak/` makes leanVM write. It writes the stream
`verifier::reduce` reads (through the Keccak-256 chain) and one PCS opening per claim, one claim per commitment (`C1`,
`C2`, the setup `F`). It proves every variant, `KECCAK_MAIN`, `KECCAK_REC3` and `KECCAK_REC4` (π1-rec4, the
recursion's inner proof), with point claims; weighted claims (extension W) have no opening prover. Its measurements
are in [`docs/PERF_PROVER.md`](../../PERF_PROVER.md).

## Status

On real executions (32, 128 and 400 signatures) and every variant: the Rust verifier accepts; the three WHIR openings
verify; the contract (`KECCAK_MAIN`, `KECCAK_REC3`) accepts the real calldata, word for word with the Rust verifier,
with the frame declaring exactly the claims the openings prove, and rejects a flipped byte and a claim left
undeclared; five stream mutations are rejected by the Rust verifier (`tests/prove_real.rs`).

**Rust→EVM test vectors.** `tests/vectors/` holds five real proofs ([`KECCAK.md`](KECCAK.md), "Vectors"). Each holds
the calldata, the claims the contract checks declared, the committed roots, the verdict and the gas, straight and
deployed. `tests/evm_vectors.rs` replays them with no prover and no trace, the contract binding the vector's own `F`
(its third claim's root): both builds accept at the recorded gas, check exactly the recorded claims declared, and
revert on 17 mutations each (a row count, `C1`'s root, `C1`'s out-of-domain answer, two scalars, a batching round, the
last byte or the public input flipped; each claim left undeclared; each declared value and each declared
out-of-domain answer flipped). The π1-rec4 vectors, which have no contract, are replayed through the Rust verifier:
it gives the recorded claims, and 9 flipped bytes change them. `tests/lean_keccak_vectors.rs` turns the real proofs and
solved sample streams into the Lean transcription's differential vectors.

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
   it, and the trace keeps no copy.
4. **Proving and checking.** Build with `RUSTFLAGS="-C target-cpu=native"`, as leanVM's own `.cargo/config.toml`
   does (without it the field is about 25× slower), and set `LEANVM_TRACE=<dir of a dump_keccak trace>`:

   ```sh
   cargo test --release -p leanvm_univariate --test prove_real -- --ignored --nocapture --test-threads 1
   ```

   - `proves_and_verifies_keccak` (`KECCAK_MAIN`), `proves_and_verifies_keccak_rec3` (`KECCAK_REC3`) and
     `proves_and_verifies_keccak_rec4` (`KECCAK_REC4`): the proof, the quotients' degrees, every combined claim against
     its stack, the Rust verifier, the WHIR openings, the contract on the real calldata (word-for-word parity with the
     Rust verifier; π1-rec4 has none, its Rust verifier's claims are the openings'), each claim against the one its
     opening proves, and the mutations. With `WRITE_VECTORS=<dir>` each writes its test vector (`VECTOR_FILE` names
     it).
   - `identities_hold_on_the_domain` (the bus balance, the copies on every row, the counters), `setup_roots` (the
     trace's `F` root), `unused_words_are_not_relied_on` (below).
   - `keccak_prover_benchmark`: warm passes with a cooldown between them, as leanVM's benchmark runs (`PI1_REPEAT`,
     default 3; `PI1_COOLDOWN`, default 2 s; `PI1_VARIANT=rec4` for `KECCAK_REC4`, `rec3` for `KECCAK_REC3`), the median of each phase; each
     pass's proof is checked to be the first's.

   Without a trace: `flock_skip` and `flock_keccak` (the skip kernels, Flock on the Keccak-f block), `evm_vectors`
   (the committed vectors).

## The prover, phase by phase (`src/prover/prove.rs`)

1. **`C1` and the setup** (`columns.rs`, `stack.rs`, `setup.rs`): every column through the inverse additive NTT to
   its novel coefficients (`crates/membership/quotient/src/ntt.rs`, vectorized), then by subset sums to basis `B`
   straight into the stack; the counter inverses `z_T = 1/Π c_j` on every row; `q_flock` as values, from the Flock
   witness. The setup `F`: the bytecode's 16 tuple slots interleaved and the memory's addresses. Then leanVM's WHIR
   commits of both. The prover checks that the contract's `F` root is the one it commits (`setup::shape_roots`).
   `Config::low_memory` commits `C1` without keeping its codeword (twice its stack), so that its opening re-encodes the
   rows its queries open: the same proof, a lower peak.
2. **The seed** is `keccak(name ‖ contract_iv(shape, variant, program IV, roots) ‖ public input)` (`SPEC.md` §13,
   F2). The stream starts with the six row counts, then `C1`'s commitment: its root's 32 bytes as they are (`KeccakWriter::send_root`),
   then its out-of-domain answer, which binds the root to one polynomial before any challenge.
3. **The challenges** `α, β, γ`; with π1-rec3 and π1-rec4 `α = (c, c², c⁴, c⁸)`, squared in `E` as the verifier
   squares it; with π1-rec4 drawn wide, as the verifier draws them (`SPEC.md` §14.4).
4. **Flock** (`flock.rs`, behind one call): the zerocheck at a skip of 3 (`flock::zerocheck::skip`, below; with
   π1-rec3 and π1-rec4 its sampled eq coordinates are successive squares, `EqPoint::Squares`), the lincheck at the row
   weights the skip leaves, the 64 slices, then the ring map's six challenges (with π1-rec4 after `C2`'s commitment).
   The slices' point is checked against the one the verifier derives. Flock's witness is freed after it.
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
     substitution) and all the checks (`ntt::on_coset_prefix_each`); one quotient at a time, its short dispatches would
     leave most threads idle. The memory's and
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
   commit, its root and out-of-domain answer sent; then **`t`** and the values at `t`, in the verifier's order.
8. **`ρ`, and the combined claims**: the verifier's own `reduce_combined` on the stream so far (a `KeccakChannel`
   collecting its checks; it reads nothing after `ρ`), the ring switch's weight written as its 64 twisted terms
   (`verifier::expand_ring`). The verifier's checks on the stream so far are required to hold. Then each claim's
   weight on its stack (`weight.rs`, `Weight::with_slot_bits`: eq tensors, one table per several-point column,
   `q_flock`'s slot terms with 11 slot bits, the ring switch's map).
9. **The batching sumcheck** (`batch.rs`): `Σ_k λ^k Σ_u W_k(u) C_k(u)` over the longest stack, the others
   zero-extended. `batch::prove` (`KECCAK_MAIN`) sends two scalars a round, low variable first: its first 6 rounds
   read the stacks' words and the weights' pieces, then the folded stacks and weights are written out and folded on.
   `batch::prove_pairs` (`KECCAK_REC3`, `KECCAK_REC4`; `SPEC.md` §14.1) runs two variables a round with narrow
   challenges; a stack shorter than the
   batch with an odd number of variables (the setup's `2^23` against `2^25`, say) zero-extends itself past its words'
   rounds. Then the stacks' values at the end point.
10. **The openings** (`opening.rs`, over `crates/pcs_claim`): one PCS claim per commitment, the EIP draft's: the
    stack in its `vars` variables (its leading lanes committed, the commitment the whole stack's), its root and
    out-of-domain answer (sent after the root, §4 of SPEC.md), the batch's point and the value; one opening of PCS
    version 1 (leanVM's WHIR, vendored from c445e3d5, at rate `1/2` on its ladder), its transcript seeded by
    `keccak256(PCS_claim)`, proving the out-of-domain answer and the claim at one random combination, its level-0
    rows padded to the whole stack's (`pcs_claim::open_words`).

## The skip kernels (`crates/vendor/flock-42422001/src/zerocheck/skip.rs`)

leanVM's zerocheck prover hard-codes a skip of 6 in its round-1 kernel; its bit and table rounds were written for
rows of 8 bytes or more. The skip module proves the zerocheck for any `3 ≤ k ≤ 6`:

- **round 1**: `P(λ) = Σ_x eq(r, x)(â b̂ + ĉ)(λ, x)` on `Λ = φ_8(2^k + i)`. The seven fixed coordinates keep leanVM's
  small/medium structure (`eq(r_small, K) = C_s φ_8(X^K)`, asserted), so the 8 groups of a small run combine in
  `F_8`. At `k = 3` a word's 8 groups extend in one `gf2p8affine` (`round1_bytes`, x86 with GFNI); without GFNI (the
  Mac's aarch64) a medium position's AB row `Σ_K X^K â b̂` is 8 lookups of 8 tables `T_K[a ‖ b]` of `2^16` words
  (4 MB, built once: `round1_table`) and its C row an 8×8 bit transpose, instead of 128 byte products in software.
  At 4 and 5 a group's bytes are one affine each
  (`round1_words`); the 16 medium positions are one `BitFold` of 16-byte rows; the C part is computed on `S` and
  extended to `Λ`, as leanVM does;
- **bit rounds**: leanVM's pair kernels at levels `0, 2, ..` on rows of `2^(k + t)` bits, extended to rows of 1, 2,
  4 bytes (`BitFold`, GFNI included); at `k = 3`, level 0 is GF(2) matrix products on GFNI where it is available
  (`bytes_gfni`, no table or gathers), and otherwise reads its products from the table of all 65,536 byte
  products (`multilinear::bit_round_pair_bytes`); the pair passes at levels 2 and 4 multiply straight from the GFNI
  fold's limb-major registers (`fold_quads`, `pair_lanes`); on aarch64 (`bit_round_pair_bytes_scaled`) the quads' two lowest eq
  coordinates are in 4 such tables (6 MiB, `e_s[la] T[x] T[y]`), so a group of 4 quads sums its 8 slots by lookups and
  pays 8 products by eq, a quarter of the products; the storing pass at the level whose rows are 64 or 128 bytes;
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

Flock end to end on the Keccak-f block is `tests/flock_keccak.rs` ([`FLOCK.md`](FLOCK.md), "Tests").

## Parallel structure

On many threads the phases are bound by the pool's dispatches more than by arithmetic, so the prover avoids short
dispatches: each piece's transform runs on one worker, a round of them a dispatch, and columns share dispatches; the
tables' leaves and `Q_W`'s parts share their dispatches (`quotients::prefix_quotients`), and every block's heap leaves
are one dispatch (`heap_of`). Columns near `2^25` words span the L3 caches of several CCDs, so the thread-affine
dispatches (`parallel::for_each_affine`, `affine`) give each worker the same range of a column every call. The
per-phase times, on 8 threads of an AMD EPYC 9355P and against leanVM `9d50c92a3`'s own prover, are in
[`docs/PERF_PROVER.md`](../../PERF_PROVER.md).

## The stacks' unused words

WHIR commits a stack's whole lanes that carry data; the words past the columns' blocks inside them are the
prover's. The verifier relies on nothing there: `unused_words_are_not_relied_on` fills them with pseudo-random words
(`Stack::fill_unused`, `Config::garbage`), and the proof is accepted by the verifier and the contract that bind the
resulting `F` root (garbage in the setup's unused words makes another `F`).

## Notes for the verifier

What the verifier's interface leaves to the prover, and how this one copes:

- **The combined claims**: the prover needs each commitment's combined claim (terms, points, value) to write the
  batching sumcheck's weights; `reduce_combined` returns them (`reduce` is it and `batch`), and the prover runs it on
  its stream so far.
- **The setup roots**: `record_verifier`, `parity` and `rust_verifier` bind `SetupRoots::REFERENCE` (the
  128-signature shape's `F`) whatever the shape; `record_verifier_with`, `parity_with` and `rust_verifier_with` take a
  shape's own roots. The prover's tests verify every shape against the contract that binds its own `F`.
- The IV binds the shape's bytes once (the claims carry no layout word).
