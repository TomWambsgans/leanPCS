<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# leanVM's statement, Flock's verifier and the EVM toolchain, generic over the scalar

The pieces `crates/leanvm/univariate` (π1) and `crates/leanvm/rec` (π2 and the recursion's contract) are built on:

- **leanVM's statement**, ported from leanVM `42422001`'s `crates/verifier` (`src/layout.rs`, `src/bus.rs`): the
  six instruction tables, their bus flushes and constraints, and the stacking.
  - `layout::tables_keccak` puts the `SHA3` table of leanVM's Keccak VM (commit `9d50c92a3`) in BLAKE2S's place
    (`docs/leanvm/univariate/KECCAK.md`).
- **Flock's verifier**, generic over the scalar it computes on (`src/flock.rs`, `src/flock_min.rs`): the zerocheck
  with a univariate skip, the lincheck, the ring switch (`src/ring_tower.rs`) and the matrices' reduction
  (`src/matrices.rs`).
  - Its lincheck terminal is either BLAKE2s's walk, or the Keccak-f block's structured terminal
    (`src/keccak_flock.rs`, design in `docs/leanvm/flock/KECCAK.md`).
- **The Keccak-256 Fiat–Shamir chain** (`src/transcript.rs`, after `crates/membership/quotient/src/transcript.rs`).
- **The EVM toolchain** (`src/evm/`):
  - a recorder that runs a verifier on a symbolic scalar and gives its graph;
  - the nodes' code for `crates/evm_link`, which compiles, assembles and links into EIP-170 contracts;
  - a revm machine with `FIELD_MUL` and a mock `PCS_OPEN` that gives each instruction's gas;
  - deployment of a linked verifier, and the gas of a fragment.
- **The measured workloads** (`src/shapes.rs`): leanVM `42422001` leaf aggregates of 32 to 2,000 leanXMSS signatures,
  their announced sizes, and the program's IV.

```sh
cargo test --release -p leanvm_statement                                                         # reductions, terminals
cargo test --release -p leanvm_statement --test keccak_terminal -- --nocapture                   # Keccak-f terminal == walk
```

Where each file comes from is in its first lines and in `NOTICE.md`.
