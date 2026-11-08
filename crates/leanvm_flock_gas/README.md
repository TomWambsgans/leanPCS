<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# leanVM's statement, Flock's verifier and the EVM toolchain, generic over the scalar

The pieces `crates/leanvm_univariate` (π1) and `crates/leanvm_rec` (π2 and the recursion's contract) are built on:

- **leanVM's statement**, ported from leanVM `42422001`'s `crates/verifier` (`src/layout.rs`, `src/bus.rs`): the
  six instruction tables, their bus flushes and constraints, and the stacking.
  - `layout::tables_keccak` puts the `SHA3` table of leanVM's Keccak VM (commit `9d50c92a3`) in BLAKE2S's place
    (`crates/leanvm_univariate/KECCAK.md`).
- **Flock's verifier**, generic over the scalar it computes on (`src/flock.rs`, `src/flock_min.rs`): the zerocheck
  with a univariate skip, the lincheck, the ring switch (`src/ring_tower.rs`) and the matrices' reduction
  (`src/matrices.rs`).
  - Its lincheck terminal is either BLAKE2s's walk, or the Keccak-f block's structured terminal
    (`src/keccak_flock.rs`, design in `crates/lv42_flock/KECCAK.md`).
- **The Keccak-256 Fiat–Shamir chain** (`src/transcript.rs`, after `crates/quotient/src/transcript.rs`).
- **The EVM toolchain** (`src/evm/`):
  - a recorder that runs a verifier on a symbolic scalar and gives its graph;
  - the nodes' code for `crates/evm_link`, which compiles, assembles and links into EIP-170 contracts;
  - a revm machine with `FIELD_MUL` and a mock `PCS_OPEN` that gives each instruction's gas;
  - contract, deployment and gas reports.
- **The measured workloads** (`src/shapes.rs`): leanVM `42422001` leaf aggregates of 32 to 2,000 leanXMSS signatures,
  their announced sizes, and the program's IV.

The crate also keeps leanVM `42422001`'s own verifier, ported and made generic (`src/lib.rs`: `walk`,
`verify_execution`, `reduce`; native `field`, `hash`, `merkle`, `bytecode`, `whir`). It is the reference the port is
checked against. As a contract, it is this repository's baseline: 335,627 gas of execution, and 1,077,470 of
transaction gas under EIP-7623 (calldata-bound, 27 KB), for leanVM's 1,290-signature proof. `crates/leanvm_rec`
verifies the same statement for about 45,000.

```sh
cargo test --release -p leanvm_flock_gas                                                         # parity, reductions, terminals
cargo test --release -p leanvm_flock_gas --test evm -- --ignored --nocapture gas_report          # the baseline's gas
cargo test --release -p leanvm_flock_gas --test keccak_terminal -- --nocapture                   # Keccak-f terminal == walk
```

Where each file comes from is in its first lines and in `NOTICE.md`.
