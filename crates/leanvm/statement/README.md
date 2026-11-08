<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# leanvm_statement

The Keccak VM's statement and the verifier pieces built on it, generic over the scalar they compute on, shared by
`leanvm_univariate` (π1) and `leanvm_rec` (π2):

- `layout`: the six instruction tables (leanVM `42422001`'s XOR, MUL, SET, DEREF, JUMP, and leanVM `9d50c92a3`'s
  `SHA3`), their bus flushes and constraints;
- `flock`, `flock_min`, `ring_tower`: Flock's verifier (zerocheck with a univariate skip, lincheck, ring switch with
  the map in tower order); `keccak_flock`: the Keccak-f block's walk and structured terminal
  ([`docs/leanvm/flock/KECCAK.md`](../../../docs/leanvm/flock/KECCAK.md));
- `transcript`: the Keccak-256 Fiat–Shamir chain (`KeccakChannel`, `KeccakWriter`, the shapes `FsShape`);
- `evm`: the recorder that runs a verifier on a symbolic scalar, the nodes' code for `crates/evm_link`, a revm
  machine with `FIELD_MUL` and a mock `PCS_OPEN`, deployment;
- `shapes`: the measured workloads (leanVM `9d50c92a3`, 32 to 1,000 signatures; the reference is 128) and the
  program IV the contracts are built with.

```sh
cargo test --release -p leanvm_statement                                                  # reductions, terminals
cargo test --release -p leanvm_statement --test keccak_terminal -- --nocapture            # Keccak-f terminal == walk
```
