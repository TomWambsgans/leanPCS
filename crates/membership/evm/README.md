<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->
# evm

The membership verifier as an EVM contract, recorded from `quotient::protocol::reduce` and compiled through
`evm_link`, run in tests on `evm_link::machine` (revm with `FIELD_MUL` and EIP-8141's frame introspection). ABI, deployment and `setIndexCommitment` are in
`src/quotient.rs`. Design: [`docs/membership/PROTOCOL.md`](../../../docs/membership/PROTOCOL.md).

```sh
cargo test --release -p evm                                         # the contract == the Rust verifier, attacks
cargo test --release -p evm -- --ignored --nocapture gas_report     # gas
```
