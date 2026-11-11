<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->
# evm_link

Compiles a recorded verifier graph to straight-line EVM code and assembles it into one contract (`front`,
`assemble`), with the checks of the PCS claims a transaction declares in its frame of PCS claims (`declared_claims`;
the claim's wire format: `wire`; [`docs/PCS_CLAIM.md`](../../docs/PCS_CLAIM.md), "The EVM check"). With the feature
`machine`, the EVM the contracts run on in tests (`machine`: revm with `FIELD_MUL` and EIP-8141's frame
introspection over a mock frame of PCS claims, per-instruction gas). Used by `crates/membership/evm`,
`crates/leanvm/statement` and `crates/pcs_claim`.

```sh
cargo test --release -p evm_link
```
