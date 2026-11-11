<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->
# evm_link

Compiles a recorded verifier graph to straight-line EVM code and assembles it into one contract (`assemble`,
`front`), with the checks of the claims a transaction declares in its frame of PCS claims (`declared`,
`declared_claims`; [`docs/PCS_CLAIM.md`](../../docs/PCS_CLAIM.md), "The EVM check"). Used by `crates/membership/evm`
and `crates/leanvm/statement`.

```sh
cargo test --release -p evm_link
```
