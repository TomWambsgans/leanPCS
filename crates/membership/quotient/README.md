<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->
# quotient

Zero-knowledge Keccak-256 Merkle membership: the circuit (one χ gate on bits), the prover, the Rust verifier
(`protocol::reduce`) and the openings (`opening`: two commitments, three one-point PCS claims). Design:
[`docs/membership/PROTOCOL.md`](../../../docs/membership/PROTOCOL.md).

```sh
cargo test --release -p quotient                       # protocol, openings, zero knowledge's rank tests
cargo bench -p quotient --bench membership             # prover / verifier timings and sizes
```
