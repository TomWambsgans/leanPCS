<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->
# pcs_claim

The EIP draft's PCS claim, version 1 ([`docs/PCS_CLAIM.md`](../../docs/PCS_CLAIM.md)): its encoding
(`version || n || root || ood || point || value`), its commitment (leanVM's WHIR root and the out-of-domain answer at a
point derived from the root), and its opening (one WHIR opening of `f(z) = ood` and `f(point) = value`, transcript
seeded by `keccak256(PCS_claim)`), with leanVM's WHIR prover and verifier unchanged. `verify` is the EIP's
`pcs_verify`. The EVM check of a claim declared in a frame is `evm_link::Item::DeclaredClaim`.

```sh
cargo test --release -p pcs_claim                                                 # encoding, binding, openings, EVM packing
cargo test --release -p pcs_claim --test evm_packing -- --ignored --nocapture     # gas of one claim's check, by n
cargo run --release -p pcs_claim --example eip_vectors                            # the EIP's test case
```
