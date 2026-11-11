<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->
# gf2_linear

GF(2)-linear maps of `E = GF(2^192)`, `x ↦ Σ_k c_k x^(2^k)`, `N` at once: byte tables, and a GFNI kernel
(`vgf2p8affineqb`) on x86-64. Used by π1's prover (`leanvm_univariate`'s batching sumcheck;
[`docs/leanvm/univariate/PROVER.md`](../../../docs/leanvm/univariate/PROVER.md)).

```sh
cargo test --release -p gf2_linear
```
