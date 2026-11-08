# Vendored code

- `leanvm-c445e3d5/`: leanVM (https://github.com/leanEthereum/leanVM) commit `c445e3d5`'s `primitives`,
  `fiat_shamir`, `pcs`, `parallel`, `verifier` and `bench`: WHIR, its Merkle trees and transcript, the fields.
  Package names as upstream.
- `flock-42422001/`: leanVM commit `42422001`'s Flock prover (`crates/flock`), package `flock`, ported onto
  `leanvm-c445e3d5/`'s `primitives`, `parallel` and `pcs`. What it uses of `42422001`'s own `primitives` and `pcs` that
  `c445e3d5` lacks is copied into it (`src/field`, `src/lagrange.rs`, `src/ntt`); its transcript is a trait
  (`src/transcript.rs`, new here). Its BLAKE2s block is not vendored; the Keccak-f block (`src/keccak.rs`) and the skip
  zerocheck (`src/zerocheck/skip.rs`) are new here.

Files are as upstream but for what their header lists; [`../../AGENTS.md`](../../AGENTS.md) has the details.
