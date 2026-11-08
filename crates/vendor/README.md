# Vendored code

- `leanvm-c445e3d5/`: leanVM (https://github.com/leanEthereum/leanVM) commit `c445e3d5`'s `primitives`,
  `fiat_shamir`, `pcs`, `parallel`, `verifier` and `bench`: WHIR, its Merkle trees and transcript, the fields.
  Package names as upstream.
- `leanvm-42422001/`: leanVM commit `42422001`'s Flock prover: `primitives`, `parallel`, `pcs` (a part), `flock`, and
  `fiat_shamir` (a trait, new here), as packages `lv42_*`. Its BLAKE2s block is not vendored; the Keccak-f block
  (`flock/src/keccak.rs`) and the skip zerocheck (`flock/src/zerocheck/skip.rs`) are new here.

Files are as upstream but for what their header lists; [`../../NOTICE.md`](../../NOTICE.md) has the details.
