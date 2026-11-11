<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# leanvm_univariate (π1)

A univariate PIOP for the Keccak VM's statement (leanVM `9d50c92a3`), for the EVM with aggregated PCS claims
(declared in a transaction's frame, the EIP draft): two proof commitments and one setup commitment (each a root and
an out-of-domain answer, `crates/pcs_claim`), the bus as a grand product in a committed heap, every identity checked at
one point, Flock on the Keccak-f block, one PCS claim per commitment (a point of its whole stack).

- `verifier`: the verifier (`reduce`), generic over the scalar; `contract`: it compiled to EVM code, its calldata,
  its gas; `prover`: the prover, on traces leanVM writes (`prover/dump_keccak`).
- Variants: `KECCAK_MAIN`; `KECCAK_REC4` (π1-rec4, the inner proof of `crates/leanvm/rec` since
  `docs/leanvm/rec/PERF_GAS2.md`, no contract of its own); `KECCAK_REC3` (π1-rec3, the inner proof before it, kept
  because the Lean proves it).
- Design: [`SPEC.md`](../../../docs/leanvm/univariate/SPEC.md) (the PIOP),
  [`SPEC-FLOCK.md`](../../../docs/leanvm/univariate/SPEC-FLOCK.md),
  [`PROVER.md`](../../../docs/leanvm/univariate/PROVER.md),
  [`KECCAK.md`](../../../docs/leanvm/univariate/KECCAK.md) (the VM, workloads, gas, measurements).

At the reference workload (128 signatures) the contract alone takes 8,069 B of calldata and 231,511 gas of execution;
as an EIP-8141 frame transaction (EIP-7976's floor) standard 360,255, floor 516,416, without its frame of claims.

```sh
cargo test --release -p leanvm_univariate                                                  # contract == Rust verifier, vectors, Flock
cargo test --release -p leanvm_univariate --test keccak_vm -- --ignored --nocapture keccak_gas_report
LEANVM_TRACE=<trace> cargo test --release -p leanvm_univariate --test prove_real -- --ignored --nocapture --test-threads 1
```

`tests/vectors/` holds real proofs (calldata, the claims declared, gas): `keccak.txt` (32 signatures, `KECCAK_MAIN`),
`keccak128_rec4.txt` (128, `KECCAK_REC4`, the reference) and `keccak_rec4.txt` (400, `KECCAK_REC4`), and
`keccak128_rec3.txt`, `keccak_rec3.txt` (the same with `KECCAK_REC3`, which the Lean proves), replayed by
`tests/evm_vectors.rs` (π1-rec4's against the Rust verifier) and written by `tests/prove_real.rs` (`WRITE_VECTORS=<dir>`). `tests/lean_keccak_vectors.rs`
writes the vectors of `formal/UniKeccak`'s differential runner.
