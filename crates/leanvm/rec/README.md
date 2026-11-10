<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# leanvm_rec (π2 and the recursion's contract)

A Keccak VM proof verified on the EVM by recursion. π1 is `crates/leanvm/univariate`'s π1-rec3 (`KECCAK_REC3`); π2 is
a univariate SNARK of π1-rec3's verifier minus its openings, its circuit compiled from π1's recorded verifier graph
(`circuit`, D16v); the contract (`pi2::contract`) runs π2's verifier only and checks π1's and π2's claims
declared in its transaction's frame of PCS claims (7 claims as 6, `crates/membership/evm/src/machine.rs`'s encoding).

On the real 128-signature proof (the reference, `crates/leanvm/univariate/tests/vectors/keccak128_rec3.txt`):
1,004 B of calldata, 27,641 gas of execution, 42,997 of transaction gas (EIP-7623, claims free, without the 21,000
base); one contract of 13.2 KB. π2 is π2v2 (`PI2.md`: the ports out of the copy argument, `Q` `12N` words).

Design: [`SPEC-REC.md`](../../../docs/leanvm/rec/SPEC-REC.md) (the recursion), [`PI2.md`](../../../docs/leanvm/rec/PI2.md)
(π2's PIOP), [`SPEC-POINTS.md`](../../../docs/leanvm/rec/SPEC-POINTS.md) (the claims' points).

```sh
cargo test --release -p leanvm_rec                                                          # circuit, PIOP, contract
cargo test --release -p leanvm_rec --test keccak_vm_rec -- --ignored --nocapture            # π2's circuit and gas, 128 and 400
PI2_VECTOR=keccak128_rec3 cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end
LEANVM_TRACE=<trace dir> cargo test --release -p leanvm_rec --test pipeline -- --ignored --nocapture   # trace → π1 → π2, timed
```

`real_end_to_end` proves π2 on the real π1-rec3 proof, verifies its openings, and runs the contract on the real
calldata with its frame declaring exactly the openings' claims (and rejects flipped bytes). `pipeline` runs the
recursion from a Keccak VM trace (`crates/leanvm/univariate/src/prover/dump_keccak`): the per-circuit setup once, then
warm passes of π1-rec3's proof and openings (π2's witness compiled on π1's stream while π1's openings run,
`prover::prove::prove_streaming`), π2's proof and openings, each phase's median; it checks the proofs against the
committed vector and `pi2_real`'s fingerprints. Build with `RUSTFLAGS="-C target-cpu=native"` for timings.
