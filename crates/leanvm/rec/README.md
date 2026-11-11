<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# leanvm_rec (π2 and the recursion's contract)

A Keccak VM proof verified on the EVM by recursion. π1 is `crates/leanvm/univariate`'s π1-rec4 (`KECCAK_REC4`,
`leanvm_rec::PI1`; the Lean states π1-rec3); π2 is a univariate SNARK of π1's verifier minus its
openings, its circuit compiled from π1's recorded verifier graph (`circuit`, D16v), which also hashes π1's three
claims; the contract (`pi2::contract`) runs π2's verifier only and checks π1's three (by their hashes, the frame's
payloads 0 … 2, which the circuit computes) and π2's four claims declared in its transaction's frame of PCS claims,
each the EIP draft's PCS claim (`crates/pcs_claim`: a commitment's root and out-of-domain answer, one point, its value;
one opening a claim).

On the real 128-signature proof (the reference, `crates/leanvm/univariate/tests/vectors/keccak128_rec4.txt`):
577 B of calldata, 31,212 gas of execution; as an EIP-8141 frame transaction (EIP-7976's floor, without the base and
per-frame costs) standard 40,396, floor 36,928, and 63,328 with its frame of PCS claims and their PCS gas
(`docs/leanvm/rec/SPEC-REC.md` §6). π2 is π2v4
(transcript `leanvm-rec-pi2v4`, `PI2.md`: the ports out of the copy argument, on the EIP's PCS claims, the copy sum
forced by `Q`'s layout),
`Q` sixteen slots of `N` words.

Design: [`SPEC-REC.md`](../../../docs/leanvm/rec/SPEC-REC.md) (the recursion), [`PI2.md`](../../../docs/leanvm/rec/PI2.md)
(π2's PIOP).

```sh
cargo test --release -p leanvm_rec                                                          # circuit, PIOP, contract
cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_gas        # π2's circuit and gas, 128 and 400
PI2_VECTOR=keccak128_rec4 cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end
LEANVM_TRACE=<trace dir> cargo test --release -p leanvm_rec --test pipeline -- --ignored --nocapture   # trace → π1 → π2, timed
```

`real_end_to_end` proves π2 on the real π1-rec4 proof, verifies its openings, and runs the contract on the real
calldata with its frame declaring exactly the openings' claims (and rejects flipped bytes). `pipeline` runs the
recursion from a Keccak VM trace (`crates/leanvm/univariate/src/prover/dump_keccak`): the per-circuit setup once, then
warm passes of π1-rec4's proof and openings (π2's witness compiled on π1's stream while π1's openings run,
`prover::prove::prove_streaming`), π2's proof and openings, each phase's median; every pass's proofs equal the first's,
and at the reference trace π1's stream equals the committed vector's and the four fingerprints (π1's stream and
openings, π2's stream and openings) are pinned. Build with `RUSTFLAGS="-C target-cpu=native"` for timings.
