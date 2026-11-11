# ZK-STARKS on Ethereum via PCS opening aggregations?

## Naive, simplified, idea:

- We agree on:
  - one base field K, one extension field E (example: K = F_2^64, E = F_2^192)
  - one PCS (example: WHIR in the LDR at rate 1/2)
- We add a new instruction to perform extension field multiplication in E: MULFIELD.
- Users can attach to each transaction a list of PCS claims.
- Each PCS claim contains:
  - header (the EIP draft's `PCS_claim`, `crates/pcs_claim`): the PCS version, `num_variables`, the commitment (a
    Merkle root and an out-of-domain answer, which binds the root to one polynomial), one opening point
    (`num_variables` E field elements) and its value (1 E field element)
  - opening_proof (the PCS opening transcript, where Fiat-Shamir is seeded by the header's Keccak-256)
- The transaction declares each header by its Keccak-256, as an EIP-8288 dependency (a frame of PCS claims).
- In the mempool, all the opening_proof 'disappear', and instead some STARK attests of their existence.
- Each Ethereum block's STARK proves every header its transactions declare.
- No precompile: a contract hashes the header it needs and finds it in its transaction's frame of PCS claims
  (EIP-8141's frame introspection).

## Simplified example for R1CS: A.z ⊙ B.z = C.z in K

- A, B, and C, all of size 2^n x 2^n are interpreted as three multilinear polynomials in 2n variables in K
- All three have hardcoded commitment in the smart contract (storage or bytecode): comA, comB, comC.
- Prover commits to z (n variables): comZ (appears in calldata)
- It seeds some Fiat-Shamir state (not necessarily the same hash function as the one used in WHIR! (this requires future security proofs))
- Runs Spartan's sumchecks (1 zerocheck, 3 linchecks)
- In the end, you get 4 opening claims: pointZ, valueZ, pointA, valueA, ...
- Check that the transaction declares the headers (comZ, pointZ, valueZ), (comA, pointA, valueA), ...

## Forward compatibility

- The witness polynomial of the STARK is easy to change (commitment / opening algorithms are offchain).
- The difficult part is the polynomial representing the circuit whose commitment is hardcoded in a smart contract.

In 2031, when WHIR 2.0 is released, how to upgrade the PCS? -> An idea from Justin D:
- each header carries a version (its first byte). Initially one version is valid, and a block cannot prove a
  header of another version.
- Hardfork -> version v + 1 is introduced. Version v remains available for a period of time (1 year), and is afterward deleted.
Every smart contract should:
- put the commitment of the circuit in storage (not bytecode)
- have a (trustless) function that lets any users calling it update the commitment (from v to v + 1). To prove that the new commitment is valid, we sample a random point (Fiat-Shamir) and require both PCS openings at versions v and v + 1 to agree on that point (Schwartz–Zippel); the new root binds one polynomial because anyone can recompute it from the public circuit.

TLDR: The PCS is relatively easy to upgrade, the only thing that cannot be upgraded is the (binary) field.

## Details

- We want a "ZKZK-friendly" PCS -> at a prover overhead of typically 2x or 4x, we can make it ZKZK without changing the verifier *at all* (WHIR is an example)
- I don't think we need to put the Fiat-Shamir states (before + after) in the header (but this requires security analysis)

## This repository

The idea above on two Keccak workloads: `K = GF(2^64)`, `E = GF(2^192)`, `MUL_FIELD` at 10 gas, leanVM's WHIR, Fiat–Shamir
Keccak-256, and each transaction's PCS claims declared in an EIP-8288 frame that the contract reads with EIP-8141's
`FRAMEPARAM` and `FRAMEDATALOAD` (mocked on revm), as the EIP draft ([`eip-draft_leanPCS.md`](eip-draft_leanPCS.md)) has it.

### One ZK proof of Keccak-256 Merkle membership (`crates/membership`)

Statement `(y, root)`, witness `x` and a depth-32 path: `y = H(x | 0x11..)`, path from `H(x | 0x22..)` to `root`
([`docs/membership/PROTOCOL.md`](docs/membership/PROTOCOL.md)).

| | |
|---|---|
| Circuit | 34 Keccak-256 (one gate `V = Y + C + X·C` on bits), the public words packed and pinned: 3,878,615 of 2^22 rows |
| Prover | **1.01 s**, 6.0 GiB, on 8 threads of an AMD EPYC 9355P (median of 5, 2026-11-11): two commitments, three openings |
| Calldata | 273 B (statement, 2 roots, 6 field elements, the frame's index; no selector) |
| PCS claims | 3, in the EIP's encoding (97 B of frame) |
| Gas | 15,753 execution; **31,680** transaction under EIP-8141 (floor-bound, `pcs_gas` in the floor; no base or per-frame cost) |
| Deployment | 4,866 B of code, 1,149,640 gas |
| Lean 4 | knowledge soundness (≈ 2^-61.4 at 2^64 queries), completeness (< 2^-163) and the contract = the verifier, proved; zero knowledge proved under two hypotheses; all of the protocol of `f96a7938` (six claims), not yet ported to the current one ([`docs/LEAN_PORT.md`](docs/LEAN_PORT.md)) |

### One leanVM proof by recursion (`crates/leanvm`)

A leaf aggregate of leanXMSS signatures by leanVM's Keccak VM (commit `9d50c92a3`: leanVM `42422001` with a `SHA3`
table). π1, a univariate PIOP, proves its execution, Flock proving the Keccak-f permutations; π2 proves π1-rec4's
verifier (π1 with Fiat–Shamir shaped for π2) minus its openings; the contract runs π2's verifier.

| | **128 signatures (the reference)** | 400 signatures |
|---|---:|---:|
| VM execution | 154,148 cycles; tables of `2^14`–`2^16` rows, memory `2^20` | 473,348 cycles; `2^16`–`2^17` rows, memory `2^22` |
| Prover, trace → π1 → π2 and openings | **2.52 s**, 15.6 GB, on 8 threads of an AMD EPYC 9355P (median of 5, 2026-11-11) | |
| Calldata | 577 B (4 zero): π1's three claims hashed in π2's circuit, no selector | 577 B |
| Gas (EIP-8141 frame transaction, EIP-7976 floor, no base or per-frame cost) | 31,524 execution; standard 40,708, floor 36,928; with the frame (257 B) and `pcs_gas` 13,000: **66,376** (the floor binds) | 35,761 execution; 66,376 |
| PCS claims | 8: π1's 3, π2's 5 | 8 |
| Lean 4 | the VM's statement, the Keccak-f block, π1's knowledge soundness (≤ 2^-64 at 2^64 queries) and completeness; the recursion's knowledge soundness as an explicit reduction and its completeness; all of π2 over π1-rec3 at `f96a7938`, not yet ported ([`docs/LEAN_PORT.md`](docs/LEAN_PORT.md)) | |

π1 alone as a contract (no recursion) at 128 signatures: 8,065 B of calldata, 231,489 execution; standard 360,169,
floor 516,160. The Keccak VM fits WHIR's `2^28`-word commitments up to about 470 signatures.

Where things are, what is proved and what remains: [`AGENTS.md`](AGENTS.md). The design documents:
[`docs/README.md`](docs/README.md). Code under `crates/` is MIT OR Apache-2.0, derived from leanVM.

## Build, test, measure

Build with `RUSTFLAGS="-C target-cpu=native"`. On a Zen 5 host (AMD EPYC 9355P) rustc 1.99.1's LLVM crashes (SIGILL
in `SelectionDAG::Combine`) on some test crates with `native` or `znver4`; there,
`-C target-cpu=x86-64-v4 -C target-feature=+gfni,+vpclmulqdq,+vaes,+pclmulqdq,+avx512vbmi,+aes,+bmi2` covers every
`target_feature` the code tests and measures the same.

```sh
cargo test --release --workspace                                         # every default test

# the membership proof
cargo test --release -p quotient -p evm                                  # incl. the contract == the Rust verifier
cargo bench -p quotient --bench membership                               # prover / verifier timings and sizes
cargo test --release -p evm -- --ignored --nocapture gas_report          # the contract's gas

# the leanVM line
cargo test --release -p leanvm_univariate -p leanvm_rec
cargo test --release -p leanvm_univariate --test keccak_vm -- --ignored --nocapture keccak_gas_report  # π1's gas
cargo test --release -p leanvm_univariate --test evm_vectors              # the committed real proofs replayed
cargo test --release -p leanvm_rec --test keccak_vm_rec -- --ignored --nocapture                       # π2's circuit, gas
PI2_VECTOR=keccak128_rec4 cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end
LEANVM_TRACE=<trace> PI1_VARIANT=rec4 cargo test --release -p leanvm_univariate --test prove_real -- --ignored \
  --nocapture keccak_prover_benchmark                                    # π1's prover on a real trace
LEANVM_TRACE=<trace> cargo test --release -p leanvm_rec --test pipeline -- --ignored --nocapture       # trace → π1 → π2, timed

# the EIP draft's two benchmarks (writes the trace once, ends with the EIP's table; docs/PERF_PROVER.md)
LEANVM_NUM_THREADS=8 BENCH_PIN="taskset -c 0-7" REPEAT=5 sh bench.sh
```

A trace is written by leanVM `9d50c92a3` itself, patched by `crates/leanvm/univariate/src/prover/dump_keccak/apply.sh`
([`docs/leanvm/univariate/PROVER.md`](docs/leanvm/univariate/PROVER.md)). The Lean builds:
[`formal/README.md`](formal/README.md).
