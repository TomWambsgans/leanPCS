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

An implementation of the idea above, on two Keccak workloads, with `MUL_FIELD` priced at 10 gas and, as the EIP draft
([`eip-draft_leanPCS.md`](eip-draft_leanPCS.md)) now has it, no precompile: a transaction declares its PCS claims in an
EIP-8288 dependency verification frame (each claim's Keccak-256), which the block proves and the contract reads with
EIP-8141's `FRAMEPARAM` and `FRAMEDATALOAD` (mocked on revm). The field is `K = GF(2^64)`,
`E = GF(2^192)`, the PCS leanVM's WHIR unchanged, Fiat–Shamir Keccak-256.

1. **A zero-knowledge proof of Keccak-256 Merkle membership** (`crates/membership`), verified by an EVM contract and
   proved correct in Lean 4 (`formal/`).
2. **leanVM proofs on the EVM by recursion** (`crates/leanvm`): a leaf aggregate of leanXMSS signatures by leanVM's
   Keccak VM, proved by a univariate PIOP (π1), whose verifier a second SNARK (π2) proves; the contract runs π2's
   verifier and checks every claim declared.

### Key figures: one ZK proof of a Merkle path

Statement `(y, root)`, witness `x` and a depth-32 path, Keccak-256: `y = H(x | 0x11..)`, path from `H(x | 0x22..)`
to `root` (details: [`AGENTS.md`](AGENTS.md#membership-what-is-proved)).

| | |
|---|---|
| Circuit | 34 Keccak-256 (χ gate on bits), the public words packed and pinned: 3,878,615 of 2^22 rows |
| Prover | 0.63 s, 6.6 GiB on an AMD EPYC 9355P (64 threads; main 0.91 s, 8.7 GiB there); two commitments, four openings (`docs/membership/PERF_GAS.md`). Not re-measured on the M4 Max (main: 2.8 s) |
| Calldata to the contract | 301 bytes (statement, 2 roots, 7 field elements, and the frame's index) |
| PCS claims | 4, in the EIP's encoding (129 bytes of frame) |
| Gas | 16,414 execution; **36,520** transaction under EIP-8141 (floor-bound, `pcs_gas` in the floor; without the base and per-frame costs). Main: 52,856 |
| Contract deployment | 1.24 M gas |
| Formal verification (Lean 4) | **of main's protocol (six claims), not yet of this branch's** (`docs/membership/PERF_GAS.md`, "What the Lean needs"): knowledge soundness (≈ 2^-61.4 at 2^64 queries) and completeness (failure < 2^-163) proved end to end, in the random-permutation model; zero knowledge proved assuming a zero-knowledge PCS opening and the revealed scalars' uniformity (tested, not proved); the contract proved to be the verifier (its bytecode by tests) |

### Key figures: one leanVM proof by recursion

A leaf aggregate of leanXMSS signatures by leanVM's Keccak VM (commit `9d50c92a3`: leanVM `42422001` with a `SHA3`
table, one Keccak-f step a row). π1 proves its execution, Flock proving the Keccak-f permutations; π2 proves π1-rec3's
verifier (π1 with Fiat–Shamir shaped for π2) minus its openings; the contract runs π2's verifier only. Measured on an
Apple M4 Max (16 cores), `RUSTFLAGS="-C target-cpu=native"`, with other jobs on the machine (load average 9–14);
the gas row as its first cell says.

| | **128 signatures (the reference)** | 400 signatures |
|---|---:|---:|
| VM execution | 154,148 cycles; tables of `2^14`–`2^16` rows, memory `2^20` | 473,348 cycles; `2^16`–`2^17` rows, memory `2^22` |
| π1 prover (π1-rec3) | in the pipeline below; before the PCS claims (version 3, layout words): 2.7 s cold, 3.65 s warm median of 3, 6.9 GB; EPYC 9355P 0.40 s warm | 4.7 s (main line), 14.4 GB, before the PCS claims |
| π2 prover | in the pipeline below; before the PCS claims: 4.4 s + 1.7 s openings (and 3.8 s witness), 9.8 GB; EPYC 9355P (π2v2) 0.196 s + 0.049 s openings at version 3 | 3.0 s + 0.9 s openings, before the PCS claims |
| trace → π1 → π2, per proof (`tests/pipeline.rs`) | on the PCS claims (one opening a claim, every opening on leanVM's ladder): **3.7 s** on this Mac (`bench.sh`, 2026-11-11, high power mode, median of 5; π1-rec3 with its openings 1.41 s, π2 0.95 s, π2's five openings 1.25 s), 1.4 s per circuit once, 14.3 GB. Before (π2's three stacks opened once each, every opening at version 3): 2.06 s on this Mac, **0.59 s** on an AMD EPYC 9355P (64 threads) | |
| Calldata to the contract | 1,101 B (61 zero) | 1,101 B (59 zero) |
| Gas (real proof, EIP-8141 frame transaction, EIP-7976 floor, no base or per-frame cost) | 32,794 execution; standard 49,678, floor **70,464**; with the frame of PCS claims (257 B) and `pcs_gas` 13,000 on both sides: **99,912** (the floor binds) | 33,740 execution; standard 50,648, floor 70,464; 99,912 with the frame and the PCS gas |
| PCS claims | 8: π1's 3, π2's 5 (`W`, the setup, `Q`'s identity, pushes and sum), each the EIP draft's | 8 |
| Formal verification (Lean 4) | the VM's statement and arithmetization, the Keccak-f block, π1's knowledge soundness (≤ 2^-64 at 2^64 queries) and completeness (failure < 2^-169), π1-rec3's recorded graph = its verifier; the recursion: knowledge soundness as an explicit reduction (π2's part ≤ 2^-64, plus π1-rec3 at Keccak-f[1600]), completeness (failure 2^-164 plus two premises at Keccak-f[1600]); the compiled circuit's checks evaluated, not proved | |

π1 alone as a contract (no recursion) costs 358,957 transaction gas at 128 signatures (8,020 B of calldata, 3 claims).
The Keccak VM fits WHIR's `2^28`-word commitments up to about 470 signatures. Details:
[`docs/leanvm/univariate/KECCAK.md`](docs/leanvm/univariate/KECCAK.md), [`AGENTS.md`](AGENTS.md).

## Repository map

```
crates/
  membership/quotient      the membership proof: circuit, prover, Rust verifier, hiding openings
  membership/evm           its verifier as EVM bytecode; revm with FIELD_MUL and EIP-8141 frames; gas
  evm_link                 compiles a recorded verifier graph and assembles it into one contract
  leanvm/statement         the Keccak VM's statement, Flock's verifier, the Keccak-256 chain, the EVM recorder
  leanvm/univariate        π1: the univariate PIOP's verifier, contract and prover (package leanvm_univariate)
  leanvm/rec               π2 and the recursion's contract (package leanvm_rec)
  leanvm/gf2_linear        GF(2)-linear maps of GF(2^192) for the prover
  vendor/leanvm-c445e3d5   leanVM's WHIR stack (primitives, fiat_shamir, pcs, parallel, verifier, bench)
  vendor/flock-42422001    leanVM's Flock prover on c445e3d5's primitives (package flock) and the Keccak-f block
docs/
  membership/HIDING.md     zero knowledge, assuming a ZK PCS
  membership/EIP_CLAIMS.md the membership protocol under the EIP's claims, and its cost
  leanvm/univariate/       π1: SPEC.md (the PIOP), SPEC-FLOCK.md, PROVER.md, KECCAK.md (the VM, gas, measurements)
  leanvm/rec/              π2: SPEC-REC.md (the recursion), PI2.md (π2's PIOP), SPEC-POINTS.md (the claims' points)
  leanvm/flock/KECCAK.md   the Keccak-f[1600] Flock block
formal/                    Lean 4 proofs (formal/README.md)
params/                    soundness and parameter calculators (Python)
```

A crate's directory is its package name without its group's prefix (`crates/leanvm/rec` is `leanvm_rec`,
`crates/vendor/flock-42422001` is `flock`); `crates/leanvm/statement` is `leanvm_statement`.

## Build, test, measure

```sh
cargo build --release --workspace --tests
cargo test --release --workspace                                         # every default test

# the membership proof
cargo bench -p quotient --bench membership                               # prover / verifier timings and sizes
cargo test --release -p evm -- --ignored --nocapture gas_report          # the contract's gas

# the leanVM line (build with RUSTFLAGS="-C target-cpu=native" for timings)
cargo test --release -p leanvm_univariate --test keccak_vm -- --ignored --nocapture keccak_gas_report  # π1's gas
cargo test --release -p leanvm_univariate --test evm_vectors              # the committed real proofs replayed
cargo test --release -p leanvm_rec --test keccak_vm_rec -- --ignored --nocapture                       # π2's circuit, gas
PI2_VECTOR=keccak128_rec3 cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end
LEANVM_TRACE=<trace> PI1_VARIANT=rec3 cargo test --release -p leanvm_univariate --test prove_real -- --ignored \
  --nocapture keccak_prover_benchmark                                    # π1's prover on a real trace
```

A trace is written by leanVM `9d50c92a3` itself, patched by `crates/leanvm/univariate/src/prover/dump_keccak/apply.sh`
([`docs/leanvm/univariate/KECCAK.md`](docs/leanvm/univariate/KECCAK.md), "The prover"). The Lean builds:
[`formal/README.md`](formal/README.md) and [`AGENTS.md`](AGENTS.md).

## Documents

- [`eip-draft_leanPCS.md`](eip-draft_leanPCS.md): the EIP draft (PCS claims as EIP-8288 dependencies, and `MULFIELD`) this repository backs.
- [`AGENTS.md`](AGENTS.md): notes for contributors (people and agents): what the implementation adds to the idea above,
  what is proved, tested and measured, what remains, provenance and licenses (MIT OR Apache-2.0), and conventions.
