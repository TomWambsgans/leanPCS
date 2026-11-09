# ZK-STARKS on Ethereum via PCS opening aggregations?

## Naive, simplified, idea:

- We agree on:
  - one base field K, one extension field E (example: K = F_2^64, E = F_2^192)
  - one PCS (example: WHIR in the LDR at rate 1/4)
- We add a new instruction to perform extension field multiplication in E: MUL_FIELD.
- Users can attach to each transaction a list of PCS claims.
- Each PCS claim contains:
  - header:
    - `num_variables` (1 byte)
    - commitment (32 bytes + 1 E field element) -> Merkle hash + OOD_answer (the OOD point being Fiat-Shamir derived from the Merkle hash)
    - opening point (`num_variables` E field elements)
    - value (1 E field element)
  - opening_proof (the PCS opening transcript, where Fiat-Shamir is seeded by the header)
- In the mempool, all the opening_proof 'disappear', and instead some STARK attests of their existence.
- Each Ethereum block contains a list of "headers", one STARK proves them all.
- We add a new magic precompile to the EVM: PCS_OPEN that takes as input header and attests that it is contained in the block's list of headers.

## Simplified example for R1CS: A.z ⊙ B.z = C.z in K

- A, B, and C, all of size 2^n x 2^n are interpreted as three multilinear polynomials in 2n variables in K
- All three have hardcoded commitment in the smart contract (storage or bytecode): comA, comB, comC.
- Prover commits to z (n variables): comZ (appears in calldata)
- It seeds some Fiat-Shamir state (not necessarily the same hash function as the one used in WHIR! (this requires future security proofs))
- Runs Spartan's sumchecks (1 zerocheck, 3 linchecks)
- In the end, you get 4 opening claims: pointZ, valueZ, pointA, valueA, ...
- Call PCS_OPEN(n, comZ, pointZ, valueZ), PCS_OPEN(n, comA, pointA, valueA), ...

## Forward compatibility

- The witness polynomial of the STARK is easy to change (commitment / opening algorithms are offchain).
- The difficult part is the polynomial representing the circuit whose commitment is hardcoded in a smart contract.

In 2031, when WHIR 2.0 is released, how to upgrade the PCS_OPEN precompile? -> An idea from Justin D:
- add a 'version' parameter to the arguments of the PCS_OPEN precompile. Initially it has version 1, and returns "invalid version" when called with version != 1.
- Hardfork -> version 2 is introduced. Version 1 remains available for a period of time (1 year), and is afterward deleted.
Every smart contract should:
- put the commitment of the circuit in storage (not bytecode)
- have a (trustless) function that lets any users calling it update the commitment (from v1 to v2). To prove that the new commitment is valid, we sample a random point (Fiat-Shamir) and require both PCS openings at version 1 and version 2 to agree on that point (Schwartz–Zippel).

TLDR: The PCS is relatively easy to upgrade, the only thing that cannot be upgraded is the (binary) field.

## Details

- We want a "ZKZK-friendly" PCS -> at a prover overhead of typically 2x or 4x, we can make it ZKZK without changing the verifier *at all* (WHIR is an example)
- I don't think we need to put the Fiat-Shamir states (before + after) in the header (but this requires security analysis)

## This repository

An implementation of the idea above, on two Keccak workloads, with the `PCS_OPEN` precompile mocked and `MUL_FIELD`
priced at 10 gas (the EIP draft: [`eip-draft_leanPCS.md`](eip-draft_leanPCS.md)). The field is `K = GF(2^64)`,
`E = GF(2^192)`, the PCS leanVM's WHIR unchanged, Fiat–Shamir Keccak-256.

1. **A zero-knowledge proof of Keccak-256 Merkle membership** (`crates/membership`), verified by an EVM contract and
   proved correct in Lean 4 (`formal/`).
2. **leanVM proofs on the EVM by recursion** (`crates/leanvm`): a leaf aggregate of leanXMSS signatures by leanVM's
   Keccak VM, proved by a univariate PIOP (π1), whose verifier a second SNARK (π2) proves; the contract runs π2's
   verifier and hands every claim to `PCS_OPEN`.

### Key figures: one ZK proof of a Merkle path

Statement `(y, root)`, witness `x` and a depth-32 path, Keccak-256: `y = H(x | 0x11..)`, path from `H(x | 0x22..)`
to `root` (details: [`AGENTS.md`](AGENTS.md#membership-what-is-proved)).

| | |
|---|---|
| Circuit | 34 Keccak-256 (χ gate on bits): 3,878,612 of 2^22 rows |
| Prover | 3.6 s, 6.2 GiB peak on h1 (Ryzen 7 PRO 8700GE, 8 cores, AVX-512) at load 9–14, where the prover before the x86 work took 8.4 s; 2.3 s on h2 (Core Ultra 7 265, 20 cores, AVX2) at load 10, 5.0 s before; 2.2 s on an M4 Max (16 cores) before the x86 work |
| Calldata to the contract | 252 bytes (2 roots + 5 field elements + statement) |
| PCS claims | 4, in 3 `PCS_OPEN` calls |
| Gas, `PCS_OPEN` free | 14,289 execution; 18,309 transaction (without the 21,000 base) |
| Contract deployment | 1.43 M gas |
| Formal verification (Lean 4) | knowledge soundness (≈ 2^-62 at 2^64 queries), completeness (failure < 2^-162) and zero knowledge (≈ 2^-113) proved end to end, in the random-permutation model; the contract proved to be the verifier (its bytecode by tests) |

### Key figures: one leanVM proof by recursion

A leaf aggregate of leanXMSS signatures by leanVM's Keccak VM (commit `9d50c92a3`: leanVM `42422001` with a `SHA3`
table, one Keccak-f step a row). π1 proves its execution, Flock proving the Keccak-f permutations; π2 proves π1-rec3's
verifier (π1 with Fiat–Shamir shaped for π2) minus its openings; the contract runs π2's verifier only. Measured on an
Apple M4 Max (16 cores), `RUSTFLAGS="-C target-cpu=native"`, with other jobs on the machine (load average 9–14);
transaction gas under EIP-7623 at a claim price of 0, without the 21,000 base.

| | **128 signatures (the reference)** | 400 signatures |
|---|---:|---:|
| VM execution | 154,148 cycles; tables of `2^14`–`2^16` rows, memory `2^20` | 473,348 cycles; `2^16`–`2^17` rows, memory `2^22` |
| π1 prover (π1-rec3) | 2.7 s cold, 3.65 s warm median of 3; 6.9 GB | 4.7 s (main line), 14.4 GB |
| π2 prover | 4.4 s + 1.7 s openings (and 3.8 s witness); 9.8 GB | 3.0 s + 0.9 s openings (and 2.9 s witness); 9.8 GB |
| trace → π1 → π2, per proof (`tests/pipeline.rs`) | **4.1 s** (Mac, load 2–7; π1 with π2's witness 1.87, π2 1.58 + 0.70 openings); 8.9 s on h2, 11.5–12.1 s on h1 under load; per circuit, once, 0.9 s; 12.5 GB | |
| Calldata to the contract | 980 B | 980 B |
| Gas (real proof) | 28,325 execution; **43,213** transaction | 29,105 execution; 44,041 transaction |
| PCS claims | 7, in 6 `PCS_OPEN` calls | 7, in 6 calls |
| Formal verification (Lean 4) | the VM's statement and arithmetization, the Keccak-f block, π1's knowledge soundness (≤ 2^-64 at 2^64 queries) and completeness (failure < 2^-169), π1-rec3's recorded graph = its verifier; the recursion: knowledge soundness as an explicit reduction (π2's part ≤ 2^-64, plus π1-rec3 at Keccak-f[1600]), completeness (failure 2^-164 plus two premises at Keccak-f[1600]); the compiled circuit's checks evaluated, not proved | |

π1 alone as a contract (no recursion) costs 358,957 transaction gas at 128 signatures (8,020 B of calldata, 3 claims).
The Keccak VM fits WHIR's `2^28`-word commitments up to about 470 signatures. Details:
[`docs/leanvm/univariate/KECCAK.md`](docs/leanvm/univariate/KECCAK.md), [`AGENTS.md`](AGENTS.md).

## Repository map

```
crates/
  membership/quotient      the membership proof: circuit, prover, Rust verifier, hiding openings
  membership/evm           its verifier as EVM bytecode; revm with FIELD_MUL and a mock PCS_OPEN; gas
  evm_link                 compiles a recorded verifier graph, assembles it, links it into EIP-170 contracts
  leanvm/statement         the Keccak VM's statement, Flock's verifier, the Keccak-256 chain, the EVM recorder
  leanvm/univariate        π1: the univariate PIOP's verifier, contract and prover (package leanvm_univariate)
  leanvm/rec               π2 and the recursion's contract (package leanvm_rec)
  leanvm/gf2_linear        GF(2)-linear maps of GF(2^192) for the prover
  vendor/leanvm-c445e3d5   leanVM's WHIR stack (primitives, fiat_shamir, pcs, parallel, verifier, bench)
  vendor/flock-42422001    leanVM's Flock prover on c445e3d5's primitives (package flock) and the Keccak-f block
docs/
  membership/HIDING.md     the hiding layouts
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

- [`eip-draft_leanPCS.md`](eip-draft_leanPCS.md): the EIP draft (`PCS_OPEN` and `MULFIELD`) this repository backs.
- [`AGENTS.md`](AGENTS.md): notes for contributors (people and agents): what the implementation adds to the idea above,
  what is proved, tested and measured, what remains, provenance and licenses (MIT OR Apache-2.0), and conventions.
