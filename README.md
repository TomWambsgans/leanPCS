# ZK-STARKS on Ethereum via PCS opening aggregations?

## Naive, simplified, idea:

- We agree on:
  - one base field K, one extension field E (example: K = F_2^64, E = F_2^192)
  - one PCS (example: WHIR in the LDR at rate 1/2)
- We add a new instruction to perform extension field multiplication in E: MULFIELD.
- Users can attach to each transaction a list of PCS claims.
- Each PCS claim contains:
  - header:
    - commitment: a Merkle root, and a layout word (the PCS version, `num_variables`, the coefficients committed)
    - every opening point on that commitment (`num_variables` E field elements each), and its value (1 E field
      element): with no OOD answer, a root binds only a short list of polynomials, so claims on one commitment go
      together, proved by one opening
  - opening_proof (the PCS opening transcript, where Fiat-Shamir is seeded by the header)
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
- each header carries a version (in its layout word). Initially one version is valid, and a block cannot prove a
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
| Circuit | 34 Keccak-256 (χ gate on bits): 3,878,612 of 2^22 rows |
| Prover | 3.6 s, 6.2 GiB peak on h1 (Ryzen 7 PRO 8700GE, 8 cores, AVX-512) at load 9–14, where the prover before the x86 work took 8.4 s; 2.3 s on h2 (Core Ultra 7 265, 20 cores, AVX2) at load 10, 5.0 s before; 2.2 s on an M4 Max (16 cores) before the x86 work |
| Calldata to the contract | 253 bytes (2 roots + 5 field elements + statement, and the frame's index) |
| PCS claims | 4, declared as 3 (97 bytes of frame) |
| Gas | 14,831 execution; 18,855 transaction (without the 21,000 base); 28,407 with the frame and the claims' 8,000 intrinsic gas |
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
| π1 prover (π1-rec3) | 2.7 s cold, 3.65 s warm median of 3; 6.9 GB. EPYC 9355P: 0.40 s warm (0.94 s before), 7.2 GB; with opening version 3 its openings 0.064 → 0.033 s, 6.2 GB | 4.7 s (main line), 14.4 GB |
| π2 prover | 4.4 s + 1.7 s openings (and 3.8 s witness); 9.8 GB. EPYC 9355P (π2v2): 0.196 s + 0.104 s openings (and 7 ms witness), 9.9 GB, the openings 0.049 s with opening version 3; π2v1 before the work 0.54 + 0.16 s (and 0.61 s witness) | 3.0 s + 0.9 s openings (and 2.9 s witness); 9.8 GB |
| trace → π1 → π2, per proof (`tests/pipeline.rs`) | **0.59 s** on an AMD EPYC 9355P (64 threads, 2026-11-09, load 14–21; π1 with its openings 0.34, π2 0.195 + 0.051 openings, π2's witness 7 ms meanwhile), 3.7× its 2.16 s before; per circuit, once, 1.7 s; 12.6 GB. With opening version 3 (WHIR's deeper levels at rates 1/4, 1/8, …): about 80 ms less a proof (π1's openings −30 ms, π2's 0.108 → 0.054 s), best passes 0.68 → 0.59 s, 12.0 GB. The Mac: 4.1 s before | |
| Calldata to the contract | 1,005 B | 1,005 B |
| Gas (real proof) | 28,459 execution; **43,819** transaction (27,641 and 42,997 with `PCS_OPEN`); 57,883 with the frame (193 B) and the claims' 11,000 intrinsic gas | 29,257 execution; 44,593 transaction (28,421 and 43,753 with `PCS_OPEN`); 58,669 with the frame and the claims' intrinsic gas |
| PCS claims | 7, declared as 6 | 7, as 6 |
| Formal verification (Lean 4) | the VM's statement and arithmetization, the Keccak-f block, π1's knowledge soundness (≤ 2^-64 at 2^64 queries) and completeness (failure < 2^-169), π1-rec3's recorded graph = its verifier; the recursion: knowledge soundness as an explicit reduction (π2's part ≤ 2^-64, plus π1-rec3 at Keccak-f[1600]), completeness (failure 2^-164 plus two premises at Keccak-f[1600]); the compiled circuit's checks evaluated, not proved | |

π1 alone as a contract (no recursion) costs 358,957 transaction gas at 128 signatures (8,020 B of calldata, 3 claims).
The Keccak VM fits WHIR's `2^28`-word commitments up to about 470 signatures. Details:
[`docs/leanvm/univariate/KECCAK.md`](docs/leanvm/univariate/KECCAK.md), [`AGENTS.md`](AGENTS.md).

## Repository map

```
crates/
  membership/quotient      the membership proof: circuit, prover, Rust verifier, hiding openings
  membership/evm           its verifier as EVM bytecode; revm with FIELD_MUL and EIP-8141 frames; gas
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

- [`eip-draft_leanPCS.md`](eip-draft_leanPCS.md): the EIP draft (PCS claims as EIP-8288 dependencies, and `MULFIELD`) this repository backs.
- [`AGENTS.md`](AGENTS.md): notes for contributors (people and agents): what the implementation adds to the idea above,
  what is proved, tested and measured, what remains, provenance and licenses (MIT OR Apache-2.0), and conventions.
