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

1. **A zero-knowledge proof of Keccak-256 Merkle membership** (`crates/membership`), verified by an EVM contract; the
   Lean 4 proofs (`formal/`) are of its previous protocol (commit `f96a7938`, six claims), not yet of the current one.
2. **leanVM proofs on the EVM by recursion** (`crates/leanvm`): a leaf aggregate of leanXMSS signatures by leanVM's
   Keccak VM, proved by a univariate PIOP (π1), whose verifier a second SNARK (π2) proves; the contract runs π2's
   verifier and checks every claim declared.

### Key figures: one ZK proof of a Merkle path

Statement `(y, root)`, witness `x` and a depth-32 path, Keccak-256: `y = H(x | 0x11..)`, path from `H(x | 0x22..)`
to `root` (details: [`AGENTS.md`](AGENTS.md#membership-what-is-proved)).

| | |
|---|---|
| Circuit | 34 Keccak-256 (one gate `V = Y + C + X·C` on bits), the public words packed and pinned: 3,878,615 of 2^22 rows |
| Prover | **1.02 s**, 6.0 GiB on 8 threads of an AMD EPYC 9355P (median of 5, 2026-11-11); two commitments, three openings (`docs/membership/PERF_GAS2.md`). The previous protocol (`f96a7938`, six openings): 2.29 s there, 2.8 s on an M4 Max |
| Calldata to the contract | 273 bytes (statement, 2 roots, 6 field elements, and the frame's index; no selector) |
| PCS claims | 3, in the EIP's encoding (97 bytes of frame) |
| Gas | 15,753 execution; **31,680** transaction under EIP-8141 (floor-bound, `pcs_gas` in the floor; without the base and per-frame costs). Previously 36,520, and 52,856 before that |
| Contract deployment | 1.15 M gas |
| Formal verification (Lean 4) | **of the previous protocol (commit `f96a7938`, six claims), not yet of the current one** (`docs/membership/PERF_GAS.md` and `PERF_GAS2.md`, "What the Lean needs"): knowledge soundness (≈ 2^-61.4 at 2^64 queries) and completeness (failure < 2^-163) proved end to end, in the random-permutation model; zero knowledge proved assuming a zero-knowledge PCS opening and the revealed scalars' uniformity (tested, not proved); the contract proved to be the verifier (its bytecode by tests) |

### Key figures: one leanVM proof by recursion

A leaf aggregate of leanXMSS signatures by leanVM's Keccak VM (commit `9d50c92a3`: leanVM `42422001` with a `SHA3`
table, one Keccak-f step a row). π1 proves its execution, Flock proving the Keccak-f permutations; π2 proves π1-rec4's
verifier (π1 with Fiat–Shamir shaped for π2) minus its openings; the contract runs π2's verifier only. The pipeline
row is measured on 8 threads of an AMD EPYC 9355P; the rows marked "before the PCS claims" on an Apple M4 Max (16
cores, load average 9–14) unless they say otherwise; the gas row as its first cell says.

| | **128 signatures (the reference)** | 400 signatures |
|---|---:|---:|
| VM execution | 154,148 cycles; tables of `2^14`–`2^16` rows, memory `2^20` | 473,348 cycles; `2^16`–`2^17` rows, memory `2^22` |
| π1 prover (π1-rec4) | in the pipeline below; before the PCS claims (π1-rec3, version 3, layout words): 2.7 s cold, 3.65 s warm median of 3, 6.9 GB; EPYC 9355P 0.40 s warm | 4.7 s (main line), 14.4 GB, before the PCS claims |
| π2 prover | in the pipeline below; before the PCS claims: 4.4 s + 1.7 s openings (and 3.8 s witness), 9.8 GB; EPYC 9355P (π2v2) 0.196 s + 0.049 s openings at version 3 | 3.0 s + 0.9 s openings, before the PCS claims |
| trace → π1 → π2, per proof (`tests/pipeline.rs`) | on the PCS claims (one opening a claim, every opening on leanVM's ladder): **2.62 s** on 8 threads of an AMD EPYC 9355P (2026-11-11, median of 5 runs of 5; π1-rec4 0.86 s and its openings 0.18 s, π2 0.79 s, π2's five openings 0.79 s), 15.1 GB; 3.7 s on an M4 Max at `f96a7938`. Before (π2's three stacks opened once each, every opening at version 3): 2.06 s on the M4 Max, **0.59 s** on an AMD EPYC 9355P (64 threads) | |
| Calldata to the contract | 577 B (4 zero): π1's three claims hashed in π2's circuit (π1-rec4, `docs/leanvm/rec/PERF_GAS2.md`), no selector | 577 B |
| Gas (real proof, EIP-8141 frame transaction, EIP-7976 floor, no base or per-frame cost) | 31,524 execution; standard 40,708, floor 36,928; with the frame of PCS claims (257 B) and `pcs_gas` 13,000 on both sides: **66,376** (the floor binds; previously 89,672, and 99,912 before that) | 35,761 execution; 66,376 with the frame and the PCS gas |
| PCS claims | 8: π1's 3, π2's 5 (`W`, the setup, `Q`'s identity, pushes and sum), each the EIP draft's | 8 |
| Formal verification (Lean 4) | the VM's statement and arithmetization, the Keccak-f block, π1's knowledge soundness (≤ 2^-64 at 2^64 queries) and completeness (failure < 2^-169), π1-rec3's recorded graph = its verifier; the recursion (π2 as of `f96a7938`, before `C1`'s claim was hashed in its circuit: not yet ported): knowledge soundness as an explicit reduction (π2's part ≤ 2^-64, plus π1-rec3 at Keccak-f[1600]), completeness (failure 2^-164 plus two premises at Keccak-f[1600]); the compiled circuit's checks evaluated, not proved | |

π1 alone as a contract (no recursion, the main line) at 128 signatures: 8,069 B of calldata, 231,511 execution, 3 claims;
as an EIP-8141 frame transaction (EIP-7976's floor) standard 360,255, floor 516,416, without its frame of claims
(`keccak_gas_report`).
The Keccak VM fits WHIR's `2^28`-word commitments up to about 470 signatures. Details:
[`docs/leanvm/univariate/KECCAK.md`](docs/leanvm/univariate/KECCAK.md), [`AGENTS.md`](AGENTS.md).

## Repository map

```
crates/
  membership/quotient      the membership proof: circuit, prover, Rust verifier, its PCS claims and openings
  membership/evm           its verifier as EVM bytecode; revm with FIELD_MUL and EIP-8141 frames; gas
  evm_link                 compiles a recorded verifier graph and assembles it into one contract
  leanvm/statement         the Keccak VM's statement, Flock's verifier, the Keccak-256 chain, the EVM recorder
  leanvm/univariate        π1: the univariate PIOP's verifier, contract and prover (package leanvm_univariate)
  leanvm/rec               π2 and the recursion's contract (package leanvm_rec)
  leanvm/gf2_linear        GF(2)-linear maps of GF(2^192) for the prover
  vendor/leanvm-c445e3d5   leanVM's WHIR stack (primitives, fiat_shamir, pcs, parallel, verifier, bench)
  vendor/flock-42422001    leanVM's Flock prover on c445e3d5's primitives (package flock) and the Keccak-f block
docs/
  membership/PERF_GAS2.md  the membership protocol as deployed (three claims), on PERF_GAS.md's; what the Lean needs
  membership/HIDING.md     zero knowledge, assuming a ZK PCS
  membership/EIP_CLAIMS.md the protocol of f96a7938 (six claims, the one formal/ proves): a record
  leanvm/univariate/       π1: SPEC.md (the PIOP), SPEC-FLOCK.md, PROVER.md, KECCAK.md (the VM, gas, measurements)
  leanvm/rec/              π2: SPEC-REC.md (the recursion), PI2.md (π2's PIOP), SPEC-POINTS.md (the claims' points),
                           PERF_GAS2.md (π1-rec4, π1's claims hashed in π2's circuit: the deployed recursion)
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
PI2_VECTOR=keccak128_rec4 cargo test --release -p leanvm_rec --test pi2_real -- --ignored --nocapture real_end_to_end
LEANVM_TRACE=<trace> PI1_VARIANT=rec4 cargo test --release -p leanvm_univariate --test prove_real -- --ignored \
  --nocapture keccak_prover_benchmark                                    # π1's prover on a real trace
```

A trace is written by leanVM `9d50c92a3` itself, patched by `crates/leanvm/univariate/src/prover/dump_keccak/apply.sh`
([`docs/leanvm/univariate/KECCAK.md`](docs/leanvm/univariate/KECCAK.md), "The prover"). The Lean builds:
[`formal/README.md`](formal/README.md) and [`AGENTS.md`](AGENTS.md).

## Documents

- [`eip-draft_leanPCS.md`](eip-draft_leanPCS.md): the EIP draft (PCS claims as EIP-8288 dependencies, and `MULFIELD`) this repository backs.
- [`AGENTS.md`](AGENTS.md): notes for contributors (people and agents): what the implementation adds to the idea above,
  what is proved, tested and measured, what remains, provenance and licenses (MIT OR Apache-2.0), and conventions.
