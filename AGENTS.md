# AGENTS.md

Notes for contributors (people and agents): what the implementation adds to the design note in
[`README.md`](README.md), where things are, what is proved, tested and measured, what remains, provenance and
licensing, and the conventions. The build and test commands are in [`README.md`](README.md); the design documents,
in [`docs/README.md`](docs/README.md); superseded protocols and figures, in [`docs/HISTORY.md`](docs/HISTORY.md).

## Status (2026-11-11)

- **The Rust** is the deployed system: the membership protocol of [`docs/membership/PROTOCOL.md`](docs/membership/PROTOCOL.md)
  (three claims on two commitments and the circuit's) and the recursion of
  [`docs/leanvm/rec/SPEC-REC.md`](docs/leanvm/rec/SPEC-REC.md) (π2v4 over π1-rec4, π1's three claims hashed in π2's
  circuit, the copy sum forced by `Q`'s layout). Each change was reviewed adversarially (soundness, zero knowledge, the contract against the verifier, the
  prover's unsafe code and determinism) before it was merged. The provers' speedups
  ([`docs/PERF_PROVER.md`](docs/PERF_PROVER.md)) change no proof.
- **The Lean lags the Rust.** `formal/` proves the protocols of commit `f96a7938` (membership: six claims on four
  commitments; π2 over π1-rec3, its three claims encoded by the contract). What the port needs:
  [`docs/LEAN_PORT.md`](docs/LEAN_PORT.md). Until then, do not regenerate the Lean-facing files (below).

## What the implementation adds to the design note

- **The out-of-domain answer binds a root to one table**, as the EIP draft has it ([`docs/PCS_CLAIM.md`](docs/PCS_CLAIM.md)).
  leanVM's WHIR takes no out-of-domain sample at its first commitment, so a root alone binds only to a list of tables
  (the level-0 lists leanerVM certifies: 87,315 at `2^15` words down to 3,564 at `2^28`). The commitment's answer
  `ood = f(z)`, `z` derived from the root by Keccak-256, singles one out except with probability
  `Q · C(L, 2) · n / 2^192` (at least 156 bits as `Q/ε`; `WhirBridge.Pcs.ood_binding_rom`), so claims on one
  commitment are opened, aggregated and proven separately, one opening a claim.
- **The opening's Fiat–Shamir seed** is the claim alone: leanVM's transcript started from `keccak256(PCS_claim)` (the
  dependency's payload) and a zero public digest, the root as the proof's first two scalars, which the verifier checks
  (`pcs_claim::verify`), the form `formal/WhirBridge` proves sound (`WhirBridge.Pcs.pcs_sound`).
- **The Fiat–Shamir states need not be in the header**, given the two points above.
- **The forward-compatibility upgrade by one Schwartz–Zippel point** needs the new commitment to bind one table: the
  out-of-domain answer gives it.
- **ZK assumes a zero-knowledge PCS** (ZK-WHIR), as the EIP does; the reference openings are leanVM's WHIR, not yet
  ZK-WHIR. The membership protocol makes its own public scalars simulatable: random rows of free cells and a blinding
  of `h` make the out-of-domain answers and the `a_j` uniform, both groups affine
  ([`docs/membership/PROTOCOL.md`](docs/membership/PROTOCOL.md), "Zero knowledge": rank tests).

## Where things are (`crates/`)

Both lines use Keccak-256 Fiat–Shamir, and both contracts check that their transaction declares their claims, as the
EIP draft has it: a claim's Keccak-256 is a payload of the transaction's frame of PCS claims (an EIP-8288 dependency
verification frame of scheme `PCS_SCHEME`), which the contract reads with EIP-8141's `FRAMEPARAM` and
`FRAMEDATALOAD`, the frame's index being the last byte of calldata (`evm_link::declared_claims`). Every commitment and
opening is the EIP draft's PCS claim (`crates/pcs_claim`: a root and an out-of-domain answer, one point per claim, one
opening per claim, PCS version 1).

**Zero-knowledge Merkle membership** (depth 32, Keccak-256), reduced to three PCS claims by six field elements, as in
leanVM's `flock::quotient` but on a circuit of one χ gate on bits (3,878,615 of 2^22 rows, the public values packed
into eight pinned `K`-words); design: [`docs/membership/PROTOCOL.md`](docs/membership/PROTOCOL.md).

- `crates/membership/quotient`: circuit, prover, Rust verifier (`protocol::reduce`) and openings (`opening`): two
  commitments with out-of-domain answers (the witness `W`; the quotient table `T`: the quotient `q` and `x h`) and
  three one-point claims. The prover's transforms are `ntt`'s (AVX-512, AVX2 or NEON lanes); the `Index` keeps σ's
  values on the quotient's coset (256 MiB at 2^22 rows), which every proof reads.
- `crates/membership/evm`: the verifier as EVM bytecode, run on revm with `FIELD_MUL` (10 gas), EIP-8141's
  `FRAMEPARAM` and `FRAMEDATALOAD`, and a mock frame of PCS claims (`PcsFrame`). ABI and deployment in `quotient.rs`:
  no selector, 272 bytes of packed arguments, then the frame's index; the circuit's commitment (root and out-of-domain
  answer) is a constructor argument kept in storage slots 0 and 1, which a fixed owner may change
  (`setIndexCommitment`). It fails closed: the named frame must be a dependency verification frame whose first byte is
  `PCS_SCHEME`, and its payloads `0 .. 2` the claims' hashes, in order; calls with value, other calldata lengths and
  degenerate proofs revert.

**leanVM proofs on the EVM, by recursion**: a leaf aggregate of leanXMSS signatures by leanVM's Keccak VM (commit
`9d50c92a3`: leanVM `42422001` with a `SHA3` table, one Keccak-f step a row).

- `crates/leanvm/univariate` (π1): a univariate PIOP for the Keccak VM's statement (two proof commitments and one setup
  commitment, the bus as a grand product in a committed heap, every identity checked at one point, Flock on the
  Keccak-f block, one point claim per commitment), its verifier (`verifier::reduce`, generic over the scalar: on `E` the
  Rust verifier, on the recorder's symbol the graph `contract` compiles), its contract and its prover (`prover/`).
  Variants: `KECCAK_MAIN`; `KECCAK_REC3` (π1-rec3, the inner proof the Lean states); `KECCAK_REC4` (π1-rec4, the
  deployed inner proof: the challenges no message separates drawn from one Keccak-f, 106 Keccak-f in its transcript;
  no contract of its own). Design: [`docs/leanvm/univariate/`](docs/leanvm/univariate/) (`SPEC.md`, `FLOCK.md`,
  `KECCAK.md`, `PROVER.md`).
- `crates/leanvm/rec` (π2): a univariate SNARK of π1-rec4's verifier (`leanvm_rec::PI1`) minus its openings: the
  recorded verifier compiled into π2's circuit (`circuit`, D16v, `2^24` positions; π1's three claims hashed in it; the
  witness replayed per proof from a plan made once per circuit, `circuit::plan`), π2's PIOP (π2v4, transcript
  `leanvm-rec-pi2v4`) and its contract (`pi2`), which runs π2's verifier and checks π1's three and π2's four claims
  declared. Design: [`SPEC-REC.md`](docs/leanvm/rec/SPEC-REC.md), [`PI2.md`](docs/leanvm/rec/PI2.md).
- `crates/leanvm/statement` (`leanvm_statement`): the VM's tables, flushes and constraints, Flock's verifier and the
  Keccak-f block's structured terminal, the Keccak-256 chain, the EVM recorder, code and machine, the workloads.
- `crates/leanvm/gf2_linear`: the prover's GF(2)-linear maps.
- `crates/vendor/flock-42422001` (`flock`): leanVM `42422001`'s Flock prover on `c445e3d5`'s `primitives`, `parallel`
  and `pcs`, with the Keccak-f block (`src/keccak.rs`) and the univariate-skip zerocheck (`src/zerocheck/skip.rs`).
- **The reference workload is 128 signatures**: `leanvm_rec::REFERENCE` = `leanvm_statement::shapes::reference()`
  (memory `2^20`, bytecode `2^18`), `contract::SetupRoots::REFERENCE`, and the real π1-rec4 proof
  `crates/leanvm/univariate/tests/vectors/keccak128_rec4.txt` (π1-rec3's: `keccak128_rec3.txt`).

**Shared.** `crates/pcs_claim` (the EIP's claim, its opening and EVM check); `crates/evm_link` (the compilation and
assembly into one contract, the claim's wire format, and with the feature `machine` the EVM the contracts run on in
tests: the membership contract, 4,866 B, and π2's, 14.5 KB, fit EIP-170; π1's own, about 86 KB,
does not and is built only to test it against its Rust verifier); `crates/vendor/leanvm-c445e3d5` (leanVM's
`primitives`, `fiat_shamir`, `pcs`, `parallel`, `verifier`, `bench`); `params/` (WHIR's, π1's and π2's soundness bits);
`formal/` (the Lean 4 proofs, [`formal/README.md`](formal/README.md)).

## Numbers

The single home of the current figures; how they are measured: [`docs/PERF_PROVER.md`](docs/PERF_PROVER.md). Provers:
medians of five interleaved runs of `bench.sh` on 8 physical cores of an idle AMD EPYC 9355P (2026-11-11). Gas is
transaction gas without the 21,000 base (EIP-7623) and without the frame's per-frame costs; the EIP draft's PCS gas is
5,000 a transaction with claims and 1,000 a claim, in the floor.

| | ZK Merkle membership | leanVM by recursion (128 signatures) |
|---|---|---|
| Prover | **1.01 s** (reduction 0.66 s, openings 0.34 s), 6.0 GiB | **2.29 s** trace → π1-rec4 → π2 and openings (π1-rec4 0.86 s, its openings 0.18 s, π2 0.74 s, π2's four openings 0.51 s), 15.6 GB |
| The EIP's prover column (+ 0.1 s a claim) | 1.3 s | 3.0 s |
| Calldata | 273 B | **577 B** (4 zero) |
| Gas without the frame | 15,753 execution; the PIOP's frame alone 20,097 (its standard binding) | 31,212 execution; standard 40,396 (the EIP's PIOP column), floor 36,928 |
| Claims | 3 | 7 (π1's 3, π2's 4) |
| With the frame (1 + 32 B a claim) and the PCS gas | **31,680** (97 B, 8,000; floor-bound: 64 · (273 + 97) + 8,000; standard 29,649) | **63,328** (225 B, `pcs_gas` 12,000 on both sides; the floor binds, standard 55,996) |
| Deployment | 4,866 B of code, 1,149,640 gas | one contract, 14.3 KB |

- Membership verifier: reduction < 1 ms, openings 6 ms (278 / 276 / 336 KiB: the witness's, the circuit's and `T`'s;
  `cargo bench -p quotient --bench membership`, 2026-11-11).
- leanVM at 400 signatures (the real proof): 577 B, 35,452 execution; standard 44,624, floor 36,928; 63,328 with the
  frame and the PCS gas (`tests/pi2_real.rs`, `real_end_to_end`). π2's circuit fills 97.8% of `2^24` at 128 signatures
  and 99.4% at 400; past it, fewer of π1's claims are hashed, the last dropped first, down to all encoded by the
  contract ([`SPEC-REC.md`](docs/leanvm/rec/SPEC-REC.md)).
- π1 alone as a contract (the main line, 128 signatures): 8,065 B calldata, 231,489 execution, 3 claims; standard
  360,169, floor 516,160 (`keccak_gas_report`).
- Capacity: about 470 signatures ([`docs/leanvm/univariate/KECCAK.md`](docs/leanvm/univariate/KECCAK.md)).
- Soundness at 128 signatures, as `Q/ε` with the openings charged at WhirBridge's `269 · 2^-137` a query
  (`params/`): membership about 126.4 bits; π1 128.93 (main line), π1-rec4 128.79, π2 128.93, the recursion 127.86
  (WHIR charged twice: [`SPEC-REC.md`](docs/leanvm/rec/SPEC-REC.md) §5).

## What is proved and tested

- **Proved in Lean** (sorry-free, on `propext`, `Classical.choice` and `Quot.sound` only; of `f96a7938`'s protocols;
  [`formal/README.md`](formal/README.md) has the theorems and their hypotheses): membership's knowledge soundness
  (about 2^-61.4 at 2^64 queries) and completeness with no hypotheses, its zero knowledge under `PcsZeroKnowledge` and
  `RevealedUniform`, its contract = its verifier; the Keccak VM's statement, the Keccak-f block, π1's knowledge
  soundness (≤ 2^-64 at 2^64 queries) and completeness (< 2^-169, given a program IV of 32 to 2^16 bytes), π1-rec3's
  recorded graph = its verifier, the recursion's knowledge soundness as an explicit reduction and its completeness under
  two premises at Keccak-f[1600]. The compiled π2 circuit's checks are evaluated in Lean, not proved. Of π1-rec4
  (branch `lean/pi1-rec4`): its verifier transcribed (`UniKeccak.reduceWithK4`, differential-tested on the real
  π1-rec4 proofs), its recorded graph = its verifier (`RecGraphKeccak.Sim.pi1GraphIsVerifierK4`, no hypothesis); its
  knowledge soundness and completeness are stated, not proved.
- **Argued and tested (current code)**: the current membership protocol's soundness and zero knowledge
  ([`PROTOCOL.md`](docs/membership/PROTOCOL.md); `protocol::tests`, the rank tests in `hiding`); each contract equals
  its Rust verifier; the real π1 proofs at 32, 128 and 400 signatures (committed vectors) are accepted with their frame
  declaring exactly the claims their openings prove; π2's proof of the real 128-signature π1-rec4 proof is accepted,
  its openings verify, and every calldata byte but the frame's index flipped at bits 0 and 7 and the frame's attacks
  are rejected (`pi2_real.rs`, `frame_and_calldata_attacks`). π1-rec4 has no contract; its vectors are checked against
  the Rust verifier.
- **Trusted**: the deployed Rust provers, for completeness; Keccak-f[1600] as a random permutation; the bytecode
  computes the recorded graph (by tests).

## Security notes

- **Claims on one commitment may be proven separately**: the out-of-domain answer binds the root, so the block's
  aggregation needs no grouping of declared claims.
- **WHIR's parameters.** The code's proximity-gap accounting omits a factor `2^(ℓ-1)` that leanerVM's theorems carry;
  leanerVM's certified parameters account for it.
- **Hiding.** The reference openings (leanVM's WHIR) are not zero knowledge: the membership proof's zero knowledge
  assumes the EIP's ZK-WHIR.
- **Integrating the membership contract**: deploy with no owner; a proof carries no application context; never
  `DELEGATECALL` it ([`PROTOCOL.md`](docs/membership/PROTOCOL.md), "Integration").
- **The prover's low-memory paths** make the dense prover's commitments and proofs (differential tests in
  `crates/vendor/leanvm-c445e3d5/pcs` and `crates/membership/quotient`); the in-place NTT encodes are free of the
  aliasing bug Miri flags in leanVM's.

## Remaining

- The Lean port to the deployed protocols ([`docs/LEAN_PORT.md`](docs/LEAN_PORT.md)).
- Membership: zero knowledge with a pre-proof phase (the distinguisher's queries before the proof);
  simulation-extractability; `RevealedUniform` proved rather than tested (in the current protocol it reduces to two
  rank conditions).
- leanVM in Lean: the model gap (π2's circuit computes π1's Fiat–Shamir at the real Keccak-f[1600], π1's theorems are
  in the random-permutation model); the compiler's IV uniformity (`RecCompose.PatchChecked`); closed bounds at other
  shapes than the reference ([`formal/README.md`](formal/README.md), "Remaining").
- leanVM: capacity beyond about 470 signatures; a lower-degree `SHA3` leaf by committing its seven address products
  `fp·o` in `C1` (54.5 → 28.5 pieces, about 11 ms a proof: a π1 format change not yet worth it).

## Provenance and licensing

The Rust code under `crates/` is derived from [leanVM](https://github.com/leanEthereum/leanVM) (Copyright (c) 2026
leanEthereum) and is licensed, like leanVM, under the MIT license ([`LICENSE-MIT`](LICENSE-MIT)) or the Apache License
2.0 ([`LICENSE-APACHE`](LICENSE-APACHE)), at your option. Every file says where it comes from in its first lines.

- **Vendored, leanVM `c445e3d5`** (the commit [leanerVM](https://github.com/Verified-zkEVM/leanerVM)'s `mumbai`
  formalizes): `crates/vendor/leanvm-c445e3d5/*`, unchanged but for a header line, except: `verifier/src/lib.rs`
  makes the WHIR verifier public; `pcs`'s `src/whir.rs`, `src/whir_ntt_ext.rs` and `src/ntt/additive_ntt_f64.rs` add
  low-memory paths (the last also fixes an aliasing bug of the in-place encodes); a lane tensor may carry a scale for
  every lane of the cube (`pcs`'s `LaneTensor`, `tensor_lane_rounds`), for `crates/pcs_claim`; robustness asserts and
  bounds checks; prover speedups, the same commitments and proofs (`pcs`, `primitives/src/hash.rs`,
  `parallel/src/lib.rs`, `bench/src/allocator.rs`; tests in `pcs`'s `src/whir/adversarial.rs`). Each file's header
  lists its changes; the speedups: [`docs/PERF_PROVER.md`](docs/PERF_PROVER.md). The workspace `Cargo.toml` and
  `rustfmt.toml` follow leanVM's.
- **Vendored, leanVM `42422001`** (its Flock prover): `crates/vendor/flock-42422001` (package `flock`), ported onto
  `c445e3d5`'s `primitives`, `parallel` and `pcs`, so that one leanVM commit is vendored. Without the BLAKE2s block;
  byte rows in the zerocheck, given row weights in the lincheck; new here: the Keccak-f block (`src/keccak.rs`) and the
  univariate-skip zerocheck (`src/zerocheck/skip.rs`). What Flock uses of `42422001`'s `primitives` and `pcs` that
  `c445e3d5` lacks is copied into the crate: `src/field` (GF(2^8), φ₈), `src/lagrange.rs`, `src/ntt`;
  `src/transcript.rs` (new) states the transcript methods as a trait.
- **Adapted from leanVM `651453c6`** (branch `PCS-openings-aggregation`): `crates/membership/quotient` (the protocol of
  `flock::quotient`, its Cantor-basis domain, wiring, transcript; new here: the χ gate, the Keccak-256 statement, the
  claims and zero knowledge), `crates/membership/evm` (bytecode generator, recording scalar; its revm machine now `crates/evm_link/src/machine.rs`), and
  leanVM's Lean proofs `formal/quotient`, ported to this circuit (here `formal/QuotientSecurity`).
- **Adapted from leanVM `42422001`'s `crates/verifier`**: `crates/leanvm/statement` (the same protocol, generic over the
  scalar; new here: the Keccak-256 chain, the tower-order ring map, the Keccak-f terminal, the workloads, the EVM
  recorder). Its `SHA3` table and the workloads follow leanVM **`9d50c92a3`**, which `prover/dump_keccak/` patches to
  write its traces.
- **New here**: `crates/leanvm/{univariate,rec,gf2_linear}`, `crates/evm_link`, `crates/pcs_claim`, `params/`,
  `formal/Statement`.
- **Lean**: built on leanerVM `mumbai` `6175f1a0` (MIT OR Apache-2.0; `formal/WhirBridge`, `formal/Statement`'s
  style), with `formal/Lv42` adapted from leanerVM `f0393df4`; dependencies pinned in `formal/lakefile.toml`:
  [CompPoly](https://github.com/Verified-zkEVM/CompPoly), [ArkLib](https://github.com/Verified-zkEVM/ArkLib),
  [VCVio](https://github.com/dtumad/VCV-io), [Mathlib](https://github.com/leanprover-community/mathlib4)
  (Apache-2.0). Each adapted file says so in its header.
- **Third-party credits** carried by vendored files: [succinctlabs/flock](https://github.com/succinctlabs/flock) (MIT
  OR Apache-2.0), [Plonky3](https://github.com/Plonky3/Plonky3) (MIT OR Apache-2.0),
  [binius64](https://github.com/binius-zk/binius64) (Apache-2.0), [bolt-rs](https://github.com/bcc-research/bolt-rs)
  (MIT).

## Conventions

- **Layout.** A crate's directory is its package name without its group's prefix: `crates/membership/*`,
  `crates/leanvm/*` (`leanvm_*`; `statement` is `leanvm_statement`), `crates/vendor/leanvm-c445e3d5/*`,
  `crates/vendor/flock-42422001` (package `flock`). Design documents live in `docs/`, by line; each crate's README
  says what it is, how to test it, and where its design is.
- **Figures.** Current figures live in this file's "Numbers" and in the README's tables; design documents give the
  figures their design explains; superseded ones go to [`docs/HISTORY.md`](docs/HISTORY.md).
- **Provenance.** Every file says where it comes from in its first lines (summed up above). Vendored files stay as
  upstream but for what their header lists.
- **Committed vectors** (`crates/leanvm/univariate/tests/vectors/*.txt`) are real proofs: never edit them by hand.
  `tests/evm_vectors.rs` replays them; `tests/prove_real.rs` writes them (`WRITE_VECTORS=<dir>`, `VECTOR_FILE`).
- **Lean-facing outputs.** Some tests write the inputs of `formal/`'s differential runners or check files there:
  `crates/membership/evm/src/lean.rs` (`formal/Implementation/Graph.lean`, `UPDATE_LEAN=1`), `crates/membership/quotient`'s
  `tests/{lean_beta_vector,lean_field_vectors,whir_bridge_vector,whir_large_params}.rs` and
  `examples/statement_vectors.rs`, `crates/leanvm/statement/tests/{lean_keccak_tables,lean_keccak_block}.rs`,
  `crates/leanvm/univariate/tests/lean_keccak_vectors.rs`, `crates/leanvm/rec/tests/{lean_circuit_keccak,
  lean_pad_counts,lean_pi2_prover,lean_graph_keccak,lean_statement_keccak}.rs`. A change of their output must go
  with the Lean side; until the port ([`docs/LEAN_PORT.md`](docs/LEAN_PORT.md)), do not regenerate them: `formal/`
  holds `f96a7938`'s.

## Lean builds

The Lean builds run on h1, under `/root/pcs-quotient-fv/` only (the rest of h1 is other work). Copy the
repository there (rsync, without `.lake`), link `formal/leanervm` to `/root/pcs-quotient-fv/leanervm` (a built
leanerVM `6175f1a0`, which `WhirBridge`, `Compose`, `Completeness` and `EndToEnd` build against), then:

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=12G lake build Soundness E2ECompleteness Evm ZK   # end theorems; #guard_msgs checks axioms
systemd-run --scope -p MemoryMax=12G lake build KeccakVm KeccakArith KeccakFlushes KeccakFlock UniKeccak UniKeccak.Fits \
  UniStatement.KeccakTables UniKeccakSound UniKeccakComplete RecGraphKeccak RecCircuit rec-circuit-keccak RecStatement \
  RecCompose                                                                     # the leanVM line's end theorems
```
