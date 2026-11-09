# AGENTS.md

Notes for contributors (people and agents): what the implementation adds to the design note in
[`README.md`](README.md), where things are, what is proved, tested and measured, what remains, provenance and
licensing, and the conventions.

## What the implementation adds to the design note

- **No OOD answer, so claims on one commitment go together.** leanVM's WHIR, which the implementation uses unchanged,
  takes no out-of-domain sample at its first commitment: a root then binds only to a short (Johnson) list of tables
  (≤ 323 at the code's parameters, ≤ 7,908 at the ones leanerVM certifies). So every claim on one commitment must be in
  one `PCS_OPEN` call and checked by one opening (a precompile that accepted them separately would be forgeable at
  about 2^111 work), and the protocol must union-bound the challenges it draws before its claims over these lists
  (≥ 130 bits remain here).
- **The opening's Fiat–Shamir seed** has leanVM's transcript shape, the form `formal/WhirBridge` proves sound
  (`family_sound`): one hash of a prefix fixed by the verifier (label, version, the layout's hash, `log_n`, the
  rate) and the claims, a zero public digest, and the root as the proof's first two scalars, which the verifier
  checks (`opening::iv`).
- **The Fiat–Shamir states need not be in the header**, given the two points above.
- **The forward-compatibility upgrade by one Schwartz–Zippel point** needs the new commitment to bind one table: an
  OOD answer at commit time, or a root anyone recomputes from the public circuit.
- **ZK without changing the verifier**: true (`docs/membership/HIDING.md`), but at these sizes it is not leanVM's 4×
  padding (which would exceed WHIR's 2^28 words): a random first piece per lane, 7 random lanes, and a *gadget* (a
  fixed weight on nine first-piece entries, cancelled by the values there, batched as a claim of value zero) that makes
  WHIR's lane rounds uniform for every challenge outside a set below 2^-188. The padding must cover the masks' lane:
  without it, anyone could solve the masks from the opening and find the Merkle path.

## Implementation (`crates/`)

Two lines, both with Keccak-256 Fiat–Shamir and both passing their claims to `PCS_OPEN`.

**Zero-knowledge Merkle membership** with Keccak-256 (depth 32: `y = H(x | 0x11..)`, path from `H(x | 0x22..)` to
`root`), reduced to four PCS claims by five field elements, as in leanVM's `flock::quotient` but on a circuit of
one χ gate on bits (3,878,612 of 2^22 rows), its claims opened by leanVM's WHIR unchanged.

- `crates/membership/quotient`: circuit, prover, Rust verifier (`protocol::reduce`), and the openings (`opening`), whose
  hidden layouts make the roots and the openings hide the witness ([`HIDING.md`](docs/membership/HIDING.md)). The
  prover's transforms are `ntt`'s (AVX-512, AVX2 or NEON lanes), split around one block-wise pass over the quotients'
  values; the `Index` keeps σ's values on the quotients' coset (512 MiB at 2^22 rows), which every proof reads.
- `crates/membership/evm`: the same verifier compiled to EVM bytecode, run on revm with `FIELD_MUL` (10 gas) and a mock
  `PCS_OPEN` precompile (ABI in `machine.rs`), which the contract calls once per commitment: three calls for the
  four claims. The contract's ABI (`verify(bytes32,bytes32,bytes)`, selector `0xde12c640`, 252 bytes of packed
  calldata) and its deployment are in `quotient.rs`: the circuit's commitment is a constructor argument kept in
  storage (read by one cold `SLOAD`), which a fixed owner may change (`setIndexRoot`). It fails closed: each
  `PCS_OPEN` reply must be a success with 32 bytes and the word 1; calls with value, other calldata lengths and
  degenerate proofs revert.
- `formal/`: the Lean 4 proofs ([below](#membership-what-is-proved)).

**leanVM proofs on the EVM, by recursion**: a leaf aggregate of leanXMSS signatures by leanVM's Keccak VM (commit
`9d50c92a3`: leanVM `42422001` with a `SHA3` table, one Keccak-f step a row).

- `crates/leanvm/univariate` (π1): a univariate PIOP for the Keccak VM's statement (two proof commitments and one setup
  commitment, the bus as a grand product in a committed heap, every identity checked at one point, Flock on the
  Keccak-f block with its structured terminal, one point claim per commitment), its verifier (`verifier::reduce`,
  generic over the scalar: on `E` the Rust verifier, on the recorder's symbol the graph `contract` compiles), its
  contract and its prover (`prover/`, on traces `prover/dump_keccak/` makes leanVM write). Two variants:
  `KECCAK_MAIN` and `KECCAK_REC3`, π1-rec3, the recursion's inner proof. Design:
  [`SPEC.md`](docs/leanvm/univariate/SPEC.md), [`KECCAK.md`](docs/leanvm/univariate/KECCAK.md),
  [`PROVER.md`](docs/leanvm/univariate/PROVER.md).
- `crates/leanvm/rec` (π2): a univariate SNARK of π1-rec3's verifier minus its openings: the recorded verifier
  compiled into π2's circuit (`circuit`, D16v, `2^24` positions; the witness replayed per proof from a plan made once
  per circuit, `circuit::plan`), π2's PIOP (π2v2: the ports out of the copy argument, the pushes `P` committed in `Q`
  with their definition, `q` below `2N`) and its contract (`pi2`), which runs π2's
  verifier and passes π1's and π2's claims to `PCS_OPEN`. Design: [`SPEC-REC.md`](docs/leanvm/rec/SPEC-REC.md),
  [`PI2.md`](docs/leanvm/rec/PI2.md), [`SPEC-POINTS.md`](docs/leanvm/rec/SPEC-POINTS.md).
- `crates/leanvm/statement` (`leanvm_statement`): the shared parts: the VM's tables, flushes and constraints, Flock's
  verifier and the Keccak-f block's structured terminal, the Keccak-256 chain, the EVM recorder, code and machine,
  the workloads (`shapes`).
- `crates/leanvm/gf2_linear`: the prover's GF(2)-linear maps.
- `crates/vendor/flock-42422001` (`flock`): leanVM `42422001`'s Flock prover, ported onto `c445e3d5`'s `primitives`,
  `parallel` and `pcs`, with the Keccak-f block (`src/keccak.rs`,
  [`docs/leanvm/flock/KECCAK.md`](docs/leanvm/flock/KECCAK.md)) and the univariate-skip zerocheck (`src/zerocheck/skip.rs`).
- **The reference workload is 128 signatures**: `leanvm_rec::REFERENCE` = `leanvm_statement::shapes::reference()`
  (memory `2^20`, bytecode `2^18`), `contract::SetupRoots::REFERENCE` (its `F`), and the real π1-rec3 proof
  `crates/leanvm/univariate/tests/vectors/keccak128_rec3.txt`.

**Shared.**

- `crates/evm_link`: the compilation and assembly the code generators share, and the linker that cuts a program too
  big for EIP-170 into a driver and parts of at most 24,576 bytes it `DELEGATECALL`s, computing the same. The
  membership contract fits and is assembled byte for byte as without the linker (its tests also run on it linked
  into 2 KB parts); π1's contract is 4 parts.
- `crates/vendor/leanvm-c445e3d5`: leanVM `c445e3d5`'s `primitives`, `fiat_shamir`, `pcs`, `parallel`, `verifier`,
  `bench`.
- `params/`: the parameter calculators (WHIR's, π1's and π2's soundness bits).

```sh
cargo test --release --workspace                                      # every crate's tests
cargo test --release -p quotient -p evm                               # the membership line, incl. contract == Rust verifier
cargo bench -p quotient --bench membership                            # prover / verifier timings and sizes
cargo test --release -p evm -- --ignored --nocapture gas_report       # gas of the membership contract
cargo test --release -p leanvm_univariate -p leanvm_rec               # the leanVM line
LEANVM_TRACE=<trace> cargo test --release -p leanvm_rec --test pipeline -- --ignored --nocapture   # trace → π1 → π2, timed
cargo test --release -p leanvm_rec --test pi2_bench -- --ignored --nocapture                    # π2's prove/open alone (PI2_PROFILE=1)
```

Build with `RUSTFLAGS="-C target-cpu=native"`. On a Zen 5 host (AMD EPYC 9355P) rustc 1.99.1's LLVM crashes (SIGILL in
`SelectionDAG::Combine`) on some test crates with `native` or `znver4`; there,
`-C target-cpu=x86-64-v4 -C target-feature=+gfni,+vpclmulqdq,+vaes,+pclmulqdq,+avx512vbmi,+aes,+bmi2` covers every
`target_feature` the code tests and measured the same.

## Numbers (M4 Max, 16 cores, but where a machine is named)

Gas is transaction gas without the 21,000 base (EIP-7623), `PCS_OPEN` at a claim price of 0.

| | ZK Merkle membership | leanVM by recursion (128 signatures) |
|---|---|---|
| Prover | 2.2 s (reduction 1.46 s, openings 0.76 s), 5.9 GiB, before the x86 work. h1 (Ryzen 7 PRO 8700GE, AVX-512), load 9–14: 3.6 s (reduction 2.46 s, openings 1.14 s), 6.2 GiB, against 8.4 s (6.45 s, 1.92 s) before. h2 (Core Ultra 7 265, AVX2), load 10: 2.3 s (1.5 s, 0.8 s), against 5.0 s | trace → π1-rec3 → π2 and openings: **0.59 s per proof** (π1 with its openings 0.34, π2 0.195 + 0.051 openings), 1.7 s per circuit once, 12.6 GB (`tests/pipeline.rs`; AMD EPYC 9355P, 64 threads, load 14–21, 2026-11-09, medians of 5 passes, three runs interleaved with the start's 2.16 s: 3.7×). Format-preserving alone 0.81 s (2.7×); with π2v2 0.69 s; with `PCS_OPEN` version 3 0.59 s. The Mac: 4.1 s before the work |
| Calldata | 252 B | 1,004 B |
| Gas | 14,289 execution, **18,309** transaction | 27,641 execution, **42,973** transaction (64,256 under EIP-7976; 43,009 before `PCS_OPEN` version 3, the calldata's zero bytes) |
| Claims | 4 in 3 calls | 7 in 6 calls |
| Deployment | 6,308-byte code, 1,426,798 gas | one contract of 13.2 KB |

- Membership, at a claim price c: 18,309 / 26,309 / 38,309 / 98,309 gas for c = 0 / 2,000 / 5,000 / 20,000. Its
  verifier: reduction < 1 ms, openings 5 ms (248 / 278 / 333 KiB).
- leanVM: at 400 signatures, 43,729 transaction gas (43,777 before version 3). π1 alone as a contract costs 358,957 transaction gas at 128
  signatures (8,020 B calldata, 3 claims). **Capacity**: `q_flock` is `2^11` words a permutation, so `C1` reaches
  WHIR's `2^28` words at about 470 signatures (1,000 do not fit, `tests/keccak_vm.rs`).

## Membership: what is proved

`formal/Statement` (`PcsQuotient`) states the relation (Keccak-256 Merkle membership over the deployed Keccak-256), the
proof format, the verifier, the honest prover, the extractor, the simulator and the experiments, in one random
permutation; `formal/EndToEnd` proves them ([`formal/README.md`](formal/README.md)). All sorry-free, on `propext`,
`Classical.choice` and `Quot.sound` only (`#guard_msgs` in each library).

- **Knowledge soundness, no hypotheses**: `Soundness.knowledgeSoundness`, about 2^-105 at Q = 0, 2^-86 at 2^40 and
  2^-62 at 2^64 queries. The extractor (`PcsQuotient.extractor`) is explicit, computable and straight-line: it reads
  the proof, the adversary's transcript and the public setup tree, then decodes (interpolation, Gao, Guruswami–Sudan).
  Stand-alone, not simulation-extractability.
- **Completeness, no hypotheses**: `E2ECompleteness.completeness_end`, δ ≈ 2^-163.9.
- **Zero knowledge, no hypotheses**: `PcsQuotient.EndToEnd.zeroKnowledge_closed`, about 2^-113 for Q ≤ 2^126, for an
  explicit simulator named in the statement (`zkSimulator`, `rpmSimOracle`; compiled in
  `zeroKnowledge_closed_computable`). Single-proof: no distinguisher query before the proof, no second proof under the
  same permutation.
- **The EVM contract is the Statement's verifier**: `Evm.evm_accepts_iff_verifyWith`, `Evm.evm_accepts_iff_exists`,
  at the real Keccak-f[1600]: the recorded graph the contract is compiled from accepts exactly when `verifyWith` does.
- **Models and trust.** Keccak-f[1600] is one random permutation; the prover's randomness is uniform (deployed:
  ChaCha12 and a Keccak-256 KDF, so computational ZK). Tested, not proved: the bytecode computes the graph;
  `FIELD_MUL` and `KECCAK256` are the Lean operations; the `PCS_OPEN` mock is `opening::verify` and that is the
  Statement's opening; the Statement is the Rust (differential tests at 2^16..2^23 rows). The deployed Rust prover is
  trusted for completeness (compared with the Statement's on the reduction's nine scalars at 2^17 rows only). The
  random-permutation theorems and the EVM one do not formally compose.

## leanVM: what is proved and tested

- **Tested.** π1's contract equals its Rust verifier word for word (straight and linked into EIP-170 parts); the real
  proofs at 32, 128 and 400 signatures (committed vectors) are accepted with `PCS_OPEN` attesting exactly the claims
  their WHIR openings prove, and mutations are rejected. π2's proof of the real 128-signature π1-rec3 proof is
  accepted by its contract, its openings verify, flipped calldata bytes are rejected, every pull of the circuit equals
  its push on the real witnesses, and the contract equals π2's Rust verifier.
- **Lean (in progress, being merged).** The Keccak VM's statement with soundness and completeness of its
  arithmetization (`formal/KeccakVm`, `formal/KeccakArith`), the Keccak-f block's soundness, completeness and terminal
  (`formal/KeccakFlock`), π1's transcription (`formal/UniKeccak`, differential-tested on `tests/lean_keccak_vectors.rs`'
  vectors) and its knowledge soundness at the reference shape, and π2's circuit = π1-rec3's verifier at 128
  signatures (`formal/RecGraphKeccak`); the recursion's end theorem remains. Until the merge, `formal/` here still
  holds the removed BLAKE2s VM's development (`Lv42`, `UniStatement`, `UniSound`, `UniComplete`, `FlockSound`,
  `RecGraph`, `RecStatement`, `RecCompose`, ...). π2's PIOP is now π2v2; `formal/RecPiop`, `RecStatement` and
  `RecCompose` state π2v1, and what changes for them (and `tests/lean_pi2_prover.rs`' output) is listed in
  [`PI2.md`](docs/leanvm/rec/PI2.md) §10. π1 and π2's circuit are unchanged.
- **Modelled, not proved.** WHIR's openings are at leanVM's ≈ 129-bit certificate each. Since `PCS_OPEN` version 3
  the recursion's six openings take another ladder past level 0 (rates `1/2, 1/4, 1/8, …`, `pcs::whir::RECURSION_SCHEDULE`;
  `params/whir_params.py --recursion`): the same eta search and 128-bit checks, and leanerVM's certificate groups,
  computed by the script, at least 128.98 bits past level 0 at `2^24 … 2^28` (128.88 at `2^23`); those ladders are not
  in leanerVM's `certTable`. The membership line keeps version 2. `params/leanvm_univariate_params.py`
  and `params/leanvm_rec_params.py` still model the old BLAKE2s π1 at 1,000 signatures; π2's rounds there are π2v2's
  (D16v: PIOP 141.3 bits, its weakest round `t`).

## Security notes

- **Claims on one commitment are opened together** (above): a requirement on the `PCS_OPEN` aggregation layer too.
- **WHIR's parameters.** The code's proximity-gap accounting omits a factor `2^(ℓ-1)` that leanerVM's theorems carry;
  leanerVM's certified parameters account for it.
- **Hiding.** Unpadded openings would not be zero knowledge: the masks can be solved from an opened mask lane, and
  per-coset fingerprints identify the Merkle path. The hiding layouts prevent both.
- **The prover's low-memory paths** make the dense prover's commitments and proofs (differential tests in
  `crates/vendor/leanvm-c445e3d5/pcs` and `crates/membership/quotient`); the in-place NTT encodes are free of the
  aliasing bug Miri flags in leanVM's.

## Remaining

- Membership: zero knowledge with a pre-proof phase (the distinguisher's queries before the proof); simulation-
  extractability; ζ could reach about 2^-157 with a tighter grinding fuel and a challenge-dependent mask bound.
- leanVM: the recursion's end theorem in Lean, and the merge of the Keccak Lean development; the soundness calculators
  for the Keccak VM; capacity beyond about 470 signatures; the contract IV (`contract::contract_iv`) still hashes two
  fixed BLAKE2s-era roots (`SetupRoots::a0`, `b0`) and two fixed layout words, kept so the committed vectors stay
  valid (dropping them means regenerating the vectors).
- Possible gas saving: absorb the membership index root in the byte order `PCS_OPEN` takes (−132 gas).
- The recursion's WHIR ladder (`PCS_OPEN` version 3) in Lean: leanerVM's `Whir.ladder` and `certTable` for its
  schedule (`shapeOK`), `formal/WhirBridge`'s Large* and `RecCompose`'s openings at its counts and version, the
  layout words' version byte in `UniKeccak` and `RecStatement`.
- The recursion prover: a lower-degree `SHA3` leaf by committing its seven address products `fp·o` in `C1` (54.5 →
  28.5 pieces; measured on the batched quotients, about 11 ms a proof, with the same stream length and Keccak-f
  count: a π1 format change not yet worth it).

## Provenance and licensing

The Rust code under `crates/` is derived from [leanVM](https://github.com/leanEthereum/leanVM) (Copyright (c) 2026
leanEthereum) and is licensed, like leanVM, under the MIT license ([`LICENSE-MIT`](LICENSE-MIT)) or the Apache License
2.0 ([`LICENSE-APACHE`](LICENSE-APACHE)), at your option. Every file says where it comes from in its first lines.

- **Vendored, leanVM `c445e3d5`** (the commit [leanerVM](https://github.com/Verified-zkEVM/leanerVM)'s `mumbai`
  formalizes): `crates/vendor/leanvm-c445e3d5/*`, unchanged but for a header line, except: `verifier/src/lib.rs`
  makes the WHIR verifier public; `pcs`'s `src/whir.rs`, `src/whir_ntt_ext.rs` and `src/ntt/additive_ntt_f64.rs` add
  low-memory paths (the last also fixes an aliasing bug of the in-place encodes); `primitives/src/hash.rs` and
  `fiat_shamir/src/lib.rs` carry test-only trace hooks behind a `trace` feature. A second WHIR ladder, for the
  recursion's openings (`PCS_OPEN` version 3), leanVM's unchanged: `pcs`'s `src/whir_config.rs` (the RS-domain
  schedule a parameter, `RECURSION_SCHEDULE`) and `src/whir.rs` (`config_for_schedule`), `verifier/src/whir.rs`
  (`Ladder::Recursion`, its query table, `verify_whir_on`, `ladder`). Prover speedups, the same commitments
  and proofs (each file's header lists them): `pcs`'s `src/whir.rs`, `src/whir_induce.rs`,
  `src/ntt/additive_ntt_f64.rs` (the encode into the kept codeword in place, the gathers, the induces, the E rounds, a
  commit that keeps its codeword) and `benches/lanes.rs` (new); `primitives/src/hash.rs` (the AVX-512 batched
  Keccak-256's transposes in registers); `parallel/src/lib.rs` (affine dispatches: each worker the same contiguous
  range of tasks every call); `bench/src/allocator.rs` (jemalloc's extents on transparent huge pages). The workspace `Cargo.toml` and
  `rustfmt.toml` follow leanVM's.
- **Vendored, leanVM `42422001`** (its Flock prover, `crates/flock`): `crates/vendor/flock-42422001` (package `flock`),
  ported onto `c445e3d5`'s `primitives`, `parallel` and `pcs`, so that one leanVM commit is vendored (`42422001`'s own
  copies of those are not). Without the BLAKE2s block; byte rows in the zerocheck, given row weights in the lincheck;
  new here: the Keccak-f block (`src/keccak.rs`) and the univariate-skip zerocheck (`src/zerocheck/skip.rs`). What
  Flock uses of `42422001`'s `primitives` and `pcs` that `c445e3d5` lacks is copied into the crate: `src/field`
  (GF(2^8), φ₈), `src/lagrange.rs` (the φ₈ barycentric weights), `src/ntt` (the GF(2^8) additive NTT);
  `src/transcript.rs` (new) states the transcript methods as a trait.
- **Adapted from leanVM `651453c6`** (branch `PCS-openings-aggregation`): `crates/membership/quotient` (the protocol of
  `flock::quotient`, its Cantor-basis domain, wiring, transcript; new here: the χ gate, the Keccak-256 statement, the
  layouts and hiding), `crates/membership/evm` (bytecode generator, recording scalar, revm machine), and the Lean
  proofs of `formal/quotient`, ported to this circuit (`formal/QuotientSecurity`).
- **Adapted from leanVM `42422001`'s `crates/verifier`**: `crates/leanvm/statement` (the same protocol, generic over the
  scalar; new here: the Keccak-256 chain, the tower-order ring map, the Keccak-f terminal, the workloads, the EVM
  recorder). Its `SHA3` table and the workloads follow leanVM **`9d50c92a3`**, which `prover/dump_keccak/` patches to
  write its traces.
- **New here**: `crates/leanvm/{univariate,rec,gf2_linear}`, `crates/evm_link`, `params/`, `formal/Statement`.
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
  `crates/vendor/flock-42422001` (one crate, `flock`: leanVM `42422001`'s, ported onto `c445e3d5`). Design documents live in `docs/`, by line; a crate's README says what
  it is, how to test it, and where its design is.
- **Provenance.** Every file says where it comes from in its first lines (summed up above). Vendored files stay as
  upstream but for what their header lists.
- **Committed vectors** (`crates/leanvm/univariate/tests/vectors/*.txt`) are real proofs: never edit them by hand.
  `tests/evm_vectors.rs` replays them; `tests/prove_real.rs` writes them (`WRITE_VECTORS=<dir>`, `VECTOR_FILE`).
- **Lean-facing outputs.** Some tests write the inputs of `formal/`'s differential runners or check files there:
  `crates/membership/evm/src/lean.rs` (`formal/Implementation/Graph.lean`, `UPDATE_LEAN=1`), `crates/membership/quotient`'s
  `tests/{lean_beta_vector,lean_field_vectors,skel_trace,whir_bridge_vector,whir_large_params}.rs` and
  `examples/statement_vectors.rs`, `crates/leanvm/statement/tests/{lean_keccak_tables,lean_keccak_block}.rs`,
  `crates/leanvm/univariate/tests/lean_keccak_vectors.rs`, `crates/leanvm/rec/tests/{lean_circuit_keccak,
  lean_pad_counts,lean_pi2_prover}.rs`. A change of their output must go with the Lean side.

## Lean builds

The Lean builds run on h1, under `/root/pcs-quotient-fv/` only (the rest of h1 is other work). Copy the
repository there (rsync, without `.lake`), link `formal/leanervm` to `/root/pcs-quotient-fv/leanervm` (a built
leanerVM `6175f1a0`, which `WhirBridge`, `Compose`, `Completeness` and `EndToEnd` build against), then:

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=12G lake build Soundness E2ECompleteness Evm ZK   # end theorems; #guard_msgs checks axioms
```
