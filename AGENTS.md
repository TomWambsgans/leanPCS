# AGENTS.md

Notes for contributors (people and agents): what the implementation adds to the design note in
[`README.md`](README.md), where things are, what is proved, tested and measured, what remains, provenance and
licensing, and the conventions.

## What the implementation adds to the design note

- **The out-of-domain answer binds a root to one table**, as the EIP draft has it (`docs/PCS_CLAIM.md`). leanVM's
  WHIR takes no out-of-domain sample at its first commitment, so a root alone binds only to a list of tables (the
  level-0 lists leanerVM certifies: 87,315 at `2^15` words down to 3,564 at `2^28`). The commitment's answer `ood = f(z)`,
  `z` derived from the root by Keccak-256, singles one out except with probability `Q · C(L, 2) · n / 2^192` (at least
  156 bits as `Q/ε`; `WhirBridge.Pcs.ood_binding_rom`), so claims on one commitment are opened, aggregated and proven
  separately, one opening a claim.
- **The opening's Fiat–Shamir seed** is the claim alone: leanVM's transcript started from `keccak256(PCS_claim)` (the
  dependency's payload) and a zero public digest, the root as the proof's first two scalars, which the verifier checks
  (`pcs_claim::verify`), the form `formal/WhirBridge` proves sound (`WhirBridge.Pcs.pcs_sound`).
- **The Fiat–Shamir states need not be in the header**, given the two points above.
- **The forward-compatibility upgrade by one Schwartz–Zippel point** needs the new commitment to bind one table: the
  out-of-domain answer gives it.
- **ZK assumes a zero-knowledge PCS** (ZK-WHIR), as the EIP does; the reference openings are leanVM's WHIR, not yet
  ZK-WHIR. With the EIP's plain point claims the earlier hidden layouts (claims on a layout, a gadget) cannot be
  expressed, so the membership protocol now makes only its own public scalars simulatable: random rows, the masks and a
  blinding of `h` make the out-of-domain answers and the part values uniform (`docs/membership/HIDING.md`: rank tests
  for the affine groups; the group `G` enters is not affine and is measured over `GF(2)`, not argued).

## Implementation (`crates/`)

Two lines, both with Keccak-256 Fiat–Shamir, and both contracts checking that their transaction declares their claims,
as the EIP draft has it: a claim's Keccak-256 is a payload of the transaction's frame of PCS claims (an EIP-8288
dependency verification frame of scheme `PCS_SCHEME`), which the contract reads with EIP-8141's `FRAMEPARAM` and
`FRAMEDATALOAD`, the frame's index being the last byte of calldata (`evm_link::declared`). The block proves the declared
claims; the contracts' `PCS_OPEN` precompile is gone.

**Zero-knowledge Merkle membership** with Keccak-256 (depth 32: `y = H(x | 0x11..)`, path from `H(x | 0x22..)` to
`root`), reduced to four PCS claims by five field elements, as in leanVM's `flock::quotient` but on a circuit of
one χ gate on bits (3,878,612 of 2^22 rows), its claims opened by leanVM's WHIR unchanged.

- `crates/membership/quotient`: circuit, prover, Rust verifier (`protocol::reduce`), and the openings (`opening`): the
  EIP's PCS claims (`pcs_claim`), four commitments with out-of-domain answers (the witness `W`, the quotient table's
  parts `H`, `Q`, `G`; `docs/membership/EIP_CLAIMS.md`) and six one-point claims; zero knowledge assuming a ZK PCS
  ([`HIDING.md`](docs/membership/HIDING.md)). The
  prover's transforms are `ntt`'s (AVX-512, AVX2 or NEON lanes), split around one block-wise pass over the quotients'
  values; the `Index` keeps σ's values on the quotients' coset (512 MiB at 2^22 rows), which every proof reads.
- `crates/membership/evm`: the same verifier compiled to EVM bytecode, run on revm with `FIELD_MUL` (10 gas), EIP-8141's
  `FRAMEPARAM` and `FRAMEDATALOAD`, and a mock frame of PCS claims (`PcsFrame`): the six claims in the EIP's encoding
  (`evm_link::declared_claims`). The contract's ABI (`verify(bytes32,bytes32,bytes)`, selector `0xde12c640`, 460 bytes
  of packed arguments, then the frame's index: 461 bytes) and its deployment are in `quotient.rs`: the circuit's
  commitment (root and out-of-domain answer) is a constructor argument kept in two storage slots (two cold `SLOAD`s),
  which a fixed owner may change (`setIndexCommitment`). It fails closed: the named frame must be a dependency
  verification frame whose first byte is `PCS_SCHEME`, and its payloads `0 .. 5` the claims' hashes, in order; calls
  with value, other calldata lengths and degenerate proofs revert.
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
  with their definition, `q` below `2N`; `Q` in sixteen slots so that its three claims are points of its stack) and
  its contract (`pi2`), which runs π2's verifier and checks π1's three and π2's five claims declared. Every commitment
  and opening of the line is the EIP draft's PCS claim (`crates/pcs_claim`: a root and an out-of-domain answer, one
  point per claim, one opening per claim, PCS version 1). Design: [`SPEC-REC.md`](docs/leanvm/rec/SPEC-REC.md),
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
- `formal/`: the Lean 4 proofs of this line ([below](#leanvm-what-is-proved-and-tested); [`formal/README.md`](formal/README.md),
  "leanVM by recursion: the Keccak VM").

**Shared.**

- `crates/evm_link`: the compilation and assembly into one contract that the code generators share. The membership
  contract (6,314 B) and π2's (13.2 KB) fit EIP-170; π1's own contract (about 86 KB) does not, and is built only to
  test it against its Rust verifier and to record the vectors' claims (the recursion verifies π1 inside π2).
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
```

Build with `RUSTFLAGS="-C target-cpu=native"`. On a Zen 5 host (AMD EPYC 9355P) rustc 1.99.1's LLVM crashes (SIGILL in
`SelectionDAG::Combine`) on some test crates with `native` or `znver4`; there,
`-C target-cpu=x86-64-v4 -C target-feature=+gfni,+vpclmulqdq,+vaes,+pclmulqdq,+avx512vbmi,+aes,+bmi2` covers every
`target_feature` the code tests and measured the same.

## Numbers (M4 Max, 16 cores, but where a machine is named)

Gas is transaction gas without the 21,000 base (EIP-7623), without the frame of PCS claims and the claims' intrinsic
gas (the EIP draft: 5,000 a transaction with claims, 1,000 a claim), which are given apart below; the leanVM column
gives the EIP-8141 frame transaction (EIP-7976's floor; without `FRAME_TX_INTRINSIC_COST` and the per-frame costs),
its PCS gas on both sides as the EIP draft has it.

| | ZK Merkle membership | leanVM by recursion (128 signatures) |
|---|---|---|
| Prover | 7.2 s (reduction 4.0 s, openings 3.2 s), 8.6 GiB (`bench.sh`, 2026-11-10), with the EIP's claims (four commitments up to `2^28` words, six openings; `docs/membership/EIP_CLAIMS.md`); before them, with the hidden layouts, 2.2 s (reduction 1.46 s, openings 0.76 s) | trace → π1-rec3 → π2 and openings, on the PCS claims (`tests/pipeline.rs`): **8.3 s per proof** (median of 5, `bench.sh`, 2026-11-10: π1 with its openings 2.2 s, π2's five openings 3.4 s), 15.2 GB. Before the PCS claims (π2's three stacks opened once each, opening version 3): 2.06 s on this Mac, 0.59 s on an AMD EPYC 9355P (64 threads) |
| Calldata | 461 B | 1,101 B (61 zero) |
| Gas | 18,899 execution; **52,856** transaction under EIP-8141 with `pcs_gas` in the floor (floor-bound: 64 · (461 + 193) + 11,000; standard 40,315) | 32,794 execution; frame transaction (EIP-8141, EIP-7976's floor, no base or per-frame cost): standard 49,678, floor **70,464** |
| Claims | 6 declared | 8 (π1's 3, π2's 5), each the EIP draft's PCS claim |
| With the frame (1 + 32 B a claim) and the PCS gas | included above (193 B, 11,000) | **99,912** (257 B, `pcs_gas` 13,000 on both sides; the floor binds) |
| Deployment | 6,667-byte code, 1,536,984 gas | one contract |

- Membership: checking the claims declared costs 61 gas once (the frame's mode and scheme) and 43 a claim beyond its
  `KECCAK256`. Its verifier: reduction < 1 ms, openings 5 ms (248 / 278 / 333 KiB).
- leanVM: at 400 signatures (the real proof), 33,740 execution; standard 50,648, floor 70,464; 99,912 with the frame
  and the PCS gas (`tests/pi2_real.rs`, `real_end_to_end`). π1 alone as a contract (the main line, 128 signatures):
  8,069 B calldata, 231,511 execution, 3 claims; standard 360,255, floor 516,416 (`keccak_gas_report`). The prover
  on the PCS claims (one opening a claim, every opening on leanVM's ladder): 8.3 s a proof (`bench.sh`, median of
  5, 2026-11-10: π1 with its openings 2.2 s, π2's five openings 3.4 s), against 2.06 s before (three openings of
  π2's three stacks at version 3). **Capacity**: `q_flock` is `2^11` words a permutation, so `C1`
  reaches WHIR's `2^28` words at about 470 signatures (1,000 do not fit, `tests/keccak_vm.rs`).

## Membership: what is proved

`formal/Statement` (`PcsQuotient`) states the relation (Keccak-256 Merkle membership over the deployed Keccak-256), the
protocol on the EIP's PCS claims (`docs/membership/EIP_CLAIMS.md`: four commitments with out-of-domain answers, six
one-point claims each opened by a version-1 PCS opening, the quotient table in three parts, random rows, the blinding of
`h`), the verifier, the honest prover, the extractor, the simulator and the experiments, in one random permutation;
`formal/EndToEnd` proves them ([`formal/README.md`](formal/README.md)). All sorry-free, on `propext`,
`Classical.choice` and `Quot.sound` only (`#guard_msgs` in each library).

- **Knowledge soundness, no hypotheses**: `Soundness.knowledgeSoundness : KnowledgeSoundness ksBound`, about
  2^-104.4 at Q = 0, 2^-85.4 at 2^40 and 2^-61.4 at 2^64 queries (125.4 bits as Q/ε), the six openings' 2^-128 a
  query dominating. Each challenge is bounded for the one candidate tuple the four roots' out-of-domain answers pin
  (`ComposePcs.prEvent_pinned_le`, `trace_core4P`: 2^-164 a query, not the union over < 2^50 tuples), the four lists
  separated at their points (`WhirBridge.Pcs.ood_binding_coords` at 25, 27, 28 variables: about 2^-166.5 a query
  together). The openings are sound with the verifier computing the out-of-domain point from Keccak-256
  (`WhirBridge.Pcs.pcs_sound_oracle`). The extractor
  (`PcsQuotient.extractor`) is explicit, computable and straight-line. Stand-alone, not simulation-extractability.
- **Completeness, no hypotheses**: `E2ECompleteness.completeness_end : Completeness deltaPcs`, `deltaPcs` < 2^-163.
- **Zero knowledge, under two hypotheses**: `PcsQuotient.EndToEnd.zeroKnowledge_pcs_closed`: `PcsZeroKnowledge`
  (the PCS opening is zero knowledge, as the EIP assumes ZK-WHIR) and `RevealedUniform` (the revealed scalars are
  uniform at all but `εr` of the challenges) give zero knowledge within `εpcs Q + εr + εfs₀` for the explicit simulator
  `zkSimulator`, `εfs₀ ≤ 2^-162` proved (`fiatShamirUniform_closed`). `RevealedUniform` is tested, not proved: two of
  its three groups are affine and of full rank (`hiding::revealed_scalars_are_uniform`); the third is not affine and
  is measured over `GF(2)` (`hiding::group_a_*`, `docs/membership/HIDING.md`, "Group 2, measured"). Single-proof.
- **The EVM contract is the Statement's verifier**: `Evm.evm_accepts_iff_verifyWith`, `Evm.evm_accepts_iff_exists`,
  at the real Keccak-f[1600], against the regenerated `Graph.lean` (the six declared claims, the index commitment's
  two storage words).
- **Models and trust.** Keccak-f[1600] is one random permutation; the prover's randomness is uniform (deployed:
  a Keccak-256 KDF, `Randomness::derive`, so computational ZK). Tested, not proved: the bytecode computes the graph;
  `FIELD_MUL` and `KECCAK256` are the Lean operations; the Statement is the Rust (differential tests: the reduction,
  index and proof vectors agree; the prover vectors are too slow for interpreted Lean). The deployed Rust prover is
  trusted for completeness. The random-permutation theorems and the EVM one do not formally compose.

## leanVM: what is proved and tested

- **Tested.** π1's contract equals its Rust verifier word for word; the real
  proofs at 32, 128 and 400 signatures (committed vectors) are accepted with their frame of PCS claims declaring
  exactly the claims their WHIR openings prove, and mutations are rejected. π2's proof of the real 128-signature π1-rec3 proof is
  accepted by its contract, its openings verify, flipped calldata bytes are rejected, every pull of the circuit equals
  its push on the real witnesses, and the contract equals π2's Rust verifier.
- **Proved in Lean** (`formal/`, [`formal/README.md`](formal/README.md); sorry-free, no `native_decide`, on `propext`,
  `Classical.choice` and `Quot.sound` only, `#guard_msgs` in each library), at the 128-signature reference shape:
  - **the statement**: `KeccakArith.kvSoundness`, `kvCompleteness` (the Keccak VM's `KvHolds` against its valid
    executions), `KeccakFlushes.flushesSha3_eq`, the Keccak-f block `KeccakFlock.keccakFlockSpec` (sound, complete)
    and its structured terminal;
  - **π1**, on the EIP's PCS claims (each commitment's out-of-domain answer read after its root, the claims
    `pcsClaimsK` opened by `WhirBridge.Pcs.pcsVerifyWithHash`, the three openings charged once by
    `WhirBridge.Pcs.pcs_union_sound`), in one random permutation: knowledge soundness
    `UniKeccakSound.uniKnowledgeSoundnessKeccak_closed` (≤ 2^-64 at Q ≤ 2^64, 128.87 bits as Q/ε) and
    `uniKnowledgeSoundnessKeccakRec3_closed` (π1-rec3, 128.49 bits), explicit extractor; completeness
    `UniKeccakComplete.uniCompletenessKeccak_closed`, `uniCompletenessKeccakRec3_closed`, for an explicit Lean honest
    prover, δ = `Prob.deltaK` < 2^-169, given a program IV of at least 32 bytes (the deployed one has 32);
  - **π1-rec3's graph**: the recorded graph computes π1-rec3's verifier off the merge hazard, for every permutation
    (`RecGraphKeccak.Sim.pi1GraphIsVerifierK`, no hypothesis); the hazard has ≤ 2^16 values of `t` per `p_0`, 2^-176
    (`hazard_probK`); a satisfied π2 circuit carries the graph's outputs (`pi1rec3K_end`);
  - **the recursion**, knowledge soundness as an explicit reduction, with no Fiat–Shamir premise:
    `RecCompose.recKnowledgeSoundness_reduction_real`: Pr[the contract accepts ∧ the extractor finds no `KvHolds`
    witness] ≤ `pi2Bound Q` (≤ 2^-64 at Q ≤ 2^64, 128.93 bits as Q/ε; π2's Fiat–Shamir and the eight PCS openings,
    charged once by `WhirBridge.Pcs.pcs_union_sound_oracle`, in the random-permutation model, with `Q`'s three claims
    bound to one table by its out-of-domain answer, `qOodBinding`, proved)
    \+ Pr[`pi1Adversary` breaks π1-rec3 at Keccak-f[1600]] + Pr[`hazardAdversary` hits the merge hazard], the two
    adversaries explicit (the adversary, then π2's extractor; same query count). Completeness
    `RecCompose.Pi1K.recCompleteness_real_K_fs_bits`, error δ1 + δh + 2^-164 for the Lean provers, under
    `Pi1CompletenessKeccak` (δ1; its random-permutation reading is proved at 2^-169) and `Pi1HazardKeccakHonest` (δh),
    both about the honest π1-rec3 run at Keccak-f[1600].
- **Evaluated in Lean, not proved** (the end theorems' hypotheses): the emitted π1-rec3 graph is the Lean program
  (`GraphsAgree`, `RecGraphKeccakTest/Pi1Check.lean`); the digest and the setup root of the Lean compiler's π2 circuit
  are the Rust's (`DigestChecked`, `SetupRootChecked`); the per-IV check (`IvChecked`: compile, view check, stream
  decoding) at the reference, zero and all-ones IVs, assumed at the others (`rec-real-check`, `rec-view-check`).
- **Tested against the Rust, not proved**: π1's verifier transcription (`UniKeccakTest/Runner.lean`, 90 verifier and
  14 terminal vectors, the real proofs among them), the verifier's tables, the block's rows and terminal, the circuit
  compiler (`rec-circuit-keccak`: the identical circuit), π2's statement data (`lean_statement_keccak.rs`), the emitted
  graph (`lean_graph_keccak.rs`), π2's Lean prover on two small circuits. The deployed Rust provers are trusted for
  completeness; the contract's bytecode is π2's Rust verifier by the Rust's tests.
- **Modelled, not proved: soundness at other shapes.** `params/leanvm_univariate_params.py` and
  `params/leanvm_rec_params.py` give every round's bits at the code's degrees and the certified lists, at 32, 128 and
  400 signatures. At 128, with the openings charged once at WhirBridge's `269 · 2^-137` a query: π1 128.93 bits as
  Q/ε (main line) and 128.79 (π1-rec3), π2 128.93, the recursion about 127.9; the Lean bounds, coarser, are 128.87,
  128.49 and 128.93 (`docs/leanvm/univariate/SPEC.md` §9).
- **The Lean follows the Rust's protocol** (π2v3 on the EIP's PCS claims): π2's contract model checks the eight
  claims (π1's three, π2's five), each `[root, ood, point, value]` opened by one PCS opening; π2's IV binds the setup's
  answer; `Q` is the plain sixteen-slot stack, its four empty slots the prover's: `RecPiop` reads `h` below `2N` and
  slot 12 inside `P`'s share, at round 1's error `(4N − 1)/|E|` (`docs/leanvm/rec/PI2.md`, "The empty slots").
  W's and Q's openings read their out-of-domain point off the model's Keccak-256 (`pcsOpenKO`; equal to the fixed point
  at Keccak-f[1600], `pcsOpenKO_keccakF1600`); π1's three claims and π2's setup claim, one claim per commitment, keep
  the fixed point. π2's Lean prover agrees with the Rust on the `lean_pi2_prover` vectors (2/2: roots, IV, stream).

## Security notes

- **Claims on one commitment may be proven separately**: the out-of-domain answer binds the root (above), so the block's
  aggregation needs no grouping of declared claims.
- **WHIR's parameters.** The code's proximity-gap accounting omits a factor `2^(ℓ-1)` that leanerVM's theorems carry;
  leanerVM's certified parameters account for it.
- **Hiding.** The reference openings (leanVM's WHIR) are not zero knowledge: the membership proof's zero knowledge
  assumes the EIP's ZK-WHIR (`HIDING.md`).
- **The prover's low-memory paths** make the dense prover's commitments and proofs (differential tests in
  `crates/vendor/leanvm-c445e3d5/pcs` and `crates/membership/quotient`); the in-place NTT encodes are free of the
  aliasing bug Miri flags in leanVM's.

## Remaining

- Membership: zero knowledge with a pre-proof phase (the distinguisher's queries before the proof); simulation-
  extractability.
- leanVM in Lean: (1) the model gap: π2's circuit computes π1-rec3's Fiat–Shamir at the real Keccak-f[1600] while
  π1-rec3's theorems are in the random-permutation model, so the soundness reduction's two π1 terms and the two
  completeness premises are left to the Fiat–Shamir heuristic for Keccak-f[1600]; (2) the compiler's IV uniformity
  (`RecCompose.PatchChecked`, which with the evaluated checks gives `IvChecked` at every IV; a relational simulation
  of about 1,200 lines of the builder); (3) closed bounds at other shapes than the reference; (4) declarations in the
  shared libraries that no end theorem uses ([`formal/README.md`](formal/README.md)).
- leanVM: capacity beyond about 470 signatures.
- Membership in Lean: `RevealedUniform` proved rather than tested, which needs a protocol whose revealed scalars are affine in
  its randomness (e.g. `G` blinded as `h` is: `HIDING.md`).
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
  `fiat_shamir/src/lib.rs` carry test-only trace hooks behind a `trace` feature. A lane tensor may carry a scale for
  every lane of the cube (`pcs`'s `src/whir.rs`, `LaneTensor`, `tensor_lane_rounds`), for a claim at a point of the
  whole stack opened against a commitment of its leading lanes (`crates/pcs_claim`). Prover speedups, the same commitments
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
  lean_pad_counts,lean_pi2_prover,lean_graph_keccak,lean_statement_keccak}.rs`. A change of their output must go
  with the Lean side.

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
