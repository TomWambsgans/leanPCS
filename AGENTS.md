# AGENTS.md

Notes for contributors (people and agents): what the implementation adds to the design note in
[`README.md`](README.md), where things are, and the conventions.

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

Two lines, both with Keccak-256 Fiat–Shamir and both passing their claims to `PCS_OPEN`. See
[`NOTICE.md`](NOTICE.md) for what comes from where.

**Zero-knowledge Merkle membership** with Keccak-256 (depth 32: `y = H(x | 0x11..)`, path from `H(x | 0x22..)` to
`root`), reduced to four PCS claims by five field elements, as in leanVM's `flock::quotient` but on a circuit of
one χ gate on bits, its claims opened by leanVM's WHIR unchanged.

- `crates/membership/quotient`: circuit, prover, Rust verifier (`protocol::reduce`), and the openings (`opening`), whose
  hidden layouts make the roots and the openings hide the witness ([`HIDING.md`](docs/membership/HIDING.md)).
- `crates/membership/evm`: the same verifier compiled to EVM bytecode, run on revm with `FIELD_MUL` (10 gas) and a mock
  `PCS_OPEN` precompile (ABI in `machine.rs`), which the contract calls once per commitment: three calls for the
  four claims. The contract's ABI (`verify` with a selector and packed arguments, 252 bytes of calldata) and its
  deployment are in `quotient.rs`: the circuit's commitment is a constructor argument kept in storage (read by one
  cold `SLOAD`), which a fixed owner may change (`setIndexRoot`). About 14,300 gas of execution at a claim price
  of 0, and 1.43 M gas to deploy.
- `formal/`: the Lean 4 proofs, sorry-free, on the three standard axioms.
  [`formal/Statement`](formal/Statement/README.md) states the end theorems about its own transcription of the
  Rust; `formal/EndToEnd` proves them ([`formal/README.md`](formal/README.md), "End-to-end theorems"):
  - knowledge soundness, no hypotheses: `Soundness.knowledgeSoundness`, about 2^-62 at 2^64 queries, with an
    explicit computable extractor that reads the adversary's transcript and the public setup tree;
  - completeness, no hypotheses: `E2ECompleteness.completeness_end`, δ < 2^-162;
  - the EVM contract is the Statement's verifier: `Evm.evm_accepts_iff_verifyWith`, `Evm.evm_accepts_iff_exists`
    (the bytecode = the recorded graph, and the `PCS_OPEN` mock = `opening::verify` = the Statement's opening,
    by tests);
  - zero knowledge, no hypotheses: `PcsQuotient.EndToEnd.zeroKnowledge_closed`, about 2^-113, for an explicit
    simulator named in the statement; `zeroKnowledge_closed_computable` restates it with a compiled simulator.

  The deployed Rust prover is trusted for completeness (the Statement's prover is compared with it on the
  reduction's nine scalars at 2^17 rows only). The theorems are in the random-permutation model and do not
  formally compose with the EVM one, which holds at the real Keccak-f[1600].

  The models: Keccak-f[1600] as one random permutation, the prover's randomness uniform (deployed: ChaCha12 and a
  Keccak-256 KDF, so computational). The Statement is the Rust by differential tests, not by proof.

**leanVM proofs on the EVM, by recursion** (the Keccak VM only: leanVM `9d50c92a3`'s `SHA3` table; the BLAKE2s VM
of leanVM `42422001` was removed from `crates/`).

- `crates/leanvm/univariate` (π1): a univariate PIOP for the Keccak VM's statement, its verifier
  (`verifier::reduce`, generic over the scalar: on `E` the Rust verifier, on the recorder's symbol the graph
  `contract` compiles), its contract and its prover (`prover/`, on traces `prover/dump_keccak/` makes leanVM write).
  Two variants: `KECCAK_MAIN` and `KECCAK_REC3`, π1-rec3, the recursion's inner proof. Design:
  [`SPEC.md`](docs/leanvm/univariate/SPEC.md), [`KECCAK.md`](docs/leanvm/univariate/KECCAK.md).
- `crates/leanvm/rec` (π2): π1-rec3's recorded verifier compiled into π2's circuit (`circuit`), π2's PIOP and its
  contract (`pi2`), which runs π2's verifier and passes π1's and π2's claims to `PCS_OPEN`: 43,309 transaction gas on
  the real 128-signature proof. Design: [`SPEC-REC.md`](docs/leanvm/rec/SPEC-REC.md), [`PI2.md`](docs/leanvm/rec/PI2.md).
- `crates/leanvm/statement` (`leanvm_statement`): the shared parts: the VM's tables, flushes and constraints, Flock's
  verifier and the Keccak-f block's structured terminal, the Keccak-256 chain, the EVM recorder, code and machine,
  the workloads (`shapes`: the reference is 128 signatures).
- `crates/leanvm/gf2_linear`: the prover's GF(2)-linear maps.
- `crates/vendor/leanvm-42422001`: leanVM `42422001`'s Flock prover (`lv42_*`), with the Keccak-f block
  (`flock/src/keccak.rs`, [`docs/leanvm/flock/KECCAK.md`](docs/leanvm/flock/KECCAK.md)).
- The reference: `leanvm_rec::REFERENCE` = `leanvm_statement::shapes::reference()` (128 signatures, memory `2^20`,
  bytecode `2^18`), `contract::SetupRoots::REFERENCE` (its `F`), and the real π1-rec3 proof
  `crates/leanvm/univariate/tests/vectors/keccak128_rec3.txt`.
- `formal/`: the Keccak VM's Lean development is on a separate branch (statement, Keccak-f block, π1's
  transcription); this branch's `formal/` still holds the BLAKE2s VM's ([`formal/README.md`](formal/README.md)).

**Shared.**

- `crates/evm_link`: the compilation and assembly the code generators share, and the linker that cuts a program too
  big for EIP-170 into a driver and parts of at most 24,576 bytes it `DELEGATECALL`s, computing the same. The
  membership contract fits and is assembled byte for byte as without the linker (its tests also run on it linked
  into 2 KB parts); π1's contract is 4 parts.
- `crates/vendor/leanvm-c445e3d5`: leanVM `c445e3d5`'s `primitives`, `fiat_shamir`, `pcs`, `parallel`, `verifier`,
  `bench`.
- `params/`: the parameter calculators (WHIR's, π1's and π2's soundness bits; π1's and π2's still model the BLAKE2s
  VM).
- [`STATUS.md`](STATUS.md): what is proved, tested and measured, and what remains.

```sh
cargo test --release --workspace                                      # every crate's tests
cargo test --release -p quotient -p evm                               # the membership line, incl. contract == Rust verifier
cargo bench -p quotient --bench membership                            # prover / verifier timings and sizes
cargo test --release -p evm -- --ignored --nocapture gas_report       # gas of the membership contract
cargo test --release -p leanvm_univariate -p leanvm_rec               # the leanVM line
```

## Conventions

- **Layout.** A crate's directory is its package name without its group's prefix: `crates/membership/*`,
  `crates/leanvm/*` (`leanvm_*`; `statement` is `leanvm_statement`), `crates/vendor/leanvm-c445e3d5/*`,
  `crates/vendor/leanvm-42422001/*` (`lv42_*`). Design documents live in `docs/`, by line; a crate's README says what
  it is, how to test it, and where its design is.
- **Provenance.** Every file says where it comes from in its first lines; [`NOTICE.md`](NOTICE.md) sums it up. Vendored
  files stay as upstream but for what their header lists.
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
