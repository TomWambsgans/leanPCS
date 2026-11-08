# AGENTS.md

Part of this repository. Notes for contributors: what the implementation adds to the design note in
[`README.md`](README.md), and where things are.

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
- **ZK without changing the verifier**: true (`crates/quotient/HIDING.md`), but at these sizes it is not leanVM's 4×
  padding (which would exceed WHIR's 2^28 words): a random first piece per lane, 7 random lanes, and a *gadget* (a
  fixed weight on nine first-piece entries, cancelled by the values there, batched as a claim of value zero) that makes
  WHIR's lane rounds uniform for every challenge outside a set below 2^-188. The padding must cover the masks' lane:
  without it, anyone could solve the masks from the opening and find the Merkle path.

## Implementation (`crates/`)

Two lines, both with Keccak-256 Fiat–Shamir and both passing their claims to `PCS_OPEN`. See
[`AGENTS.md`](AGENTS.md) for what comes from where.

**Zero-knowledge Merkle membership** with Keccak-256 (depth 32: `y = H(x | 0x11..)`, path from `H(x | 0x22..)` to
`root`), reduced to four PCS claims by five field elements, as in leanVM's `flock::quotient` but on a circuit of
one χ gate on bits, its claims opened by leanVM's WHIR unchanged.

- `crates/quotient`: circuit, prover, Rust verifier (`protocol::reduce`), and the openings (`opening`), whose
  hidden layouts make the roots and the openings hide the witness ([`HIDING.md`](crates/quotient/HIDING.md)).
- `crates/evm`: the same verifier compiled to EVM bytecode, run on revm with `FIELD_MUL` (10 gas) and a mock
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

**leanVM proofs on the EVM, by recursion.**

- `crates/leanvm_univariate`, `crates/leanvm_rec`: π1 is a univariate PIOP for leanVM's statement, with its prover
  and verifier; π2 wraps π1's verifier, and the contract runs π2's verifier for about 45K gas
  (`crates/leanvm_rec/README.md`). Both the BLAKE2s VM (leanVM `42422001`, end to end, Lean proofs) and the
  Keccak VM (the `SHA3` table of leanVM `9d50c92a3`, Flock on the Keccak-f block; verifier and gas only so far,
  [`KECCAK.md`](crates/leanvm_univariate/KECCAK.md)) are supported.
  - `crates/leanvm_flock_gas` holds the shared parts: leanVM's statement ported, Flock's verifier, and the EVM
    recorder and machine.
  - `crates/lv42_*` is leanVM `42422001`'s Flock prover, vendored, with the Keccak-f block (`lv42_flock/KECCAK.md`).
  - `crates/gf2_linear` holds the prover's GF(2)-linear maps.
- `formal/`: π1's statement and knowledge soundness (`UniStatement`, `UniSound`, `FlockSound`, on `Lv42`'s
  relation), its completeness (`UniComplete`), and the recursion's end theorems (`RecGraph`, `RecStatement`,
  `RecPiop`, `RecCircuit`, `RecCompose`), described in [`formal/README.md`](formal/README.md).

**Shared.**

- `crates/evm_link`: the compilation and assembly the code generators share, and the linker that cuts a program too
  big for EIP-170 into a driver and parts of at most 24,576 bytes it `DELEGATECALL`s, computing the same. The
  membership contract fits and is assembled byte for byte as without the linker (its tests also run on it linked
  into 2 KB parts); leanVM's verifier (`crates/leanvm_flock_gas`, option A) is 5 contracts, 26,601 gas more (7.9%),
  its transaction unchanged under EIP-7623.
- Vendored from leanVM `c445e3d5`: `primitives`, `fiat_shamir`, `pcs`, `parallel`, `verifier`, `bench`.
- `params/`: the parameter calculators (WHIR's, π1's and π2's soundness bits).
- [`STATUS.md`](STATUS.md): what is proved, tested and measured, and what remains.

```sh
cargo test --release -p quotient -p evm                               # tests, incl. contract == Rust verifier
cargo bench -p quotient --bench membership                            # prover / verifier timings and sizes
cargo test --release -p evm -- --ignored --nocapture gas_report       # gas of the contract
cargo test --release --workspace                                      # every crate's tests
```

The Lean builds run on h1, under `/root/pcs-quotient-fv/` only (the rest of h1 is other work). Copy the
repository there (rsync, without `.lake`), link `formal/leanervm` to `/root/pcs-quotient-fv/leanervm` (a built
leanerVM `6175f1a0`, which `WhirBridge`, `Compose`, `Completeness` and `EndToEnd` build against), then:

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=12G lake build Soundness E2ECompleteness Evm ZK   # end theorems; #guard_msgs checks axioms
```
