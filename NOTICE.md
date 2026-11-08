# Notice

The Rust code under `crates/` is derived from [leanVM](https://github.com/leanEthereum/leanVM)
(Copyright (c) 2026 leanEthereum) and is licensed, like leanVM, under the MIT license
([`LICENSE-MIT`](LICENSE-MIT)) or the Apache License 2.0 ([`LICENSE-APACHE`](LICENSE-APACHE)), at your
option. Every file says where it comes from in its first lines.

## What comes from where

### Vendored

- **leanVM, commit `c445e3d51a5a85031df47240595698f3b24897bf`** (branch `main`, the commit
  [leanerVM](https://github.com/Verified-zkEVM/leanerVM)'s `mumbai` branch formalizes):
  `crates/vendor/leanvm-c445e3d5/{primitives,fiat_shamir,pcs,parallel,verifier,bench}` (leanVM's
  `crates/{primitives,fiat_shamir,pcs,parallel,verifier,bench}`), copied unchanged but for a header line, except:
  - `verifier/src/lib.rs`, which makes the WHIR verifier public;
  - three prover files of `pcs` (`src/whir.rs`, `src/whir_ntt_ext.rs`, `src/ntt/additive_ntt_f64.rs`), which add ways
    to make the same commitments and proofs in less memory; the last also fixes an aliasing bug of leanVM's in-place
    encodes. `src/whir.rs` and `src/whir_config.rs` also have comments corrected (no code change), reported upstream;
  - `primitives/src/hash.rs` and `fiat_shamir/src/lib.rs`, which carry test-only trace hooks behind a `trace` feature
    that no production build enables.

  Each file's header says what changed. The workspace `Cargo.toml` and `rustfmt.toml` follow leanVM's.
- **leanVM, commit `42422001`** (branch `main`, the parent of `4af2cddd` "Replace BLAKE2S by KECCAK-256"): its Flock
  prover, in `crates/vendor/leanvm-42422001/`:
  - `primitives`, `parallel`, `flock` (packages `lv42_primitives`, `lv42_parallel`, `lv42_flock`; renamed, since the
    workspace's `primitives` and `parallel` are `c445e3d5`'s) are leanVM `42422001`'s crates of those names, copied
    unchanged but for a header line, except where the headers say otherwise:
    - its BLAKE2s compression block is not vendored (`flock`'s `hash.rs` and `gf2.rs`, `primitives`' `hash`, the
      BLAKE2s helpers of `witness.rs`); `flock/src/slice.rs` keeps `hash.rs`'s circuit-agnostic `SliceClaim` and
      `min_n_blocks_log`;
    - `zerocheck/bit_fold.rs` and `zerocheck/multilinear.rs` take rows of 1, 2 and 4 bytes (and the latter a byte-row
      pass with a product table); `lincheck.rs` takes its row weights given;
    - new here: `flock/src/keccak.rs` (and its test), the Keccak-f[1600] block of
      [`docs/leanvm/flock/KECCAK.md`](docs/leanvm/flock/KECCAK.md), whose walks and prover entry follow the BLAKE2s
      block's; and `flock/src/zerocheck/skip.rs` (built on leanVM `42422001`'s zerocheck prover and its round-1
      kernel, CREDIT flock-core), the zerocheck with a univariate skip of 3 to 6.
  - `pcs` (`lv42_pcs`) is the part of `42422001`'s `pcs` that `flock` uses: the GF(2^8) additive NTT, its inverse
    table, the packing constants and one inner product.
  - `fiat_shamir` (`lv42_fiat_shamir`, new here) states as a trait the transcript methods `flock` calls (leanVM's
    `ProverState`'s), which the univariate prover's Keccak-256 chain implements.

### The zero-knowledge membership proof

- **Adapted from leanVM's branch `PCS-openings-aggregation`, commit `651453c6`**:
  - `crates/membership/quotient`: the protocol of `flock::quotient` (`doc/quotient/main.tex` there), its Cantor-basis
    domain (copied), its circuit's wiring and public rows, the Keccak-256 transcript chain, and the idea of opening a
    claim on a table whose stack holds only the lanes that can be nonzero. New here: the gate (one χ on bits), the
    Keccak-256 statement, and the tables' layouts for leanVM's WHIR as it is, including the hidden layouts of
    [`docs/membership/HIDING.md`](docs/membership/HIDING.md) (which adapt the padding of `flock::membership`,
    `crates/flock/membership-zk.md` on the same branch) and their exact checks (`src/hiding.rs`).
  - `crates/membership/evm`: the bytecode generator, the recording scalar and the revm machine with `FIELD_MUL`.
  - `formal/`: the Lean proofs of `formal/quotient` (sorry-free for the original circuit), ported to this circuit
    (`formal/QuotientSecurity`); each file names its source.
- **`crates/evm_link`** (new here): the compilation of a recorded graph and the assembly, moved from
  `crates/leanvm/statement/src/evm/codegen.rs` and `crates/membership/evm/src/codegen.rs` (the latter adapted from
  leanVM's branch `PCS-openings-aggregation`, commit `651453c6`), and the linker into deployable contracts.

### The leanVM line (the Keccak VM)

- **`crates/leanvm/statement`** (package `leanvm_statement`): adapted from leanVM `42422001`'s `crates/verifier`.
  `src/field.rs` is its `field.rs`, unchanged but for a header and the changes it lists; `src/lib.rs` (errors and the
  announced shape), `src/layout.rs` (the five shared tables, their flushes and constraints), `src/flock.rs`,
  `src/flock_min.rs`, `src/multilinear.rs` and `src/transcript.rs` adapt the files of the same names (the same
  protocol, generic over the scalar it computes on). New here: the Keccak-256 chain (after
  `crates/membership/quotient/src/transcript.rs`), the ring map in tower order (`src/ring_tower.rs`), the Keccak-f
  block's verifier walk and structured terminal (`src/keccak_flock.rs`), the workloads (`src/shapes.rs`), and the EVM
  recorder, code generator and machine (`src/evm/`, after `crates/membership/evm`).
- **Adapted from leanVM, commit `9d50c92a3`** (its Keccak branch before the switch to GKR): `src/layout.rs`'s `SHA3`
  table (`flushes_sha3`, its columns and `SHA3_CELL_LANES`) states `crates/leanvm_core/src/tables.rs`'s `Sha3Table`
  and `hash_flock.rs`'s cell layout there. The workloads (`src/shapes.rs`) are runs of that commit, and
  `crates/leanvm/univariate/src/prover/dump_keccak/` patches a tree of it to write its execution traces.
- **`crates/leanvm/univariate`** (new here): a univariate PIOP for the Keccak VM's statement
  ([`docs/leanvm/univariate/SPEC.md`](docs/leanvm/univariate/SPEC.md)), its verifier generic over the scalar and
  compiled to EVM code through `crates/leanvm/statement`. Its Cantor basis is computed as
  `crates/membership/quotient/src/domain.rs`'s (adapted from leanVM `651453c6`). Its prover
  ([`docs/leanvm/univariate/PROVER.md`](docs/leanvm/univariate/PROVER.md)) reads leanVM `9d50c92a3`'s own execution
  traces, transforms them with `crates/membership/quotient/src/domain.rs`'s additive NTT, vectorized in
  `crates/membership/quotient/src/ntt.rs` (the same layers in the same order; its lane-wise product and reduction are
  those of the vendored `primitives`' AVX-512 field, after binius64), commits and opens them with the vendored WHIR
  (leanVM `c445e3d5`), its openings in the transcript shape of `crates/membership/quotient/src/opening.rs`, and runs
  Flock with the vendored leanVM `42422001` prover.
- **`crates/leanvm/gf2_linear`** (new here): the GF(2)-linear maps `x ↦ Σ_k c_k x^(2^k)` of `E` that the prover's
  batching sumcheck evaluates the ring switch's twisted weight with, as byte tables and eight at a time with GFNI.
- **`crates/leanvm/rec`** (new here): recursion for `crates/leanvm/univariate`'s verifier
  ([`docs/leanvm/rec/SPEC-REC.md`](docs/leanvm/rec/SPEC-REC.md)). It counts and evaluates that verifier's recorded
  graph (`crates/leanvm/statement/src/evm/record.rs`, whose node semantics and Keccak-256 chain `src/eval.rs`
  follows), compiles it into π2's circuit, and measures `crates/membership/quotient`'s circuit (adapted from leanVM
  `651453c6`) as the reference of its outer proof.

### Parameters and Lean

- **`params/`** (new here): the parameter calculators. `whir_params.py` replicates leanVM's WHIR parameter search
  (`crates/vendor/leanvm-c445e3d5/pcs/src/whir_config.rs`) and copies rows of leanerVM's certified parameter table
  (`Params/Deployed.lean`); `leanvm_univariate_params.py` and `leanvm_rec_params.py` (which builds on it) compute
  π1's and π2's soundness.
- **`formal/Statement/`** (new here): the statement of `crates/membership/quotient` in Lean, in the style of
  leanerVM's `Statement/` package (branch `mumbai`, commit `6175f1a0`, MIT OR Apache-2.0), on which it depends (a Lake
  dependency, not vendored) for the fields, Keccak-256, the random-permutation model, the WHIR verifier and prover
  pieces and the extractor's decoder; each file names what it takes from it.
- **Built on [leanerVM](https://github.com/Verified-zkEVM/leanerVM) `mumbai`, commit `6175f1a0`** (MIT OR
  Apache-2.0): `formal/WhirBridge` states this repository's WHIR openings in mumbai's verifier language and proves
  their soundness from mumbai's theorems, importing them; `WhirBridge/Variant.lean` adapts mumbai's assembly of
  leanVM's verifier (`lean_vm/LeanVM/Protocol/EndToEnd/Sound/`, `Verifier/Cost.lean`). Each file says so in its
  header.
- **Adapted from [leanerVM](https://github.com/Verified-zkEVM/leanerVM) `mumbai`, commit `f0393df4`** (the last
  before its switch to Keccak, formalizing leanVM `3f7dc219`, whose `crates/verifier`, `crates/flock`,
  `python-verifier` and `doc` are leanVM `42422001`'s; MIT OR Apache-2.0, `Protocol/ToCompPoly/AmbientStacking.lean`
  Apache-2.0 by its own notice): `formal/Lv42`, leanVM `42422001`'s VM (leanISA with `BLAKE2S`), its
  arithmetization, the abstract M3 instance with its Flock region and the leanISA adaptor, from `lean_vm/LeanVM/`
  (`Spec/Isa.lean`, `Spec/IsaWith.lean`, `Spec/Blake2s.lean`, `Parameters/Isa.lean`, `Semantics/Lemmas.lean`,
  `Arithmetization/`, `Protocol/Spine/Instance.lean`, `Protocol/Stack.lean`, `Protocol/FixedColumns.lean`,
  `Protocol/LeanIsa.lean`, `Protocol/LeanIsa/`, `Protocol/Blake2sHash.lean`, `Protocol/Blake2sCircuit.lean`,
  `Protocol/FlockSpec.lean`, `Protocol/ToArkLib/Flock/{BlockR1CS,Circuit,Builder,Words}.lean`,
  `Protocol/ToCompPoly/{Stacking,AmbientStacking}.lean`, and the Flock constants and padding tables of
  `Spec/Verifier.lean`), renamed from `LeanVM` to `Lv42` and otherwise unchanged but for the imports of the
  BLAKE2s-era verifier and GKR bus phase, which are not ported. The field, multilinear and Clean-bridge modules those
  files import are leanerVM `6175f1a0`'s, imported as they are (`formal/EndToEnd` builds against it). Each file says
  so in its header.
- **Lean dependencies** (pinned in `formal/lakefile.toml`, at the revisions leanerVM `mumbai` uses):
  [CompPoly](https://github.com/Verified-zkEVM/CompPoly) `572f9973` (Apache-2.0), whose `BF64` and `BF64.Ext3`
  (GF(2^64) and GF(2^192) with their irreducibility proofs) `formal/Field` builds on;
  [ArkLib](https://github.com/Verified-zkEVM/ArkLib), [VCVio](https://github.com/dtumad/VCV-io),
  [Mathlib](https://github.com/leanprover-community/mathlib4) (Apache-2.0); leanerVM `mumbai`'s `statement`, `common`
  and `lean_vm` packages (`formal/QuotientRpm`, `formal/Compose`, `formal/QuotientZk`, `formal/Circuit` import them).
  Files adapted from any of them say so in their header.

### Third-party credits

Carried by the vendored files (each file names its own):
[succinctlabs/flock](https://github.com/succinctlabs/flock) (MIT OR Apache-2.0),
[Plonky3](https://github.com/Plonky3/Plonky3) (MIT OR Apache-2.0),
[binius-zk/binius64](https://github.com/binius-zk/binius64) (Apache-2.0),
[bcc-research/bolt-rs](https://github.com/bcc-research/bolt-rs) (MIT).
