<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# WhirBridge: the PCS openings under leanerVM `mumbai`'s proofs

[leanerVM](https://github.com/Verified-zkEVM/leanerVM) `mumbai` (commit `6175f1a0`, MIT OR Apache-2.0; its
`leanvm-rev` is leanVM `c445e3d5`, the commit `crates/vendor/leanvm-c445e3d5` vendors) proves leanVM's WHIR verifier
knowledge sound. This package transcribes the EIP draft's **PCS claim, version 1** (`crates/pcs_claim`,
[`docs/PCS_CLAIM.md`](../../docs/PCS_CLAIM.md)) into mumbai's verifier language, its transcript included, and proves
it sound in the random-oracle model, with the binding of a root to one table by its out-of-domain answer. It also keeps
the earlier layout openings (version 2, [below](#legacy-the-layout-openings-version-2)). Sorry-free, on `propext`,
`Classical.choice` and `Quot.sound` only (`#guard_msgs` in `WhirBridge.lean`, `WhirBridge/Pcs.lean`,
`PcsUnionOracle.lean`); no `native_decide` (facts about shapes are `decide +kernel`).

## The PCS claim, version 1

Files: `PcsClaim.lean`, `PcsBinding.lean`, `PcsBindingRom.lean`, `PcsBindingCoords.lean`, `PcsOracle.lean`,
`PcsUnion.lean`, `PcsUnionOracle.lean` (namespace `WhirBridge.Pcs`; `PcsUnionOracle` is `WhirBridge.Pcs.UnionO`).

**The transcription** (`crates/pcs_claim/src/lib.rs`): `claimBytes` is `PCS_claim = 1 ‖ n ‖ root (32) ‖ ood (24) ‖
point (24 n) ‖ value (24)`, each element its limbs `c2, c1, c0` big-endian; `oodPoint n root` is `ood_point`
(coordinate `j` the element in the low 24 bytes of `keccak256("leanPCS-ood" ‖ 1 ‖ n ‖ root ‖ j)`);
`pcsVerifyWithHash H F zOf x π` is `verify_claim`: reject unless `15 ≤ n ≤ 28`, the IV `H(claimBytes x)` and a zero
public digest, the proof's first two scalars the root (compared with the claim's), then `λ`, the target
`ood + λ · value`, the weight `eq(z, ·) + λ · eq(point, ·)`, `z = zOf root`, and WHIR on the deployed ladder at rate
`1/2`. In mumbai's language it is the stacked opening of two stack claims `(z, ood)` and `(point, value)` on the
polynomial's `2^n` words (`check_eq`, `prog_eq`); a claim holds of a stack iff `colEval q p = v`, the EIP's `f`
(`holds_iff`).

| Theorem | File | What |
|---|---|---|
| `claimBytes_injective`, `pcsVerify_imp`, `pcs_family_sound` | `PcsClaim.lean` | the claim's bytes name the claim; acceptance by `verify_claim` implies the root check and acceptance by the proven program; `family_sound` at this shape |
| **`pcs_sound`** | `PcsClaim.lean` | at every `15 ≤ n ≤ 28` and every `zOf`: `Pr[verify_claim accepts ∧ PcsDoomed] ≤ openingBound QA` |
| **`pcs_sound_any`** | `PcsClaim.lean` | the adversary chooses `n` too: `≤ 14 · openingBound QA ≤ 2^-59` for `QA ≤ 2^64` |
| **`two_openings_one_polynomial`** | `PcsBinding.lean` | two claims on one `(root, ood)` whose openings are not doomed, the root's list separated at `z`: **one** candidate satisfies both claims and `f(z) = ood` |
| `ood_binding`, **`ood_binding_rom`** | `PcsBinding.lean`, `PcsBindingRom.lean` | the point from an out-of-domain oracle: `Pr[some answered root's list not separated at its point] ≤ Q · C(L, 2) · n / 2^192 (+ Q (Q + 1)/2^256)`; `extract_stable` |
| **`ood_binding_coords`** | `PcsBindingCoords.lean` | **the deployed point**, read off Keccak-256 at `oodInput n root j`: `Pr[BindBadC] ≤ Q · δc n + Q (Q + 1)/2^256`, `δc n = C(L, 2)/2^192` (`δc_le`: `≤ 2^-160`; `δc_27`: `≤ 2^-168`) |
| **`pcs_union_sound`** | `PcsUnion.lean` | claims of several sizes charged once: `(QA + QV) · (ε + 5 (QA + QV)/2^256)`; what `UniKeccakSound` charges π1's three openings with |
| **`pcs_sound_oracle`**, `pcs_sound_any_oracle` | `PcsOracle.lean` | the deployed verifier, the point read off Keccak-256 by the verifier itself (`pcsVerifierO`): `pcs_sound`'s bound; what the membership end theorem uses |
| **`pcs_union_sound_oracle`** | `PcsUnionOracle.lean` | `pcs_union_sound` with the point read off Keccak-256 at a set of sizes, the bound unchanged; what `RecCompose` charges π2's eight openings with |
| `pcsVerifyWithHashO_pure`, `oodPointWith_keccak256` | `PcsUnionOracle.lean` | over a hash function the oracle verifier is `pcsVerifyWithHash` at `oodPointWith h n`; at the deployed Keccak-256 that point is `oodPoint` |
| `δood_le`, `binding_bound_le` | `PcsBindingRom.lean`, `PcsBinding.lean` | `C(L, 2) · n / 2^192 ≤ 2^-156` at every `n` (certified lists) |

```lean
theorem pcs_sound (h1 : minVars ≤ n) (h2 : n ≤ maxVars) (zOf : Digest → Vector E n)
    (A : OracleComp KeccakCalls (Claim1 n × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (pcsVerifier zOf)}[z.1.2 = true ∧ PcsDoomed zOf z.1.1 z.2] ≤
      openingBound QA

def PcsDoomed (zOf : Digest → Vector E n) (w : Claim1 n × Proof) (cache) : Prop :=
  ∀ q ∈ Candidates n logInvRate (code₀ n logInvRate).thr
      (extract (fun x ↦ cache (.inl x)) w.1.root (rootHeight n logInvRate) (2 ^ laneFold)),
    colEval q (zOf w.1.root).toList ≠ w.1.ood ∨ colEval q w.1.point ≠ w.1.value

theorem ood_binding_coords (hw : Whir.Admissible n logInvRate) (oa : OracleComp KeccakCalls α)
    (Q : ℕ) (hQ : IsTotalQueryBound oa Q) :
    Pr{let z ← (simulateQ KeccakCalls.randomOracle oa).run ∅}[BindBadC n z.2] ≤
      Q * δc n + ((Q * (Q + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256          -- δc n = C(listMax, 2) / 2^192
```

**The numbers.** `openingBound QA = (QA + 10122)(2^-128 + 5 (QA + 10122)/2^256)` (`10122` bounds the verifier's
queries at every admissible shape): `≤ 2^-63` at one `n`. The binding's error, `L` level 0's **certified** list
(leanerVM's `certOf`), in bits per query, `C(L, 2) · n / 2^192` with an out-of-domain oracle (`δood`) and
`C(L, 2) / 2^192` with the deployed point (`δc`, `log₂ n` bits better: `160.2` at `n = 15`, `168.7` at `27`, `169.4` at
`28`):

| `n` | 15 | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `L` | 87315 | 65939 | 53937 | 43620 | 34894 | 27718 | 22133 | 15692 | 12514 | 9952 | 7908 | 6296 | 4473 | 3564 |
| `δood` bits | 156.3 | 157.0 | 157.5 | 158.0 | 158.6 | 159.2 | 159.7 | 160.7 | 161.3 | 161.9 | 162.5 | 163.1 | 164.0 | 164.6 |

`whir_config.rs`'s own lists (323, 216) omit the fold group's row-union factor `2^(ℓ−1)` that leanerVM's proved fold
bound carries; only the certified lists make the deployed query counts reach `2^-128` a group.

**How they combine.** Two claims on one commitment `(root, ood)`, two proofs: by `pcs_sound` neither opening is doomed
except with `openingBound QA` each; by `ood_binding_coords` every asked root's list is separated at its point except
with `Q · δc n + Q (Q + 1)/2^256`; then `two_openings_one_polynomial`: one candidate satisfies all the claims. So
claims on one commitment may be declared and proven separately. `pcs_sound_oracle` and `pcs_union_sound_oracle` make
the two terms events of one experiment (the verifier reads the point off the oracle), as `RecCompose` composes them
(`FsBind.prEvent_doomFG_p2Ops_le`).

**Executed** (the Rust prover's openings against the Lean verifier, mumbai's Keccak):

```sh
cargo run --release -p pcs_claim --example lean_vector > target/pcs_claim_vector.txt   # n = 15, 16, 18
cargo test -p quotient --release --test whir_bridge_vector -- --ignored                # a 2^15-word table; a membership proof's three
cargo test --release -p quotient --test whir_large_params -- --ignored large_public_openings   # 2^24 .. 2^WHIR_LARGE_MAX words
(cd formal/EndToEnd && lake env lean --run ../WhirBridge/Test/CheckPcs.lean ../../target/pcs_claim_vector.txt)
(cd formal/EndToEnd && lake env lean --run ../WhirBridge/Test/CheckPcs.lean ../../target/whir_bridge_vector.txt)
(cd formal/EndToEnd && lake env lean --run ../WhirBridge/Test/CheckPcs.lean ../../target/whir_large_vector.txt)
```

All three writers use `pcs_claim::lean::pcs_vector`. `Test/CheckPcs.lean` recomputes `PCS_claim`'s bytes, its
Keccak-256 and the out-of-domain point, accepts the honest proof, and rejects a wrong value, a wrong out-of-domain
answer, a wrong root, a changed stream scalar, a changed leaf word, and the honest proof against another out-of-domain
point: `all checks: true` on the three files (2026-11-11: `3 PCS openings`; `4 PCS openings`, the membership proof's
witness and wiring claims at `n = 19` and its copy claim at `n = 23` on a `2^17`-row circuit; `5 PCS openings` at `2^24 .. 2^28`, `WHIR_LARGE_MAX=28`).

## WHIR's parameters at `2^24 ..= 2^28`

`LargeParams.lean` decides, at rate `1/2`, `Whir.ladder μ 1 = some (largeLadder μ)` (`ladder_large`), the certified
codes at `2^-128` per group and not at `2^-129` (`shapeOK_large`), the lists `listHi_large` and the verifier's query
counts `largeQueries_eq` (`≤ 10122`). `params/whir_params.py --large` computes the same bounds; `cargo test --release
-p quotient --test whir_large_params` checks the Rust's configuration and `WHIR_QUERIES` equal `largeLadder`.

| `log_n` | folds | queries (after 17 bits of grinding) | residual | `L₀` | `QO` | weakest group (bits) |
|---|---|---|---|---|---|---|
| 24 | 6, 4, 4, 4, 4 | 224, 56, 32, 23, 17 | 2 | 9952 | 7183 | 128.97 (level 0) |
| 25 | 6, 4, 4, 4, 4 | 224, 56, 32, 23, 17 | 3 | 7908 | 7546 | 128.96 (level 0) |
| 26 | 6, 4, 4, 4, 4 | 224, 56, 32, 23, 18 | 4 | 6296 | 7928 | 128.95 (level 0) |
| 27 | 6, 4, 4, 4, 4 | 225, 56, 32, 23, 18 | 5 | 4473 | 8318 | 128.99 (levels 1, 2) |
| 28 | 6, 4, 4, 4, 4, 4 | 225, 56, 32, 23, 18, 14 | 2 | 3564 | 9018 | 128.98 (level 1) |

Level 0 takes no out-of-domain sample, every later level one. `LargeMargins.lean` gives the union bounds over the lists
(`union_one_root_le`, `union_two_roots_le`, `union_three_roots_le`) and one opening's batching lead (`eBatch_large`).

## Legacy: the layout openings (version 2)

The openings before the EIP's PCS claims (`crates/membership/quotient/src/opening.rs` then: a layout
of tables on up to 64 lanes, the IV `keccak256(prefix ‖ claims)` with a 76-byte prefix holding the layout's id, the
hidden layouts' overflow lane, random lanes and gadget) stay proved, because `Compose` and parts of the leanVM line
import them:

- **`ours_sound`** (`Verifier.lean`): for every `17 ≤ log_rows ≤ 22` and each of `witnessLayout r`, `wiringLayout r`,
  `quotientLayout r`, accepting while every candidate table violates a claim has probability `≤ openingBound QA`;
  `Layout.check_eq` (the check is mumbai's `verifyStackedOpening`), `Layout.holds_iff` (table terms through
  `Table::read`), `gadget_holds_iff`, `Layout.joint_of_not_doom`, `layouts_ok`, `layouts_valid`, `family_sound`,
  `openingVerify_imp`, `candidates_ours` (`9952`, `7908`, `3564`).
- **`ours_sound_public`** (`LargeSound.lean`): every `Layout.new` layout passing `NewOK` at `2^24 ..= 2^28` words is
  `Layout.Valid` (`Layout.new_valid`) and sound at `openingBound`; `joint_public_large`.
- The guarantee is joint within one opening only (no out-of-domain sample at level 0): claims on one root split over
  two openings could get different list members. Version 1's out-of-domain answer removes this restriction.
- **No executed test**: the layout openings' checks (`Test/Check.lean`, `Test/CheckLarge.lean`) were removed with
  the Rust's layout openings (the writers now write PCS-claim vectors, which `Test/CheckPcs.lean` checks); they last
  passed against the Rust of the layout openings (git history).

## Assumptions and gaps

- **The model**: Keccak-256 and Keccak-f[1600] two independent random oracles (mumbai's two-oracle model; the end
  theorems move to one random permutation, mumbai's `LeanVMRpm.lean`, at `q²/2^508`). The adversary is classical,
  its code fixed before the oracles are sampled.
- **The Rust is the model** by execution (`Test/CheckPcs.lean`), not by proof; `MIN_VARIABLES`, `MAX_VARIABLES` and
  `decode` are transcribed as the range check and `Claim1 n`'s fixed point length. mumbai's `verifyWhir` transcribes
  `verifier.py` at `c445e3d5`; the vendored `whir.rs`, `transcript.rs`, `merkle.rs`, `multilinear.rs`, `field.rs`,
  `hash.rs` are byte-identical to leanVM `c445e3d5`'s past their headers, so mumbai's tests of leanVM's verifier hold of
  ours. `derive_config` is `Whir.ladder`; `WHIR_QUERIES` is `queryTable` (56 rows).
- **Pruned Merkle paths** (the Rust's `PrunedMerklePaths::expand`) are not formalised; they only restrict what is
  accepted.
- **Extraction** is mumbai's straight-line `extract` and Guruswami–Sudan list decoding of the level-0 word, read off
  the final cache.
- **Hiding**: none. The EIP assumes ZK-WHIR; the membership end theorem takes it as a hypothesis.

## Building

A library of `formal/EndToEnd`: `cd formal/EndToEnd && lake build WhirBridge`, against a built leanerVM `6175f1a0` at
`formal/leanervm` (on h1 a link to `/root/pcs-quotient-fv/leanervm`; AGENTS.md, "Lean builds"). The `Pcs*` modules
build in about 15 s on h1, the `Large*` ones in about 20 s.
