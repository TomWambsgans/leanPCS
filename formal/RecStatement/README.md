<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The structure follows formal/UniStatement/README.md. -->

# RecStatement

> **Of `f96a7938`'s π2, not the deployed one.** This library states π2 (π2v3) over π1-rec3 with π1's three claims
> encoded by the contract, as at commit `f96a7938`. The deployed π2 proves π1-rec4 and hashes π1's three claims in its
> circuit ([`docs/leanvm/rec/SPEC-REC.md`](../../docs/leanvm/rec/SPEC-REC.md)); the port is
> [`docs/LEAN_PORT.md`](../../docs/LEAN_PORT.md).

The recursion's outer proof π2 (`crates/leanvm/rec`, [`docs/leanvm/rec/PI2.md`](../../docs/leanvm/rec/PI2.md) §2
and §9), **π2v3** (`leanvm-rec-pi2v3`: the ports out of the copy argument, checked by the ports' term
`T = Σ_{port pairs} I_p (E_p + Φ_k)`; the internal pushes `P` committed in `Q` with `P = P_v + Z_V q_P`; `q`, `q_P`
below `2N`; `s = P(t)` sent; `Q` the plain sixteen-slot stack, slots `1, 5, 9, 12` the prover's, with three claims:
the identity's at `(u, ρ', y_0, y_1)`, the pushes' at `(u, ρ, 1, 1)`, the sum at `(1^m, 0, 0, y_0, y_1)`), on the EIP
draft's PCS claims (version 1: every commitment a root and its out-of-domain answer, one point a claim, one opening a
claim), for the recursion of the Keccak VM: π1 is [`UniKeccak`](../UniKeccak/README.md)'s verifier at π1-rec3's
Fiat–Shamir shape (`keccakRec3`) at the 128-signature reference (`RecGraphKeccak.Pi1.keccak128`), its recorded graph
[`RecGraphKeccak`](../RecGraphKeccak/README.md)'s `pi1GraphK`. In the files a reviewer reads:

* **π2's verifier as computable Lean**, step by step as `pi2/verifier.rs` and the contract's order;
* the circuit's tables as **data the Rust emitted** (`Data.lean`; never `σ`);
* **the eight declared claims** word for word (`contract::claim_words`) and their openings (`WhirBridge`'s
  transcription of `pcs_claim::verify_claim`);
* the **verifier-arithmetic lemmas** `RecPiop`'s rounds consume, proved;
* the **end statements**, proved in [`RecCompose`](../RecCompose/README.md): π2's part in the random-permutation model
  (`RecKnowledgeSoundness2`, `RecCompleteness2`), end-to-end knowledge soundness against `KeccakVm.KvHolds` as an
  **explicit reduction** (`RecKnowledgeSoundnessReduction`, `Reduction.lean`), and Prop-premise forms
  (`RecKnowledgeSoundness`, `RecCompleteness`) under hypotheses about π1-rec3 at Keccak-f[1600] (the soundness ones,
  `Pi1FsKeccak`, `Pi1HazardKeccak`, are false as stated for unbounded adversaries: read them as the Fiat–Shamir
  heuristic).

No `sorry`, no `native_decide`, every headline definition and theorem on Lean's three axioms (`RecStatement.lean`'s
`#guard_msgs`). A library of `formal/EndToEnd` (`srcDir = "../RecStatement"`), reusing `UniStatement`'s definitions,
`UniKeccak`'s for π1 (`KDeployment`, `SetupRootsK`, `setupTreeKWith`, `setupOodK`, `contractIvKWith`, `runK`,
`pcsOpenK`, `uniExtractorK`, `KvHolds`), `WhirBridge.Pcs`'s for the openings and `RecGraphKeccak`'s for π1-rec3's graph
and merge hazard.

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=10G lake build RecStatement            # the library; the axiom guards
```

**Do not regenerate `Data.lean` until the port** ([`docs/LEAN_PORT.md`](../../docs/LEAN_PORT.md)): the Rust's
`tests/lean_statement_keccak.rs` now compiles the deployed circuit (π1-rec4, its claims hashed), and `UPDATE_LEAN=1`
would overwrite `f96a7938`'s data with a circuit this library does not state. Its `keccak_statement_data_is_current`
is ignored and stale.

## Reading order

1. [`Basic.lean`](RecStatement/Basic.lean): the circuit as the verifier reads it (`Coeff`, `Lin`, `Formula`, `Pair`,
   `Read`, `PublicTerm`, `Circuit` with each public term's hole) and π1's call words (`CallWord`).
2. [`Data.lean`](RecStatement/Data.lean) (generated at `f96a7938`): π2's circuit for π1-rec3's graph, D16v: `2^24`
   positions, rows of 16, 55 formulas, 134 (block, role) pairs in 66 groups, 21 reads, 38 public terms and their holes;
   π1's contract IV, the setup's root, the circuit's digest; π1's three claims (`30`, `29`, `26` words).
3. [`Core.lean`](RecStatement/Core.lean): the arithmetic at `t`, over any field (`CoreSpec.run`); `stackVars`.
4. [`Spec.lean`](RecStatement/Spec.lean): `Spec::of` (the blocks' constants, the groups, the ports' `Φ`, `phiOf`).
5. [`Verifier.lean`](RecStatement/Verifier.lean): the norm's inverse, the extension, `Q`'s slots (`quotientSlots`,
   `emptySlots`), **the IV** (`ivWith`, v3), `pairPoint`, `Reduced` and its five claims, **`reduceWith`**, `runWith`.
6. [`Calls.lean`](RecStatement/Calls.lean): **the eight claims word for word** (`pcsCalls`, `claimWords`, `rootsAt`),
   π1-rec3's contract IV (`pi1IvWith`).
7. [`Security.lean`](RecStatement/Security.lean): `Pi2Circuit` (with `σ`, `κ`, its digest, setup table and
   `setupOod`), `RecDeployment` and `RecDeployment.Real`, the setup's commitments, a declared claim decoded
   (`claimOfWords`) and opened (`pcsOpenWords`: `pcsOpenKO` at `W`'s and `Q`'s sizes, reading the point off the
   permutation, else `UniKeccak.pcsOpenK` at the fixed `oodPoint`; the two agree at Keccak-f[1600],
   `pcsOpenKO_keccakF1600`), `RecProof`, the contract (`contractWith`: π2's IV v3 `keccak("leanvm-rec-iv-v3" ‖ π1's
   contract IV ‖ π2's setup root ‖ its answer ‖ the circuit's digest ‖ log_n)`, π2's verifier, the eight claims), the
   extractors (`recExtractor2`, `recExtractor`: explicit and computable), the experiments, the hypotheses and the end
   statements. [`Reduction.lean`](RecStatement/Reduction.lean): `pi1Adversary`, `hazardAdversary`,
   **`RecKnowledgeSoundnessReduction`**.
8. [`Lemmas/`](RecStatement/Lemmas): the verifier-arithmetic lemmas (below).

## Rust → Lean (at `f96a7938`)

| Rust (`crates/leanvm/rec/src/pi2`) | Lean (`RecStatement.`) |
|---|---|
| `circuit.rs`: `Coeff`, `Lin`, `Formula`, `Pair`, `Read`, `PublicTerm`, `Circuit` (but `σ`, `κ`), `max_gamma`, `coset_constants`, `vanishing`, `pair_constants`, `digest` | `Coeff`, …, `Circuit` (with `holes`), `Circuit.maxGamma`, `cosetConstants`, `vanishing`, `pairConstants`, `Pi2Circuit.digestWith` |
| `verifier.rs`: `Spec::of`, `normalised_constants`, `frobenius`, `inverse`, `extension`, `reduce`, `Reduced`, `verify` | `Spec.of`, `normalisedConstants`, `frobenius`, `normInverse`, `extension`, `reduceWith` (+ `CoreSpec.run`), `Reduced`, `runWith`/`run` |
| `prover.rs`: `stack_vars`, `QUOTIENT_SLOTS`, `EMPTY_SLOTS`, `iv`, `Setup::new`'s table and answer | `stackVars`, `quotientSlots`, `emptySlots`, `ivWith`, `Pi2Circuit.setupStack`, `Pi2Circuit.setupOod` |
| `contract.rs`: `read_indices`, `element_word`, `claim_words`, `claim_of_words` | `elementIndices`, `UniStatement.elementWord`, `claimWords`/`pcsCalls`, `claimOfWords` |
| `pcs_claim`: `verify_claim`, `ood_point` | `WhirBridge.Pcs.pcsVerifyWithHash`, `pcsVerifyWithHashO`; `pcsOpenWords` |
| `leanvm_univariate/contract.rs`: `variant_bytes`, `contract_iv_for` (`KECCAK_REC3`) | `rec3VariantBytes`, `pi1IvWith` |

Deviations, none changing a value: a `List` for a `Vec`; an out-of-range read gives a default (the Rust would panic;
it never does on the circuits tested); products by one taken; the field's inverse for the norm's (`normInverse`
transcribed).

## The verifier-arithmetic lemmas (`Lemmas/`, proved)

Over any field of characteristic two, under `SpecOf S G B pairOf portOf pubOf` (the arithmetic's constants are
`Spec::of` of `RecPiop`'s circuit `G` on a Cantor basis `B`): `ind_eval_closed` (the indicators' closed form at
`t ∉ V_m`), **`phiAt_eq`** (the verifier's `Φ_k(t)` is `phiPoly`'s value), `cellsList_eq_cellsOf`, `foldW_eq_foldAt`,
`push_side` (`P_v(t) = v_0 + w_m A/B` and the ports' fraction), `all_ne_zero_iff` (the one inversion carries the
nonzero conditions), **`checks_claims_iff`** and `checks_claims_iff_post2` (the verifier's check passes and its claims
hold iff `t ∉ V_{m+1}`, `α + P_v(t) + ξ ≠ 0` and `RecPiop`'s claims hold), the claims' values and points
(`run_quotientValue`, `run_pushesValue`, `run_u`, `digitsScale_eq`), `normConsts_of_spec`, `pairZ_eq_zHat`.

## Where the statements are proved

In [`RecCompose`](../RecCompose/README.md), at the real deployment (`realDeployment prog hprog`) from the evaluated
checks `GraphsAgree`, `DigestChecked`, `SetupRootChecked`, `IvChecked`:
`recKnowledgeSoundness_reduction_real` (`pi2Bound Q ≤ 2^-64` for `Q ≤ 2^64`, `2^-64.93` at `2^64`; the eight openings
charged once by `pcs_union_sound_oracle`, `Q`'s three claims bound by `qOodBinding`: `pi2OpenErr = 269 · 2^-137 +
2^-156`; round 1 `(4N − 1)/|F|`, `2^-140.92` with the lists), `recKnowledgeSoundness2_closed`,
`recKnowledgeSoundness_closed`, `Pi1K.recCompleteness2_pi2_rec3_K` (`δ2 ≤ 2^-164`) and
`Pi1K.recCompleteness_real_K_fs_bits` (`δ1 + δh + 2^-164`).

## Tested, defined

**Tested**: `Data.lean` is what the Rust emitted at `f96a7938`. **No Lean differential run of π2's verifier on Keccak
vectors exists**: π2's verifier is a transcription; what runs against the Rust is π2's Lean prover
(`RecComposeTest/Pi2Prover.lean`, 2/2 vectors: setup, `W`, `Q` roots, their answers, the stream, the IV v3), the
evaluated `viewCheck`, and π1's contract IV and claim words (`UniKeccak`'s). **Evaluated**: `DigestChecked`,
`SetupRootChecked` (`rec-real-check`). **Defined, not tested**: the extractors, the experiments, the Props.

## Open points

1. **The two models do not compose formally**: π2's circuit computes π1-rec3's Fiat–Shamir with the real
   Keccak-f[1600]; π1-rec3's theorems are in the random-permutation model. The soundness reduction leaves two explicit
   adversaries to the Fiat–Shamir heuristic; `Pi1CompletenessKeccak`'s random-permutation reading is proved
   (`pi1CompletenessFs_rpm`), `Pi1HazardKeccakHonest`'s is not (motivated by `hazard_probK`, a count).
2. **`pi1Stream`** (where π2's witness holds π1's stream) and **`pi2`** (π2's circuit at each IV, the Lean compiler's,
   `SetupFromCompiler`) are deployment fields; that every 32-byte IV compiles as the reference does is `IvChecked`,
   evaluated at three IVs.
3. **π1's setup commitment** is the setup's in the model; the Rust's `Data.pi1Iv` is at `SetupRoots::REFERENCE`
   (= `referenceRootsK`).
4. **The degenerate events** (`all = 0`) reject; they matter for completeness only (`all_ne_zero_iff`).
