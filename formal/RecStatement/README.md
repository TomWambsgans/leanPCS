<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The structure follows formal/UniStatement/README.md. -->

# RecStatement

The recursion's outer proof π2 (`crates/leanvm/rec`, [`docs/leanvm/rec/PI2.md`](../../docs/leanvm/rec/PI2.md) §2,
§7, §8), **π2v4** as deployed (main `7e6d353c`; transcript `leanvm-rec-pi2v4`): the ports out of the copy argument
(the ports' term `T = Σ_{port pairs} I_p (E_p + Φ_k)`), the internal pushes `P` committed in `Q` with `P = P_v + Z_V
q_P`, `q`, `q_P` below `2N`, `s = P(t)` sent; `Q`'s sixteen slots `b_0 + 2 b_1 + 4 limb` (`H = x h`, `q`'s two digits,
`G`; `P`, `q_P`'s two digits, `S`) and **two claims on `Q`**, the identity's at `(u, z_0, z_1, y_0, y_1)` (whose layout
forces the copy sum: no sum claim) and the pushes' at `(u, ρ, z'_1, 1, 1)`; on the EIP draft's PCS claims (version 1:
every commitment a root and its out-of-domain answer, one point a claim, one opening a claim). π1 is
[`UniKeccak`](../UniKeccak/README.md)'s verifier at **π1-rec4** (`keccakRec4`, `runK4`) at the 128-signature
reference (`RecGraphKeccak.Pi1.keccak128`), its recorded graph `RecGraphKeccak.Pi1.pi1GraphK4`; **π1's three claims are
hashed in π2's circuit** (`ClaimHash` ports): the contract reads their Keccak-256s from the transaction's frame of PCS
claims (payloads 0, 1, 2) into π2's seed and encodes none of them. In the files a reviewer reads:

* **π2's verifier as computable Lean**, step by step as `pi2/verifier.rs` and the contract's order;
* the circuit's tables as **data the Rust emitted** (`Data.lean`; never `σ`);
* **the seven declared claims** (π1's three as the frame declares them, π2's four word for word) and their openings
  (`WhirBridge`'s transcription of `pcs_claim::verify_claim`);
* the **verifier-arithmetic lemmas** `RecPiop`'s rounds consume, proved;
* the **end statements**, proved in [`RecCompose`](../RecCompose/README.md): π2's part in the random-permutation model
  (`RecKnowledgeSoundness2`, `RecCompleteness2`), end-to-end knowledge soundness against `KeccakVm.KvHolds` as an
  **explicit reduction** (`RecKnowledgeSoundnessReduction`, `Reduction.lean`: π2's bound plus three explicit derived
  adversaries — π1-rec4 at Keccak-f[1600], the merge hazard, **a Keccak-256 collision**), and Prop-premise forms under
  hypotheses about π1-rec4 at Keccak-f[1600] (`Pi1FsKeccak`, `Pi1HazardKeccak`, `Keccak256CR`: false as stated for
  unbounded adversaries, read them as the Fiat–Shamir heuristic and collision resistance for bounded ones).

No `sorry`, no `native_decide`, every headline definition and theorem on Lean's three axioms (`RecStatement.lean`'s
`#guard_msgs`). A library of `formal/EndToEnd` (`srcDir = "../RecStatement"`).

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=16G lake build RecStatement            # the library; the axiom guards
UPDATE_LEAN=1 cargo test --release -p leanvm_rec --test lean_statement_keccak -- --ignored   # regenerates Data.lean
```

## Reading order

1. [`Basic.lean`](RecStatement/Basic.lean): the circuit as the verifier reads it (`Coeff`, `Lin`, `Formula`, `Pair`,
   `Read` — integer, root, scalar, `narrow` (20 bytes), `frame p` (a frame payload's four words) — `PublicTerm`,
   `Circuit` with each public term's hole, `frameReads`) and π1's call words (`CallWord`).
2. [`Data.lean`](RecStatement/Data.lean) (generated for π1-rec4): `2^24` positions, rows of 16, 63 formulas, 176
   (block, role) pairs in 74 groups, the reads `[.frame 0, .frame 1, .frame 2]`, 99 public terms (95 of value zero) and
   their holes; π1's contract IV, the setup's root, the circuit's digest; `hashed = [0, 1, 2]`, no encoded π1 claim.
3. [`Core.lean`](RecStatement/Core.lean): the arithmetic at `t`, over any field (`CoreSpec.run`): the digits `w_0 … w_m`,
   the cells, the groups' fractions, `Φ` by rows, `Y_1 = c_h + t w_m`, `Y_2 = c_h + t w_m²`, `Y_3 = 1 + ρ + ρ w_m`, the
   one inversion of `R_d Y_1 Y_2 B w_m Y_3 · c_h D_n`, the claims' points and values; `stackVars`.
4. [`Spec.lean`](RecStatement/Spec.lean): `Spec::of`.
5. [`Verifier.lean`](RecStatement/Verifier.lean): the norm's inverse, the extension, `Y³`, `Q`'s slots
   (`quotientSlots`, `emptySlots`), the IV (`ivWith`, `leanvm-rec-iv-v3`), `pairPoint`, `Reduced` and its four claims,
   **`reduceWith`** (a frame read `.frame p` reads the payload `frameAt p`), `runWith` (the seed `keccak(name ‖ IV ‖
   input ‖ the frame reads' payloads)`).
6. [`Calls.lean`](RecStatement/Calls.lean): π2's four claims word for word (`pcsCalls`, after the claims the contract
   encodes, none here), π1's contract IV (`pi1IvWith` at `pi1Variant = keccakRec4`).
7. [`Security.lean`](RecStatement/Security.lean): `Pi2Circuit`, `RecDeployment` (π2's circuit **keyed by π1's setup
   commitment**: it hashes the setup claim's root and answer) and `RecDeployment.Real`, `pi1GraphAt roots`
   (`RecGraphKeccak.graphAtSetup`), the claims' encoding and Keccak-256 (`pcsClaimBytes`, `claimHash`, `frameOf`),
   `RecProof` (the stream, π1's declared claims `pi1Claims`, seven opening proofs), the contract (`contractWith`), the
   extractors (`recExtractor2`: the first `W` candidate whose π1 stream the graph accepts with its claims hashing to the
   declared ones; `recExtractor`), the experiments, the collision game (`claimCollision`, `Keccak256Collision`,
   `collisionExperiment`, `Keccak256CR`), the hypotheses and end statements.
   [`Reduction.lean`](RecStatement/Reduction.lean): `pi1Adversary`, `hazardAdversary`, `collisionAdversary`,
   **`RecKnowledgeSoundnessReduction`**.
8. [`Lemmas/`](RecStatement/Lemmas): the verifier-arithmetic lemmas (below).

## Rust → Lean (main `7e6d353c`)

| Rust (`crates/leanvm/rec/src/pi2`) | Lean (`RecStatement.`) |
|---|---|
| `circuit.rs`: `Coeff`, `Lin`, `Formula`, `Pair`, `Read`, `PublicTerm`, `Circuit` (but `σ`, `κ`), `digest` | `Coeff`, …, `Circuit` (with `holes`), `Pi2Circuit.digestWith` |
| `verifier.rs`: `NAME`, `Spec::of`, `frobenius`, `inverse`, `extension`, `reduce`, `Reduced`, `seed`, `verify`, `QUOTIENT_SLOTS`, `EMPTY_SLOTS` | `name`, `Spec.of`, `frobenius`, `normInverse`, `extension`, `reduceWith` (+ `CoreSpec.run`), `Reduced`, `runWith`/`run`, `quotientSlots`, `emptySlots` |
| `prover.rs`: `iv`, `Setup::new`'s table and answer | `ivWith`, `Pi2Circuit.setupStack`, `Pi2Circuit.setupOod` |
| `contract.rs`: `read_indices`, `frame_payloads`, `payloads`, `claim_words` | `elementIndices`, `frameReads`, `contractWith`'s claim order, `pcsCalls` |
| `pcs_claim`: `encode`, `verify_claim` | `pcsClaimBytes`, `pcsOpenWords` |
| `leanvm_univariate/contract.rs`: `variant_bytes`, `contract_iv_for` (`KECCAK_REC4`) | `pi1VariantBytes`, `pi1IvWith` |

Deviations, none changing a value on the contract's calls: a `List` for a `Vec`; an out-of-range read gives a default;
products by one taken; the field's inverse for the norm's; the frame read by payload (`frameAt p`) where the Rust pops
the frame words in order and errs on none left (the contract hands its frame reads' payloads in that order).

## The verifier-arithmetic lemmas (`Lemmas/`, proved)

Over any field of characteristic two, under `SpecOf`: `ind_eval_closed`, **`phiAt_eq`**, `cellsList_eq_cellsOf`,
`foldW_eq_foldAt`, `push_side`, `all_ne_zero_iff` (`all ≠ 0` iff `t ∉ V_m`, `c_h`, `Y_1`, `Y_2`, `Y_3`,
`α + P_v(t) + ξ` nonzero), `run_invs`, `run_zs` (`z_0 = t w_m/Y_1`, `z_1 = t w_m²/Y_2`, `z'_1 = ρ w_m/Y_3`),
**`checks_claims_iff`** and `checks_claims_iff_post2` (the verifier's check passes and its claims hold at the slots'
values — `idEq`, `pushEq`: each claim's value is the slots' combination at its point — iff `t ∉ V_m`,
`α + P_v(t) + ξ ≠ 0` and `RecPiop`'s claims `QClaim` hold, for a nonzero scale), `run_u`, `digitsScale_eq`.

## Tested, evaluated, defined

**Tested**: `Data.lean` is what the Rust emits for π1-rec4 (`lean_statement_keccak`). No Lean differential run of π2's
verifier exists: it is a transcription. **Defined, not tested**: the extractors, the experiments, the Props.

## Open points

1. **The two models do not compose formally**: π2's circuit computes π1-rec4's Fiat–Shamir and its claims'
   Keccak-256s with the real Keccak-f[1600]; π1-rec4's theorems are random-permutation ones. The soundness reduction
   leaves three explicit adversaries (π1-rec4's break, the merge hazard, a Keccak-256 collision) to the reader's
   heuristics for Keccak-f[1600].
2. **The frame's binding is modelled by the declared claims**: `RecProof.pi1Claims` are the claims the frame declares
   and the block proved; the contract's frame word is their Keccak-256 at Keccak-f[1600] (`claimHash`).
3. **`pi1Stream`** and **`pi2`** (π2's circuit at each setup commitment, the Lean compiler's: `SetupFromCompiler`) are
   deployment fields.
