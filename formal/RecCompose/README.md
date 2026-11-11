<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# RecCompose: the recursive verifier's end theorems

The recursive EVM verifier for the Keccak VM's proofs (leanVM 9d50c92a3's `SHA3` table, the 128-signature reference;
`crates/leanvm/rec`): the contract runs π2's verifier, then checks eight claims declared, each the EIP draft's PCS claim
(a root, its out-of-domain answer, one point, a value; π1's `C1`, `C2`, `F`; π2's `W`, the setup, `Q`'s identity,
pushes' and sum claims). Its statements are `RecStatement`'s (`RecStatement/Security.lean`, `Reduction.lean`;
[`../RecStatement/README.md`](../RecStatement/README.md)). π2's circuit computes π1-rec3's Fiat–Shamir with the real
Keccak-f[1600], while π1-rec3's theorems (`UniKeccakSound`, `UniKeccakComplete`) are in the random-permutation model,
so the statements come in three forms:

1. **π2's part, in the random-permutation model**: `RecKnowledgeSoundness2 D ε2` (if the contract accepts, π2's
   extractor outputs π1's stream, on which π1-rec3's recorded graph over Keccak-f[1600] accepts with the contract's
   three π1 calls), `RecCompleteness2 D P1 P2 δ2`;
2. **end to end against the Keccak VM's `KvHolds` (`UniKeccak.KDeployment.Relation`), knowledge soundness as an
   explicit reduction**, `RecKnowledgeSoundnessReduction D ε2`: for every adversary `A` of `Q` queries, the break is at
   most `ε2 Q` plus the probability that `pi1Adversary D A` breaks π1-rec3 at Keccak-f[1600] plus the probability that
   `hazardAdversary D A` hits the merge hazard on a stream π1-rec3's graph accepts. The derived adversaries are `A`
   then π2's explicit extractor, of `A`'s queries. No Fiat–Shamir premise;
3. **the Prop-premise forms**: `RecKnowledgeSoundness D ε2 ε1 εh` under `Pi1FsKeccak ε1`, `Pi1HazardKeccak εh`, and
   `RecCompletenessWith` under `Pi1CompletenessKeccak δ1`, `Pi1HazardKeccakHonest δh` (`RecGraphKeccak`'s
   `Pi1GraphIsVerifierK`, the other hypothesis of `RecKnowledgeSoundness` and `RecCompleteness`, is proved:
   `RecGraphKeccak.Sim.pi1GraphIsVerifierK`). `Pi1FsKeccak` and `Pi1HazardKeccak` are **false as stated** for
   unbounded adversaries, which grind Keccak-f[1600] offline for free: read them as the Fiat–Shamir heuristic for
   adversaries of bounded Keccak-f[1600] work, motivated by π1-rec3's random-permutation theorem
   (`UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_closed`, 128.49 bits) and `RecGraphKeccak.hazard_probK`
   (`≤ 2^16/|E|`). The completeness premises are about one fixed honest prover: no adversary grinds there.

The merge hazard (`RecGraphKeccak.MergeHazardK`) asks that π1-rec3's run draw `t` (challenge 52) and that `t` be a root
of `Z_bad(p_0)` (`p_0` challenge 45), so the empty stream and every run that stops early are off it (were they on it,
`Z_bad(0) = 0` would force `εh ≥ 1`). The soundness hazard (`Pi1HazardAccepted`) also asks that π1-rec3's graph accept
the stream.

Sorry-free, no `native_decide`; the root's `#guard_msgs` checks that the headline theorems below depend on
`[propext, Classical.choice, Quot.sound]` only.

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only
systemd-run --scope -p MemoryMax=10G lake build RecCompose     # the theorems; #guard_msgs checks their axioms
systemd-run --scope -p MemoryMax=12G lake exe rec-view-check   # viewCheck at two IVs (about 14 minutes an IV)
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check   # DigestChecked, ivCheck at three IVs (RealDeployment.lean)
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check --setup-only   # SetupRootChecked
PI2_PROVER=<vectors> lake env lean ../RecCompose/RecComposeTest/Pi2Prover.lean   # π2's Lean prover against the Rust's
```

On the Keccak VM's π1-rec3 (128 signatures) every evaluated check holds: `viewCheck` at π1's reference IV and the zero
IV; `DigestChecked`, `ivCheck` at the reference, zero and all-ones IVs, `SetupRootChecked`. Each compile of the graph
takes 13–21 minutes (`rec-real-check` compiles it once for the reference circuit and once per IV), the setup root
under about 12 more; peak memory 6.7 GB. Arguments `ref`, `zero`, `ones` choose the IVs, `--no-digest` skips the
digest. These are long evaluations, not builds: run them outside the build lock. `GraphsAgree` is checked by
`RecGraphKeccakTest/Pi1Check.lean` ([`../RecGraphKeccak/README.md`](../RecGraphKeccak/README.md)). π2's Lean prover
writes the Rust prover's setup, `W` and `Q` roots and its stream byte for byte on 2/2 vectors, on the PCS claims (the
compiler's example at `2^9`, `2^10` positions, `2^15`-word stacks, `Q` sixteen slots with `1, 5, 9, 12` zero; each root
its bytes and out-of-domain answer in the `568`-byte stream; the runner also recomputes π2's IV v3 from the setup's
answer and the circuit's digest and matches the Rust's; `crates/leanvm/rec/tests/lean_pi2_prover.rs`; about 15 and
34 minutes interpreted).

## Status of the move to the PCS claims (branch `lean-pi2v3`)

π1 (`UniKeccak`, `UniKeccakSound`, `UniKeccakComplete`, `RecGraphKeccak`) and `RecStatement` state the EIP draft's PCS
claims (`RecStatement` 954a238e: eight claims `[root, ood, point…, value]`, `pcsOpenWords`, IV v3). **The base of
RecCompose builds on them**, and so do **the Fiat–Shamir layer** (`Fs*`, `GenericSetupLog`, `RealEnd`: branch
`lean-pi2v3-fs`) and **the completeness side** (`Pi2Prover*`, `Pi2Honest*`, `Pi2Whir`, `Pi2Complete*`, `Pi2Calls*`,
`Pi2Prob*`, `Pi2Sim*`, `Pi2Alpha*`, `Pi2Run{Cost,Duplex}`, `Pi2TFresh*`, `Pi2Chain`, `Pi2P1`, `Pi2Witness`, `Pi2Closed`,
`Pi1Keccak*`, `CompleteKeccakEnd`: branch `lean-pi2v3-cmp`): the whole library, its guards passing.

* **`Q`'s empty slots** (`RecPiop`, merged from `lean-pi2v3-piop`): `Q` is the plain sixteen-slot stack, slots `1, 5, 9`
  (`h`'s second digit: `h` below `2N`) and `12` (`S`) the prover's; the claims read `P(t) + S(t)/Z_V(t)` and the sum
  claim **`Σ_V (h + c_3 S) = 0`** (`RecPiop.SumOK`; `SumH`, `Σ_V h = 0`, in `Pre1`): the sum claim reads `S`'s slot with
  `h`'s top coefficient, so the earlier `Σ_V h = 0` could not be read off it. Round 1 `(4N − 1)/|F|`;
  `pi2RoundErr = 9952 · 3564 · (4 · 2^24 − 1)/2^192` (`2^-140.92`); `pi2Bound Q ≤ 2^-64` at `Q ≤ 2^64` still.
* **The openings' term** of `pi2Bound`, `N (pi2OpenErr + 5 N/2^256)`, `pi2OpenErr = 269 · 2^-137 + 2^-156`: the eight
  PCS openings charged once (`FsOps.prEvent_doomH_le`, `WhirBridge.Pcs.UnionO.pcs_union_sound_oracle` over version 1's
  sizes, as π1's `UniKeccakSound.hU_uniK`), and **`Q`'s out-of-domain binding**, proved (branch `lean-pi2v3-ood`). The
  contract reads the out-of-domain point of the claims on the proof's commitments, `W`'s and `Q`'s three, off
  Keccak-256 over `F` (`RecStatement.pcsOpenKO`, `WhirBridge.Pcs.pcsVerifyWithHashO`; `RecStatement.oodRead`: sizes
  `24`, `28`); the claims on the deployment's commitments, π1's three and π2's setup's, keep the fixed
  `WhirBridge.Pcs.oodPoint` (`UniKeccak.pcsOpenK`, one claim per commitment, the setup's answer computed by the setup).
  At the real Keccak-f[1600] both are the deployed `ood_point` (`RecStatement.pcsOpenKO_keccakF1600`). In the
  random-permutation model the point is then read off the permutation: the union splits the random oracle on the
  out-of-domain inputs of every size (`WhirBridge/PcsUnionOracle.lean`, the bound unchanged), and the chain's one
  candidate of `Q`'s root satisfying all three claims comes from `WhirBridge.Pcs.ood_binding_coords` at `n = 28`
  (`FsBind.qOodBinding`, `δBind QA = QA · δc 28 + QA (QA + 1)/2^256`, `δc 28 = C(3564, 2)/2^192 ≤ 2^-160`), the event
  read off the run's final cache (`doomFG_p2Ops_cases`, the accepting `Q` openings having asked the point:
  `PcsOp.present`). The premise `QOodBinding` is gone from `pi2FsLayer_real` and the end theorems. Each opening counts
  `10150` queries (`10122 + 28`, `FsOod.pcsVerifierO_queryBound`). `pi2Bound` is unchanged:
  `pi2Bound Q ≤ 2^-64` at `Q ≤ 2^64` (`2^-64.93` at `2^64`, 128.93 bits as `Q/ε2`).
* **The claims on the candidates** (`Layers.lean`: `ClaimOn vars stack (point, value)` is `UniSound.mleStk`, each claim a
  point of its whole stack); `W`'s witness values the stack's leading `N` words (`wVars`, `witnessOf`).
* **The honest prover** (`Pi2Prover`): the plain stacks (`padStack` to `stackVars`), `Q` with its empty slots zero (so
  the model's `h` on `m + 1` digits is the honest `h`, its high digit zero, and `S = 0`: `modelS_eq`,
  `qClaim_of_eval_sP`, the sum `Σ_V (h + c_3 S) = Σ_V h = 0`), each root sent as its bytes (`rootHalves`) with its
  out-of-domain answer (`pi2Ood`, UniKeccakComplete's `pcsOod`), five PCS openings (`pcsProveH`, accepted by
  `pi2PcsOpen_honest` at `24`, `25`, `28` variables; the setup's table padded to its stack, its commitment and answer
  unchanged: `commitWithH_padStack`, `setupOod_eq`). The contract's eight claims decode (`claimOfWords_claim`) and
  accept (`contract_accepts`); the graph's and the contract's π1 claims are the same PCS claims
  (`pi2Pi1Openings`). Counts: the contract's eight checks `openCost` each, the IV's `137` bytes, `δ2 ≤ 2^-164` as before.
* **π1's claims**: the contract opens each at its point's length, π1's verifier at `stackVarsK`; `Pi1CallsShape`
  (three claims of `stackVarsK + 3` words, `30, 29, 26`, the setup's root and answer constants) gives the lengths
  (`contract_ops`); `decodePi1Call ∘ pcsClaimWordsK` round-trips (`Pi1Decode.decodePi1Call_claim`,
  `digestOfBytes32_rootWord`).

## The end theorems

**Knowledge soundness** (`RealEnd.lean`, `FsClosed.lean`):

| Theorem | Statement | Premises |
|---|---|---|
| **`recKnowledgeSoundness_reduction_real prog hprog`** | `RecKnowledgeSoundnessReduction (realDeployment prog hprog) pi2Bound ∧ ∀ Q ≤ 2^64, pi2Bound Q ≤ 2^-64` | the evaluated checks `GraphsAgree`, `DigestChecked`, `SetupRootChecked`, `IvChecked` |
| **`recKnowledgeSoundness_reduction D`** | `RecKnowledgeSoundnessReduction D pi2Bound ∧ ∀ Q ≤ 2^64, pi2Bound Q ≤ 2^-64` | `hD : D.Real`, `C : Pi2Circuits D`, `hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt`, `GraphsAgree`, `Pi2ViewChecked C` |
| `recKnowledgeSoundness2_closed D` | `RecKnowledgeSoundness2 D pi2Bound ∧ ∀ Q ≤ 2^64, pi2Bound Q ≤ 2^-64` (π2's part) | as above |
| `recKnowledgeSoundness_closed D` | `RecKnowledgeSoundness D pi2Bound ε1 εh` | as above |
| `recKnowledgeSoundness_closed_fs D` | `RecKnowledgeSoundnessWith D (recExtractor D) fun Q ↦ pi2Bound Q + ε1 Q + εh Q` | as above, and `Pi1FsKeccak D ε1`, `Pi1HazardKeccak D εh` (false as stated, above) |
| `pi2Bound_le_bits` (`Numbers.lean`) | `pi2Bound Q ≤ 2^-64` for `Q ≤ 2^64` | none |

`realDeployment_real`, `pi2Circuits_real`, `pi2ViewChecked_real` (`RealDeployment.lean`) build `D.Real`, `C` (with
`hroots` by `rfl`) and `Pi2ViewChecked C` for `realDeployment prog hprog` from the four evaluated checks.

**Completeness** (`CompleteKeccakEnd.lean`, namespace `RecCompose.Pi1K`), at the recursion's concrete π1-rec3 prover
`pi1Rec3ProverK D` (UniKeccakComplete's π1-rec3 prover with its Fiat–Shamir the pure `keccak256`, over the real
Keccak-f[1600] as π1-rec3's graph hashes it, its trees and PCS openings over `π`) and π2's Lean prover `pi2Prover`:

| Theorem | Statement | Premises |
|---|---|---|
| **`recCompleteness_real_K_fs_bits prog hprog`** | `RecCompletenessWith D (composeProver D (pi1Rec3ProverK D) (pi2Prover D …)) (δ1 + δh + 2^-164)`, `D = realDeployment prog hprog` | the four evaluated checks; `Pi1CompletenessKeccak D (pi1Rec3ProverK D) δ1`, `Pi1HazardKeccakHonest D (pi1Rec3ProverK D) δh` |
| `recCompleteness_real_K_fs`, `recCompleteness_pi2_rec3_K_fs` | the same with `δ2` unevaluated, at `realDeployment`, resp. at any `D` | as above, resp. `hD`, `C`, `hroots`, `GraphsAgree`, `Pi2ViewChecked C` and the two premises |
| **`recCompleteness2_pi2_rec3_K`** | `RecCompleteness2 D (pi1Rec3ProverK D) (pi2Prover …) δ2`, `δ2 ≤ 2^-164` (`Pi2Alpha.delta2_alpha_le`) (π2's part) | `hD`, `C`, `hroots`, `GraphsAgree`, `Pi2ViewChecked C` |
| `pi1ProverFactsK` | `Pi1ProverFacts D (pi1Rec3ProverK D) (p1kK D)`: `Pi1OverPerm`, `Pi1Disc`, `Pi1Cost` (`≤ 2^47` blocks), `Pi1HashShort` (inputs `< 2^26` bytes) | `hD` |
| `pi1CompletenessKeccak_iff` (`Pi1KeccakRpm.lean`) | `Pi1CompletenessKeccak D (pi1Rec3ProverK D) δ ↔ Pi1CompletenessFs D (fun s ↦ pure (keccakF1600 s)) δ` | none |
| `pi1CompletenessFs_rpm` (`Pi1KeccakRpm.lean`) | `Pi1CompletenessFs D queryPermutation Prob.deltaK` (`deltaK < 2^-169`): the first premise's random-permutation reading, from `UniKeccakComplete.uniCompletenessKeccakRec3_closed` | `hD` |

`Pi1HazardKeccakHonest`'s random-permutation reading is not proved: it is motivated only by `hazard_probK`, a count
(`2^-176` for a uniform `t`), not a game. The generic forms are kept: `Pi2Alpha.recCompleteness2_pi2_rec3_closed`,
`Pi2Alpha.recCompleteness_pi2_rec3_closed_fs` (`Pi2AlphaEnd.lean`, for any π1-rec3 prover `P1` with its two-call
program `P1k` and `Pi1ProverFacts D P1 P1k`), and `recCompleteness_end_fs` (`End.lean`, from any `RecCompleteness2`).

## The Keccak VM

The library at the Keccak VM:
- π1 is `UniKeccak`'s verifier at `keccakRec3`, on `RecGraphKeccak.Pi1.keccak128` (`= UniKeccakSound.keccakRefShape`,
  `Pi1K.keccak128_eq_refShape`).
- π1-rec3's recorded graph is `RecGraphKeccak.Pi1.pi1GraphK` (`RecGraphKeccak.Emitted`), at the reference setup roots
  `RecGraphKeccak.Pi1.referenceRootsK`. Every file reads them through `RecCompose.keccakRefRoots` (`realRoots` in
  `RealDeployment`).
- π2's circuit is `RecStatement.Data`, emitted by `crates/leanvm/rec/tests/lean_statement_keccak.rs`.
- The relation is `KvHolds` at `D.flock`; `Real` pins `D.flock = KeccakFlock.keccakFlockSpec`.
- **π1's setup is one tree.** `A0` and `B0` are the deployment's constants, so π2's Fiat–Shamir family holds π1's
  `2^27`, `2^26` and `2^23` openings. The `2^23` one is certified by `UniKeccakSound.plainShapeE23`.
- `GenericSetupLog.lean` holds the four VM-generic lemmas of the logged setup.

## Files

| File | What |
|---|---|
| `Basic.lean` | π2's outcome's fields; `keccakRefRoots : SetupRootsK`; `W`'s stack variables `wVars`, its candidates and their witness values (the stack's leading `N` words) as π2's extractor reads them; `pi1GraphAcceptsB_iff`; `recExtractFrom2_of_mem` (one accepted candidate suffices). |
| `Part1.lean` | `CallsPure` (the contract's first three claims decode to `pi1OpsOf`), `Pi2Extraction`, `Pi2Layers`; **`recKnowledgeSoundness2_of_layers`**. |
| `Circuit.lean` | `GraphsAgree`; `Pi2Layers.circuit` from `RecGraphKeccak.pi1rec3K_end` and `CircuitBridge`; `compile_ok` from the compiler's run on the emitted graph and `GraphsAgree`; `Pi1RootWordOk` (the root-word fix's named dependence). |
| `Numbers.lean` | **`pi2Bound`** (`ε2`; the openings' constant `pi2OpenErr = 269 · 2^-137 + 2^-156`: `pcs_union_sound`'s per-group bound and `Q`'s binding), `pi2RoundErr` (`(4N − 1)` over `L_W L_Q`, `2^-140.92`), `pi2_rounds_le`, **`pi2Bound_le_bits`**. |
| `Part2.lean` | the three events (`HazardEvent` on `Pi1HazardAccepted`), `ExperimentsAgree`, `HazardCoupling`, `Pi1Coupling`, `breaks_cases`; **`recKnowledgeSoundnessReduction_of_part1`** (the reduction), `recKnowledgeSoundness_of_reduction`, **`recKnowledgeSoundness_of_part1`**. The derived adversaries are `RecStatement/Reduction.lean`'s. |
| `Complete.lean` | `CompletenessAgree`, `CompletenessPi1Coupling`; **`recCompleteness_of_part1`**. |
| `Layers.lean` | `Pi2FsLayer` (π2's Fiat–Shamir layer), `Pi2Tables` (the tables' layer, proved in `Tables.lean`), `Pi2Circuits`, `Pi2Facts`; `ClaimOn` (a PCS claim of a stack, `mleStk`), `Pi2ClaimsHold` (the five claims on `stackVars`); `pi2Piop`, `hbind_of`, `indep_K`, `satisfies_congr`; **`pi2Extraction_of_layers`**, `pi2Layers_of`. |
| `Holds.lean`, `Chan.lean`, `Pi2Run.lean`, `CallsPure.lean` | postconditions in any lawful monad (`Holds`), the channel's reads (`Reads`), π2's run's public data independent of the permutation (`runWith_post`); **`callsPure`**. |
| `Rpm.lean`, `Couplings.lean` | the logging lemmas, eager comparisons per permutation; `openAt` (`pcsOpenK` at the point's length), `openSeq`; **`experimentsAgree`**, **`hazardCoupling`**, **`pi1Coupling`** (under `Pi1OpeningsAgree`; `loop_le` over the eight openings). |
| `OpeningsAgree.lean`, `RunOpenings.lean` | `Pi1CallsShape` (word counts `stackVarsK + 3`, the setup's two constants), `contract_ops`, **`pi1OpeningsAgree`** (from `pi1RunShape`, `pi1RunOpenings`, `pi1CallsShape_data`), **`pi1RunOpenings`**. |
| `RpmC.lean`, `Pi1Decode.lean`, `CompleteCouplings.lean`, `RunShape.lean` | eager comparisons, π1's claim words decoded back (`decodePi1Call_claim`, `claimOfWords_length`, `digestOfBytes32_rootWord`, `decode_pcsClaimWordsK`); **`completenessAgree`**, **`completenessPi1Coupling`**, **`pi1RunShape`**. |
| `Tables.lean`, `Real.lean` | **`pi2Tables`** (the tables' layer on `Q`'s plain sixteen-slot stack: `h` on `m + 1` digits, `S` slot `12`; claims of the whole stacks, `mleStk_eq`), `cells_wFold`, `claim_wFold`, `claim_quotient`, `claim_pushes`, `claim_sum`, `claim_setup`, `sum_novP_omega`, `novP_succ_eval_omega`; `pi2SetupColumns_of_real`. |
| `Bridge.lean` | **`circuitBridge`** (from `StatementPortMeaning`, `ZeroPortsMeaning`, `CallWordsAgree`; the claims by `claimOfWords`: `C1`, `C2` word for word, the setup from word `2` on, `claimOfWords_tail`, `emitted_setup_ood`). |
| `End.lean` | `recKnowledgeSoundness2_real`, `recKnowledgeSoundnessReduction_end`, `recKnowledgeSoundness_end`, `recKnowledgeSoundness_end_real`, `recCompleteness_end`, `recKnowledgeSoundness_end_fs`, **`recCompleteness_end_fs`**: the end statements from named layers. |
| `ViewDefs.lean`, `View.lean` | **`viewOf`** (`pi2::adapt` transcribed), `callsOf`, `validB`, **`viewCheck`** (evaluated by `rec-view-check`, `RecComposeTest/ViewCheck.lean`); the slots, `groupsOf_perm`, `groupsOf_mem`. |
| `Valid.lean` | **`validB_sound`**: `validB` gives `RecPiop.Circuit.Valid` of `toPiop`. |
| `FactsAlg.lean`, `FactsSpec.lean`, `FactsSpecOf.lean` | the formulas' and terms' values, `pubOfC`; `Data`'s facts by kernel decision; **`specOf_data`**. |
| `Facts.lean` | `Pi2ViewChecked`; **`pi2Facts`** (`Pi2Facts D C`), `pubOfC_canon`, `pi2Facts_pubOf`. |
| `IvLength.lean` | **`RecDeployment.pi1IvAt_length`**: π1's contract IV has 32 bytes (a Keccak-256 digest); the per-IV premises are stated at 32-byte IVs and reach `pi1IvAt` through it (`Pi2Circuits.compile_okAt`, `stream_eqAt`). |
| `RealDeployment.lean` | **`realDeployment prog hprog`** (σ, κ the Lean compiler's at every IV, π1's stream its `streamW`), `DigestChecked`, `SetupRootChecked`, `IvChecked`, **`realDeployment_real`** (`Real`, from `GraphsAgree`, `DigestChecked`, `SetupRootChecked`), **`pi2Circuits_real`**, **`pi2ViewChecked_real`** (from `GraphsAgree`, `IvChecked`); `ivCheck` (compile, `viewCheck`, `streamAgree`), `streamW_eq_of_streamAgree`. Why IV uniformity is not proved: the module docstring. |
| `IvUniform.lean` | **`ivChecked_of_patchChecked`**: `IvChecked` from `PatchChecked` (the compiler's IV factorization, **not proved**) and `ivCheck` at the all-ones and zero IVs (evaluated); `viewCheck_patch`, `streamAgree_patch`. |
| `Meanings.lean` | **`statementPortMeaning`**, **`zeroPortsMeaning`**, **`callWordsAgree`** for `pi2Facts`. |
| `Layouts.lean` | **`pi1CallsShape_of_real`** (the layout-word check is gone with the layout words). |
| `Final.lean` | `recKnowledgeSoundness2_final`, `recKnowledgeSoundnessReduction_final`, `recKnowledgeSoundness_final`, `recKnowledgeSoundness_final_fs`: the end theorems from the named inputs left. |
| `FsOod.lean` | π2's `W` and `Q` openings with the point read off Keccak-256 (`pcsOpenCO`, `pcsVerifierO`): **`pcsOpenKO_eq`** (the contract's `pcsOpenKO` over `π`), `pcsVerifierO_queryBound` (`10150`), `duplexVm_pcsVerifierO`, `allQ_pcsVerifierO`, `simulateQ_pcsVerifierO`. |
| `FsDefs.lean` | π2's Fiat–Shamir layer's objects: the chain `pi2Spec` (the label `name ‖ iv ‖ input`, the public data's 520 bytes before `W`'s root), the proof `P2Pf` (the setup's commitments `RecSetupRoots` as the setup's output) and its view, **the eight PCS openings** `p2Pcs` (`PcsOp`: `pcsOpenC` on `plainShapeK n` as a `Compose.GOp`), the composition's six `p2Ops` (`Q`'s three as one, `qOp`), the setup's stacks `p2Stk`, the composed setup `p2Setup` (`setupOut`: the roots with their out-of-domain answers), the IV `p2IvKC4` (v3), the composed verifier `p2Ver`, the bridge facts' Props. |
| `FsOps.lean`, `FsBind.lean`, `FsBytes.lean` | the openings' `OKP`, coverage, `hS_p2` (the setup's claim), a PCS claim's point claim as `ClaimOn` (`colEval_iff_claimOn`), **`prEvent_doomH_le`** (any `PcsOp`s charged once through `WhirBridge.Pcs.UnionO.pcs_union_sound_oracle` over `UniKeccakSound.pcsKShapes`, the doom `PcsOp.DoomedH` read off the final cache), `gopsRun_p2Ops`, `maxErrK_p2`; `Q`'s binding: **`qOodBinding`** (from `ood_binding_coords`), `doomFG_p2Ops_cases`, `PcsOp.present`, **`prEvent_doomFG_p2Ops_le`**; a digest's and an element's words read back. |
| `FsSetup.lean`, `FsExtract.lean`, `FsWalk.lean`, `GenericSetupLog.lean` | **`pi2SetupBridge`** (the setup's output the trees' commitments), the setup's facts and `okp_setupOp`; **`pi2ExtractBridge`** (`W`'s decoder `tableCode` of the plain `2^24`, roots as their bytes); **`pi2Walk`** (π2's run is the chain), **`pi2WalkReject`**, `pi2Scalars_real`; the logged plain tree (`simulateQ_loggedKC_stackSetupS`). |
| `FsVerifier.lean`, `FsCouple.lean`, `FsCost.lean` | **`pi2VerifierBridge`** (the contract's eight claims, decoded by `claimOfWords`, are the eight composed openings answered over `π`), **`pi2GameLeV`** (the coupling), the composed verifier's cost (`2^49` calls of `π`), the IV moved into the adversary (`expU_p2IvAdv`), `hlab_p2`. |
| `FsGame.lean`, `FsClosed.lean` | **`pi2FsLayer_of`** (through `Compose.knowledgeSoundness_listChainU_closed128SG`, `prEvent_doomFG_p2Ops_le`, `prEvent_pairTr_expLG_le`, `le_pi2BoundE`); **`pi2FsLayer_real`** (no premise); **`recKnowledgeSoundness_reduction`**, **`recKnowledgeSoundness2_closed`**, **`recKnowledgeSoundness_closed`**, **`recKnowledgeSoundness_closed_fs`**. |
| `RealEnd.lean` | **`recKnowledgeSoundness_reduction_real`**: `recKnowledgeSoundness_reduction` at `realDeployment prog hprog`, from the four evaluated checks. |
| `Pi2Prover.lean`, `Pi2ProverRun.lean` | **π2's honest prover** (`prover.rs` phase by phase: `pi2ProveStreamWith`, `pi2ProveWith`, over any Keccak-256 `H`), on the PCS claims: the plain stacks (`padStack` to `stackVars`; `Q` sixteen slots, `1, 5, 9, 12` zero), each root sent as its bytes (`rootHalves`) with its out-of-domain answer (`pi2Ood`), five openings (`pcsProveH`, one a claim); `pi2ProveStreamWith_holds`, `pi2ProveStreamWith_claims` (the stacks and inputs its run leaves). |
| `Pi2HonestBase.lean`, `Pi2HonestCopy.lean`, `Pi2HonestQ.lean`, `Pi2Honest.lean`, `Pi2HonestMain.lean`, `Pi2HonestThm.lean`, `Pi2HonestCount.lean` | the honest prover's algebra on the plain stacks (`honestW`, `honestQ`: `padStack`; `readW_honest`, `readQ_honest`, `sCoef_honest`): transforms and coset, the copy argument's sum, `q` on the extension coset (its degree below `2N`, `natDegree_numPoly_le`); `modelH_eq` (`h` on `m + 1` digits, the high one zero), `modelS_eq` (`S = 0`); **`pi2_honest`** (off `BadCopy`, `BadT` the check passes and the five claims hold, `Pi2ClaimsHold`), `pi2_honest_post2` (`qClaim_of_eval_sP`), `claims_of_model` (`mleStk`); `card_badCopy_le`, `card_badT_le`. |
| `Pi2Whir.lean`, `Pi2CompleteCalls.lean`, `Pi2CompleteH.lean`, `Pi2CompleteSync.lean`, `Pi2Complete.lean` | honest PCS openings at π2's stacks (`pi2PcsOpen_honest`, `pi2PcsOpen_fails_only_at_pow`; `commitWithH_padStack`, `setupOod_eq`); a PCS claim's words decoded (`claimOfWords_claim`, `rootOfWord_rootWord_rootHalves`); the verifier, contract and setup with Keccak-256 an explicit `H` (`…_eqH`); the verifier reads what the prover writes (`runWith_honest`); **`contract_accepts`** off the bad challenges, at one permutation (eight claims; `StackClaimsHold`). |
| `Pi2CompleteEnd.lean`, `Pi2Witness.lean`, `Pi2CallsOpen.lean` | **`pi2Prover`**, `Pi2WitnessComplete`, `delta2`, `recCompleteness2_pi2`; **`pi2WitnessComplete`** (on a stream π1-rec3's graph accepts, RecCircuit's honest witness and `valuesOf` are an honest witness); `pi2_accepts` (`stackClaims_of_pi2Claims`: `mleStk` to `stackEval`; the setup's padded table); **`pi2Pi1Openings`** (the contract's π1 claims on π2's honest proof decode, `claimOfWords_elems`, and are the graph's PCS claims), `recCompleteness2_pi2_closed`. |
| `Pi2P1.lean` | **π1-rec3's prover as π2's completeness takes it**: `P1 : Pi1Prover D`, its two-call program `P1k : Pi1ProverK D`, and the four named facts `Pi1OverPerm`, `Pi1Disc`, `Pi1Cost`, `Pi1HashShort`, bundled as `Pi1ProverFacts D P1 P1k` (discharged for the concrete prover by `Pi1K.pi1ProverFactsK`). |
| `Pi2Prob.lean`, `Pi2ProbStaged.lean` | π2's challenges in the random-oracle model, `recCompleteness2_of_staged`; the staged experiment `pi2Staged` (stages A, B, C; stage C the five PCS openings), `PcsFails` (a PCS opening failing at its proof of work, `one_le_powPot_of_pcs_none`), `Pi2ExperimentLe`, `Pi2RunDuplex`, `Pi2RunCost`, `Pi2TFresh`, `recCompleteness2_pi2_staged`. |
| `Pi2SimMorph.lean`, `Pi2SimAt.lean`, `Pi2SimExp.lean`, `Pi2SimCore.lean` | π2's code commutes with monad morphisms (`sim_expW2`, `sim_stageA/B/C`); `stagedAt_good`; **`pi2ExperimentLe_of`** (from `Pi1OverPerm`); **`rejectGood_pi2_good`**. |
| `Pi2Chain.lean`, `Pi2TFresh.lean`, `Pi2TFreshPi2.lean`, `Pi2RunDuplex.lean`, `Pi2RunCost.lean` | `Holds2`, `recCompleteness2_of_staged2`, `delta2'`; **`pi2TFresh_of`**; **`pi2RunDuplex_of`** (from `Pi1Disc`), **`pi2RunCost_of`** (from `Pi1Cost`; `pi2RunN ≤ 2^50`: the contract's eight checks `openCost` each, the prover's five `cost_pcsProveH`, the IV's `137` bytes). |
| `Pi2SimEnd.lean`, `Pi2Closed.lean` | the earlier forms with `hal : Pi2AlphaFresh εα` (`recCompleteness2_pi2_rec3_final`, `delta2_rec3_le`). |
| `Pi2AlphaLen.lean`, `Pi2AlphaChain.lean`, `Pi2AlphaSupport.lean`, `Pi2AlphaG.lean`, `Pi2AlphaFresh.lean`, `Pi2AlphaEnd.lean` | **`α`'s freshness**: nothing of `2^26` bytes is hashed before π2's IV (the setup's trees, the graph; π1's prover by `Pi1HashShort`), the chain from `σ`'s hash (the IV's `137` bytes, the digest at `104`), `hashOK_pcsProveH`, freshness conditioned on the graph's acceptance (`Holds3`), **`alphaFresh_of`** (`alphaBound ≤ 2^-204`); **`Pi2Alpha.recCompleteness2_pi2_rec3_closed`**, **`recCompleteness_pi2_rec3_closed_fs`**, **`delta2_alpha_le`** (`δ2 ≤ 2^-164`), for any `P1` with `Pi1ProverFacts`. |
| `Pi1KeccakProver.lean`, `Pi1KeccakTransfer.lean`, `Pi1KeccakCensus.lean` | **the concrete π1-rec3 prover** `pi1Rec3ProverK D` (`pi1ProverFs hKF D`, `hKF x = pure (keccak256 x)`) and `p1kK`, `pi1Rec3ProverK_eq` (its setup commitment in the IV, its openings `pcsProveH`); its facts transferred from UniKeccakComplete's two-call prover (`disc_p1kK`, `qc_p1kK`); its hash census (`hashShort_p1kK`). |
| `Pi1KeccakRpm.lean` | `pi1VerifierFsWith`, `verifierFs_eq`, `pi1KeccakVerifierWith_kf_eq`; `pi1FsCompletenessExperiment D Φ`, `Pi1CompletenessFs`; **`pi1CompletenessKeccak_iff`**, **`pi1CompletenessFs_rpm`**. |
| `CompleteKeccakEnd.lean` | **`pi1ProverFactsK`**, **`recCompleteness2_pi2_rec3_K`**, `recCompleteness_pi2_rec3_K_fs`, `recCompleteness_real_K_fs`, **`recCompleteness_real_K_fs_bits`**. |

## The statements' fixes (in `RecStatement/Security.lean`, found by this composition)

1. **π2's extractor searches by the whole acceptance.** It searched `W`'s list for the first candidate whose π1
   stream passes the graph's checks. A word within the list-decoding radius of two codewords (rate `1/2`: both within
   Johnson's `0.29`, the first within `1/4`, so the unique decoder lists it first) can make that candidate's stream an
   honest π1 proof of another transcript while the openings' claims hold of the second: the extractor would output a
   stream whose calls are not the contract's, and `RecKnowledgeSoundness2` would fail. It now searches by
   `pi1GraphAcceptsB` against the contract's π1 openings read off the calldata (`pi1OpsOf`).
2. **The derived π1 adversaries are given the setup's evaluations.** π2's extractor reads them. With the roots alone,
   the adversary built from π2's must recompute the setup: `ε1` would be charged at its `2^27` and more extra calls, not
   at `Q`, and π1-rec3's extractor would read a transcript that holds them, not π2's adversary's.
3. **π2's completeness is for π1-rec3's prover, on honest statements.** Stated for every `P1`, a `P1` of unbounded
   queries can grind its proof (the graph still accepting) until π2's honest run hits a degenerate challenge (`all = 0`).

In the proof, `α`'s freshness is asked only where π1-rec3's graph accepted (`Pi2AlphaG`'s `Holds3`): elsewhere `α`'s
input is `fixLen`'s `536` zeros, which nothing keeps π1-rec3's prover from hashing, and those outcomes are rejected.

## The root-word finding

π2's stream carries π1's `C1`, `C2` roots as `rootWordOfBytes` of π1's stream bytes (each 16-byte half reversed). The
contract decoded that word to `digestOfBytes32 raw`, while π1-rec3's verifier and WHIR open at `rootOf (halves raw) =
rootOfWord raw`, so `Pi1GraphAccepts`'s roots disagreed on honest proofs. The fix (`fix-pi1-root`, merged at
`leanvm-rec` 613b2fa) is in π1's prover: it writes each root as its root word (`hash_to_scalars`), as π2's prover and
the Lean honest provers do. `RecCircuit.pcsWord` passes stream roots as they are, so `Pi1RootWordOk` is
`pi1RootWordOk` (`rfl`).

## Remaining

1. **The model gap.** π2's circuit computes π1-rec3's Fiat–Shamir with the real Keccak-f[1600]; π1-rec3's theorems are
   in the random-permutation model. So the soundness reduction's last two terms (π1-rec3's experiment for
   `pi1Adversary D A`, the hazard's for `hazardAdversary D A`, both at Keccak-f[1600]) and the two completeness premises
   (`Pi1CompletenessKeccak`, `Pi1HazardKeccakHonest`) are not bounded in Lean: the Fiat–Shamir heuristic for
   Keccak-f[1600]. The first completeness premise's random-permutation reading is proved (`pi1CompletenessFs_rpm`);
   the second's is not.
2. **The evaluated checks** `GraphsAgree`, `DigestChecked`, `SetupRootChecked` and `IvChecked`'s three instances are
   Props checked by running Lean (`Pi1Check.lean`, `rec-real-check`, `rec-view-check`), not kernel proofs.
3. **`IvChecked`** is evaluated at the reference, zero and all-ones IVs and assumed at the other 32-byte IVs.
   `ivChecked_of_patchChecked` reduces it to `PatchChecked` (every IV's compile is the all-ones IV's with `κ` removed at
   the IV's zero bits' seed positions), which is not proved: it needs a relational simulation of the builder
   (`compileM`, the templates and `finish`, about 1,200 lines of monadic code; `RealDeployment.lean`'s docstring).
4. **The provers.** The completeness theorems are about the Lean provers. The deployed Rust provers are trusted for
   completeness: π2's Lean prover is compared with the Rust's on two small circuits (`RecComposeTest/Pi2Prover.lean`),
   UniKeccakComplete's π1-rec3 prover has no differential runner.
