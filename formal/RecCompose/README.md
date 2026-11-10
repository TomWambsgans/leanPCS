<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# RecCompose: the recursive verifier's end theorems

The recursive EVM verifier for the Keccak VM's proofs (leanVM 9d50c92a3's `SHA3` table, the 128-signature reference;
`crates/leanvm/rec`): the contract runs π2's verifier, then checks six claims declared (π1's `C1`, `C2`, `F`; π2's
`W`, the setup, `Q`). Its statements are `RecStatement`'s (`RecStatement/Security.lean`, `Reduction.lean`;
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
writes the Rust prover's setup, `W` and `Q` roots and its stream byte for byte on 2/2 vectors (the compiler's example at
`2^9`, `2^10` positions; `crates/leanvm/rec/tests/lean_pi2_prover.rs`).

## Status of the move to π2v3 (branch `lean-pi2v2`, on `c61d42e1`)

The Rust's π2 is **π2v3** (`PI2.md` §2: π2v2's PIOP, the ports out of the copy argument by `T` and `Φ_k`, `P`
committed in `Q` with its definition, `q` below `2N`; on the EIP's PCS claims: each commitment its root and
out-of-domain answer, `Q` sixteen slots, its claims the identity's, the pushes' after `ρ`, the sum). **The whole
leanVM line builds on π2v3** (sorry-free, the guards pass), the end theorems now about π2v3:

* **`RecPiop`**: logUp with poles, the copy argument over the internal positions and the ports by `T`
  (`(4N − 1 + Σ_j d_j)/|F|`), both identities below `3N` (`(3N − 1)/|F|`), `Q`'s identity and pushes' claims (round 2
  `2^r/|F|`); `qClaim_of_eval` (completeness).
* **`RecStatement`**: π2v3's verifier (`Φ_k` by rows from `Data.holes`, the inversion with `B`, `Q`'s three claims on
  sixteen slots, `m + 4` variables, the out-of-domain answers read after each root, `s` among the values).
* **`RecCompose`**: `pi2RoundErr = 2^-141.33`, `pi2Bound` unchanged (128.93 bits as `Q/ε`); the tables' layer on
  sixteen slots; the Fiat–Shamir layer on the `1016`-byte stream (`W`'s root at `472`, `Q`'s at `528`, each with its
  answer; `Q`'s call of three claims, `28` variables); the honest prover (`Pi2Prover`: `h` zero at the holes, `P` and
  `q_P`, the `2N` coset, `Φ` by the verifier's `phiAt`, the answers by `pi2Ood`) and its algebra (`KCircuit`: `q_P` in
  `K`; `pi2_honest`); the bad challenges `2N |E|²` and, for a witness, `9N` points `t`; the completeness chain at `α`'s
  `560`-byte input, `t`'s `88`-byte input, contract counts at most `3`. `delta2 ≤ 2^-164` as before.
* **The data**: `Data.lean` is `f1e33516`'s circuit with its holes (`36` public terms, `17` elements), `Emitted.lean`
  `7eac7544`'s, the π1 these Lean statements of π1 describe (main's π1 is on the EIP's claims; `UniKeccak` is not yet).

**Not done**: (1) the openings switch (one `WhirBridge.Pcs` opening per claim, the IV of the PCS claims, the setup's
answer in the IV, the union bound over lists dropped by `ood_binding_rom`): the openings keep `formal/`'s layout-word
interface, and the out-of-domain answers are read but checked by nothing; (2) `Q`'s layout is `quotientChunks`' twelve
slots, the empty slots forced zero by the read, while the Rust commits the plain sixteen-slot stack: with plain
openings the empty slots are the prover's, and the soundness argument must allow them (`h` of degree below `2N`,
`P`'s digit `0`), or the Rust must constrain them; (3) so the honest prover's `Q` stack is not the Rust's and
`lean_pi2_prover`'s vectors are not regenerated; (4) rebasing onto π1 on the EIP's claims (main's `Data.lean` and
`Emitted.lean`).

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
Keccak-f[1600] as π1-rec3's graph hashes it, its trees and WHIR openings over `π`) and π2's Lean prover `pi2Prover`:

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
| `Basic.lean` | π2's outcome's fields; `W`'s candidates and their witness values as π2's extractor reads them; `pi1GraphAcceptsB_iff`; `recExtractFrom2_of_mem` (one accepted candidate suffices). |
| `Part1.lean` | `CallsPure`, `Pi2Extraction`, `Pi2Layers`; **`recKnowledgeSoundness2_of_layers`**. |
| `Circuit.lean` | `GraphsAgree`; `Pi2Layers.circuit` from `RecGraphKeccak.pi1rec3K_end` and `CircuitBridge`; `compile_ok` from the compiler's run on the emitted graph and `GraphsAgree`; `Pi1RootWordOk` (the root-word fix's named dependence). |
| `Numbers.lean` | **`pi2Bound`** (`ε2`), `pi2_rounds_le` (RecPiop's three rounds times their lists, at most `2^-140.60`), **`pi2Bound_le_bits`**. |
| `Part2.lean` | the three events (`HazardEvent` on `Pi1HazardAccepted`), `ExperimentsAgree`, `HazardCoupling`, `Pi1Coupling`, `breaks_cases`; **`recKnowledgeSoundnessReduction_of_part1`** (the reduction), `recKnowledgeSoundness_of_reduction`, **`recKnowledgeSoundness_of_part1`**. The derived adversaries are `RecStatement/Reduction.lean`'s. |
| `Complete.lean` | `CompletenessAgree`, `CompletenessPi1Coupling`; **`recCompleteness_of_part1`**. |
| `Layers.lean` | `Pi2FsLayer` (π2's Fiat–Shamir layer, proved in `FsClosed.lean`), `Pi2Tables` (the tables' layer, proved in `Tables.lean`), `Pi2Circuits`, `Pi2Facts`; `pi2Piop`, `hbind_of`, `indep_K`, `satisfies_congr`; **`pi2Extraction_of_layers`**, `pi2Layers_of`. |
| `Holds.lean`, `Chan.lean`, `Pi2Run.lean`, `CallsPure.lean` | postconditions in any lawful monad (`Holds`), the channel's reads (`Reads`), π2's run's public data independent of the permutation (`runWith_post`); **`callsPure`**. |
| `Rpm.lean`, `Couplings.lean` | the logging lemmas, eager comparisons per permutation; **`experimentsAgree`**, **`hazardCoupling`**, **`pi1Coupling`** (under `Pi1OpeningsAgree`). |
| `OpeningsAgree.lean`, `RunOpenings.lean` | **`pi1OpeningsAgree`** (from `pi1RunShape`, `pi1RunOpenings`, `pi1CallsShape_data`), **`pi1RunOpenings`**. |
| `RpmC.lean`, `Pi1Decode.lean`, `CompleteCouplings.lean`, `RunShape.lean` | eager comparisons, π1's call bytes decoded back; **`completenessAgree`**, **`completenessPi1Coupling`**, **`pi1RunShape`**. |
| `Tables.lean`, `Real.lean` | **`pi2Tables`** (the tables' layer, from `Pi2SetupColumns`), `cells_wFold`, `claim_wFold`, `claim_quotient`, `claim_sum`, `claim_setup`, `sum_novP_omega`; `pi2SetupColumns_of_real`. |
| `Bridge.lean` | **`circuitBridge`** (from `StatementPortMeaning`, `ZeroPortsMeaning`, `CallWordsAgree`, `Pi1CallsLayouts`). |
| `End.lean` | `recKnowledgeSoundness2_real`, `recKnowledgeSoundnessReduction_end`, `recKnowledgeSoundness_end`, `recKnowledgeSoundness_end_real`, `recCompleteness_end`, `recKnowledgeSoundness_end_fs`, **`recCompleteness_end_fs`**: the end statements from named layers. |
| `ViewDefs.lean`, `View.lean` | **`viewOf`** (`pi2::adapt` transcribed), `callsOf`, `validB`, **`viewCheck`** (evaluated by `rec-view-check`, `RecComposeTest/ViewCheck.lean`); the slots, `groupsOf_perm`, `groupsOf_mem`. |
| `Valid.lean` | **`validB_sound`**: `validB` gives `RecPiop.Circuit.Valid` of `toPiop`. |
| `FactsAlg.lean`, `FactsSpec.lean`, `FactsSpecOf.lean` | the formulas' and terms' values, `pubOfC`; `Data`'s facts by kernel decision; **`specOf_data`**. |
| `Facts.lean` | `Pi2ViewChecked`; **`pi2Facts`** (`Pi2Facts D C`), `pubOfC_canon`, `pi2Facts_pubOf`. |
| `IvLength.lean` | **`RecDeployment.pi1IvAt_length`**: π1's contract IV has 32 bytes (a Keccak-256 digest); the per-IV premises are stated at 32-byte IVs and reach `pi1IvAt` through it (`Pi2Circuits.compile_okAt`, `stream_eqAt`). |
| `RealDeployment.lean` | **`realDeployment prog hprog`** (σ, κ the Lean compiler's at every IV, π1's stream its `streamW`), `DigestChecked`, `SetupRootChecked`, `IvChecked`, **`realDeployment_real`** (`Real`, from `GraphsAgree`, `DigestChecked`, `SetupRootChecked`), **`pi2Circuits_real`**, **`pi2ViewChecked_real`** (from `GraphsAgree`, `IvChecked`); `ivCheck` (compile, `viewCheck`, `streamAgree`), `streamW_eq_of_streamAgree`. Why IV uniformity is not proved: the module docstring. |
| `IvUniform.lean` | **`ivChecked_of_patchChecked`**: `IvChecked` from `PatchChecked` (the compiler's IV factorization, **not proved**) and `ivCheck` at the all-ones and zero IVs (evaluated); `viewCheck_patch`, `streamAgree_patch`. |
| `Meanings.lean` | **`statementPortMeaning`**, **`zeroPortsMeaning`**, **`callWordsAgree`** for `pi2Facts`. |
| `Layouts.lean` | **`pi1CallsLayouts_of_real`** (`stackLayout_words`). |
| `Final.lean` | `recKnowledgeSoundness2_final`, `recKnowledgeSoundnessReduction_final`, `recKnowledgeSoundness_final`, `recKnowledgeSoundness_final_fs`: the end theorems from the named inputs left. |
| `FsDefs.lean` | π2's Fiat–Shamir layer's objects: the chain `pi2Spec` (the label `name ‖ iv ‖ input`, the public data's 472 bytes before `W`'s root), the proof `P2Pf` and its view, the six openings `p2Ops`, the setup's stacks `p2Stk`, the composed setup `p2Setup`, the IV `p2IvKC4`, the composed verifier `p2Ver`, the bridge facts' Props. |
| `FsOps.lean` | the openings' `OKP`, coverage, `hS_p2` (the setup's claim), `ClaimOn` as F2's `tableEval` on public layouts, the shapes at once (`p2Shapes`, with `UniKeccakSound.plainShapeE23`), `maxErrK_p2`. |
| `FsSetup.lean`, `FsExtract.lean`, `FsWalk.lean`, `GenericSetupLog.lean` | **`pi2SetupBridge`**, the setup's facts and `okp_setupOp`; **`pi2ExtractBridge`**; **`pi2Walk`** (π2's run is the chain), **`pi2WalkReject`**, `pi2Scalars_real`; the logged plain tree (`simulateQ_loggedKC_stackSetupS`). |
| `FsVerifier.lean`, `FsCouple.lean`, `FsCost.lean` | **`pi2VerifierBridge`** (the contract's six calls below the composed openings), **`pi2GameLeV`** (the coupling), the composed verifier's cost, the IV moved into the adversary (`expU_p2IvAdv`), `hlab_p2`. |
| `FsGame.lean`, `FsClosed.lean` | **`pi2FsLayer_of`** (through `Compose.knowledgeSoundness_listChainU_closed128S`, `prEvent_doomF_le`, `prEvent_pairTr_expL_le`, `le_pi2BoundE`); **`pi2FsLayer_real`**; **`recKnowledgeSoundness_reduction`**, **`recKnowledgeSoundness2_closed`**, **`recKnowledgeSoundness_closed`**, **`recKnowledgeSoundness_closed_fs`**. |
| `RealEnd.lean` | **`recKnowledgeSoundness_reduction_real`**: `recKnowledgeSoundness_reduction` at `realDeployment prog hprog`, from the four evaluated checks. |
| `Pi2Prover.lean`, `Pi2ProverRun.lean` | **π2's honest prover** (`prover.rs` phase by phase: `pi2ProveStreamWith`, `pi2ProveWith`, over any Keccak-256 `H`); `pi2ProveStreamWith_holds`, `pi2ProveStreamWith_claims` (the stacks and inputs its run leaves). |
| `Pi2HonestBase.lean`, `Pi2HonestCopy.lean`, `Pi2HonestQ.lean`, `Pi2Honest.lean`, `Pi2HonestMain.lean`, `Pi2HonestThm.lean`, `Pi2HonestCount.lean` | the honest prover's algebra: transforms and coset, the copy argument's sum, `q` on the extension coset; **`pi2_honest`** (off `BadCopy`, `BadT` the check passes and the four claims hold), `pi2_honest_post2`, `claims_of_model`; `card_badCopy_le`, `card_badT_le`. |
| `Pi2Whir.lean`, `Pi2CompleteCalls.lean`, `Pi2CompleteH.lean`, `Pi2CompleteSync.lean`, `Pi2Complete.lean` | honest WHIR openings at π2's layouts (`pi2Open_honest`); π2's three calls decoded (`decodeWith_claims`); the verifier, contract and setup with Keccak-256 an explicit `H` (`…_eqH`); the verifier reads what the prover writes (`runWith_honest`); **`contract_accepts`** off the bad challenges, at one permutation. |
| `Pi2CompleteEnd.lean`, `Pi2Witness.lean`, `Pi2CallsOpen.lean` | **`pi2Prover`**, `Pi2WitnessComplete`, `delta2`, `recCompleteness2_pi2`; **`pi2WitnessComplete`** (on a stream π1-rec3's graph accepts, RecCircuit's honest witness and `valuesOf` are an honest witness); **`pi2Pi1Openings`** (the contract's π1 calls on π2's honest proof decode and accept), `recCompleteness2_pi2_closed`. |
| `Pi2P1.lean` | **π1-rec3's prover as π2's completeness takes it**: `P1 : Pi1Prover D`, its two-call program `P1k : Pi1ProverK D`, and the four named facts `Pi1OverPerm`, `Pi1Disc`, `Pi1Cost`, `Pi1HashShort`, bundled as `Pi1ProverFacts D P1 P1k` (discharged for the concrete prover by `Pi1K.pi1ProverFactsK`). |
| `Pi2Prob.lean`, `Pi2ProbStaged.lean` | π2's challenges in the random-oracle model, `recCompleteness2_of_staged`; the staged experiment `pi2Staged` (stages A, B, C), `Pi2ExperimentLe`, `Pi2RunDuplex`, `Pi2RunCost`, `Pi2TFresh`, `recCompleteness2_pi2_staged`. |
| `Pi2SimMorph.lean`, `Pi2SimAt.lean`, `Pi2SimExp.lean`, `Pi2SimCore.lean` | π2's code commutes with monad morphisms (`sim_expW2`, `sim_stageA/B/C`); `stagedAt_good`; **`pi2ExperimentLe_of`** (from `Pi1OverPerm`); **`rejectGood_pi2_good`**. |
| `Pi2Chain.lean`, `Pi2TFresh.lean`, `Pi2TFreshPi2.lean`, `Pi2RunDuplex.lean`, `Pi2RunCost.lean` | `Holds2`, `recCompleteness2_of_staged2`, `delta2'`; **`pi2TFresh_of`**; **`pi2RunDuplex_of`** (from `Pi1Disc`), **`pi2RunCost_of`** (from `Pi1Cost`; `pi2RunN ≤ 2^50`). |
| `Pi2SimEnd.lean`, `Pi2Closed.lean` | the earlier forms with `hal : Pi2AlphaFresh εα` (`recCompleteness2_pi2_rec3_final`, `delta2_rec3_le`). |
| `Pi2AlphaLen.lean`, `Pi2AlphaChain.lean`, `Pi2AlphaSupport.lean`, `Pi2AlphaG.lean`, `Pi2AlphaFresh.lean`, `Pi2AlphaEnd.lean` | **`α`'s freshness**: nothing of `2^26` bytes is hashed before π2's IV (the setup's trees, the graph; π1's prover by `Pi1HashShort`), the chain from `σ`'s hash, freshness conditioned on the graph's acceptance (`Holds3`), **`alphaFresh_of`** (`alphaBound ≤ 2^-204`); **`Pi2Alpha.recCompleteness2_pi2_rec3_closed`**, **`recCompleteness_pi2_rec3_closed_fs`**, **`delta2_alpha_le`** (`δ2 ≤ 2^-164`), for any `P1` with `Pi1ProverFacts`. |
| `Pi1KeccakProver.lean`, `Pi1KeccakTransfer.lean`, `Pi1KeccakCensus.lean` | **the concrete π1-rec3 prover** `pi1Rec3ProverK D` (`pi1ProverFs hKF D`, `hKF x = pure (keccak256 x)`) and `p1kK`, `pi1Rec3ProverK_eq`; its facts transferred from UniKeccakComplete's two-call prover (`disc_p1kK`, `qc_p1kK`); its hash census (`hashShort_p1kK`). |
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
