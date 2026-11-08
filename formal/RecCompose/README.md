<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# RecCompose: the recursive verifier's end theorems

The recursive EVM verifier for the Keccak VM's proofs (leanVM 9d50c92a3's `SHA3` table, the 128-signature reference; `crates/leanvm/rec`): the contract runs π2's verifier, then six
`PCS_OPEN` calls (π1's `C1`, `C2`, `F`; π2's `W`, the setup, `Q`). Its statements are `RecStatement`'s
(`RecStatement/Security.lean`), in two parts, since π2's circuit computes π1-rec3's Fiat–Shamir with the real
Keccak-f[1600] while π1-rec3's soundness is proved in the random-permutation model:

1. **π2's part, in the random-permutation model**: `RecKnowledgeSoundness2 D ε2` (if the contract accepts, π2's
   extractor outputs π1's stream on which π1-rec3's recorded graph over Keccak-f[1600] accepts, its three calls the
   contract's), `RecCompleteness2 D P1 P2 δ2`;
2. **end to end, against the Keccak VM's `KvHolds` (`UniKeccak.KDeployment.Relation`), knowledge soundness as an explicit reduction**:
   `RecKnowledgeSoundnessReduction D ε2` (`RecStatement/Reduction.lean`). For every adversary `A` of `Q` queries, the
   break is at most `ε2 Q` plus the probability that `pi1Adversary D A` breaks π1-rec3 at Keccak-f[1600] plus the
   probability that `hazardAdversary D A` hits the merge hazard on a stream π1-rec3's graph accepts; the two derived
   adversaries are `A` then π2's explicit extractor, of `A`'s queries. No Fiat–Shamir hypothesis: the headline theorem
   is **`recKnowledgeSoundness_reduction`** (`FsClosed.lean`);
3. **the Prop-premise corollaries**: `RecKnowledgeSoundness D ε2 ε1 εh`, `RecCompleteness D P1 P2 δ1 δh δ2`, whose own
   hypotheses are `RecGraphKeccak.Pi1GraphIsVerifierK` (proved: `RecGraphKeccak.Sim.pi1GraphIsVerifierK`), `Pi1FsKeccak ε1`, `Pi1HazardKeccak εh` (and the
   completeness analogues `Pi1CompletenessKeccak`, `Pi1HazardKeccakHonest`, about the honest prover). `Pi1FsKeccak` and
   `Pi1HazardKeccak` are **false as stated** for unbounded adversaries, which grind Keccak-f[1600] offline for free:
   read them as the Fiat–Shamir heuristic for adversaries of bounded
   Keccak-f[1600] work, motivated by π1-rec3's random-permutation theorem
   (`UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_closed`, 128.49 bits) and `RecGraphKeccak.hazard_probK` (`≤ 2^16/|E|`).

The merge hazard (`RecGraphKeccak.MergeHazardK`) asks that π1-rec3's run draw `t` (challenge 52, `p_0` challenge 45), so the empty stream and
every run that stops early are off it (were they on it, `Z_bad(0) = 0` would force `εh ≥ 1`). The soundness hazard
(`Pi1HazardAccepted`) also asks that π1-rec3's graph accept the stream.

This library proves part 1 from π2's layers, its bound in bits, and part 1 ⇒ parts 2 and 3.

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only
systemd-run --scope -p MemoryMax=10G lake build RecCompose     # the theorems; #guard_msgs checks their axioms
systemd-run --scope -p MemoryMax=12G lake exe rec-view-check   # viewCheck at two IVs (about 14 minutes an IV)
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check   # DigestChecked, IvChecked at three IVs (RealDeployment.lean)
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check --setup-only   # SetupRootChecked
```

On the Keccak VM's π1-rec3 (128 signatures) every evaluated check holds: `viewCheck` at π1's reference IV and the zero
IV; `DigestChecked`, `ivCheck` at the reference, zero and all-ones IVs, `SetupRootChecked`. Each compile of the graph
takes 13–21 minutes (`rec-real-check` compiles it once for the reference circuit and once per IV), the setup root
under about 12 more; peak memory 6.7 GB. Arguments `ref`, `zero`, `ones` choose the IVs, `--no-digest` skips the
digest. These are long evaluations, not builds: run them outside the build lock.

## The Keccak VM

The library is the BLAKE2s VM's, converted in place to the Keccak VM:
- π1 is `UniKeccak`'s verifier at `keccakRec3`, on `RecGraphKeccak.Pi1.keccak128`.
- π1-rec3's recorded graph is `RecGraphKeccak.Pi1.pi1GraphK` (`RecGraphKeccak.Emitted`), at the reference setup roots
  `RecGraphKeccak.Pi1.referenceRootsK`. Every file reads them through `RecCompose.keccakRefRoots` (`realRoots` in
  `RealDeployment`).
- π2's circuit is `RecStatement.Data`, emitted by `crates/leanvm/rec/tests/lean_statement_keccak.rs`.
- The relation is `KvHolds` at `D.flock`; `Real` pins `D.flock = KeccakFlock.keccakFlockSpec`.

**π1's setup is one tree.** `A0` and `B0` are the deployment's constants, so π2's Fiat–Shamir family holds π1's
`2^27`, `2^26` and `2^23` openings. The `2^23` one is certified by `UniKeccakSound.plainShapeE23`. The bound is still
`pi2Bound` (`≤ 2^-64` for `Q ≤ 2^64`).

**The headline theorems (`FsClosed.lean`).** `recKnowledgeSoundness_reduction`, `recKnowledgeSoundness2_closed`,
`recKnowledgeSoundness_closed` and `recKnowledgeSoundness_closed_fs` take `hD : D.Real`, `C`, `hroots`, `GraphsAgree`
and `Pi2ViewChecked C`. The real deployment `realDeployment prog hprog` and `realDeployment_real` supply them, from the
evaluated `DigestChecked`, `SetupRootChecked`, `IvChecked`/`viewCheck` and the identity check `GraphsAgree`
(`RecGraphKeccakTest/Pi1Check.lean`).

**π2's completeness** (`Pi2AlphaEnd.recCompleteness2_pi2_rec3_closed`, `δ2 ≤ 2^-164`, and the `_fs` form) is for an
abstract π1-rec3 prover `P1` with the named facts `Pi1ProverFacts` (`Pi2P1.lean`).
At the concrete prover (`CompleteKeccakEnd.lean`), `Pi1K.pi1Rec3ProverK D` is UniKeccakComplete's π1-rec3 prover with
its Fiat–Shamir the pure `keccak256` and its trees and openings over `π`.
- `pi1ProverFactsK` proves its facts.
- `recCompleteness2_pi2_rec3_K` is π2's part.
- `recCompleteness_real_K_fs_bits` is end to end at `realDeployment`, with error `δ1 + δh + 2^-164`.

Two premises are left, both about this one honest prover at Keccak-f[1600]:
- `Pi1CompletenessKeccak`: its random-permutation reading, `pi1CompletenessFs_rpm`, is proved at `Prob.deltaK < 2^-169`.
- `Pi1HazardKeccakHonest`.

## The end theorems (`End.lean`)

See the section "The recursive verifier" of [`../README.md`](../README.md) for the statements verbatim and the list of
named inputs; the files:

| File | What |
|---|---|
| `Basic.lean` | π2's outcome's fields; `W`'s candidates and their witness values as π2's extractor reads them; `pi1GraphAcceptsB_iff`; `recExtractFrom2_of_mem` (one accepted candidate suffices). |
| `Part1.lean` | `CallsPure`, `Pi2Extraction`, `Pi2Layers`; **`recKnowledgeSoundness2_of_layers`**. |
| `Circuit.lean` | `Pi2Layers.circuit` from `RecGraphKeccak.pi1rec3K_end` and `CircuitBridge`; `compile_ok` from the compiler's run on the emitted graph and `GraphsAgree`; `Pi1RootWordOk` (the root-word fix's named dependence). |
| `Numbers.lean` | **`pi2Bound`** (`ε2`), `pi2_rounds_le` (RecPiop's three rounds times their lists, at most `2^-140.60`), **`pi2Bound_le_bits`** (`≤ 2^-64` for `Q ≤ 2^64`). |
| `Part2.lean` | the three events (`HazardEvent` on `Pi1HazardAccepted`), `ExperimentsAgree`, `HazardCoupling`, `Pi1Coupling`, `breaks_cases`; **`recKnowledgeSoundnessReduction_of_part1`** (the reduction), `recKnowledgeSoundness_of_reduction`, **`recKnowledgeSoundness_of_part1`**. The derived adversaries (`hazardAdversary`, `pi1Adversary`) are `RecStatement/Reduction.lean`'s. |
| `Complete.lean` | `CompletenessAgree`, `CompletenessPi1Coupling`; **`recCompleteness_of_part1`**. |
| `Layers.lean` | `Pi2FsLayer` (π2's Fiat–Shamir layer, proved in `FsClosed.lean`), `Pi2Tables` (the tables' layer, open), `Pi2Circuits`, `Pi2Facts`; `pi2Piop` (`RecPiop.piop` per setup), `hbind_of`, `indep_K`, `satisfies_congr`; **`pi2Extraction_of_layers`**, `pi2Layers_of`. |
| `Holds.lean`, `Chan.lean`, `Pi2Run.lean`, `CallsPure.lean` | postconditions in any lawful monad (`Holds`), the channel's reads (`Reads`), π2's run's public data independent of the permutation (`runWith_post`); **`callsPure`**. |
| `Rpm.lean`, `Couplings.lean` | the logging lemmas, eager comparisons per permutation; **`experimentsAgree`**, **`hazardCoupling`**, **`pi1Coupling`** (under `Pi1OpeningsAgree`). |
| `OpeningsAgree.lean`, `RunOpenings.lean` | **`pi1OpeningsAgree`** (from `pi1RunShape`, `pi1RunOpenings`, `pi1CallsShape_data`), **`pi1RunOpenings`**. |
| `RpmC.lean`, `Pi1Decode.lean`, `CompleteCouplings.lean`, `RunShape.lean` | eager comparisons, π1's call bytes decoded back; **`completenessAgree`**, **`completenessPi1Coupling`**, **`pi1RunShape`**. |
| `Tables.lean` | **`pi2Tables`** (the tables' layer, from `Pi2SetupColumns`), `cells_wFold`, `claim_wFold`, `claim_quotient`, `claim_sum`, `claim_setup`, `sum_novP_omega`. |
| `Bridge.lean` | **`circuitBridge`** (from `StatementPortMeaning`, `ZeroPortsMeaning`, `CallWordsAgree`, `Pi1CallsLayouts`). |
| `End.lean` | `recKnowledgeSoundness2_real`, **`recKnowledgeSoundnessReduction_end`**, **`recKnowledgeSoundness_end`**, `recKnowledgeSoundness_end_real`, **`recCompleteness_end`**, **`recKnowledgeSoundness_end_fs`**, **`recCompleteness_end_fs`**. |
| `ViewDefs.lean`, `View.lean` | **`viewOf`** (`pi2::adapt` transcribed), `callsOf`, `validB`, **`viewCheck`** (evaluated by `rec-view-check`, `RecComposeTest/ViewCheck.lean`); the slots, `groupsOf_perm`, `groupsOf_mem`. |
| `Valid.lean` | **`validB_sound`**: `validB` gives `RecPiop.Circuit.Valid` of `toPiop`. |
| `FactsAlg.lean`, `FactsSpec.lean`, `FactsSpecOf.lean` | the formulas' and terms' values, `pubOfC`; `Data`'s facts by kernel decision; **`specOf_data`**. |
| `Facts.lean` | `Pi2ViewChecked`; **`pi2Facts`** (`Pi2Facts D C`), `pubOfC_canon`, `pi2Facts_pubOf`. |
| `IvLength.lean` | **`RecDeployment.pi1IvAt_length`**: π1's contract IV has 32 bytes (a Keccak-256 digest); the per-IV premises are stated at 32-byte IVs and reach `pi1IvAt` through it (`Pi2Circuits.compile_okAt`, `stream_eqAt`). |
| `RealDeployment.lean` | **`realDeployment prog hprog`** (σ, κ the Lean compiler's at every IV, π1's stream its `streamW`), **`realDeployment_real`** (`Real`, from `GraphsAgree`, `DigestChecked`, `SetupRootChecked`), **`pi2Circuits_real`**, **`pi2ViewChecked_real`** (from `GraphsAgree`, `IvChecked`); `ivCheck` (compile, `viewCheck`, `streamAgree`), `streamW_eq_of_streamAgree`. Why IV uniformity is not proved: the module docstring. |
| `IvUniform.lean` | **`ivChecked_of_patchChecked`**: `IvChecked` from `PatchChecked` (the compiler's IV factorization: at every 32-byte IV, the all-ones IV's circuit with `κ` removed at the zero bits' seed positions, same view, free bits, free reads; **not proved**) and `ivCheck` at the all-ones and zero IVs (evaluated). `viewCheck_patch`, `streamAgree_patch`. |
| `Meanings.lean` | **`statementPortMeaning`**, **`zeroPortsMeaning`**, **`callWordsAgree`** for `pi2Facts`. |
| `Layouts.lean` | **`pi1CallsLayouts_of_real`** (`stackLayout_words`). |
| `Final.lean` | **`recKnowledgeSoundness2_final`**, **`recKnowledgeSoundnessReduction_final`**, **`recKnowledgeSoundness_final`**, **`recKnowledgeSoundness_final_fs`**: the end theorems from the named inputs left. |
| `FsDefs.lean` | π2's Fiat–Shamir layer's objects: the chain `pi2Spec` (`ChainSpecU` over π2's transcript: the label `name ‖ iv ‖ input`, the public data's 472 bytes before `W`'s root), the proof `P2Pf` and its view, the six openings `p2Ops` (π1's `C1`, `C2`, `F`, π2's `W`, the setup, `Q`), the setup's stacks `p2Stk`, the composed setup `p2Setup`, the IV `p2IvKC4`, the composed verifier `p2Ver`, the bridge facts' Props. |
| `FsOps.lean` | the openings' `OKP`, coverage, `hS_p2` (the setup's claim), `ClaimOn` as F2's `tableEval` on public layouts (`claimOn_iff`, `readEntry_public`), the shapes at once (`p2Shapes`), `maxErrK_p2`. |
| `FsSetup.lean`, `FsExtract.lean`, `FsWalk.lean` | **`pi2SetupBridge`**, the setup's facts and `okp_setupOp`; **`pi2ExtractBridge`**; **`pi2Walk`** (π2's run is the chain), **`pi2WalkReject`**, `pi2Scalars_real`. |
| `FsVerifier.lean`, `FsCouple.lean`, `FsCost.lean` | **`pi2VerifierBridge`** (the contract's six calls below the composed openings), **`pi2GameLeV`** (the coupling), the composed verifier's cost, the IV moved into the adversary (`expU_p2IvAdv`), `hlab_p2`. |
| `Pi2Witness.lean` | **`pi2WitnessComplete hD C hchk : Pi2WitnessComplete D C (pi2Facts hD C hchk)`** (π2's completeness input 1): on a stream π1-rec3's graph accepts, RecCircuit's honest witness (`RecCircuit/Complete.lean`) and the public values `valuesOf` (the roots' 32 bytes of the stream, the element ports' values) are an honest witness; the ports: the statement's the input's words, the roots' the stream's, the zero ports `0` (the graph's checks, `zero_port_sat`). |
| `FsGame.lean`, `FsClosed.lean` | **`pi2FsLayer_of`** (through `Compose.knowledgeSoundness_listChainU_closed128S`, `prEvent_doomF_le`, `prEvent_pairTr_expL_le`, `le_pi2BoundE`); **`pi2FsLayer_real`** (`Pi2FsLayer D` proved at the real deployment); **`recKnowledgeSoundness_reduction`** (the headline), **`recKnowledgeSoundness2_closed`**, **`recKnowledgeSoundness_closed`**, **`recKnowledgeSoundness_closed_fs`**: `Final.lean`'s end theorems without `hfs`, `Fa`, `hstmt`, `hzero`, `hcalls`, `hlay` (their inputs `C`, `hroots`, `GraphsAgree`, `Pi2ViewChecked C`). |

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

## The root-word finding

π2's stream carries π1's `C1`, `C2` roots as `rootWordOfBytes` of π1's stream bytes (each 16-byte half reversed): the
real vectors' π2 stream starts `b25c056f…cef8`, π1's `C1` root is `f30c504d…b05f`. The contract decodes that word to
`digestOfBytes32 raw`, while π1-rec3's verifier and WHIR open at `rootOf (halves raw) = rootOfWord raw` (evaluated).
So `Pi1GraphAccepts`'s roots disagreed on honest proofs, and the contract opened π1's commitments at other digests.
The fix (`fix-pi1-root`, merged at `leanvm-rec` 613b2fa) is in π1's prover: it now writes each root as its root word
(`hash_to_scalars`), as π2's prover and UniComplete's honest prover do. `RecCircuit.pcsWord` passes stream roots as
they are, so `Pi1RootWordOk` is `pi1RootWordOk` (`rfl`).

## π2's completeness, closed (`lean-pi2-run`)

| File | What |
|---|---|
| `Pi2P1.lean` | **π1-rec3's prover as π2's completeness takes it**: an abstract `P1 : Pi1Prover D` and its two-call program `P1k : Pi1ProverK D`, with the four named facts `Pi1OverPerm D P1 P1k` (`P1` is `P1k` answered over `π`), `Pi1Disc D P1k` (duplex discipline), `Pi1Cost D P1k` (`≤ 2^47` block calls), `Pi1HashShort D P1k` (hash inputs `< 2^26` bytes), bundled as `Pi1ProverFacts D P1 P1k`. No Lean Keccak π1 prover exists in this branch. |
| `Pi2SimMorph.lean` | π2's code (setup, IV, graph verifier, run, contract, prover, `expW2`, stages) commutes with monad morphisms; `sim_expW2`, `sim_stageA/B/C`. |
| `Pi2SimAt.lean` | `stream_split`, `tInput_pre2_length` (`536` bytes), `stagedAt`, `runAt_staged`, **`stagedAt_good`**. |
| `Pi2SimExp.lean` | `perm_kc`, `experiment_eq_kc` (from `P1 = P1k` over `π` at the statement), **`pi2ExperimentLe_of`** (from `Pi1OverPerm`). |
| `Pi2SimCore.lean` | `rejects_at_good`, **`rejectGood_pi2_good`** (no `Pi2RunAt`). |
| `Pi2Chain.lean`, `Pi2TFresh.lean`, `Pi2TFreshPi2.lean` | `Holds2` (`Pi2AlphaFresh` for `Pi2HashBeforeAlpha`, which a π1 prover hashing `32`-byte inputs breaks), `recCompleteness2_of_staged2`, `delta2'`; **`pi2TFresh_of`**. |
| `Pi2RunDuplex.lean`, `Pi2RunCost.lean` | **`pi2RunDuplex_of`** (from `Pi1Disc`), **`pi2RunCost_of`** (from `Pi1Cost`; `pi2RunN ≤ 2^50`; π1's setup one tree, `treeCost 23`; the circuit's encoding `24264` bytes). |
| `Pi2SimEnd.lean`, `Pi2Closed.lean` | `recCompleteness2_pi2_rec3(_closed)`, **`recCompleteness2_pi2_rec3_final`**, **`recCompleteness_pi2_rec3_final_fs`** (with `hal : Pi2AlphaFresh εα`), **`delta2_rec3_le`** (`≤ 2^-164` at `εα ≤ 2^-201`). |

## `α`'s freshness, proved (`lean-pi2-alpha`)

(as before, with:) `Pi2AlphaLen.lean`: the census before `σ` for the setup (`hashOK_setupTreesWithH2`, two trees) and the graph (`hashOK_graph`); π1-rec3's prover's is the named `Pi1HashShort`; the tools for a concrete prover's census (`hashOK_commitWithH`, `hashOK_proveOpeningWithH`, the writer calculus `WS`) are kept. `Pi2AlphaFresh.lean`: **`alphaFresh_of`** (from `Pi1Cost`, `Pi1HashShort`), `alphaBound ≤ 2^-204`. `Pi2AlphaEnd.lean`: **`holds3_pi2_of`**; **`Pi2Alpha.recCompleteness2_pi2_rec3_closed`** (from `Pi2Circuits D`, `hroots`, `GraphsAgree`, `Pi2ViewChecked C`, `Pi1ProverFacts D P1 P1k` only), **`Pi2Alpha.recCompleteness_pi2_rec3_closed_fs`**, **`delta2_alpha_le`** (`δ2 ≤ 2^-164`): the headline completeness theorems.

## The recursion's π1 prover

Deleted with the BLAKE2s VM: `Pi1KF.lean`, `Pi1KFCore.lean`, `Pi1KFTransfer.lean`, `Pi1KFRpm.lean`, `Pi1HazardFs.lean`,
`Pi2KFEnd.lean` (UniComplete's BLAKE2s π1-rec3 prover with its Fiat–Shamir over Keccak-f[1600]). The abstract theorems
of `Pi2AlphaEnd` cover such a prover: a `P1k` whose Fiat–Shamir is the pure `keccak256` makes no Fiat–Shamir queries.
