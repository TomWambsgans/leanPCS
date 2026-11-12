<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# UniKeccakComplete

Completeness of the Keccak VM's univariate verifier (`formal/UniKeccak`, `docs/leanvm/univariate/KECCAK.md`):
`UniKeccak.UniCompletenessKeccak`, `UniCompletenessKeccakRec3` and `UniCompletenessKeccakRec4`
(`UniKeccak/Security.lean`) at the Keccak-f block
`F = KeccakFlock.keccakFlockSpec`, **for an explicit Lean honest prover, closed** at the reference shape (128
signatures). A library of `formal/EndToEnd` (`UniKeccakComplete`, `srcDir = "../UniKeccakComplete"`,
`warningAsError`), plain (non-`module`) Lean files. Sorry-free, no `native_decide`, no new axioms.

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only, with formal/leanervm linked
systemd-run --scope -p MemoryMax=12G lake build UniKeccakComplete   # every file; the root's #guard_msgs check the axioms
```

## The end theorems (`UniKeccakComplete/K/EndClosed.lean`, `K/Rec4End.lean`)

```lean
theorem UniKeccakComplete.uniCompletenessKeccak_closed (D : KDeployment)
    (hD : D.shape = UniKeccakSound.keccakRefShape) (hiv : D.programIv.length ≤ 2 ^ 16)
    (hpiv : 32 ≤ D.programIv.length) :
    UniCompletenessKeccak KeccakFlock.keccakFlockSpec D (Prob.uniProverRP flockProveH D) Prob.deltaK
theorem UniKeccakComplete.uniCompletenessKeccakRec3_closed (D : KDeployment)
    (hD : D.shape = UniKeccakSound.keccakRefShape) (hiv : D.programIv.length ≤ 2 ^ 16)
    (hpiv : 32 ≤ D.programIv.length) :
    UniCompletenessKeccakRec3 KeccakFlock.keccakFlockSpec D (Rec3.uniProverRec3RP flockProveH D) Prob.deltaK
theorem UniKeccakComplete.uniCompletenessKeccakRec4_closed (D : KDeployment)
    (hD : D.shape = UniKeccakSound.keccakRefShape) (hiv : D.programIv.length ≤ 2 ^ 16)
    (hpiv : 32 ≤ D.programIv.length) :
    UniCompletenessKeccakRec4 KeccakFlock.keccakFlockSpec D (Rec4.uniProverRec4RP D) Prob.deltaK
theorem UniKeccakComplete.Prob.deltaK_lt : deltaK < (2 : ℝ≥0∞)⁻¹ ^ 169
```

All depend on `[propext, Classical.choice, Quot.sound]` only (the root's `#guard_msgs`).

**On the EIP's PCS claims** (the verifier of `formal/UniKeccak`: each commitment's out-of-domain answer read after
its root, the roots carried as their bytes, the setup's commitment `(root, ood)` in the contract's IV, one PCS claim
per commitment opened by `WhirBridge.Pcs.pcsVerifyWithHash`). The prover sends each root's bytes (`rootHalves`) and
its out-of-domain answer (`pcsOod`: the stack's multilinear extension at `WhirBridge.Pcs.oodPoint n root`), and opens
each claim by `pcsProveH` (`K/PcsProver.lean`). `hpiv` (the program's IV at least a digest's `32` bytes; the deployed
one has `32`): the first bus-challenge input is `112` bytes (the seed, the counts, `C1`'s root and its out-of-domain
answer), fresh by its length only if the IV's preimage (`91 + |IV|` bytes) has another length.

- **The provers.** `Prob.uniProverRP flockProveH D` is `uniProverWith` (`K/Witness.lean`) over the random
  permutation's two calls (Keccak-256 the sponge over `π`, `π` itself for WHIR's proofs of work), with Flock's honest
  prover on the Keccak-f block `flockProveH = fun H ↦ FlockP.flockProve H`; `Rec3.uniProverRec3RP flockProveH D` is
  π1-rec3's (`K/Rec3Prover.lean`). No hypothesis beyond the statement's own (`RowsFit`, `HonestRelation` = `KvHonest`).
- **The reference shape** `keccakRefShape = keccakShapeOf 721598 [24260, 36229, 24626, 35812, 15509, 17712]`
  (`UniKeccakSound`'s): heights `15 16 15 16 14 15`, memory `2^20`, bytecode `2^18`; `C1` has `2^27` words, `C2`
  `2^26`, the setup `2^23`.
- **The bound** `deltaK = (2^22 − 1)/2^192 + 6/2^256 + (2^15/2^192 + 2^-200) + 2^-304 + rpmError (2^48) < 2^-169`
  (about `2^-169.99`; π1-rec3's own bound lacks the `6/2^256` and is at most `deltaK`, `Rec3.delta3_le_deltaK`):

| term | event | where |
|---|---|---|
| `(2^22 − 1)/2^192` | a bus challenge `β` makes a divided fingerprint vanish (≤ `capBoundK = 3,227,648` per `α`; `2,439,584` at the reference row counts) | `K/BadFpCount.lean` (`badFpCard_keccakRef_22`) |
| `6/2^256` | the main line's five chained bus answers meet an earlier query | `Chain.lean` |
| `2^15/2^192` | `y(t)` a proper prefix of another point on `C1` (≤ `2·2^14` such `t` per Flock point) | `K/ProbBadT.lean` (`badTCard_keccakRef_15`) |
| `2^-200` | `t`'s query not fresh (`75` chain steps, `34,078,798` hashed inputs before it; π1-rec4: `42` steps, `< 2^28`) | `K/ProbTFresh.lean`, `K/Rec3ProbTFresh.lean`, `K/Rec4TFresh.lean` |
| `2^-304` | an opening's proof of work fails for every nonce below `nonceFuel` | `K/ProbGrind.lean`, `K/Rec3ProbGrind.lean` |
| `rpmError (2^48)` | the permutation as two random oracles (π1-rec4: the rate and the permutation): setup, prover (`≤ 2^47`), verifier on streams of `≤ 2^14` bytes | `K/FlockCost.lean` (`totalCostK_le`), `K/Rec3ProverCost.lean` (`totalCostK3_le`), `K/Rec4CostBound.lean` (`expCost4_reference`) |

## π1-rec4 (`K/Rec4*.lean`)

`UniKeccak.UniCompletenessKeccakRec4` (the recursion's inner proof since π1-rec4) is closed at the same bound
(`uniCompletenessKeccakRec4_closed`), for the honest prover **`Rec4.uniProverRec4RP D`** (`K/Rec4Prover.lean`):
`Rec4.uniProverRec4With H W F D`, generic in the monad, Keccak-256 `H`, its 136-byte rate `W` and the permutation `F`
(it commutes with every monad morphism that commutes with the opening, `app_uniProverRec4With`), over the random
permutation (`H = keccak256With π`, `W = rateWith π`, `F = π`). Its stream is π1-rec3's byte for byte with π1-rec4's
three wide draws (`sampleWideW`: `c, β, γ, c'` after `C1`; `t, f_0 … f_3` after `C2`; `ρ, λ, f_4, f_5` after the
values at `t`), Flock's zerocheck from the given `c'` (`zerocheckW4`), no ring map in Flock (its end the ring switch at
the late map, `flockOut4`), π1-rec3's paired batch with `λ` given.

- **The verifier with `H` and `W` explicit** (`Rec4VerifierH.lean`): `reduceWithKH4`, `verifyWithKH4`,
  `KDeployment.verifierWith4H`, equal to `UniKeccak`'s at `H = keccak256With F`, `W` its rate (`verifierWith4_eqH4`).
- **Random permutation → rate random oracle → five digests** (`Rec4Rate.lean`, `Rec4Couple.lean`, `Rec4Exp.lean`,
  `Rec4Prob.lean`): the experiment over π1-rec4's calls (`experiment4_eq`), the soundness side's
  `UniKeccakSound.Rec4.keccak256RateTransfer` for the transfer (`rpm_le_romW`, `rpmError N`), then an exact coupling
  of a rate query with five digest queries (`romW_evalDistEq`: the input and four tails `extIn i x`, the rate the first
  `136` bytes of the five digests, `mkRate`).
- **The staged run** (`Rec4Staged.lean`, `Rec4Split.lean`, `Rec4Grind.lean`, `Rec4ProbK.lean`): `KStaged4` (the bus
  draw at `Nbad/2^192`, `t` at `ct/2^192 + εt`, grinding `2^-304`), the prover cut at its draws (`stagedU4`),
  `uniCompletenessKeccakRec4_of_core` from named hypotheses, each discharged: the block count
  (`Rec4Cost.lean`, `Rec4CostBound.lean`: `expCost4_reference`, `2^48`, π1-rec4's three calls read through
  leanerVM's two), the duplex discipline (`Rec4Duplex.lean`: `expDuplex4`), the deterministic core
  (`Rec4Flock.lean`, `Rec4Batch.lean`, `Rec4SyncVerifier.lean`, `Rec4CoreRun.lean`, `Rec4Core.lean`:
  `coreAccepts4_reference`, `coreFailsOnlyAtPow4`), the point draw's freshness (`Rec4Chain.lean`, `Rec4TFresh.lean`:
  `tQueryFresh4_reference`, `2^-200`: `42` challenges after the bus draw, each a step and four tails, Flock's last on
  `80` bytes taking `C2`'s tree into its step, fewer than `2^28` hashed inputs); the bound is π1-rec3's
  (`Rec3.delta3_le_deltaK`).
- **The openings** (`Rec4Core.lean`, `Rec4RunOpenings.lean`): `Rec4.honest_openings4` (the run on an honest proof, at
  every rate and permutation and every challenge, returns three point claims on `C1`, `C2`, the setup, in order, at
  points of `27`, `26`, `23` coordinates); `Rec4.runK4_openings` (every run of `runK4` that returns a result: three
  point claims on `C1`, `C2`, the setup, in order, no bit slice; their lengths in an accepting `verifyWithK4` by
  `pcsOpenK_length`).
- Decision (recorded): the defeq checks against the prover's state (`frontOf4`) keep Flock's prover, `atTOf`,
  `c2DataOf`, `c1Stack`, `setupStackOf` folded (`attribute [local irreducible]` in `Rec4SyncVerifier.lean`,
  `Rec4Core.lean`); unfolded, they exhaust memory.

## The layers

- **The staged premise** (`Staged.lean`, `Chain.lean`, `End.lean`): `UniComplete`'s probability layer at the Keccak
  experiment; `KStagedK` (five chained bus answers, the main line's) and `uniCompletenessKeccak_end`. π1-rec3 draws
  **two** chained answers (`c` with `α = (c, c², c⁴, c⁸)`, then `β`; then `γ`, Flock's first coordinate, then Flock's
  coset values are absorbed), so `KStagedK` cannot describe its experiment (the fifth answer would be a query the
  experiment never makes): π1-rec3 has its own staged form `Rec3.KStaged3` (`K/Rec3ProbChain.lean`,
  `K/Rec3ProbStaged.lean`, `uniCompletenessKeccakRec3_of_staged3`); `End.lean`'s `uniCompletenessKeccakRec3_end` is
  unused.
- **The honest prover** (`K/Trace`, `Bus`, `Quotients`, `Batch`, `Claims`, `Prover`, `Witness`, `FlockProver`,
  `Rec3Prover`): `UniComplete`'s prover on the Keccak VM: the placed trace read off the Keccak VM's stack
  (`honestTrace`; the `SHA3` table's padding rows' lanes set to `q_flock`'s port words, `+ END_BIT` on `in_16`, as the
  Rust prover's `trace.rs` does, so that the unselected copy constraint holds on every row), `C1` with every `SHA3`
  column committed, `q_flock` of `2^(h_SHA3 + 11)` words, the bus leaves and product heap, the quotients (the `SHA3`
  copies `lane − port − END_BIT`), the batching sumcheck with no matrices term (`denseWeight` at stride `2048`), Flock's
  prover on the Keccak-f block (one prover for both Fiat–Shamir shapes: zerocheck with skip `3` and `drawW`, `11`
  lincheck rounds, the `64` slices always sent, the ring map in tower order), the setup of one tree, the Keccak
  contract's IV (the setup's commitment, `setupRootsOf`), each root's bytes and out-of-domain answer, three PCS
  claims' openings (`pcsProveH`).
- **The PCS claim's opening** (`K/PcsProver.lean`): `pcsProveH` (the claim's sponge `F(seedInput(H(claim), 0))`, the
  root's two scalars, then the Statement's opening script at the plain layout run against the claim's program
  `verifyStackedOpening n 1 [(eq(z,·), ood), (eq(point,·), value)]`); `pcsProveH_eq_prove` (at a pure hash it is
  mumbai's compiled honest prover of `openingProgram`: at the plain layout a claim's weight on the cube is `eq`,
  `basisTable_pcs`); `pcsVerify_pcsProveH` (accepted at `23 ≤ n ≤ 28`, through `runProof_prove` and
  `runI_openingProgram`); `pcsProveH_fails_only_at_pow`; its simulation, discipline, cost and failure in `Option`
  (`simulateQ_pcsProveH`, `disc_pcsProveH`, `cost_pcsProveH`, `pcsProveH_eq_some_none`) and the verifier's
  (`simulateQ_pcsVerify`, `disc_pcsVerify`, `cost_pcsVerify`).
- **The verifier with Keccak-256 explicit** (`K/VerifierH`, `VerifierHSim`, `VerifierHDuplex`, `VerifierHCost`):
  `reduceWithK`, `verifyWithK`, `KDeployment.verifierWith`, `setupTreeKWith` with `H` explicit, equal to UniKeccak's
  at `H = keccak256With F`; they commute with simulation, follow the duplex discipline, and count their blocks.
- **The probability layer** (`K/ProbSplit`, `ProbHyp`, `ProbExp`, `ProbGrind`, `ProbK`; `Rec3Split`, `Rec3Hyp`,
  `Rec3ProbExp`, `Rec3ProbGrind`, `Rec3ProbK`; `EndRef`): the staged runs, their conditions, completeness from the
  named hypotheses, then at the reference shape from the deterministic core alone.
- **The mapping** (`K/MappingBasic`, `MappingRows`, `MappingTrace`, `MappingBus`, `Mapping`, `Setup`):
  `Mapping.honestTrace_honest`: a `KvHonest` stack's placed trace satisfies `TraceHonest` (the bus through
  `UniKeccakSound`'s row tuples, the lane copies from `KeccakAux`, the Keccak-f region block by block);
  `setupStackOf_honestTrace = setupStackK`.
- **Flock** (`K/FlockProver*`): `FlockP.flockSyncs` (the prover synchronises with `verifyWalkedKH`, collecting the
  terminal check), `flockZero_eq_zero` (for an honest `q_flock` the lincheck's last claim is the slices' bilinear form,
  which is `structuredTerminal` by `KeccakFlock.Core.structuredTerminal_eq_bilinear` and
  `UniKeccakSound.KF.Br.structuredTerminal_eq`), `flockRingHolds`.
- **The algebra** (`K/AlgC*`, `K/AlgH*`): every relation the verifier states at `t` holds; the quotients divide
  exactly and fit their chunks (`AlgC.relations_hold_reference`, `AlgH.heapRelations_hold`).
- **Synchronisation and the batch** (`K/SyncBasic`, `SyncTable`, `SyncVerifier`, `BatchProof*`, `Combine`,
  `VerifierAccept`; `Rec3BatchAlg`, `Rec3BatchSync`, `Rec3BatchZero`, `Rec3SyncVerifier`).
- **The deterministic core** (`K/ProverRun`, `CoreRun`, `CoreBatch`, `Core`; `Rec3CoreRun`, `Rec3CoreBatch`,
  `Rec3Core`; `Whir23`): `Core.coreAccepts_reference`, `Core.coreFailsOnlyAtPow`, `Rec3.coreAccepts3_reference`,
  `Rec3.coreFailsOnlyAtPow3`; the setup's opening at `2^23` words through `UniKeccakSound.Fs.Whir23`'s admissibility.
- **Counts and costs** (`K/BadFpCount`, `ProbBadT`, `ProbTFresh`, `Rec3ProbTFresh`, `ProverBounds`, `ProverCost`,
  `FlockCommutes`, `FlockCost`, `Rec3ProverSim`, `Rec3ProverDuplex`, `Rec3ProverCost`, `Reference`).

## Imports

`UniComplete`'s generic modules (`Basic`, `Div`, `Domain*`, `Whir`, `Rec3Pairs`), `UniSound` through `UniKeccakSound`,
and `Lv42`'s shared `Protocol.LeanIsaBase` and `Arithmetization.Completeness.BasicsBase`.

## What is not done

The three statements are closed at the reference shape. Other shapes would need the
reference-shape numbers (stack sizes, the bad sets' counts, the costs, the coordinate functionals at `h_SHA3`)
recomputed; most layers are shape-generic.
