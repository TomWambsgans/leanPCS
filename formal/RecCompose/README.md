<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# RecCompose: the recursive verifier's end theorems

The recursion of commit `f96a7938` (π2 over π1-rec3, π1's three claims encoded by the contract; the deployed π2 over
π1-rec4 is not yet ported: [`docs/LEAN_PORT.md`](../../docs/LEAN_PORT.md)). The contract runs π2's verifier, then
checks eight claims declared, each the EIP draft's PCS claim `[root, ood, point…, value]`: π1's `C1`, `C2`, `F`; π2's
`W`, the setup, `Q`'s identity, pushes and sum. The statements are `RecStatement`'s (`Security.lean`,
`Reduction.lean`; [`../RecStatement/README.md`](../RecStatement/README.md)). π2's circuit computes π1-rec3's
Fiat–Shamir with the real Keccak-f[1600], while π1-rec3's theorems are in the random-permutation model, so the
statements come in three forms:

1. **π2's part, in the random-permutation model**: `RecKnowledgeSoundness2 D ε2` (if the contract accepts, π2's
   extractor outputs π1's stream, on which π1-rec3's recorded graph accepts with the contract's three π1 claims),
   `RecCompleteness2 D P1 P2 δ2`.
2. **End to end against `KvHolds`, knowledge soundness as an explicit reduction**, `RecKnowledgeSoundnessReduction D
   ε2`: for every adversary `A` of `Q` queries, the break is at most `ε2 Q` plus Pr[`pi1Adversary D A` breaks π1-rec3
   at Keccak-f[1600]] plus Pr[`hazardAdversary D A` hits the merge hazard on a stream the graph accepts]. The derived
   adversaries are `A` then π2's explicit extractor, of `A`'s queries. No Fiat–Shamir premise.
3. **Prop-premise forms**: `RecKnowledgeSoundness D ε2 ε1 εh` under `Pi1FsKeccak ε1`, `Pi1HazardKeccak εh`, and
   `RecCompletenessWith` under `Pi1CompletenessKeccak δ1`, `Pi1HazardKeccakHonest δh`. `Pi1FsKeccak` and
   `Pi1HazardKeccak` are false as stated for unbounded adversaries (they grind Keccak-f[1600] offline): read them as
   the Fiat–Shamir heuristic, motivated by `UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_closed` (128.49 bits) and
   `RecGraphKeccak.hazard_probK` (`≤ 2^16/|E|`). `Pi1GraphIsVerifierK` is proved
   (`RecGraphKeccak.Sim.pi1GraphIsVerifierK`).

The merge hazard (`RecGraphKeccak.MergeHazardK`): π1-rec3's run draws `t` (challenge 52) and `t` is a root of
`Z_bad(p_0)` (`p_0` challenge 45); the soundness hazard (`Pi1HazardAccepted`) also asks that the graph accept.

**The bound** `pi2Bound` (`Numbers.lean`): the rounds (`pi2RoundErr = 9952 · 3564 · (4 · 2^24 − 1)/2^192`, `2^-140.92`;
round 1 charged `(4N − 1)/|E|` for `Q`'s prover-filled slots `1, 5, 9, 12`) and the eight PCS openings charged once
(`pi2OpenErr = 269 · 2^-137 + 2^-156`, `FsOps.prEvent_doomH_le` through `WhirBridge.Pcs.UnionO.pcs_union_sound_oracle`),
with `Q`'s three claims bound to one table by its out-of-domain answer (`FsBind.qOodBinding`, from
`WhirBridge.Pcs.ood_binding_coords` at `n = 28`). `W`'s and `Q`'s openings read their point off Keccak-256
(`RecStatement.pcsOpenKO`; at Keccak-f[1600] the deployed `ood_point`, `pcsOpenKO_keccakF1600`); π1's three claims and
the setup's keep the fixed `WhirBridge.Pcs.oodPoint`. `pi2Bound_le_bits`: `pi2Bound Q ≤ 2^-64` at `Q ≤ 2^64`
(128.93 bits as `Q/ε2`).

## The end theorems

| Theorem | Statement | Premises |
|---|---|---|
| **`recKnowledgeSoundness_reduction_real prog hprog`** (`RealEnd`) | `RecKnowledgeSoundnessReduction (realDeployment prog hprog) pi2Bound ∧ ∀ Q ≤ 2^64, pi2Bound Q ≤ 2^-64` | the evaluated checks `GraphsAgree`, `DigestChecked`, `SetupRootChecked`, `IvChecked` |
| `recKnowledgeSoundness_reduction D`, `recKnowledgeSoundness2_closed D`, `recKnowledgeSoundness_closed D`, `recKnowledgeSoundness_closed_fs D` (`FsClosed`) | the reduction; π2's part; the Prop-premise form; with `ε1 + εh` | `D.Real`, `C : Pi2Circuits D`, `C.rootsAt = RecGraphKeccak.Emitted.rootsAt`, `GraphsAgree`, `Pi2ViewChecked C` (and `Pi1FsKeccak`, `Pi1HazardKeccak` for `_fs`) |
| **`Pi1K.recCompleteness_real_K_fs_bits prog hprog`** (`CompleteKeccakEnd`) | `RecCompletenessWith D (composeProver D (pi1Rec3ProverK D) (pi2Prover D …)) (δ1 + δh + 2^-164)` at `realDeployment` | the four evaluated checks; `Pi1CompletenessKeccak D (pi1Rec3ProverK D) δ1`, `Pi1HazardKeccakHonest D (pi1Rec3ProverK D) δh` |
| `Pi1K.recCompleteness2_pi2_rec3_K` | π2's part, `δ2 ≤ 2^-164` (`Pi2Alpha.delta2_alpha_le`) | `D.Real`, `C`, roots, `GraphsAgree`, `Pi2ViewChecked C` |
| `pi1CompletenessKeccak_iff`, `pi1CompletenessFs_rpm` (`Pi1KeccakRpm`) | the first completeness premise's random-permutation reading, at `Prob.deltaK < 2^-169` | `D.Real` |

`realDeployment_real`, `pi2Circuits_real`, `pi2ViewChecked_real` (`RealDeployment.lean`) build the premises from the
evaluated checks. `pi1Rec3ProverK D` is UniKeccakComplete's π1-rec3 prover with its Fiat–Shamir the pure `keccak256`;
`pi2Prover` is π2's Lean prover. Sorry-free, no `native_decide`; the root's `#guard_msgs` checks the headline theorems
depend on `[propext, Classical.choice, Quot.sound]` only.

## Build and the evaluated checks

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only
systemd-run --scope -p MemoryMax=10G lake build RecCompose     # the theorems; #guard_msgs checks their axioms
systemd-run --scope -p MemoryMax=12G lake exe rec-view-check   # viewCheck at two IVs (about 14 minutes an IV)
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check   # DigestChecked, ivCheck at three IVs (args ref, zero, ones; --no-digest)
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check --setup-only   # SetupRootChecked
PI2_PROVER=<vectors> lake env lean ../RecCompose/RecComposeTest/Pi2Prover.lean   # π2's Lean prover against the Rust's
```

At `f96a7938` every evaluated check holds: `viewCheck` at the reference and zero IVs; `DigestChecked`, `ivCheck` at the
reference, zero and all-ones IVs; `SetupRootChecked` (each compile 13–21 minutes, peak 6.7 GB; run outside the build
lock). `GraphsAgree` is `RecGraphKeccakTest/Pi1Check.lean`. π2's Lean prover writes the Rust's setup, `W` and `Q` roots
and stream byte for byte on 2/2 vectors (`crates/leanvm/rec/tests/lean_pi2_prover.rs`, `W`'s and `Q`'s points read
off Keccak-256 over Keccak-f[1600]).

## Files, by layer

- **Soundness skeleton**: `Basic`, `Part1` (`recKnowledgeSoundness2_of_layers`), `Part2` (the reduction,
  `recKnowledgeSoundnessReduction_of_part1`), `Layers` (`Pi2FsLayer`, `Pi2Tables`, `Pi2Circuits`, `ClaimOn`), `End`,
  `Final`.
- **The circuit and the view**: `Circuit` (`GraphsAgree`), `Bridge` (`circuitBridge`), `Meanings`, `ViewDefs`/`View`
  (`viewCheck`), `Valid`, `Facts*` (`specOf_data`, `pi2Facts`), `Tables` (`pi2Tables`), `Layouts`.
- **π2's Fiat–Shamir layer**: `FsDefs`, `FsOps`, `FsBind` (`qOodBinding`), `FsOod`, `FsSetup`, `FsExtract`, `FsWalk`,
  `FsVerifier`, `FsCouple`, `FsCost`, `FsGame`, `FsClosed` (`pi2FsLayer_real`, no premise), `Numbers`, `RealEnd`.
- **Couplings to π1-rec3**: `Rpm`, `Couplings`, `OpeningsAgree`, `RunOpenings`, `RpmC`, `Pi1Decode`,
  `CompleteCouplings`, `RunShape`, `Holds`, `Chan`, `Pi2Run`, `CallsPure`, `GenericSetupLog`.
- **The deployment**: `IvLength` (π1's IV has 32 bytes), `RealDeployment`, `IvUniform` (`ivChecked_of_patchChecked`).
- **Completeness**: `Pi2Prover*`, `Pi2PcsZ`, `Pi2Honest*`, `Pi2Whir`, `Pi2Complete*`, `Pi2Witness`, `Pi2CallsOpen`,
  `Pi2P1` (`Pi1ProverFacts`), `Pi2Prob*`, `Pi2Sim*`, `Pi2Chain`, `Pi2TFresh*`, `Pi2Run{Duplex,Cost}`, `Pi2Closed`,
  `Pi2Alpha*` (`α`'s freshness, `alphaBound ≤ 2^-204`), `Pi1Keccak{Prover,Transfer,Census,Rpm}`, `CompleteKeccakEnd`.

Each file's module docstring says what it proves.

## Statements this composition fixed (`RecStatement/Security.lean`)

1. π2's extractor searches `W`'s list by the whole acceptance (`pi1GraphAcceptsB` against the contract's π1 claims),
   not the first candidate whose stream passes the graph's checks: a word near two codewords could otherwise yield a
   stream whose claims are not the contract's.
2. The derived π1 adversaries are given the setup's evaluations, so `ε1` is charged at `Q`, not `Q` plus the setup.
3. π2's completeness is for π1-rec3's prover on honest statements (an unbounded `P1` could grind π2's challenges).

## Remaining

1. **The model gap**: the reduction's two π1 terms and the two completeness premises are at Keccak-f[1600], left to
   the Fiat–Shamir heuristic; `Pi1HazardKeccakHonest`'s random-permutation reading is not proved.
2. **The evaluated checks** are Props checked by running Lean, not kernel proofs; `IvChecked` is assumed at IVs other
   than the reference, zero and all-ones (`PatchChecked`, a relational simulation of about 1,200 lines of the builder).
3. **The provers**: the deployed Rust provers are trusted for completeness; π2's Lean prover is compared with the
   Rust's on two small circuits, UniKeccakComplete's π1-rec3 prover has no differential runner.
4. **The port** to the deployed π2 over π1-rec4: [`docs/LEAN_PORT.md`](../../docs/LEAN_PORT.md), "leanVM".
