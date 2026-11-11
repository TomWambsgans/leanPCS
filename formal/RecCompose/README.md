<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. -->

# RecCompose: the recursive verifier's end theorems

The deployed recursion (main `7e6d353c`): π2v4 over π1-rec4 at the 128-signature reference, π1's three claims declared
in the transaction's frame of PCS claims and hashed in π2's circuit. The contract runs π2's verifier (its seed over the
three frame words, payloads `0 … 2`), then checks seven claims, each the EIP draft's PCS claim
`[root, ood, point…, value]`: π1's `C1`, `C2`, `F` (the declared words), π2's `W`, the setup, `Q`'s identity and
pushes (payloads `3 … 6`), each opened once. The statements are `RecStatement`'s (`Security.lean`, `Reduction.lean`;
[`../RecStatement/README.md`](../RecStatement/README.md)). π2's circuit computes π1-rec4's Fiat–Shamir with the real
Keccak-f[1600], while π1-rec4's theorems are in the random-permutation model, so the statements come in three forms:

1. **π2's part, in the random-permutation model**: `RecKnowledgeSoundness2 D ε2` (if the contract accepts, π2's
   extractor outputs π1's stream, on which π1-rec4's recorded graph at π1's setup commitment accepts, its three claims
   hashing to the declared ones), `RecCompleteness2 D P1 P2 δ2`.
2. **End to end against `KvHolds`, knowledge soundness as an explicit reduction**, `RecKnowledgeSoundnessReduction D
   ε2`: for every adversary `A` of `Q` queries, the break is at most `ε2 Q` plus Pr[`pi1Adversary D A` breaks π1-rec4
   at Keccak-f[1600]] plus Pr[`hazardAdversary D A` hits the merge hazard on a stream the graph accepts] plus
   Pr[`collisionAdversary D A` outputs a Keccak-256 collision] (the extractor names π1's claims by their hashes). The
   derived adversaries are `A` then π2's explicit extractor, of `A`'s queries. No Fiat–Shamir or collision-resistance
   premise.
3. **Prop-premise forms**: `RecKnowledgeSoundness D ε2 ε1 εh εc` under `Pi1FsKeccak ε1`, `Pi1HazardKeccak εh`,
   `Keccak256CR εc`, and `RecCompletenessWith` under `Pi1CompletenessKeccak δ1`, `Pi1HazardKeccakHonest δh`. The first
   three are false as stated for unbounded adversaries (they grind Keccak-f[1600] offline): read them as the
   Fiat–Shamir heuristic and Keccak-256's collision resistance, motivated by
   `UniKeccakSound.uniKnowledgeSoundnessKeccakRec4_closed` (`uniBound128 (2^35/|E|)`, at most `2^-64` at `Q ≤ 2^64`) and
   `RecGraphKeccak.hazard_probK` (`≤ 2^16/|E|`). `Pi1GraphIsVerifierK4` is proved
   (`RecGraphKeccak.Sim.pi1GraphIsVerifierK4`, at every setup commitment `…K4At`).

The merge hazard (`RecGraphKeccak.MergeHazardK4`): π1-rec4's run draws `t` (challenge 46) and `t` is a root of
`Z_bad(p_0)` (`p_0` challenge 45); the soundness hazard (`Pi1HazardAccepted`) also asks that the graph's checks hold.

**The bound** `pi2Bound` (`Numbers.lean`): the rounds (`pi2RoundErr = 9952 · 3564 · (5 · 2^24 − 1)/2^192`,
`2^-140.60`: the identity `I = D²H + xZDq + x²Z³G + xDR`, below `5N`, and `P`'s definition at `t`, `RecPiop`'s
`err 1`; the copy argument with the statement's and the three claims' hashes, `(4N + 3)/|E|`, and `ρ`'s two claims
below them) and the seven PCS openings charged once (`pi2OpenErr = 269 · 2^-137 + 2^-156`, `FsOps.prEvent_doomH_le`
through `WhirBridge.Pcs.UnionO.pcs_union_sound_oracle`), with `Q`'s two claims bound to one table by its
out-of-domain answer (`FsBind.qOodBinding`). `W`'s and `Q`'s openings read their point off Keccak-256
(`RecStatement.pcsOpenKO`); π1's three declared claims and the setup's keep the fixed `WhirBridge.Pcs.oodPoint`.
`pi2Bound_le_bits`: `pi2Bound Q ≤ 2^-64` at `Q ≤ 2^64` (128.93 bits as `Q/ε2`).

## The end theorems

| Theorem | Statement | Premises |
|---|---|---|
| **`recKnowledgeSoundness_reduction_real prog hprog`** (`RealEnd`) | `RecKnowledgeSoundnessReduction (realDeployment prog hprog) pi2Bound ∧ ∀ Q ≤ 2^64, pi2Bound Q ≤ 2^-64` | the evaluated checks `GraphsAgreeK4`, `DigestChecked`, `SetupRootChecked`, `IvChecked` |
| `recKnowledgeSoundnessReduction_final D`, `recKnowledgeSoundness2_final D`, `recKnowledgeSoundness_final D` (`Final`) | the reduction; π2's part; the Prop-premise form | `D.Real`, `C : Pi2Circuits D`, `Fa : Pi2Facts D C`, `C.rootsAt = Emitted.rootsAt`, `Pi2CircuitAccepts C Fa`, `GraphsAgreeK4` |
| `recKnowledgeSoundnessReduction_end D` (`End`) | the reduction from π2's layers | `D.pi1.shape = keccak128`, `GraphsAgreeK4`, `Pi2Layers D ε2` |
| `recCompleteness_end`, `recCompleteness_end_fs` (`CompleteCouplings`) | `RecCompletenessWith D (composeProver D P1 P2) (δ1 + δh + δ2)` | `D.Real`, `RecCompleteness2 D P1 P2 δ2`, `Pi1CompletenessKeccak δ1`, `Pi1HazardKeccakHonest δh` |
| `pi2_accepts` (`Pi2Accepts`) | the contract accepts π2's honest proof (pure permutation, `D.Real`) | an honest witness, three declared claims opening, off `BadCopy`, `BadT`, `BadRho` |

`realDeployment_real`, `pi2Circuits_real` (`RealDeployment.lean`), `pi2Facts_real`, `pi2CircuitAccepts_real`
(`RealCircuit.lean`) build `Final`'s premises from the evaluated checks; `pi2FsLayer_real` (`FsClosed.lean`, no
premise) and `pi2Tables` (`Tables.lean`) give π2's extraction, `pi2SetupColumns_of_real` (`Real.lean`) the setup's
columns. Sorry-free, no `native_decide`; the `#guard_msgs` of each file checks its theorems depend on
`[propext, Classical.choice, Quot.sound]` only.

## Build and the evaluated checks

```sh
cd formal/EndToEnd
systemd-run --scope -p MemoryMax=16G lake build RecCompose.RealEnd RecCompose.Final   # soundness; #guard_msgs
systemd-run --scope -p MemoryMax=16G lake exe rec-view-check   # viewCheck (one compile about 14 minutes)
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check   # DigestChecked, ivCheck (args ref, zero, ones; --no-digest)
systemd-run --scope -p MemoryMax=16G lake exe rec-real-check --setup-only   # SetupRootChecked
PI2_PROVER=<vectors> lake env lean ../RecCompose/RecComposeTest/Pi2Prover.lean   # π2's Lean prover against the Rust's
```

`IvChecked` is over `(roots, iv)`: the compiled circuit depends on π1's setup commitment (`graphAtSetup`) as well as on
π1's contract IV, and is evaluated at the reference commitment only (the reference, zero and all-ones IVs);
`GraphsAgreeK4` is `RecGraphKeccakTest/Pi1Check.lean`. π2's Lean prover writes the Rust's setup, `W` and `Q` roots, IV
and stream byte for byte on 3/3 vectors (`crates/leanvm/rec/tests/lean_pi2_prover.rs`: `2^9`, `2^10`, and one with a
narrow element and a hashed claim).

## Files, by layer

- **Soundness skeleton**: `Basic`, `Part1` (`recKnowledgeSoundness2_of_layers`), `Part2` (the reduction,
  `recKnowledgeSoundnessReduction_of_part1`), `Layers` (`Pi2FsLayer`, `Pi2Tables`, `Pi2Circuits`, `Pi2Facts`,
  `Pi2CircuitAccepts`, `pi2Layers_of`), `End`, `Final`, `RealEnd`.
- **The circuit and the view**: `Circuit` (`claimHash_words32`, `pi1GraphAccepts_of_ports`),
  `ViewDefs`/`View` (`viewCheck`), `Valid`, `Facts*` (`pi2Facts`), `RealCircuit`, `Tables` (`pi2Tables`), `Layouts`.
- **π2's Fiat–Shamir layer**: `FsDefs`, `FsOps`, `FsBind` (`qOodBinding`), `FsOod`, `FsSetup`, `FsBytes`, `FsExtract`,
  `FsWalk`, `FsVerifier`, `FsCouple`, `FsCost`, `FsGame`, `FsClosed` (`pi2FsLayer_real`), `Numbers`.
- **Couplings to π1-rec4**: `Rpm`, `Couplings` (`collisionCoupling`, `pi1Coupling`), `ClaimBytes`, `Pi1Words`,
  `OpeningsAgree`, `RunOpenings`, `RpmC`, `Pi1Decode`, `CompleteCouplings`, `RunShape`, `Holds`, `Chan`, `Pi2Run`,
  `CallsPure`, `GenericSetupLog`.
- **The deployment**: `IvLength`, `RealDeployment`, `Real`, `IvUniform` (`ivChecked_of_patchChecked`).
- **Completeness**: `Points`, `Pi2Prover`, `Pi2ProverRec`, `Pi2Honest*`, `Pi2Whir`, `Pi2Complete*`, `Pi2Accepts`,
  `Pi2P1` (`Pi1ProverFacts`).

Each file's module docstring says what it proves.

## Remaining

1. **The model gap**: the reduction's π1 and hazard terms and the two completeness premises are at Keccak-f[1600], left
   to the Fiat–Shamir heuristic; the collision term to Keccak-256's collision resistance.
2. **The evaluated checks** are Props checked by running Lean, not kernel proofs; `IvChecked` is assumed at setup
   commitments and IVs other than those evaluated (`PatchChecked`, and uniformity over the commitment).
3. **π2's completeness error** `δ2` for π2's Lean prover (the probability layer, `RecCompleteness2`) and the end
   theorem of completeness at π1-rec4 with π1-rec4's honest prover: see [`docs/LEAN_PORT.md`](../../docs/LEAN_PORT.md).
4. **The provers**: the deployed Rust provers are trusted for completeness.
