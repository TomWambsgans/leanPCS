<!-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. -->

# UniKeccakComplete

The completeness half of the Keccak VM's univariate verifier (`formal/UniKeccak`, `crates/leanvm_univariate/KECCAK.md`):
`UniKeccak.UniCompletenessKeccak F D P δ` and `UniCompletenessKeccakRec3 F D P δ` (`UniKeccak/Security.lean`) at the
Keccak-f block `F = KeccakFlock.keccakFlockSpec`, **from a named premise** on the prover. A library of
`formal/EndToEnd` (`UniKeccakComplete`, `srcDir = "../UniKeccakComplete"`, `warningAsError`), plain (non-`module`)
Lean files, since it imports `E2ECompleteness`.

```sh
cd formal/EndToEnd   # on h1
systemd-run --scope -p MemoryMax=12G lake build UniKeccakComplete   # the axiom guards
```

## What is proved

```lean
theorem uniCompletenessKeccak_end (D : KDeployment) (P : KProver D) (hS : KStagedK D keccakMain P) :
    UniCompletenessKeccak KeccakFlock.keccakFlockSpec D P deltaK
theorem uniCompletenessKeccakRec3_end (D : KDeployment) (P : KProver D) (hS : KStagedK D keccakRec3 P) :
    UniCompletenessKeccakRec3 KeccakFlock.keccakFlockSpec D P deltaK
theorem deltaK_lt : deltaK < (2 : ℝ≥0∞)⁻¹ ^ 163
```

- `Staged.lean`: `UniComplete`'s probability layer (`ProbStaged.lean`) at the Keccak experiment
  (`keccakCompletenessExperiment`). If, for every honest witness, the experiment is the verdict of a staged two-call
  run (`KStaged`: up to `C1`'s root, the five chained bus challenges, up to `t`, `t`, the rest), and the run meets the
  probability conditions (`KStaged.Good`: duplex discipline, `N` block calls, the first chain input `88` bytes, bad-`β`
  and bad-`t` counts, `t`'s freshness, the grinding error), then `uniCompletenessKeccak_of_staged` gives the bound
  `Nbad/2^192 + 6/2^256 + (ct/2^192 + εt) + εpow + N²/2^508`. The premise is `KStagedHolds F D v P Nbad ct N εt εpow`.
- `Chain.lean`: the chained challenges' and `t`'s query's probability lemmas (`prEvent_staged5_le`,
  `prEvent_tquery_le`). It is `UniComplete/ProbChain.lean`, copied: the lemmas don't depend on the instruction set,
  and `UniComplete` is BLAKE2s-only.
- `End.lean`: `deltaK` at `Nbad = 2^28 − 1`, `ct = 3·2^17`, `εt = 2^-200`, `εpow = 2^-304`, `N = 2^48`. These are
  UniComplete's numbers except `Nbad`, which is raised from `2^24 − 1` to `2^28 − 1` to cover the Keccak VM's divided
  fingerprints (fewer than `2^28` heap leaves). `deltaK < 2^-163` (about `2^-164`). `KStagedK` is the premise at these
  numbers.

## What is not done

The premise `KStagedK D v P` for an explicit Lean honest prover `P`. This is the analogue of everything in
`formal/UniComplete` beyond its probability layer, about 40,000 lines for the BLAKE2s VM:

- the honest prover itself:
  - the trace placed from a `KvHonest` stack (`honestTrace`);
  - `C1`'s, the setup's and `C2`'s stacks;
  - the bus leaves and the product heap;
  - the quotients and the batching sumcheck's prover (no matrices term for the Keccak verifier);
  - Flock's prover on the Keccak-f block (zerocheck with skip, 11 lincheck rounds, the slices, the structured
    terminal, the ring map in tower order);
  - the three WHIR openings (WHIR at `2^23` words: UniKeccakSound's `Fs/Whir23.lean`);
- the staging of the prover and the verifier at the bus challenges and at `t` (`ProbSplit`, `ProbHyp`);
- the deterministic core: the Keccak verifier synchronises with the prover's stream; every relation at `t` holds and
  the batch's terminal is zero (`AlgC`, `AlgH`, `Combine`, `BatchProof`, `CoreBatch`); the openings accept;
- the bad-event counts at the Keccak shape (`BadFpCard`, `BadTCard`, `tQueryFresh`), the costs (`ProverCost`,
  `FlockCost`) and the grinding (`ProbGrind`).
