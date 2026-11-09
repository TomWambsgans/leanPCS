<!-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The structure follows formal/UniSound/UniSound.lean's report. -->

# UniKeccakSound: knowledge soundness of the Keccak VM's univariate verifier

This library proves `formal/UniKeccak`'s two knowledge-soundness statements, `UniKnowledgeSoundnessKeccak` (main
line) and `UniKnowledgeSoundnessKeccakRec3` (π1-rec3's shape). Both are proved at the Keccak-f block
`KeccakFlock.keccakFlockSpec` with the explicit extractor `uniExtractorK`, for every deployment at the reference shape
with leanVM's program IV, and with no other hypothesis. The proofs are sorry-free, use no `native_decide`, and rest
on Lean's three axioms; the root's `#guard_msgs` checks this.

It is a library of `formal/EndToEnd` (`UniKeccakSound`, `srcDir = "../UniKeccakSound"`, `warningAsError`). Its files
are plain, non-`module` Lean.

## The end theorems (`UniKeccakSound/EndClosedK.lean`)

```lean
theorem UniKeccakSound.uniKnowledgeSoundnessKeccak_closed (D : KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv = UniStatement.programIv) :
    UniKnowledgeSoundnessKeccak KeccakFlock.keccakFlockSpec D
        (uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64
theorem UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_closed (D : KDeployment) (hD : D.shape = keccakRefShape)
    (hIv : D.programIv = UniStatement.programIv) :
    UniKnowledgeSoundnessKeccakRec3 KeccakFlock.keccakFlockSpec D
        (uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞))) ∧
      ∀ Q ≤ 2 ^ 64,
        uniBound128 (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)) Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 64
```

- **The reference shape**, `keccakRefShape = keccakShapeOf 721598 [24260, 36229, 24626, 35812, 15509, 17712]`, is
  the 128-signature run:
  - heights `15 16 15 16 14 15`, so `h_SHA3 = 15`; memory `2^20`, bytecode `2^18`;
  - `C1` has `2^27` words, `C2` `2^26`, the setup `2^23`;
  - the batch has 27 rounds (`np = 13` pair rounds at π1-rec3).
- **The bounds**: every round's error is at most `2^32/|E|` (main line) or `2^35/|E|` (π1-rec3). `uniBound128` is
  `UniSound`'s bound at `≥ 128` bits. Its numbers are `UniSound.uniBound128_le_bits` (`2^-64.87` at `Q = 2^64`) and
  `uniBound128_le_bits35` (`2^-64.49`): 128.87 and 128.49 bits as `Q / ε`.
- **The three openings** (`C1`, `C2`, the setup) are charged once, as one union family, at `269 · 2^-137`. The
  setup's `2^23`-word WHIR opening, below `WhirBridge.largeShapes` (`2^24 ..= 2^28`), is certified the same way in
  `Fs/Whir23.lean` (`chkQ_23`, `decide +kernel`; family `kShapes = largeShapes ++ [plainShapeE23]`).

## The route

The proof follows `UniSound`'s, layer by layer:

| layer | files | what |
|---|---|---|
| interfaces, PIOP | `FlockInterfaceK`, `PiopK`, `PiopSoundK`, `PiopK3`, `PiopSoundK3` | Flock's interface on the Keccak-f block (`KFlockSound F κ v`), the identity models (`UniIdsK`, `UniIdsK3`: three commitments, no pending term), the PIOPs proved round-by-round sound (`uniPiopK`, `uniPiopK3`) |
| links, composition | `FsK`, `FinalK`, `FinalK3` | `UniCodeK(3)`, `UniFinalK(3)`, `FsLayer128K(3)`; the composition `uniKnowledgeSoundnessK(3)_bits` |
| Flock | `Flock/` | `KF.flockSoundK_main_closed κ`, `flockSoundK_rec3_closed κ`: the chain programs and their links to `verifyWalkedK`, the generic Flock theorems at `m = 11` slot bits, the catch from `KeccakFlock.structuredTerminal_eq_bilinear`, and `Br.structuredTerminal_eq` (`UniKeccak.structuredTerminal = KeccakFlock.Terminal.structuredTerminal`) |
| code link | `Code/` | `uniCodeKAt`, `uniCodeK3At` (`reduceWithK` as chain programs), `UniOutRootsK(3)`, the counts' zeros, `valsCountK = 118` |
| Fiat–Shamir | `Fs/` | `fsLayer128K_holds`, `fsLayer128K3_holds` and their reference instances. The setup is one tree; `A0` and `B0` are the deployment's constants. WHIR is certified at `2^23` |
| identity model, last link | `Ids/`, `Ids3/` | `uniIdsK`, `uniIdsK3`, `uniFinalK_uniCodeKAt`, `uniFinalK3_uniCodeK3At`, from the bridges below; the bus `BusModelK.mainSound`, `mainSoundSq` |
| bridges | `IdsEval/`, `IdsMain/`, `IdsReal/`, `IdsNum/`, `IdsW/` | `DiffsEvalK`, `MainOfPolysK`, `CvecOkK`, `KvConstraintsK`, `KvRealizesK` (with the SHA3 flushes' agreement `sha3_flushes_eq`), `LaneSlotsK`, `DegBoundK` (`19,339,139`), `RelCountK` (`187`), `HeapGood`, `FunctionalsCorrect 15`, `WeightMleK`, the reference numbers |
| end | `EndK`, `EndRefK`, `EndClosedK` | the end statements from named links (earlier milestones), then closed |

**What the Keccak port changes** against `UniSound`:
- the tables (`tablesKeccak`) and 11 slot bits (`weightAtK`);
- the `END_BIT` constant in `Q_W`'s `in_16` copy;
- Flock's 11 lincheck rounds and its structured terminal, a zero inside Flock's last round. The states carry it from
  `C2`'s round on (`FlockDoneZ`), where `UniSound`'s states carry the pending matrices' claim;
- three openings, and a setup of one tree;
- the Keccak VM's relation `KvHolds` through `kvStack`.

**One statement was strengthened in the process**: the bridge `DiffsEvalK` (`Ids/Build.lean`) assumes round `0` has
at least four challenges. The relations read `α` as the first four, the identities as `alphasOf`, and the two agree
only from four on. Correspondingly, `UniIdsK.diffs_eval` assumes six, and the main line's states record round `0`'s
six challenges after `C2`'s round. None of `UniKeccak`'s statements changed.

## Imports

The library imports the shared libraries' modules for their generic content. These are listed below with what is used;
the sub-libraries' docstrings name the lemmas.

- **Shared, keep**: `Compose`, `WhirBridge`, `Heap`, `Soundness`, `Bridge`, `UniStatement`'s VM-independent steps,
  `FlockSound` (`Flock.lean`, `FlockSq.lean`, `Kronecker.lean`, the generic Flock theorems), `UniKeccak`, `KeccakVm`,
  `KeccakFlock`.
- **Modules imported for their generic lemmas**, next to Lv42-instance content this library does not use:
  - `UniSound` main line:
    - `Prog`, `Prob`, `Sumcheck`, `Piop`, `PiopSound` (`RbrPiop`, `uniRounds`, `SumState`, `prEvent_*`);
    - `Final` (`openedOf` lemmas), `Fs`, `Fs128` (`uniBound128` and its bits);
    - `FsChain`, `FsOps`, `FsProof`, `FsCost`, `FsGame`, `FsWalkProof`, `FsVerifier`, `FsExtract` (the univariate
      chain `uniSpec`/`UPf`/`uView`, `progRun`, the early-stop openings);
    - `CodeBase`, `CodeTables`, `CodeBatch`, `CodeShape`, `CodeZeros`, `CodeLink` (chain-program and `ObsEq` lemmas);
    - `FinalLink`, `Bus`.
  - `UniSound.Ids`: `Model`, `Batch`, `Weights`, `Build`, `Main`, `MainOk`, `Leaves`, `Leaf`, `Cvec`, `CvecOk`,
    `Deployed`, `LvLink`, `LvRealize` (the `LvR` normal form and the five shared opcode tables), `Eval`, `Align`,
    `Degrees`, `Counts`, `Facts`, `FlockEnd`, `BcTuple`, `WeightMle`, `Cantor`, `Poly`. They hold the generic
    identity algebra; only their Lv42-instance theorems are unused.
  - `UniSound.Rec3`: `Piop3`, `PiopSound3`, `Fs3`, `Fs128_3`, `Final3`, `Batch3`, `Pairs`, `BusSq`, `CodeBatch3`,
    `CodeLink3`, `FsOps3`, `FsProof3`, `FsWalkProof3`, `FinalLink3` (`rec3Rounds`, `PairBatch`, `pairBatchRec3`,
    `expandCh`, `obsOf3`, the narrow pairs).
  - `FlockSoundUni`: `Rec3Link` and through it `Link`, `Shape`, `Decode`, `Loops`; `RoundByRound`, `Prefix`, `Catch`,
    `Transcription`, `Tower`, `TxBasic`, `WalkCode` (chain-program decoding, the tower ring claim, the counting lemma).
  - `FlockSound.Main`, `FlockSound.Leanvm`: leanVM's constants (`skipNodes`, `packW`, `fixedPt`). `Flock/Setup.lean`
    generalises them to `m` slot bits.
- **Not imported**: `UniComplete`.

## Build

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only, with formal/leanervm linked
systemd-run --scope -p MemoryMax=12G lake build UniKeccakSound   # every file; the root's #guard_msgs check the axioms
```

## What remains

- **Completeness** (`UniCompletenessKeccak{,Rec3}`) is not in this library: it is proved in [`formal/UniKeccakComplete`](../UniKeccakComplete/README.md)
  (`uniCompletenessKeccak_closed`, `uniCompletenessKeccakRec3_closed`, `Prob.deltaK < 2^-169`).
- **Closed bounds for every valid shape**: the theorems are at the reference shape. Most layers are shape-generic;
  the Fiat–Shamir layer's numbers (`UniShapesK`, `LayoutVarsSmallK`), the identity model's numbers (`DegBoundK`,
  `RelCountK`, `hB`), `FunctionalsCorrect h_SHA3`, `HeapGood` and π1-rec3's odd batch are decided at the reference.
