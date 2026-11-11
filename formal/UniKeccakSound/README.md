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
- **The three openings are the EIP draft's PCS claims** (`UniKeccak.verifyWithK`: each commitment's out-of-domain
  answer read after its root, `WhirBridge.Pcs.pcsVerifyWithHash`). They are charged once, as one union family over
  the PCS claims of every size `2^23 ..= 2^28` (`WhirBridge.Pcs.pcs_union_sound`, `Fs/PcsOpK.lean`, the generic
  opening layer `Compose.GOps`), at `269 · 2^-137` a query. The argument keeps the lists (a claim is checked against the stack the extractor decodes, `GDoomed`
  read as `PcsDoomed`); the out-of-domain binding (`WhirBridge.Pcs.ood_binding_rom`) is not needed for it, so the
  three claims on three commitments are proved separately. The setup's `2^23` words are admissible
  (`Fs/Whir23.lean`, `admissible_k`).

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
| end | `EndK`, `EndRefK`, `EndClosedK` | the end statements from named links, then closed |

**What the Keccak port changes** against `UniSound`:
- the tables (`tablesKeccak`) and 11 slot bits (`weightAtK`);
- the `END_BIT` constant in `Q_W`'s `in_16` copy;
- Flock's 11 lincheck rounds and its structured terminal, a zero inside Flock's last round. The states carry it from
  `C2`'s round on (`FlockDoneZ`), where `UniSound`'s states carry the pending matrices' claim;
- three PCS claims' openings, each commitment's out-of-domain answer in the stream after its root (rounds
  `⟨true, 1, ·⟩`), the roots read as their bytes (`UniStatement.rootOf`), and a setup of one tree whose commitment
  `(root, f(z))` is in the IV;
- the Keccak VM's relation `KvHolds` through `kvStack`.

**One bridge is stronger than its `UniSound` counterpart**: the bridge `DiffsEvalK` (`Ids/Build.lean`) assumes round `0` has
at least four challenges. The relations read `α` as the first four, the identities as `alphasOf`, and the two agree
only from four on. Correspondingly, `UniIdsK.diffs_eval` assumes six, and the main line's states record round `0`'s
six challenges after `C2`'s round. None of `UniKeccak`'s statements changed.

## Imports

Shared libraries: `Compose`, `WhirBridge`, `Heap`, `Soundness`, `Bridge`, `UniStatement`'s VM-independent steps,
`FlockSound`, `UniKeccak`, `KeccakVm`, `KeccakFlock`. It also imports `UniSound` (main line, `Ids`, `Rec3`),
`FlockSoundUni` and `FlockSound.{Main,Leanvm}` for their generic lemmas (chain programs, sumcheck rounds, the identity
algebra, `uniBound128`, the narrow pairs, leanVM's Flock constants, which `Flock/Setup.lean` generalises to `m` slot
bits); their Lv42-instance theorems are unused. `UniComplete` is not imported.

## Build

```sh
cd formal/EndToEnd   # on h1, under /root/pcs-quotient-fv/ only, with formal/leanervm linked
systemd-run --scope -p MemoryMax=12G lake build UniKeccakSound   # every file; the root's #guard_msgs check the axioms
```

## π1-rec4: not proved

`UniKeccak.UniKnowledgeSoundnessKeccakRec4` (π1-rec4's verifier, `UniKeccak.verifyWithK4`) is stated, **not
proved**. What is here: [`Rec4/RingSplit.lean`](UniKeccakSound/Rec4/RingSplit.lean), **`Rec4.ring_split`**: for a
nonzero polynomial of degree at most `1` in each of six variables, split as four drawn with `t` and two drawn with `ρ`
(`SPEC.md` §14.5 (2)), some coefficient in the first four vanishes with probability at most `4/|E|`, and where it does
not, the polynomial vanishes in the last two with probability at most `2/|E|` (Mathlib's Schwartz–Zippel, in two
blocks). That the ring switch's relation is such a polynomial is not stated here.

What a proof needs, against π1-rec3's (`FinalK3.lean`'s `uniKnowledgeSoundnessK3` from `KFlockSound`, `UniIdsK3`,
`PairBatch`, `UniCodeK3`, `UniFinalK3`, `FsLayer128K3`):

1. **The Fiat–Shamir layer for wide draws** (`fsLayer128K3_holds`' analog). `Compose.ListChainK` models a round as a
   root, then values, then `ns + 1` challenges from `ns + 1` successive Keccak-256 calls (`absorbs`, `chalsT`), over a
   table of 32-byte answers. A wide draw takes its `ns + 1` challenges from **one** call's sponge rate, past the digest,
   and π1-rec4's `C2` call absorbs the slices **before** the root (`encM` puts the root first). So the chain needs (a)
   rounds whose challenges are one step's rate, with a table answering the rate (or the digest and an independent
   tail), and a message with the root after values; and (b) **the random-permutation transfer to that table**:
   leanerVM's `Common.keccak256_transfer2` (`Rpm.lean`, `ListChainKRpm.lean`) answers Keccak-256's digest; the rate's
   other lanes (`rateTailOf`) are uniform for a fresh last permutation in the random-permutation model, but no transfer
   here states it. Neither is in this repository.
2. **Flock without its ring map** (`KFlockSound` with the map's six challenges moved out of Flock's rounds:
   `f_0 … f_3` into `C2`'s round, `f_4, f_5` into the values' round, the zerocheck's first coordinate into round `0`),
   the ring switch's bad events assigned to those rounds (`ring_split` is their bound in two blocks), and the PIOP
   (`uniPiopK3`'s states) re-indexed: round `0` draws `c, β, γ, c'`; `C2`'s round `t, f_0 … f_3`; the values' round
   `ρ, λ, f_4, f_5`.
3. **The code link** (`UniCodeK3`'s analog for `reduceWithK4` on those rounds) and the last link.

The arithmetic carries over: a query's error is the sum of its challenges' (π1-rec4's per-query sums are at most
`2^35/|E|`, `params/leanvm_univariate_params.py`, `rounds(.., "rec4")`), so `uniBound128 (2^35/|E|)` and
`uniBound128_le_bits35` (128.49 bits) would apply unchanged; this is modelled, not proved.

## What remains

- **Completeness** (`UniCompletenessKeccak{,Rec3}`) is not in this library: it is proved in [`formal/UniKeccakComplete`](../UniKeccakComplete/README.md)
  (`uniCompletenessKeccak_closed`, `uniCompletenessKeccakRec3_closed`, `Prob.deltaK < 2^-169`).
- **Closed bounds for every valid shape**: the theorems are at the reference shape. Most layers are shape-generic;
  the Fiat–Shamir layer's numbers (`UniShapesK`, `LayoutVarsSmallK`), the identity model's numbers (`DegBoundK`,
  `RelCountK`, `hB`), `FunctionalsCorrect h_SHA3`, `HeapGood` and π1-rec3's odd batch are decided at the reference.
