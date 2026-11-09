-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Transcribed from `formal/UniStatement` (`Transcript.lean`, `Flock.lean`, `Rec.lean`, `Opening.lean`) and
-- `formal/UniKeccak` (`Verifier.lean`, `Opening.lean`, `Security.lean`), with Keccak-256 an explicit call, as
-- `formal/EndToEnd/Completeness/E2ECompleteness/WithHash.lean` rewrites `formal/Statement`; the openings and the
-- commitments are WithHash's (`openingWithH`, `commitWithH`, after leanerVM `mumbai` 6175f1a0's `runWithHash`,
-- `buildTreeWithHash`, MIT OR Apache-2.0).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/VerifierH.lean` and `Rec3VerifierH.lean`.
import UniKeccak.Security
import E2ECompleteness.WithHash

/-!
# The Keccak verifier and setup with Keccak-256 an explicit call

`formal/UniKeccak`'s verifier and setup are written over a permutation `F`, every Keccak-256 the sponge over it
(`keccak256With F`). Here each function that hashes is rewritten with Keccak-256 a separate function `H` (`…H`), the
code text the Statement's, only the hash changed:

* the transcript: `seedWithH`, `sampleH`, `samplesH`, `sumcheckH`, `sampleNarrowH`, `sampleDrawnH`, `drawRunH`,
  `sumcheckDrawnH`, `sumcheckPairsDrawnH`;
* Flock on the Keccak-f block: `Flock.zerocheckFsH`, `Flock.ringEndH`, `frontKH`, `verifyWalkedKH`;
* the batch `batchKH`, the walk `reduceWithKH`, the run on calldata `runWithKH`;
* the Keccak contract's IV `contractIvKWithH`, `KDeployment.ivWithH`; `PCS_OPEN` `pcsOpenWithH` (WithHash's
  `openingWithH`), the verifier `verifyWithKH`, the deployed verifier `KDeployment.verifierWithH`;
* the setup `setupTreeKWithH` (WithHash's `commitWithH`).

**At `H = keccak256With F`** each is the Statement's (`…_eqH`): by `rfl` but where an opening or a commitment is
involved (WithHash's `openingWith_eqH`, `commitWith_eqH`).
-/

open UniStatement UniKeccak LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

namespace UniKeccakComplete

/-! ## The transcript -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- `seedWith` with Keccak-256 `H`. -/
def seedWithH (iv publicInput : List UInt8) : m Digest := H (name ++ iv ++ publicInput)

/-- `sample` with Keccak-256 `H`. -/
def sampleH : ChanM m E := do
  let c ← get
  let input := digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList
  let state ← (H input : m Digest)
  let x := PcsQuotient.Transcript.challengeOf state
  set { c with absorbed := c.cursor, state := state, challenges := c.challenges.push x }
  return x

/-- `samples` with Keccak-256 `H`. -/
def samplesH (count : ℕ) : ChanM m (List E) := do
  let mut out : Array E := #[]
  for _ in [0:count] do
    out := out.push (← sampleH H)
  return out.toList

/-- `sumcheck` with Keccak-256 `H`. -/
def sumcheckH (claim : E) (count : ℕ) (equalities : List (Option E)) : ChanM m (List E × E) := do
  let mut point : Array E := #[]
  let mut claim := claim
  for equality in equalities do
    let message ← roundPoly (m := m) count claim equality
    let challenge ← sampleH H
    point := point.push challenge
    claim := polyEval message challenge
  return (point.toList, claim)

/-- `sampleNarrow` with Keccak-256 `H`. -/
def sampleNarrowH : ChanM m E := do
  let c ← get
  let input := digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList
  let state ← (H input : m Digest)
  let x := narrowE (PcsQuotient.Transcript.challengeOf state)
  set { c with absorbed := c.cursor, state := state, challenges := c.challenges.push x }
  return x

/-- `sampleDrawn` with Keccak-256 `H`. -/
def sampleDrawnH (narrow : Bool) : ChanM m E :=
  match narrow with
  | true => sampleNarrowH H
  | false => sampleH H

/-- `drawRun` with Keccak-256 `H`. -/
def drawRunH (fs : FsShape) (count : ℕ) : ChanM m (List E) :=
  match fs with
  | .main => samplesH H count
  | .rec1 | .rec2 | .rec3 =>
    if count = 0 then pure [] else do
      let c ← sampleH H
      pure (squares c count)

/-- `sumcheckDrawn` with Keccak-256 `H`. -/
def sumcheckDrawnH (claim : E) (count : ℕ) (equalities : List (Option E)) (narrow : Bool) :
    ChanM m (List E × E) := do
  let mut point : Array E := #[]
  let mut claim := claim
  for equality in equalities do
    let message ← roundPoly (m := m) count claim equality
    let challenge ← sampleDrawnH H narrow
    point := point.push challenge
    claim := polyEval message challenge
  return (point.toList, claim)

/-- `sumcheckPairsDrawn` with Keccak-256 `H`. -/
def sumcheckPairsDrawnH (claim : E) (degree vars : ℕ) (narrow : Bool) : ChanM m (List E × List E × E) := do
  let mut point : Array E := #[]
  let mut challenges : Array E := #[]
  let mut claim := claim
  for _ in [0:vars / 2] do
    let message ← pairRoundPoly (m := m) degree claim
    let z ← sampleDrawnH H narrow
    point := point ++ (pairPoint z).toArray
    challenges := challenges.push z
    claim := polyEval message z
  if vars % 2 = 1 then
    let (last, end_) ← sumcheckDrawnH H claim (degree + 1) [none] narrow
    challenges := challenges ++ last.toArray
    point := point ++ last.toArray
    claim := end_
  return (point.toList, challenges.toList, claim)

end With

/-! ## Flock on the Keccak-f block -/

namespace Flock

open UniStatement.Flock

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- `Flock.zerocheckFs` with Keccak-256 `H`. -/
def zerocheckFsH (logN k : ℕ) (fs : FsShape := .main) : ChanM m (Option E × List E × E × E × E) := do
  let sampled ← drawRunH H fs (logN - k - nFixed)
  let r : List (Option E) := (fixedChallenges ++ sampled).map some
  let (zSkip, claim) ← if k > 0 then do
      let coset ← nextScalars (m := m) (2 ^ k)
      let z ← sampleH H
      pure (some z, lagrangeInterpolate (2 ^ (k + 1)) (List.replicate (2 ^ k) 0 ++ coset) z)
    else pure (none, 0)
  let (chi, running) ← sumcheckH H claim 3 r
  let vA ← nextScalar (m := m)
  let vB ← nextScalar (m := m)
  return (zSkip, chi, vA, vB, running + vA * vB)

/-- `Flock.ringEnd` with Keccak-256 `H`. -/
def ringEndH (variant : Variant) (s : List E) : ChanM m Flock.End := do
  let map ← samplesH H ringMapShifts.length
  let target := if variant.slices = .tower then towerTarget s map
    else polyEval (s.map fun value ↦ ringMap value map) gen
  return .ring map target

end With

end Flock

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

open UniStatement.Flock in
/-- `UniKeccak.frontK` with Keccak-256 `H`. -/
def frontKH (logN : ℕ) (v : KeccakVariant) : ChanM m Front := do
  let k := v.skip
  let (zSkip, chi, vA, vB, vC) ← Flock.zerocheckFsH H logN k v.fs
  let rowLow := chi.take (packing - k)
  let rest := chi.drop (packing - k)
  let chiIn := rest.take lincheckRoundsK
  let chiRest := rest.drop lincheckRoundsK
  let alpha ← sampleH H
  let claim := vA + alpha * vB + epow alpha 2 * vC + epow alpha 3
  let (roundChallenges, rLc) ← sumcheckH H claim 3 (List.replicate lincheckRoundsK none)
  let chiInPrime := roundChallenges.reverse
  let s ← nextScalars (m := m) kBits
  return ⟨zSkip, chi, rowLow, chiIn, chiInPrime, alpha, rLc, some s, chiInPrime ++ chiRest⟩

/-- `UniKeccak.verifyWalkedK` with Keccak-256 `H`. -/
def verifyWalkedKH (logN : ℕ) (v : KeccakVariant) : ChanM m (List E × UniStatement.Flock.End) := do
  let fr ← frontKH H logN v
  let s := fr.slices.getD []
  requireZero (m := m) (structuredTerminal fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime s fr.alpha + fr.rLc)
  let end_ ← Flock.ringEndH H v.flock s
  return (fr.point, end_)

/-- `UniKeccak.batchK` with Keccak-256 `H`. -/
def batchKH (fs : FsShape) (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) : ChanM m (List (Commitment × Opening)) := do
  let lambda ← sampleH H
  let vars := (layouts.map (·.2.vars)).foldl max 0
  let (target, _) := combined.foldl (fun (acc : E × E) (_, claim) ↦
    (acc.1 + acc.2 * claim.value, acc.2 * lambda)) (0, 1)
  let (r, last) ← match fs with
    | .rec3 => do
      let (r, _, last) ← sumcheckPairsDrawnH H target 2 vars true
      pure (r, last)
    | .main | .rec1 | .rec2 => sumcheckDrawnH H target 3 (List.replicate vars none) fs.narrow
  let values ← nextScalars (m := m) combined.length
  let layoutOf (c : Commitment) : StackLayout := ((layouts.find? (·.1 == c)).map (·.2)).getD default
  let (sum, _, openings) := (combined.zip values).foldl
    (fun (acc : E × E × Array (Commitment × Opening)) ((commitment, claim), value) ↦
      let (sum, scale, openings) := acc
      let layout := layoutOf commitment
      let weight := weightAtK claim layout r ringMap
      let extension := (List.range' layout.vars (vars - layout.vars)).foldl
        (fun e j ↦ e * (1 + r.getD j 0)) 1
      (sum + scale * weight * extension * value, scale * lambda,
        openings.push (commitment, .point (r.take layout.vars) value none)))
    (0, 1, #[])
  requireZero (m := m) (sum + last)
  return openings.toList

/-- `UniKeccak.reduceWithK` with Keccak-256 `H`. -/
def reduceWithKH (shape : Shape) (publicWords : List E) (v : KeccakVariant) (mode : ClaimsMode) :
    ChanM m Reduced := do
  if !shape.validate true then throw .invalidShape
  let fs := v.fs
  let heights := shape.heights
  let heap := shape.heap
  let rW := shape.constraintVars
  let h := heap.h
  let counts ← countBits (m := m) heights
  let root1 ← nextRoot (m := m)
  let alphas ← drawRunH H fs 4
  let beta ← sampleH H
  let gamma ← sampleH H
  let weights := eqKernel alphas
  let logN := keccakR1csLogSize + heights.getD opSha3 0
  let (flockPoint, flockEnd) ← verifyWalkedKH H logN v
  let root2 ← nextRoot (m := m)
  let t ← sampleH H
  let w := digits t (max h (rW + 4) + 2)
  let active := (counts.zip heights).map fun (bits, r) ↦ activeVanishingFromBits w bits r
  let mut relations : Array Relation := #[]
  let mut parts : Array TablePart := #[]
  for table in tablesKeccak do
    let (part, rels) ← tablePart (m := m) table (heights.getD table.opcode 0) weights beta w
    parts := parts.push part
    relations := relations ++ rels.toArray
  let lm := shape.logMemory
  let memoryFinalCount ← nextScalar (m := m)
  let address ← nextScalar (m := m)
  let memoryPull ← nextScalar (m := m)
  relations := relations.push (Relation.equal (.memory 3) (w.take lm) memoryFinalCount)
  relations := relations.push (Relation.equal .address (w.take lm) address)
  relations := relations.push ⟨(List.range 3).map (fun k ↦ term (.memory k) (w.take lm) (weights.getD (3 + k) 0)),
    memoryPull + beta + weights.getD 0 0 * sepMem + weights.getD 1 0 * address +
      weights.getD 2 0 * memoryFinalCount⟩
  let memoryPush := memoryPull + weights.getD 2 0 * (1 + memoryFinalCount)
  let lb := shape.logBytecode
  let bytecodeFinalCount ← nextScalar (m := m)
  let bytecodePull ← nextScalar (m := m)
  relations := relations.push (Relation.equal .bytecodeFinal (w.take lb) bytecodeFinalCount)
  relations := relations.push (Relation.equal .bytecodeTuple (alphas ++ w.take lb)
    (bytecodePull + beta + weights.getD 2 0 * bytecodeFinalCount))
  let bytecodePush := bytecodePull + weights.getD 2 0 * (1 + bytecodeFinalCount)
  let heapValue ← nextScalar (m := m)
  let constraintValue ← nextScalar (m := m)
  let (constraint, quotientDegree) :=
    constraintRelationK shape parts.toList publicWords gamma t constraintValue w
  relations := relations.push constraint
  let constraintChunks := chunks (quotientDegree + 1)
  let c2Columns : List (Column × ℕ × Bool) :=
    [(.heap, h, true), (.treeQuotient 0, h, true), (.treeQuotient 1, 0, true)] ++
      (constraintChunks.zip (List.range constraintChunks.length)).map fun (e, c) ↦
        (Column.constraintQuotient c, e, true)
  let (heapRels, leafColumns) := heapRelations shape active parts.toList weights beta heapValue
    constraintValue memoryPull memoryPush bytecodePull bytecodePush w constraintChunks
  relations := relations ++ heapRels.toArray
  let c2Columns := c2Columns ++ leafColumns
  let mut ringMap : Option (List E) := none
  match flockEnd with
  | .ring map target =>
    if mode == .point then
      relations := relations.push ⟨[⟨.qflock, flockPoint, ringTwist, 1⟩], target⟩
      ringMap := some map
    else
      let coefficients := UniStatement.Flock.towerCoefficients map
      relations := relations.push ⟨(coefficients.zip (List.range coefficients.length)).map
        (fun (c, k) ↦ ⟨.qflock, flockPoint, k, c⟩), target⟩
  | .combination _ _ => pure ()
  let rho ← sampleH H
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine relations.toList c rho).map (c, ·)
  let stackLayouts := layoutsK shape c2Columns
  let stackVars := stackLayouts.map fun (c, l) ↦ (c, l.vars)
  let openings ← match mode with
    | .weighted => pure (combined.map fun (c, claim) ↦ (c, Opening.weighted claim))
    | .point => batchKH H fs combined stackLayouts ringMap
  return ⟨(root1, root2), openings, none, relations.size, stackVars, stackLayouts⟩

/-- `UniKeccak.runWithK` with Keccak-256 `H`. -/
def runWithKH (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (v : KeccakVariant)
    (mode : ClaimsMode) : m Outcome := do
  let seed ← seedWithH H iv publicInput
  let walkM : ChanM m Reduced := do
    let r ← reduceWithKH H shape (publicWordsOf publicInput) v mode
    finish (m := m)
    return r
  let (result, chan) ← (walkM.run).run (Chan.start seed stream)
  return ⟨result, chan⟩

/-- `UniKeccak.contractIvKWith` with Keccak-256 `H`. -/
def contractIvKWithH (s : Shape) (v : KeccakVariant) (programIv : List UInt8) (roots : SetupRoots) :
    m (List UInt8) := do
  let d ← H (ivTag ++ programIv ++ digestBytes roots.bytecode ++
    shapeBytes s ++ (layoutWordsK s).flatten ++ variantBytesK v)
  return digestBytes d

/-- `KDeployment.ivWith` with Keccak-256 `H`. -/
def KDeployment.ivWithH (D : KDeployment) (v : KeccakVariant) (roots : SetupRoots) : m (List UInt8) :=
  contractIvKWithH H D.shape v D.programIv roots

end With

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- `pcsOpenWith` with Keccak-256 `H`: WithHash's `openingWithH` on the plain layout. -/
def pcsOpenWithH (vars : ℕ) (root : Digest) (claims : List PcsQuotient.Claim)
    (proof : LeanVM.Protocol.Compile.Proof) : m Bool :=
  E2ECompleteness.openingWithH H F (plainLayout vars) root claims proof

/-- `UniKeccak.verifyWithK` with Keccak-256 `H`. -/
def verifyWithKH (shape : Shape) (v : KeccakVariant) (iv : List UInt8) (roots : SetupRoots)
    (publicInput : Vector UInt8 32) (proof : KeccakProof) : m Bool := do
  let o ← runWithKH H shape iv publicInput.toList proof.stream v .point
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let words := layoutWordsK shape
    let callOf : Commitment → Digest × List UInt8 × LeanVM.Protocol.Compile.Proof
      | .c1 => (rootOf r.roots.1, words.getD 0 [], proof.c1)
      | .c2 => (rootOf r.roots.2, words.getD 1 [], proof.c2)
      | .setup => (roots.bytecode, words.getD 2 [], proof.setup)
    let mut ok := r.openings.map (·.1) == commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        let (root, word, p) := callOf c
        ok := ok && (← pcsOpenWithH H F (layoutWordVars word) root [⟨pt, value⟩] p)
      | _ => ok := false
    if r.matrices.isSome then ok := false
    return ok

/-- `KDeployment.verifierWith` with Keccak-256 `H`. -/
def KDeployment.verifierWithH (D : KDeployment) (v : KeccakVariant) (roots : SetupRoots)
    (input : Vector UInt8 32) (proof : KeccakProof) : m Bool := do
  verifyWithKH H F D.shape v (← KDeployment.ivWithH H D v roots) roots input proof

/-- `setupTreeKWith` with Keccak-256 `H` (WithHash's `commitWithH`). The setup only hashes: `_F` is unused, there
for the two-call signature the end statements use. -/
def setupTreeKWithH (_F : KeccakState → m KeccakState) (D : KDeployment) : m LeanVM.Prover.Tree :=
  E2ECompleteness.commitWithH H (setupLayout D.shape).vars (setupStackK D.prog D.shape)

end With

/-! ## At `H = keccak256With F` -/

section Eq

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem seedWith_eqH (iv publicInput : List UInt8) :
    seedWith F iv publicInput = seedWithH (keccak256With F) iv publicInput := rfl

theorem sample_eqH : sample F = sampleH (keccak256With F) := rfl

theorem samples_eqH (count : ℕ) : samples F count = samplesH (keccak256With F) count := rfl

theorem sumcheck_eqH (claim : E) (count : ℕ) (equalities : List (Option E)) :
    sumcheck F claim count equalities = sumcheckH (keccak256With F) claim count equalities := rfl

theorem drawRun_eqH (fs : FsShape) (count : ℕ) : drawRun F fs count = drawRunH (keccak256With F) fs count := rfl

theorem sumcheckDrawn_eqH (claim : E) (count : ℕ) (equalities : List (Option E)) (narrow : Bool) :
    sumcheckDrawn F claim count equalities narrow =
      sumcheckDrawnH (keccak256With F) claim count equalities narrow := rfl

theorem sumcheckPairsDrawn_eqH (claim : E) (degree vars : ℕ) (narrow : Bool) :
    sumcheckPairsDrawn F claim degree vars narrow = sumcheckPairsDrawnH (keccak256With F) claim degree vars narrow :=
  rfl

theorem verifyWalkedK_eqH (logN : ℕ) (v : KeccakVariant) :
    verifyWalkedK F logN v = verifyWalkedKH (keccak256With F) logN v := rfl

theorem batchK_eqH (fs : FsShape) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (ringMap : Option (List E)) :
    batchK F fs combined layouts ringMap = batchKH (keccak256With F) fs combined layouts ringMap := rfl

/-- The walk at `H = keccak256With F`: its parts rewritten, the rest the same code (a plain `rfl` from the two
names times out in the elaborator). -/
theorem reduceWithK_eqH (shape : Shape) (publicWords : List E) (v : KeccakVariant) (mode : ClaimsMode) :
    reduceWithK F shape publicWords v mode = reduceWithKH (keccak256With F) shape publicWords v mode := by
  unfold reduceWithK reduceWithKH
  simp only [drawRun_eqH, sample_eqH, verifyWalkedK_eqH, batchK_eqH]
  rfl

theorem runWithK_eqH (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (v : KeccakVariant)
    (mode : ClaimsMode) :
    runWithK F shape iv publicInput stream v mode = runWithKH (keccak256With F) shape iv publicInput stream v mode := by
  unfold runWithK runWithKH
  simp only [seedWith_eqH, reduceWithK_eqH]

theorem contractIvKWith_eqH (s : Shape) (v : KeccakVariant) (programIv : List UInt8) (roots : SetupRoots) :
    contractIvKWith F s v programIv roots = contractIvKWithH (keccak256With F) s v programIv roots := rfl

theorem ivWith_eqH (D : KDeployment) (v : KeccakVariant) (roots : SetupRoots) :
    D.ivWith F v roots = KDeployment.ivWithH (keccak256With F) D v roots := rfl

theorem pcsOpenWith_eqH (vars : ℕ) (root : Digest) (claims : List PcsQuotient.Claim)
    (proof : LeanVM.Protocol.Compile.Proof) :
    pcsOpenWith F vars root claims proof = pcsOpenWithH (keccak256With F) F vars root claims proof :=
  E2ECompleteness.openingWith_eqH F _ _ _ _

theorem verifyWithK_eqH (shape : Shape) (v : KeccakVariant) (iv : List UInt8) (roots : SetupRoots)
    (publicInput : Vector UInt8 32) (proof : KeccakProof) :
    verifyWithK F shape v iv roots publicInput proof =
      verifyWithKH (keccak256With F) F shape v iv roots publicInput proof := by
  unfold verifyWithK verifyWithKH
  simp only [runWithK_eqH, pcsOpenWith_eqH]
  rfl

/-- **The deployed Keccak verifier at `H = keccak256With F`** is the Statement's. -/
theorem verifierWith_eqH :
    KDeployment.verifierWith F = KDeployment.verifierWithH (keccak256With F) F := by
  funext D v roots input proof
  simp only [KDeployment.verifierWith, KDeployment.verifierWithH, ivWith_eqH, verifyWithK_eqH]

/-- **The setup at `H = keccak256With F`** is the Statement's. -/
theorem setupTreeKWith_eqH (D : KDeployment) :
    setupTreeKWith F D = setupTreeKWithH (keccak256With F) F D := by
  simp only [setupTreeKWith, setupTreeKWithH, E2ECompleteness.commitWith_eqH]

end Eq

end UniKeccakComplete
