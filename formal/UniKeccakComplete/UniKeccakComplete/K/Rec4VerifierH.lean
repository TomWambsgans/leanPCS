-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `formal/UniKeccak/UniKeccak/Verifier4.lean`
-- (`reduceWithK4`, `runWithK4`), `formal/UniKeccak/UniKeccak/Pcs.lean` (`verifyWithK4`), `Security.lean`
-- (`KDeployment.verifierWith4`) and `formal/UniStatement/UniStatement/Rec.lean` (`sampleWide`,
-- `Flock.zerocheckFirst`), with Keccak-256 and its rate explicit calls, as `VerifierH.lean` rewrites π1-rec3's.
import UniKeccakComplete.K.VerifierH
import UniKeccakComplete.K.Rec4Couple

/-!
# π1-rec4's verifier with Keccak-256 and its rate explicit

`formal/UniKeccak`'s π1-rec4 verifier is written over a permutation `F`: every Keccak-256 the sponge over it, every
wide draw the sponge's rate after its last permutation (`UniStatement.sampleWide`). Here it is rewritten with
Keccak-256 a function `H` (as `VerifierH.lean`) and its rate a function `W` (`…H4`), the code text the Statement's:
`sampleWideH` (the wide draw: one call of `W`, the challenges `challengeAt` of its bytes, the new state its digest
`digestOfRate`), `Flock.zerocheckFirstH`, `frontKH4`, `verifyWalkedKH4`, `batchKH4`, `reduceWithKH4`, `runWithKH4`,
`verifyWithKH4`, `KDeployment.verifierWith4H`.

**At `H = keccak256With F`, `W = rateOfState <$> keccak256StateWith F`** each is the Statement's (`…_eqH4`): the
rate's bytes are `rateBytesOf` (`rateOfState_toList`) and its digest `digestOfState` (`digestOfRate_rateOfState`).
-/

open UniStatement UniKeccak LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Rpm (lanesBytes)

set_option autoImplicit false

namespace UniKeccakComplete.Rec4

/-! ## The rate of a state -/

theorem take_lanesBytes (l : List UInt64) (n : ℕ) : (LeanVM.Rpm.lanesBytes l).take (8 * n) =
    LeanVM.Rpm.lanesBytes (l.take n) := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [LeanVM.Rpm.lanesBytes_cons, show 8 * (n + 1) = (wordBytes a).length + 8 * n by
        rw [LeanVM.Rpm.wordBytes_len]; ring, List.take_length_add_append, ih, List.take_succ_cons,
        LeanVM.Rpm.lanesBytes_cons]

theorem toRBlock_toList (B : Common.KBlock) :
    (UniKeccakSound.Rec4.toRBlock B).1.toList = B.1.toList ++ B.2.toList := by
  refine List.ext_getElem (by simp) fun k h1 h2 ↦ ?_
  simp only [UniKeccakSound.Rec4.toRBlock, Vector.toList_ofFn, List.getElem_ofFn]
  by_cases hk : k < 32
  · simp only [hk, ↓reduceDIte]
    rw [List.getElem_append_left (by simpa using hk)]
    simp
  · simp only [hk, ↓reduceDIte]
    rw [List.getElem_append_right (by simp; omega)]
    simp

/-- **The rate of a state is its rate's bytes** (`rateBytesOf`: lanes `0 … 16`, little-endian). -/
theorem rateOfState_toList (st : KeccakState) : (rateOfState st).toList = rateBytesOf st := by
  have h1 : (rateOfState st).toList = ((LeanVM.KState.toRpm st).toBytes).take 136 := by
    show (UniKeccakSound.Rec4.toRBlock (LeanVM.KState.toRpm st).1).1.toList = _
    rw [toRBlock_toList, Common.KState.toBytes, List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp)]
  have hl : st.toList.take 17 = (List.range 17).map (Keccak.lane st) := by
    refine List.ext_getElem (by simp) fun k hk1 hk2 ↦ ?_
    simp only [List.length_map, List.length_range] at hk2
    simp only [List.getElem_take, List.getElem_map, List.getElem_range, Vector.getElem_toList]
    rw [LeanVM.Rpm.lane_eq_getElem _ _ (by omega)]
  rw [h1, LeanVM.Rpm.toBytes_toRpm, show (136 : ℕ) = 8 * 17 from rfl, take_lanesBytes, hl]
  unfold rateBytesOf LeanVM.Rpm.lanesBytes
  rw [List.flatMap_map]

/-- **A rate's digest is read off its first 32 bytes.** -/
theorem digestOfRate_eq_of_take (r : RateB) (d : Digest) (h : r.toList.take 32 = digestBytes d) :
    digestOfRate r = d := by
  have e : (Vector.ofFn fun i : Fin 32 ↦ r[i.val]) = LeanVM.Rpm.Digest.toRpm d := by
    apply Vector.toList_inj.mp
    rw [LeanVM.Rpm.toList_digestToRpm]
    show _ = digestBytes d
    rw [← h]
    refine List.ext_getElem (by simp) fun k h1 h2 ↦ ?_
    simp
  rw [digestOfRate, e, LeanVM.Rpm.digestOfRpm_toRpm]

/-- **The rate's digest of a state is its digest.** -/
theorem digestOfRate_rateOfState (st : KeccakState) : digestOfRate (rateOfState st) = digestOfState st := by
  refine digestOfRate_eq_of_take _ _ ?_
  rw [rateOfState_toList, rateBytesOf_eq]
  exact List.take_left' (digestBytes_length_eq _)

/-! ## The wide draw and Flock's zerocheck -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (W : List UInt8 → m RateB)

/-- **`sampleWide` with Keccak-256's rate `W`**: one call of `W` on the state and the bytes since the last challenge;
the challenges `challengeAt` of its bytes, the new state its digest. -/
def sampleWideH (count : ℕ) : ChanM m (List E) := do
  let c ← get
  let input := digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList
  let r ← (W input : m RateB)
  let xs := (List.range count).map (challengeAt r.toList)
  set { c with absorbed := c.cursor, state := digestOfRate r, challenges := c.challenges ++ xs.toArray }
  return xs

namespace Flock

open UniStatement.Flock

/-- `Flock.zerocheckFirst` with Keccak-256 `H`. -/
def zerocheckFirstH (logN k : ℕ) (c : E) : ChanM m (Option E × List E × E × E × E) := do
  let sampled := squares c (logN - k - nFixed)
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

end Flock

open UniStatement.Flock in
/-- `UniKeccak.frontK4` with Keccak-256 `H`. -/
def frontKH4 (logN : ℕ) (v : KeccakVariant) (c : E) : ChanM m Front := do
  let k := v.skip
  let (zSkip, chi, vA, vB, vC) ← Flock.zerocheckFirstH H logN k c
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

/-- `UniKeccak.verifyWalkedK4` with Keccak-256 `H`. -/
def verifyWalkedKH4 (logN : ℕ) (v : KeccakVariant) (c : E) : ChanM m (List E × List E) := do
  let fr ← frontKH4 H logN v c
  let s := fr.slices.getD []
  requireZero (m := m) (structuredTerminal fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime s fr.alpha + fr.rLc)
  return (fr.point, s)

/-- `UniKeccak.batchK4` with Keccak-256 `H`. -/
def batchKH4 (lambda : E) (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) : ChanM m (List (Commitment × Opening)) := do
  let vars := (layouts.map (·.2.vars)).foldl max 0
  let (target, _) := combined.foldl (fun (acc : E × E) (_, claim) ↦
    (acc.1 + acc.2 * claim.value, acc.2 * lambda)) (0, 1)
  let (r, _, last) ← sumcheckPairsDrawnH H target 2 vars true
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

/-- `UniKeccak.reduceWithK4` with Keccak-256 `H` and its rate `W`. -/
def reduceWithKH4 (shape : UniStatement.Shape) (publicWords : List E) (v : KeccakVariant) (mode : ClaimsMode) :
    ChanM m Reduced := do
  if !shape.validate true then throw .invalidShape
  let heights := shape.heights
  let heap := shape.heap
  let rW := shape.constraintVars
  let h := heap.h
  let counts ← countBits (m := m) heights
  let root1 ← nextRoot (m := m)
  let ood1 ← nextScalar (m := m)
  let bus ← sampleWideH W 4
  let alphas := squares (bus.getD 0 0) 4
  let beta := bus.getD 1 0
  let gamma := bus.getD 2 0
  let weights := eqKernel alphas
  let logN := keccakR1csLogSize + heights.getD opSha3 0
  let (flockPoint, slices) ← verifyWalkedKH4 H logN v (bus.getD 3 0)
  let root2 ← nextRoot (m := m)
  let ood2 ← nextScalar (m := m)
  let pointDraw ← sampleWideH W 5
  let t := pointDraw.getD 0 0
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
  let late ← sampleWideH W 4
  let rho := late.getD 0 0
  let lambda := late.getD 1 0
  let map := pointDraw.drop 1 ++ [late.getD 2 0, late.getD 3 0]
  let target := UniStatement.Flock.towerTarget slices map
  let mut ringMap : Option (List E) := none
  if mode == .point then
    relations := relations.push ⟨[⟨.qflock, flockPoint, ringTwist, 1⟩], target⟩
    ringMap := some map
  else
    let coefficients := UniStatement.Flock.towerCoefficients map
    relations := relations.push ⟨(coefficients.zip (List.range coefficients.length)).map
      (fun (c, k) ↦ ⟨.qflock, flockPoint, k, c⟩), target⟩
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine relations.toList c rho).map (c, ·)
  let stackLayouts := layoutsK shape c2Columns
  let stackVars := stackLayouts.map fun (c, l) ↦ (c, l.vars)
  let openings ← match mode with
    | .weighted => pure (combined.map fun (c, claim) ↦ (c, Opening.weighted claim))
    | .point => batchKH4 H lambda combined stackLayouts ringMap
  return ⟨(root1, root2), openings, none, relations.size, stackVars, stackLayouts, (ood1, ood2)⟩

/-- `UniKeccak.runWithK4` with Keccak-256 `H` and its rate `W`. -/
def runWithKH4 (shape : UniStatement.Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (v : KeccakVariant)
    (mode : ClaimsMode) : m Outcome := do
  let seed ← seedWithH H iv publicInput
  let walkM : ChanM m Reduced := do
    let r ← reduceWithKH4 H W shape (publicWordsOf publicInput) v mode
    finish (m := m)
    return r
  let (result, chan) ← (walkM.run).run (Chan.start seed stream)
  return ⟨result, chan⟩

end With

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (W : List UInt8 → m RateB)
  (F : KeccakState → m KeccakState)

/-- `UniKeccak.verifyWithK4` with Keccak-256 `H` and its rate `W`. -/
def verifyWithKH4 (shape : UniStatement.Shape) (v : KeccakVariant) (iv : List UInt8) (roots : SetupRootsK)
    (publicInput : Vector UInt8 32) (proof : KeccakProof) : m Bool := do
  let o ← runWithKH4 H W shape iv publicInput.toList proof.stream v .point
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let mut ok := r.openings.map (·.1) == commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        ok := ok && (← pcsOpenKH H F (stackVarsK shape c) (commitOfK roots r c).1 (commitOfK roots r c).2 pt value
          (proof.openingOf c))
      | _ => ok := false
    if r.matrices.isSome then ok := false
    return ok

/-- `KDeployment.verifierWith4` with Keccak-256 `H` and its rate `W`. -/
def KDeployment.verifierWith4H (D : KDeployment) (roots : SetupRootsK) (input : Vector UInt8 32)
    (proof : KeccakProof) : m Bool := do
  verifyWithKH4 H W F D.shape keccakRec4 (← KDeployment.ivWithH H D keccakRec4 roots) roots input proof

end With

/-! ## At `H = keccak256With F`, `W` its rate -/

section Eq

variable {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState)

/-- Keccak-256's rate over `F`. -/
def rateWith (x : List UInt8) : m RateB := rateOfState <$> keccak256StateWith F x

theorem sampleWide_eqH4 (count : ℕ) : sampleWide F count = sampleWideH (rateWith F) count := by
  unfold sampleWide sampleWideH rateWith
  refine bind_congr fun c ↦ ?_
  simp only [liftM_map, bind_map_left, rateOfState_toList, digestOfRate_rateOfState]

omit [LawfulMonad m] in
theorem zerocheckFirst_eqH4 (logN k : ℕ) (c : E) :
    UniStatement.Flock.zerocheckFirst F logN k c = Flock.zerocheckFirstH (keccak256With F) logN k c := rfl

omit [LawfulMonad m] in
theorem verifyWalkedK4_eqH4 (logN : ℕ) (v : KeccakVariant) (c : E) :
    verifyWalkedK4 F logN v c = verifyWalkedKH4 (keccak256With F) logN v c := rfl

omit [LawfulMonad m] in
theorem batchK4_eqH4 (lambda : E) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (ringMap : Option (List E)) :
    batchK4 F lambda combined layouts ringMap = batchKH4 (keccak256With F) lambda combined layouts ringMap := rfl

theorem reduceWithK4_eqH4 (shape : UniStatement.Shape) (publicWords : List E) (v : KeccakVariant)
    (mode : ClaimsMode) :
    reduceWithK4 F shape publicWords v mode = reduceWithKH4 (keccak256With F) (rateWith F) shape publicWords v mode := by
  unfold reduceWithK4 reduceWithKH4
  simp only [sampleWide_eqH4, verifyWalkedK4_eqH4, batchK4_eqH4]
  rfl

theorem runWithK4_eqH4 (shape : UniStatement.Shape) (iv publicInput : List UInt8) (stream : Array UInt8)
    (v : KeccakVariant) (mode : ClaimsMode) :
    runWithK4 F shape iv publicInput stream v mode =
      runWithKH4 (keccak256With F) (rateWith F) shape iv publicInput stream v mode := by
  unfold runWithK4 runWithKH4
  simp only [seedWith_eqH, reduceWithK4_eqH4]

theorem verifyWithK4_eqH4 (shape : UniStatement.Shape) (v : KeccakVariant) (iv : List UInt8) (roots : SetupRootsK)
    (publicInput : Vector UInt8 32) (proof : KeccakProof) :
    verifyWithK4 F shape v iv roots publicInput proof =
      verifyWithKH4 (keccak256With F) (rateWith F) F shape v iv roots publicInput proof := by
  unfold verifyWithK4 verifyWithKH4
  simp only [runWithK4_eqH4, pcsOpenK_eqH]
  rfl

/-- **π1-rec4's deployed verifier at `H = keccak256With F`, `W` its rate** is the Statement's. -/
theorem verifierWith4_eqH4 :
    KDeployment.verifierWith4 F = KDeployment.verifierWith4H (keccak256With F) (rateWith F) F := by
  funext D roots input proof
  simp only [KDeployment.verifierWith4, KDeployment.verifierWith4H, ivWith_eqH, verifyWithK4_eqH4]

end Eq

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.verifierWith4_eqH4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.verifierWith4_eqH4
