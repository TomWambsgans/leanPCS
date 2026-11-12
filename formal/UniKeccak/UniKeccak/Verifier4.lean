-- Part of this repository. Transcribed from `crates/leanvm/univariate/src/verifier.rs` (`reduce`, `reduce_combined` at
-- `KECCAK_REC4`: `bus_challenges`, `point_challenge`, `late_challenges`, `batch` with `λ` drawn) and
-- `crates/leanvm/statement/src/flock_min.rs` (`verify_walked` with `eq_first`, `ring_end_at`). MIT OR Apache-2.0; see
-- AGENTS.md.
module

public import UniKeccak.Verifier

/-!
# The Keccak VM's verifier at π1-rec4's Fiat–Shamir shape (`KECCAK_REC4`, `docs/leanvm/univariate/SPEC.md` §14.4)

π1-rec4 is π1-rec3 (`keccakRec3`) with the challenges no message separates drawn from one Keccak-f each (`sampleWide`:
challenge `k` of a draw is the rate's lanes `1 + 3k … 3 + 3k` after the hash's last permutation, challenge `0`
`sample`'s), and the ring switch's map drawn after `C2`'s commitment. The stream is π1-rec3's byte for byte; only the
challenges' derivation changes:

| call | absorbs | draws |
|---|---|---|
| after `C1`'s commitment | the row counts, `C1`'s root and answer | `α`'s `c`, `β`, `γ`, the zerocheck's `c'` (wide, 4) |
| Flock's skip, zerocheck and lincheck rounds | as π1-rec3 | one each |
| after `C2`'s commitment | the slices, `C2`'s root and answer | `t`, the map's `f_0 … f_3` (wide, 5) |
| after the values at `t` | the values | `ρ`, the batch's `λ`, `f_4`, `f_5` (wide, 4) |
| the batch | 13 pairs, then one plain round | one each (narrow) |

`reduceWithK4` is `reduce` at `KECCAK_REC4`, a function of its own: `reduceWithK` (the main line, π1-rec3) is left
as it is, so `reduceWithK … keccakRec4` is **not** π1-rec4's verifier (`runWithK4`, `runK4` are). Its steps are
`reduceWithK`'s, in the Rust's order:

* `zerocheckFirst` (`flock_min::zerocheck` with `eq_first`): the zerocheck's coordinates after the seven fixed ones are
  `c', c'², …` of the caller's `c'`; `verifyWalkedK4` (`verify_walked`) leaves the slices' point and the slices;
* `ringEndAt` (`ring_end_at`): the ring switch's map and its target in tower order, once all six are drawn;
* `batchK4` (`batch` with `drawn_lambda`): `batchK` at `.rec4` (paired, narrow), `λ` given.
-/

@[expose] public section

namespace UniKeccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement

/-- **`KECCAK_REC4`**: `KECCAK_REC3` with π1-rec4's Fiat–Shamir shape (`FsShape::Rec4`): the recursion's inner proof. -/
def keccakRec4 : KeccakVariant := ⟨3, .rec4⟩

/-- **`ring_end_at(s, map)`**: the ring switch's end on the slices at the map (drawn after the slices), its target in
tower order (`Slices::TowerWalk`). -/
def ringEndAt (s map : List E) : Flock.End := .ring map (Flock.towerTarget s map)

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`front_with(log_n, variant, 17, Some(c))`**: `frontK`, the zerocheck's coordinates after the seven fixed ones
`c, c², c⁴, …` (`Flock.zerocheckFirst`). -/
def frontK4 (logN : ℕ) (v : KeccakVariant) (c : E) : ChanM m Flock.Front := do
  let k := v.skip
  let (zSkip, chi, vA, vB, vC) ← Flock.zerocheckFirst F logN k c
  let rowLow := chi.take (Flock.packing - k)
  let rest := chi.drop (Flock.packing - k)
  let chiIn := rest.take lincheckRoundsK
  let chiRest := rest.drop lincheckRoundsK
  let alpha ← sample F
  let claim := vA + alpha * vB + epow alpha 2 * vC + epow alpha 3
  let (roundChallenges, rLc) ← sumcheck F claim 3 (List.replicate lincheckRoundsK none)
  let chiInPrime := roundChallenges.reverse
  let s ← nextScalars (m := m) Flock.kBits
  return ⟨zSkip, chi, rowLow, chiIn, chiInPrime, alpha, rLc, some s, chiInPrime ++ chiRest⟩

/-- **`verify_walked::<S, Keccak>(log_n, variant, Some(c))`**: the front, the lincheck's terminal against the
structured terminal (collected); the slices' point and the slices, whose ring switch the caller draws later. -/
def verifyWalkedK4 (logN : ℕ) (v : KeccakVariant) (c : E) : ChanM m (List E × List E) := do
  let fr ← frontK4 F logN v c
  let s := fr.slices.getD []
  requireZero (m := m) (structuredTerminal fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime s fr.alpha + fr.rLc)
  return (fr.point, s)

/-- **`batch(fs, …, Some(λ))`** on the Keccak VM at π1-rec4: `batchK` at `.rec4` (pairs of variables, narrow
challenges) with `λ` drawn before (with `ρ`). -/
def batchK4 (lambda : E) (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) : ChanM m (List (Commitment × Opening)) := do
  let vars := (layouts.map (·.2.vars)).foldl max 0
  let (target, _) := combined.foldl (fun (acc : E × E) (_, claim) ↦
    (acc.1 + acc.2 * claim.value, acc.2 * lambda)) (0, 1)
  let (r, _, last) ← sumcheckPairsDrawn F target 2 vars true
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

/-- **The Keccak VM's verifier at π1-rec4** over the permutation `F` (`reduce` at `KECCAK_REC4`): `reduceWithK`'s
steps with the wide draws (`bus_challenges`, `point_challenge`, `late_challenges`) and the ring switch's map drawn
in two parts. `v` gives the skip (`keccakRec4`'s is `3`); its Fiat–Shamir shape is not read. -/
def reduceWithK4 (shape : Shape) (publicWords : List E) (v : KeccakVariant) (mode : ClaimsMode) :
    ChanM m Reduced := do
  if !shape.validate true then throw .invalidShape
  let heights := shape.heights
  let heap := shape.heap
  let rW := shape.constraintVars
  let h := heap.h
  -- 0. The tables' row counts: six 32-bit integers, absorbed with C1's commitment.
  let counts ← countBits (m := m) heights
  -- 1. C1's commitment, then one wide draw (`bus_challenges`): α's c, β, γ, the zerocheck's first coordinate.
  let root1 ← nextRoot (m := m)
  let ood1 ← nextScalar (m := m)
  let bus ← sampleWide F 4
  let alphas := squares (bus.getD 0 0) 4
  let beta := bus.getD 1 0
  let gamma := bus.getD 2 0
  let weights := eqKernel alphas
  -- 2. Flock on the Keccak-f block, its zerocheck's coordinates from the draw; the ring switch is drawn later.
  let logN := keccakR1csLogSize + heights.getD opSha3 0
  let (flockPoint, slices) ← verifyWalkedK4 F logN v (bus.getD 3 0)
  -- 3. C2's commitment, then one wide draw (`point_challenge`): t and the map's f_0 … f_3.
  let root2 ← nextRoot (m := m)
  let ood2 ← nextScalar (m := m)
  let pointDraw ← sampleWide F 5
  let t := pointDraw.getD 0 0
  let w := digits t (max h (rW + 4) + 2)
  let active := (counts.zip heights).map fun (bits, r) ↦ activeVanishingFromBits w bits r
  -- 4. The values at t, with the relations they take part in.
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
  -- 5. The constraint quotient's identity.
  let (constraint, quotientDegree) :=
    constraintRelationK shape parts.toList publicWords gamma t constraintValue w
  relations := relations.push constraint
  let constraintChunks := chunks (quotientDegree + 1)
  let c2Columns : List (Column × ℕ × Bool) :=
    [(.heap, h, true), (.treeQuotient 0, h, true), (.treeQuotient 1, 0, true)] ++
      (constraintChunks.zip (List.range constraintChunks.length)).map fun (e, c) ↦
        (Column.constraintQuotient c, e, true)
  -- 6. C2: the heap's tree, root and leaves, and Q_W's value.
  let (heapRels, leafColumns) := heapRelations shape active parts.toList weights beta heapValue
    constraintValue memoryPull memoryPush bytecodePull bytecodePush w constraintChunks
  relations := relations ++ heapRels.toArray
  let c2Columns := c2Columns ++ leafColumns
  -- 8 (π1-rec4). One wide draw after the values at t (`late_challenges`): ρ, the batch's λ, the map's f_4, f_5; the
  -- ring switch's end at the whole map.
  let late ← sampleWide F 4
  let rho := late.getD 0 0
  let lambda := late.getD 1 0
  let map := pointDraw.drop 1 ++ [late.getD 2 0, late.getD 3 0]
  let target := Flock.towerTarget slices map
  -- 7. Flock's claim on q_flock: the ring switch's weight, one term (the point-claim ABI) or 64 (tower order).
  let mut ringMap : Option (List E) := none
  if mode == .point then
    relations := relations.push ⟨[⟨.qflock, flockPoint, ringTwist, 1⟩], target⟩
    ringMap := some map
  else
    let coefficients := Flock.towerCoefficients map
    relations := relations.push ⟨(coefficients.zip (List.range coefficients.length)).map
      (fun (c, k) ↦ ⟨.qflock, flockPoint, k, c⟩), target⟩
  -- 8. One claim per commitment.
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine relations.toList c rho).map (c, ·)
  let stackLayouts := layoutsK shape c2Columns
  let stackVars := stackLayouts.map fun (c, l) ↦ (c, l.vars)
  let openings ← match mode with
    | .weighted => pure (combined.map fun (c, claim) ↦ (c, Opening.weighted claim))
    | .point => batchK4 F lambda combined stackLayouts ringMap
  return ⟨(root1, root2), openings, none, relations.size, stackVars, stackLayouts, (ood1, ood2)⟩

/-- **The Keccak verifier at π1-rec4 on calldata** over `F` (`rust_verifier` at `KECCAK_REC4`): the seed of the IV
and the public input, the walk, nothing of the stream left. -/
def runWithK4 (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (v : KeccakVariant)
    (mode : ClaimsMode) : m Outcome := do
  let seed ← seedWith F iv publicInput
  let walkM : ChanM m Reduced := do
    let r ← reduceWithK4 F shape (publicWordsOf publicInput) v mode
    finish (m := m)
    return r
  let (result, chan) ← (walkM.run).run (Chan.start seed stream)
  return ⟨result, chan⟩

/-- **The Keccak verifier at any variant** (the Rust's `reduce` takes the variant): `runWithK4` at a wide shape,
`runWithK` otherwise. -/
def runWithKV (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (v : KeccakVariant)
    (mode : ClaimsMode) : m Outcome :=
  if v.fs.wide then runWithK4 F shape iv publicInput stream v mode
  else runWithK F shape iv publicInput stream v mode

end With

/-- The Keccak verifier's run at π1-rec4 over Keccak-f[1600]. -/
def runK4 (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (v : KeccakVariant)
    (mode : ClaimsMode) : Outcome :=
  Id.run (runWithK4 (m := Id) (fun s ↦ pure (keccakF1600 s)) shape iv publicInput stream v mode)

/-- The Keccak verifier's run at any variant over Keccak-f[1600]. -/
def runKV (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (v : KeccakVariant)
    (mode : ClaimsMode) : Outcome :=
  Id.run (runWithKV (m := Id) (fun s ↦ pure (keccakF1600 s)) shape iv publicInput stream v mode)

end UniKeccak

end
