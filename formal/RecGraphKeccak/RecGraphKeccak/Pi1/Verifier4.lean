-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed, in the Rust's operation order, from
-- `crates/leanvm/univariate/src/verifier.rs` (`reduce` at `KECCAK_REC4`: `bus_challenges`, `point_challenge`,
-- `late_challenges`, `batch` with `λ` drawn) and `crates/leanvm/statement/src/flock_min.rs` (`zerocheck` and
-- `verify_walked` with `eq_first`, `ring_end_at`).
import RecGraphKeccak.Pi1.Verifier

/-!
# The Keccak VM's π1-rec4 verifier as a program

`reduce` at the reference workload's shape with `KECCAK_REC4` and `Claims::Point`, on the recorder: `pi1Rec4K`. It is
`reduceK` (π1-rec3's, `Verifier.lean`) with π1-rec4's draws (`docs/leanvm/univariate/SPEC.md` §14.4):

* after `C1`'s commitment one wide draw (`sampleWide 4`: `α`'s `c`, `β`, `γ`, the zerocheck's first coordinate), `α`
  the squares of `c`;
* Flock's zerocheck with its first coordinate given (`zerocheck4`: `squares c' (log_n − k − 7)`), no ring end after
  the slices (`verifyWalkedK4`);
* after `C2`'s commitment one wide draw (`sampleWide 5`: `t`, the map's `f_0 … f_3`);
* after the heap's relations one wide draw (`sampleWide 4`: `ρ`, `λ`, `f_4`, `f_5`), then the ring switch's target
  (`towerTarget`) and its relation;
* the batch with `λ` given (`batchK4`).

Its recording is `Emitted.lean` (`RecGraphKeccakTest/Pi1Check.lean`: `pi1GraphK4 = Emitted.graph`).
-/

namespace RecGraphKeccak.Pi1

open LeanVM.Parameters UniStatement UniStatement.Flock RecGraph RecGraph.Pi1

/-- **`zerocheck(log_n, k, fs, Some(c))`**: the seven fixed coordinates, then `c` and its squares; the skip's coset
values and `z`; the rounds; `v_a`, `v_b`, `v_c = running + v_a v_b`. -/
def zerocheck4 (logN k : Nat) (c : Sym) : Prog (Option Sym × List Sym × Sym × Sym × Sym) := do
  let mut r : Array (Option Sym) := #[]
  for x in fixedChallenges do
    r := r.push (some (← const x))
  let drawn ← squares c (logN - k - nFixed)
  r := r ++ (drawn.map some).toArray
  let (zSkip, claim) ← if k > 0 then do
      let coset ← nextScalars (2 ^ k)
      let z ← sample
      let zz ← zero
      let values := List.replicate (2 ^ k) zz ++ coset
      pure (some z, ← lagrangeInterpolate (2 ^ (k + 1)) values z)
    else do
      pure (none, ← zero)
  let (chi, running) ← sumcheckDrawn claim 3 r.toList false
  let vA ← nextScalar
  let vB ← nextScalar
  let ab ← mul vA vB
  let vC ← add running ab
  return (zSkip, chi, vA, vB, vC)

/-- **`front_with(log_n, variant, 17, Some(c))`**: `frontK` on `zerocheck4`. -/
def frontK4 (logN k : Nat) (c : Sym) : Prog FrontS := do
  let (zSkip, chi, vA, vB, vC) ← zerocheck4 logN k c
  let rowLow := chi.take (packing - k)
  let rest := chi.drop (packing - k)
  let chiIn := rest.take lincheckRoundsK
  let chiRest := rest.drop lincheckRoundsK
  let alpha ← sample
  let t1 ← mul alpha vB
  let s1 ← add vA t1
  let a2 ← pow alpha 2
  let t2 ← mul a2 vC
  let s2 ← add s1 t2
  let a3 ← pow alpha 3
  let claim ← add s2 a3
  let (roundChallenges, rLc) ← sumcheckDrawn claim 3 (List.replicate lincheckRoundsK none) false
  let chiInPrime := roundChallenges.reverse
  let slices ← nextScalars kBits
  return ⟨zSkip, rowLow, chiIn, chiInPrime, chi, alpha, rLc, slices, chiInPrime ++ chiRest⟩

/-- **`verify_walked::<S, Keccak>(log_n, variant, Some(c))`**: the front, the structured terminal against `r_lc`;
the slices' point and the slices (the ring switch is drawn later). -/
def verifyWalkedK4 (logN k : Nat) (c : Sym) : Prog (List Sym × List Sym) := do
  let fr ← frontK4 logN k c
  let terminal ← structuredTerminalS fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.slices fr.alpha
  requireZero (← add terminal fr.rLc)
  return (fr.point, fr.slices)

/-- **`batch`** at π1-rec4 on the Keccak VM: `batchK` with `λ` given. -/
def batchK4 (lambda : Sym) (combined : List (Commitment × CombinedS)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List Sym)) : Prog (List (Commitment × List Sym × Sym)) := do
  let vars := (layouts.map (·.2.vars)).foldl max 0
  let mut target ← zero
  let mut scale ← one
  for (_, claim) in combined do
    let sv ← mul scale claim.value
    target ← add target sv
    scale ← mul scale lambda
  let (r, _, last) ← sumcheckPairsDrawn target 2 vars true
  let values ← nextScalars combined.length
  let layoutOf (c : Commitment) : StackLayout := ((layouts.find? (·.1 == c)).map (·.2)).getD default
  let mut sum ← zero
  let mut scale2 ← one
  let mut openings : Array (Commitment × List Sym × Sym) := #[]
  for ((commitment, claim), value) in combined.zip values do
    let layout := layoutOf commitment
    let weight ← weightAtK claim layout r ringMap
    let mut extension ← one
    for j in [layout.vars:vars] do
      let o ← one
      let s ← add o (r.getD j 0)
      extension ← mul extension s
    let sw ← mul scale2 weight
    let swe ← mul sw extension
    let swev ← mul swe value
    sum ← add sum swev
    scale2 ← mul scale2 lambda
    openings := openings.push (commitment, r.take layout.vars, value)
  requireZero (← add sum last)
  return openings.toList

/-- **The Keccak VM's π1-rec4 verifier** (`reduce` with `KECCAK_REC4`, `Claims::Point`), on the recorder, from the
public input's words. -/
def reduceK4 (shape : Shape) (publicWords : List Sym) : Prog ReducedSK := do
  let heights := shape.heights
  let heap := shape.heap
  let rW := shape.constraintVars
  let h := heap.h
  -- 0. The row counts.
  let counts ← countBits heights
  -- 1. C1's commitment, then one wide draw: α's c (α its squares), β, γ, the zerocheck's first coordinate.
  let root1 ← nextRoot
  let ood1 ← nextScalar
  let bus ← sampleWide 4
  let alphas ← squares (bus.getD 0 0) 4
  let beta := bus.getD 1 0
  let gamma := bus.getD 2 0
  let weights ← eqKernel alphas
  -- 2. Flock on the Keccak-f block, its structured terminal; the ring switch later.
  let logN := keccakR1csLogSize + heights.getD opSha3 0
  let (flockPoint, slices) ← verifyWalkedK4 logN UniKeccak.keccakRec4.skip (bus.getD 3 0)
  -- 3. C2's commitment, then one wide draw: t and the map's f_0 … f_3; the digits, Z_act.
  let root2 ← nextRoot
  let ood2 ← nextScalar
  let pointDraw ← sampleWide 5
  let t := pointDraw.getD 0 0
  let w ← digits t (max h (rW + 4) + 2)
  let mut active : Array Sym := #[]
  for (bs, r) in counts.zip heights do
    active := active.push (← activeVanishingFromBits w bs r)
  -- 4. The values at t.
  let mut relations : Array RelationS := #[]
  let mut parts : Array TablePartS := #[]
  for table in tablesKeccak do
    let (part, rels) ← tablePart table (heights.getD table.opcode 0) weights beta w
    parts := parts.push part
    relations := relations ++ rels.toArray
  let o ← one
  let lm := shape.logMemory
  let memoryFinalCount ← nextScalar
  let address ← nextScalar
  let memoryPull ← nextScalar
  relations := relations.push (← equalS (.memory 3) (w.take lm) memoryFinalCount)
  relations := relations.push (← equalS .address (w.take lm) address)
  let mp1 ← add memoryPull beta
  let cm ← const sepMem
  let w0m ← mul (weights.getD 0 0) cm
  let mp2 ← add mp1 w0m
  let w1a ← mul (weights.getD 1 0) address
  let mp3 ← add mp2 w1a
  let w2m ← mul (weights.getD 2 0) memoryFinalCount
  let mp4 ← add mp3 w2m
  relations := relations.push ⟨(List.range 3).map (fun k ↦ termS (.memory k) (w.take lm) (weights.getD (3 + k) 0)), mp4⟩
  let om ← add o memoryFinalCount
  let w2om ← mul (weights.getD 2 0) om
  let memoryPush ← add memoryPull w2om
  let lb := shape.logBytecode
  let bytecodeFinalCount ← nextScalar
  let bytecodePull ← nextScalar
  relations := relations.push (← equalS .bytecodeFinal (w.take lb) bytecodeFinalCount)
  let bp1 ← add bytecodePull beta
  let w2b ← mul (weights.getD 2 0) bytecodeFinalCount
  let bp2 ← add bp1 w2b
  relations := relations.push (← equalS .bytecodeTuple (alphas ++ w.take lb) bp2)
  let ob ← add o bytecodeFinalCount
  let w2ob ← mul (weights.getD 2 0) ob
  let bytecodePush ← add bytecodePull w2ob
  let heapValue ← nextScalar
  let constraintValue ← nextScalar
  -- 5. The constraint quotient's identity.
  let constraint ← constraintRelationK shape parts.toList publicWords gamma t constraintValue w
  relations := relations.push constraint
  let constraintChunks := chunks (UniKeccak.Shape.constraintDegreeK shape + 1)
  let c2Base : List (Column × Nat × Bool) :=
    [(.heap, h, true), (.treeQuotient 0, h, true), (.treeQuotient 1, 0, true)] ++
      (constraintChunks.zip (List.range constraintChunks.length)).map fun (e, c) ↦
        (Column.constraintQuotient c, e, true)
  -- 6. C2: the heap.
  let (heapRels, leafColumns) ← heapRelations shape active.toList parts.toList weights beta heapValue
    constraintValue memoryPull memoryPush bytecodePull bytecodePush w constraintChunks
  relations := relations ++ heapRels.toArray
  let c2Columns := c2Base ++ leafColumns
  -- 8 (π1-rec4). One wide draw: ρ, λ, f_4, f_5; the ring switch's end at the whole map.
  let late ← sampleWide 4
  let map := pointDraw.drop 1 ++ [late.getD 2 0, late.getD 3 0]
  let target ← towerTarget slices map
  -- 7. Flock's claim on q_flock: one term for the whole ring-switch weight.
  relations := relations.push ⟨[⟨.qflock, flockPoint, ringTwist, ← one⟩], target⟩
  -- 8. One claim per commitment, the batch.
  let rho := late.getD 0 0
  let mut combined : Array (Commitment × CombinedS) := #[]
  for c in commitments do
    if let some claim ← combine relations.toList c rho then
      combined := combined.push (c, claim)
  let _ ← one
  let stackLayouts := UniKeccak.layoutsK shape c2Columns
  let openings ← batchK4 (late.getD 1 0) combined.toList stackLayouts (some map)
  return ⟨root1, root2, ood1, ood2, openings⟩

/-- **The recorded Keccak π1-rec4 verifier**: the recorder's start (the seed), the public input's four words, then
`reduceK4` at `leanvm_rec::REFERENCE`. -/
def pi1Rec4K : Prog ReducedSK := do
  let mut words : Array Sym := #[]
  for k in [0:4] do
    words := words.push (← statement k)
  reduceK4 shapeK words.toList

/-- **The Keccak VM's π1-rec4 graph, recorded in Lean**. -/
abbrev pi1GraphK4 : Graph := recordedGraphK pi1Rec4K

end RecGraphKeccak.Pi1
