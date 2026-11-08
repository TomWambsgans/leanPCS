-- Part of this repository. Transcribed from `crates/leanvm/univariate/src/verifier.rs` (`reduce` with
-- `Blake2s::Keccak`, `qflock_slot`, `qflock_row_bits`, `vm_tables`, `stack_layouts_for`, `weight_at`, `batch`,
-- `KECCAK_MAIN`, `KECCAK_REC3`) and `crates/leanvm/statement/src/flock_min.rs` (`verify_walked_with::<Keccak>`,
-- `front_with`). The tables, flushes, fingerprints and public lines are leanVM 42422001's, the `SHA3` table leanVM
-- 9d50c92a3's (https://github.com/leanEthereum/leanVM), read through `crates/leanvm/statement`. MIT OR Apache-2.0;
-- see AGENTS.md.
module

public import UniStatement.Rec
public import UniKeccak.Terminal

/-!
# The Keccak VM's verifier (`reduce` with `Blake2s::Keccak`, `docs/leanvm/univariate/KECCAK.md`)

`reduceWithK F shape publicWords variant mode`, line by line `reduce` on the Keccak VM, reusing `UniStatement`'s
`reduceWithFs` steps where they do not change. What changes:

* **The tables** are `tablesKeccak` (the `SHA3` table in `BLAKE2S`'s place, `UniStatement/KeccakTables.lean`).
* **Flock** runs on the Keccak-f block (`verifyWalkedK`: `flock_min::verify_walked_with::<S, Keccak>`): `log_n =
  17 + h_SHA3`, the zerocheck (`Flock.zerocheckFs`, its coordinates drawn as the variant's Fiat–Shamir shape has
  them), the lincheck's **11** rounds (`17 − 6`), the 64 slices, the terminal `r_lc` against
  `structuredTerminal` (collected: `FlockMatrixTerminal`), then the ring switch's map and target in tower order.
  No matrices' reduction, no claims on `A0`, `B0`.
* **`Q_W`'s copies** (`constraintRelationK`): every `SHA3` lane column against `q_flock`'s word `keccakSlot` (input
  lane `l` at the block's input port word `4l + 2`, output lane `l` at its output port word `4l`), read through
  `y(t)`; for `in_16` the constant `END_BIT` joins the known part (`keccakSlotOffset`).
* **`C1`'s layout** (`layoutsK`): `q_flock` of `h_SHA3 + 11` variables (`2^11` words a block), the Keccak VM's
  tables' columns; the quotients' sizes from the Keccak tables (`Shape.c2ColumnsK`, `layoutsOfK`).
* **A `q_flock` slot term's weight** (`weightAtK`): `q_flock`'s variables minus the point's are the slot bits, `11`
  here (the Rust's `weight_at` reads them so; `UniStatement.weightAt` fixes them at BLAKE2s's `8`).
* **The batch** (`batchK`): `batchFs` with `weightAtK`, and no pending matrices nor bit-slice claim (the Keccak
  verifier has neither).

The variant (`KeccakVariant`) is the skip and the Fiat–Shamir shape; the slices are always `Slices::TowerWalk`
(the Rust asserts it). `keccakMain` is `KECCAK_MAIN` (skip 3, `FsShape::Main`), `keccakRec3` is `KECCAK_REC3`
(skip 3, `FsShape::Rec3`: `α = (c, c², c⁴, c⁸)`, Flock's zerocheck coordinates after the seven fixed ones as
squares of one challenge, the batch two variables a round with narrow challenges).
-/

@[expose] public section

namespace UniKeccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement

/-- **The Keccak verifier's variant** (`Variant` with `slices: TowerWalk`): the univariate skip and the Fiat–Shamir
shape. -/
structure KeccakVariant where
  skip : ℕ
  fs : FsShape
  deriving DecidableEq, Repr, Inhabited

/-- **`KECCAK_MAIN`**: skip 3, the slices sent and the structured terminal, `FsShape::Main`. -/
def keccakMain : KeccakVariant := ⟨3, .main⟩

/-- **`KECCAK_REC3`**: `KECCAK_MAIN` with π1-rec3's Fiat–Shamir shape (`FsShape::Rec3`). -/
def keccakRec3 : KeccakVariant := ⟨3, .rec3⟩

/-- The `Flock.Variant` the ring switch reads: the variant's skip, the tower order (`Slices::TowerWalk` is
`Slices::Tower` for `ring_end`). -/
def KeccakVariant.flock (v : KeccakVariant) : Flock.Variant := ⟨v.skip, .tower⟩

/-- `qflock_row_bits(true) = 17 − 6`: `q_flock`'s words a `SHA3` row, `2^11`. -/
def qflockRowBits : ℕ := keccakR1csLogSize - Flock.packing

/-- The Keccak-f block's lincheck rounds, `LOG_SIZE − 6 = 11` (`WalkedCircuit::lincheck_rounds`). -/
def lincheckRoundsK : ℕ := keccakR1csLogSize - Flock.packing

/-! ### Flock on the Keccak-f block (`verify_walked_with::<S, Keccak>`) -/

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`front_with(log_n, variant, 17)`**: the zerocheck (its coordinates after the seven fixed ones drawn as the
variant's shape has them), the row point's split (the skip, the packing bits left to rounds, the block's 11 word
bits, the instance bits), the lincheck (`α`, 11 rounds), the 64 slices (always sent). -/
def frontK (logN : ℕ) (v : KeccakVariant) : ChanM m Flock.Front := do
  let k := v.skip
  let (zSkip, chi, vA, vB, vC) ← Flock.zerocheckFs F logN k v.fs
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

/-- **`verify_walked_with::<S, Keccak>(log_n, variant)`**: the front, the lincheck's terminal `r_lc` against the
structured terminal (`structuredTerminal`, collected: `FlockMatrixTerminal`), then the ring switch's map and target
(tower order). The slices' point and the ring switch's end. -/
def verifyWalkedK (logN : ℕ) (v : KeccakVariant) : ChanM m (List E × Flock.End) := do
  let fr ← frontK F logN v
  let s := fr.slices.getD []
  requireZero (m := m) (structuredTerminal fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime s fr.alpha + fr.rLc)
  let end_ ← Flock.ringEnd F v.flock s
  return (fr.point, end_)

end With

/-! ### The constraint quotient's identity and the stacks -/

/-- **The constraint quotient's identity** on the Keccak VM (step 5 of `reduce`): `constraintRelation` on
`tablesKeccak`, the hash table's copies the `SHA3` lanes against `q_flock`'s words `keccakSlot`, `END_BIT` in
`in_16`'s known part (`keccak_slot_offset`). -/
def constraintRelationK (shape : Shape) (parts : List TablePart) (publicWords : List E)
    (gamma t constraintValue : E) (w : List E) : Relation × ℕ := Id.run do
  let heights := shape.heights
  let rW := shape.constraintVars
  let mut known : E := 0
  let mut terms : Array Term := #[]
  let mut power : E := 1
  let mut qDegree : ℕ := 0
  for (table, part) in tablesKeccak.zip parts do
    let r := heights.getD table.opcode 0
    let n := 2 ^ r
    let lift := vanishingRatio w r rW
    -- JUMP: b + v_cond w, v_cond (b + 1).
    if table.opcode = opJump then
      let cond := (part.sent.getD (colIdx table.columns "v_cond") none).getD 0
      let flag := (part.sent.getD (colIdx table.columns "b") none).getD 0
      let g1 := power * lift
      power := power * gamma
      known := known + g1 * flag
      terms := terms.push (term (.table table.opcode (colIdx table.columns "w")) (w.take r) (g1 * cond))
      let g2 := power * lift
      power := power * gamma
      known := known + g2 * cond * (flag + 1)
      qDegree := max qDegree (degree n 2)
    -- Counters nonzero on every row: z Π c + 1.
    let counters := table.countColumns.foldl (fun acc c ↦ acc * (part.sent.getD c none).getD 0) 1
    let g := power * lift
    power := power * gamma
    terms := terms.push (term (.inverse table.opcode) (w.take r) (g * counters))
    known := known + g
    let counts := table.countColumns.length
    qDegree := max qDegree (degree ((n - 1) * (1 + counts)) n)
    -- The SHA3 lanes' copies equal q_flock's words: copy − port, the port read through y(t); in_16 − port = END_BIT.
    if table.opcode = opBlake2s then
      let y := coordinatesAt t (coordinateFunctionals r)
      for c in List.range table.width do
        let name := table.columns.getD c ""
        if let some slot := keccakSlot name then
          let g := power * lift
          power := power * gamma
          terms := terms.push (term (.table table.opcode c) (w.take r) g)
          terms := terms.push (term (.qflockSlot slot) y g)
          if keccakSlotOffset name != 0 then
            known := known + g * eK (keccakSlotOffset name)
      qDegree := max qDegree (degree (r * (n / 2)) n)
  -- The public input: the memory's limbs at cells 0 and 1 are the public lines.
  let lm := shape.logMemory
  let lines : List (E × E) :=
    [(publicWords.getD 0 0, publicWords.getD 2 0), (publicWords.getD 1 0, publicWords.getD 3 0), (0, 0)]
  let lift := vanishingRatio w 1 rW
  for ((low, high), k) in lines.zip (List.range 3) do
    let g := power * lift
    power := power * gamma
    terms := terms.push (term (.memory k) (w.take lm) g)
    known := known + g * (low + t * (low + high))
  qDegree := max qDegree (degree (2 ^ lm) 3)
  return (⟨terms.toList, constraintValue * w.getD rW 0 + known⟩, qDegree)

/-- **The Keccak VM's three stacks' layouts** (`stack_layouts_for(shape, c2, true)`): `C1` holds `q_flock` (values,
`h_SHA3 + 11` variables), every Keccak table's columns (the 50 lanes included) and its `z_T`, the memory's four
columns, the bytecode's final counts; `C2` its columns; the setup the bytecode's tuples and the addresses. -/
def layoutsK (shape : Shape) (c2Columns : List (Column × ℕ × Bool)) : List (Commitment × StackLayout) :=
  let heights := shape.heights
  let c1 : List (Column × ℕ × Bool) :=
    [(.qflock, heights.getD opBlake2s 0 + qflockRowBits, false)] ++
      tablesKeccak.flatMap (fun t ↦
        let h := heights.getD t.opcode 0
        (List.range t.width).map (fun c ↦ (Column.table t.opcode c, h, false)) ++
          [(.inverse t.opcode, h, false)]) ++
      (List.range 4).map (fun k ↦ (Column.memory k, shape.logMemory, false)) ++
      [(.bytecodeFinal, shape.logBytecode, false)]
  let setup : List (Column × ℕ × Bool) :=
    [(.bytecodeTuple, shape.logBytecode + 4, false), (.address, shape.logMemory, false)]
  [(.c1, StackLayout.new c1), (.c2, StackLayout.new c2Columns), (.setup, StackLayout.new setup)]

/-- The constraint quotient's degree on the Keccak VM (`Shape.constraintDegree` on `tablesKeccak`). -/
def Shape.constraintDegreeK (shape : Shape) : ℕ :=
  let tableDegree := tablesKeccak.foldl (fun d table ↦
    let r := shape.heights.getD table.opcode 0
    let n := 2 ^ r
    let d := if table.opcode = opJump then max d (degree n 2) else d
    let d := max d (degree ((n - 1) * (1 + table.countColumns.length)) n)
    if table.opcode = opBlake2s then max d (degree (r * (n / 2)) n) else d) 0
  max tableDegree (degree (2 ^ shape.logMemory) 3)

/-- A heap block's leaf quotient's degree on the Keccak VM (`Shape.leafDegree` on `tablesKeccak`). -/
def Shape.leafDegreeK (block : Block) : Option ℕ :=
  let n := 2 ^ block.r
  match block.leaves with
  | .unused => none
  | .memory | .bytecode => some (degree (2 * (n - 1)) n)
  | .table t =>
    let (pd, ppd) := tableDegrees (tablesKeccak.getD t default)
    some (degree (max pd ppd * (n - 1) + (n - Shape.leastRows block.r)) n)

/-- **`C2`'s columns at a shape** on the Keccak VM, as `reduceWithK` lists them. -/
def Shape.c2ColumnsK (shape : Shape) : List (Column × ℕ × Bool) :=
  let h := shape.heap.h
  let constraintChunks := chunks (Shape.constraintDegreeK shape + 1)
  [(.heap, h, true), (.treeQuotient 0, h, true), (.treeQuotient 1, 0, true)] ++
    (constraintChunks.zip (List.range constraintChunks.length)).map (fun (e, c) ↦
      (Column.constraintQuotient c, e, true)) ++
    (shape.heap.blocks.zip (List.range shape.heap.blocks.length)).flatMap fun (block, index) ↦
      match Shape.leafDegreeK block with
      | none => []
      | some d =>
        let sizes := chunks (d + 1)
        (sizes.zip (List.range sizes.length)).map fun (e, chunk) ↦ (Column.leafQuotient index chunk, e, true)

/-- **`layouts_for(shape, Blake2s::Keccak(..))`**: the Keccak VM's three stacks' layouts of a shape. -/
def layoutsOfK (shape : Shape) : List (Commitment × StackLayout) := layoutsK shape (Shape.c2ColumnsK shape)

/-- **A combined claim's weight at the stack point `r`** on the Keccak VM (`weight_at`): `weightAt`, but a
`q_flock` slot term's slot bits are `q_flock`'s variables minus its point's (the Rust's `slot_bits`), `11` here. -/
def weightAtK (claim : Combined) (layout : StackLayout) (r : List E) (ringMap : Option (List E) := none) : E :=
  let points := claim.points.toArray
  let onePlusR := r.map (1 + ·)
  let qflockVars := ((layout.limbs .qflock).head?.map (·.2.1)).getD 0
  let maxTwist : Array ℕ := claim.terms.foldl (fun acc (_, p, twist, _) ↦
    if twist = ringTwist then acc else acc.modify p (max twist)) (Array.replicate points.size 0)
  let twisted : Array (Array (List E)) :=
    Array.ofFn (n := points.size) fun p ↦ twistedPoints (points.getD p.val []) (maxTwist.getD p.val 0)
  claim.terms.foldl (fun total (column, p, twist, coefficient) ↦
    if twist = ringTwist then
      (layout.limbs column).foldl (fun total (limb, vars, offset) ↦
        let row := match ringMap with
          | some map => Flock.towerWeightAt ((points.getD p []).take vars) (onePlusR.take vars) map
          | none => 0
        let scale := if limb = 0 then coefficient else coefficient * limbBasis.getD limb 0
        total + scale * (row * selector r vars offset)) total
    else
    let point := (twisted.getD p #[]).getD twist []
    -- `q_flock`'s word `slot + 2^b · instance`: the slot's `b` bits, then the instance's coordinates.
    let (column, row, rowLen) : Column × List E × ℕ := match column with
      | .qflockSlot j =>
        let slotBits := qflockVars - (points.getD p []).length
        let row := (List.range slotBits).map (bitE j) ++ point
        (.qflock, row, row.length)
      | _ => (column, point, 0)
    (layout.limbs column).foldl (fun total (limb, vars, offset) ↦
      let len := if rowLen > 0 then rowLen else vars
      let eq := rowEq row len r * selector r vars offset
      let scale := if limb = 0 then coefficient else coefficient * limbBasis.getD limb 0
      total + scale * eq) total) 0

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`batch(fs, combined, layouts, None, ring_map, None)`** on the Keccak VM: `λ`, the sumcheck over the longest
stack (plain, plain and narrow, or paired and narrow as `fs` has it), the stacks' values at its point, the terminal
collected (`StackBatchTerminal`) with each claim's weight `weightAtK`; one point claim per commitment. -/
def batchK (fs : FsShape) (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) : ChanM m (List (Commitment × Opening)) := do
  let lambda ← sample F
  let vars := (layouts.map (·.2.vars)).foldl max 0
  let (target, _) := combined.foldl (fun (acc : E × E) (_, claim) ↦
    (acc.1 + acc.2 * claim.value, acc.2 * lambda)) (0, 1)
  let (r, last) ← match fs with
    | .rec3 => do
      let (r, _, last) ← sumcheckPairsDrawn F target 2 vars true
      pure (r, last)
    | .main | .rec1 | .rec2 => sumcheckDrawn F target 3 (List.replicate vars none) fs.narrow
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

/-- **The Keccak VM's verifier** over the permutation `F` (`reduce` with `Blake2s::Keccak(variant)`, SPEC.md §4–§8,
§13, `KECCAK.md`): `publicWords` are the public input's four 64-bit words, low first; the row counts are read from
the stream. -/
def reduceWithK (shape : Shape) (publicWords : List E) (v : KeccakVariant) (mode : ClaimsMode) :
    ChanM m Reduced := do
  if !shape.validate true then throw .invalidShape
  let fs := v.fs
  let heights := shape.heights
  let heap := shape.heap
  let rW := shape.constraintVars
  let h := heap.h
  -- 0. The tables' row counts (F1): six 32-bit integers, absorbed with C1's root.
  let counts ← countBits (m := m) heights
  -- 1. C1, then the bus's and the constraints' challenges; α drawn as the shape has it.
  let root1 ← nextRoot (m := m)
  let alphas ← drawRun F fs 4
  let beta ← sample F
  let gamma ← sample F
  let weights := eqKernel alphas
  -- 2. Flock on the Keccak-f block, on C1's q_flock: the structured terminal, no matrices.
  let logN := keccakR1csLogSize + heights.getD opBlake2s 0
  let (flockPoint, flockEnd) ← verifyWalkedK F logN v
  -- 3. C2, then the point; the active rows' vanishing polynomials from the counts' bits (F1b).
  let root2 ← nextRoot (m := m)
  let t ← sample F
  let w := digits t (max h (rW + 4) + 2)
  let active := (counts.zip heights).map fun (bits, r) ↦ activeVanishingFromBits w bits r
  -- 4. The values at t, with the relations they take part in.
  let mut relations : Array Relation := #[]
  let mut parts : Array TablePart := #[]
  for table in tablesKeccak do
    let (part, rels) ← tablePart (m := m) table (heights.getD table.opcode 0) weights beta w
    parts := parts.push part
    relations := relations ++ rels.toArray
  -- The memory: pull (SEP_MEM, g^i, final count, limbs) of every cell, push the same with count 1.
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
  -- The bytecode: pull (SEP_BYTECODE, g^i, final count, instruction), push the same with count 1.
  let lb := shape.logBytecode
  let bytecodeFinalCount ← nextScalar (m := m)
  let bytecodePull ← nextScalar (m := m)
  relations := relations.push (Relation.equal .bytecodeFinal (w.take lb) bytecodeFinalCount)
  relations := relations.push (Relation.equal .bytecodeTuple (alphas ++ w.take lb)
    (bytecodePull + beta + weights.getD 2 0 * bytecodeFinalCount))
  let bytecodePush := bytecodePull + weights.getD 2 0 * (1 + bytecodeFinalCount)
  let heapValue ← nextScalar (m := m)
  let constraintValue ← nextScalar (m := m)
  -- 5. The constraint quotient's identity, on C1 but for Q_W(t), which is sent.
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
  -- 7. Flock's claim on q_flock: the ring switch's weight, one term (the point-claim ABI) or 64 (tower order).
  let mut ringMap : Option (List E) := none
  match flockEnd with
  | .ring map target =>
    if mode == .point then
      relations := relations.push ⟨[⟨.qflock, flockPoint, ringTwist, 1⟩], target⟩
      ringMap := some map
    else
      let coefficients := Flock.towerCoefficients map
      relations := relations.push ⟨(coefficients.zip (List.range coefficients.length)).map
        (fun (c, k) ↦ ⟨.qflock, flockPoint, k, c⟩), target⟩
  | .combination _ _ => pure ()
  -- 8. One claim per commitment.
  let rho ← sample F
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine relations.toList c rho).map (c, ·)
  let stackLayouts := layoutsK shape c2Columns
  let stackVars := stackLayouts.map fun (c, l) ↦ (c, l.vars)
  let openings ← match mode with
    | .weighted => pure (combined.map fun (c, claim) ↦ (c, Opening.weighted claim))
    | .point => batchK F fs combined stackLayouts ringMap
  return ⟨(root1, root2), openings, none, relations.size, stackVars, stackLayouts⟩

/-- **The Keccak verifier on calldata** over `F` (`rust_verifier` with `Blake2s::Keccak`): the seed of the IV (the
contract's, `contractIvKWith`) and the public input, the walk, nothing of the stream left. -/
def runWithK (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (v : KeccakVariant)
    (mode : ClaimsMode) : m Outcome := do
  let seed ← seedWith F iv publicInput
  let walkM : ChanM m Reduced := do
    let r ← reduceWithK F shape (publicWordsOf publicInput) v mode
    finish (m := m)
    return r
  let (result, chan) ← (walkM.run).run (Chan.start seed stream)
  return ⟨result, chan⟩

end With

/-- The Keccak verifier's run over Keccak-f[1600]: the deployed contract's computation. -/
def runK (shape : Shape) (iv publicInput : List UInt8) (stream : Array UInt8) (v : KeccakVariant)
    (mode : ClaimsMode) : Outcome :=
  Id.run (runWithK (m := Id) (fun s ↦ pure (keccakF1600 s)) shape iv publicInput stream v mode)

end UniKeccak

end
