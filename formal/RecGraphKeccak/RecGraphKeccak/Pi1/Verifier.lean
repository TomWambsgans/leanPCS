-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed, in the Rust's operation order, from
-- `crates/leanvm_univariate/src/verifier.rs` (`reduce` with `Blake2s::Keccak`, `weight_at`, `batch`), `stacks.rs`
-- (`EqCache`) and `contract.rs` (`record_verifier`, `calls`).
import RecGraph.Pi1.Verifier
import RecGraphKeccak.Pi1.Flock
import UniKeccak.Opening

/-!
# The Keccak VM's π1-rec3 verifier as a program

`reduce` at the Keccak VM's 400-signature shape (`UniKeccak.keccak400`, the Rust's `KECCAK_400`) with
`Blake2s::Keccak(KECCAK_REC3)` and `Claims::Point`, on the recorder: `pi1Rec3K`. Against `RecGraph.Pi1.reduce`
(π1-rec3 on the BLAKE2s VM), what changes:

* the tables are `tablesKeccak`, and Flock is `verifyWalkedK` (`log_n = 17 + h_SHA3`);
* `Q_W`'s copies (`constraintRelationK`): each `SHA3` lane column against `q_flock`'s word `keccakSlot`, read through
  `y(t)`, `END_BIT` added to `in_16`'s known part (`g · c(END_BIT)`);
* the quotient's chunks from `Shape.constraintDegreeK`, the stacks `layoutsK`;
* a `q_flock` slot term's weight (`weightAtK`): its slot bits are `q_flock`'s variables minus its point's (`11`),
  the instance's eq `EqCache::row_from(point, slot_bits)`.

The rest (`countBits`, `tablePart`, `linearise`, `combine`, `heapRelations`, `quotientTerms`, the sumchecks, `digits`,
`activeVanishingFromBits`) is `RecGraph.Pi1`'s, unchanged.
-/

namespace RecGraphKeccak.Pi1

open LeanVM.Parameters UniStatement UniStatement.Flock RecGraph RecGraph.Pi1

/-- **The constraint quotient's identity** on the Keccak VM (step 5 of `reduce`). -/
def constraintRelationK (shape : Shape) (parts : List TablePartS) (publicWords : List Sym)
    (gamma t constraintValue : Sym) (w : List Sym) : Prog RelationS := do
  let heights := shape.heights
  let rW := shape.constraintVars
  let mut known ← zero
  let mut terms : Array TermS := #[]
  let mut power ← one
  let o ← one
  for (table, part) in tablesKeccak.zip parts do
    let r := heights.getD table.opcode 0
    let lift ← vanishingRatio w r rW
    let at_ (c : Nat) : Column := .table table.opcode c
    if table.opcode = opJump then
      let cond := (part.sent.getD (colIdx table.columns "v_cond") none).getD 0
      let flag := (part.sent.getD (colIdx table.columns "b") none).getD 0
      let cur1 := power
      power ← mul power gamma
      let g1 ← mul cur1 lift
      known ← add known (← mul g1 flag)
      terms := terms.push (termS (at_ (colIdx table.columns "w")) (w.take r) (← mul g1 cond))
      let cur2 := power
      power ← mul power gamma
      let g2 ← mul cur2 lift
      let g2c ← mul g2 cond
      let f1 ← add flag o
      known ← add known (← mul g2c f1)
    let mut counters := o
    for column in table.countColumns do
      counters ← mul counters ((part.sent.getD column none).getD 0)
    let cur := power
    power ← mul power gamma
    let g ← mul cur lift
    terms := terms.push (termS (.inverse table.opcode) (w.take r) (← mul g counters))
    known ← add known g
    if table.opcode = opBlake2s then
      let y ← coordinatesAt t (coordinateFunctionals r)
      for (name, column) in table.columns.zip (List.range table.width) do
        if let some slot := keccakSlot name then
          let cur := power
          power ← mul power gamma
          let g ← mul cur lift
          terms := terms.push (termS (at_ column) (w.take r) g)
          terms := terms.push (termS (.qflockSlot slot) y g)
          if keccakSlotOffset name != 0 then
            let c ← const (eK (keccakSlotOffset name))
            known ← add known (← mul g c)
  let lm := shape.logMemory
  let z1 ← zero
  let z2 ← zero
  let lines : List (Sym × Sym) :=
    [(publicWords.getD 0 0, publicWords.getD 2 0), (publicWords.getD 1 0, publicWords.getD 3 0), (z1, z2)]
  let lift ← vanishingRatio w 1 rW
  for ((low, high), k) in lines.zip (List.range 3) do
    let cur := power
    power ← mul power gamma
    let g ← mul cur lift
    terms := terms.push (termS (.memory k) (w.take lm) g)
    let lh ← add low high
    let tlh ← mul t lh
    let l2 ← add low tlh
    known ← add known (← mul g l2)
  let cw ← mul constraintValue (w.getD rW 0)
  return ⟨terms.toList, ← add cw known⟩

/-- **`weight_at(claim, layout, r, ring_map)`** on the Keccak VM (the Rust's, `EqCache`'s caches left out): a
`q_flock` slot term's slot bits are `q_flock`'s variables minus its point's, its instance's eq `row_from`. -/
def weightAtK (claim : CombinedS) (layout : StackLayout) (r : List Sym) (ringMap : Option (List Sym)) :
    Prog Sym := do
  let mut onePlusR : Array Sym := #[]
  for x in r do
    let o ← one
    onePlusR := onePlusR.push (← add o x)
  let b0 ← const (eNew 1 0 0)
  let b1 ← const (eNew 0 1 0)
  let b2 ← const (eNew 0 0 1)
  let basis := [b0, b1, b2]
  let qflockVars := ((layout.limbs .qflock).headD (0, 0, 0)).2.1
  let mut rows : Array ((Nat × Nat × Nat) × Sym) := #[]
  let mut slots : Array (Nat × Sym) := #[]
  for (column, p, twist, coefficient) in claim.terms do
    match column with
    | .qflockSlot j =>
      let slotBits := qflockVars - (claim.points.getD p []).length
      let mut acc ← one
      for b in [0:slotBits] do
        acc ← mul acc (if j.testBit b then r.getD b 0 else onePlusR.getD b 0)
      let c ← mul coefficient acc
      match slots.findIdx? (·.1 == p) with
      | some i => slots := slots.set! i (p, ← add (slots.getD i (0, 0)).2 c)
      | none => slots := slots.push (p, c)
    | _ =>
      let (vars, sum) ← partS r basis layout column
      let c ← mul coefficient sum
      match rows.findIdx? (·.1 == (p, vars, twist)) with
      | some i => rows := rows.set! i ((p, vars, twist), ← add (rows.getD i ((0, 0, 0), 0)).2 c)
      | none => rows := rows.push ((p, vars, twist), c)
  let mut total ← zero
  for ((p, len, twist), sum) in rows do
    let point := claim.points.getD p []
    let row ← if twist = ringTwist then
        ringWeight (point.take len) (onePlusR.toList.take len) (ringMap.getD [])
      else do
        let mut product ← one
        for k in [0:len] do
          let s ← add (onePlusR.getD k 0) (point.getD k 0)
          product ← mul product s
        pure product
    let rs ← mul row sum
    total ← add total rs
  for (p, sum) in slots do
    let point := claim.points.getD p []
    let (_, qflock) ← partS r basis layout .qflock
    let slotBits := qflockVars - point.length
    let mut inst ← one
    for (x, a) in point.zip (onePlusR.toList.drop slotBits) do
      let s ← add a x
      inst ← mul inst s
    let si ← mul sum inst
    let siq ← mul si qflock
    total ← add total siq
  return total

/-- **`batch`** at π1-rec3's Fiat–Shamir shape on the Keccak VM: `RecGraph.Pi1.batch` with `weightAtK`. -/
def batchK (combined : List (Commitment × CombinedS)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List Sym)) : Prog (List (Commitment × List Sym × Sym)) := do
  let lambda ← sample
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

/-- **The Keccak VM's π1-rec3 verifier** (`reduce` with `Blake2s::Keccak(KECCAK_REC3)`, `Claims::Point`), on the
recorder, from the public input's words. -/
def reduceK (shape : Shape) (publicWords : List Sym) : Prog ReducedS := do
  let heights := shape.heights
  let heap := shape.heap
  let rW := shape.constraintVars
  let h := heap.h
  let fs := FsShape.rec3
  -- 0. The row counts.
  let counts ← countBits heights
  -- 1. C1, α (squares), β, γ.
  let root1 ← nextRoot
  let alphas ← drawRun fs 4
  let beta ← sample
  let gamma ← sample
  let weights ← eqKernel alphas
  -- 2. Flock on the Keccak-f block, its structured terminal.
  let logN := keccakR1csLogSize + heights.getD opBlake2s 0
  let (flockPoint, map, target) ← verifyWalkedK logN UniKeccak.keccakRec3.skip fs
  -- 3. C2, t, the digits, Z_act.
  let root2 ← nextRoot
  let t ← sample
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
  -- 7. Flock's claim on q_flock: one term for the whole ring-switch weight.
  relations := relations.push ⟨[⟨.qflock, flockPoint, ringTwist, ← one⟩], target⟩
  -- 8. ρ, one claim per commitment, the batch.
  let rho ← sample
  let mut combined : Array (Commitment × CombinedS) := #[]
  for c in commitments do
    if let some claim ← combine relations.toList c rho then
      combined := combined.push (c, claim)
  let _ ← one
  let stackLayouts := UniKeccak.layoutsK shape c2Columns
  let openings ← batchK combined.toList stackLayouts (some map)
  return ⟨root1, root2, openings⟩

/-- The Keccak VM's 400-signature shape (`KECCAK_400`). -/
abbrev shapeK : Shape := UniKeccak.keccak400

/-- **The recorded Keccak verifier** (`record_verifier_with`): the recorder's start (the seed), the public input's
four words, then `reduceK` at `KECCAK_400`. -/
def pi1Rec3K : Prog ReducedS := do
  let mut words : Array Sym := #[]
  for k in [0:4] do
    words := words.push (← statement k)
  reduceK shapeK words.toList

/-- **`contract::calls`** on the Keccak VM: each point claim's words (its root, its Keccak layout word, one claim, its
point, its value); a root in the stream is the word at its first half's offset; the setup's root `F` the reference
setup's (`SetupRoots::REFERENCE`, which `record_verifier` binds). -/
def callsOfK (st : RecState) (red : ReducedS) : List (List Word) :=
  let words := UniKeccak.layoutWordsK shapeK
  let streamAt (half : Sym) : Word :=
    match st.nodes[half]? with
    | some (.input off _) => .stream off
    | _ => .stream 0
  red.openings.map fun (c, point, value) ↦
    let (root, layout) : Word × List UInt8 := match c with
      | .c1 => (streamAt red.root1.1, words.getD 0 [])
      | .c2 => (streamAt red.root2.1, words.getD 1 [])
      | .setup => (.const (beNat (LeanVM.Protocol.KeccakHash.digestBytes referenceRoots.bytecode)), words.getD 2 [])
    [root, .const (beNat layout), .const 1] ++ point.map Word.node ++ [.node value]

/-- A program's recorded graph, from the recorder's start, with the Keccak calls' words (`callsOfK`) and its stream's
length; no nonzero check. -/
def recordedGraphK (p : Prog ReducedS) : Graph :=
  { (p.record RecState.start).2.graph (callsOfK (p.record RecState.start).2 (p.record RecState.start).1)
      (p.record RecState.start).2.cursor with nonzero := [] }

/-- **The Keccak VM's π1-rec3 graph, recorded in Lean**. -/
abbrev pi1GraphK : Graph := recordedGraphK pi1Rec3K

end RecGraphKeccak.Pi1
