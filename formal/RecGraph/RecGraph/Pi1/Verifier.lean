-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed, in the Rust's operation order, from
-- `crates/leanvm_univariate/src/verifier.rs` (`linearise`, `table_part`, `quotient_terms`, `heap_relations`),
-- `claims.rs` (`Relations::{push, equal, combine}`) and `stacks.rs` (`limb_basis`), at `leanvm-rec` 4247e37.
import RecGraph.Pi1.Flock

/-!
# π1's verifier as a program: the shared pieces

The pieces of `reduce` on the recorder that the Keccak VM's π1-rec3 (`RecGraphKeccak.Pi1.Verifier`, `reduceK`) uses.
Its terms and relations carry node indices (`TermS`, `RelationS`, `CombinedS`), and `combine` compares points as the
recorder does, by their nodes: `linearise`, `tablePart`, `quotientTerms`, `combine`, the heap's relations
(`heapRelations`), `countBits`, and the reduced outputs (`ReducedS`).
-/

namespace RecGraph.Pi1

open LeanVM.Parameters UniStatement UniStatement.Flock

/-- A term (`claims::Term` on the recorder). -/
structure TermS where
  column : Column
  point : List Sym
  twist : Nat
  coefficient : Sym

/-- A relation `Σ terms = value`. -/
structure RelationS where
  terms : List TermS
  value : Sym

def RelationS.commitment (r : RelationS) : Commitment :=
  match r.terms with
  | t :: _ => t.column.commitment
  | [] => .c1

/-- A combined claim: points, terms (column, point, twist, coefficient), value, relations. -/
structure CombinedS where
  points : List (List Sym)
  terms : List (Column × Nat × Nat × Sym)
  value : Sym
  relations : Nat

/-- `term(column, point, coefficient)`. -/
def termS (column : Column) (point : List Sym) (coefficient : Sym) : TermS := ⟨column, point, 0, coefficient⟩

/-- **`Relations::equal(column, point, value)`**: one term, coefficient `S::one()`. -/
def equalS (column : Column) (point : List Sym) (value : Sym) : Prog RelationS := do
  let o ← one
  return ⟨[termS column point o], value⟩

/-- `linearise`'s `add`: add to the column's coefficient, or append it. -/
def addTermS (terms : Array (Nat × Sym)) (column : Nat) (c : Sym) : Prog (Array (Nat × Sym)) := do
  match terms.findIdx? (·.1 == column) with
  | some i => return terms.set! i (column, ← add (terms.getD i (0, 0)).2 c)
  | none => return terms.push (column, c)

/-- **`linearise(tuple, weights, sent)`**. -/
def linearise (tuple : List Form) (weights : Array Sym) (sent : Array (Option Sym)) :
    Prog (Sym × List (Nat × Sym)) := do
  let mut known ← zero
  let mut terms : Array (Nat × Sym) := #[]
  for (form, s) in tuple.zip (List.range tuple.length) do
    if s < weights.size then
      let weight := weights.getD s 0
      for (monomial, coefficient) in form do
        if coefficient = 0 then continue
        let cc ← const coefficient
        let c ← mul weight cc
        match monomial with
        | [] => known ← add known c
        | [i] =>
          match sent.getD i none with
          | some v =>
            let cv ← mul c v
            known ← add known cv
          | none => terms ← addTermS terms i c
        | [i, j] =>
          match sent.getD i none, sent.getD j none with
          | some a, some b =>
            let ca ← mul c a
            let cab ← mul ca b
            known ← add known cab
          | some a, none =>
            let ca ← mul c a
            terms ← addTermS terms j ca
          | none, some b =>
            let cb ← mul c b
            terms ← addTermS terms i cb
          | none, none => pure ()
        | _ => pure ()
  return (known, terms.toList)

/-- One table's part (`TablePart`). -/
structure TablePartS where
  pull : Sym
  push : Sym
  pullDegree : Nat
  pushDegree : Nat
  sent : Array (Option Sym)

/-- **`table_part(table, log_height, weights, β, point)`**: the sent values and their relations, then the flushes'
fingerprints; the relations it states, in order. -/
def tablePart (t : Table) (logHeight : Nat) (weights : Array Sym) (beta : Sym) (point : List Sym) :
    Prog (TablePartS × List RelationS) := do
  let at_ (c : Nat) : Column := .table t.opcode c
  let pt := point.take logHeight
  let mut sent : Array (Option Sym) := Array.replicate t.width none
  let mut relations : Array RelationS := #[]
  for column in sentColumns t do
    let value ← nextScalar
    sent := sent.set! column (some value)
    relations := relations.push (← equalS (at_ column) pt value)
  let mut pull ← one
  let mut push ← one
  let mut pullDegree := 1
  let mut pushDegree := 0
  for (pulled, pushed) in t.flushes.pull.zip t.flushes.push do
    let (known, terms) ← linearise pulled weights sent
    let mut dPull := 0
    if terms.isEmpty then
      dPull ← add beta known
    else
      let value ← nextScalar
      let vb ← add value beta
      let vbk ← add vb known
      relations := relations.push ⟨terms.map (fun (c, k) ↦ termS (at_ c) pt k), vbk⟩
      dPull := value
    let (knownDifference, differenceTerms) ← linearise (difference pushed pulled) weights sent
    let mut dPush := 0
    if differenceTerms.isEmpty then
      dPush ← add dPull knownDifference
    else
      let (knownPush, termsPush) ← linearise pushed weights sent
      let value ← nextScalar
      let vb ← add value beta
      let vbk ← add vb knownPush
      relations := relations.push ⟨termsPush.map (fun (c, k) ↦ termS (at_ c) pt k), vbk⟩
      dPush := value
    pull ← mul pull dPull
    push ← mul push dPush
    pullDegree := pullDegree + tupleDegree pulled
    pushDegree := pushDegree + tupleDegree pushed
  return (⟨pull, push, pullDegree, pushDegree, sent⟩, relations.toList)

/-- **`quotient_terms(column, sizes, w, scale)`**. -/
def quotientTerms (column : Nat → Column) (sizes : List Nat) (w : List Sym) (scale : Sym) : Prog (List TermS) := do
  let mut factor := scale
  let mut out : Array TermS := #[]
  for (e, chunk) in sizes.zip (List.range sizes.length) do
    out := out.push (termS (column chunk) (w.take e) factor)
    factor ← mul factor (w.getD e 0)
  return out.toList

/-- The longest point having point `p` as a prefix (itself included), the first among equals. -/
def longestOfS (points : Array (List Sym)) (p : Nat) : Nat :=
  let pp := points.getD p []
  (List.range points.size).foldl (fun best q ↦
    let pq := points.getD q []
    if pq.length ≥ pp.length ∧ pq.take pp.length == pp ∧ pq.length > (points.getD best []).length then q
    else best) p

/-- Add `coefficient` to the term `(column, p, twist)`, or append it. -/
def mergeTermS (terms : Array (Column × Nat × Nat × Sym)) (column : Column) (p twist : Nat) (coefficient : Sym) :
    Prog (Array (Column × Nat × Nat × Sym)) := do
  match terms.findIdx? (fun (c, q, k, _) ↦ c == column && q == p && k == twist) with
  | some i =>
    let (c, q, k, v) := terms.getD i (column, p, twist, 0)
    return terms.set! i (c, q, k, ← add v coefficient)
  | none => return terms.push (column, p, twist, coefficient)

/-- **`Relations::combine(commitment, ρ)`**, its points compared by their nodes. -/
def combine (relations : List RelationS) (commitment : Commitment) (rho : Sym) : Prog (Option CombinedS) := do
  let mine := relations.filter (·.commitment == commitment)
  if mine.isEmpty then return none
  let mut points : Array (List Sym) := #[]
  let mut terms : Array (Column × Nat × Nat × Sym) := #[]
  let mut value ← zero
  let mut scale ← one
  for relation in mine do
    let sv ← mul scale relation.value
    value ← add value sv
    for t in relation.terms do
      let p := (points.findIdx? (· == t.point)).getD points.size
      if p = points.size then
        points := points.push t.point
      let coefficient ← mul scale t.coefficient
      terms ← mergeTermS terms t.column p t.twist coefficient
    scale ← mul scale rho
  let longest := (List.range points.size).map (longestOfS points)
  let kept := (List.range points.size).filter fun p ↦ longest.getD p p == p
  let renumber (p : Nat) : Nat := kept.idxOf (longest.getD p p)
  let mut merged : Array (Column × Nat × Nat × Sym) := #[]
  for (column, p, twist, coefficient) in terms do
    merged ← mergeTermS merged column (renumber p) twist coefficient
  return some ⟨kept.map (points.getD · []), merged.toList, value, mine.length⟩

/-! ### The batch's weights (`weight_at`, `EqCache`) -/

/-- **`EqCache::selector(from, offset)`**: `Π_(k ≥ from) eq(bit_k(offset), r_k)`, from the top down. -/
def selectorS (r : List Sym) : Nat → Nat → Nat → Prog Sym
  | 0, _, _ => one
  | fuel + 1, fromVar, offset =>
    if fromVar ≥ r.length then one else do
      let rest ← selectorS r fuel (fromVar + 1) offset
      let rf := r.getD fromVar 0
      let factor ← if offset.testBit fromVar then pure rf else do add (← one) rf
      mul factor rest

/-- A column's part: `Σ_limbs basis[limb] · selector(vars, offset)`, and its variables. -/
def partS (r : List Sym) (basis : List Sym) (layout : StackLayout) (column : Column) : Prog (Nat × Sym) := do
  let limbs := layout.limbs column
  let vars := (limbs.headD (0, 0, 0)).2.1
  let mut sum ← zero
  for (limb, _, offset) in limbs do
    let selector ← selectorS r (r.length + 1) vars offset
    let term ← if limb = 0 then pure selector else mul (basis.getD limb 0) selector
    sum ← add sum term
  return (vars, sum)

/-! ### `reduce` -/

/-- What π1-rec3's verifier leaves: the roots' halves, the point claims (commitment, point, value). -/
structure ReducedS where
  root1 : Sym × Sym
  root2 : Sym × Sym
  openings : List (Commitment × List Sym × Sym)

/-- **The row counts** (step 0): each count's range required zero, its bits `0..=r`. -/
def countBits (heights : List Nat) : Prog (List (List Sym)) := do
  let mut out : Array (List Sym) := #[]
  for r in heights do
    let count ← nextInteger 4
    requireZero (← bits count (r + 1) 32)
    let hi ← bits count r 1
    let lo ← bits count 0 r
    requireZero (← mul hi lo)
    let mut bs : Array Sym := #[]
    for b in [0:r + 1] do
      bs := bs.push (← bits count b 1)
    out := out.push bs.toList
  return out.toList

/-- **The heap's relations** (step 6) and the leaf quotients' columns. -/
def heapRelations (shape : Shape) (active : List Sym) (parts : List TablePartS) (weights : Array Sym)
    (beta heapValue constraintValue memoryPull memoryPush bytecodePull bytecodePush : Sym) (w : List Sym)
    (constraintChunks : List Nat) : Prog (List RelationS × List (Column × Nat × Bool)) := do
  let heap := shape.heap
  let h := heap.h
  let lb := shape.logBytecode
  let o ← one
  let atT := w.take h
  let mut relations : Array RelationS := #[← equalS .heap atT heapValue]
  let mut columns : Array (Column × Nat × Bool) := #[]
  let atS := (w.drop 1).take h
  let n0 ← add (atT.getD 0 0) o
  let atNext := atT.set 0 n0
  let w1 := w.getD 1 0
  let wh := w.getD h 0
  let w1v ← mul w1 heapValue
  let whh ← mul wh wh
  let z ← zero
  relations := relations.push ⟨[termS .heap atS w1, termS .heap atNext w1v, termS (.treeQuotient 0) atT wh,
    termS (.treeQuotient 1) [] whh], z⟩
  let mut atOne : Array Sym := #[]
  for l in [0:h] do
    atOne := atOne.push (← if l = 0 then pure o else zero)
  let c1 ← const sepState
  let w0s ← mul (weights.getD 0 0) c1
  let i1 ← add beta w0s
  let i2 ← add i1 (weights.getD 1 0)
  let init ← add i2 (weights.getD 2 0)
  let last ← const (gpow (2 ^ lb - 1))
  let c2 ← const sepState
  let w0s' ← mul (weights.getD 0 0) c2
  let f1 ← add beta w0s'
  let w1l ← mul (weights.getD 1 0) last
  let f2 ← add f1 w1l
  let fin ← add f2 (weights.getD 2 0)
  relations := relations.push ⟨[termS .heap atOne.toList init], fin⟩
  for (block, index) in heap.blocks.zip (List.range heap.blocks.length) do
    let mut mixed : Array Sym := #[]
    for l in [0:h] do
      let constant ← const (pointE (block.position >>> l))
      mixed := mixed.push (← if l < block.r then add (w.getD l 0) constant else pure constant)
    let n := 2 ^ block.r
    let wr := w.getD block.r 0
    match block.leaves with
    | .unused =>
      relations := relations.push ⟨[termS .heap mixed.toList o], o⟩
    | leaves =>
      let (pull, push, d, scale) ← match leaves with
        | .memory => pure (memoryPull, memoryPush, degree (2 * (n - 1)) n, wr)
        | .bytecode => pure (bytecodePull, bytecodePush, degree (2 * (n - 1)) n, wr)
        | .table t => do
          let part := parts.getD t ⟨0, 0, 0, 0, #[]⟩
          let zz := active.getD t 0
          let square ← mul zz zz
          let rows := Shape.leastRows block.r
          let d := degree (max part.pullDegree part.pushDegree * (n - 1) + (n - rows)) n
          let pw ← mul part.pull wr
          let pl ← add pw square
          let qw ← mul part.push wr
          let ps ← add qw square
          let sc ← mul wr zz
          pure (pl, ps, d, sc)
        | .unused => pure (0, 0, 0, 0)
      let sizes := chunks (d + 1)
      columns := columns ++ (sizes.zip (List.range sizes.length)).toArray.map fun (e, chunk) ↦
        (Column.leafQuotient index chunk, e, true)
      let qt ← quotientTerms (Column.leafQuotient index) sizes w scale
      relations := relations.push ⟨[termS .heap mixed.toList pull] ++ qt, push⟩
  let qt ← quotientTerms .constraintQuotient constraintChunks w o
  relations := relations.push ⟨qt, constraintValue⟩
  return (relations.toList, columns.toList)

/-- The big-endian number of some bytes. -/
def beNat (l : List UInt8) : Nat := l.foldl (fun acc b ↦ acc * 256 + b.toNat) 0

end RecGraph.Pi1
