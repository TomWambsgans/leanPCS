-- Part of this repository. Transcribed from `crates/leanvm/univariate/src/verifier.rs` (`reduce`, `table_part`,
-- `linearise`, `tuple_degree`, `chunks`, `quotient_terms`, `sent_columns`, `layouts`, `stack_layouts`, `degree`,
-- `Shape`). The tables, flushes, fingerprints, public lines and Flock are leanVM 42422001's
-- (https://github.com/leanEthereum/leanVM), read through `crates/leanvm/statement`. MIT OR Apache-2.0; see
-- AGENTS.md.
module

public import UniStatement.Domain
public import UniStatement.Heap
public import UniStatement.Flock
public import UniStatement.Batch

/-!
# The verifier (`verifier.rs`, SPEC.md §4–§8 and §13): from the stream to one claim per commitment

`reduceWith F shape publicWords blake2s mode`, line by line `reduce` at iteration 2 (`ad49e74`):

0. **The shape** must be one a verifier is built for (`Shape.validate`, F5), else `InvalidShape`. **The six row
   counts** (F1): 32-bit big-endian integers at the stream's start, absorbed with `C1`'s root; each `c ≤ 2^r`
   (`c >> (r+1) = 0`, and `c`'s low `r` bits zero if bit `r` is set: collected, `TableRows`); its bits `0..=r`.
1. **`C1`**, then `α ∈ E^4` (the tuple weights, `eq(α, ·)` over 16 slots), `β` (the fingerprint shift),
   `γ` (the constraints' batching).
2. **Flock** (`Flock.verify`, or with the point-claim ABI `Flock.verifyDeferred`: its matrices' reduction left
   to the batching sumcheck, lever 4a), on `q_flock`.
3. **`C2`**, then `t`, its digits `w_l(t)`, and each table's `Z_act(t)` from its count's bits
   (`activeVanishingFromBits`: the active rows are the fixed cosets of the count's set bits, F1b).
4. **The values at `t`** (`tablePart`, then the memory, the bytecode, `T(t)`, `Q_W(t)`): each table's
   counters and factor columns, then each flush's pull fingerprint (computed when every column of its tuple
   is sent, else sent and bound by a relation on `C1`), and its push fingerprint (the pull's plus their
   difference when the sent values give it, else sent and bound).
5. **The constraint quotient's identity** on `C1`: JUMP's two constraints, every table's counters
   (`z Π c + 1`, on every row: padding rows' counters are nonzero too, F1), BLAKE2S's limb copies against
   `q_flock`'s slots (read through `y(t)`), the public lines; batched by the powers of `γ`, each lifted to
   `V_{r_W}`; `= Q_W(t) w_{r_W}(t)`.
6. **`C2`**: `T(t)`, the tree, the root, each heap block's leaf identity (a table's times `Z_act`:
   `R (P_pull w_r + Z_act²) + Q w_r Z_act = P_push w_r + Z_act²`, F1), the constraint quotient's chunks.
7. **Flock's end** on `q_flock`: with the point-claim ABI and the tower order (the main line), one term for the
   whole ring-switch weight (`ringTwist`, evaluated by the batch at its point); in tower order otherwise, its 64
   coefficients (`towerCoefficients`); in leanVM's order, `ringSwitchCoefficients`; or the bit-slice
   combination.
8. **`ρ`** combines each commitment's relations (`combine`); then one claim per commitment: weighted
   (extension W) or by the batching sumcheck (`batch`, a module of its own, with Flock's pending matrices) to
   point claims (the ABI).

The verdict is `reduce`'s: no error, every collected value zero, the stream consumed (`run`, `Accepts`). What
`PCS_OPEN` then checks of the claims is `Opening.lean`'s.

Degrees are `ℕ`, whose subtraction saturates as the Rust's `degree` (F5); every Rust `u64` here stays below
`2^64` at a valid shape (heights at most `31`).
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol

/-- **The sizes a contract is built for** (`Shape`): the memory's and the bytecode's log-sizes and each table's
log-height (XOR, MUL, SET, DEREF, JUMP, BLAKE2S), one contract per shape class. The heap, the stacks and every
quotient's size depend on these only. The Rust's `Shape` carries row counts, of which only the heights
`⌈log₂ rows⌉` are read (`shapeWith`). **The row counts are the stream's** (iteration 2, F1): the verifier reads
them (`reduceWith`), any count up to `2^r`. -/
structure Shape where
  logMemory : ℕ
  logBytecode : ℕ
  heights : List ℕ
  deriving Inhabited, Repr

/-- **`Shape::least_rows(r)`**: the fewest rows of a height-`r` table, which size its quotients:
`2^(r−1) + 1` (`0` at height `0`). -/
def Shape.leastRows (r : ℕ) : ℕ := if r = 0 then 0 else 2 ^ (r - 1) + 1

/-- The rows each table's quotients are sized for (`least_rows` of its height). -/
def Shape.capacityRows (s : Shape) : List ℕ := s.heights.map Shape.leastRows

/-- **`degree(plus, minus)`**: a quotient's degree `plus − minus`, `0` where a small domain makes it negative
(F5: the Rust's `saturating_sub`; `ℕ`'s subtraction). -/
def degree (plus minus : ℕ) : ℕ := plus - minus

/-- **`Shape::validate(flock)`** (F5): the shapes a verifier can be built for: the memory at least `2` cells (the
public input's), every height below `32` (the counts are 32-bit), and with Flock BLAKE2S's height at least `7`
(its zerocheck's seven fixed coordinates). -/
def Shape.validate (s : Shape) (flock : Bool) : Bool :=
  !(decide (s.logMemory < 1) || s.heights.any (· > 31) || (flock && decide (s.heights.getD opSha3 0 < 7)))

/-- **A valid shape**, for a deployment of the main line (Flock): six tables, and `Shape.validate` with Flock. -/
def Shape.Valid (s : Shape) : Prop := s.heights.length = 6 ∧ s.validate true = true

instance (s : Shape) : Decidable s.Valid := inferInstanceAs (Decidable (_ ∧ _))

/-- **Row counts an honest prover's quotients fit**: six, each at least the fewest its table's height sizes for
and at most its height (so `⌈log₂ rows⌉` is the height). The verifier accepts any count up to `2^r`; with fewer
than `leastRows r` rows an honest quotient does not fit (a smaller shape class), and soundness does not depend
on it. -/
def Shape.RowsFit (s : Shape) (rows : List ℕ) : Prop :=
  rows.length = 6 ∧ ∀ t < 6, s.capacityRows.getD t 0 ≤ rows.getD t 0 ∧ rows.getD t 0 ≤ 2 ^ s.heights.getD t 0

instance (s : Shape) (rows : List ℕ) : Decidable (s.RowsFit rows) := inferInstanceAs (Decidable (_ ∧ _))

/-- `Shape::constraint_vars`: the domain of the constraint quotient, the largest table or the memory. -/
def Shape.constraintVars (s : Shape) : ℕ := (s.heights ++ [s.logMemory]).foldl max 0

/-- `Shape::heap`. -/
def Shape.heap (s : Shape) : HeapLayout := HeapLayout.new s.logMemory s.logBytecode s.heights

/-- `factor_columns(opcode)`: the columns a table sends at `t` besides its counters, every factor of a
product in its flushes and constraints. -/
def factorColumns (opcode : ℕ) : List String :=
  if opcode = opMul then ["fp", "pc", "va_0", "va_1", "va_2"]
  else if opcode = opDeref then ["fp", "pc", "ptr", "f_pc", "f_fp"]
  else if opcode = opJump then ["fp", "b", "v_cond"]
  else ["fp", "pc"]

/-- **`sent_columns(table)`**: the counters, then the factor columns, in the order they are sent. -/
def sentColumns (t : Table) : List ℕ :=
  t.countColumns ++ (factorColumns t.opcode).map (colIdx t.columns)

/-- Add `c` to `column`'s coefficient, or append it (`linearise`'s `add`). -/
def addTerm (terms : List (ℕ × E)) (column : ℕ) (c : E) : List (ℕ × E) :=
  match terms.findIdx? (·.1 == column) with
  | some i => terms.modify i fun (k, v) ↦ (k, v + c)
  | none => terms ++ [(column, c)]

/-- **`linearise(tuple, weights, sent)`**: `Σ_s weights[s] · tuple[s]` split into what the sent values give
and the terms in the other columns (a product of a sent and an unsent column is a term in the unsent one;
the tables have no product of two unsent columns). -/
def linearise (tuple : List Form) (weights : Array E) (sent : Array (Option E)) : E × List (ℕ × E) :=
  ((tuple.zip (List.range tuple.length)).foldl (fun (acc : E × List (ℕ × E)) (form, s) ↦
    let weight := weights.getD s 0
    form.foldl (fun (acc : E × List (ℕ × E)) (monomial, coefficient) ↦
      let (known, terms) := acc
      if coefficient = 0 then acc else
      let c := weight * coefficient
      match monomial with
      | [] => (known + c, terms)
      | [i] => match sent.getD i none with
        | some v => (known + c * v, terms)
        | none => (known, addTerm terms i c)
      | [i, j] => match sent.getD i none, sent.getD j none with
        | some a, some b => (known + c * a * b, terms)
        | some a, none => (known, addTerm terms j (c * a))
        | none, some b => (known, addTerm terms i (c * b))
        | none, none => (known, terms)
      | _ => acc) acc) (0, []))

/-- `tuple_degree(tuple)`: the largest degree of a nonzero monomial, at least `1`. -/
def tupleDegree (tuple : List Form) : ℕ :=
  max 1 (tuple.foldl (fun d form ↦
    form.foldl (fun d (monomial, c) ↦ if c = 0 then d else max d monomial.length) d) 0)

/-- **`chunks(count)`**: `Σ_k 2^(e_k)`, at most three powers of two, covering `count` coefficients (a
quotient's chunks: the largest powers of two, the third rounded up). -/
def chunks (count : ℕ) : List ℕ := Id.run do
  let mut sizes : Array ℕ := #[]
  let mut left := count
  for _ in [0:4] do
    if left > 0 then
      let top := Nat.log2 left
      if sizes.size = 2 ∧ left ≠ 2 ^ top then
        sizes := sizes.push (top + 1)
        left := 0
      else
        sizes := sizes.push top
        left := left - 2 ^ top
  return sizes.toList

/-- **`quotient_terms(column, sizes, w, scale)`**: `Q(t) = Q_0 + w_{e_0}(Q_1 + w_{e_1}(Q_2 …))` times `scale`,
as terms on the chunks, chunk `c` at `w[..e_c]`. -/
def quotientTerms (column : ℕ → Column) (sizes : List ℕ) (w : List E) (scale : E) : List Term :=
  ((sizes.zip (List.range sizes.length)).foldl (fun (acc : Array Term × E) (e, chunk) ↦
    (acc.1.push (term (column chunk) (w.take e) acc.2), acc.2 * w.getD e 0)) (#[], scale)).1.toList

/-- One table's part of the check (`TablePart`): its leaf's two products, their degrees over `n − 1`, its
sent values. -/
structure TablePart where
  pull : E
  push : E
  pullDegree : ℕ
  pushDegree : ℕ
  sent : Array (Option E)
  deriving Inhabited

/-- The push tuple's difference from the pull tuple, slot by slot (`pushed + pulled`). -/
def difference (pushed pulled : List Form) : List Form :=
  (pushed.zip pulled).map fun (a, b) ↦ a.addScaled b 1

/-- A table's leaf degrees over `n − 1` (`TablePart`'s `pull_degree`, `push_degree`): `1 + Σ` the pull tuples'
degrees (the leaf's `R` factor), `Σ` the push tuples'. They do not depend on the stream. -/
def tableDegrees (t : Table) : ℕ × ℕ :=
  (t.flushes.pull.zip t.flushes.push).foldl (fun (acc : ℕ × ℕ) (pulled, pushed) ↦
    (acc.1 + tupleDegree pulled, acc.2 + tupleDegree pushed)) (1, 0)

/-- **How the relations reach `PCS_OPEN`** (`Claims`). -/
inductive ClaimsMode where
  /-- `PCS_OPEN`'s ABI: point claims, by the batching sumcheck. -/
  | point
  /-- Extension W: one weighted claim per commitment. -/
  | weighted
  deriving DecidableEq, Repr, Inhabited

/-- `FLOCK_MAIN`: the main line, (a′), skip 3, the slices sent, the ring map in tower order (iteration 2,
lever 1a). -/
def flockMain : Flock.Variant := ⟨3, .tower⟩
/-- `FLOCK_BIT_SLICE`: extension B, skip 4, the slices left to a bit-slice claim. -/
def flockBitSlice : Flock.Variant := ⟨4, .claim⟩
/-- `FLOCK_LEANVM_SKIP`: leanVM's skip 6 with (a′)'s weighted claim (the ring map in leanVM's order). -/
def flockLeanvmSkip : Flock.Variant := ⟨6, .weighted⟩

/-- **What the verifier leaves** (`Reduced`): the two roots (each its halves), one opening per commitment,
Flock's claims on `A0`, `B0`, the number of relations combined, each stack's variables, and (iteration 2) the
three stacks' layouts, a function of the shape alone (`layoutsOf`). -/
structure Reduced where
  roots : (E × E) × (E × E)
  openings : List (Commitment × Opening)
  matrices : Option Flock.MatrixClaim
  relations : ℕ
  stackVars : List (Commitment × ℕ)
  layouts : List (Commitment × StackLayout)
  deriving Inhabited

/-- **The setup stack's columns** (`stack_layouts`' setup): the bytecode's tuples (`lb + 4`), the memory's
addresses. They do not depend on the tables. -/
def setupStackColumns (shape : Shape) : List (Column × ℕ × Bool) :=
  [(.bytecodeTuple, shape.logBytecode + 4, false), (.address, shape.logMemory, false)]

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`table_part`**: a table's sent values (each bound on `C1` at `w[..r]`), then its flushes'
fingerprints and its leaf's products; the relations it states, in order. -/
def tablePart (t : Table) (logHeight : ℕ) (weights : Array E) (beta : E) (w : List E) :
    ChanM m (TablePart × List Relation) := do
  let at_ (c : ℕ) : Column := .table t.opcode c
  let pt := w.take logHeight
  let mut sent : Array (Option E) := Array.replicate t.width none
  let mut relations : Array Relation := #[]
  for column in sentColumns t do
    let value ← nextScalar (m := m)
    sent := sent.set! column (some value)
    relations := relations.push (Relation.equal (at_ column) pt value)
  let mut pull : E := 1
  let mut push : E := 1
  let mut pullDegree := 1
  let mut pushDegree := 0
  for (pulled, pushed) in t.flushes.pull.zip t.flushes.push do
    -- The pull fingerprint: computed if every column is sent, else sent and bound.
    let (known, terms) := linearise pulled weights sent
    let mut dPull := beta + known
    if !terms.isEmpty then
      let value ← nextScalar (m := m)
      relations := relations.push ⟨terms.map (fun (c, k) ↦ term (at_ c) pt k), value + beta + known⟩
      dPull := value
    -- The push fingerprint: the pull's plus their difference, when the sent values give it; else sent.
    let (knownDifference, differenceTerms) := linearise (difference pushed pulled) weights sent
    let mut dPush := dPull + knownDifference
    if !differenceTerms.isEmpty then
      let (knownPush, termsPush) := linearise pushed weights sent
      let value ← nextScalar (m := m)
      relations := relations.push ⟨termsPush.map (fun (c, k) ↦ term (at_ c) pt k), value + beta + knownPush⟩
      dPush := value
    pull := pull * dPull
    push := push * dPush
    pullDegree := pullDegree + tupleDegree pulled
    pushDegree := pushDegree + tupleDegree pushed
  return (⟨pull, push, pullDegree, pushDegree, sent⟩, relations.toList)

/-- **The row counts** (step 0, iteration 2's F1): for each table of height `r`, the 4-byte count `c`, its range
collected (`c >> (r+1) = 0`, and bit `r` times `c`'s low `r` bits, `TableRows`), and its bits `0..=r` as
scalars. -/
def countBits (heights : List ℕ) : ChanM m (List (List E)) := do
  let mut out : Array (List E) := #[]
  for r in heights do
    let count ← nextInteger (m := m) 4
    requireZero (m := m) (intBits count (r + 1) 32)
    requireZero (m := m) (intBits count r 1 * intBits count 0 r)
    out := out.push ((List.range (r + 1)).map fun b ↦ intBits count b 1)
  return out.toList

end With

/-- **The heap's relations** (step 6) on `C2`, and the leaf quotients' columns: `T(t)`, the tree, the root,
each block's leaf identity (`R_b(o_b + t) P_pull + w_r(t) Q_b(t) = P_push` for the memory and the bytecode; a
table's times `Z_act` (`active`, F1): `R_b(o_b + t)(P_pull w_r + Z_act²) + w_r Z_act Q_b(t) = P_push w_r +
Z_act²`, its quotient sized for `leastRows r` rows; `R_u(o_u + t) = 1` on an unused block), the constraint
quotient's chunks. -/
def heapRelations (shape : Shape) (active : List E) (parts : List TablePart) (weights : Array E) (beta heapValue
    constraintValue memoryPull memoryPush bytecodePull bytecodePush : E) (w : List E)
    (constraintChunks : List ℕ) : List Relation × List (Column × ℕ × Bool) := Id.run do
  let heap := shape.heap
  let h := heap.h
  let lb := shape.logBytecode
  let atT := w.take h
  let mut relations : Array Relation := #[Relation.equal .heap atT heapValue]
  let mut columns : Array (Column × ℕ × Bool) := #[]
  -- The tree: w_1 (T(s(t)) + T(t) T(t+1)) + w_h Q_tree(t) = 0, Q_tree = Q_0 + w_h q_1.
  let atS := (w.drop 1).take h
  let atNext := atT.modify 0 (· + 1)
  let w1 := w.getD 1 0
  let wh := w.getD h 0
  relations := relations.push ⟨[term .heap atS w1, term .heap atNext (w1 * heapValue),
    term (.treeQuotient 0) atT wh, term (.treeQuotient 1) [] (wh * wh)], 0⟩
  -- The root: T(1) (β + fp(SEP_STATE, 1, 1)) = β + fp(SEP_STATE, g^(2^lb − 1), 1).
  let atOne := (List.range h).map fun l ↦ if l = 0 then (1 : E) else 0
  let init := beta + weights.getD 0 0 * sepState + weights.getD 1 0 + weights.getD 2 0
  let last := gpow (2 ^ lb - 1)
  let fin := beta + weights.getD 0 0 * sepState + weights.getD 1 0 * last + weights.getD 2 0
  relations := relations.push ⟨[term .heap atOne init], fin⟩
  -- Each block's leaves.
  for (block, index) in heap.blocks.zip (List.range heap.blocks.length) do
    let mixed := (List.range h).map fun l ↦
      let c := pointE (block.position >>> l)
      if l < block.r then w.getD l 0 + c else c
    let n := 2 ^ block.r
    let wr := w.getD block.r 0
    let leaf : Option (E × E × ℕ × E) := match block.leaves with
      | .unused => none
      | .memory => some (memoryPull, memoryPush, degree (2 * (n - 1)) n, wr)
      | .bytecode => some (bytecodePull, bytecodePush, degree (2 * (n - 1)) n, wr)
      | .table t =>
        -- Padding rows' leaves are 1, whatever they hold: (R P_pull + P_push) Z_pad + (R + 1) Z_act = Q w_r,
        -- here times Z_act (Z_pad Z_act = w_r). Sized for the fewest rows of the height, 2^(r−1) + 1.
        let part := parts.getD t default
        let z := active.getD t 0
        let square := z * z
        let rows := Shape.leastRows block.r
        let d := degree (max part.pullDegree part.pushDegree * (n - 1) + (n - rows)) n
        some (part.pull * wr + square, part.push * wr + square, d, wr * z)
    match leaf with
    | none => relations := relations.push ⟨[term .heap mixed 1], 1⟩
    | some (pull, push, d, scale) =>
      let sizes := chunks (d + 1)
      columns := columns ++ (sizes.zip (List.range sizes.length)).toArray.map fun (e, chunk) ↦
        (Column.leafQuotient index chunk, e, true)
      relations := relations.push ⟨[term .heap mixed pull] ++
        quotientTerms (Column.leafQuotient index) sizes w scale, push⟩
  relations := relations.push ⟨quotientTerms .constraintQuotient constraintChunks w 1, constraintValue⟩
  return (relations.toList, columns.toList)

end UniStatement

end
