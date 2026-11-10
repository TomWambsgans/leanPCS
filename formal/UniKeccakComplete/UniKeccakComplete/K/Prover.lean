-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows `crates/leanvm/univariate/src/prover/prove.rs`
-- (branch `leanvm-univariate-prover2`): the prover phase by phase, its messages in the verifier's order
-- (`formal/UniKeccak/UniKeccak/Verifier.lean`'s `reduceWithK`).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/Prover.lean`.
import UniKeccakComplete.K.Quotients
import UniKeccakComplete.K.Batch
import E2ECompleteness.WithHash
import UniKeccakComplete.K.PcsProver

/-!
# The honest prover (`prove.rs`) of the Keccak VM, on a placed trace

`proveStreamWith`, phase by phase, writing the stream `reduceWithK` (the main line) reads:

0. the six row counts (4-byte big-endian);
1. `C1` (every column in basis `B`, `z_T`, the memory, the bytecode's final counts, `q_flock` as values), committed,
   its root's halves; then `α ∈ E^4`, `β`, `γ`;
2. Flock on the Keccak-f block (a prover given as a function, `FlockProver`: its messages, the ring map; the
   verifier checks the lincheck's terminal itself, `structuredTerminal`, so nothing is left to the batch);
3. the heap's values, its novel and basis-`B` coefficients; the quotients (exact divisions); `C2`, committed, its
   root's halves; then `t`;
4. the values at `t`, in `reduceWith`'s order;
5. `ρ`; the relations exactly as `reduceWith` states them (its own `tablePart` run on the values each table sends,
   and its pure `constraintRelation`, `heapRelations`, `combine`); the combined claims;
6. `λ`, the batching sumcheck's rounds (`batchRounds`, the dense weights of the combined claims), the three stacks'
   values at its point (no matrices' term, no `a`, `b`).

`proveWith` adds the setup (its one tree, as the experiment's `setupTreeKWith`, recomputed), the Keccak contract's
IV, the seed, and the three WHIR openings (`C1`, `C2`, the setup) (`proveOpeningWithH`, the Statement's honest opening): `none` if a proof of
work fails. The commitments go through a function (`commit`), the real one `commitWithH`; the differential test
passes stand-in roots.
-/

namespace UniKeccakComplete

open UniComplete

open UniStatement UniKeccak LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- A commitment: the tree the opening needs, and the root's halves the stream carries. -/
structure Committed where
  tree : LeanVM.Prover.Tree
  halves : E × E

/-- What Flock's prover leaves: `q_flock`'s point and its end on `q_flock` (the ring switch's map and target), what
the verifier's `verifyWalkedK` returns. -/
structure FlockOut where
  point : List E
  end_ : Flock.End
  deriving Inhabited

/-- **Flock's prover** (`FlockProver`): at `log_n` variables and a variant, on `q_flock`'s words, its messages
written and its challenges drawn as `UniKeccak.verifyWalkedK` reads them. -/
abbrev FlockProver (m : Type → Type) : Type := ℕ → UniKeccak.KeccakVariant → Array K → WrM m FlockOut

/-- Run a channel program that only reads, on given bytes: the verifier's own code on the values it reads. -/
def runReader {α : Type} [Inhabited α] (x : ChanM Id α) (bytes : List UInt8) : α :=
  match (x.run.run (Chan.start default bytes.toArray) : Id (Except UniError α × Chan)) with
  | (.ok a, _) => a
  | (.error _, _) => default

/-- **What table `t` sends at `t`** (`tablePart`'s reads): its sent columns' values, then each flush's pull
fingerprint when its tuple reads an unsent column, and its push fingerprint when their difference does. -/
def tableValues (table : Table) (at_ : ℕ → E) (weights : Array E) (beta : E) : List E := Id.run do
  let mut sent : Array (Option E) := Array.replicate table.width none
  let mut out : Array E := #[]
  for column in sentColumns table do
    sent := sent.set! column (some (at_ column))
    out := out.push (at_ column)
  for (pulled, pushed) in table.flushes.pull.zip table.flushes.push do
    if !(linearise pulled weights sent).2.isEmpty then
      out := out.push (fpE pulled weights beta at_)
    if !(linearise (difference pushed pulled) weights sent).2.isEmpty then
      out := out.push (fpE pushed weights beta at_)
  return out.toList

/-- The stream so far, and what the openings need. -/
structure CoreOut where
  stream : Array UInt8
  c1 : Array K × Committed
  c2 : Array K × Committed
  setup : Array K
  /-- One point claim per commitment, in the combined claims' order. -/
  claims : List (Commitment × List E × E)
  /-- For the tests: the combined claims, the heap's values. -/
  combined : List (Commitment × Combined)
  heap : Array E

instance : Inhabited Committed := ⟨⟨⟨0, fun _ ↦ [], #[]⟩, (0, 0)⟩⟩

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)

/-- **`C2`'s columns** after the bus's and the constraints' challenges (`prove`, steps 4–6): the heap's values, its
novel and basis-`B` coefficients; the tree quotient's, the constraint quotient's and every used block's leaf
quotient's chunks (in basis `B`); the stack. -/
structure C2Data where
  heapVals : Array E
  heapNovel : Array E
  heapB : Array E
  treeChunks : List (Array E)
  constraintSizes : List ℕ
  constraintChunks : List (Array E)
  leafChunks : List (ℕ × List ℕ × List (Array E))
  stack : Array K

/-- **`C2`** at `α` (through its `eq` weights), `β`, `γ`. -/
def c2DataOf (tr : Trace) (weights : Array E) (beta gamma : E) : C2Data :=
  let shape := tr.shape
  let heap := shape.heap
  let h := heap.h
  let heapVals := heapValues tr weights beta
  let heapNovel := novelOfValuesE h heapVals
  let heapB := bOfNovelE h heapNovel
  let treeChunks := chunksB (treeQuotient h heapNovel) [h, 0]
  let constraintSizes := chunks (UniKeccak.Shape.constraintDegreeK shape + 1)
  let constraintQ := chunksB (constraintQuotient tr gamma (publicWordsOf tr.publicInput)) constraintSizes
  let leafChunks : List (ℕ × List ℕ × List (Array E)) :=
    (heap.blocks.zip (List.range heap.blocks.length)).filterMap fun (block, index) ↦
      match UniKeccak.Shape.leafDegreeK block, leafNumerator tr weights beta block
          (ofNovel block.r (novelOfValuesE block.r (blockLeaves tr weights beta block.leaves))) with
      | some d, some numerator =>
        let sizes := chunks (d + 1)
        some (index, sizes, chunksB (divM numerator (wPoly block.r)) sizes)
      | _, _ => none
  let c2Layout := ((UniKeccak.layoutsOfK shape).lookup .c2).getD default
  let c2Words : Column → ℕ → Array K := fun column limb ↦
    match column with
    | .heap => limbWords heapB limb
    | .treeQuotient c => limbWords (treeChunks.getD c #[]) limb
    | .constraintQuotient c => limbWords (constraintQ.getD c #[]) limb
    | .leafQuotient b c => match leafChunks.find? (·.1 == b) with
      | some (_, _, parts) => limbWords (parts.getD c #[]) limb
      | none => #[]
    | _ => #[]
  ⟨heapVals, heapNovel, heapB, treeChunks, constraintSizes, constraintQ, leafChunks, placeStack c2Layout c2Words⟩

/-- **What the prover sends at `t` and what the verifier states then** (`prove`, step 7; `reduceWithK`, steps 4–7):
every value in the verifier's order (per table `tableValues`, then the memory's three, the bytecode's two, `T(t)`
and `Q_W(t)`), every relation (each table's by the verifier's own `tablePart` on the values it reads; the rest by
its pure `constraintRelation`, `heapRelations`; Flock's ring term), `C2`'s columns as the verifier lists them, the
ring map. -/
structure AtT where
  values : List E
  relations : List Relation
  c2Columns : List (Column × ℕ × Bool)
  ringMap : Option (List E)

/-- **The values and the relations at `t`**, from the trace, `C2`, the challenges and Flock's output. -/
def atTOf (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) (flockOut : Option FlockOut) :
    AtT := Id.run do
  let shape := tr.shape
  let heights := shape.heights
  let h := shape.heap.h
  let rW := shape.constraintVars
  let lm := shape.logMemory
  let lb := shape.logBytecode
  let weights := eqKernel alphas
  let w := digits t (max h (rW + 4) + 2)
  let active := ((tr.rows.zip heights).map fun (rows, r) ↦
    activeVanishingFromBits w ((List.range (r + 1)).map fun b ↦ intBits rows b 1) r)
  let mut sent : Array E := #[]
  let mut relations : Array Relation := #[]
  let mut parts : Array TablePart := #[]
  for table in tablesKeccak do
    let r := heights.getD table.opcode 0
    let at_ : ℕ → E := fun c ↦ evalB ((bCoefficients r (tr.column table.opcode c)).map ofK) r w
    let values := tableValues table at_ weights beta
    sent := sent ++ values.toArray
    let (part, rels) := runReader (tablePart (m := Id) table r weights beta w) (values.flatMap scalarWire)
    parts := parts.push part
    relations := relations ++ rels.toArray
  let memAt (k : ℕ) : E := evalB ((bCoefficients lm (tr.memory.getD k #[])).map ofK) lm w
  let memoryFinalCount := memAt 3
  let address := evalB ((bCoefficients lm (addressColumn lm)).map ofK) lm w
  let memoryPull := memoryFp weights beta address memoryFinalCount ((List.range 3).map memAt)
  sent := sent ++ #[memoryFinalCount, address, memoryPull]
  relations := relations.push (Relation.equal (.memory 3) (w.take lm) memoryFinalCount)
  relations := relations.push (Relation.equal .address (w.take lm) address)
  relations := relations.push ⟨(List.range 3).map (fun k ↦ term (.memory k) (w.take lm) (weights.getD (3 + k) 0)),
    memoryPull + beta + weights.getD 0 0 * sepMem + weights.getD 1 0 * address +
      weights.getD 2 0 * memoryFinalCount⟩
  let memoryPush := memoryPull + weights.getD 2 0 * (1 + memoryFinalCount)
  let bytecodeFinalCount := evalB ((bCoefficients lb tr.bytecodeFinal).map ofK) lb w
  let slotAt (s : ℕ) : E := evalB ((bCoefficients lb (tr.slots.getD s #[])).map ofK) lb w
  let bytecodePull := bytecodeFp weights beta fun s ↦ if s = 2 then bytecodeFinalCount else slotAt s
  sent := sent ++ #[bytecodeFinalCount, bytecodePull]
  relations := relations.push (Relation.equal .bytecodeFinal (w.take lb) bytecodeFinalCount)
  relations := relations.push (Relation.equal .bytecodeTuple (alphas ++ w.take lb)
    (bytecodePull + beta + weights.getD 2 0 * bytecodeFinalCount))
  let bytecodePush := bytecodePull + weights.getD 2 0 * (1 + bytecodeFinalCount)
  let heapValue := evalB c2.heapB h w
  let constraintValue := ((c2.constraintChunks.zip c2.constraintSizes).foldl (fun (acc : E × E) (chunk, e) ↦
    (acc.1 + acc.2 * evalB chunk e w, acc.2 * w.getD e 0)) (0, 1)).1
  sent := sent ++ #[heapValue, constraintValue]
  -- The constraint quotient's identity; the heap's.
  let (constraint, quotientDegree) :=
    UniKeccak.constraintRelationK shape parts.toList (publicWordsOf tr.publicInput) gamma t constraintValue w
  relations := relations.push constraint
  let verifierChunks := chunks (quotientDegree + 1)
  let c2Columns : List (Column × ℕ × Bool) :=
    [(.heap, h, true), (.treeQuotient 0, h, true), (.treeQuotient 1, 0, true)] ++
      (verifierChunks.zip (List.range verifierChunks.length)).map fun (e, c) ↦
        (Column.constraintQuotient c, e, true)
  let (heapRels, leafColumns) := heapRelations shape active parts.toList weights beta heapValue
    constraintValue memoryPull memoryPush bytecodePull bytecodePush w verifierChunks
  relations := relations ++ heapRels.toArray
  -- Flock's claim on q_flock: one term for the ring switch's weight (the main line).
  let mut ringMap : Option (List E) := none
  match flockOut with
  | some out =>
    match out.end_ with
    | .ring map target =>
      relations := relations.push ⟨[⟨.qflock, out.point, ringTwist, 1⟩], target⟩
      ringMap := some map
    | .combination _ _ => pure ()
  | none => pure ()
  return ⟨sent.toList, relations.toList, c2Columns ++ leafColumns, ringMap⟩

/-- The stacks' layouts the verifier states (`layouts shape c2Columns`), and one of them. -/
def layoutIn (stackLayouts : List (Commitment × StackLayout)) (c : Commitment) : StackLayout :=
  ((stackLayouts.find? (·.1 == c)).map (·.2)).getD default

/-- **The prover's stream** (`prove`, steps 0–9), from the seed. -/
def proveStreamWith (commit : Commitment → ℕ → Array K → m Committed) (flock : FlockProver m)
    (tr : Trace) : WrM m CoreOut := do
  let shape := tr.shape
  -- 0. The six row counts.
  for rows in tr.rows do
    sendInteger rows 4
  -- 1. C1.
  let stack1 := c1Stack tr
  let committed1 ← (StateT.lift (commit .c1 (UniKeccak.c1LayoutK shape).vars stack1) : WrM m Committed)
  sendRoot committed1.halves
  sendScalar (pcsOod (UniKeccak.c1LayoutK shape).vars stack1 (rootOf committed1.halves))
  let alphas ← samplesW H 4
  let beta ← sampleW H
  let gamma ← sampleW H
  -- 2. Flock on the Keccak-f block.
  let logN := keccakR1csLogSize + shape.heights.getD opSha3 0
  let flockOut : Option FlockOut ← some <$> flock logN UniKeccak.keccakMain tr.qflock
  -- 3. The heap, the quotients, C2.
  let c2 := c2DataOf tr (eqKernel alphas) beta gamma
  let committed2 ← (StateT.lift (commit .c2 (((UniKeccak.layoutsOfK shape).lookup .c2).getD default).vars c2.stack) :
    WrM m Committed)
  sendRoot committed2.halves
  sendScalar (pcsOod (((UniKeccak.layoutsOfK shape).lookup .c2).getD default).vars c2.stack (rootOf committed2.halves))
  -- 4.–7. The values at t.
  let t ← sampleW H
  let a := atTOf tr c2 alphas beta gamma t flockOut
  sendScalars a.values
  -- 8. ρ, the combined claims.
  let rho ← sampleW H
  let combined : List (Commitment × Combined) :=
    commitments.filterMap fun c ↦ (combine a.relations c rho).map (c, ·)
  let stackLayouts := UniKeccak.layoutsK shape a.c2Columns
  let stack3 := setupStackOf tr
  let stackOf : Commitment → Array K
    | .c1 => stack1
    | .c2 => c2.stack
    | .setup => stack3
  -- 9. The batching sumcheck.
  let lambda ← sampleW H
  let vars := (stackLayouts.map (·.2.vars)).foldl max 0
  let st : BatchState := ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) a.ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), none, 0, []⟩
  let r ← batchRounds H lambda vars st
  let claims : List (Commitment × List E × E) := combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)
  sendScalars (claims.map (·.2.2))
  let c ← get
  return ⟨c.stream, (stack1, committed1), (c2.stack, committed2), stack3, claims, combined, c2.heapVals⟩

end With

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- The real commitment: the WHIR tree of the stack (`commitWithH`), its root's halves (`rootHalves`: its bytes as
they are, `prover::prove::halves`). -/
def commitReal (_ : Commitment) (vars : ℕ) (stack : Array K) : m Committed := do
  let tree ← E2ECompleteness.commitWithH H vars stack
  return ⟨tree, rootHalves tree.root⟩

/-- The setup's tree, as the experiment computes it (`setupTreeKWith`), from the trace's setup stack. -/
def setupTreeOf (tr : Trace) : m LeanVM.Prover.Tree :=
  E2ECompleteness.commitWithH H (setupLayout tr.shape).vars (setupStackOf tr)

/-- The seed of the contract's IV (`keccak(name ‖ IV ‖ public input)`). -/
def seedOf (iv publicInput : List UInt8) : m Digest := H (name ++ iv ++ publicInput)

/-- The Keccak contract's IV with Keccak-256 `H` (`contract_iv_for(·, Keccak(v), ·, ·)`, `contractIvKWith`): the
setup's commitment (its root and out-of-domain answer). -/
def contractIvOf (shape : UniStatement.Shape) (v : UniKeccak.KeccakVariant) (programIv : List UInt8)
    (roots : UniKeccak.SetupRootsK) : m (List UInt8) := do
  let d ← H (ivTag ++ programIv ++ digestBytes roots.f ++ UniKeccak.elementBytes24 roots.fOod ++
    shapeBytes shape ++ UniKeccak.variantBytesK v)
  return digestBytes d

/-- The setup's commitment as the prover computes it: the tree's root and the setup stack's out-of-domain answer. -/
def setupRootsOf (tr : Trace) (tree : LeanVM.Prover.Tree) : UniKeccak.SetupRootsK :=
  ⟨tree.root, pcsOod (setupLayout tr.shape).vars (setupStackOf tr) tree.root⟩

/-- **The honest prover** over `H`, `F` (`prove`) of the main line (`keccakMain`): the setup's tree, the Keccak
contract's IV (the setup's commitment, `setupRootsOf`), the seed, the stream, then the three PCS claims' openings
(`C1`, `C2`, the setup: `pcsProveH` at the commitment's stack variables `stackVarsK`); `none` if a proof of work
fails. -/
def proveWith (fuel : ℕ) (flock : FlockProver m) (programIv : List UInt8) (tr : Trace) :
    m (Option UniKeccak.KeccakProof) := do
  let tree ← setupTreeOf H tr
  let iv ← contractIvOf H tr.shape UniKeccak.keccakMain programIv (setupRootsOf tr tree)
  let seed ← seedOf H iv tr.publicInput
  let (out, _) ← (proveStreamWith H (commitReal H) flock tr).run (Wr.start seed)
  let openOne (c : Commitment) (pt : List E) (value : E) : m (Option Compile.Proof) :=
    let (stack, tree) : Array K × LeanVM.Prover.Tree := match c with
      | .c1 => (out.c1.1, out.c1.2.tree)
      | .c2 => (out.c2.1, out.c2.2.tree)
      | .setup => (out.setup, tree)
    pcsProveH H F fuel (UniKeccak.stackVarsK tr.shape c) tree stack pt value
  let p1 ← match out.claims.find? (·.1 == .c1) with
    | some (_, pt, v) => openOne .c1 pt v
    | none => pure none
  let p2 ← match out.claims.find? (·.1 == .c2) with
    | some (_, pt, v) => openOne .c2 pt v
    | none => pure none
  let p3 ← match out.claims.find? (·.1 == .setup) with
    | some (_, pt, v) => openOne .setup pt v
    | none => pure none
  return do
    let c1 ← p1
    let c2 ← p2
    let s ← p3
    pure ⟨out.stream, c1, c2, s⟩

end With

end UniKeccakComplete
