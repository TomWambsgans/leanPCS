-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The identities are
-- `docs/leanvm/univariate/KECCAK.md` and `formal/UniKeccak`'s `reduceWithK` (`constraintRelationK`, `layoutsK`,
-- `weightAtK`, `batchK`); the model is `formal/UniSound/UniSound/Ids/Model.lean`'s on the Keccak VM's tables.
import UniSound.Ids.Model
import UniSound.CodeTables
import UniSound.CodeBatch
import UniKeccakSound.FsK
import UniKeccakSound.Code.Shape

/-!
# The Keccak identity model's data

`UniSound/Ids/Model.lean`'s model for the Keccak VM (`formal/UniKeccak`'s `reduceWithK`), for a deployment `D`
(`KDeployment`) and Flock's phase on the Keccak-f block `Fl` (`KFlockSound F κ v`):

* **the relations** (`relsAtK`): `reduceWithK`'s steps 4–7 as a pure function of the values at `t`, the code-level
  link's (`UniKeccakSound.mainRelsK`, `flockClaimK`: `tablesKeccak`, the memory's, the bytecode's,
  `constraintRelationK`, the heap's `heapRelations`, Flock's ring term); no pending matrices;
* **the relations' differences** (`diffsK`): each commitment's relations on its candidate stack the way `batchK`
  reads them (`termWK`: `weightAtK` of the term alone, at the merged point, against the zero-extended stack);
* **the batch** (`prodK`, `targetK`): `Σ_{k<3} λ^k W_k C_k` over the batch's variables (`weightAtK`), and
  `Σ_k λ^k v_k`, as `batchK` computes them;
* **the identities as polynomials in `t`** (`polysK`): the tree, the root, the constraint quotient's identity
  (times `Z_bad`) with the Keccak copies `copy + slot(y) + END_BIT·[in_16]`, each heap block's leaf identity on
  `tablesKeccak`;
* **the heap read off `C1`** (`hdK`), **the constraint vectors** (`cvecK`), **`q_flock`** (`qfK`, `2^(11 + κ)`
  words), **the copies** (`CopiesK`: on every `SHA3` row, each lane column is `q_flock`'s port word, plus
  `END_BIT` for `in_16`).

Out of range (row counts above `2^h`) or for a Flock result not the main line's (`FlockGoodK`: a ring end, a point
of `11 + κ` coordinates) the model is degenerate, as `UniSound`'s.
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak Polynomial Finset

/-! ## Layouts, the values' count -/

/-- A commitment's stack layout at a shape on the Keccak VM (`layoutsOfK`, as `batchK` finds it). -/
def layoutOfK (S : Shape) (c : Commitment) : StackLayout := UniSound.layoutOf (layoutsOfK S) c

/-- **The batch's variables** on the Keccak VM: the longest stack's (`batchK`'s `vars`). -/
def batchVarsK (S : Shape) : ℕ := varsOf (layoutsOfK S)

/-- **Flock's result is the main line's** on the Keccak-f block: a ring end, a point of `q_flock`'s `11 + κ`
coordinates. -/
def FlockGoodK (κ : ℕ) (fl : List E × Flock.End) : Prop :=
  (∃ map target, fl.2 = .ring map target) ∧ fl.1.length = KeccakVm.kWords + κ

/-! ## A relation's difference on a stack -/

/-- **A term's weight at the batch's cube point `u`** on the Keccak VM (`weightAtK` of the term alone). -/
def termWK (L : StackLayout) (ringMap : Option (List E)) (V : ℕ) (column : Column) (pt : List E)
    (twist : ℕ) (u : ℕ) : E :=
  weightAtK ⟨[pt], [(column, 0, twist, 1)], 0, 1⟩ L (bitsE u V) ringMap

/-- **A relation's difference** on the Keccak VM: `Σ terms + value`, each term its coefficient times its weight's
inner product with the stack, at its merged point. -/
noncomputable def relDiffK (L : StackLayout) (ringMap : Option (List E)) (V : ℕ) (C : Stk)
    (mp : List E → List E) (r : Relation) : E :=
  (r.terms.map fun tm ↦ tm.coefficient *
    ∑ u ∈ range (2 ^ V), termWK L ringMap V tm.column (mp tm.point) tm.twist u * stE C L.vars u).sum +
    r.value

section Model

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant} (Fl : KFlockSound F κ v)

/-- **The relations at `t`** at a statement, round `0`'s challenges, Flock's transcript, `t` and the values: the
code-level link's (`mainRelsK`, then Flock's ring term, `flockClaimK`), so that the model's batch is the verifier's
by definition. -/
def relsAtK (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) : List Relation :=
  (flockClaimK (mainRelsK D.shape (publicWordsOf s.1.toList) (countsBits D.shape.heights s.2) (ch.take 4)
    (ch.getD 4 0) (ch.getD 5 0) t vals).1 (Fl.prog.out fd [])).1.toList

/-- The ring map of Flock's end (`flockClaimK`'s). -/
def ringMapAtK (fd : Done) : Option (List E) := (flockClaimK #[] (Fl.prog.out fd [])).2

open Classical in
/-- **The relations' differences** (`UniIdsK.diffs`): per commitment (`C1`, `C2`, the setup) its relations'
differences. -/
noncomputable def diffsK (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E)
    (vals : List E) : List (List E) :=
  if CountsFit D.shape s.2 ∧ FlockGoodK κ (Fl.prog.out fd []) then
    commitments.map fun c ↦ (mine (relsAtK D Fl s ch fd t vals) c).map
      (relDiffK (layoutOfK D.shape c) (ringMapAtK Fl fd) (batchVarsK D.shape) (stackForK D c1 c2 c)
        (mergedPoint (mine (relsAtK D Fl s ch fd t vals) c)))
  else [[1]]

/-- A commitment's combined claim. -/
def combAtK (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) (ρ : E) (c : Commitment) :
    Combined :=
  (combine (relsAtK D Fl s ch fd t vals) c ρ).getD zeroClaim

open Classical in
/-- **The batch** (`UniIdsK.prod`): `Σ_{k<3} λ^k W_k C_k` over the batch's variables, `W_k` the combined
claim's `weightAtK` at the cube's points, `C_k` the stack zero-extended. -/
noncomputable def prodK (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E)
    (vals : List E) (ρ l : E) : ProdSum :=
  if CountsFit D.shape s.2 ∧ FlockGoodK κ (Fl.prog.out fd []) then
    { vars := batchVarsK D.shape
      n := 3
      coef := fun k ↦ l ^ k
      A := fun k u ↦ weightAtK (combAtK D Fl s ch fd t vals ρ (cm k)) (layoutOfK D.shape (cm k))
            (bitsE u (batchVarsK D.shape)) (ringMapAtK Fl fd)
      B := fun k u ↦ stE (stackForK D c1 c2 (cm k)) (layoutOfK D.shape (cm k)).vars u }
  else { vars := batchVarsK D.shape, n := 0, coef := fun _ ↦ 0, A := fun _ _ ↦ 0, B := fun _ _ ↦ 0 }

open Classical in
/-- **The batch's target** (`UniIdsK.target`): `Σ_{k<3} λ^k v_k`. -/
noncomputable def targetK (s : USt) (_c1 : Stk) (ch : List E) (fd : Done) (_c2 : Stk) (t : E)
    (vals : List E) (ρ l : E) : E :=
  if CountsFit D.shape s.2 ∧ FlockGoodK κ (Fl.prog.out fd []) then
    ∑ k ∈ range 3, l ^ k * (combAtK D Fl s ch fd t vals ρ (cm k)).value
  else 1

end Model

/-! ## Columns as polynomials -/

section Polys

variable (S : Shape) (c1 c2 setup : Stk)

/-- A `C1` column at the digits. -/
noncomputable def c1PK (column : Column) : Polynomial E :=
  colPoly (layoutOfK S .c1) (batchVarsK S) c1 column digitP

/-- A `C2` column at a polynomial point. -/
noncomputable def c2PK (column : Column) (pt : ℕ → Polynomial E) : Polynomial E :=
  colPoly (layoutOfK S .c2) (batchVarsK S) c2 column pt

/-- A setup column at a polynomial point. -/
noncomputable def suPK (column : Column) (pt : ℕ → Polynomial E) : Polynomial E :=
  colPoly (layoutOfK S .setup) (batchVarsK S) setup column pt

/-- A quotient's polynomial from its chunks (`quotientTerms`). -/
noncomputable def quotPK (column : ℕ → Column) (sizes : List ℕ) : Polynomial E :=
  ((List.range sizes.length).map fun c ↦
    c2PK S c2 (column c) digitP * ((List.range c).map fun c' ↦ digitP (sizes.getD c' 0)).prod).sum

/-- `q_flock`'s word `slot` at `y(X)`: its claim at `(bits(slot), y(X))`, `11` slot bits (`weightAtK`). -/
noncomputable def slotPK (slot : ℕ) : Polynomial E :=
  colPoly (layoutOfK S .c1) (batchVarsK S) c1 .qflock fun l ↦
    if l < qflockRowBits then C (bitE slot l)
    else yP (coordinateFunctionals (S.heights.getD opBlake2s 0)) (l - qflockRowBits)

/-- **A table's constraints** `(M_i, W_i)` on the Keccak VM (`constraintRelationK`'s, in its order): `JUMP`'s two,
the counters' `z Π c + 1`, the `SHA3` lanes' copies `copy_c + slot(y) + offset`; `M_i` the lift to `V_{r_W}`. -/
noncomputable def tableConstraintsPK (tab : Table) : List (Polynomial E × Polynomial E) :=
  let o := tab.opcode
  let lift := liftP (S.heights.getD o 0) S.constraintVars
  let col (n : String) : Polynomial E := c1PK S c1 (.table o (colIdx tab.columns n))
  (if o = opJump then
    [(lift, col "b" + col "v_cond" * col "w"), (lift, col "v_cond" * (col "b" + 1))] else []) ++
  [(lift, c1PK S c1 (.inverse o) * (tab.countColumns.map fun c ↦ c1PK S c1 (.table o c)).prod + 1)] ++
  (if o = opBlake2s then (List.range tab.width).filterMap fun c ↦
    (keccakSlot (tab.columns.getD c "")).map fun slot ↦
      (lift, c1PK S c1 (.table o c) + slotPK S c1 slot + C (eK (keccakSlotOffset (tab.columns.getD c ""))))
   else [])

/-- The public lines' constraints: memory limb `k`'s cells `0, 1` on the line through them. -/
noncomputable def linesPK (pw : List E) : List (Polynomial E × Polynomial E) :=
  ((linesOf pw).zip (List.range 3)).map fun lk ↦
    (liftP 1 S.constraintVars, c1PK S c1 (.memory lk.2) + C lk.1.1 + X * C (lk.1.1 + lk.1.2))

/-- **The constraints** `(M_i, W_i)` on the Keccak VM (`constraintRelationK`'s, in its order). -/
noncomputable def constraintsPK (pw : List E) : List (Polynomial E × Polynomial E) :=
  tablesKeccak.flatMap (tableConstraintsPK S c1) ++ linesPK S c1 pw

/-- **The constraint quotient's identity** (step 5) on the Keccak VM, times `Z_bad`. -/
noncomputable def wPK (pw : List E) (gamma p0 : E) : Polynomial E :=
  zBad S p0 * ((((constraintsPK S c1 pw).zip (List.range (constraintsPK S c1 pw).length)).map
      fun mw ↦ C (gamma ^ mw.2) * mw.1.1 * mw.1.2).sum +
    quotPK S c2 Column.constraintQuotient (chunks (UniKeccak.Shape.constraintDegreeK S + 1)) * digitP S.constraintVars)

/-- **The tree's identity** (step 6). -/
noncomputable def treePK : Polynomial E :=
  digitP 1 * (c2PK S c2 .heap (fun l ↦ digitP (l + 1)) +
      c2PK S c2 .heap digitP * c2PK S c2 .heap (fun l ↦ if l = 0 then digitP 0 + 1 else digitP l)) +
    digitP S.heap.h * (c2PK S c2 (.treeQuotient 0) digitP +
      digitP S.heap.h * c2PK S c2 (.treeQuotient 1) digitP)

/-- **The root's identity**: `T(1) fp(init) + fp(fin)`, a constant. -/
noncomputable def rootPK (weights : Array E) (beta : E) : Polynomial E :=
  C (rootInit weights beta) * c2PK S c2 .heap (fun l ↦ if l = 0 then 1 else 0) + C (rootFin S weights beta)

/-- The memory's pull fingerprint as a polynomial. -/
noncomputable def memPullPK (weights : Array E) (beta : E) : Polynomial E :=
  C beta + C (weights.getD 0 0 * sepMem) + C (weights.getD 1 0) * suPK S setup .address digitP +
    C (weights.getD 2 0) * c1PK S c1 (.memory 3) +
    ((List.range 3).map fun k ↦ C (weights.getD (3 + k) 0) * c1PK S c1 (.memory k)).sum

/-- The bytecode's pull fingerprint as a polynomial. -/
noncomputable def bcPullPK (alphas : List E) (weights : Array E) (beta : E) : Polynomial E :=
  C beta + suPK S setup .bytecodeTuple (fun l ↦ if l < 4 then C (alphas.getD l 0) else digitP (l - 4)) +
    C (weights.getD 2 0) * c1PK S c1 .bytecodeFinal

/-- **A heap block's leaf identity** (step 6) on the Keccak VM's tables. -/
noncomputable def blockPK (rows : List ℕ) (alphas : List E) (beta : E) (b : Block) (i : ℕ) :
    Polynomial E :=
  let weights := eqKernel alphas
  let R := c2PK S c2 .heap (mixP b)
  let wr := digitP b.r
  let n := 2 ^ b.r
  match b.leaves with
  | .unused => R + 1
  | .memory =>
    R * memPullPK S c1 setup weights beta +
      quotPK S c2 (Column.leafQuotient i) (chunks (degree (2 * (n - 1)) n + 1)) * wr +
      (memPullPK S c1 setup weights beta + C (weights.getD 2 0) * (1 + c1PK S c1 (.memory 3)))
  | .bytecode =>
    R * bcPullPK S c1 setup alphas weights beta +
      quotPK S c2 (Column.leafQuotient i) (chunks (degree (2 * (n - 1)) n + 1)) * wr +
      (bcPullPK S c1 setup alphas weights beta + C (weights.getD 2 0) * (1 + c1PK S c1 .bytecodeFinal))
  | .table t =>
    let tab := tablesKeccak.getD t default
    let cols (c : ℕ) : Polynomial E := c1PK S c1 (.table tab.opcode c)
    let Z := zActP ((List.range (b.r + 1)).map fun j ↦ intBits (rows.getD t 0) j 1) b.r
    let d := degree (max (tableDegrees tab).1 (tableDegrees tab).2 * (n - 1) + (n - Shape.leastRows b.r)) n
    R * (pullP tab weights beta cols * wr + Z ^ 2) +
      quotPK S c2 (Column.leafQuotient i) (chunks (d + 1)) * (wr * Z) +
      pushP tab weights beta cols * wr + Z ^ 2

end Polys

/-- The setup stack, word by word (`stackForK`'s). -/
def setupStkK (D : KDeployment) : Stk := fun i ↦ (setupStackK D.prog D.shape).getD i 0

open Classical in
/-- **The identities as polynomials in `t`** (`UniIdsK.polys`): the tree, the root, the constraint quotient's
(times `Z_bad`), every heap block's leaf identity; a nonzero constant out of range. -/
noncomputable def polysK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) :
    List (Polynomial E) :=
  if CountsFit D.shape s.2 then
    [treePK D.shape c2, rootPK D.shape c2 (eqKernel (alphasOf ch)) (betaOf ch),
      wPK D.shape c1 c2 (publicWordsOf s.1.toList) (gammaOf ch) ((Fl.prog.out fd []).1.getD 0 0)] ++
    (D.shape.heap.blocks.zip (List.range D.shape.heap.blocks.length)).map fun bi ↦
      blockPK D.shape c1 c2 (setupStkK D) s.2 (alphasOf ch) (betaOf ch) bi.1 bi.2
  else [1]

/-- **The merge polynomial** (`UniIdsK.zb`): `Z_bad` at Flock's point's first coordinate. -/
noncomputable def zbK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (fd : Done) : Polynomial E :=
  zBad D.shape ((Fl.prog.out fd []).1.getD 0 0)

/-! ## The heap read off `C1`, the constraint vectors, `q_flock`, the copies -/

section Heap

variable (D : KDeployment) (c : Stk)

/-- **A `C1` column's value at row `x`** (basis `B` at `vars` variables), as `kvColumn` reads it. -/
def c1ValK (column : Column) (vars x : ℕ) : K := basisValue (c1Block (c1LayoutK D.shape) c column) vars x

/-- A setup column's value at row `x`. -/
def suValK (column : Column) (vars x : ℕ) : K :=
  basisValue (c1Block (setupLayout D.shape) (setupStkK D) column) vars x

/-- The setup's bytecode tuples' offset. -/
def tupleOffK : ℕ := (((setupLayout D.shape).limbs .bytecodeTuple).headD (0, 0, 0)).2.2

/-- The setup's bytecode slot `s` at instruction `x`. -/
def slotValK (s x : ℕ) : K :=
  basisValue (Array.ofFn (n := 2 ^ D.shape.logBytecode) fun k ↦ setupStkK D (tupleOffK D + s + 16 * k.val))
    D.shape.logBytecode x

/-- Table `o`'s row `x` of `C1`, as values. -/
def c1RowK (o x : ℕ) : ℕ → K := fun i ↦ c1ValK D c (.table o i) (D.shape.heights.getD o 0) x

/-- A table's block of leaves on `C1` (the Keccak VM's tables): its active rows with their flushes' tuples. -/
def tableBlockKK (rows : List ℕ) (b : Block) (o : ℕ) : Heap.LeafBlock (Vector K 16) where
  r := b.r
  push x := if isActive x (rows.getD o 0) b.r then
      (tablesKeccak.getD o default).flushes.push.map fun tup ↦ tupleK tup (c1RowK D c o x) else []
  pull x := if isActive x (rows.getD o 0) b.r then
      (tablesKeccak.getD o default).flushes.pull.map fun tup ↦ tupleK tup (c1RowK D c o x) else []

/-- The memory's tuple of cell `x` with count `cnt`. -/
def memTupleKK (cnt : K) (x : ℕ) : Vector K 16 :=
  Vector.ofFn fun s ↦
    if s.val = 0 then toK sepMem
    else if s.val = 1 then suValK D .address D.shape.logMemory x
    else if s.val = 2 then cnt
    else if s.val < 6 then c1ValK D c (.memory (s.val - 3)) D.shape.logMemory x
    else 0

/-- The bytecode's tuple of instruction `x`: the setup's slots, the count added in slot `2`. -/
def bcTupleKK (cnt : K) (x : ℕ) : Vector K 16 :=
  Vector.ofFn fun s ↦ slotValK D s.val x + if s.val = 2 then cnt else 0

/-- **A heap block's leaves read off `C1`.** -/
def blockKK (rows : List ℕ) (b : Block) : Heap.LeafBlock (Vector K 16) :=
  match b.leaves with
  | .memory => Heap.LeafBlock.pair b.r (memTupleKK D c 1)
      (fun x ↦ memTupleKK D c (c1ValK D c (.memory 3) D.shape.logMemory x) x)
  | .bytecode => Heap.LeafBlock.pair b.r (bcTupleKK D 1)
      (fun x ↦ bcTupleKK D (c1ValK D c .bytecodeFinal D.shape.logBytecode x) x)
  | .table t => tableBlockKK D c rows b t
  | .unused => Heap.LeafBlock.unused b.r

/-- The state boundary's pull `(SEP_STATE, g^(2^lb − 1), 1)`. -/
def finKK : Vector K 16 :=
  Vector.ofFn fun s ↦ if s.val = 1 then toK (UniStatement.gpow (2 ^ D.shape.logBytecode - 1))
    else if s.val < 3 then 1 else 0

/-- **The heap the verifier reads off `C1`** (`BusModelK.hd`). -/
def hdK (s : USt) : Heap.HeapData :=
  ⟨D.shape.heap.h, D.shape.heap.blocks.map (blockKK D c s.2), initK, finKK D⟩

open Classical in
/-- **The constraint vectors** (`BusModelK.cvec`): row `x`'s `M_i(ω_x) W_i(ω_x)`; a `1` out of range. -/
noncomputable def cvecK (s : USt) (x : ℕ) : List E :=
  if CountsFit D.shape s.2 then
    (constraintsPK D.shape c (publicWordsOf s.1.toList)).map fun mw ↦ (mw.1 * mw.2).eval (pointE x)
  else [1]

/-- `q_flock`'s offset in `C1`. -/
def qfOffK : ℕ := (((c1LayoutK D.shape).limbs .qflock).headD (0, 0, 0)).2.2

/-- **`C1`'s column `q_flock`** (`UniIdsK.qf`): `2^(11 + κ)` words from its offset. -/
def qfK (κ : ℕ) : LeanVM.Protocol.Column (KeccakVm.kWords + κ) :=
  ⟨Vector.ofFn fun x ↦ c (qfOffK D + x.val)⟩

/-- **The lanes' copies hold** (`BusModelK.Copies`): the counts in range, and on every `SHA3` row `x` of `C1`
each lane column is `q_flock`'s port word `keccakSlot` of block `x`, plus its offset (`END_BIT` for `in_16`). -/
def CopiesK (s : USt) : Prop :=
  CountsFit D.shape s.2 ∧
    ∀ x < 2 ^ D.shape.heights.getD opBlake2s 0, ∀ col slot,
      keccakSlot (sha3Columns.getD col "") = some slot →
        c1ValK D c (.table opBlake2s col) (D.shape.heights.getD opBlake2s 0) x =
          c (qfOffK D + slot + 2 ^ qflockRowBits * x) + toK (eK (keccakSlotOffset (sha3Columns.getD col "")))

end Heap

end UniKeccakSound.Ids
