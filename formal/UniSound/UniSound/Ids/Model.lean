-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The identities are
-- `docs/leanvm/univariate/SPEC.md` §5–§6 and `formal/UniStatement`'s `constraintRelation`,
-- `heapRelations`, `batch`.
import UniSound.Ids.Rels
import UniSound.Mle
import UniStatement.FormPoly

/-!
# The identity model's data

What `BusModel` and `UniIdsRest` are made of, for a deployment `D` and Flock's phase `Fl` (the proofs
are elsewhere):

* **the relations' differences** (`diffsOf`): each commitment's relations (`relsOf`, in `combine`'s
  order), each evaluated on its candidate stack the way the batch reads it — a term's weight on the
  batch's cube (`termW`, `weightAt` of the term alone) at the point `combine` merges its point into
  (`mergedPoint`), against the stack zero-extended (`stE`) — plus its value; and the pending matrices'
  sum plus its claim;
* **the batch** (`prodOf`, `targetOf`): `Σ_{k<3} λ^k W_k C_k + λ³ G L` over the batch's `V`
  variables, `W_k` the combined claim's weight (`weightAt`) at the cube's points, and its target
  `Σ_k λ^k v_k + λ³ claim`, as `batch` computes them;
* **the identities as polynomials in `t`** (`polysOf`): the tree, the root, the constraint quotient's
  identity (times `Z_bad`, below), and each heap block's leaf identity, each read off the committed
  columns by `colPoly` (a column's claim at a polynomial point);
* **the heap read off `C1`** (`hdOf`, `Heap.HeapData`): the memory's, the bytecode's and each table's
  blocks (a table's active rows, `isActive`, with their flushes' tuples, `tupleK` of the forms on the
  row's values, `c1Val`), the unused blocks, the state boundary;
* **the constraint vectors** (`cvecOf`): each row's `M_i(ω_x) W_i(ω_x)`, the constraint quotient's
  numerator's terms on the domain.

**Out of range** (a row count above `2^h`, which the verifier's range checks reject), the model is
degenerate: the constraint vectors hold a `1` and the identities a nonzero constant, so the states are
false from round `0` on. Likewise, if Flock's result is not the main line's (a ring end, its point of
`8 + κ` coordinates, its pending rounds within the batch's), the differences are a nonzero constant.

**`Z_bad`.** `combine` merges a point that is a prefix of a longer one into that one (a column reads
only as many of its point's coordinates as it has variables). `q_flock`'s slot view reads its whole
point, `8 + |y|` coordinates (`weightAt`'s `.qflockSlot` case): if `y(t)` were a strict prefix of a
longer `C1` point (`w(t)` cut at `21`, Flock's point), the batch would weigh the copies' slots wrongly.
Every longer `C1` point starts with `t` or with Flock's first coordinate, so this needs
`y_0(t) ∈ {t, p_0}`, the roots of `Z_bad = (y_0 + X)(y_0 + p_0)`; the constraint identity is stated
times `Z_bad`, which costs `2^(h_B)` in its degree and nothing in the polynomial's vanishing.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Polynomial Finset

/-! ## Layouts, challenges, the inputs of the relations -/

/-- A commitment's stack layout at a shape (`layoutsOf`, as `batch` finds it). -/
def layoutOf (S : Shape) (c : Commitment) : StackLayout :=
  (((layoutsOf S).find? (·.1 == c)).map (·.2)).getD default

/-- The tuple weights' point `α`, as the verifier samples it (round `0`'s first four challenges). -/
def alphasOf (ch : List E) : List E := (List.range 4).map fun i ↦ ch.getD i 0

/-- `β`, round `0`'s fifth challenge. -/
def betaOf (ch : List E) : E := ch.getD 4 0

/-- `γ`, round `0`'s sixth challenge. -/
def gammaOf (ch : List E) : E := ch.getD 5 0

/-- Each table's count bits `0..=r` (`countBits`). -/
def countsOf (S : Shape) (rows : List ℕ) : List (List E) :=
  (rows.zip S.heights).map fun p ↦ (List.range (p.2 + 1)).map fun b ↦ intBits p.1 b 1

/-- Flock's result: its point, its end, its pending reduction. -/
abbrev FlockOut := List E × Option Flock.End × Flock.Pending

/-- **The counts the verifier accepts** (`readCounts`' range checks): six, each at most `2^h`. -/
def CountsFit (S : Shape) (rows : List ℕ) : Prop :=
  rows.length = 6 ∧ ∀ j < 6, rows.getD j 0 ≤ 2 ^ S.heights.getD j 0

/-- **Flock's result is the main line's**: a ring end, a point of `q_flock`'s `8 + κ` coordinates, the
pending reduction's rounds within the batch's `V`. -/
def FlockGood (κ V : ℕ) (fl : FlockOut) : Prop :=
  (∃ map target, fl.2.1 = some (.ring map target)) ∧ fl.1.length = 8 + κ ∧ fl.2.2.rounds ≤ V

/-! ## A relation's difference on a stack -/

/-- **A term's weight at the batch's cube point `u`** (`weightAt` of the term alone, coefficient `1`). -/
def termW (L : StackLayout) (ringMap : Option (List E)) (V : ℕ) (column : Column) (pt : List E)
    (twist : ℕ) (u : ℕ) : E :=
  weightAt ⟨[pt], [(column, 0, twist, 1)], 0, 1⟩ L (bitsE u V) ringMap

/-- **A stack, zero-extended** past its `2^vars` words (the batch's `C_k`). -/
def stE (C : Stk) (vars u : ℕ) : E := if u < 2 ^ vars then ofK (C u) else 0

/-- `combine`'s points: every term's point, each once, in order of first use. -/
def combinePoints (rels : List Relation) : Array (List E) :=
  rels.foldl (fun points r ↦ r.terms.foldl (fun points tm ↦
    match points.findIdx? (· == tm.point) with
    | some _ => points
    | none => points.push tm.point) points) #[]

/-- **The point `combine` reads a term at `p` with**: of the points having `p` as a prefix, the longest
(`longestOf`). -/
def mergedPoint (rels : List Relation) (p : List E) : List E :=
  (combinePoints rels).getD
    (longestOf (combinePoints rels) (((combinePoints rels).findIdx? (· == p)).getD 0)) []

/-- **A relation's difference**: `Σ terms + value`, each term its coefficient times its weight's inner
product with the stack, at its merged point. -/
noncomputable def relDiff (L : StackLayout) (ringMap : Option (List E)) (V : ℕ) (C : Stk)
    (mp : List E → List E) (r : Relation) : E :=
  (r.terms.map fun tm ↦ tm.coefficient *
    ∑ u ∈ range (2 ^ V), termW L ringMap V tm.column (mp tm.point) tm.twist u * stE C L.vars u).sum +
    r.value

section Model

variable (D : Deployment) {κ : ℕ}

/-- The commitment of the batch's `k`-th product. -/
def cm (k : ℕ) : Commitment := commitments.getD k .c1

/-- The empty claim (a commitment with no relation). -/
def zeroClaim : Combined := ⟨[], [], 0, 0⟩

end Model

/-! ## Columns as polynomials -/

/-- `weightAt`'s limb scale: `1, y, y²`. -/
def limbScale (limb : ℕ) : E := if limb = 0 then 1 else limbBasis.getD limb 0

/-- The aligned block a selector picks: the offset's bits from `v` to `V`. -/
def blockBase (off v V : ℕ) : ℕ := off % 2 ^ V / 2 ^ v * 2 ^ v

/-- **A column's polynomial on a stack**, its claim at the polynomial point `pt`: limb by limb, the
block's words (zero-extended) at the multilinear point `pt`. -/
noncomputable def colPoly (L : StackLayout) (V : ℕ) (C : Stk) (column : Column)
    (pt : ℕ → Polynomial E) : Polynomial E :=
  ((L.limbs column).map fun b ↦
    Polynomial.C (limbScale b.1) * mlP (fun x ↦ stE C L.vars (blockBase b.2.2 b.2.1 V + x)) b.2.1 pt).sum

/-- A form as a polynomial in its columns' polynomials (monomials of degree at most two, as
`linearise` reads them). -/
noncomputable def formP (f : Form) (cols : ℕ → Polynomial E) : Polynomial E :=
  (f.map fun mc ↦ match mc.1 with
    | [] => C mc.2
    | [i] => C mc.2 * cols i
    | [i, j] => C mc.2 * cols i * cols j
    | _ => 0).sum

/-- A tuple's fingerprint without `β`: `Σ_s eq(α, s) τ_s`. -/
noncomputable def tupleP (tuple : List Form) (weights : Array E) (cols : ℕ → Polynomial E) :
    Polynomial E :=
  ((tuple.zip (List.range tuple.length)).map fun p ↦ C (weights.getD p.2 0) * formP p.1 cols).sum

/-- A table's pull product `Π_j (β + fp_j)`. -/
noncomputable def pullP (tab : Table) (weights : Array E) (beta : E) (cols : ℕ → Polynomial E) :
    Polynomial E :=
  ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ C beta + tupleP fl.1 weights cols).prod

/-- A table's push product `Π_j (β + fp'_j)`. -/
noncomputable def pushP (tab : Table) (weights : Array E) (beta : E) (cols : ℕ → Polynomial E) :
    Polynomial E :=
  ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ C beta + tupleP fl.2 weights cols).prod

/-- **`Z_act` as a polynomial** (`activeVanishingFromBits`, F1b). -/
noncomputable def zActP (bits : List E) (r : ℕ) : Polynomial E :=
  (List.range r).foldl (fun prod b ↦
    prod * (1 + C (bits.getD b 0) * (digitP b + C (cosetOffset r b + 1))))
    (1 + C (bits.getD r 0) * (digitP r + 1))

/-- `w_m / w_r = Π_{j=r}^{m−1} (w_j + 1)` (`vanishingRatio`). -/
noncomputable def liftP (r m : ℕ) : Polynomial E :=
  ((List.range' r (m - r)).map fun j ↦ digitP j + 1).prod

/-- The coordinate functional `y_l(X) = Σ_m a_{l,m} X^(2^m)` (`coordinatesAt`). -/
noncomputable def yP (a : Array (Array K)) (l : ℕ) : Polynomial E :=
  ((List.range a.size).map fun m ↦ C (ofK ((a.getD l #[]).getD m 0)) * X ^ (2 ^ m)).sum

section Polys

variable (S : Shape) (c1 c2 setup : Stk)

/-- The public lines (`constraintRelation`): limb `k`'s cells `0, 1`. -/
def linesOf (pw : List E) : List (E × E) :=
  [(pw.getD 0 0, pw.getD 2 0), (pw.getD 1 0, pw.getD 3 0), (0, 0)]

/-- **`Z_bad`**: `(y_0 + X)(y_0 + p_0)`, `p_0` Flock's point's first coordinate. -/
noncomputable def zBad (p0 : E) : Polynomial E :=
  (yP (coordinateFunctionals (S.heights.getD opSha3 0)) 0 + X) *
    (yP (coordinateFunctionals (S.heights.getD opSha3 0)) 0 + C p0)

/-- The state boundary's push and pull fingerprints (`heapRelations`' root). -/
def rootInit (weights : Array E) (beta : E) : E :=
  beta + weights.getD 0 0 * sepState + weights.getD 1 0 + weights.getD 2 0

def rootFin (S : Shape) (weights : Array E) (beta : E) : E :=
  beta + weights.getD 0 0 * sepState + weights.getD 1 0 * UniStatement.gpow (2 ^ S.logBytecode - 1) +
    weights.getD 2 0

/-- A heap block's mixed point (SPEC §2's restriction): `w_l + ω_{pos >> l}` below `r`, `ω_{pos >> l}`
above. -/
noncomputable def mixP (b : Block) (l : ℕ) : Polynomial E :=
  if l < b.r then digitP l + C (pointE (b.position >>> l)) else C (pointE (b.position >>> l))

end Polys

/-! ## The heap read off `C1`, the constraint vectors -/

section Heap

variable (D : Deployment) (c : Stk)

/-- The state boundary's push `(SEP_STATE, 1, 1)`. -/
def initK : Vector K 16 := Vector.ofFn fun s ↦ if s.val < 3 then 1 else 0

end Heap

end UniSound.Ids
