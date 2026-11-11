-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The reduction of `crates/membership/quotient/src/protocol.rs` (`docs/membership/PROTOCOL.md`) as polynomials, in
-- the style of `formal/QuotientSecurity/Protocol.lean` (adapted from leanVM, branch PCS-openings-aggregation,
-- commit 651453c6, `formal/quotient`), whose row geometry (`shift`, `digit`, `rowPoly`) it reuses.
import QuotientSecurity.Protocol
import Mathlib.LinearAlgebra.Lagrange

/-!
# The membership reduction (`pcs-quotient-kc3`), as polynomials

The protocol of `docs/membership/PROTOCOL.md` with its tables read as the polynomials they hold (F1 with ideal
commitments): a claim on a table is an evaluation of those polynomials. This file defines the parameters (a
circuit's geometry, wiring, pins and random rows), the two messages, the relation, the identity and the
verifier's decision as predicates on the transcript; `Rounds.lean` bounds each challenge.

* **The circuit**: cells `(x, c)`, `x ∈ T` a row's first point, `c` a role, at the point `x + shift θ c`; the gate
  `V = Y + C + X·C` (`gate`); the wiring `σ` (`sigmaPoly` carries it); eleven **pins**, the `C` cells of the anchor
  rows `pins k`, whose values the statement gives; the **random rows**, whose cells the pole condition leaves out.
* **The first message**: the four row polynomials `g` (`QuotientSecurity.Params.Witness`); the cells'
  polynomial is `cellPoly g 0 = Σ_j digit_j · g_j ∘ rowPoly`, the cell of role `c` of row `x` its value at
  `x + shift θ c`.
* **The second message** (`TMsg`): the quotient table's four polynomials, `q = A₀ + ζ A₁` and `P = x h = B₀ + ζ B₁`,
  `ζ = Z · X`.
* **The identity** (`identity`): `X Z q + d d' P + X (d + d' + μ Z g)`, `Z g = (Z / Z_R) gate + (Z / Z_P)(w + v)`,
  `v` the pins' interpolant; the second message is consistent when it is the zero polynomial.
* **The verifier's decision** (`Accepts`): the witness claim on the row polynomials' conic, the wiring claim, the
  denominators nonzero, and the copy claim at `t`, the identity's combination of `q` and `P`.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Kc3

open QuotientSecurity QuotientSecurity.Params

variable {F : Type*} [Field F]

/-- **The gate** `V + Y + C + X·C` of a row's cells `(X, Y, C, V)` (`protocol.rs`'s `gate`): on bits it says
`V = Y ⊕ (C ∧ ¬X)`, Keccak's χ. Of degree 2. -/
def gate {R : Type*} [CommRing R] (x y c v : R) : R := v + y + c + x * c

theorem gate_eval (a b c d : F[X]) (t : F) :
    (gate a b c d).eval t = gate (a.eval t) (b.eval t) (c.eval t) (d.eval t) := by
  simp [gate]

/-- The pins: the anchor rows `0 … 10`. -/
abbrev pinCount : ℕ := 11

/-- **The fixed data of the protocol**: a circuit's geometry (`QuotientSecurity.Params`'s: rows, roles, the
vanishing polynomials of the cells and of the rows' first cells, the wiring), its pins and random rows, and the
two properties of the cells the soundness argument uses: a polynomial of degree at most `n − 2` sums to zero over
the cells (they are an `F₂`-subspace), and the pole condition (`Circuit::errors_have_their_own_poles`). -/
structure Params (F : Type*) [Field F] [DecidableEq F] where
  θ : F
  hθ : θ * θ + θ + 1 = 0
  /-- The rows' first (`X`) cells. -/
  T : Finset F
  /-- Cells are distinct points. -/
  hT : ∀ x ∈ T, ∀ y ∈ T, ∀ c d : Fin 4, x + shift θ c = y + shift θ d → x = y ∧ c = d
  /-- The wiring, and the polynomial that carries it. -/
  σ : Equiv.Perm (T × Fin 4)
  sigmaPoly : F[X]
  hσ : ∀ i : T × Fin 4, sigmaPoly.eval (i.1.1 + shift θ i.2) = (σ i).1.1 + shift θ (σ i).2
  hσdeg : sigmaPoly.natDegree < 4 * T.card
  /-- The anchor rows, whose `C` cells are pinned. -/
  pins : Fin pinCount ↪ T
  /-- The random rows. -/
  random : Finset T
  /-- **The cells sum low-degree polynomials to zero**: `Σ_cells p = 0` when `deg p ≤ n − 2`. -/
  hSum : ∀ p : F[X], p.natDegree + 2 ≤ 4 * T.card → ∑ i : T × Fin 4, p.eval (i.1.1 + shift θ i.2) = 0

variable [DecidableEq F] (P : Params F)

namespace Params

/-- The point of a cell. -/
def pt (i : P.T × Fin 4) : F := i.1.1 + shift P.θ i.2

theorem pt_injective : Function.Injective P.pt := by
  rintro ⟨⟨x, hx⟩, c⟩ ⟨⟨y, hy⟩, d⟩ h
  obtain ⟨rfl, rfl⟩ := P.hT x hx y hy c d h
  rfl

/-- The number of cells, `n`. -/
abbrev nCells : ℕ := Fintype.card (P.T × Fin 4)

/-- `Z`: the cells' vanishing polynomial, monic of degree `n`. -/
noncomputable def vCells : F[X] := ∏ i : P.T × Fin 4, (X - C (P.pt i))

/-- `Z_R`: the rows' first cells' vanishing polynomial. -/
noncomputable def vRows : F[X] := ∏ x : P.T, (X - C (x : F))

/-- `Z / Z_R`: the cells but the rows' first. -/
noncomputable def cofRows : F[X] := ∏ i ∈ (univ.filter fun i : P.T × Fin 4 => i.2 ≠ 0), (X - C (P.pt i))

/-- The pinned cell of anchor `k`: its `C` cell (role `2`). -/
def pinCell (k : Fin pinCount) : P.T × Fin 4 := (P.pins k, 2)

/-- The pinned cells' points `p_k`. -/
def pinPt (k : Fin pinCount) : F := P.pt (P.pinCell k)

/-- `Z_P`: the pinned cells' vanishing polynomial. -/
noncomputable def vPins : F[X] := ∏ k : Fin pinCount, (X - C (P.pinPt k))

/-- `Z / Z_P`: the cells but the pinned ones. -/
noncomputable def cofPins : F[X] :=
  ∏ i ∈ (univ.filter fun i : P.T × Fin 4 => ∀ k, i ≠ P.pinCell k), (X - C (P.pt i))

/-- **The cells an error can sit on** (`Circuit::errors_have_their_own_poles`): a row's first cell, a pinned cell,
or a cell of a random row. -/
def ErrorCell (i : P.T × Fin 4) : Prop := i.2 = 0 ∨ (∃ k, i = P.pinCell k) ∨ i.1 ∈ P.random

/-- **The pole condition** (`Circuit::errors_have_their_own_poles`): every cycle of the wiring but a lone cell's
holds a cell that is not an error cell. -/
def PoleCondition : Prop := ∀ i, P.σ i ≠ i → ∃ k : ℕ, ¬ P.ErrorCell ((P.σ ^ k) i)

/-- The statement: the eleven pinned values (the eight public words, then `0`, `1`, `3`). -/
abbrev Stmt (F : Type*) := Fin pinCount → F

/-- `v`: the pinned values' interpolant on the pins. -/
noncomputable def pinPoly (stmt : Stmt F) : F[X] := Lagrange.interpolate univ P.pinPt stmt

/-- **The relation proved**: cells that satisfy every gate, every copy, and every pin. -/
def Sat (stmt : Stmt F) (w : P.T × Fin 4 → F) : Prop :=
  (∀ x : P.T, gate (w (x, 0)) (w (x, 1)) (w (x, 2)) (w (x, 3)) = 0) ∧
    (∀ i, w (P.σ i) = w i) ∧ ∀ k, w (P.pinCell k) = stmt k

/-- The polynomial of role `c` (`QuotientSecurity.Params.cellPoly`): at a row's first cell, the value of the cell
of role `c` of its row. -/
noncomputable def cellPoly (g : Witness F) (c : Fin 4) : F[X] :=
  ∑ j, (digit j).comp (X + C (shift P.θ c)) * (g j).comp rowPoly

/-- The cells a first message holds. -/
noncomputable def cells (g : Witness F) (i : P.T × Fin 4) : F := (P.cellPoly g i.2).eval i.1.1

/-- **The second message**: the quotient table's four polynomials, `q = A₀ + ζ A₁` (kind `0`) and
`P = x h = B₀ + ζ B₁` (kind `1`), `ζ = Z · X`. -/
structure TMsg (F : Type*) [Field F] where
  A₀ : F[X]
  A₁ : F[X]
  B₀ : F[X]
  B₁ : F[X]

/-- `ζ = Z · X`. -/
noncomputable def zeta : F[X] := P.vCells * X

/-- The quotient `q = A₀ + ζ A₁`. -/
noncomputable def qPoly (R : TMsg F) : F[X] := R.A₀ + P.zeta * R.A₁

/-- `P = x h = B₀ + ζ B₁`. -/
noncomputable def xhPoly (R : TMsg F) : F[X] := R.B₀ + P.zeta * R.B₁

/-- The two denominators as polynomials: `d = α + w + β X`, `d' = α + w + β σ`. -/
noncomputable def dPoly (g : Witness F) (α β : F) : F[X] := C α + P.cellPoly g 0 + C β * X

noncomputable def dNextPoly (g : Witness F) (α β : F) : F[X] := C α + P.cellPoly g 0 + C β * P.sigmaPoly

/-- The gate on the cells' polynomials, at a row's first cell. -/
noncomputable def gatePoly (g : Witness F) : F[X] :=
  gate (P.cellPoly g 0) (P.cellPoly g 1) (P.cellPoly g 2) (P.cellPoly g 3)

/-- **`Z g`**: `(Z / Z_R) gate + (Z / Z_P)(w + v)`, a polynomial. -/
noncomputable def zgPoly (stmt : Stmt F) (g : Witness F) : F[X] :=
  P.cofRows * P.gatePoly g + P.cofPins * (P.cellPoly g 0 + P.pinPoly stmt)

/-- **The identity's right side** `R = d + d' + μ Z g`. -/
noncomputable def rhsPoly (stmt : Stmt F) (g : Witness F) (α β μ : F) : F[X] :=
  P.dPoly g α β + P.dNextPoly g α β + C μ * P.zgPoly stmt g

/-- **The identity** `I = X Z q + d d' P + X R` (characteristic two), the layout's: zero exactly when the second
message is consistent. -/
noncomputable def identity (stmt : Stmt F) (g : Witness F) (R : TMsg F) (α β μ : F) : F[X] :=
  X * P.vCells * P.qPoly R + P.dPoly g α β * P.dNextPoly g α β * P.xhPoly R + X * P.rhsPoly stmt g α β μ

/-- The second message is consistent with the first: the identity holds as polynomials. -/
def Consistent (stmt : Stmt F) (g : Witness F) (R : TMsg F) (α β μ : F) : Prop :=
  P.identity stmt g R α β μ = 0

/-- The same at one point. -/
def ConsistentAt (stmt : Stmt F) (g : Witness F) (R : TMsg F) (α β μ t : F) : Prop :=
  (P.identity stmt g R α β μ).eval t = 0

/-! ### The verifier's decision -/

/-- The four cells of the row of `t` from the row polynomials' values `a` at `t` (`row_values`). -/
noncomputable def cellAt (a : Fin 4 → F) (t : F) (c : Fin 4) : F :=
  ∑ j, (digit j).eval (t + shift P.θ c) * a j

/-- **The three values the verifier reads** of a row (`row_values`): `X`, `C`, `V + Y`. -/
noncomputable def rowValues (a : Fin 4 → F) (t : F) : Fin 3 → F :=
  ![P.cellAt a t 0, P.cellAt a t 2, P.cellAt a t 3 + P.cellAt a t 1]

/-- `witness_conic` (`protocol.rs`): `(a, b)`, the witness claim's row point `z₁ = a / (a + b)`, `ω = t² + t`. -/
def conic (θ t ρ : F) : F × F :=
  ((t + (t * t + t) * θ) * (1 + ρ) + ρ, θ * (1 + ρ))

/-- The row point's weights `e = (1 + z₀, z₀) ⊗ (1 + z₁, z₁)`, `z₀ = ρ` (`Tables.lean`'s order: index
`j = j₀ + 2 j₁`). -/
def rowWeights (ρ z₁ : F) : Fin 4 → F := ![(1 + ρ) * (1 + z₁), ρ * (1 + z₁), (1 + ρ) * z₁, ρ * z₁]

/-- `witness_weights` (`protocol.rs`): `λ` with `e = λ₀ X + λ₁ C + λ₂ (V + Y)` as linear forms of the row
polynomials' values. -/
def conicWeights (θ t ρ z₁ : F) : Fin 3 → F :=
  let ω := t * t + t
  let e00 := (1 + ρ) * (1 + z₁)
  let e01 := (1 + ρ) * z₁
  let e11 := ρ * z₁
  let k3 := t + θ * ω + θ + 1
  let l1 := e11 + t * ω * e00 + k3 * (e01 + ω * e00)
  ![e00 + l1, l1, e01 + ω * e00 + l1]

/-- **The verifier's decision** at the challenges `α, β, μ, t, ρ` on the values `v = (X, C, V + Y)` and `s`
(`next`), its three claims checked against what the messages hold: the witness claim on the conic, the wiring
claim, the nonzero denominators, and the copy claim. -/
def Accepts (stmt : Stmt F) (g : Witness F) (R : TMsg F) (α β μ t : F) (v : Fin 3 → F) (s ρ : F) : Prop :=
  let x := v 0
  let d := α + x + β * t
  let d' := α + x + β * s
  let z := P.vCells.eval t
  let ζ := z * t
  let ab := conic P.θ t ρ
  let z₁ := ab.1 / (ab.1 + ab.2)
  let gt := gate x 0 (v 1) (v 2) / P.vRows.eval t + (x + (P.pinPoly stmt).eval t) / P.vPins.eval t
  let κ := d * d' / (ζ + d * d')
  -- The witness claim, the wiring claim, the nonzero denominators, the copy claim.
  (∑ j, rowWeights ρ z₁ j * ((g j).comp rowPoly).eval t = ∑ k, conicWeights P.θ t ρ z₁ k * v k) ∧
    P.sigmaPoly.eval t = s ∧
    ab.1 + ab.2 ≠ 0 ∧ ζ + d * d' ≠ 0 ∧ P.vRows.eval t ≠ 0 ∧ P.vPins.eval t ≠ 0 ∧
    (1 + κ) * (P.qPoly R).eval t + κ * (P.xhPoly R).eval t =
      t * (d + d' + μ * z * gt) / (ζ + d * d')

end Params

/-! ### The messages' bounds -/

/-- The degree bounds of the messages: the row polynomials below `n / 4`, the table's four polynomials below
`n` (the committed tables' sizes). -/
def Params.Msg₁ : Type _ := { g : Witness F // ∀ j, (g j).natDegree < P.T.card }

def Params.Msg₂ : Type _ :=
  { R : Params.TMsg F // R.A₀.natDegree < P.nCells ∧ R.A₁.natDegree < P.nCells ∧ R.B₀.natDegree < P.nCells ∧
      R.B₁.natDegree < P.nCells }

/-! ### The states of the proof, and the rounds' errors -/

namespace Params

variable {P}

/-- The states after the first message, the first challenge, the second message, `t`, and `ρ`: a state is true
when the prover can still win (`QuotientSecurity/Spec.lean`'s, for this protocol). -/
def State₁ (stmt : Stmt F) (g : P.Msg₁) : Prop := P.Sat stmt (P.cells g.1)

def State₂ (stmt : Stmt F) (g : P.Msg₁) (c : F × F × F) : Prop :=
  State₁ stmt g ∨ ∃ R : P.Msg₂, P.Consistent stmt g.1 R.1 c.1 c.2.1 c.2.2

def State₃ (stmt : Stmt F) (g : P.Msg₁) (c : F × F × F) (R : P.Msg₂) : Prop :=
  State₁ stmt g ∨ P.Consistent stmt g.1 R.1 c.1 c.2.1 c.2.2

def State₄ (stmt : Stmt F) (g : P.Msg₁) (c : F × F × F) (R : P.Msg₂) (t : F) : Prop :=
  State₃ stmt g c R ∨ P.ConsistentAt stmt g.1 R.1 c.1 c.2.1 c.2.2 t

def State₆ (stmt : Stmt F) (g : P.Msg₁) (c : F × F × F) (R : P.Msg₂) (t : F) (v : (Fin 3 → F) × F)
    (ρ : F) : Prop :=
  State₄ stmt g c R t ∨ P.Accepts stmt g.1 R.1 c.1 c.2.1 c.2.2 t v.1 v.2 ρ

variable (P)

/-- The first challenge's count factor: at most `E1 · q²` of the `q³` triples `(α, β, μ)` admit a consistent
second message when the first message's cells fail the relation (`Rounds.lean`). -/
def E1 : ℕ := 8 * P.nCells

/-- The second challenge's: the identity's degree, at most `4 n`. -/
def D2 : ℕ := 4 * P.nCells

/-- **The rounds' error**: each challenge turns a lost state into a won one with probability at most
`E1 / q` (`E1 ≥ D2 ≥ 3`). -/
noncomputable def roundError [Fintype F] : ENNReal := (P.E1 : ENNReal) / (Fintype.card F : ENNReal)

end Params

end Kc3
