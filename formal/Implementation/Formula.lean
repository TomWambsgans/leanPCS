-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import PcsQuotient.Reduction

/-!
# The reduction's formulas, named

`PcsQuotient.claimsAt` (the Statement's transcription of `quotient::protocol::reduce` after its
transcript reads) at `2^22` rows, its local definitions as top-level ones over the leaves (`Vals`:
the statement, the challenges `α, β, γ, t, ρ`, the values `a`, `next`, `qValue`, `gValue`), so that the
graph's nodes can be stated equal to them one by one. `claimsAt_eq`: `claimsAt` is these definitions,
by unfolding (`rfl`).
-/

set_option linter.unusedVariables false

namespace Implementation.Formula

open LeanVM.Parameters LeanVM.Protocol PcsQuotient PcsQuotient.Domain

/-- The leaves of the reduction. -/
structure Vals where
  stmt : Statement
  α : E
  β : E
  γ : E
  t : E
  ρ : E
  a : Vector E 4
  next : E
  qValue : E
  gValue : E

variable (I : Vals)

/-- `m = 24`. -/
abbrev m : ℕ := cellVars logRows

def w : List E := (List.range (m + 1)).foldl (fun ws _ ↦ ws ++ [ws.getLastD I.t * ws.getLastD I.t +
    ws.getLastD I.t]) [I.t]

def wAt (k : ℕ) : E := (w I).getD k 0

def cell (shift : K) (second : Bool) : E :=
  let first := I.t + ofK shift
  let second := if second then wAt I 1 + 1 else wAt I 1
  I.a[0] + first * I.a[1] + second * (I.a[2] + first * I.a[3])

def x : E := cell I 0 false
def y : E := cell I 1 false
def c : E := cell I (betaAt 1) true
def v : E := cell I (betaAt 1 + 1) true
def gate : E := v I + x I + c I + y I * c I

def gammas : List E := [I.γ, I.γ * I.γ, (I.γ * I.γ) * (I.γ * I.γ)]

def outside : E := (List.range' region (m - region)).foldl (fun acc k ↦ acc * (1 + wAt I k)) 1

def coordinate (k : ℕ) : E :=
  (List.range' (k + 1) (region - (k + 1))).foldl
    (fun s j ↦ s + ofK ((coordinates region).getD (j - k) 0) * wAt I j) (wAt I k)

def slope (k : ℕ) : E :=
  match coordinateWeight k with
  | some weight => 1 + weight
  | none => 1 + (gammas I).getD (k - 8) 0

def publicWeight : E :=
  (List.range region).foldl (fun acc k ↦ acc * (1 + coordinate I k * slope I k)) (outside I)

def target : E := (statementWords I.stmt).foldr (fun word acc ↦ word + I.γ * acc) 0

def rows : E := (List.range (m - 1)).foldl (fun acc k ↦ acc + ofK ((rowVanishing m).getD k 0) * wAt I k) 0

def d : E := I.α + x I + I.β * I.t
def dNext : E := I.α + x I + I.β * I.next
def product : E := d I * dNext I
def copies : E := d I + dNext I + publicWeight I * x I * product I

def denominators : List E := (w I).map (1 + ·) ++ [product I + wAt I m, rows I, product I, 1 + I.ρ]

def inv (k : ℕ) : E := ((denominators I).getD k 1)⁻¹
def u : List E := (List.range (m + 2)).map fun k ↦ wAt I k * inv I k
def middle : E := (List.range' 3 (m - 3)).foldl (fun acc k ↦ acc * inv I k) (inv I 2)
def wiringScale : E := middle I * inv I 0 * inv I 1
def quotientScale : E := wiringScale I * inv I m * inv I (m + 1)
def rho2 : E := I.ρ * I.ρ
def opened : E := (1 + rho2 I) * (I.a[0] + I.ρ * (I.a[0] + I.a[1])) + rho2 I * (I.a[2] + I.ρ * (I.a[2] + I.a[3]))
def identities : E := (1 + I.ρ) * copies I * rows I + I.ρ * product I * gate I
def quotientPoint : List E := u I ++ [wAt I m * inv I (m + 2), I.ρ, extension.1.1, extension.1.2]
def quotientValue : E := extension.2 * quotientScale I * inv I (m + 2) * inv I (m + 3) * identities I
def parts : (List E × E) × (List E × E) × (List E × E) := quotientParts (quotientPoint I) m
def hInverse : E := (1 + wAt I (m + 1)) * (product I + wAt I m) * inv I (m + 4) * inv I (m + 5)
def hValue : E := (quotientValue I + (parts I).2.1.2 * I.qValue + (parts I).2.2.2 * I.gValue) * hInverse I

/-- **The six claims** at the leaves. -/
def claims : Claims :=
  { witness := ⟨[I.ρ, rho2 I] ++ ((u I).drop 2).take (m - 1), opened I * middle I * inv I m⟩
    wiring := ⟨(u I).take m, I.next * wiringScale I⟩
    h := ⟨(parts I).1.1, hValue I⟩
    q := ⟨(parts I).2.1.1, I.qValue⟩
    g := ⟨(parts I).2.2.1, I.gValue⟩
    sum := ⟨sumPoint logRows, extension.2 * target I⟩ }

/-- **`claimsAt` is these definitions.** -/
theorem claimsAt_eq : claimsAt logRows I.stmt I.α I.β I.γ I.t I.ρ I.a I.next I.qValue I.gValue =
    if (denominators I).any (· = 0) then none else some (claims I) := rfl

end Implementation.Formula
