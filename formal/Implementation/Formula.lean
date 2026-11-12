-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import PcsQuotient.Reduction

/-!
# The reduction's formulas, named

`PcsQuotient.claimsAt` (the Statement's transcription of `quotient::protocol::reduce` after its
transcript reads) at `2^22` rows, its local definitions as top-level ones over the leaves (`Vals`:
the statement, the challenges `α, β, μ, t, ρ`, the three values `X`, `C`, `V + Y`, `next`), so that the
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
  μ : E
  t : E
  ρ : E
  v : Vector E 3
  next : E

variable (I : Vals)

/-- `m = 24`. -/
abbrev m : ℕ := cellVars logRows

def w : List E := digitsOf I.t m

def wAt (k : ℕ) : E := (w I).getD k 0

def x : E := I.v[0]
def c : E := I.v[1]
def vy : E := I.v[2]
def gate : E := vy I + c I + x I * c I

def rows : E := (List.range (m - 1)).foldl (fun acc k ↦ acc + ofK ((rowVanishing m).getD k 0) * wAt I k) 0

def d : E := I.α + x I + I.β * I.t
def dNext : E := I.α + x I + I.β * I.next
def product : E := d I * dNext I
def z : E := wAt I m
def zeta : E := z I * I.t
def conicA : E := (witnessConic I.t (wAt I 1) I.ρ).1
def conicB : E := (witnessConic I.t (wAt I 1) I.ρ).2

def denominators : List E :=
  (List.range m).map (fun k ↦ 1 + wAt I k) ++ [1 + zeta I, zeta I + product I, rows I] ++
    pinPoints.map (fun p ↦ I.t + ofK p) ++ [conicA I + conicB I]

def inv (k : ℕ) : E := ((denominators I).getD k 1)⁻¹
def u : List E := (List.range m).map (fun k ↦ wAt I k * inv I k) ++ [zeta I * inv I m]
def copyInverse : E := inv I (m + 1)
def rowsInverse : E := inv I (m + 2)
def pinInverse (k : ℕ) : E := inv I (m + 3 + k)
def conicInverse : E := inv I (m + 3 + publicRows)
def middle : E := (List.range' 3 (m - 3)).foldl (fun acc k ↦ acc * inv I k) (inv I 2)
def wiringScale : E := middle I * inv I 0 * inv I 1
def tableScale : E := wiringScale I * inv I m

/-- The pins' fold's step. -/
def pinStep (acc : E) (k : ℕ) : E :=
  if k < publicWords then acc + ofK (I.stmt.words.getD k 0) * ofK (pinWeights.getD k 0) * pinInverse I k
  else if anchorValues I.stmt.words k = 0 then acc
  else acc + ofK (pinWeights.getD k 0 * anchorValues I.stmt.words k) * pinInverse I k

def pinned : E :=
  (List.range publicRows).foldl (pinStep I)
    (x I * (List.range publicRows).foldl (fun acc k ↦ acc * pinInverse I k) 1)

def g : E := gate I * rowsInverse I + pinned I
def kappa : E := product I * copyInverse I
def copyValue : E := extension.2 * tableScale I * I.t * (d I + dNext I + I.μ * z I * g I) * copyInverse I
def z1 : E := conicA I * conicInverse I
def lam : Vector E 3 := witnessWeights I.t (wAt I 1) I.ρ (z1 I)
def opened : E := (lam I)[0] * x I + (lam I)[1] * c I + (lam I)[2] * vy I

/-- **The three claims** at the leaves. -/
def claims : Claims :=
  { witness := ⟨[I.ρ, z1 I] ++ ((u I).drop 2).take (m - 2), opened I * middle I⟩
    wiring := ⟨(u I).take m, I.next * wiringScale I⟩
    copy := ⟨copyPoint (u I) (kappa I), copyValue I⟩ }

/-- **`claimsAt` is these definitions.** -/
theorem claimsAt_eq : claimsAt logRows I.stmt I.α I.β I.μ I.t I.ρ I.v I.next =
    if (denominators I).any (· = 0) then none else some (claims I) := rfl

end Implementation.Formula
