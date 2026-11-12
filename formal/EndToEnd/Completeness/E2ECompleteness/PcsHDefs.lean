-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the Statement's `quotientParts` (`formal/Statement/PcsQuotient/Prover.lean`) by named pieces.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E`.
import PcsQuotient.Prover

/-!
# The prover's quotient, by named pieces

`quotientParts` computes in `let`s; here each piece is a definition of its own (the same terms), and
**`quotientParts_eq`** (`rfl`) writes `quotientParts` with them.
-/

set_option autoImplicit false

open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain

namespace E2ECompleteness.Pcs.H

variable (circuit : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins) (α β μ : E)

/-- The sum's values on the cells. -/
def hArr : Array E :=
  Array.ofFn (n := 2 ^ cellVars circuit.logRows) fun i ↦
    let common := α + ofK ((witnessParts circuit cells₀ coins).1.getD i.val 0)
    (common + β * ofK (point i.val))⁻¹ + (common + β * ofK (point (circuit.sigma.getD i.val 0)))⁻¹

/-- `h`'s coefficients. -/
def hHatOf : Array E := coefficients (cellVars circuit.logRows) 0 (hArr circuit cells₀ coins α β)

/-- The coset's offset. -/
def offsetOf : K := betaAt (cellVars circuit.logRows + 2)

def wValuesOf : Array K :=
  values (cellVars circuit.logRows + 2) (offsetOf circuit)
    (Array.ofFn (n := 4 * 2 ^ cellVars circuit.logRows) fun i ↦
      (witnessParts circuit cells₀ coins).2.getD i.val 0)

def sigmaValuesOf : Array K :=
  values (cellVars circuit.logRows + 2) (offsetOf circuit)
    (Array.ofFn (n := 4 * 2 ^ cellVars circuit.logRows) fun i ↦ circuit.wiringTable.getD i.val 0)

def hValuesOf : Array E :=
  values (cellVars circuit.logRows + 2) (offsetOf circuit)
    (Array.ofFn (n := 4 * 2 ^ cellVars circuit.logRows) fun i ↦
      if i.val < 2 ^ cellVars circuit.logRows then (hHatOf circuit cells₀ coins α β).getD i.val 0
      else blindAt coins (i.val - 2 ^ cellVars circuit.logRows))

def rowPolyOf (x : K) : K :=
  ((chain x (cellVars circuit.logRows - 1)).zip (rowVanishing (cellVars circuit.logRows))).foldl
    (fun acc (w, t) ↦ acc + t * w) 0

def zPinsOf (x : K) : K := pinPoints.foldl (fun acc p ↦ acc * (x + p)) 1

def pinPolyOf (x : K) : K := (List.range publicRows).foldl
  (fun acc k ↦ acc + pinWeights.getD k 0 * anchorValues stmt.words k *
    (List.range publicRows).foldl (fun pr j ↦ if j = k then pr else pr * (x + pinPoints.getD j 0)) 1) 0

/-- The quotient's two parts on the coset. -/
def partsOf : Array (E × E) :=
  Array.ofFn (n := 4 * 2 ^ cellVars circuit.logRows) fun i ↦
    let at_ (i : ℕ) : K := (wValuesOf circuit cells₀ coins).getD i 0
    let x := offsetOf circuit + point i.val
    let w := at_ i.val
    let d := α + ofK w + β * ofK x
    let dNext := α + ofK w + β * ofK ((sigmaValuesOf circuit).getD i.val 0)
    let z := (chain x (cellVars circuit.logRows + 1)).getD (cellVars circuit.logRows) 0
    let gate := at_ (i.val ^^^ 3) + at_ (i.val ^^^ 1) + at_ (i.val ^^^ 2) + w * at_ (i.val ^^^ 2)
    let g := ofK (gate * (rowPolyOf circuit x)⁻¹ + (w + pinPolyOf stmt x) * (zPinsOf x)⁻¹)
    (((hValuesOf circuit cells₀ coins α β).getD i.val 0 * d * dNext + d + dNext) * ofK z⁻¹ + μ * g,
      ofK (x * x + x) * d * dNext)

def q0HatOf : Array E :=
  coefficients (cellVars circuit.logRows + 2) (offsetOf circuit) ((partsOf circuit stmt cells₀ coins α β μ).map (·.1))

def eHatOf : Array E :=
  coefficients (cellVars circuit.logRows + 2) (offsetOf circuit) ((partsOf circuit stmt cells₀ coins α β μ).map (·.2))

def b2Of : E :=
  (q0HatOf circuit stmt cells₀ coins α β μ).getD (2 ^ cellVars circuit.logRows) 0 *
    ((eHatOf circuit stmt cells₀ coins α β μ).getD (2 ^ cellVars circuit.logRows) 0 +
      (eHatOf circuit stmt cells₀ coins α β μ).getD (2 * 2 ^ cellVars circuit.logRows) 0)⁻¹

def qHatOf : Array E :=
  Array.ofFn (n := 2 * 2 ^ cellVars circuit.logRows + 1) fun j ↦
    (q0HatOf circuit stmt cells₀ coins α β μ).getD j.val 0 +
      b2Of circuit stmt cells₀ coins α β μ * (eHatOf circuit stmt cells₀ coins α β μ).getD j.val 0

theorem quotientParts_fst : (quotientParts circuit stmt cells₀ coins α β μ).1 = hHatOf circuit cells₀ coins α β := by
  unfold quotientParts hHatOf hArr
  rfl

theorem quotientParts_snd :
    (quotientParts circuit stmt cells₀ coins α β μ).2.1 = qHatOf circuit stmt cells₀ coins α β μ := by
  unfold quotientParts
  rfl

theorem quotientParts_thd :
    (quotientParts circuit stmt cells₀ coins α β μ).2.2 = b2Of circuit stmt cells₀ coins α β μ := by
  unfold quotientParts
  rfl

/-- **`quotientParts` by its pieces.** -/
theorem quotientParts_eq :
    quotientParts circuit stmt cells₀ coins α β μ =
      (hHatOf circuit cells₀ coins α β, qHatOf circuit stmt cells₀ coins α β μ, b2Of circuit stmt cells₀ coins α β μ) :=
  Prod.ext (quotientParts_fst ..) (Prod.ext (quotientParts_snd ..) (quotientParts_thd ..))

end E2ECompleteness.Pcs.H
