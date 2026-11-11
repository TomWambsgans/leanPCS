-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/ProverDefs.lean` (the previous prover's computations, named) to the
-- PCS claims' prover (`formal/Statement/PcsQuotient/Prover.lean`: `quotientTables`, with the blinding of
-- `h`). Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E` and their limbs.
import PcsQuotient.Prover

/-!
# The honest prover's tables, named (the PCS claims)

`quotientTables` (`Prover.lean`) computes the three parts in `let`s. Here each pure computation is a
definition of its own, so that the bridge to the proof layers can speak of it, and
**`quotientTables_eq`** (`rfl`) writes `quotientTables` with them:

* `hValues`: the sum's polynomial on the cells; `wValuesOf`, `sigmaValuesOf`: the witness and wiring
  polynomials on the coset; `q0BOf`: the sum's polynomial with its blinding on the coset; `blocksOf`: the
  public weights, `1/Z_cells` and `1/Z_rows` per block of `2^11` coset points; `qValuesOf`,
  `qGateValuesOf`: the two quotients' values on the coset;
* `hTableOf`, `qTableOf`, `gTableOf`: the three parts.

`Constants` states the Statement's computed constants' defining properties.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-- **The Statement's computed constants have their defining properties** (`Domain.lean`):
`beta()` is a Cantor basis, `coordinates(11)` reads the region's coordinates and `row_vanishing(24)`
vanishes exactly on the `X` cells. -/
structure Constants : Prop where
  cantor : IsCantorBasis
  coords : CoordinatesRead 11
  rows : RowVanishingProperty 24

/-- **The witness table's entry `i`**: the cells' coefficients `wHat` below `n`, then the masks'
entries. -/
def witnessEntry (n : ℕ) (wHat mask : Array K) (i : ℕ) : K :=
  if i < n then wHat.getD i 0 else mask.getD (i - n) 0

/-- **The witness table on the coset** `β_{m+2} + span(β₀ … β_{m+1})`. -/
def wValuesOf (logRows : ℕ) (wHat mask : Array K) : Array K :=
  values (cellVars logRows + 2) (betaAt (cellVars logRows + 2))
    (Array.ofFn (n := 4 * 2 ^ cellVars logRows) fun i ↦
      if i.val < 2 ^ cellVars logRows then wHat.getD i.val 0
      else mask.getD (i.val - 2 ^ cellVars logRows) 0)

/-- **The sum's polynomial on the cells**. -/
def hValues (logRows : ℕ) (cells : Array K) (sigma : Array ℕ) (α β γ : E) : Array E :=
  Array.ofFn (n := 2 ^ cellVars logRows) fun i ↦
    let common := α + ofK (cells.getD i.val 0)
    (common + β * ofK (point i.val))⁻¹ + (common + β * ofK (point (sigma.getD i.val 0)))⁻¹ +
      if i.val < 2 ^ region then publicCellWeight i.val γ * ofK (cells.getD i.val 0) else 0

/-- **The wiring polynomial on the coset.** -/
def sigmaValuesOf (logRows : ℕ) (sigmaHat : Array K) : Array K :=
  values (cellVars logRows + 2) (betaAt (cellVars logRows + 2))
    (Array.ofFn (n := 4 * 2 ^ cellVars logRows) fun i ↦ sigmaHat.getD i.val 0)

/-- The blinding's coefficient `2^m + i`. -/
def blindAt (blind : Fin 3 → Fin hBlind → K) (i : ℕ) : E :=
  if hi : i < hBlind then E.ofLimbs (blind 0 ⟨i, hi⟩) (blind 1 ⟨i, hi⟩) (blind 2 ⟨i, hi⟩) else 0

/-- **The sum's polynomial with its blinding on the coset.** -/
def q0BOf (logRows : ℕ) (hHat : Array E) (blind : Fin 3 → Fin hBlind → K) : Array E :=
  values (cellVars logRows + 2) (betaAt (cellVars logRows + 2))
    (Array.ofFn (n := 4 * 2 ^ cellVars logRows) fun i ↦
      if i.val < 2 ^ cellVars logRows then hHat.getD i.val 0
      else blindAt blind (i.val - 2 ^ cellVars logRows))

/-- The rows' polynomial at `x`. -/
def rowPolyOf (logRows : ℕ) (x : K) : K :=
  ((chain x (cellVars logRows - 1)).zip (rowVanishing (cellVars logRows))).foldl
    (fun acc (w, t) ↦ acc + t * w) 0

/-- **Per block of `2^11` coset points**: the public weights, `1/Z_cells` and `1/Z_rows` by role. -/
def blocksOf (logRows : ℕ) (γ : E) : Array (Array E × K × Array K) :=
  Array.ofFn (n := 4 * 2 ^ cellVars logRows / 2 ^ region) fun hi ↦
    let base := hi.val * 2 ^ region
    let wAt (k : ℕ) : K :=
      (chain (betaAt (cellVars logRows + 2)) (cellVars logRows + 1)).getD k 0 + point (base >>> k)
    let indicator :=
      (List.range' region (cellVars logRows - region)).foldl (fun acc k ↦ acc * (1 + wAt k)) 1
    let weights : Array E :=
      if indicator = 0 then #[ofK indicator]
      else (List.range region).foldl
        (fun ws k ↦
          let shift := (List.range' k (region - k)).foldl
            (fun acc j ↦ acc + (coordinates region).getD (j - k) 0 * wAt j) 0
          let slope : E := 1 + (coordinateWeight k).getD ([γ, γ * γ, (γ * γ) * (γ * γ)].getD (k - 8) 0)
          let low := 1 + slope * ofK shift
          ws.map (· * low) ++ ws.map (· * (low + slope)))
        #[ofK indicator]
    let rowBase := rowPolyOf logRows (betaAt (cellVars logRows + 2) + point base)
    (weights, (wAt (cellVars logRows))⁻¹,
      Array.ofFn (n := 4) fun r ↦ (rowBase + rowPolyOf logRows (point r.val))⁻¹)

/-- **The copy identity's quotient on the coset**. -/
def qValuesOf (logRows : ℕ) (wValues sigmaValues : Array K) (q₀ : Array E)
    (blocks : Array (Array E × K × Array K)) (α β : E) : Array E :=
  Array.ofFn (n := 4 * 2 ^ cellVars logRows) fun i ↦
    let (weights, cellVanishing, _) := blocks.getD (i.val / 2 ^ region) (#[], 0, #[])
    let w := wValues.getD i.val 0
    let common := α + ofK w
    let d := common + β * ofK (betaAt (cellVars logRows + 2) + point i.val)
    let dNext := common + β * ofK (sigmaValues.getD i.val 0)
    let pub := if i.val % 2 ^ region < weights.size then
      weights.getD (i.val % 2 ^ region) 0 * ofK w else 0
    ((q₀.getD i.val 0 + pub) * d * dNext + d + dNext) * ofK cellVanishing

/-- **The gate's quotient on the coset**. -/
def qGateValuesOf (logRows : ℕ) (wValues : Array K) (blocks : Array (Array E × K × Array K)) :
    Array K :=
  Array.ofFn (n := 4 * 2 ^ cellVars logRows) fun i ↦
    let (_, _, rowInv) := blocks.getD (i.val / 2 ^ region) (#[], 0, #[])
    let at_ (j : ℕ) : K := wValues.getD j 0
    let (x, y, cc, v) := (at_ i.val, at_ (i.val ^^^ 1), at_ (i.val ^^^ 2), at_ (i.val ^^^ 3))
    (v + x + cc + y * cc) * rowInv.getD (i.val % 4) 0

/-- **The part `H`**: limb `e` of `h`'s coefficients, then of its blinding. -/
def hTableOf (logRows : ℕ) (hHat : Array E) (blind : Fin 3 → Fin hBlind → K) : Array K :=
  let n := 2 ^ cellVars logRows
  Array.ofFn (n := 8 * n) fun i ↦
    let (e, j) := (i.val / (2 * n), i.val % (2 * n))
    if 3 ≤ e then 0
    else if j < n then limbOf (hHat.getD j 0) e
    else if hj : j - n < hBlind ∧ e < 3 then blind ⟨e, hj.2⟩ ⟨j - n, hj.1⟩
    else 0

/-- **The part `Q`**: limb `e` of `q`'s coefficients. -/
def qTableOf (logRows : ℕ) (qHat : Array E) : Array K :=
  let n := 2 ^ cellVars logRows
  Array.ofFn (n := 16 * n) fun i ↦
    let (e, j) := (i.val / (4 * n), i.val % (4 * n))
    if e < 3 then limbOf (qHat.getD j 0) e else 0

/-- **The part `G`**: the gate's quotient's first `2^(m+1)` coefficients. -/
def gTableOf (logRows : ℕ) (qGateHat : Array K) : Array K :=
  Array.ofFn (n := 2 * 2 ^ cellVars logRows) fun i ↦ qGateHat.getD i.val 0

/-- The cells with the random rows filled. -/
def cellsR (circuit : Circuit) (cells₀ : Array K) (coins : Coins) : Array K :=
  randomizeCells circuit cells₀ coins.rows

/-- The sum's coefficients. -/
def hHatOf (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (α β γ : E) : Array E :=
  coefficients (cellVars circuit.logRows) 0
    (hValues circuit.logRows (cellsR circuit cells₀ coins) circuit.sigma α β γ)

/-- The witness values on the coset. -/
def wValuesC (circuit : Circuit) (cells₀ : Array K) (coins : Coins) : Array K :=
  wValuesOf circuit.logRows (coefficients (cellVars circuit.logRows) 0 (cellsR circuit cells₀ coins))
    (maskEntries coins.masks)

/-- The copy quotient's coefficients. -/
def qHatOf (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (α β γ : E) : Array E :=
  coefficients (cellVars circuit.logRows + 2) (betaAt (cellVars circuit.logRows + 2))
    (qValuesOf circuit.logRows (wValuesC circuit cells₀ coins)
      (sigmaValuesOf circuit.logRows circuit.wiringTable)
      (q0BOf circuit.logRows (hHatOf circuit cells₀ coins α β γ) coins.blind)
      (blocksOf circuit.logRows γ) α β)

/-- The gate quotient's coefficients. -/
def qGateHatOf (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (γ : E) : Array K :=
  coefficients (cellVars circuit.logRows + 2) (betaAt (cellVars circuit.logRows + 2))
    (qGateValuesOf circuit.logRows (wValuesC circuit cells₀ coins) (blocksOf circuit.logRows γ))

/-- **`quotientTables` with its computations named.** -/
theorem quotientTables_eq (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (α β γ : E) :
    quotientTables circuit cells₀ coins α β γ =
      (hTableOf circuit.logRows (hHatOf circuit cells₀ coins α β γ) coins.blind,
        qTableOf circuit.logRows (qHatOf circuit cells₀ coins α β γ),
        gTableOf circuit.logRows (qGateHatOf circuit cells₀ coins γ)) := rfl

/-- **The witness table with its computations named.** -/
theorem witnessTable_eq (circuit : Circuit) (cells₀ : Array K) (coins : Coins) :
    witnessTable circuit cells₀ coins = Array.ofFn (n := 2 * 2 ^ cellVars circuit.logRows) fun i ↦
      witnessEntry (2 ^ cellVars circuit.logRows)
        (coefficients (cellVars circuit.logRows) 0 (cellsR circuit cells₀ coins))
        (maskEntries coins.masks) i.val := rfl

end E2ECompleteness.Pcs
