-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed, in the Rust's operation order, from
-- `crates/leanvm/statement/src/flock_min.rs` (`zerocheck`, `ring_end`), `flock.rs` (`lagrange_weights`,
-- `lagrange_interpolate`) and `ring_tower.rs` (`target`, `xor_network`).
import RecGraph.Pi1.Ops

/-!
# Flock's verifier as a program: the shared pieces

The pieces of Flock's verifier that the Keccak VM's π1-rec3 (`RecGraphKeccak.Pi1.Flock`) uses: the Lagrange weights
and interpolation, the zerocheck, the front's outputs (`FrontS`), and the ring switch's end in tower order
(`xorNetwork`, `towerTarget`, `ringEnd`). The constants (`fixedChallenges`, `phi`, `windowDenominator`, the tower's
`θ_j` and leaves) are `UniStatement`'s; the leaves' `XOR` network (`xorNetwork`, Paar's greedy common subexpressions)
is `ring_tower::xor_network`'s.
-/

namespace RecGraph.Pi1

open LeanVM.Parameters UniStatement UniStatement.Flock

/-- **`lagrange_weights(count, point)`**: the differences, the prefix and suffix products, the denominator. -/
def lagrangeWeights (count : Nat) (pt : Sym) : Prog (List Sym) := do
  let mut differences : Array Sym := #[]
  for node in [0:count] do
    let c ← const (phi node)
    differences := differences.push (← add pt c)
  let o1 ← one
  let mut prefix_ : Array Sym := Array.replicate (count + 1) o1
  let o2 ← one
  let mut suffix : Array Sym := Array.replicate (count + 1) o2
  for i in [0:count] do
    prefix_ := prefix_.set! (i + 1) (← mul (prefix_.getD i 0) (differences.getD i 0))
    suffix := suffix.set! (count - 1 - i) (← mul (suffix.getD (count - i) 0) (differences.getD (count - 1 - i) 0))
  let denominator ← const (windowDenominator count)
  let mut out : Array Sym := #[]
  for i in [0:count] do
    let p ← mul (prefix_.getD i 0) (suffix.getD (i + 1) 0)
    out := out.push (← mul p denominator)
  return out.toList

/-- `lagrange_interpolate(count, values, point)`. -/
def lagrangeInterpolate (count : Nat) (values : List Sym) (pt : Sym) : Prog Sym := do
  let weights ← lagrangeWeights count pt
  dot weights values

/-- **`zerocheck(log_n, k, fs)`**: the seven fixed coordinates, the others drawn as `fs` has it; the skip's coset
values and `z`; the rounds; `v_a`, `v_b`, `v_c = running + v_a v_b`. -/
def zerocheck (logN k : Nat) (fs : FsShape) : Prog (Option Sym × List Sym × Sym × Sym × Sym) := do
  let mut r : Array (Option Sym) := #[]
  for c in fixedChallenges do
    r := r.push (some (← const c))
  let drawn ← drawRun fs (logN - k - nFixed)
  r := r ++ (drawn.map some).toArray
  let (zSkip, claim) ← if k > 0 then do
      let coset ← nextScalars (2 ^ k)
      let z ← sample
      let zz ← zero
      let values := List.replicate (2 ^ k) zz ++ coset
      pure (some z, ← lagrangeInterpolate (2 ^ (k + 1)) values z)
    else do
      pure (none, ← zero)
  let (chi, running) ← sumcheckDrawn claim 3 r.toList false
  let vA ← nextScalar
  let vB ← nextScalar
  let ab ← mul vA vB
  let vC ← add running ab
  return (zSkip, chi, vA, vB, vC)

/-- What the zerocheck and the lincheck leave (`Front`). -/
structure FrontS where
  zSkip : Option Sym
  rowLow : List Sym
  chiIn : List Sym
  chiInPrime : List Sym
  chi : List Sym
  alpha : Sym
  rLc : Sym
  slices : List Sym
  point : List Sym

/-! ### The ring switch's end in tower order -/

/-- **`xor_network(leaves)`** (Paar's greedy common subexpressions): while some pair of variables occurs in two sums
or more, the most frequent pair (the first such) becomes a new variable. -/
def xorNetwork (leaves : Array Nat) : List (Nat × Nat) × List (List Nat) := Id.run do
  let mut rows : Array (List Nat) := leaves.map fun mask ↦ (List.range kBits).filter fun i ↦ mask.testBit i
  let mut xors : Array (Nat × Nat) := #[]
  for _ in [0:4096] do
    let vars := kBits + xors.size
    let mut count : Array Nat := Array.replicate (vars * vars) 0
    for row in rows do
      let ra := row.toArray
      for x in [0:ra.size] do
        for y in [x + 1:ra.size] do
          let idx := ra.getD x 0 * vars + ra.getD y 0
          count := count.modify idx (· + 1)
    -- the largest count, the first index among equals
    let mut best := 0
    let mut most := 0
    for at_ in [0:count.size] do
      if count.getD at_ 0 > most then
        best := at_
        most := count.getD at_ 0
    if most < 2 then break
    let a := best / vars
    let b := best % vars
    rows := rows.map fun row ↦ if row.contains a && row.contains b then (row.erase a).erase b ++ [vars] else row
    xors := xors.push (a, b)
  return (xors.toList, rows.toList)

/-- The tower's network, computed once. -/
def towerNetwork : List (Nat × Nat) × List (List Nat) := xorNetwork towerLeaves

/-- **`ring_tower::target(slices, map)`**: the leaves by the `XOR` network, then six levels. -/
def towerTarget (slices map : List Sym) : Prog Sym := do
  let (xors, sums) := towerNetwork
  let mut vars : Array Sym := slices.toArray
  for (a, b) in xors do
    vars := vars.push (← add (vars.getD a 0) (vars.getD b 0))
  let mut nodes : Array Sym := #[]
  for leaf in sums do
    let mut acc ← zero
    for v in leaf do
      acc ← add acc (vars.getD v 0)
    nodes := nodes.push acc
  for (f, j) in map.zip (List.range map.length) do
    let theta ← const (towerTheta.getD j 0)
    let mut next : Array Sym := #[]
    for q in [0:nodes.size / 2] do
      let a := nodes.getD (2 * q) 0
      let b := nodes.getD (2 * q + 1) 0
      let tb ← mul theta b
      let first ← add a tb
      let mut fa := a
      for _ in [0:2 ^ j] do
        fa ← square fa
      let mut fb := b
      for _ in [0:2 ^ j] do
        fb ← square fb
      let tfb ← mul theta fb
      let inner ← add fa tfb
      let second ← mul f inner
      next := next.push (← add first second)
    nodes := next
  return nodes.getD 0 0

/-- **`ring_end`** (tower order): the map's six challenges, then the target. -/
def ringEnd (s : List Sym) : Prog (List Sym × Sym) := do
  let map ← samples 6
  let target ← towerTarget s map
  return (map, target)

end RecGraph.Pi1
