-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniKeccak.Terminal

/-!
# The structured terminal's pieces, on `E`

`UniKeccak.structuredTerminal` (`keccak_flock::structured_terminal`) is one `Id.run do` block; here its `let`s and its
two loops as definitions of their own (`eLowE`, `corrE`, `lrE`, …, `rcE`, `gE`), each the block's own text, and
`structuredTerminal_eq`: the block is `finalE` of them (by `rfl`). The simulation (`Sim/Terminal.lean`) relates each
piece of the program `RecGraphKeccak.Pi1.structuredTerminalS` to its definition here.
-/

namespace RecGraphKeccak.TerminalE

open LeanVM.Parameters UniStatement UniKeccak

section
variable (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E)

def kE : ℕ := 6 - rowLow.length
def pE : ℕ := max (kE rowLow) 3
def loE : ℕ := 2 ^ pE rowLow
def nHiE : ℕ := 2 ^ (6 - pE rowLow)
def lagE : List E := match zSkip with
    | some z => Flock.lagrangeWeights (2 ^ kE rowLow) z
    | none => [1]
def eLowE : Array E :=
  ((eqKernel (rowLow.take (pE rowLow - kE rowLow))).toList.flatMap fun m ↦
    (lagE zSkip rowLow).map fun l ↦ l * m).toArray
def eHighE : Array E := eqKernel (rowLow.drop (pE rowLow - kE rowLow))
def eAtE (z : ℕ) : E := (eLowE zSkip rowLow).getD (z % loE rowLow) 0 * (eHighE rowLow).getD (z / loE rowLow) 0
def partialAtE (ol m : ℕ) : E :=
  sumRange 0 (loE rowLow) fun zl ↦
    (eLowE zSkip rowLow).getD zl 0 * s.toArray.getD ((loE rowLow * m + zl + 64 - ol) % 64) 0
def corrAtE (off : ℕ) : E :=
  sumRange 0 (nHiE rowLow) fun zh ↦ (eHighE rowLow).getD zh 0 *
    partialAtE zSkip rowLow s (off % loE rowLow) ((zh + nHiE rowLow - off / loE rowLow) % nHiE rowLow)
def corrE : Array E := Array.ofFn (n := 64) fun off ↦
    if shiftOffsets.getD off.val false then corrAtE zSkip rowLow s off.val else 0
def lrE : Array E := eqKernel (chiIn.take 5)
def rdE : Array E := eqKernel (chiIn.drop 6)
def lhE : Array E := eqKernel (chiInPrime.take 5)
def rhE : Array E := eqKernel (chiInPrime.drop 6)
def kdE : Array E := #[1 + chiIn.getD 5 0, chiIn.getD 5 0]
def khE : Array E := #[1 + chiInPrime.getD 5 0, chiInPrime.getD 5 0]
def krGE : Array E := Array.ofFn (n := 4) fun g ↦ (kdE chiIn).getD (g.val &&& 1) 0 * (rdE chiIn).getD (g.val >>> 1) 0
def khGE : Array E :=
  Array.ofFn (n := 4) fun g ↦ (khE chiInPrime).getD (g.val &&& 1) 0 * (rhE chiInPrime).getD (g.val >>> 1) 0
def krhGE : Array E := Array.ofFn (n := 4) fun g ↦ (krGE chiIn).getD g.val 0 * (khGE chiInPrime).getD g.val 0
def laneOfE (q role : ℕ) : ℕ := (4 * q + role) % 32
def rxE : Array E :=
  Array.ofFn (n := lanes) fun q ↦ (lrE chiIn).getD (laneOfE q.val roleX) 0 * (krGE chiIn).getD (q.val >>> 3) 0
def pcE : Array E :=
  Array.ofFn (n := lanes) fun q ↦ (lhE chiInPrime).getD (laneOfE q.val roleC) 0 * (khGE chiInPrime).getD (q.val >>> 3) 0
def sumLrE : E := sumRange 0 lanes fun l ↦ (lrE chiIn).getD l 0
def sumRdAE : E := sumRange 2 (rounds + 1) fun f ↦ (rdE chiIn).getD f 0
def sumRdTE : E := sumRdAE chiIn + (rdE chiIn).getD (rounds + 1) 0
def tOneE : E := (kdE chiIn).getD 0 0 * sumLrE chiIn * sumRdTE chiIn
/-- ι's loop's body at the packing position `z`. -/
def rcBodyE (z : ℕ) (r : E × E) : Id (ForInStep (E × E)) :=
  let rs := (List.range rounds).filter fun j ↦ ((rc.getD j 0) >>> z.toUInt64) &&& 1 == 1
  if !rs.isEmpty then
    let ez := eAtE zSkip rowLow z
    let midSum := esum ((rs.filter (· < rounds - 1)).map fun j ↦ (rdE chiIn).getD (j + 2) 0)
    if rs.contains (rounds - 1) then pure (.yield (r.1 + ez * midSum, r.2 + ez))
    else pure (.yield (r.1 + ez * midSum, r.2))
  else pure (.yield (r.1, r.2))
/-- ι's loop: `(rcMid, rcLast)`. -/
def rcE : E × E := forIn (m := Id) [0:64] ((0 : E), (0 : E)) (rcBodyE zSkip rowLow chiIn)
def rcOneE : E :=
  (lrE chiIn).getD 0 0 * (kdE chiIn).getD 1 0 * (rcE zSkip rowLow chiIn).1 + (rxE chiIn).getD 0 0 * (rcE zSkip rowLow chiIn).2
def yWordsE : E := ((rdE chiIn).getD 0 0 + (rdE chiIn).getD 1 0) * sumRange 0 8 fun a ↦ (lrE chiIn).getD (laneOfE a roleY) 0
def constantsE : E := eAtE zSkip rowLow 0 * yWordsE chiIn + eAtE zSkip rowLow 1 * (krGE chiIn).getD 3 0 *
    ((lrE chiIn).getD (laneOfE xQuad roleX) 0 + (lrE chiIn).getD (laneOfE xQuad roleV) 0)
def bOneE : E := (kdE chiIn).getD 1 0 * sumLrE chiIn * sumRdAE chiIn + sumRange 0 lanes (fun q ↦ (rxE chiIn).getD q 0) +
    grouped lanes (krGE chiIn) (fun q ↦ (lrE chiIn).getD (laneOfE q roleC) 0) +
    grouped lanes (krGE chiIn) (fun q ↦ (lrE chiIn).getD (laneOfE q roleV) 0)
def oneCoefficientE : E := tOneE chiIn + rcOneE zSkip rowLow chiIn + constantsE zSkip rowLow chiIn +
    alpha * (constantsE zSkip rowLow chiIn + bOneE chiIn) + alpha * alpha * alpha
def oneColumnE : E := s.toArray.getD 0 0 * ((lhE chiInPrime).getD 1 0 * (khGE chiInPrime).getD 0 0)
def freeE : E := grouped lanes (krhGE chiIn chiInPrime) fun q ↦
    (lrE chiIn).getD (laneOfE q roleC) 0 * (lhE chiInPrime).getD (laneOfE q roleC) 0
def copiesE : E := grouped lanes (krhGE chiIn chiInPrime) fun q ↦
    (lrE chiIn).getD (laneOfE q roleV) 0 * (lhE chiInPrime).getD (laneOfE q roleX) 0
def aTMidE : E := (kdE chiIn).getD 1 0 * (khE chiInPrime).getD 0 0 *
    sumRange 0 lanes (fun l ↦ (lrE chiIn).getD l 0 * (lhE chiInPrime).getD l 0) *
    sumRange 2 (rounds + 1) (fun f ↦ (rdE chiIn).getD f 0 * (rhE chiInPrime).getD f 0)
def aTLastE : E := (khE chiInPrime).getD 0 0 * (rhE chiInPrime).getD (rounds + 1) 0 *
    sumRange 0 lanes (fun l ↦ (rxE chiIn).getD l 0 * (lhE chiInPrime).getD l 0)
def diagonalE : E := (corrE zSkip rowLow s).getD 0 0 * (freeE chiIn chiInPrime + copiesE chiIn chiInPrime +
    aTMidE chiIn chiInPrime + aTLastE chiIn chiInPrime + alpha * alpha * eqEval chiIn chiInPrime)
def rhoMidE : E := sumRange 1 (rounds - 1) fun j ↦ (rdE chiIn).getD (j + 2) 0 * (rhE chiInPrime).getD (j + 1) 0
def colLhE : Array E := Array.ofFn (n := 5) fun x ↦ sumRange 0 5 fun y ↦ (lhE chiInPrime).getD (x.val + 5 * y) 0
def colPcE : Array E := Array.ofFn (n := 5) fun x ↦ sumRange 0 5 fun y ↦ (pcE chiInPrime).getD (x.val + 5 * y) 0
def c23E : E := (rdE chiIn).getD (rounds + 1) 0 * (kdE chiIn).getD 0 0
def vMidE : E := (khE chiInPrime).getD 1 0 * rhoMidE chiIn chiInPrime
def vLastE : E := (khE chiInPrime).getD 1 0 * (rhE chiInPrime).getD rounds 0
/-- The shifts' weights' loop body at lane `i`. -/
def gBodyE (i : ℕ) (g : Array E) : Id (ForInStep (Array E)) :=
  let x := i % 5
  let y := i / 5
  let t := (lrE chiIn).getD ((x + 4) % 5 + 5 * y) 0 + alpha * (lrE chiIn).getD ((x + 3) % 5 + 5 * y) 0
  let u := t + chiIn.getD 5 0 * (t + (lrE chiIn).getD i 0)
  let last := c23E chiIn * t + (rxE chiIn).getD i 0
  let v := vMidE chiIn chiInPrime * u + vLastE chiInPrime * last
  let w0 := (rdE chiIn).getD 2 0 * u
  let src := (source.getD i (0, 0)).1
  let rot := (source.getD i (0, 0)).2
  let xs := src % 5
  pure (.yield ((g.modify rot (· + (v * ((lhE chiInPrime).getD src 0 + (colLhE chiInPrime).getD ((xs + 4) % 5) 0) +
      w0 * ((pcE chiInPrime).getD src 0 + (colPcE chiInPrime).getD ((xs + 4) % 5) 0)))).modify ((rot + 1) % 64)
      (· + (v * (colLhE chiInPrime).getD ((xs + 1) % 5) 0 + w0 * (colPcE chiInPrime).getD ((xs + 1) % 5) 0))))
/-- The shifts' weights `g`, lane by lane. -/
def gE : Array E := forIn (m := Id) [0:lanes] (Array.replicate 64 (0 : E)) (gBodyE chiIn chiInPrime alpha)
def shiftsE : E := sumRange 0 64 fun off ↦
  if shiftOffsets.getD off false then (gE chiIn chiInPrime alpha).getD off 0 * (corrE zSkip rowLow s).getD off 0 else 0
def finalE : E := oneColumnE chiInPrime s * oneCoefficientE zSkip rowLow chiIn alpha +
  diagonalE zSkip rowLow chiIn chiInPrime s alpha + shiftsE zSkip rowLow chiIn chiInPrime s alpha
end

/-- **The structured terminal is `finalE` of its pieces.** -/
theorem structuredTerminal_eq (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E) :
    structuredTerminal zSkip rowLow chiIn chiInPrime s alpha = finalE zSkip rowLow chiIn chiInPrime s alpha := rfl

end RecGraphKeccak.TerminalE
