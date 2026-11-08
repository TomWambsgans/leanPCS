-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed from
-- `crates/leanvm_flock_gas/src/keccak_flock.rs` (`structured_terminal`, `shift_offsets`, `grouped`, `SOURCE`, `RC`,
-- `RHO`) and `flock_min.rs` (`walked_terminal_with`, `known_weights_with`) with the Keccak block's walk; the shared
-- helpers (`eqKernel`, `eqEval`, `dot`, `lagrangeWeights`, `rowLowWeights`) are `formal/UniStatement`'s
-- transcriptions of `multilinear.rs` and `flock.rs`.
import KeccakFlock.Complete
import UniStatement.Flock

/-!
# The Keccak-f block's lincheck terminal, two ways

* **`walkedTerminal`** (`walked_terminal_with::<_, KeccakWalked>`): the column weights `w = s ⊗ eq(chi_in', ·)`,
  the specification's forward walk `r1cs.rows w`, weighed by `e = (L(z_skip) ⊗ eq(row_low)) ⊗ eq(chi_in, ·)` and
  `α`, plus the `C = I` claim's `α² eq(chi_in, chi_in') Σ e_z s_z` and the constant position's pin
  `α³ eq(word 1, chi_in') s_0` (`known_weights_with` at `CONSTANT_COLUMN = 64`).
* **`structuredTerminal`** (`structured_terminal`): the same value from the block's structure, a few thousand `E`
  operations: the packing weights split at bit `p = max(k, 3)`, the 40 correlations through partial correlations,
  the eq factors of a word (lane, kind, round), the 25 lanes of `b` spread over their two offsets, the constant
  column's coefficient and the diagonal terms. Rust's accumulations into arrays (`g`, `rc_mid`, `rc_last`,
  `partial`) are written as the sums they compute.

`walkedTerminal_eq_bilinear` (`TerminalWalk.lean`) states the walked terminal as the matrices' bilinear form;
`structuredTerminal_eq_walked` (in progress) the two terminals' equality.
-/

namespace KeccakFlock.Terminal

open LeanVM.Parameters UniStatement UniStatement.Flock CompPoly

/-! ## Constants (`keccak_flock.rs`) -/

/-- `RHO`: ρ's rotation of lane `x + 5y`. -/
def rhoTable : List ℕ :=
  [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- `RC[j] >> z & 1 == 1`. -/
def rcBitR (j z : ℕ) : Bool := ((keccakRC.getD j 0).toNat >>> z) % 2 == 1

/-- `SOURCE[i] = (lane, rotation)`: `b[x, y] = rotl(θ(A)[lane], rotation)`, π moving lane `(x', y')` to
`(y', 2x' + 3y')` (the const loop, run). -/
def source : List (ℕ × ℕ) :=
  ((List.range 5).flatMap fun x ↦ (List.range 5).map fun y ↦ (y + 5 * ((2 * x + 3 * y) % 5), x + 5 * y)).foldl
    (fun acc (dst, src) ↦ acc.set dst (src, rhoTable.getD src 0)) (List.replicate 25 (0, 0))

/-- `shift_offsets()`: the offsets ρ's rotations and those plus one take. -/
def needed (off : ℕ) : Bool := rhoTable.any fun rot ↦ rot == off || (rot + 1) % 64 == off

/-- `grouped(n, weights, x) = Σ_(g < 4, 8g < n) weights[g] Σ_(8g ≤ q < min(n, 8g + 8)) x(q)`. -/
def grouped (n : ℕ) (weights : ℕ → E) (x : ℕ → E) : E :=
  esum (((List.range 4).filter fun g ↦ 8 * g < n).map fun g ↦
    weights g * esum ((List.range' (8 * g) (min n (8 * g + 8) - 8 * g)).map x))

/-- `Σ_(a ≤ i < b) f(i)`. -/
def sumRange (a b : ℕ) (f : ℕ → E) : E := esum ((List.range' a (b - a)).map f)

/-! ## The structured terminal -/

/-- **`structured_terminal(z_skip, row_low, chi_in, chi_in', s, α)`** (`keccak_flock.rs`). The Rust's assertions
(`chi_in`, `chi_in'` of 11, `s` of 64, `row_low` of at most 6, a skip point exactly when the skip has bits) are the
hypotheses of the theorems about it. -/
def structuredTerminal (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E) : E :=
  let one : E := 1
  let k := 6 - rowLow.length
  -- E = (skip's Lagrange weights) ⊗ eq(row_low, ·), split at bit p as E_low ⊗ E_high.
  let p := max k 3
  let lag : List E := match zSkip with
    | some z => lagrangeWeights (2 ^ k) z
    | none => [one]
  let mid := rowLow.take (p - k)
  let high := rowLow.drop (p - k)
  let eLow : Array E := ((eqKernel mid).toList.flatMap fun m ↦ lag.map fun l ↦ l * m).toArray
  let eHigh : Array E := eqKernel high
  let lo := 2 ^ p
  let nHi := 2 ^ (6 - p)
  let eAt := fun z : ℕ ↦ eLow.getD (z % lo) 0 * eHigh.getD (z / lo) 0
  let sA := s.toArray
  let sAt := fun i : ℕ ↦ sA.getD i 0
  -- Corr[off] = Σ_zh E_high[zh] Q[off mod lo][zh − off / lo], Q[ol][m] = Σ_zl E_low[zl] s_(lo m + zl − ol).
  let partialCorr := fun ol m : ℕ ↦ esum ((List.range lo).map fun zl ↦ eLow.getD zl 0 * sAt ((lo * m + zl + 64 - ol) % 64))
  let corr := fun off : ℕ ↦
    if needed off then
      esum ((List.range nHi).map fun zh ↦ eHigh.getD zh 0 * partialCorr (off % lo) ((zh + nHi - off / lo) % nHi))
    else 0
  let es := corr 0
  -- The eq factors of a word: lane, kind, round field.
  let lr := eqKernel (chiIn.take 5)
  let rd := eqKernel (chiIn.drop 6)
  let lh := eqKernel (chiInPrime.take 5)
  let rh := eqKernel (chiInPrime.drop 6)
  let lrAt := fun i : ℕ ↦ lr.getD i 0
  let rdAt := fun i : ℕ ↦ rd.getD i 0
  let lhAt := fun i : ℕ ↦ lh.getD i 0
  let rhAt := fun i : ℕ ↦ rh.getD i 0
  let kr5 := chiIn.getD 5 0
  let kh5 := chiInPrime.getD 5 0
  let kd := fun b : ℕ ↦ if b = 0 then one + kr5 else kr5
  let kh := fun b : ℕ ↦ if b = 0 then one + kh5 else kh5
  let krG := fun g : ℕ ↦ kd (g % 2) * rdAt (g / 2)
  let khG := fun g : ℕ ↦ kh (g % 2) * rhAt (g / 2)
  let krhG := fun g : ℕ ↦ krG g * khG g
  let laneOf := fun q role : ℕ ↦ (4 * q + role) % 32
  -- The rows' weights of the X words, the columns' of the C words.
  let rx := fun q : ℕ ↦ lrAt (laneOf q 0) * krG (q / 8)
  let pc := fun q : ℕ ↦ lhAt (laneOf q 2) * khG (q / 8)
  -- The constant column's coefficient, the pin's α³ with it.
  let sumLr := sumRange 0 25 lrAt
  let sumRdA := sumRange 2 25 rdAt
  let sumRdT := sumRdA + rdAt 25
  let tOne := kd 0 * sumLr * sumRdT
  let rcMid := esum ((List.range 64).map fun z ↦
    let rounds := (List.range 24).filter fun j ↦ rcBitR j z
    if rounds.isEmpty then 0 else eAt z * esum ((rounds.filter fun j ↦ j < 23).map fun j ↦ rdAt (j + 2)))
  let rcLast := esum ((List.range 64).map fun z ↦
    let rounds := (List.range 24).filter fun j ↦ rcBitR j z
    if !rounds.isEmpty && rounds.contains 23 then eAt z else 0)
  let rcOne := lrAt 0 * kd 1 * rcMid + rx 0 * rcLast
  let yWords := (rdAt 0 + rdAt 1) * esum ((List.range 8).map fun a ↦ lrAt (laneOf a 1))
  let constants := eAt 0 * yWords + eAt 1 * krG 3 * (lrAt (laneOf 25 0) + lrAt (laneOf 25 3))
  let bOne := kd 1 * sumLr * sumRdA + esum ((List.range 25).map rx) + grouped 25 krG (fun q ↦ lrAt (laneOf q 2)) +
    grouped 25 krG (fun q ↦ lrAt (laneOf q 3))
  let alpha2 := alpha * alpha
  let alpha3 := alpha2 * alpha
  let oneCoefficient := tOne + rcOne + constants + alpha * (constants + bOne) + alpha3
  let oneColumn := sAt 0 * (lhAt 1 * khG 0)
  -- Terms in Corr[0]: the free inputs, the copies, the A rows' t term, the C = I claim.
  let free := grouped 25 krhG (fun q ↦ lrAt (laneOf q 2) * lhAt (laneOf q 2))
  let copies := grouped 25 krhG (fun q ↦ lrAt (laneOf q 3) * lhAt (laneOf q 0))
  let aTMid := kd 1 * kh 0 * sumRange 0 25 (fun l ↦ lrAt l * lhAt l) * sumRange 2 25 (fun f ↦ rdAt f * rhAt f)
  let aTLast := kh 0 * rhAt 25 * sumRange 0 25 (fun l ↦ rx l * lhAt l)
  let cClaim := alpha2 * eqEval chiIn chiInPrime
  let diagonal := es * (free + copies + aTMid + aTLast + cClaim)
  -- b's terms: per b lane i, the row lane weight, spread over b[i]'s two offsets.
  let rhoMid := sumRange 1 23 (fun j ↦ rdAt (j + 2) * rhAt (j + 1))
  let colLh := fun x : ℕ ↦ esum ((List.range 5).map fun y ↦ lhAt (x + 5 * y))
  let colPc := fun x : ℕ ↦ esum ((List.range 5).map fun y ↦ pc (x + 5 * y))
  let c23 := rdAt 25 * kd 0
  let vMid := kh 1 * rhoMid
  let vLast := kh 1 * rhAt 24
  let laneTerms := fun i : ℕ ↦
    let x := i % 5
    let y := i / 5
    let t := lrAt ((x + 4) % 5 + 5 * y) + alpha * lrAt ((x + 3) % 5 + 5 * y)
    let u := t + kr5 * (t + lrAt i)
    let last := c23 * t + rx i
    let v := vMid * u + vLast * last
    let w0 := rdAt 2 * u
    let (src, rot) := source.getD i (0, 0)
    let xs := src % 5
    (rot, v * (lhAt src + colLh ((xs + 4) % 5)) + w0 * (pc src + colPc ((xs + 4) % 5)),
      (rot + 1) % 64, v * colLh ((xs + 1) % 5) + w0 * colPc ((xs + 1) % 5))
  let g := fun off : ℕ ↦ esum ((List.range 25).map fun i ↦
    let (o₁, a₁, o₂, a₂) := laneTerms i
    (if o₁ = off then a₁ else 0) + (if o₂ = off then a₂ else 0))
  let shifts := esum (((List.range 64).filter needed).map fun off ↦ g off * corr off)
  oneColumn * oneCoefficient + diagonal + shifts

/-! ## The walked terminal -/

/-- The bits of the constant's word, `CONSTANT_COLUMN / 64 = 1`, as the eq point of `known_weights_with`. -/
def constantBits : List E := (List.range 11).map (bitE 1)

/-- **`walked_terminal_with::<_, KeccakWalked>`** (`flock_min.rs`): the column weights `w[h·64 + l] = s_l ·
eq(chi_in')[h]`, the specification's forward walk `r1cs.rows w` weighed by `eq(chi_in)[h] · lowWeights[low]` and
`α`, plus the `C = I` claim and the constant position's pin. -/
def walkedTerminal (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E) : E :=
  let lowWeights := (rowLowWeights zSkip rowLow).2
  let high := eqKernel chiInPrime
  let w : CMlPolynomialEval E m :=
    (Vector.ofFn fun p : Pos ↦ s.getD (p.val % 64) 0 * high.getD (p.val / 64) 0 : Vector E (2 ^ m))
  let lr := r1cs.rows w
  let rows := eqKernel chiIn
  let entry := fun (v : CMlPolynomialEval E m) (i : ℕ) ↦ if h : i < 2 ^ m then v[(⟨i, h⟩ : Fin (2 ^ m))] else 0
  let matrix := esum ((List.range 2048).map fun h ↦
    rows.getD h 0 * (esum ((List.range 64).map fun low ↦ lowWeights.getD low 0 * entry lr.1 (h * 64 + low)) +
      alpha * esum ((List.range 64).map fun low ↦ lowWeights.getD low 0 * entry lr.2 (h * 64 + low))))
  matrix + alpha * alpha * eqEval chiIn chiInPrime * dot lowWeights s +
    alpha * alpha * alpha * eqEval constantBits chiInPrime * s.getD 0 0

end KeccakFlock.Terminal
