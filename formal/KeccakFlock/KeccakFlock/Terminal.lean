-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from
-- `crates/leanvm/statement/src/keccak_flock.rs` (`structured_terminal`, `shift_offsets`, `grouped`, `SOURCE`, `RC`,
-- `RHO`) and `flock_min.rs` (`walked_terminal_with`, `known_weights_with`) with the Keccak block's walk; the shared
-- helpers (`eqKernel`, `eqEval`, `dot`, `lagrangeWeights`, `rowLowWeights`) are `formal/UniStatement`'s
-- transcriptions of `multilinear.rs` and `flock.rs`.
import KeccakFlock.Complete
import UniStatement.FlockBase

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
  `partial`) are written as the sums they compute. The function is split into the packing weights
  (`packingAt`), the correlations (`correlation`) and the rest (`structuredCore`), itself in the Rust's named parts
  (`tOne`, `rcOne`, `constants`, `bOne`, `oneCoefficient`, `freeW`, `copiesW`, `aTMid`, `aTLast`, `diagonal`,
  `laneTerms`, `gAt`, `shifts`).

`walkedTerminal_eq_bilinear` (`TerminalWalk.lean`) states the walked terminal as the matrices' bilinear form;
`Core.structuredTerminal_eq_walked` (`TerminalMain.lean`) the two terminals' equality.
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

/-! ### The body, in the Rust's named parts

The tables: the packing weights `eAt`, the correlations `corr`, the eq tables of the lane and round fields of
`chi_in` (`lrAt`, `rdAt`) and of `chi_in'` (`lhAt`, `rhAt`), the slices `sAt`; the kind coordinates `kr5 = chi_in[5]`,
`kh5 = chi_in'[5]`; `cEq = eq(chi_in, chi_in')`. -/

/-- A kind factor `kd[b]` (`kh[b]`): `1 + k5` for kind 0, `k5` for kind 1. -/
def kindW (k5 : E) (b : ℕ) : E := if b = 0 then 1 + k5 else k5

/-- A port group's kind and round factor `kr_g[g] = kd[g & 1] · rd[g >> 1]` (`kh_g`). -/
def groupW (k5 : E) (rAt : ℕ → E) (g : ℕ) : E := kindW k5 (g % 2) * rAt (g / 2)

/-- `lane_of(q, role) = (4q + role) mod 32`: a port word's lane field. -/
def laneOf (q role : ℕ) : ℕ := (4 * q + role) % 32

/-- A port word's weight: `lane factor · kr_g[q >> 3]` (`rx` for role 0 on the row side, `pc` for role 2 on the column
side). -/
def portW (lAt rAt : ℕ → E) (k5 : E) (q role : ℕ) : E := lAt (laneOf q role) * groupW k5 rAt (q / 8)

/-- `t_one = kd[0] · Σ lr · (Σ rd[2..=24] + rd[25])`: the `t` rows' `1 +`. -/
def tOne (lrAt rdAt : ℕ → E) (kr5 : E) : E := kindW kr5 0 * sumRange 0 25 lrAt * (sumRange 2 25 rdAt + rdAt 25)

/-- `rc_mid`: ι's bits of rounds `0..22`, `Σ_z E_z Σ_(j < 23, RC_j bit z) rd[j + 2]`. -/
def rcMid (eAt rdAt : ℕ → E) : E := esum ((List.range 64).map fun z ↦
  let rounds := (List.range 24).filter fun j ↦ rcBitR j z
  if rounds.isEmpty then 0 else eAt z * esum ((rounds.filter fun j ↦ j < 23).map fun j ↦ rdAt (j + 2)))

/-- `rc_last`: ι's bits of round 23. -/
def rcLast (eAt : ℕ → E) : E := esum ((List.range 64).map fun z ↦
  let rounds := (List.range 24).filter fun j ↦ rcBitR j z
  if !rounds.isEmpty && rounds.contains 23 then eAt z else 0)

/-- `rc_one = lr[0] kd[1] rc_mid + rx[0] rc_last`. -/
def rcOne (eAt lrAt rdAt : ℕ → E) (kr5 : E) : E :=
  lrAt 0 * kindW kr5 1 * rcMid eAt rdAt + portW lrAt rdAt kr5 0 0 * rcLast eAt

/-- `constants`: bit 0 of the 32 `Y` words, bit 1 of the `x` quad's `X` and `V` words. -/
def constants (eAt lrAt rdAt : ℕ → E) (kr5 : E) : E :=
  eAt 0 * ((rdAt 0 + rdAt 1) * esum ((List.range 8).map fun a ↦ lrAt (laneOf a 1))) +
    eAt 1 * groupW kr5 rdAt 3 * (lrAt (laneOf 25 0) + lrAt (laneOf 25 3))

/-- `b_one`: the `B = [1]` of the `A` rows (materialised and `A_23`), the free inputs and the copies. -/
def bOne (lrAt rdAt : ℕ → E) (kr5 : E) : E :=
  kindW kr5 1 * sumRange 0 25 lrAt * sumRange 2 25 rdAt + esum ((List.range 25).map fun q ↦ portW lrAt rdAt kr5 q 0) +
    grouped 25 (groupW kr5 rdAt) (fun q ↦ lrAt (laneOf q 2)) + grouped 25 (groupW kr5 rdAt) (fun q ↦ lrAt (laneOf q 3))

/-- `one_coefficient = t_one + rc_one + constants + α (constants + b_one) + α³`. -/
def oneCoefficient (eAt lrAt rdAt : ℕ → E) (kr5 alpha : E) : E :=
  tOne lrAt rdAt kr5 + rcOne eAt lrAt rdAt kr5 + constants eAt lrAt rdAt kr5 +
    alpha * (constants eAt lrAt rdAt kr5 + bOne lrAt rdAt kr5) + alpha * alpha * alpha

/-- `free`: the free inputs (`A = [own slot]`). -/
def freeW (lrAt rdAt lhAt rhAt : ℕ → E) (kr5 kh5 : E) : E :=
  grouped 25 (fun g ↦ groupW kr5 rdAt g * groupW kh5 rhAt g) (fun q ↦ lrAt (laneOf q 2) * lhAt (laneOf q 2))

/-- `copies`: the `V` words (`A = [X word, same z]`). -/
def copiesW (lrAt rdAt lhAt rhAt : ℕ → E) (kr5 kh5 : E) : E :=
  grouped 25 (fun g ↦ groupW kr5 rdAt g * groupW kh5 rhAt g) (fun q ↦ lrAt (laneOf q 3) * lhAt (laneOf q 0))

/-- `a_t_mid`: the `A` rows' `t` term, rounds `0..22`. -/
def aTMid (lrAt rdAt lhAt rhAt : ℕ → E) (kr5 kh5 : E) : E :=
  kindW kr5 1 * kindW kh5 0 * sumRange 0 25 (fun l ↦ lrAt l * lhAt l) * sumRange 2 25 (fun f ↦ rdAt f * rhAt f)

/-- `a_t_last`: the `X` words' `t` term (round 23). -/
def aTLast (lrAt rdAt lhAt rhAt : ℕ → E) (kr5 kh5 : E) : E :=
  kindW kh5 0 * rhAt 25 * sumRange 0 25 (fun l ↦ portW lrAt rdAt kr5 l 0 * lhAt l)

/-- `diagonal = Corr[0] (free + copies + a_t_mid + a_t_last + α² eq(chi_in, chi_in'))`. -/
def diagonal (corr lrAt rdAt lhAt rhAt : ℕ → E) (kr5 kh5 alpha cEq : E) : E :=
  corr 0 * (freeW lrAt rdAt lhAt rhAt kr5 kh5 + copiesW lrAt rdAt lhAt rhAt kr5 kh5 +
    aTMid lrAt rdAt lhAt rhAt kr5 kh5 + aTLast lrAt rdAt lhAt rhAt kr5 kh5 + alpha * alpha * cEq)

/-- `col_lh[x]` (`col_pc[x]`): a column's five lanes' weights. -/
def colSum (f : ℕ → E) (x : ℕ) : E := esum ((List.range 5).map fun y ↦ f (x + 5 * y))

/-- The row lane weight `u` of `b` lane `i`: `kd[0] (Lr[x − 1] + α Lr[x − 2]) + kd[1] Lr[i]`, written
`t + kr5 (t + Lr[i])`. -/
def laneU (lrAt : ℕ → E) (kr5 alpha : E) (i : ℕ) : E :=
  (lrAt ((i % 5 + 4) % 5 + 5 * (i / 5)) + alpha * lrAt ((i % 5 + 3) % 5 + 5 * (i / 5))) +
    kr5 * ((lrAt ((i % 5 + 4) % 5 + 5 * (i / 5)) + alpha * lrAt ((i % 5 + 3) % 5 + 5 * (i / 5))) + lrAt i)

/-- Round 23's row weight of `b` lane `i`: its `t` rows (`c23 t`) and the `X` word's `A` row (`rx[i]`). -/
def laneLast (lrAt rdAt : ℕ → E) (kr5 alpha : E) (i : ℕ) : E :=
  rdAt 25 * kindW kr5 0 * (lrAt ((i % 5 + 4) % 5 + 5 * (i / 5)) + alpha * lrAt ((i % 5 + 3) % 5 + 5 * (i / 5))) +
    portW lrAt rdAt kr5 i 0

/-- `v = v_mid u + v_last last`: the rounds `1..23`, whose columns are materialised states. -/
def laneV (lrAt rdAt rhAt : ℕ → E) (kr5 kh5 alpha : E) (i : ℕ) : E :=
  kindW kh5 1 * sumRange 1 23 (fun j ↦ rdAt (j + 2) * rhAt (j + 1)) * laneU lrAt kr5 alpha i +
    kindW kh5 1 * rhAt 24 * laneLast lrAt rdAt kr5 alpha i

/-- **The two coefficients of `b` lane `i`** (`g[rot] +=`, `g[rot + 1] +=`), with `(src, rot) = SOURCE[i]`. -/
def laneTerms (lrAt rdAt lhAt rhAt : ℕ → E) (kr5 kh5 alpha : E) (i : ℕ) : ℕ × E × ℕ × E :=
  let v := laneV lrAt rdAt rhAt kr5 kh5 alpha i
  let w0 := rdAt 2 * laneU lrAt kr5 alpha i
  let pc := fun q ↦ portW lhAt rhAt kh5 q 2
  let (src, rot) := source.getD i (0, 0)
  let xs := src % 5
  (rot, v * (lhAt src + colSum lhAt ((xs + 4) % 5)) + w0 * (pc src + colSum pc ((xs + 4) % 5)),
    (rot + 1) % 64, v * colSum lhAt ((xs + 1) % 5) + w0 * colSum pc ((xs + 1) % 5))

/-- `g[off]`: the 25 lanes' coefficients at offset `off`. -/
def gAt (lrAt rdAt lhAt rhAt : ℕ → E) (kr5 kh5 alpha : E) (off : ℕ) : E := esum ((List.range 25).map fun i ↦
  let (o₁, a₁, o₂, a₂) := laneTerms lrAt rdAt lhAt rhAt kr5 kh5 alpha i
  (if o₁ = off then a₁ else 0) + (if o₂ = off then a₂ else 0))

/-- `shifts = Σ_(off needed) g[off] Corr[off]`. -/
def shifts (corr lrAt rdAt lhAt rhAt : ℕ → E) (kr5 kh5 alpha : E) : E :=
  esum (((List.range 64).filter needed).map fun off ↦ gAt lrAt rdAt lhAt rhAt kr5 kh5 alpha off * corr off)

/-- **The structured terminal's body** (`structured_terminal` from the eq factors on):
`one_column · one_coefficient + diagonal + shifts`, `one_column = s_0 · eq(word 1, chi_in')`. -/
def structuredCore (eAt corr lrAt rdAt lhAt rhAt sAt : ℕ → E) (kr5 kh5 alpha cEq : E) : E :=
  sAt 0 * (lhAt 1 * groupW kh5 rhAt 0) * oneCoefficient eAt lrAt rdAt kr5 alpha +
    diagonal corr lrAt rdAt lhAt rhAt kr5 kh5 alpha cEq + shifts corr lrAt rdAt lhAt rhAt kr5 kh5 alpha

/-- The packing weights `E = (skip's Lagrange weights) ⊗ eq(row_low, ·)`, split at bit `p = max(k, 3)` as
`E_low ⊗ E_high`: `E_z = E_low[z mod 2^p] · E_high[z / 2^p]`. -/
def packingAt (zSkip : Option E) (rowLow : List E) (z : ℕ) : E :=
  let k := 6 - rowLow.length
  let p := max k 3
  let lag : List E := match zSkip with
    | some z => lagrangeWeights (2 ^ k) z
    | none => [1]
  let eLow : Array E := ((eqKernel (rowLow.take (p - k))).toList.flatMap fun m ↦ lag.map fun l ↦ l * m).toArray
  let eHigh : Array E := eqKernel (rowLow.drop (p - k))
  eLow.getD (z % 2 ^ p) 0 * eHigh.getD (z / 2 ^ p) 0

/-- The correlations `Corr[off] = Σ_zh E_high[zh] Q[off mod lo][zh − off / lo]` through the partial correlations
`Q[ol][m] = Σ_zl E_low[zl] s_(lo m + zl − ol)`, at the needed offsets (zero elsewhere). -/
def correlation (zSkip : Option E) (rowLow s : List E) (off : ℕ) : E :=
  let k := 6 - rowLow.length
  let p := max k 3
  let lag : List E := match zSkip with
    | some z => lagrangeWeights (2 ^ k) z
    | none => [1]
  let eLow : Array E := ((eqKernel (rowLow.take (p - k))).toList.flatMap fun m ↦ lag.map fun l ↦ l * m).toArray
  let eHigh : Array E := eqKernel (rowLow.drop (p - k))
  let lo := 2 ^ p
  let nHi := 2 ^ (6 - p)
  let sA := s.toArray
  let partialCorr := fun ol m : ℕ ↦
    esum ((List.range lo).map fun zl ↦ eLow.getD zl 0 * sA.getD ((lo * m + zl + 64 - ol) % 64) 0)
  if needed off then
    esum ((List.range nHi).map fun zh ↦ eHigh.getD zh 0 * partialCorr (off % lo) ((zh + nHi - off / lo) % nHi))
  else 0

/-- **`structured_terminal(z_skip, row_low, chi_in, chi_in', s, α)`** (`keccak_flock.rs`): the packing weights and
the correlations (`packingAt`, `correlation`), then the body (`structuredCore`) on the eq tables of `chi_in`'s and
`chi_in'`'s lane (`[..5]`) and round (`[6..]`) fields, their kind coordinates (`[5]`) and `eq(chi_in, chi_in')`. The
Rust's assertions (`chi_in`, `chi_in'` of 11, `s` of 64, `row_low` of at most 6, a skip point exactly when the skip
has bits) are the hypotheses of the theorems about it. -/
def structuredTerminal (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E) : E :=
  let lr := eqKernel (chiIn.take 5)
  let rd := eqKernel (chiIn.drop 6)
  let lh := eqKernel (chiInPrime.take 5)
  let rh := eqKernel (chiInPrime.drop 6)
  let sA := s.toArray
  structuredCore (packingAt zSkip rowLow) (correlation zSkip rowLow s) (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0)
    (fun i ↦ lh.getD i 0) (fun i ↦ rh.getD i 0) (fun i ↦ sA.getD i 0) (chiIn.getD 5 0) (chiInPrime.getD 5 0) alpha
    (eqEval chiIn chiInPrime)

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
