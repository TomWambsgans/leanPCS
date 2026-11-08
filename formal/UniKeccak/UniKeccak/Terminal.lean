-- Part of this repository (new here, not from leanVM). Transcribed from `crates/leanvm/statement/src/keccak_flock.rs`
-- (`structured_terminal`, `shift_offsets`, `grouped`, `RC`, `RHO`, `SOURCE`, `port_word`, `CONSTANT_COLUMN`,
-- `X_QUAD`): the structured lincheck terminal of the Keccak-f[1600] Flock block of `crates/vendor/flock-42422001/src/keccak.rs`
-- (`docs/leanvm/flock/KECCAK.md` §4.2, M3). MIT OR Apache-2.0; see AGENTS.md.
module

public import UniStatement.Flock
public import UniStatement.KeccakTables

/-!
# The Keccak-f block's structured lincheck terminal (`keccak_flock::structured_terminal`)

Flock on the Keccak VM's `q_flock` runs on blocks of `2^17` positions (`2^11` words of 64 bits), one Keccak-f[1600]
permutation each, every round's state materialised (`flock::keccak`). Its lincheck terminal is
`Σ_(row, col) e(row) (Â0 + α B̂0)(row, col) w(col) + α² eq(chi_in, chi_in') Σ_z E_z s_z + α³ eq(word 1, chi_in') s_0`,
`e = E ⊗ eq(chi_in, ·)` (`E` the 64 packing weights: the skip's Lagrange weights ⊗ `eq(row_low, ·)`),
`w = s ⊗ eq(chi_in', ·)`. `structuredTerminal` computes it from the block's structure (eq factors of a word's
`(lane, kind, round)` fields, ρ and θ as cyclic shifts of the packing position, corrections), line by line as the
Rust's, with no walk of the circuit and no matrices. The order of a sum is the Rust's where it is a fold, any order
where the Rust's is `S::sum` (field addition is exact).

`structuredTerminal` is the value the Keccak verifier's Flock (`UniKeccak.verifyWalkedK`) checks `r_lc` against
(collected: `FlockMatrixTerminal`). That it equals the matrices' sum for `flock::keccak`'s R1CS is the Rust's
test (`keccak_flock`'s against `walked_terminal_with::<KeccakWalked>`, `crates/leanvm/statement/tests/
keccak_terminal.rs`), not a theorem here.
-/

@[expose] public section

namespace UniKeccak

open LeanVM.Parameters UniStatement

/-- `LOG_SIZE`: a block's positions, `2^17` (`keccakR1csLogSize`). -/
def logSize : ℕ := keccakR1csLogSize

/-- `LANES`. -/
def lanes : ℕ := 25

/-- `ROUNDS`. -/
def rounds : ℕ := 24

/-- The roles of a quad's four port words: `X`, `Y`, `C`, `V`. -/
def roleX : ℕ := 0
def roleY : ℕ := 1
def roleC : ℕ := 2
def roleV : ℕ := 3

/-- `X_QUAD`: the quad `(x, 1, 0, x)`. -/
def xQuad : ℕ := 25

/-- `CONSTANT_COLUMN`: the constant wire, quad 0's `Y` word, bit 0. -/
def constantColumn : ℕ := 64 * keccakPortWord 0 roleY

/-- `RC`: ι's round constants (FIPS 202). -/
def rc : List UInt64 :=
  [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- `RHO`: ρ's rotation of lane `x + 5 y`. -/
def rho : List ℕ :=
  [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- `SOURCE[x + 5 y] = (lane, rotation)`: `b[x, y] = rotl(θ(A)[lane], rotation)` (π: `(x', y') → (y', 2x' + 3y')`),
filled as the Rust's `const` block fills it. -/
def source : Array (ℕ × ℕ) := Id.run do
  let mut s : Array (ℕ × ℕ) := Array.replicate lanes (0, 0)
  for x in [0:5] do
    for y in [0:5] do
      s := s.set! (y + 5 * ((2 * x + 3 * y) % 5)) (x + 5 * y, rho.getD (x + 5 * y) 0)
  return s

/-- **`shift_offsets()`**: the cyclic shifts `z ↦ z − off` `b`'s forms read `ẑ`'s slices at: ρ's rotations and
those plus one (θ's `C[x + 1][z − 1]`). -/
def shiftOffsets : Array Bool := Id.run do
  let mut needed : Array Bool := Array.replicate 64 false
  for rot in rho do
    needed := needed.set! rot true
    needed := needed.set! ((rot + 1) % 64) true
  return needed

/-- **`grouped(n, weights, x)`**: `Σ_(g < 4) weights[g] Σ_(q in group g, q < n) x(q)`, group `g = q >> 3`. -/
def grouped (n : ℕ) (weights : Array E) (x : ℕ → E) : E :=
  esum ((List.range 4).filter (fun g ↦ 8 * g < n) |>.map fun g ↦
    weights.getD g 0 * esum ((List.range' (8 * g) (min n (8 * g + 8) - 8 * g)).map x))

/-- The sum of `f i` for `i ∈ [a, b)`. -/
def sumRange (a b : ℕ) (f : ℕ → E) : E := esum ((List.range' a (b - a)).map f)

/-- **The structured terminal** (`structured_terminal(z_skip, row_low, chi_in, chi_in', s, α)`, `keccak_flock.rs`):
the Keccak-f block's lincheck terminal from its structure (see the module documentation). `chi_in`, `chi_in'` have
`11` coordinates, `s` the `64` slices, `row_low` the `6 − k` packing bits left to rounds (`k` the skip). -/
def structuredTerminal (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E) : E := Id.run do
  let packing := 6
  let k := packing - rowLow.length
  let one : E := 1
  let sA := s.toArray
  -- E = (skip's Lagrange weights) ⊗ eq(row_low, ·) on the packing bits (skip low), split at bit p as E_low ⊗ E_high.
  let p := max k 3
  let lag : List E := match zSkip with
    | some z => Flock.lagrangeWeights (2 ^ k) z
    | none => [one]
  let mid := rowLow.take (p - k)
  let high := rowLow.drop (p - k)
  let eLow : Array E := ((eqKernel mid).toList.flatMap fun m ↦ lag.map fun l ↦ l * m).toArray
  let eHigh := eqKernel high
  let lo := 2 ^ p
  let nHi := 2 ^ (packing - p)
  let eAt (z : ℕ) : E := eLow.getD (z % lo) 0 * eHigh.getD (z / lo) 0
  -- Corr[off] = Σ_z E_z s_(z − off) = Σ_zh E_high[zh] Q[off mod lo][zh − off / lo], with the partial correlations
  -- Q[ol][m] = Σ_zl E_low[zl] s_(lo m + zl − ol).
  let needed := shiftOffsets
  let partialAt (ol m : ℕ) : E := sumRange 0 lo fun zl ↦ eLow.getD zl 0 * sA.getD ((lo * m + zl + 64 - ol) % 64) 0
  let corr : Array E := Array.ofFn (n := 64) fun off ↦
    if needed.getD off.val false then
      let ol := off.val % lo
      let oh := off.val / lo
      sumRange 0 nHi fun zh ↦ eHigh.getD zh 0 * partialAt ol ((zh + nHi - oh) % nHi)
    else 0
  let es := corr.getD 0 0
  -- The eq factors of a word: lane, kind, round field.
  let lr := eqKernel (chiIn.take 5)
  let rd := eqKernel (chiIn.drop 6)
  let lh := eqKernel (chiInPrime.take 5)
  let rh := eqKernel (chiInPrime.drop 6)
  let kr5 := chiIn.getD 5 0
  let kh5 := chiInPrime.getD 5 0
  let kd : Array E := #[one + kr5, kr5]
  let kh : Array E := #[one + kh5, kh5]
  -- A port group's kind and round factor, rows and columns, and their products.
  let krG : Array E := Array.ofFn (n := 4) fun g ↦ kd.getD (g.val &&& 1) 0 * rd.getD (g.val >>> 1) 0
  let khG : Array E := Array.ofFn (n := 4) fun g ↦ kh.getD (g.val &&& 1) 0 * rh.getD (g.val >>> 1) 0
  let krhG : Array E := Array.ofFn (n := 4) fun g ↦ krG.getD g.val 0 * khG.getD g.val 0
  let laneOf (q role : ℕ) : ℕ := (4 * q + role) % 32
  -- The rows' weights of the X words (A_23, round 23's lin-id rows), and the columns' of the C words (A_{−1}).
  let rx : Array E := Array.ofFn (n := lanes) fun q ↦ lr.getD (laneOf q.val roleX) 0 * krG.getD (q.val >>> 3) 0
  let pc : Array E := Array.ofFn (n := lanes) fun q ↦ lh.getD (laneOf q.val roleC) 0 * khG.getD (q.val >>> 3) 0
  -- The constant column's coefficient (`one = s_0 · eq(chi_in', word 1)`), the pin's α³ with it.
  let sumLr := sumRange 0 lanes fun l ↦ lr.getD l 0
  let sumRdA := sumRange 2 (rounds + 1) fun f ↦ rd.getD f 0
  let sumRdT := sumRdA + rd.getD (rounds + 1) 0
  -- t rows: A = 1 + b[x+1], at every position.
  let tOne := kd.getD 0 0 * sumLr * sumRdT
  -- ι: lane 0's A rows at RC_j's bits (A_23's in the X word of quad 0).
  let mut rcMid : E := 0
  let mut rcLast : E := 0
  for z in [0:64] do
    let rs := (List.range rounds).filter fun j ↦ ((rc.getD j 0) >>> z.toUInt64) &&& 1 == 1
    if !rs.isEmpty then
      let ez := eAt z
      let midSum := esum ((rs.filter (· < rounds - 1)).map fun j ↦ rd.getD (j + 2) 0)
      rcMid := rcMid + ez * midSum
      if rs.contains (rounds - 1) then rcLast := rcLast + ez
  let rcOne := lr.getD 0 0 * kd.getD 1 0 * rcMid + rx.getD 0 0 * rcLast
  -- Constant rows (A = B = [1]): bit 0 of the 32 Y words, bit 1 of the x quad's X and V words (group 3).
  let yWords := (rd.getD 0 0 + rd.getD 1 0) * sumRange 0 8 fun a ↦ lr.getD (laneOf a roleY) 0
  let constants := eAt 0 * yWords +
    eAt 1 * krG.getD 3 0 * (lr.getD (laneOf xQuad roleX) 0 + lr.getD (laneOf xQuad roleV) 0)
  -- B = [1]: the A rows (materialised and A_23), the free inputs, the copies.
  let bOne := kd.getD 1 0 * sumLr * sumRdA + sumRange 0 lanes (fun q ↦ rx.getD q 0) +
    grouped lanes krG (fun q ↦ lr.getD (laneOf q roleC) 0) + grouped lanes krG (fun q ↦ lr.getD (laneOf q roleV) 0)
  let alpha2 := alpha * alpha
  let alpha3 := alpha2 * alpha
  let oneCoefficient := tOne + rcOne + constants + alpha * (constants + bOne) + alpha3
  let oneColumn := sA.getD 0 0 * (lh.getD 1 0 * khG.getD 0 0)
  -- Terms in Corr[0] = Σ_z E_z s_z: the free inputs, the copies, the A rows' t term, and the C = I claim.
  let free := grouped lanes krhG fun q ↦ lr.getD (laneOf q roleC) 0 * lh.getD (laneOf q roleC) 0
  let copies := grouped lanes krhG fun q ↦ lr.getD (laneOf q roleV) 0 * lh.getD (laneOf q roleX) 0
  let aTMid := kd.getD 1 0 * kh.getD 0 0 * sumRange 0 lanes (fun l ↦ lr.getD l 0 * lh.getD l 0) *
    sumRange 2 (rounds + 1) (fun f ↦ rd.getD f 0 * rh.getD f 0)
  let aTLast := kh.getD 0 0 * rh.getD (rounds + 1) 0 * sumRange 0 lanes (fun l ↦ rx.getD l 0 * lh.getD l 0)
  let cClaim := alpha2 * eqEval chiIn chiInPrime
  let diagonal := es * (free + copies + aTMid + aTLast + cClaim)
  -- b's terms: a row lane weight per b lane i, the t rows reading b[i] on the left (lane x − 1) and, times α, on
  -- the right (lane x − 2), and the A row of lane i.
  let rhoMid := sumRange 1 (rounds - 1) fun j ↦ rd.getD (j + 2) 0 * rh.getD (j + 1) 0
  let colLh : Array E := Array.ofFn (n := 5) fun x ↦ sumRange 0 5 fun y ↦ lh.getD (x.val + 5 * y) 0
  let colPc : Array E := Array.ofFn (n := 5) fun x ↦ sumRange 0 5 fun y ↦ pc.getD (x.val + 5 * y) 0
  let c23 := rd.getD (rounds + 1) 0 * kd.getD 0 0
  let vMid := kh.getD 1 0 * rhoMid
  let vLast := kh.getD 1 0 * rh.getD rounds 0
  let mut g : Array E := Array.replicate 64 0
  for i in [0:lanes] do
    let x := i % 5
    let y := i / 5
    let t := lr.getD ((x + 4) % 5 + 5 * y) 0 + alpha * lr.getD ((x + 3) % 5 + 5 * y) 0
    -- Rounds 0..22: Kd[0] t + Kd[1] Lr[i]; round 23: its t rows, and the X word's A row.
    let u := t + kr5 * (t + lr.getD i 0)
    let last := c23 * t + rx.getD i 0
    -- Columns: A_{j−1} materialised (rounds 1..23), A_{−1} (round 0, the C words).
    let v := vMid * u + vLast * last
    let w0 := rd.getD 2 0 * u
    let (src, rot) := source.getD i (0, 0)
    let xs := src % 5
    g := g.modify rot (· + (v * (lh.getD src 0 + colLh.getD ((xs + 4) % 5) 0) +
      w0 * (pc.getD src 0 + colPc.getD ((xs + 4) % 5) 0)))
    g := g.modify ((rot + 1) % 64) (· + (v * colLh.getD ((xs + 1) % 5) 0 + w0 * colPc.getD ((xs + 1) % 5) 0))
  let shifts := sumRange 0 64 fun off ↦ if needed.getD off false then g.getD off 0 * corr.getD off 0 else 0
  return oneColumn * oneCoefficient + diagonal + shifts

end UniKeccak

end
