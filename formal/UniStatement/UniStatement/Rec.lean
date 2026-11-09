-- Part of this repository. Transcribed from `crates/leanvm/statement/src/transcript.rs` (`FsShape`, `squares`,
-- `NARROW_BITS`, `narrow`, `Channel::sample_narrow`, `sumcheck_drawn`, `cantor_beta1`, `pair_point`,
-- `pair_round_poly`, `sumcheck_pairs_drawn`), `flock_min.rs` (`zerocheck`'s draw, `Slices::TowerWalk`,
-- `verify_walked`, `walked_terminal`), `flock.rs` (`blake2s_row_values`, `RowValues`, adapted there from leanVM
-- (https://github.com/leanEthereum/leanVM), commit 42422001), `hash.rs` (`BLAKE2S_IV`, `BLAKE2S_SIGMA`,
-- `BLAKE2S_G_LANES`, leanVM's), `crates/leanvm/univariate/src/verifier.rs` (`reduce`'s `α` draw and walked Flock,
-- `batch`'s rounds) and `contract.rs` (`variant_bytes`, `contract_iv_for`), at `leanvm-rec` 4247e37. MIT OR
-- Apache-2.0; see AGENTS.md.
module

public import UniStatement.Opening

/-!
# π1's Fiat–Shamir shapes for the recursion: π1-rec, π1-rec2, π1-rec3

`docs/leanvm/rec/SPEC-REC.md` §1.4 and §12 (items 4, 6–8), `SPEC-POINTS.md`. The recursion's inner proof π1 is the
main line with its Fiat–Shamir shape changed (`FsShape`, a parameter here, **`main` by default**) and, from π1-rec2
on, Flock's lincheck terminal checked by π1's verifier itself (`walk`, `Slices::TowerWalk`):

| Rust | `Blake2s` | `fs` | `walk` |
|---|---|---|---|
| `FLOCK_MAIN` (the main line) | `.flock flockMain` | `.main` | `false` |
| `FLOCK_REC` (π1-rec) | `.flock flockMain` | `.rec1` | `false` |
| `FLOCK_REC2` (π1-rec2) | `.flock flockMain` | `.rec2` | `true` |
| `FLOCK_REC3` (π1-rec3, the recursion's) | `.flock flockMain` | `.rec3` | `true` |

* **Squares** (`.rec1`, `.rec2`, `.rec3`; `FsShape::draw`): the bus's `α = (c, c², c⁴, c⁸)` of one challenge `c`, and
  Flock's zerocheck eq coordinates after the seven fixed ones `c', c'², c'⁴, …` of one challenge `c'` (`drawRun`).
* **The walked terminal** (`walk`, `Slices::TowerWalk`: the main line's `tower` slices, and the terminal walked):
  Flock's lincheck terminal `r_lc` is checked against `walkedTerminal`, leanVM's forward walk of the BLAKE2s circuit
  on the sent slices (`blake2sRowValues`: `A0 w`, `B0 w`), collected as a zero (`FlockMatrixTerminal`). No matrices'
  reduction, no `a`, `b`, no claims on `A0`, `B0`: three calls, `C1`, `C2`, the setup, all at the batch's point.
* **Narrow challenges** (`.rec2`, `.rec3`): the batching sumcheck's challenges are the hash's low 160 bits
  (`sampleNarrow`: limb 2 cut to 32 bits, `narrowE`).
* **Paired rounds** (`.rec3`): the batch two variables a round (`sumcheckPairsDrawn`): pair `j`'s round polynomial
  `G_j` of degree `4 · 2` sent but `c_3` (`pairRoundPoly`: `Σ_(x ∈ V_2) G_j(x) = Σ_(e > 0, 3 | e) c_e`), one narrow
  challenge `z_j`, the point's two coordinates `pairPoint z_j = (z + β_1 (z² + z), z² + z)` (`cantorBeta1`); with
  the variables odd, a last plain round.
* **The IV binds the variant** (`variantBytes`, `contractIvForWith`): with a shape other than
  `main`, the tag `fs-rec`, `fs-rec2` or `fs-rec3`, the skip and the slices' code are appended to the IV's preimage.

**The existing definitions are unchanged**: every function that changes has a parameterised copy here, named with
`Fs` (`Flock.zerocheckFs`, `Flock.frontFs`, `Flock.verifyFs`, `Flock.verifyDeferredFs`, `batchFs`, `reduceWithFs`,
`runWithFs`, `runFs`, `verifyWithFs`; and the new `Flock.verifyWalkedFs`), its body the original's but for the
draws, the walk and the batch's rounds. At `fs = .main`, `walk = false` each is the original (`…_main`, by `rfl`
after a case split on the configuration), so the proofs about the main line (`UniSound`, `UniComplete`) keep their
meaning and are not rebuilt. The verifier the recursion's π2 proves is `runFs reference iv publicInput stream
(.flock flockMain) .point .rec3 true`, and with its three openings `verifyWithFs … .rec3 true`.
-/

@[expose] public section

namespace UniStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **The verifier's Fiat–Shamir shape** (`transcript::FsShape`): which runs of challenges are derived, how wide the
batch's challenges are, and how many variables a batch round takes. -/
inductive FsShape where
  /-- Every challenge drawn, one Keccak-256 each: the main line's. -/
  | main
  /-- π1-rec (the Rust's `Rec`; `rec` is the recursor's name here): `α` and Flock's zerocheck eq point after its
  seven fixed coordinates as successive squares. -/
  | rec1
  /-- π1-rec2: `rec`, and the batching sumcheck's challenges narrow (160 bits). -/
  | rec2
  /-- π1-rec3: `rec2` with the batching sumcheck two variables a round. -/
  | rec3
  deriving DecidableEq, Repr, Inhabited

/-- Whether the batch's challenges are narrow (`.rec2`, `.rec3`). -/
def FsShape.narrow : FsShape → Bool
  | .rec2 | .rec3 => true
  | .main | .rec1 => false

/-- **`NARROW_BITS`**: a narrow challenge's bits, its top limb's low 32. -/
def narrowBits : ℕ := 160

/-- **`narrow(x)`**: the narrow challenge of a hash's challenge, its limb 2 cut to 32 bits. -/
def narrowE (x : E) : E := eNew (x.limb 0).lane (x.limb 1).lane ((x.limb 2).lane &&& 0xFFFFFFFF)

/-- **`squares(first, count)`**: `first, first², first⁴, …`, `count` terms, each the square of the one before. -/
def squares : E → ℕ → List E
  | _, 0 => []
  | x, n + 1 => x :: squares (x * x) n

/-- **`cantor_beta1()`**: `β_1` of the Cantor basis (`β_1² + β_1 = 1`, its low bit clear): `x^((2^64 − 1)/3)`, an
element of order 3, or it plus one, the one whose low bit is clear. -/
def cantorBeta1 : E :=
  let g := epow gen ((2 ^ 64 - 1) / 3)
  if (g.limb 0).lane &&& 1 = 0 then g else g + 1

/-- **`pair_point(z)`**: a pair's two coordinates at its challenge, `(y_0, y_1) = (z + β_1 y_1, z² + z)`, the
coordinate functionals of `V_2 = {0, 1, β_1, 1 + β_1}`. -/
def pairPoint (z : E) : List E :=
  let y1 := z * z + z
  [z + cantorBeta1 * y1, y1]

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`Channel::sample_narrow`** (`KeccakChannel`: `narrow(self.sample())`): a challenge, cut to 160 bits. The channel
keeps the narrow one among its challenges. -/
def sampleNarrow : ChanM m E := do
  let c ← get
  let input := digestBytes c.state ++ (c.data.extract c.absorbed c.cursor).toList
  let state ← (keccak256With F input : m Digest)
  let x := narrowE (PcsQuotient.Transcript.challengeOf state)
  set { c with absorbed := c.cursor, state := state, challenges := c.challenges.push x }
  return x

/-- A challenge, narrow or not. -/
def sampleDrawn (narrow : Bool) : ChanM m E :=
  match narrow with
  | true => sampleNarrow F
  | false => sample F

/-- **`FsShape::draw(channel, count)`**: a run of `count` challenges, drawn one by one (`main`), or the first drawn and
each next the square of the one before (the others). -/
def drawRun (fs : FsShape) (count : ℕ) : ChanM m (List E) :=
  match fs with
  | .main => samples F count
  | .rec1 | .rec2 | .rec3 =>
    if count = 0 then pure [] else do
      let c ← sample F
      pure (squares c count)

/-- **`sumcheck_drawn(claim, count, equalities, narrow)`**: `sumcheck`, its challenges narrow when `narrow`. -/
def sumcheckDrawn (claim : E) (count : ℕ) (equalities : List (Option E)) (narrow : Bool) :
    ChanM m (List E × E) := do
  let mut point : Array E := #[]
  let mut claim := claim
  for equality in equalities do
    let message ← roundPoly (m := m) count claim equality
    let challenge ← sampleDrawn F narrow
    point := point.push challenge
    claim := polyEval message challenge
  return (point.toList, claim)

/-- **`pair_round_poly(degree, claim)`**: a pair's round polynomial `G` of degree `4 · degree`, its monomial
coefficients but `c_3` read (`c_0, c_1, c_2`, then `c_4 …`); `c_3` is the claim plus every read `c_e` with `e > 0`,
`3 | e` (over `V_2 = GF(4)`, `Σ_x x^e` is `1` exactly then). -/
def pairRoundPoly (degree : ℕ) (claim : E) : ChanM m (List E) := do
  let top := 4 * degree
  let low ← nextScalars (m := m) 3
  let high ← nextScalars (m := m) (top - 3)
  let c3 := (high.zip (List.range high.length)).foldl
    (fun acc (c, k) ↦ if (k + 4) % 3 = 0 then acc + c else acc) claim
  return low ++ [c3] ++ high

/-- **`sumcheck_pairs_drawn(claim, degree, vars, narrow)`** (π1-rec3, `SPEC-POINTS.md`): `vars` variables two at a
time, low first: pair `j`'s round polynomial, one challenge `z_j` (narrow when `narrow`), its two coordinates
`pairPoint z_j`; with `vars` odd a last plain round (`sumcheckDrawn` of `degree + 1` coefficients). The point, the
challenges, the last claim. -/
def sumcheckPairsDrawn (claim : E) (degree vars : ℕ) (narrow : Bool) : ChanM m (List E × List E × E) := do
  let mut point : Array E := #[]
  let mut challenges : Array E := #[]
  let mut claim := claim
  for _ in [0:vars / 2] do
    let message ← pairRoundPoly (m := m) degree claim
    let z ← sampleDrawn F narrow
    point := point ++ (pairPoint z).toArray
    challenges := challenges.push z
    claim := polyEval message z
  if vars % 2 = 1 then
    let (last, end_) ← sumcheckDrawn F claim (degree + 1) [none] narrow
    challenges := challenges ++ last.toArray
    point := point ++ last.toArray
    claim := end_
  return (point.toList, challenges.toList, claim)

end With

/-! ### The BLAKE2s circuit's walk (`flock.rs`'s `blake2s_row_values`, π1-rec2's terminal) -/

namespace Flock

/-- A 32-bit word of the walk: its bits' values. -/
abbrev WalkWord := Array E

/-- `RowValues::slots(base)`: the column weights at `base .. base + 32`. -/
def walkSlots (cw : Array E) (base : ℕ) : WalkWord := Array.ofFn (n := 32) fun b ↦ cw.getD (base + b.val) 0

/-- `RowValues::literal(value)`: the constant column's weight at each set bit of `value`. -/
def walkLiteral (cw : Array E) (value : ℕ) : WalkWord :=
  Array.ofFn (n := 32) fun b ↦ if value.testBit b.val then cw.getD constantColumn 0 else 0

/-- `xor(x, y)`. -/
def walkXor (x y : WalkWord) : WalkWord := Array.ofFn (n := 32) fun b ↦ x.getD b.val 0 + y.getD b.val 0

/-- `rotate_right(word, amount)`. -/
def walkRotr (w : WalkWord) (amount : ℕ) : WalkWord := Array.ofFn (n := 32) fun b ↦ w.getD ((b.val + amount) % 32) 0

/-- **`RowValues::add(x, y, carry_base)`**: the 31 carry rows of `x + y` (left `x_i + c`, right `y_i + c`, the carry
`c` the sum of the carry slots below `i`), and the sum's bits. -/
def walkAdd (cw left right : Array E) (x y : WalkWord) (carryBase : ℕ) : Array E × Array E × WalkWord := Id.run do
  let mut left := left
  let mut right := right
  let mut carry : E := 0
  let mut output : Array E := Array.replicate 32 0
  for bit in [0:32] do
    if bit < 31 then
      left := left.set! (carryBase + bit) (x.getD bit 0 + carry)
      right := right.set! (carryBase + bit) (y.getD bit 0 + carry)
    output := output.set! bit (x.getD bit 0 + y.getD bit 0 + carry)
    if bit < 31 then
      carry := carry + cw.getD (carryBase + bit) 0
  return (left, right, output)

/-- **`RowValues::add3(x, y, z, base)`**: the fused three-operand add, 31 majority rows then 30 ripple rows. -/
def walkAdd3 (cw left right : Array E) (x y z : WalkWord) (base : ℕ) : Array E × Array E × WalkWord := Id.run do
  let mut left := left
  let mut right := right
  let mut majority : Array E := Array.replicate 31 0
  for bit in [0:31] do
    left := left.set! (base + bit) (x.getD bit 0 + z.getD bit 0)
    right := right.set! (base + bit) (y.getD bit 0 + z.getD bit 0)
    majority := majority.set! bit (cw.getD (base + bit) 0 + z.getD bit 0)
  let rippleBase := base + 31
  let mut carry : E := 0
  let mut output : Array E := Array.replicate 32 0
  for bit in [0:32] do
    let q : E := if bit = 0 then 0 else majority.getD (bit - 1) 0
    let l := x.getD bit 0 + y.getD bit 0 + z.getD bit 0 + carry
    output := output.set! bit (l + q)
    if 1 ≤ bit ∧ bit ≤ 30 then
      left := left.set! (rippleBase + bit - 1) l
      right := right.set! (rippleBase + bit - 1) (q + carry)
      carry := carry + cw.getD (rippleBase + bit - 1) 0
  return (left, right, output)

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`zerocheck(log_n, k, fs)`**: `zerocheck`, the coordinates after the seven fixed ones drawn as `fs` has it. -/
def zerocheckFs (logN k : ℕ) (fs : FsShape := .main) : ChanM m (Option E × List E × E × E × E) := do
  let sampled ← drawRun F fs (logN - k - nFixed)
  let r : List (Option E) := (fixedChallenges ++ sampled).map some
  let (zSkip, claim) ← if k > 0 then do
      let coset ← nextScalars (m := m) (2 ^ k)
      let z ← sample F
      pure (some z, lagrangeInterpolate (2 ^ (k + 1)) (List.replicate (2 ^ k) 0 ++ coset) z)
    else pure (none, 0)
  let (chi, running) ← sumcheck F claim 3 r
  let vA ← nextScalar (m := m)
  let vB ← nextScalar (m := m)
  return (zSkip, chi, vA, vB, running + vA * vB)

theorem zerocheckFs_main (logN k : ℕ) : zerocheckFs F logN k .main = zerocheck F logN k := rfl

end With

end Flock

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem sumcheckDrawn_false (claim : E) (count : ℕ) (equalities : List (Option E)) :
    sumcheckDrawn F claim count equalities false = sumcheck F claim count equalities := rfl

/-- **`batch(fs, …)`**: `batch`, its rounds as `fs` has them: plain (`main`, `rec1`), plain and narrow (`rec2`), paired
and narrow (`rec3`: degree 2 a variable, no pending matrices). -/
def batchFs (fs : FsShape) (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E) := none)
    (pending : Option (Flock.Pending × List E) := none) :
    ChanM m (List (Commitment × Opening) × Option Flock.MatrixClaim) := do
  let lambda ← sample F
  let vars := (layouts.map (·.2.vars)).foldl max 0
  let (target, scale) := combined.foldl (fun (acc : E × E) (_, claim) ↦
    (acc.1 + acc.2 * claim.value, acc.2 * lambda)) (0, 1)
  let target := match pending with
    | some (p, _) => target + scale * p.claim
    | none => target
  let (r, last) ← match fs with
    | .rec3 => do
      let (r, _, last) ← sumcheckPairsDrawn F target 2 vars true
      pure (r, last)
    | .main | .rec1 | .rec2 => sumcheckDrawn F target 3 (List.replicate vars none) fs.narrow
  let values ← nextScalars (m := m) combined.length
  let matrices ← match pending with
    | some _ => do
      let a ← nextScalar (m := m)
      let b ← nextScalar (m := m)
      pure (some (a, b))
    | none => pure none
  let layoutOf (c : Commitment) : StackLayout := ((layouts.find? (·.1 == c)).map (·.2)).getD default
  let (sum, scale, openings, _) := (combined.zip values).foldl
    (fun (acc : E × E × Array (Commitment × Opening) × Option Combined) ((commitment, claim), value) ↦
      let (sum, scale, openings, bitSlice) := acc
      let layout := layoutOf commitment
      let weight := weightAt claim layout r ringMap
      let extension := (List.range' layout.vars (vars - layout.vars)).foldl
        (fun e j ↦ e * (1 + r.getD j 0)) 1
      let (mine, rest) := if commitment == .c1 then (bitSlice, none) else (none, bitSlice)
      (sum + scale * weight * extension * value, scale * lambda,
        openings.push (commitment, .point (r.take layout.vars) value mine), rest))
    (0, 1, #[], bitSlice)
  match pending, matrices with
  | some (p, flockPoint), some (a, b) =>
    let extension := (List.range' p.rounds (vars - p.rounds)).foldl (fun e j ↦ e * (1 + r.getD j 0)) 1
    if p.hasSlices then
      let (value, claim) := p.terminal r a b
      requireZero (m := m) (sum + scale * value * extension + last)
      return (openings.toList, some claim)
    else
      let (weights, claim) := p.combination r a b extension scale
      let relation : Relation := ⟨(weights.zip (List.range weights.length)).map
        (fun (c, i) ↦ ⟨.qflockBits, flockPoint, i, c⟩), sum + last⟩
      let combination := combine [relation] .c1 1
      let openings := openings.map fun (c, o) ↦ match c, o with
        | .c1, .point pt v _ => (c, .point pt v combination)
        | _, _ => (c, o)
      return (openings.toList, some claim)
  | _, _ =>
    requireZero (m := m) (sum + last)
    return (openings.toList, none)

theorem batchFs_main (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (bitSlice : Option Combined) (ringMap : Option (List E)) (pending : Option (Flock.Pending × List E)) :
    batchFs F .main combined layouts bitSlice ringMap pending = batch F combined layouts bitSlice ringMap pending :=
  rfl

end With

/-! ### The contract's IV binds the variant (`variant_bytes`, `contract_iv_for`) -/

/-! ### The whole verifier at a Fiat–Shamir shape -/

end UniStatement

end
