-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `crates/leanvm/rec/src/pi2/verifier.rs`
-- (`NAME`, `frobenius`, `inverse`, `extension`, `reduce`'s transcript, `statement_words`, `verify`) and
-- `crates/leanvm/rec/src/pi2/prover.rs` (`stack_vars`, `QUOTIENT_SLOTS`, `EMPTY_SLOTS`, `iv`), π2v4
-- (`leanvm-rec-pi2v4`, main 7e6d353c), on the EIP draft's PCS claims (`crates/pcs_claim`: each commitment a root and its
-- out-of-domain answer, one point claim per claim; the claims and their openings are `Calls.lean`'s and
-- `Security.lean`'s). The channel is `formal/UniStatement`'s (`KeccakChannel`).
import RecStatement.Spec
import RecStatement.Core
import UniKeccak.Opening

/-!
# π2's verifier on calldata

**The transcript** (`KeccakChannel`, `PI2.md` §2): the seed `keccak(NAME ‖ IV ‖ public input ‖ frame words)`,
`NAME = "leanvm-rec-pi2v4"`, the frame words the payloads the `Read.frame`s name (the Keccak-256s of π1's claims π2's
circuit hashes: all three at 128 signatures); the stream holds the public data of the claims the contract encodes
(`Read`s: π1's roots, π1's claims' elements, a narrow one as its 20 bytes: none at 128 signatures), `W`'s commitment (its root, then its out-of-domain
answer), then `α, β, γ` are drawn; `Q`'s commitment, then `t`; the `2^r` fold values, `ξ = κ(t) + βσ(t)` and
`s = P(t)`, then `ρ`. The first challenge hashes the state
and everything read before it: the public data is bound there. Then the arithmetic (`CoreSpec.run`, over `E`, its
constants `Spec.of`'s: `Spec.core`), which requires one value nonzero (`Out.all`, the contract's one nonzero check).

**The IV** (`prover::iv`): `keccak("leanvm-rec-iv-v3" ‖ π1's contract IV ‖ the setup's root ‖ the setup's
out-of-domain answer ‖ the circuit's digest ‖ log_n)`.

**The stacks** (`PI2.md` §2): `W` (`w` in its leading lanes), `Q` (`m + 4` variables: the position, two slot bits
`b_0, b_1`, two limb bits: sixteen slots of `N`, `b_0 + 2 b_1 + 4 limb`; for limbs `0..2` `H = x h` at `(0, 0)`, `q`'s
digits at `(1, 0)`, `(0, 1)`, `G` at `(1, 1)`; at limb code `3` `P`, `q_P`'s digits, `S`; `G`, `S` the honest
prover's zeros), the setup (`κ` then `κ + σ`),
on stacks of at least `2^24` words (`2^15` below `2^20` positions: `stackVars`); every claim a point of its whole
stack.

**The inverse**: the arithmetic takes the field's; the Rust's is the norm's (`normInverse`: two Frobenius maps
from the limbs' shifts, Itoh–Tsujii on the norm in `K`), the same value for a nonzero element (the runner checks it on
every vector's `Out.all`).
-/

namespace RecStatement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-! ## `E`'s helpers -/

/-- `Y`, the extension's generator (`F192::Y`). -/
def yE : E := UniStatement.eNew 0 1 0

/-- `x >> 64 = c_1 + c_2 Y` and `x >> 128 = c_2` (`Limbs::shifted`). -/
def shifted (x : E) : E × E :=
  (UniStatement.eNew (x.limb 1).lane (x.limb 2).lane 0, UniStatement.eNew (x.limb 2).lane 0 0)

/-- **`frobenius(x)`** `= x^(2^64)`: `x + (Y + Y²)(x >> 64) + (1 + Y²)(x >> 128)`. -/
def frobenius (x : E) : E :=
  let (u, v) := shifted x
  x + (yE + yE * yE) * u + (1 + yE * yE) * v

/-- **`inverse(x)`**, by the norm: `m = x^(2^64) x^(2^128)`, `N = x m` in `K`, `N^-1 = N^(2^64 − 2)` by the chain
`1, 2, 3, 6, 7, …, 62, 63`, then `x^-1 = m N^-1`. -/
def normInverse (x : E) : E := Id.run do
  let f := frobenius x
  let m := f * frobenius f
  let norm := x * m
  let mut t := norm
  let mut k := 1
  for bit in (List.range 5).reverse do
    let mut s := t
    for _ in [0:k] do
      s := s * s
    t := s * t
    k := 2 * k
    if (63 >>> bit) % 2 = 1 then
      t := t * t * norm
      k := k + 1
  return m * (t * t)

/-- **`extension()`**: the extension's coordinates `(Y/(1 + Y), Y²/(1 + Y²))` and the scale `1/((1 + Y)(1 + Y²))`
(`quotient::protocol::extension`). -/
def extension : (E × E) × E :=
  let y2 := yE * yE
  let d0 := 1 + yE
  let d1 := 1 + y2
  ((yE * d0⁻¹, y2 * d1⁻¹), (d0 * d1)⁻¹)

/-- `Y³` (`F192::Y` cubed): limb code `3`'s weight at `(y_0, y_1)`, over the scale. -/
def yCubeE : E := yE * yE * yE

/-- `base::<S>(x)`: an element of `K` in `E`. -/
def kE (x : K) : E := ofK x

/-! ## The constants over `E` -/

def Coeff.toF (c : Coeff) : CoeffF E := ⟨c.field, c.gamma⟩

def Lin.toF (l : Lin) : LinF E := ⟨l.terms.map fun t ↦ (t.1.toF, t.2), l.constant.map Coeff.toF⟩

def Formula.toF (f : Formula) : FormulaF E :=
  ⟨f.lin.toF, f.products.map fun p ↦ (p.1.toF, p.2.1.toF, p.2.2.toF)⟩

/-- **The arithmetic's constants over `E`**: `Spec.of`'s, the extension's, the points `ω_i = point_e(i)`. -/
def Spec.core (s : Spec) : CoreSpec E :=
  { logN := s.logN
    logRow := s.logRow
    pairs := s.pairs.map fun p ↦ (p.logRows, kE p.z)
    groups := s.groups.map fun g ↦ ⟨g.role, g.formula.toF, g.pulls, g.pairs⟩
    c := s.c.map kE
    phi := s.phi.map fun kt ↦ (kt.1, kt.2.map fun yl ↦ (yl.1, yl.2.toF))
    maxGamma := s.maxGamma
    y0 := extension.1.1
    y1 := extension.1.2
    scale := extension.2
    yCube := yCubeE
    ω := UniStatement.pointE }

/-! ## The stacks, the IV -/

/-- `MIN_LOG_STACK`, `MIN_CERTIFIED_STACK`, `CERTIFIED_FROM` (`prover.rs`). -/
def minLogStack : ℕ := 15
def minCertifiedStack : ℕ := 24
def certifiedFrom : ℕ := 20

/-- **`Q`'s slots** (`QUOTIENT_SLOTS`, `h_slot`, `q_slot`, `P_SLOT`, `QP_SLOT`, `EMPTY_SLOTS`): slot
`b_0 + 2 b_1 + 4 limb`, `H`'s limb `l` at `4 l`, `q`'s digits at `4 l + 1, 4 l + 2`, `G`'s at `4 l + 3`; `P` at `12`,
`q_P` at `13, 14`, `S` at `15`. The honest prover leaves `G`'s and `S`'s slots zero (`emptySlots`); any prover's are
handled by the identity's layout (`PI2.md` §7: `G` weighs `x² Z_V³`, `S(t) = 0` is in the pushes' claim). -/
def quotientSlots : List ℕ := [0, 1, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14]

/-- The slots the honest prover leaves zero: `G`'s three limbs, then `S`. -/
def emptySlots : List ℕ := [3, 7, 11, 15]

/-- The IV's tag. -/
def ivTag : List UInt8 := "leanvm-rec-iv-v3".toUTF8.toList

/-- The transcript's name (`NAME`). -/
def name : List UInt8 := "leanvm-rec-pi2v4".toUTF8.toList

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`iv(pi1_iv, digest, setup_root, setup_ood, log_n)`** over `F`: the Keccak-256 of the tag, π1's contract IV, the
setup's root (its 32 bytes) and out-of-domain answer (24 bytes, `UniKeccak.elementBytes24`), the circuit's digest and
`log_n` (a byte). -/
def ivWith (pi1Iv setupRoot : List UInt8) (setupOod : E) (digest : List UInt8) (logN : ℕ) : m (List UInt8) := do
  let d ← keccak256With F (ivTag ++ pi1Iv ++ setupRoot ++ UniKeccak.elementBytes24 setupOod ++ digest ++
    [logN.toUInt8])
  return digestBytes d

end With

/-- The IV over Keccak-f[1600]: the deployed contract's constant. -/
def iv (pi1Iv setupRoot : List UInt8) (setupOod : E) (digest : List UInt8) (logN : ℕ) : List UInt8 :=
  Id.run (ivWith (m := Id) (fun x ↦ pure (keccakF1600 x)) pi1Iv setupRoot setupOod digest logN)

/-! ## The run -/

/-- `cantor_beta1()`: `x^((2^64 − 1)/3)`, or it plus one, the one with its low bit clear (`β_1² + β_1 = 1`;
`UniStatement.cantorBeta1`, π1-rec4's). -/
def cantorBeta1 : E := UniStatement.cantorBeta1

/-- **`pair_point(z)`**: `(z + β_1 (z² + z), z² + z)`. -/
def pairPoint (z : E) : E × E :=
  let y1 := z * z + z
  (z + cantorBeta1 * y1, y1)

/-- **What the verifier leaves** (`Reduced`): the public scalars, their pair points, `W`'s and `Q`'s roots (each
two halves) and out-of-domain answers, what the transcript gave the arithmetic, and every value the arithmetic
computes. -/
structure Reduced where
  scalars : List E
  pairPoints : List (E × E)
  roots : (E × E) × (E × E)
  oods : E × E
  inputs : Inputs E
  out : Out E

/-- `W`'s claim: `(ρ, ρ², …, ρ^(2^(r−1)), w_r, …, w_{m−1})`, value `Σ_k eq(ρ⃗, k) a_k`. -/
def Reduced.witness (r : Reduced) : List E × E := (r.out.witnessPoint, r.out.fold)

/-- `Q`'s identity claim at `(u_0, …, u_{m−1}, z_0, z_1, y_0, y_1)`. -/
def Reduced.quotient (r : Reduced) : List E × E := (r.out.quotientPoint, r.out.quotientValue)

/-- `Q`'s pushes' claim at `(u_0, …, u_{m−1}, ρ, z'_1, 1, 1)`. -/
def Reduced.pushes (r : Reduced) : List E × E := (r.out.pushesPoint, r.out.pushesValue)

/-- The setup's claim at `(w_0, …, w_{m−1}, β)`, value `ξ`. -/
def Reduced.setup (r : Reduced) : List E × E := (r.out.setupPoint, r.inputs.ξ)

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`next_narrow`**: 20 bytes, big-endian, `c2` its first 4, `c1` the next 8, `c0` the last 8. -/
def nextNarrow : UniStatement.ChanM m E := do
  let b ← UniStatement.takeBytes (m := m) 20
  return UniStatement.eNew (UniStatement.beWordAt b 12) (UniStatement.beWordAt b 4)
    ((List.range 4).foldl (fun acc k ↦ (acc <<< 8) ||| (b.getD k 0).toUInt64) 0)

/-- **`reduce`**: the public data (a frame read `Read.frame p` the payload `frameAt p`'s four big-endian words: the
contract's frame of PCS claims), `W`'s root and out-of-domain answer, `α, β, γ`, `Q`'s, `t`, the fold values, `ξ` and
`s`, `ρ`; then the arithmetic. (The Rust's `next_frame` pops the frame words in order, and errs on none left; the
contract hands the verifier its frame reads' payloads in that order, so they are `frameAt` of each read's payload.) -/
def reduceWith (s : Spec) (statement : List E) (frameAt : ℕ → List UInt8) : UniStatement.ChanM m Reduced := do
  let mut pubs := statement
  for rd in s.reads do
    match rd with
    | .integer b => pubs := pubs ++ [UniStatement.eK (UInt64.ofNat (← UniStatement.nextInteger (m := m) b))]
    | .root =>
      let (lo, hi) ← UniStatement.nextRoot (m := m)
      pubs := pubs ++ [lo, hi]
    | .scalar => pubs := pubs ++ [← UniStatement.nextScalar (m := m)]
    | .narrow => pubs := pubs ++ [← nextNarrow (m := m)]
    | .frame p => pubs := pubs ++ UniStatement.publicWordsOf (frameAt p)
  let wRoot ← UniStatement.nextRoot (m := m)
  let wOod ← UniStatement.nextScalar (m := m)
  let α ← UniStatement.sample F
  let β ← UniStatement.sample F
  let γ ← UniStatement.sample F
  let qRoot ← UniStatement.nextRoot (m := m)
  let qOod ← UniStatement.nextScalar (m := m)
  let t ← UniStatement.sample F
  let a ← UniStatement.nextScalars (m := m) (2 ^ s.logRow)
  let ξ ← UniStatement.nextScalar (m := m)
  let sv ← UniStatement.nextScalar (m := m)
  let ρ ← UniStatement.sample F
  let inp : Inputs E := ⟨pubs, α, β, γ, t, a, ξ, sv, ρ⟩
  return ⟨pubs, pubs.map pairPoint, (wRoot, qRoot), (wOod, qOod), inp, s.core.run inp⟩

/-- **A run's outcome**: the result (the reduction, or the stream's error) and the channel at the end. -/
structure Outcome where
  result : Except UniStatement.UniError Reduced
  chan : UniStatement.Chan

/-- **The verdict**: no error, and the value the verifier requires nonzero is (the inversion's). -/
def Outcome.accepts (o : Outcome) : Bool :=
  match o.result with
  | .ok r => r.out.all != 0
  | .error _ => false

/-- **π2's verifier on calldata** over `F` (`verify`): the seed of the IV, the public input and the frame words (the
frame reads' payloads, in order), the reduction, nothing of the stream left. -/
def runWith (s : Spec) (iv publicInput : List UInt8) (frameAt : ℕ → List UInt8) (stream : Array UInt8) :
    m Outcome := do
  let seed ← keccak256With F (name ++ iv ++ publicInput ++ (frameReads s.reads).flatMap frameAt)
  let walk : UniStatement.ChanM m Reduced := do
    let r ← reduceWith F s (UniStatement.publicWordsOf publicInput) frameAt
    UniStatement.finish (m := m)
    return r
  let (result, chan) ← (walk.run).run (UniStatement.Chan.start seed stream)
  return ⟨result, chan⟩

end With

/-- The run over Keccak-f[1600]: the deployed contract's computation. -/
def run (s : Spec) (iv publicInput : List UInt8) (frameAt : ℕ → List UInt8) (stream : Array UInt8) : Outcome :=
  Id.run (runWith (m := Id) (fun x ↦ pure (keccakF1600 x)) s iv publicInput frameAt stream)

end RecStatement
