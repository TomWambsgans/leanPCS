-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Transcribes `quotient::protocol::reduce` (crates/membership/quotient/src/protocol.rs) and the smart constructors of
-- `crates/membership/evm/src/record.rs` (`Sym`'s `Add`, `Mul`, `frobenius`), adapted from leanVM
-- (https://github.com/leanEthereum/leanVM, branch PCS-openings-aggregation, commit 651453c6).
import Implementation.Interp

/-!
# The reduction, read off the graph

`quotient::protocol::reduce` again, over node indices: every operation the Rust verifier does on
its scalars is looked up in the emitted graph (`look`), after the folds `record.rs`'s `Sym` does on
constants (`add`, `mul`, `frob`). The program is `reduceIds`; `reduceIds_eq` checks, by evaluation
in the kernel, that it finds every node it asks for and that the three PCS claims the contract checks
declared (`claims`, resolved to their output words) are word for word the program's (`claimWords`: each
claim's root, out-of-domain answer, point and value), and `checkId_eq` that the value it requires nonzero
is `nonzero`'s. So the graph holds the Rust verifier's
computation in the order of `reduce`, and `Semantics.lean` can read its values off this program.

Nothing here is trusted: a node the program asks for and the graph lacks makes `reduceIds` `none`
and `reduceIds_eq` fail.
-/

namespace Implementation.Program

open Emitted

/-! ## Looking up nodes -/

/-- The first index, from `i` on, of a node in a list. -/
def findFrom (n : Node) : List Node → Nat → Option Nat
  | [], _ => none
  | m :: l, i => if m = n then some i else findFrom n l (i + 1)

/-- The index of a node in the graph. -/
def look (n : Node) : Option Nat := findFrom n nodes 0

/-- The constant at an index, if that node is one. -/
def constAt (i : Nat) : Option Nat :=
  match nodes[i]? with
  | some (.const c) => some c
  | _ => none

/-- `S::constant`. -/
def cnst (c : Nat) : Option Nat := look (.const c)

/-- `Sym + Sym`: two constants fold, zero is dropped, `x + x` is zero. -/
def add (a b : Nat) : Option Nat :=
  match constAt a, constAt b with
  | some x, some y => cnst (x ^^^ y)
  | _, _ =>
    if constAt a = some 0 then some b
    else if constAt b = some 0 then some a
    else if a = b then cnst 0
    else look (.add (min a b) (max a b))

/-- `Sym * Sym`: two constants fold, zero absorbs, one is dropped. -/
def mul (a b : Nat) : Option Nat :=
  match constAt a, constAt b with
  | some x, some y => cnst (mulE x y)
  | _, _ =>
    if constAt a = some 0 ∨ constAt b = some 0 then cnst 0
    else if constAt a = some 1 then some b
    else if constAt b = some 1 then some a
    else look (.mul (min a b) (max a b))

/-- `Sym::frobenius`. -/
def frob (a : Nat) : Option Nat :=
  match constAt a with
  | some x => cnst (frobE x)
  | none => look (.frob a)

/-! ## The transcript (`contract::Recorder`) -/

/-- The leaves: the constant one, the statement's eight `K`-words, the challenges, the out-of-domain answers and
the proof's other scalars, as `reduce` reads them. -/
structure Leaves where
  one : Nat
  s : List Nat
  oods : List Nat
  alpha : Nat
  beta : Nat
  mu : Nat
  t : Nat
  v : List Nat
  next : Nat
  rho : Nat
  deriving Repr, DecidableEq

/-- The transcript as the recorder writes it: the witness table's commitment (its root's two scalars, its
out-of-domain answer), three challenges, the quotient table's commitment, `t`, the three values and `next`,
`ρ`. -/
def chain : Option Leaves := do
  let seed ← look .seed
  let one ← cnst 1
  let s ← [0, 1, 2, 3, 4, 5, 6, 7].mapM fun k => look (.statement k)
  let r0 ← look (.root 0)
  let r1 ← look (.root 1)
  let wo ← look (.input 0)
  let st1 ← look (.hash seed [r0, r1, wo])
  let alpha ← look (.low st1)
  let st2 ← look (.hash st1 [])
  let beta ← look (.low st2)
  let st3 ← look (.hash st2 [])
  let mu ← look (.low st3)
  let t0 ← look (.root 2)
  let t1 ← look (.root 3)
  let tz ← look (.input 1)
  let st4 ← look (.hash st3 [t0, t1, tz])
  let t ← look (.low st4)
  let v ← [2, 3, 4].mapM fun i => look (.input i)
  let next ← look (.input 5)
  let st5 ← look (.hash st4 (v ++ [next]))
  let rho ← look (.low st5)
  pure { one, s, oods := [wo, tz], alpha, beta, mu, t, v, next, rho }

/-- The leaves of the graph. -/
def leaves₀ : Leaves :=
  { one := 1, s := [2, 3, 4, 5, 6, 7, 8, 9], oods := [12, 21], alpha := 14, beta := 16, mu := 18, t := 23,
    v := [24, 25, 26], next := 27, rho := 29 }

set_option maxRecDepth 20000 in
theorem chain_eq : chain = some leaves₀ := by decide +kernel

/-! ## The arithmetic of `reduce` -/

/-- `w_0 .. w_n`: `w_{k+1} = w_k^2 + w_k`. -/
def wChain (t : Nat) : Nat → Option (List Nat)
  | 0 => some [t]
  | n + 1 => do
    let ws ← wChain t n
    let w := ws.getLastD 0
    let sq ← mul w w
    let w' ← add sq w
    pure (ws ++ [w'])

/-- A fold of `reduce`, over a list of indices. -/
def foldO (f : Nat → Nat → Option Nat) : Nat → List Nat → Option Nat
  | acc, [] => some acc
  | acc, k :: ks => do
    let acc' ← f acc k
    foldO f acc' ks

/-- A map of `reduce`, over a list of indices. -/
def mapO (f : Nat → Option Nat) : List Nat → Option (List Nat)
  | [] => some []
  | k :: ks => do
    let r ← f k
    let rs ← mapO f ks
    pure (r :: rs)

/-- `x^(2^n)`, by `n` squarings. -/
def squareN (x : Nat) : Nat → Option Nat
  | 0 => some x
  | n + 1 => do
    let y ← squareN x n
    mul y y

/-- One round of `inverse`'s loop: `ones = norm^(2^k - 1)` becomes `norm^(2^(2k+1) - 1)`. -/
def invRound (norm : Nat) (p : Nat × Nat) : Option (Nat × Nat) := do
  let shifted ← squareN p.1 p.2
  let ones ← mul shifted p.1
  let sq ← mul ones ones
  let ones' ← mul sq norm
  pure (ones', 2 * p.2 + 1)

/-- Five rounds. -/
def invRounds (norm : Nat) : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, p => some p
  | n + 1, p => do
    let q ← invRound norm p
    invRounds norm n q

/-- `protocol::inverse`: `x^-1 = m · N(x)^(2^64 - 2)`, `m = x^(2^64) x^(2^128)`, `N(x) = x m`. -/
def inverse (x : Nat) : Option Nat := do
  let f1 ← frob x
  let f2 ← frob f1
  let m ← mul f1 f2
  let norm ← mul x m
  let p ← invRounds norm 5 (norm, 1)
  let sq ← mul p.1 p.1
  mul m sq

/-- The prefix products: `prefix[i]` the product of the first `i` values. -/
def prefixes : Nat → List Nat → Option (List Nat)
  | acc, [] => some [acc]
  | acc, d :: ds => do
    let acc' ← mul acc d
    let rest ← prefixes acc' ds
    pure (acc :: rest)

/-- The inverses, from the last: `inverses[i] = running · prefix[i]`, then `running ·= d_i`. The
pairs `(prefix[i], d_i)` come last first; the result too. -/
def backInv : Nat → List (Nat × Nat) → Option (List Nat)
  | _, [] => some []
  | running, (p, d) :: rest => do
    let inv ← mul running p
    let running' ← mul running d
    let tail ← backInv running' rest
    pure (inv :: tail)

/-- What the first stage of `reduce` leaves: the `w` chain, the gate, the rows' polynomial, the denominators'
pieces (`d`, `d'`, their product, `ζ = Z t`), the conic's `a`, `b` and the constant `θ`. -/
structure StageA where
  w : List Nat
  gate : Nat
  rows : Nat
  d : Nat
  dNext : Nat
  product : Nat
  zeta : Nat
  theta : Nat
  conicA : Nat
  conicB : Nat
  deriving Repr, DecidableEq

/-- `reduce`, up to the denominators: `w_k(t)`, the gate `V + Y + C + X·C` of the values read, the rows'
polynomial, `d`, `d'`, `ζ`, and `witness_conic`. -/
def stageA (L : Leaves) : Option StageA := do
  let m := 24
  let one := L.one
  let t := L.t
  let w ← wChain t m
  let x := L.v.getD 0 0
  let c := L.v.getD 1 0
  let vy := L.v.getD 2 0
  -- `gate = vy + c + x · c`
  let g1 ← add vy c
  let g2 ← mul x c
  let gate ← add g1 g2
  -- the rows' polynomial
  let zr ← cnst 0
  let rows ← foldO (fun acc k => do
      let tk ← cnst (tau.getD k 0)
      let p ← mul tk (w.getD k 0)
      add acc p) zr (List.range (m - 1))
  -- the copy identity's denominators
  let ax ← add L.alpha x
  let bt ← mul L.beta t
  let d ← add ax bt
  let bn ← mul L.beta L.next
  let dNext ← add ax bn
  let product ← mul d dNext
  let zeta ← mul (w.getD m 0) t
  -- `witness_conic`: `((t + ω θ)(1 + ρ) + ρ, θ (1 + ρ))`
  let theta ← cnst (beta.getD 1 0)
  let rho1 ← add one L.rho
  let ot ← mul (w.getD 1 0) theta
  let tot ← add t ot
  let ca0 ← mul tot rho1
  let conicA ← add ca0 L.rho
  let conicB ← mul theta rho1
  pure { w, gate, rows, d, dNext, product, zeta, theta, conicA, conicB }

/-- What the second stage leaves: the denominators, their prefix products, and their product. -/
structure StageB where
  dens : List Nat
  pre : List Nat
  total : Nat
  deriving Repr, DecidableEq

/-- `reduce`'s denominators (every `1 + w_k` below the digit, `1 + ζ`, `ζ + d d'`, the rows' polynomial, every
`t + p_k`, `a + b`) and their prefix products: the value it requires nonzero. -/
def stageB (L : Leaves) (A : StageA) : Option StageB := do
  let ws ← mapO (fun k => add L.one (A.w.getD k 0)) (List.range 24)
  let oz ← add L.one A.zeta
  let zp ← add A.zeta A.product
  let ps ← mapO (fun k => do
      let p ← cnst (pinPoints.getD k 0)
      add L.t p) (List.range 11)
  let ab ← add A.conicA A.conicB
  let dens := ws ++ [oz, zp, A.rows] ++ ps ++ [ab]
  let pre ← prefixes L.one dens
  pure { dens, pre, total := pre.getD dens.length 0 }

/-- What `reduce` leaves, as indices: each claim's point and value. -/
structure Out where
  wPt : List Nat
  wVal : Nat
  fPt : List Nat
  fVal : Nat
  cPt : List Nat
  cVal : Nat
  deriving Repr, DecidableEq

/-- The pins' term of anchor `k` (`reduce`'s loop): a word's `λ_k`-weighted statement word, the constant `λ_k v_k`
of `1` and `3`, nothing for `0`. -/
def pinStep (L : Leaves) (pinInv : Nat → Nat) (acc k : Nat) : Option Nat :=
  if k < 8 then do
    let lam ← cnst (pinWeights.getD k 0)
    let weight ← mul (L.s.getD k 0) lam
    let term ← mul weight (pinInv k)
    add acc term
  else if k = 8 then some acc
  else do
    let weight ← cnst (mulE (pinWeights.getD k 0) (if k = 9 then 1 else 3))
    let term ← mul weight (pinInv k)
    add acc term

/-- `reduce`'s one inversion, and the claims. -/
def stageC (L : Leaves) (A : StageA) (B : StageB) : Option Out := do
  let m := 24
  let one := L.one
  let t := L.t
  let w := A.w
  let x := L.v.getD 0 0
  let c := L.v.getD 1 0
  let vy := L.v.getD 2 0
  let dens := B.dens
  let running ← inverse B.total
  let invsRev ← backInv running ((List.range dens.length).reverse.map fun i => (B.pre.getD i 0, dens.getD i 0))
  let inverses := invsRev.reverse
  let u0 ← mapO (fun k => mul (w.getD k 0) (inverses.getD k 0)) (List.range m)
  let um ← mul A.zeta (inverses.getD m 0)
  let u := u0 ++ [um]
  let copyInverse := inverses.getD (m + 1) 0
  let rowsInverse := inverses.getD (m + 2) 0
  let pinInv (k : Nat) : Nat := inverses.getD (m + 3 + k) 0
  let conicInverse := inverses.getD (m + 3 + 11) 0
  let middle ← foldO (fun acc k => mul acc (inverses.getD k 0)) (inverses.getD 2 0) (List.range' 3 (m - 3))
  let ws0 ← mul middle (inverses.getD 0 0)
  let wiringScale ← mul ws0 (inverses.getD 1 0)
  let tableScale ← mul wiringScale (inverses.getD m 0)
  -- `g(t) = gate / Z_R + (w + v) / Z_P`
  let pp ← foldO (fun acc k => mul acc (pinInv k)) one (List.range 11)
  let p0 ← mul x pp
  let pinned ← foldO (pinStep L pinInv) p0 (List.range 11)
  let gr ← mul A.gate rowsInverse
  let g ← add gr pinned
  -- the copy claim
  let sc ← cnst Emitted.scale
  let kappa ← mul A.product copyInverse
  let cv0 ← mul sc tableScale
  let cv1 ← mul cv0 t
  let dd ← add A.d A.dNext
  let mz ← mul L.mu (w.getD m 0)
  let mzg ← mul mz g
  let r ← add dd mzg
  let cv2 ← mul cv1 r
  let cVal ← mul cv2 copyInverse
  -- the witness claim on the conic (`witness_weights`)
  let z1 ← mul A.conicA conicInverse
  let omega := w.getD 1 0
  let rho1 ← add one L.rho
  let z11 ← add one z1
  let e00 ← mul rho1 z11
  let e01 ← mul rho1 z1
  let e11 ← mul L.rho z1
  let tho ← mul A.theta omega
  let k30 ← add t tho
  let k31 ← add k30 A.theta
  let k3 ← add k31 one
  let tw ← mul t omega
  let twe ← mul tw e00
  let l0 ← add e11 twe
  let we ← mul omega e00
  let ewe ← add e01 we
  let kk ← mul k3 ewe
  let lambda1 ← add l0 kk
  let lx ← add e00 lambda1
  let lvy ← add ewe lambda1
  let o1 ← mul lx x
  let o2 ← mul lambda1 c
  let o3 ← add o1 o2
  let o4 ← mul lvy vy
  let opened ← add o3 o4
  let wVal ← mul opened middle
  let fVal ← mul L.next wiringScale
  let cy0 ← cnst y0
  let cy1 ← cnst y1
  pure {
    wPt := [L.rho, z1] ++ (u.drop 2).take (m - 2), wVal
    fPt := u.take m, fVal
    cPt := u ++ [cy0, cy1, kappa], cVal }

/-- **`reduce`, over the graph.** -/
def reduceIds : Option Out := do
  let L ← chain
  let A ← stageA L
  let B ← stageB L A
  stageC L A B

/-- The value `reduce` requires nonzero. -/
def checkId : Option Nat := do
  let L ← chain
  let A ← stageA L
  let B ← stageB L A
  pure B.total

/-- **The words of the three claims** from what `reduce` leaves (`quotient::recorded`): each its root's word,
its out-of-domain answer's, its point's and its value's; in the order of `Claims::on`, the roots of the witness
table and of the quotient table the calldata's words at `64` and `96`, the circuit's commitment the stored one. -/
def claimWords (L : Leaves) (o : Out) : List (Word × Word × List Word × Word) :=
  [(.calldata 64, .node (L.oods.getD 0 0), o.wPt.map .node, .node o.wVal),
   (.storedRoot, .storedOod, o.fPt.map .node, .node o.fVal),
   (.calldata 96, .node (L.oods.getD 1 0), o.cPt.map .node, .node o.cVal)]

/-- An output word by its index (`Word.const 0` past the end). -/
def outAt (i : Nat) : Word := outputs.getD i (.const 0)

/-- A claim of `Graph.lean`'s `claims`, its indices resolved to the output words. -/
def resolve (c : Nat × Nat × List Nat × Nat) : Word × Word × List Word × Word :=
  (outAt c.1, outAt c.2.1, c.2.2.1.map outAt, outAt c.2.2.2)

/-- **The graph is `reduce`'s**: every node the program asks for is in the graph, and the claims the
contract checks are, word for word, the program's. -/
theorem reduceIds_eq : (do let L ← chain; let o ← reduceIds; pure (claimWords L o)) =
    some (claims.map resolve) := by
  decide +kernel

/-- The value it requires nonzero is the one the contract requires nonzero. -/
theorem checkId_eq : checkId.map (fun c => [c]) = some nonzero := by
  decide +kernel

end Implementation.Program
