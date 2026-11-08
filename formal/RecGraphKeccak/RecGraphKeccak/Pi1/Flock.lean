-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Transcribed, in the Rust's operation order, from
-- `crates/leanvm_flock_gas/src/flock_min.rs` (`front_with`, `verify_walked_with::<S, Keccak>`) and
-- `crates/leanvm_flock_gas/src/keccak_flock.rs` (`structured_terminal`, `grouped`).
import RecGraph.Pi1.Flock
import UniKeccak.Terminal

/-!
# The Keccak VM's π1-rec3 verifier as a program: Flock on the Keccak-f block

`flock_min::verify_walked_with::<S, Keccak>` on the recorder: the zerocheck (`RecGraph.Pi1.zerocheck`, unchanged),
the lincheck's `17 − 6 = 11` rounds (`frontK`), the structured terminal (`structuredTerminalS`,
`keccak_flock::structured_terminal` operation for operation: its memoised partial correlations, its `S::sum`s as
lazy folds from `S::zero()`, each `std::array::from_fn` in index order) required zero with `r_lc`, then the ring
switch's end in tower order (`RecGraph.Pi1.ringEnd`, unchanged). The constants (`rc`, `rho`, `source`,
`shiftOffsets`, `xQuad`, the roles) are `UniKeccak`'s.
-/

namespace RecGraphKeccak.Pi1

open LeanVM.Parameters UniStatement UniStatement.Flock RecGraph RecGraph.Pi1

/-- `WalkedCircuit::lincheck_rounds` of the Keccak-f block: `17 − 6`. -/
def lincheckRoundsK : Nat := keccakR1csLogSize - packing

/-- **`S::sum(xs.map(f))`**, the iterator lazy: `S::zero()`, then each item made and added. -/
def sumL {α : Type} (xs : List α) (f : α → Prog Sym) : Prog Sym := do
  let mut acc ← zero
  for x in xs do
    let v ← f x
    acc ← add acc v
  return acc

/-- **`front_with(log_n, variant, 17)`**: the zerocheck, the row point's split (the skip, the packing bits left to
rounds, the block's 11 word bits, the instance bits), the lincheck (`α`, 11 rounds), the 64 slices. -/
def frontK (logN k : Nat) (fs : FsShape) : Prog FrontS := do
  let (zSkip, chi, vA, vB, vC) ← zerocheck logN k fs
  let rowLow := chi.take (packing - k)
  let rest := chi.drop (packing - k)
  let chiIn := rest.take lincheckRoundsK
  let chiRest := rest.drop lincheckRoundsK
  let alpha ← sample
  let t1 ← mul alpha vB
  let s1 ← add vA t1
  let a2 ← pow alpha 2
  let t2 ← mul a2 vC
  let s2 ← add s1 t2
  let a3 ← pow alpha 3
  let claim ← add s2 a3
  let (roundChallenges, rLc) ← sumcheckDrawn claim 3 (List.replicate lincheckRoundsK none) false
  let chiInPrime := roundChallenges.reverse
  let slices ← nextScalars kBits
  return ⟨zSkip, rowLow, chiIn, chiInPrime, chi, alpha, rLc, slices, chiInPrime ++ chiRest⟩

/-- **`grouped(n, weights, x)`**: `Σ_(g < 4, 8g < n) weights[g] · Σ_(8g ≤ q < min(n, 8g + 8)) x(q)`. -/
def groupedS (n : Nat) (weights : Array Sym) (x : Nat → Prog Sym) : Prog Sym :=
  sumL ((List.range 4).filter fun g ↦ 8 * g < n) fun g ↦ do
    let inner ← sumL (List.range' (8 * g) (min n (8 * g + 8) - 8 * g)) x
    mul (weights.getD g 0) inner

/-- `lane_of(q, role) = (4q + role) mod 32`. -/
def laneOf (q role : Nat) : Nat := (4 * q + role) % 32

/-- **`structured_terminal(z_skip, row_low, chi_in, chi_in', s, α)`** on the recorder, in the Rust's order. -/
def structuredTerminalS (zSkip : Option Sym) (rowLow chiIn chiInPrime s : List Sym) (alpha : Sym) : Prog Sym := do
  let k := packing - rowLow.length
  let o ← one
  let p := max k 3
  let lag ← match zSkip with
    | some z => lagrangeWeights (2 ^ k) z
    | none => pure [o]
  let mid := rowLow.take (p - k)
  let high := rowLow.drop (p - k)
  let midK ← eqKernel mid
  let mut eLow : Array Sym := #[]
  for m in midK.toList do
    for l in lag do
      eLow := eLow.push (← mul l m)
  let eHigh ← eqKernel high
  let lo := 2 ^ p
  let nHi := 2 ^ (packing - p)
  let eAt (z : Nat) : Prog Sym := mul (eLow.getD (z % lo) 0) (eHigh.getD (z / lo) 0)
  let needed := UniKeccak.shiftOffsets
  let sA := s.toArray
  let mut partial_ : Array (Option (List Sym)) := Array.replicate lo none
  let z0 ← zero
  let mut corr : Array Sym := Array.replicate 64 z0
  for off in (List.range 64).filter fun off ↦ needed.getD off false do
    let ol := off % lo
    let oh := off / lo
    let q ← match partial_.getD ol none with
      | some q => pure q
      | none => do
        let mut q : Array Sym := #[]
        for m in List.range nHi do
          q := q.push (← sumL (List.range lo) fun zl ↦
            mul (eLow.getD zl 0) (sA.getD ((lo * m + zl + 64 - ol) % 64) 0))
        pure q.toList
    partial_ := partial_.set! ol (some q)
    corr := corr.set! off (← sumL (List.range nHi) fun zh ↦
      mul (eHigh.getD zh 0) (q.getD ((zh + nHi - oh) % nHi) 0))
  let es := corr.getD 0 0
  let lr ← eqKernel (chiIn.take 5)
  let rd ← eqKernel (chiIn.drop 6)
  let lh ← eqKernel (chiInPrime.take 5)
  let rh ← eqKernel (chiInPrime.drop 6)
  let kr5 := chiIn.getD 5 0
  let kh5 := chiInPrime.getD 5 0
  let kd0 ← add o kr5
  let kd : Array Sym := #[kd0, kr5]
  let kh0 ← add o kh5
  let kh : Array Sym := #[kh0, kh5]
  let mut krG : Array Sym := #[]
  for g in List.range 4 do
    krG := krG.push (← mul (kd.getD (g &&& 1) 0) (rd.getD (g >>> 1) 0))
  let mut khG : Array Sym := #[]
  for g in List.range 4 do
    khG := khG.push (← mul (kh.getD (g &&& 1) 0) (rh.getD (g >>> 1) 0))
  let mut krhG : Array Sym := #[]
  for g in List.range 4 do
    krhG := krhG.push (← mul (krG.getD g 0) (khG.getD g 0))
  let mut rx : Array Sym := #[]
  for q in List.range UniKeccak.lanes do
    rx := rx.push (← mul (lr.getD (laneOf q UniKeccak.roleX) 0) (krG.getD (q >>> 3) 0))
  let mut pc : Array Sym := #[]
  for q in List.range UniKeccak.lanes do
    pc := pc.push (← mul (lh.getD (laneOf q UniKeccak.roleC) 0) (khG.getD (q >>> 3) 0))
  let sumLr ← sumL (List.range UniKeccak.lanes) fun l ↦ pure (lr.getD l 0)
  let sumRdA ← sumL (List.range' 2 (UniKeccak.rounds - 1)) fun f ↦ pure (rd.getD f 0)
  let sumRdT ← add sumRdA (rd.getD (UniKeccak.rounds + 1) 0)
  let t1 ← mul (kd.getD 0 0) sumLr
  let tOne ← mul t1 sumRdT
  let mut rcMid ← zero
  let mut rcLast ← zero
  for z in List.range 64 do
    let rs := (List.range UniKeccak.rounds).filter fun j ↦ ((UniKeccak.rc.getD j 0) >>> z.toUInt64) &&& 1 == 1
    if rs.isEmpty then continue
    let ez ← eAt z
    let midSum ← sumL (rs.filter (· < UniKeccak.rounds - 1)) fun j ↦ pure (rd.getD (j + 2) 0)
    let em ← mul ez midSum
    rcMid ← add rcMid em
    if rs.contains (UniKeccak.rounds - 1) then
      rcLast ← add rcLast ez
  let r1 ← mul (lr.getD 0 0) (kd.getD 1 0)
  let r2 ← mul r1 rcMid
  let r3 ← mul (rx.getD 0 0) rcLast
  let rcOne ← add r2 r3
  let rd01 ← add (rd.getD 0 0) (rd.getD 1 0)
  let ys ← sumL (List.range 8) fun a ↦ pure (lr.getD (laneOf a UniKeccak.roleY) 0)
  let yWords ← mul rd01 ys
  let e0 ← eAt 0
  let c1 ← mul e0 yWords
  let e1 ← eAt 1
  let c2 ← mul e1 (krG.getD 3 0)
  let xv ← add (lr.getD (laneOf UniKeccak.xQuad UniKeccak.roleX) 0) (lr.getD (laneOf UniKeccak.xQuad UniKeccak.roleV) 0)
  let c3 ← mul c2 xv
  let constants ← add c1 c3
  let b1 ← mul (kd.getD 1 0) sumLr
  let b2 ← mul b1 sumRdA
  let sumRx ← sumL (List.range UniKeccak.lanes) fun q ↦ pure (rx.getD q 0)
  let b3 ← add b2 sumRx
  let gC ← groupedS UniKeccak.lanes krG fun q ↦ pure (lr.getD (laneOf q UniKeccak.roleC) 0)
  let b4 ← add b3 gC
  let gV ← groupedS UniKeccak.lanes krG fun q ↦ pure (lr.getD (laneOf q UniKeccak.roleV) 0)
  let bOne ← add b4 gV
  let alpha2 ← square alpha
  let alpha3 ← mul alpha2 alpha
  let o1 ← add tOne rcOne
  let o2 ← add o1 constants
  let cb ← add constants bOne
  let acb ← mul alpha cb
  let o3 ← add o2 acb
  let oneCoefficient ← add o3 alpha3
  let lk ← mul (lh.getD 1 0) (khG.getD 0 0)
  let oneColumn ← mul (sA.getD 0 0) lk
  let free ← groupedS UniKeccak.lanes krhG fun q ↦
    mul (lr.getD (laneOf q UniKeccak.roleC) 0) (lh.getD (laneOf q UniKeccak.roleC) 0)
  let copies ← groupedS UniKeccak.lanes krhG fun q ↦
    mul (lr.getD (laneOf q UniKeccak.roleV) 0) (lh.getD (laneOf q UniKeccak.roleX) 0)
  let m1 ← mul (kd.getD 1 0) (kh.getD 0 0)
  let sl ← sumL (List.range UniKeccak.lanes) fun l ↦ mul (lr.getD l 0) (lh.getD l 0)
  let m2 ← mul m1 sl
  let sf ← sumL (List.range' 2 (UniKeccak.rounds - 1)) fun f ↦ mul (rd.getD f 0) (rh.getD f 0)
  let aTMid ← mul m2 sf
  let n1 ← mul (kh.getD 0 0) (rh.getD (UniKeccak.rounds + 1) 0)
  let sx ← sumL (List.range UniKeccak.lanes) fun l ↦ mul (rx.getD l 0) (lh.getD l 0)
  let aTLast ← mul n1 sx
  let ee ← eqEval chiIn chiInPrime
  let cClaim ← mul alpha2 ee
  let d1 ← add free copies
  let d2 ← add d1 aTMid
  let d3 ← add d2 aTLast
  let d4 ← add d3 cClaim
  let diagonal ← mul es d4
  let rhoMid ← sumL (List.range' 1 (UniKeccak.rounds - 2)) fun j ↦ mul (rd.getD (j + 2) 0) (rh.getD (j + 1) 0)
  let mut colLh : Array Sym := #[]
  for x in List.range 5 do
    colLh := colLh.push (← sumL (List.range 5) fun y ↦ pure (lh.getD (x + 5 * y) 0))
  let mut colPc : Array Sym := #[]
  for x in List.range 5 do
    colPc := colPc.push (← sumL (List.range 5) fun y ↦ pure (pc.getD (x + 5 * y) 0))
  let c23 ← mul (rd.getD (UniKeccak.rounds + 1) 0) (kd.getD 0 0)
  let vMid ← mul (kh.getD 1 0) rhoMid
  let vLast ← mul (kh.getD 1 0) (rh.getD UniKeccak.rounds 0)
  let zg ← zero
  let mut g : Array Sym := Array.replicate 64 zg
  for i in List.range UniKeccak.lanes do
    let x := i % 5
    let y := i / 5
    let at_ ← mul alpha (lr.getD ((x + 3) % 5 + 5 * y) 0)
    let t ← add (lr.getD ((x + 4) % 5 + 5 * y) 0) at_
    let tl ← add t (lr.getD i 0)
    let ktl ← mul kr5 tl
    let u ← add t ktl
    let ct ← mul c23 t
    let last ← add ct (rx.getD i 0)
    let vm ← mul vMid u
    let vl ← mul vLast last
    let v ← add vm vl
    let w0 ← mul (rd.getD 2 0) u
    let (src, rot) := UniKeccak.source.getD i (0, 0)
    let xs := src % 5
    let a1 ← add (lh.getD src 0) (colLh.getD ((xs + 4) % 5) 0)
    let va ← mul v a1
    let a2 ← add (pc.getD src 0) (colPc.getD ((xs + 4) % 5) 0)
    let wa ← mul w0 a2
    let r ← add va wa
    g := g.set! rot (← add (g.getD rot 0) r)
    let vb ← mul v (colLh.getD ((xs + 1) % 5) 0)
    let wb ← mul w0 (colPc.getD ((xs + 1) % 5) 0)
    let r' ← add vb wb
    g := g.set! ((rot + 1) % 64) (← add (g.getD ((rot + 1) % 64) 0) r')
  let shifts ← sumL ((List.range 64).filter fun off ↦ needed.getD off false) fun off ↦
    mul (g.getD off 0) (corr.getD off 0)
  let f1 ← mul oneColumn oneCoefficient
  let f2 ← add f1 diagonal
  add f2 shifts

/-- **`verify_walked_with::<S, Keccak>(log_n, variant)`**: the front, the structured terminal against `r_lc`
(required zero), the ring switch's end (tower order). -/
def verifyWalkedK (logN k : Nat) (fs : FsShape) : Prog (List Sym × List Sym × Sym) := do
  let fr ← frontK logN k fs
  let terminal ← structuredTerminalS fr.zSkip fr.rowLow fr.chiIn fr.chiInPrime fr.slices fr.alpha
  requireZero (← add terminal fr.rLc)
  let (map, target) ← ringEnd fr.slices
  return (fr.point, map, target)

end RecGraphKeccak.Pi1
