-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Relates `formal/UniKeccak/UniKeccak/Terminal.lean`'s
-- `structuredTerminal` (transcribed from `crates/leanvm/statement/src/keccak_flock.rs`) to `formal/KeccakFlock`'s
-- `KeccakFlock.Terminal.structuredTerminal` (the same function, its loops written as sums).
import UniKeccakSound.Flock.Terminal
import FlockSoundUni.WalkCode

/-!
# The two transcriptions of the structured terminal agree

**`structuredTerminalBridge : StructuredTerminalBridge`**, for all inputs (`structuredTerminal_eq`): the verifier's
`UniKeccak.structuredTerminal` (the Rust's loops and arrays) equals `KeccakFlock.Terminal.structuredTerminal` (its
sums and functions), the one `KeccakFlock.Core.structuredTerminal_eq_bilinear` is about.

* the verifier's function is, **by definitional unfolding**, `ukBody` of its packing weights, its correlations
  (`ukCorr`) and its eq tables (`structuredTerminal_eq_body`), `ukBody` written in `structuredCore`'s parts with
  the code's arrays (`ukKd`, `ukKG`, `ukPort`, `ukCol`) and loops (`ukRc`, `ukG`);
* each part is the corresponding sum: the arrays' entries are `kindW`, `groupW`, `portW`, `colSum` at the indices
  read (`kd_getD`, `kG_getD`, `port_getD`, `col_getD`); the `ι` loop is `rcMid`, `rcLast` (`ukRc_eq`); the lanes'
  loop is `gAt` at every offset (`ukG_getD`); the correlations are `correlation` (`ukCorr_getD`);
* the constant tables agree, by kernel evaluation: `RC`'s bits (`rc_filter_eq`), `SOURCE` (`source_eq`), the shift
  offsets (`shiftOffsets_eq`).
-/

namespace UniKeccakSound.KF.Br

open LeanVM.Parameters UniStatement KeccakFlock.Terminal

/-! ## The constant tables -/

theorem rc_filter_eq : ∀ z < 64, (List.range 24).filter (fun j ↦ ((UniKeccak.rc.getD j 0) >>> z.toUInt64) &&& 1 == 1) =
    (List.range 24).filter (fun j ↦ rcBitR j z) := by
  decide +kernel

theorem source_eq : ∀ i < 25, UniKeccak.source.getD i (0, 0) = KeccakFlock.Terminal.source.getD i (0, 0) := by
  decide +kernel

theorem source_lt : ∀ i < 25, (KeccakFlock.Terminal.source.getD i (0, 0)).1 < 25 ∧
    (KeccakFlock.Terminal.source.getD i (0, 0)).2 < 63 := by
  decide +kernel

theorem shiftOffsets_eq : ∀ off < 64, UniKeccak.shiftOffsets.getD off false = needed off := by
  decide +kernel

/-! ## The code, its loops and arrays named -/

/-- `kd = [1 + k5, k5]` (`kh`). -/
def ukKd (k5 : E) : Array E := #[1 + k5, k5]

/-- `kr_g` (`kh_g`). -/
def ukKG (kd r : Array E) : Array E := Array.ofFn (n := 4) fun g ↦ kd.getD (g.val &&& 1) 0 * r.getD (g.val >>> 1) 0

/-- `krh_g`. -/
def ukKrhG (a b : Array E) : Array E := Array.ofFn (n := 4) fun g ↦ a.getD g.val 0 * b.getD g.val 0

/-- `rx` (role `0`), `pc` (role `2`). -/
def ukPort (l kG : Array E) (role : ℕ) : Array E :=
  Array.ofFn (n := 25) fun q ↦ l.getD ((4 * q.val + role) % 32) 0 * kG.getD (q.val >>> 3) 0

/-- `col_lh`, `col_pc`. -/
def ukCol (a : Array E) : Array E := Array.ofFn (n := 5) fun x ↦ UniKeccak.sumRange 0 5 fun y ↦ a.getD (x.val + 5 * y) 0

/-- The `ι` loop. -/
def ukRc (eAt : ℕ → E) (rd : Array E) : E × E := Id.run do
  let mut rcMid : E := 0
  let mut rcLast : E := 0
  for z in [0:64] do
    let rs := (List.range 24).filter fun j ↦ ((UniKeccak.rc.getD j 0) >>> z.toUInt64) &&& 1 == 1
    if !rs.isEmpty then
      let ez := eAt z
      let midSum := esum ((rs.filter (· < 23)).map fun j ↦ rd.getD (j + 2) 0)
      rcMid := rcMid + ez * midSum
      if rs.contains 23 then rcLast := rcLast + ez
  return (rcMid, rcLast)

/-- The `b` lanes' loop. -/
def ukG (lr rd lh rx pc colLh colPc : Array E) (alpha kr5 c23 vMid vLast : E) : Array E := Id.run do
  let mut g : Array E := Array.replicate 64 0
  for i in [0:25] do
    let x := i % 5
    let y := i / 5
    let t := lr.getD ((x + 4) % 5 + 5 * y) 0 + alpha * lr.getD ((x + 3) % 5 + 5 * y) 0
    let u := t + kr5 * (t + lr.getD i 0)
    let last := c23 * t + rx.getD i 0
    let v := vMid * u + vLast * last
    let w0 := rd.getD 2 0 * u
    let (src, rot) := UniKeccak.source.getD i (0, 0)
    let xs := src % 5
    g := g.modify rot (· + (v * (lh.getD src 0 + colLh.getD ((xs + 4) % 5) 0) +
      w0 * (pc.getD src 0 + colPc.getD ((xs + 4) % 5) 0)))
    g := g.modify ((rot + 1) % 64) (· + (v * colLh.getD ((xs + 1) % 5) 0 + w0 * colPc.getD ((xs + 1) % 5) 0))
  return g

/-- The correlations. -/
def ukCorr (zSkip : Option E) (rowLow s : List E) : Array E :=
  let packing := 6
  let k := packing - rowLow.length
  let one : E := 1
  let sA := s.toArray
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
  let needed := UniKeccak.shiftOffsets
  let partialAt (ol m : ℕ) : E :=
    UniKeccak.sumRange 0 lo fun zl ↦ eLow.getD zl 0 * sA.getD ((lo * m + zl + 64 - ol) % 64) 0
  Array.ofFn (n := 64) fun off ↦
    if needed.getD off.val false then
      let ol := off.val % lo
      let oh := off.val / lo
      UniKeccak.sumRange 0 nHi fun zh ↦ eHigh.getD zh 0 * partialAt ol ((zh + nHi - oh) % nHi)
    else 0

def ukTOne (lr rd : Array E) (kr5 : E) : E :=
  (ukKd kr5).getD 0 0 * UniKeccak.sumRange 0 25 (fun l ↦ lr.getD l 0) *
    (UniKeccak.sumRange 2 25 (fun f ↦ rd.getD f 0) + rd.getD 25 0)

def ukRcOne (eAt : ℕ → E) (lr rd : Array E) (kr5 : E) : E :=
  lr.getD 0 0 * (ukKd kr5).getD 1 0 * (ukRc eAt rd).1 + (ukPort lr (ukKG (ukKd kr5) rd) 0).getD 0 0 * (ukRc eAt rd).2

def ukConstants (eAt : ℕ → E) (lr rd : Array E) (kr5 : E) : E :=
  eAt 0 * ((rd.getD 0 0 + rd.getD 1 0) * UniKeccak.sumRange 0 8 fun a ↦ lr.getD ((4 * a + 1) % 32) 0) +
    eAt 1 * (ukKG (ukKd kr5) rd).getD 3 0 * (lr.getD ((4 * 25 + 0) % 32) 0 + lr.getD ((4 * 25 + 3) % 32) 0)

def ukBOne (lr rd : Array E) (kr5 : E) : E :=
  (ukKd kr5).getD 1 0 * UniKeccak.sumRange 0 25 (fun l ↦ lr.getD l 0) * UniKeccak.sumRange 2 25 (fun f ↦ rd.getD f 0) +
    UniKeccak.sumRange 0 25 (fun q ↦ (ukPort lr (ukKG (ukKd kr5) rd) 0).getD q 0) +
    UniKeccak.grouped 25 (ukKG (ukKd kr5) rd) (fun q ↦ lr.getD ((4 * q + 2) % 32) 0) +
    UniKeccak.grouped 25 (ukKG (ukKd kr5) rd) (fun q ↦ lr.getD ((4 * q + 3) % 32) 0)

def ukOneCoefficient (eAt : ℕ → E) (lr rd : Array E) (kr5 alpha : E) : E :=
  ukTOne lr rd kr5 + ukRcOne eAt lr rd kr5 + ukConstants eAt lr rd kr5 +
    alpha * (ukConstants eAt lr rd kr5 + ukBOne lr rd kr5) + alpha * alpha * alpha

def ukOneColumn (sA lh rh : Array E) (kh5 : E) : E := sA.getD 0 0 * (lh.getD 1 0 * (ukKG (ukKd kh5) rh).getD 0 0)

def ukFree (lr rd lh rh : Array E) (kr5 kh5 : E) : E :=
  UniKeccak.grouped 25 (ukKrhG (ukKG (ukKd kr5) rd) (ukKG (ukKd kh5) rh)) fun q ↦
    lr.getD ((4 * q + 2) % 32) 0 * lh.getD ((4 * q + 2) % 32) 0

def ukCopies (lr rd lh rh : Array E) (kr5 kh5 : E) : E :=
  UniKeccak.grouped 25 (ukKrhG (ukKG (ukKd kr5) rd) (ukKG (ukKd kh5) rh)) fun q ↦
    lr.getD ((4 * q + 3) % 32) 0 * lh.getD ((4 * q + 0) % 32) 0

def ukATMid (lr rd lh rh : Array E) (kr5 kh5 : E) : E :=
  (ukKd kr5).getD 1 0 * (ukKd kh5).getD 0 0 * UniKeccak.sumRange 0 25 (fun l ↦ lr.getD l 0 * lh.getD l 0) *
    UniKeccak.sumRange 2 25 (fun f ↦ rd.getD f 0 * rh.getD f 0)

def ukATLast (lr rd lh rh : Array E) (kr5 kh5 : E) : E :=
  (ukKd kh5).getD 0 0 * rh.getD 25 0 *
    UniKeccak.sumRange 0 25 (fun l ↦ (ukPort lr (ukKG (ukKd kr5) rd) 0).getD l 0 * lh.getD l 0)

def ukDiagonal (corr lr rd lh rh : Array E) (kr5 kh5 alpha cEq : E) : E :=
  corr.getD 0 0 * (ukFree lr rd lh rh kr5 kh5 + ukCopies lr rd lh rh kr5 kh5 + ukATMid lr rd lh rh kr5 kh5 +
    ukATLast lr rd lh rh kr5 kh5 + alpha * alpha * cEq)

def ukGArr (lr rd lh rh : Array E) (kr5 kh5 alpha : E) : Array E :=
  ukG lr rd lh (ukPort lr (ukKG (ukKd kr5) rd) 0) (ukPort lh (ukKG (ukKd kh5) rh) 2) (ukCol lh)
    (ukCol (ukPort lh (ukKG (ukKd kh5) rh) 2)) alpha kr5 (rd.getD 25 0 * (ukKd kr5).getD 0 0)
    ((ukKd kh5).getD 1 0 * UniKeccak.sumRange 1 23 (fun j ↦ rd.getD (j + 2) 0 * rh.getD (j + 1) 0))
    ((ukKd kh5).getD 1 0 * rh.getD 24 0)

def ukShifts (corr lr rd lh rh : Array E) (kr5 kh5 alpha : E) : E :=
  UniKeccak.sumRange 0 64 fun off ↦
    if UniKeccak.shiftOffsets.getD off false then (ukGArr lr rd lh rh kr5 kh5 alpha).getD off 0 * corr.getD off 0
    else 0

/-- **The verifier's structured terminal in `structuredCore`'s parts**, with the code's arrays and loops. -/
def ukBody (eAt : ℕ → E) (corr lr rd lh rh sA : Array E) (kr5 kh5 alpha cEq : E) : E :=
  ukOneColumn sA lh rh kh5 * ukOneCoefficient eAt lr rd kr5 alpha + ukDiagonal corr lr rd lh rh kr5 kh5 alpha cEq +
    ukShifts corr lr rd lh rh kr5 kh5 alpha

/-- **The verifier's structured terminal is `ukBody`**, by definitional unfolding. -/
theorem structuredTerminal_eq_body (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E) :
    UniKeccak.structuredTerminal zSkip rowLow chiIn chiInPrime s alpha =
      ukBody (packingAt zSkip rowLow) (ukCorr zSkip rowLow s) (eqKernel (chiIn.take 5)) (eqKernel (chiIn.drop 6))
        (eqKernel (chiInPrime.take 5)) (eqKernel (chiInPrime.drop 6)) s.toArray (chiIn.getD 5 0)
        (chiInPrime.getD 5 0) alpha (eqEval chiIn chiInPrime) := rfl

/-! ## Sums and arrays -/

theorem sumRange_zero (n : ℕ) (f : ℕ → E) : UniKeccak.sumRange 0 n f = esum ((List.range n).map f) := by
  unfold UniKeccak.sumRange
  rw [Nat.sub_zero, ← List.range_eq_range']

theorem sumRange_eqT (a b : ℕ) (f : ℕ → E) : UniKeccak.sumRange a b f = KeccakFlock.Terminal.sumRange a b f := rfl

theorem sumRange_congr (a b : ℕ) (f g : ℕ → E) (h : ∀ i, a ≤ i → i < b → f i = g i) :
    UniKeccak.sumRange a b f = UniKeccak.sumRange a b g := by
  unfold UniKeccak.sumRange
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range'_1] at hi
  exact h i hi.1 (by omega)

theorem getD_ofFn_lt {α : Type} {n : ℕ} (f : Fin n → α) {i : ℕ} (h : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  rw [FlockSound.Uni.getD_ofFn, dite_eq_left h]

theorem kd_getD (k5 : E) {b : ℕ} (hb : b < 2) : (ukKd k5).getD b 0 = kindW k5 b := by
  interval_cases b <;> rfl

theorem kG_getD (k5 : E) (r : Array E) {g : ℕ} (hg : g < 4) :
    (ukKG (ukKd k5) r).getD g 0 = groupW k5 (fun i ↦ r.getD i 0) g := by
  rw [ukKG, getD_ofFn_lt _ hg]
  show (ukKd k5).getD (g &&& 1) 0 * r.getD (g >>> 1) 0 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, pow_one, kd_getD k5 (Nat.mod_lt _ (by norm_num))]
  rfl

theorem krhG_getD (a b : E) (r r' : Array E) {g : ℕ} (hg : g < 4) :
    (ukKrhG (ukKG (ukKd a) r) (ukKG (ukKd b) r')).getD g 0 =
      groupW a (fun i ↦ r.getD i 0) g * groupW b (fun i ↦ r'.getD i 0) g := by
  rw [ukKrhG, getD_ofFn_lt _ hg]
  show (ukKG (ukKd a) r).getD g 0 * (ukKG (ukKd b) r').getD g 0 = _
  rw [kG_getD _ _ hg, kG_getD _ _ hg]

theorem port_getD (k5 : E) (l r : Array E) (role : ℕ) {q : ℕ} (hq : q < 25) :
    (ukPort l (ukKG (ukKd k5) r) role).getD q 0 = portW (fun i ↦ l.getD i 0) (fun i ↦ r.getD i 0) k5 q role := by
  rw [ukPort, getD_ofFn_lt _ hq]
  show l.getD ((4 * q + role) % 32) 0 * (ukKG (ukKd k5) r).getD (q >>> 3) 0 = _
  rw [show q >>> 3 = q / 8 by rw [Nat.shiftRight_eq_div_pow], kG_getD k5 r (by omega)]
  rfl

theorem col_getD (a : Array E) {x : ℕ} (hx : x < 5) : (ukCol a).getD x 0 = colSum (fun i ↦ a.getD i 0) x := by
  rw [ukCol, getD_ofFn_lt _ hx]
  dsimp only
  rw [sumRange_zero]
  rfl

theorem colPc_getD (kh5 : E) (lh rh : Array E) {x : ℕ} (hx : x < 5) :
    (ukCol (ukPort lh (ukKG (ukKd kh5) rh) 2)).getD x 0 =
      colSum (fun q ↦ portW (fun i ↦ lh.getD i 0) (fun i ↦ rh.getD i 0) kh5 q 2) x := by
  rw [col_getD _ hx]
  unfold colSum
  refine congrArg esum (List.map_congr_left fun y hy ↦ ?_)
  rw [List.mem_range] at hy
  exact port_getD _ _ _ _ (by omega)

theorem grouped_eq (n : ℕ) (w : Array E) (w' : ℕ → E) (hw : ∀ g < 4, w.getD g 0 = w' g) (x : ℕ → E) :
    UniKeccak.grouped n w x = KeccakFlock.Terminal.grouped n w' x := by
  unfold UniKeccak.grouped KeccakFlock.Terminal.grouped
  refine congrArg esum (List.map_congr_left fun g hg ↦ ?_)
  rw [List.mem_filter, List.mem_range] at hg
  rw [hw g hg.1]

theorem esum_cons (a : E) (l : List E) : esum (a :: l) = a + esum l := by
  rw [esum_eq, esum_eq, List.sum_cons]

theorem esum_filter (l : List ℕ) (p : ℕ → Bool) (f : ℕ → E) :
    esum ((l.filter p).map f) = esum (l.map fun x ↦ if p x then f x else 0) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons, List.map_cons]
    split_ifs with h
    · rw [List.map_cons, esum_cons, esum_cons, ih]
    · rw [esum_cons, ih, zero_add]

/-! ## The `ι` loop -/

/-- Two running sums, as a fold. -/
theorem foldl_pairAdd (F G : ℕ → E) : ∀ (l : List ℕ) (b : E × E),
    l.foldl (fun b z ↦ (b.1 + F z, b.2 + G z)) b = (b.1 + esum (l.map F), b.2 + esum (l.map G))
  | [], b => by simp [esum]
  | z :: l, b => by
    rw [List.foldl_cons, foldl_pairAdd F G l, List.map_cons, List.map_cons, esum_cons, esum_cons, add_assoc,
      add_assoc]

/-- What position `z` adds to `rc_mid`. -/
def rcFm (eAt : ℕ → E) (rd : Array E) (z : ℕ) : E :=
  let rs := (List.range 24).filter fun j ↦ ((UniKeccak.rc.getD j 0) >>> z.toUInt64) &&& 1 == 1
  if rs.isEmpty then 0 else eAt z * esum ((rs.filter (· < 23)).map fun j ↦ rd.getD (j + 2) 0)

/-- What position `z` adds to `rc_last`. -/
def rcFl (eAt : ℕ → E) (z : ℕ) : E :=
  let rs := (List.range 24).filter fun j ↦ ((UniKeccak.rc.getD j 0) >>> z.toUInt64) &&& 1 == 1
  if !rs.isEmpty && rs.contains 23 then eAt z else 0

/-- The `ι` loop's step, by its branches. -/
def rcBranch (b : E × E) (rs : List ℕ) (e m : E) : E × E :=
  if !rs.isEmpty then (if rs.contains 23 then (b.1 + e * m, b.2 + e) else (b.1 + e * m, b.2)) else (b.1, b.2)

theorem rcBranch_eq (b : E × E) (rs : List ℕ) (e m : E) :
    rcBranch b rs e m = (b.1 + (if rs.isEmpty then 0 else e * m), b.2 + (if !rs.isEmpty && rs.contains 23 then e else 0)) := by
  unfold rcBranch
  cases rs.isEmpty <;> cases rs.contains 23 <;> simp

theorem ukRc_eq (eAt : ℕ → E) (rd : Array E) :
    ukRc eAt rd = (rcMid eAt (fun i ↦ rd.getD i 0), rcLast eAt) := by
  have hf : ukRc eAt rd = (List.range' 0 64).foldl (fun b z ↦ (b.1 + rcFm eAt rd z, b.2 + rcFl eAt z)) (0, 0) := by
    unfold ukRc
    dsimp only
    rw [FlockSound.Uni.Walk.forIn_range0_eq _ _ _ (fun b z ↦ (b.1 + rcFm eAt rd z, b.2 + rcFl eAt z))
      fun i b ↦ ?_]
    · rfl
    · simp only [rcFm, rcFl]
      rw [← rcBranch_eq]
      unfold rcBranch
      split_ifs <;> rfl
  rw [hf, foldl_pairAdd, ← List.range_eq_range']
  simp only [zero_add]
  unfold rcMid rcLast
  refine Prod.ext ?_ ?_
  · refine congrArg esum (List.map_congr_left fun z hz ↦ ?_)
    rw [List.mem_range] at hz
    simp only [rcFm]
    rw [rc_filter_eq z hz]
  · refine congrArg esum (List.map_congr_left fun z hz ↦ ?_)
    rw [List.mem_range] at hz
    simp only [rcFl]
    rw [rc_filter_eq z hz]

/-! ## The lanes' loop -/

section Lanes

variable (lr rd lh rx pc colLh colPc : Array E) (alpha kr5 c23 vMid vLast : E)

/-- What lane `i` adds at its rotation. -/
def gA1 (i : ℕ) : E :=
  let t := lr.getD ((i % 5 + 4) % 5 + 5 * (i / 5)) 0 + alpha * lr.getD ((i % 5 + 3) % 5 + 5 * (i / 5)) 0
  let u := t + kr5 * (t + lr.getD i 0)
  let v := vMid * u + vLast * (c23 * t + rx.getD i 0)
  let w0 := rd.getD 2 0 * u
  let src := (UniKeccak.source.getD i (0, 0)).1
  v * (lh.getD src 0 + colLh.getD ((src % 5 + 4) % 5) 0) + w0 * (pc.getD src 0 + colPc.getD ((src % 5 + 4) % 5) 0)

/-- What lane `i` adds at its rotation plus one. -/
def gA2 (i : ℕ) : E :=
  let t := lr.getD ((i % 5 + 4) % 5 + 5 * (i / 5)) 0 + alpha * lr.getD ((i % 5 + 3) % 5 + 5 * (i / 5)) 0
  let u := t + kr5 * (t + lr.getD i 0)
  let v := vMid * u + vLast * (c23 * t + rx.getD i 0)
  let w0 := rd.getD 2 0 * u
  let src := (UniKeccak.source.getD i (0, 0)).1
  v * colLh.getD ((src % 5 + 1) % 5) 0 + w0 * colPc.getD ((src % 5 + 1) % 5) 0

/-- One step of the lanes' loop. -/
def gStep (g : Array E) (i : ℕ) : Array E :=
  (g.modify (UniKeccak.source.getD i (0, 0)).2 (· + gA1 lr rd lh rx pc colLh colPc alpha kr5 c23 vMid vLast i)).modify
    (((UniKeccak.source.getD i (0, 0)).2 + 1) % 64) (· + gA2 lr rd rx colLh colPc alpha kr5 c23 vMid vLast i)

/-- Lane `i`'s addition at the offset `off`. -/
def gAdd (i off : ℕ) : E :=
  (if (UniKeccak.source.getD i (0, 0)).2 = off then gA1 lr rd lh rx pc colLh colPc alpha kr5 c23 vMid vLast i
    else 0) +
  (if ((UniKeccak.source.getD i (0, 0)).2 + 1) % 64 = off then
    gA2 lr rd rx colLh colPc alpha kr5 c23 vMid vLast i else 0)

theorem ukG_eq :
    ukG lr rd lh rx pc colLh colPc alpha kr5 c23 vMid vLast =
      (List.range' 0 25).foldl (gStep lr rd lh rx pc colLh colPc alpha kr5 c23 vMid vLast)
        (Array.replicate 64 0) := by
  unfold ukG
  dsimp only
  rw [FlockSound.Uni.Walk.forIn_range0_eq _ _ _ (gStep lr rd lh rx pc colLh colPc alpha kr5 c23 vMid vLast)
    fun i b ↦ ?_]
  · rfl
  · rcases h : UniKeccak.source.getD i (0, 0) with ⟨src, rot⟩
    simp only [gStep, gA1, gA2, h]

theorem gStep_getD (g : Array E) (i off : ℕ) (hoff : off < g.size) :
    (gStep lr rd lh rx pc colLh colPc alpha kr5 c23 vMid vLast g i).getD off 0 =
      g.getD off 0 + gAdd lr rd lh rx pc colLh colPc alpha kr5 c23 vMid vLast i off := by
  unfold gStep gAdd
  rw [FlockSound.Uni.getD_modify _ _ _ _ _ (by rw [Array.size_modify]; exact hoff),
    FlockSound.Uni.getD_modify _ _ _ _ _ hoff]
  split_ifs <;> ring

theorem foldl_gStep_getD (off : ℕ) : ∀ (l : List ℕ) (g : Array E), off < g.size →
    (l.foldl (gStep lr rd lh rx pc colLh colPc alpha kr5 c23 vMid vLast) g).getD off 0 =
      g.getD off 0 + esum (l.map fun i ↦ gAdd lr rd lh rx pc colLh colPc alpha kr5 c23 vMid vLast i off)
  | [], arr, _ => by simp [esum]
  | i :: l, arr, h => by
    have hs : off < (gStep lr rd lh rx pc colLh colPc alpha kr5 c23 vMid vLast arr i).size := by
      simpa [gStep] using h
    rw [List.foldl_cons, foldl_gStep_getD off l _ hs, gStep_getD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h, List.map_cons,
      esum_cons]
    ring

end Lanes

/-- **The lanes' loop is `gAt`** at every offset. -/
theorem ukG_getD (lr rd lh rh : Array E) (kr5 kh5 alpha : E) {off : ℕ} (hoff : off < 64) :
    (ukGArr lr rd lh rh kr5 kh5 alpha).getD off 0 =
      gAt (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) (fun i ↦ lh.getD i 0) (fun i ↦ rh.getD i 0) kr5 kh5 alpha off := by
  unfold ukGArr
  rw [ukG_eq, foldl_gStep_getD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using hoff), FlockSound.Uni.getD_replicate,
    ite_eq_left hoff, zero_add, ← List.range_eq_range']
  unfold gAt
  refine congrArg esum (List.map_congr_left fun i hi ↦ ?_)
  rw [List.mem_range] at hi
  have hs := source_eq i hi
  have hlt := source_lt i hi
  rcases hs' : KeccakFlock.Terminal.source.getD i (0, 0) with ⟨src, rot⟩
  rw [hs'] at hs hlt
  obtain ⟨hsrc, hrot⟩ := hlt
  simp only [gAdd, gA1, gA2, hs, laneTerms, hs', laneV, laneU, laneLast]
  rw [colPc_getD _ _ _ (Nat.mod_lt _ (by norm_num)), colPc_getD _ _ _ (Nat.mod_lt _ (by norm_num)),
    col_getD _ (Nat.mod_lt _ (by norm_num)), col_getD _ (Nat.mod_lt _ (by norm_num)), port_getD _ _ _ _ hi,
    port_getD _ _ _ _ hsrc, kd_getD _ (by norm_num), kd_getD _ (by norm_num), sumRange_eqT]

/-- **The shifts.** -/
theorem ukShifts_eq (corr : Array E) (corrF : ℕ → E) (hcorr : ∀ off < 64, corr.getD off 0 = corrF off)
    (lr rd lh rh : Array E) (kr5 kh5 alpha : E) :
    ukShifts corr lr rd lh rh kr5 kh5 alpha =
      shifts corrF (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) (fun i ↦ lh.getD i 0) (fun i ↦ rh.getD i 0) kr5 kh5
        alpha := by
  unfold ukShifts shifts
  rw [sumRange_zero, esum_filter]
  refine congrArg esum (List.map_congr_left fun off hoff ↦ ?_)
  rw [List.mem_range] at hoff
  rw [shiftOffsets_eq off hoff, ukG_getD _ _ _ _ _ _ _ hoff, hcorr off hoff]

/-! ## The parts -/

section Parts

variable (eAt : ℕ → E) (lr rd lh rh sA : Array E) (kr5 kh5 alpha cEq : E)

theorem ukTOne_eq : ukTOne lr rd kr5 = tOne (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) kr5 := by
  unfold ukTOne tOne
  rw [kd_getD _ (by norm_num)]
  rfl

theorem ukRcOne_eq : ukRcOne eAt lr rd kr5 = rcOne eAt (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) kr5 := by
  unfold ukRcOne rcOne
  rw [ukRc_eq, kd_getD _ (by norm_num), port_getD _ _ _ _ (by norm_num)]

theorem ukConstants_eq :
    ukConstants eAt lr rd kr5 = constants eAt (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) kr5 := by
  unfold ukConstants constants
  rw [kG_getD _ _ (by norm_num), sumRange_zero]
  rfl

theorem ukBOne_eq : ukBOne lr rd kr5 = bOne (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) kr5 := by
  unfold ukBOne bOne
  rw [kd_getD _ (by norm_num), grouped_eq 25 _ _ (fun g hg ↦ kG_getD _ _ hg),
    grouped_eq 25 _ _ (fun g hg ↦ kG_getD _ _ hg),
    sumRange_congr 0 25 _ (fun q ↦ portW (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) kr5 q 0)
      (fun q _ hq ↦ port_getD _ _ _ _ hq),
    sumRange_zero 25 (fun q ↦ portW (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) kr5 q 0)]
  rfl

theorem ukOneCoefficient_eq :
    ukOneCoefficient eAt lr rd kr5 alpha =
      oneCoefficient eAt (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) kr5 alpha := by
  unfold ukOneCoefficient oneCoefficient
  rw [ukTOne_eq, ukRcOne_eq, ukConstants_eq, ukBOne_eq]

theorem ukOneColumn_eq :
    ukOneColumn sA lh rh kh5 = sA.getD 0 0 * (lh.getD 1 0 * groupW kh5 (fun i ↦ rh.getD i 0) 0) := by
  unfold ukOneColumn
  rw [kG_getD _ _ (by norm_num)]

theorem ukFree_eq : ukFree lr rd lh rh kr5 kh5 =
    freeW (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) (fun i ↦ lh.getD i 0) (fun i ↦ rh.getD i 0) kr5 kh5 := by
  unfold ukFree freeW
  rw [grouped_eq 25 _ _ (fun g hg ↦ krhG_getD _ _ _ _ hg)]
  rfl

theorem ukCopies_eq : ukCopies lr rd lh rh kr5 kh5 =
    copiesW (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) (fun i ↦ lh.getD i 0) (fun i ↦ rh.getD i 0) kr5 kh5 := by
  unfold ukCopies copiesW
  rw [grouped_eq 25 _ _ (fun g hg ↦ krhG_getD _ _ _ _ hg)]
  rfl

theorem ukATMid_eq : ukATMid lr rd lh rh kr5 kh5 =
    aTMid (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) (fun i ↦ lh.getD i 0) (fun i ↦ rh.getD i 0) kr5 kh5 := by
  unfold ukATMid aTMid
  rw [kd_getD _ (by norm_num), kd_getD _ (by norm_num)]
  rfl

theorem ukATLast_eq : ukATLast lr rd lh rh kr5 kh5 =
    aTLast (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) (fun i ↦ lh.getD i 0) (fun i ↦ rh.getD i 0) kr5 kh5 := by
  unfold ukATLast aTLast
  rw [kd_getD _ (by norm_num), sumRange_congr 0 25 _
    (fun l ↦ portW (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) kr5 l 0 * lh.getD l 0)
    (fun l _ hl ↦ by rw [port_getD _ _ _ _ hl])]
  rfl

theorem ukDiagonal_eq (corr : Array E) (corrF : ℕ → E) (h0 : corr.getD 0 0 = corrF 0) :
    ukDiagonal corr lr rd lh rh kr5 kh5 alpha cEq =
      diagonal corrF (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) (fun i ↦ lh.getD i 0) (fun i ↦ rh.getD i 0) kr5 kh5
        alpha cEq := by
  unfold ukDiagonal diagonal
  rw [h0, ukFree_eq, ukCopies_eq, ukATMid_eq, ukATLast_eq]

/-- **`ukBody` is `structuredCore`**, its arrays read as functions. -/
theorem ukBody_eq (corr : Array E) (corrF : ℕ → E) (hcorr : ∀ off < 64, corr.getD off 0 = corrF off) :
    ukBody eAt corr lr rd lh rh sA kr5 kh5 alpha cEq =
      structuredCore eAt corrF (fun i ↦ lr.getD i 0) (fun i ↦ rd.getD i 0) (fun i ↦ lh.getD i 0)
        (fun i ↦ rh.getD i 0) (fun i ↦ sA.getD i 0) kr5 kh5 alpha cEq := by
  unfold ukBody structuredCore
  rw [ukOneColumn_eq, ukOneCoefficient_eq, ukDiagonal_eq _ _ _ _ _ _ _ _ _ _ (hcorr 0 (by norm_num)),
    ukShifts_eq _ _ hcorr]

end Parts

/-- **The correlations.** -/
theorem ukCorr_getD (zSkip : Option E) (rowLow s : List E) {off : ℕ} (h : off < 64) :
    (ukCorr zSkip rowLow s).getD off 0 = correlation zSkip rowLow s off := by
  unfold ukCorr correlation
  rw [getD_ofFn_lt _ h]
  dsimp only
  rw [shiftOffsets_eq off h]
  simp only [sumRange_zero]
  rfl

/-- **The two transcriptions of the structured terminal agree**, for all inputs. -/
theorem structuredTerminal_eq (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E) :
    UniKeccak.structuredTerminal zSkip rowLow chiIn chiInPrime s alpha =
      KeccakFlock.Terminal.structuredTerminal zSkip rowLow chiIn chiInPrime s alpha := by
  rw [structuredTerminal_eq_body, ukBody_eq _ _ _ _ _ _ _ _ _ _ _ (correlation zSkip rowLow s)
    (fun off h ↦ ukCorr_getD zSkip rowLow s h)]
  rfl

end UniKeccakSound.KF.Br

namespace UniKeccakSound.KF

/-- **The bridge holds.** -/
theorem structuredTerminalBridge : StructuredTerminalBridge :=
  fun z rowLow chiIn chiInPrime s α _ _ _ _ ↦ Br.structuredTerminal_eq (some z) rowLow chiIn chiInPrime s α

/-- **Flock's interface on the Keccak-f block, main line** (`KECCAK_MAIN`), closed, for every `κ`. -/
noncomputable def flockSoundK_main_closed (κ : ℕ) :
    KFlockSound KeccakFlock.keccakFlockSpec κ UniKeccak.keccakMain :=
  flockSoundK_main structuredTerminalBridge κ

/-- **Flock's interface on the Keccak-f block, π1-rec3** (`KECCAK_REC3`), closed, for every `κ`. -/
noncomputable def flockSoundK_rec3_closed (κ : ℕ) :
    KFlockSound KeccakFlock.keccakFlockSpec κ UniKeccak.keccakRec3 :=
  flockSoundK_rec3 structuredTerminalBridge κ

open scoped ENNReal in
/-- **Its rounds' errors, main line**: at most `2^32/|E|` each (for `7 + κ ≤ 2^32`). -/
theorem flockSoundK_main_closed_err_le (κ : ℕ) (hκ : 7 + κ ≤ 2 ^ 32) (j : ℕ) :
    (flockSoundK_main_closed κ).err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card LeanVM.Parameters.E : ℝ≥0∞) :=
  flockSoundK_main_err_le _ κ hκ j

open scoped ENNReal in
/-- **Its rounds' errors, π1-rec3**: at most `2^35/|E|` each, for `κ ≤ 28`. -/
theorem flockSoundK_rec3_closed_err_le (κ : ℕ) (hκ : κ ≤ 28) (j : ℕ) :
    (flockSoundK_rec3_closed κ).err j ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card LeanVM.Parameters.E : ℝ≥0∞) :=
  flockSoundK_rec3_err_le _ κ hκ j

/-- **Flock's result is the main line's** (`FlockGoodDoneK`, unfolded), main line. -/
theorem flockSoundK_main_closed_good (κ : ℕ) :
    ∀ fd, UniSound.DoneFits (flockSoundK_main_closed κ).prog.rounds fd →
      (∃ map target, ((flockSoundK_main_closed κ).prog.out fd []).2 = .ring map target) ∧
        ((flockSoundK_main_closed κ).prog.out fd []).1.length = KeccakVm.kWords + κ :=
  flockSoundK_main_good _ κ

/-- **Flock's result is the main line's** (`FlockGoodDoneK`, unfolded), π1-rec3. -/
theorem flockSoundK_rec3_closed_good (κ : ℕ) :
    ∀ fd, UniSound.DoneFits (flockSoundK_rec3_closed κ).prog.rounds fd →
      (∃ map target, ((flockSoundK_rec3_closed κ).prog.out fd []).2 = .ring map target) ∧
        ((flockSoundK_rec3_closed κ).prog.out fd []).1.length = KeccakVm.kWords + κ :=
  flockSoundK_rec3_good _ κ

/-- **The Fiat–Shamir layer's sizes**, main line. -/
theorem flockSoundK_main_closed_nv (κ : ℕ) : ∀ r ∈ (flockSoundK_main_closed κ).prog.rounds, r.nv ≤ 2 ^ 30 :=
  flockSoundK_main_nv _ κ

theorem flockSoundK_main_closed_nSteps : Compose.nSteps (flockSoundK_main_closed 15).prog.rounds + 27 ≤ 1014 :=
  flockSoundK_main_nSteps _

theorem flockSoundK_rec3_closed_nv (κ : ℕ) : ∀ r ∈ (flockSoundK_rec3_closed κ).prog.rounds, r.nv ≤ 2 ^ 30 :=
  flockSoundK_rec3_nv _ κ

theorem flockSoundK_rec3_closed_nSteps : Compose.nSteps (flockSoundK_rec3_closed 15).prog.rounds + 27 ≤ 1014 :=
  flockSoundK_rec3_nSteps _

end UniKeccakSound.KF

/-- info: 'UniKeccakSound.KF.structuredTerminalBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.structuredTerminalBridge

/-- info: 'UniKeccakSound.KF.flockSoundK_main_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.flockSoundK_main_closed

/-- info: 'UniKeccakSound.KF.flockSoundK_rec3_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.flockSoundK_rec3_closed

/-- info: 'UniKeccakSound.KF.flockSoundK_main_closed_err_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.flockSoundK_main_closed_err_le

/-- info: 'UniKeccakSound.KF.flockSoundK_rec3_closed_err_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.flockSoundK_rec3_closed_err_le

/-- info: 'UniKeccakSound.KF.flockSoundK_main_closed_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.flockSoundK_main_closed_good

/-- info: 'UniKeccakSound.KF.flockSoundK_main_closed_nSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.flockSoundK_main_closed_nSteps
