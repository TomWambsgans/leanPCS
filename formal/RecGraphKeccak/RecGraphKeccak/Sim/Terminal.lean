-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraphKeccak.Sim.TerminalKern

/-!
# The structured terminal, simulated

**`structuredTerminal_ph`**: the program `RecGraphKeccak.Pi1.structuredTerminalS` (the Rust's
`keccak_flock::structured_terminal`, operation for operation) computes `UniKeccak.structuredTerminal`, at the Keccak
verifier's shape (a skip of 3: the skip's point drawn, `row_low` of 3 coordinates; `chi_in`, `chi_in'` of 11, the 64
slices). From the parts (`TerminalBase`, `TerminalKern`), the straight-line rest step by step, and `TerminalE`'s
`structuredTerminal_eq`. Where the program's order differs from `UniKeccak`'s, the values agree: `S::sum` from zero
is `esum` over the same list (`sumRange`'s `range'` against `range`), the shifts' sum over the needed offsets is the sum
of the guarded terms (`esum_filter`), `from_fn` is `Array.ofFn`.
-/

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics UniStatement RecGraph RecGraph.Pi1 RecGraph.Sim RecGraphKeccak.Pi1
  RecGraphKeccak.TerminalE

theorem esum_cons (x : E) (l : List E) : esum (x :: l) = x + esum l := by
  unfold esum
  rw [List.foldl_cons, zero_add]
  suffices h : ∀ a : E, l.foldl (· + ·) a = a + l.foldl (· + ·) 0 from h x
  induction l with
  | nil => intro a; simp
  | cons y t ih => intro a; rw [List.foldl_cons, List.foldl_cons, ih (a + y), ih (0 + y)]; ring

theorem esum_filter {α : Type} (l : List α) (p : α → Bool) (f : α → E) :
    esum ((l.filter p).map f) = esum (l.map fun x ↦ if p x then f x else 0) := by
  induction l with
  | nil => rfl
  | cons y t ih =>
    by_cases hp : p y
    · rw [List.filter_cons_of_pos hp, List.map_cons, List.map_cons, esum_cons, esum_cons, ih, iteT hp]
    · rw [List.filter_cons_of_neg hp, List.map_cons, esum_cons, ih, iteF hp, zero_add]

theorem sumRange_zero (n : ℕ) (f : ℕ → E) : esum ((List.range n).map f) = UniKeccak.sumRange 0 n f := by
  rw [UniKeccak.sumRange, Nat.sub_zero, List.range_eq_range']

section Terminal

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

local notation "Rp'" => Rp π iv publicInput stream
local notation "RpL'" => RpL π iv publicInput stream
local notation "RpA'" => RpA π iv publicInput stream

theorem Rp.congrV {st : RecState} {i : Sym} {x y : E} (h : Rp' st i x) (e : x = y) : Rp' st i y := e ▸ h

/-- A node held in a represented array, read. -/
theorem getP {st : RecState} (hg : Good st) {a : Array Sym} {x : Array E} (h : RpA' st a x) {i : ℕ}
    (hi : i < x.size) : ∀ st', PStep st st' → PH (pure (a.getD i 0)) st' (fun st'' v ↦ Rp' st'' v (x.getD i 0)) :=
  fun _ hs ↦ PH.ret hs.good ((h.pgrow hg hs).get hi)

/-- **`grouped(n, weights, x)`**. -/
theorem groupedS_ph {st : RecState} (hg : Good st) {n : ℕ} {w : Array Sym} {W : Array E} (x : ℕ → Prog Sym)
    (X : ℕ → E) (hx : ∀ q < n, ∀ st', PStep st st' → PH (x q) st' (fun st'' v ↦ Rp' st'' v (X q)))
    (hw : RpA' st w W) (hW : W.size = 4) :
    PH (groupedS n w x) st (fun st' v ↦ Rp' st' v (UniKeccak.grouped n W X)) := by
  unfold groupedS UniKeccak.grouped
  refine sumL_ph hg _ _ _ fun g hgm st' hs' ↦ ?_
  have hg4 : g < 4 := List.mem_range.mp (List.mem_filter.mp hgm).1
  refine PH.bind' (sumL_ph hs'.good _ x X fun q hq st'' hs'' ↦ hx q ?_ st'' (hs'.trans hs'')) fun st'' v hs'' hv ↦ ?_
  · rw [List.mem_range'] at hq; omega
  exact PH.mul hs''.good ((hw.pgrow hg (hs'.trans hs'')).get (by rw [hW]; exact hg4)) hv

theorem lanes_lt {l : ℕ} (h : l ∈ List.range UniKeccak.lanes) : l < 25 := List.mem_range.mp h

set_option maxHeartbeats 1000000 in
/-- **The structured terminal**: the program computes `UniKeccak.structuredTerminal`. -/
theorem structuredTerminal_ph {st : RecState} (hg : Good st) {z : Sym} {zE : E} (hz : Rp' st z zE)
    {rl ci cp s : List Sym} {RL CI CP S : List E} (hrl : RpL' st rl RL) (hRL : RL.length = 3)
    (hci : RpL' st ci CI) (hCI : CI.length = 11) (hcp : RpL' st cp CP) (hCP : CP.length = 11)
    (hs : RpL' st s S) (hS : S.length = 64) {alpha : Sym} {A : E} (ha : Rp' st alpha A) :
    PH (structuredTerminalS (some z) rl ci cp s alpha) st
      (fun st' v ↦ Rp' st' v (UniKeccak.structuredTerminal (some zE) RL CI CP S A)) := by
  rw [structuredTerminal_eq]
  have hrll : rl.length = 3 := by rw [hrl.length, hRL]
  have hsA := RpL.toRpA hs
  have hels : (eLowE (some zE) RL).size = 8 := by
    simp [eLowE, lagE, kE, pE, hRL, eqKernel_sizeK, lagrangeWeights_eq]
  have hehs : (eHighE RL).size = 8 := by simp [eHighE, kE, pE, hRL, eqKernel_sizeK]
  have hlrs : (lrE CI).size = 32 := lrE_size CI hCI
  have hrds : (rdE CI).size = 32 := rdE_size CI hCI
  have hlhs : (lhE CP).size = 32 := lhE_size CP hCP
  have hrhs : (rhE CP).size = 32 := rhE_size CP hCP
  have hrxs : (rxE CI).size = 25 := by simp [rxE, UniKeccak.lanes]
  have hpcs : (pcE CP).size = 25 := by simp [pcE, UniKeccak.lanes]
  have hkrGs : (krGE CI).size = 4 := by simp [krGE]
  have hkhGs : (khGE CP).size = 4 := by simp [khGE]
  have hkrhGs : (krhGE CI CP).size = 4 := by simp [krhGE]
  have hkds : (kdE CI).size = 2 := rfl
  have hkhs : (khE CP).size = 2 := rfl
  have hcorrs : (corrE (some zE) RL S).size = 64 := by simp [corrE]
  unfold structuredTerminalS
  simp only [hrll, Flock.packing, show 2 ^ max (6 - 3) 3 = 8 from rfl, show 2 ^ (6 - max (6 - 3) 3) = 8 from rfl]
  phg (packS_ph hg hz hrl hRL) as st1 P hs1 hP
  obtain ⟨ho, hel, heh⟩ := hP
  phg (corrS_ph hg hRL hel hels heh hehs hsA hS) as st2 corr hs2 hcorr
  phg (kernelsS_ph hg ho hci hcp hCI hCP) as st3 K hs3 hK
  obtain ⟨hlr, hrd, hlh, hrh, hkd, hkh, hkrG, hkhG, hkrhG, hrx, hpc⟩ := hK
  -- t rows
  phg (sumL_ph hg (List.range UniKeccak.lanes) _ (fun l ↦ (lrE CI).getD l 0)
    (fun l hl ↦ getP hg hlr (by rw [hlrs]; have := lanes_lt hl; omega))) as st4 sumLr hs4 hsumLr
  replace hsumLr := Rp.congrV hsumLr (sumRange_zero _ _)
  phg (sumL_ph hg (List.range' 2 (UniKeccak.rounds - 1)) _ (fun f ↦ (rdE CI).getD f 0)
    (fun f hf ↦ getP hg hrd (by rw [hrds]; rw [List.mem_range'] at hf; unfold UniKeccak.rounds at hf; omega)))
    as st5 sumRdA hs5 hsumRdA
  phg (PH.add hg hsumRdA (hrd.get (i := UniKeccak.rounds + 1) (by rw [hrds]; decide))) as st6 sumRdT hs6 hsumRdT
  phg (PH.mul hg (hkd.get (i := 0) (by rw [hkds]; decide)) hsumLr) as st7 t1 hs7 ht1
  phg (PH.mul hg ht1 hsumRdT) as st8 tOne hs8 htOne
  -- ι
  phg (rcS_ph hg hRL hel hels heh hehs hrd hrds) as st9 rcp hs9 hrcp
  obtain ⟨rcMid, rcLast⟩ := rcp
  obtain ⟨hrcMid, hrcLast⟩ := hrcp
  dsimp only at hrcMid hrcLast ⊢
  phg (PH.mul hg (hlr.get (i := 0) (by rw [hlrs]; decide)) (hkd.get (i := 1) (by rw [hkds]; decide)))
    as st10 r1 hs10 hr1
  phg (PH.mul hg hr1 hrcMid) as st11 r2 hs11 hr2
  phg (PH.mul hg (hrx.get (i := 0) (by rw [hrxs]; decide)) hrcLast) as st12 r3 hs12 hr3
  phg (PH.add hg hr2 hr3) as st13 rcOne hs13 hrcOne
  -- the constant rows
  phg (PH.add hg (hrd.get (i := 0) (by rw [hrds]; decide)) (hrd.get (i := 1) (by rw [hrds]; decide)))
    as st14 rd01 hs14 hrd01
  rw [laneOf_eq]
  phg (sumL_ph hg (List.range 8) _ (fun a ↦ (lrE CI).getD (laneOfE a UniKeccak.roleY) 0)
    (fun a _ ↦ getP hg hlr (by rw [hlrs]; exact laneOfE_lt _ _))) as st15 ys hs15 hys
  replace hys := Rp.congrV hys (sumRange_zero _ _)
  phg (PH.mul hg hrd01 hys) as st16 yWords hs16 hyWords
  phg (eAtS_ph hg hRL hel hels heh hehs (z := 0) (by decide)) as st17 e0 hs17 he0
  phg (PH.mul hg he0 hyWords) as st18 c1 hs18 hc1
  phg (eAtS_ph hg hRL hel hels heh hehs (z := 1) (by decide)) as st19 e1 hs19 he1
  phg (PH.mul hg he1 (hkrG.get (i := 3) (by rw [hkrGs]; decide))) as st20 c2 hs20 hc2
  phg (PH.add hg (hlr.get (i := laneOfE UniKeccak.xQuad UniKeccak.roleX) (by rw [hlrs]; exact laneOfE_lt _ _))
    (hlr.get (i := laneOfE UniKeccak.xQuad UniKeccak.roleV) (by rw [hlrs]; exact laneOfE_lt _ _))) as st21 xv hs21 hxv
  phg (PH.mul hg hc2 hxv) as st22 c3 hs22 hc3
  phg (PH.add hg hc1 hc3) as st23 constants hs23 hconstants
  -- B = [1]
  phg (PH.mul hg (hkd.get (i := 1) (by rw [hkds]; decide)) hsumLr) as st24 b1 hs24 hb1
  phg (PH.mul hg hb1 hsumRdA) as st25 b2 hs25 hb2
  phg (sumL_ph hg (List.range UniKeccak.lanes) _ (fun q ↦ (rxE CI).getD q 0)
    (fun q hq ↦ getP hg hrx (by rw [hrxs]; exact lanes_lt hq))) as st26 sumRx hs26 hsumRx
  replace hsumRx := Rp.congrV hsumRx (sumRange_zero _ _)
  phg (PH.add hg hb2 hsumRx) as st27 b3 hs27 hb3
  phg (groupedS_ph hg _ (fun q ↦ (lrE CI).getD (laneOfE q UniKeccak.roleC) 0)
    (fun q _ ↦ getP hg hlr (by rw [hlrs]; exact laneOfE_lt _ _)) hkrG hkrGs) as st28 gC hs28 hgC
  phg (PH.add hg hb3 hgC) as st29 b4 hs29 hb4
  phg (groupedS_ph hg _ (fun q ↦ (lrE CI).getD (laneOfE q UniKeccak.roleV) 0)
    (fun q _ ↦ getP hg hlr (by rw [hlrs]; exact laneOfE_lt _ _)) hkrG hkrGs) as st30 gV hs30 hgV
  phg (PH.add hg hb4 hgV) as st31 bOne hs31 hbOne
  phg (PH.square hg ha) as st32 alpha2 hs32 halpha2
  phg (PH.mul hg halpha2 ha) as st33 alpha3 hs33 halpha3
  phg (PH.add hg htOne hrcOne) as st34 o1 hs34 ho1
  phg (PH.add hg ho1 hconstants) as st35 o2 hs35 ho2
  phg (PH.add hg hconstants hbOne) as st36 cb hs36 hcb
  phg (PH.mul hg ha hcb) as st37 acb hs37 hacb
  phg (PH.add hg ho2 hacb) as st38 o3 hs38 ho3
  phg (PH.add hg ho3 halpha3) as st39 oneCoefficient hs39 hoc
  phg (PH.mul hg (hlh.get (i := 1) (by rw [hlhs]; decide)) (hkhG.get (i := 0) (by rw [hkhGs]; decide)))
    as st40 lk hs40 hlk
  phg (PH.mul hg (hsA.get (i := 0) (by simp [hS])) hlk) as st41 oneColumn hs41 hocol
  -- the diagonal
  phg (groupedS_ph hg _
    (fun q ↦ (lrE CI).getD (laneOfE q UniKeccak.roleC) 0 * (lhE CP).getD (laneOfE q UniKeccak.roleC) 0)
    (fun q _ st' hs' ↦ PH.mul hs'.good ((hlr.pgrow hg hs').get (by rw [hlrs]; exact laneOfE_lt _ _))
      ((hlh.pgrow hg hs').get (by rw [hlhs]; exact laneOfE_lt _ _))) hkrhG hkrhGs) as st42 free hs42 hfree
  phg (groupedS_ph hg _
    (fun q ↦ (lrE CI).getD (laneOfE q UniKeccak.roleV) 0 * (lhE CP).getD (laneOfE q UniKeccak.roleX) 0)
    (fun q _ st' hs' ↦ PH.mul hs'.good ((hlr.pgrow hg hs').get (by rw [hlrs]; exact laneOfE_lt _ _))
      ((hlh.pgrow hg hs').get (by rw [hlhs]; exact laneOfE_lt _ _))) hkrhG hkrhGs) as st43 copies hs43 hcopies
  phg (PH.mul hg (hkd.get (i := 1) (by rw [hkds]; decide)) (hkh.get (i := 0) (by rw [hkhs]; decide)))
    as st44 m1 hs44 hm1
  phg (sumL_ph hg (List.range UniKeccak.lanes) _ (fun l ↦ (lrE CI).getD l 0 * (lhE CP).getD l 0)
    (fun l hl st' hs' ↦ PH.mul hs'.good ((hlr.pgrow hg hs').get (by rw [hlrs]; have := lanes_lt hl; omega))
      ((hlh.pgrow hg hs').get (by rw [hlhs]; have := lanes_lt hl; omega)))) as st45 sl hs45 hsl
  replace hsl := Rp.congrV hsl (sumRange_zero _ _)
  phg (PH.mul hg hm1 hsl) as st46 m2 hs46 hm2
  phg (sumL_ph hg (List.range' 2 (UniKeccak.rounds - 1)) _ (fun f ↦ (rdE CI).getD f 0 * (rhE CP).getD f 0)
    (fun f hf st' hs' ↦ PH.mul hs'.good
      ((hrd.pgrow hg hs').get (by rw [hrds]; rw [List.mem_range'] at hf; unfold UniKeccak.rounds at hf; omega))
      ((hrh.pgrow hg hs').get (by rw [hrhs]; rw [List.mem_range'] at hf; unfold UniKeccak.rounds at hf; omega))))
    as st47 sf hs47 hsf
  phg (PH.mul hg hm2 hsf) as st48 aTMid hs48 haTMid
  phg (PH.mul hg (hkh.get (i := 0) (by rw [hkhs]; decide)) (hrh.get (i := UniKeccak.rounds + 1) (by rw [hrhs]; decide)))
    as st49 n1 hs49 hn1
  phg (sumL_ph hg (List.range UniKeccak.lanes) _ (fun l ↦ (rxE CI).getD l 0 * (lhE CP).getD l 0)
    (fun l hl st' hs' ↦ PH.mul hs'.good ((hrx.pgrow hg hs').get (by rw [hrxs]; exact lanes_lt hl))
      ((hlh.pgrow hg hs').get (by rw [hlhs]; have := lanes_lt hl; omega)))) as st50 sx hs50 hsx
  replace hsx := Rp.congrV hsx (sumRange_zero _ _)
  phg (PH.mul hg hn1 hsx) as st51 aTLast hs51 haTLast
  have hee := PSim.ph (eqEval_psim st51 hg hci hcp)
  phg hee as st52 ee hs52 hee'
  phg (PH.mul hg halpha2 hee') as st53 cClaim hs53 hcClaim
  phg (PH.add hg hfree hcopies) as st54 d1 hs54 hd1
  phg (PH.add hg hd1 haTMid) as st55 d2 hs55 hd2
  phg (PH.add hg hd2 haTLast) as st56 d3 hs56 hd3
  phg (PH.add hg hd3 hcClaim) as st57 d4 hs57 hd4
  phg (PH.mul hg (hcorr.get (i := 0) (by rw [hcorrs]; decide)) hd4) as st58 diagonal hs58 hdiag
  -- the shifts' weights
  phg (sumL_ph hg (List.range' 1 (UniKeccak.rounds - 2)) _ (fun j ↦ (rdE CI).getD (j + 2) 0 * (rhE CP).getD (j + 1) 0)
    (fun j hj st' hs' ↦ PH.mul hs'.good
      ((hrd.pgrow hg hs').get (by rw [hrds]; rw [List.mem_range'] at hj; unfold UniKeccak.rounds at hj; omega))
      ((hrh.pgrow hg hs').get (by rw [hrhs]; rw [List.mem_range'] at hj; unfold UniKeccak.rounds at hj; omega))))
    as st59 rhoMid hs59 hrhoMid
  phg (buildS_ph hg 5 _ (fun x ↦ UniKeccak.sumRange 0 5 fun y ↦ (lhE CP).getD (x + 5 * y) 0)
    (fun x hx st' hs' ↦ (sumL_ph hs'.good (List.range 5) _ (fun y ↦ (lhE CP).getD (x + 5 * y) 0)
      (fun y hy ↦ getP hs'.good (hlh.pgrow hg hs') (by rw [hlhs]; have := List.mem_range.mp hy; omega))).mono
      fun _ _ _ h ↦ Rp.congrV h (sumRange_zero _ _))) as st60 colLh hs60 hcolLh
  phg (buildS_ph hg 5 _ (fun x ↦ UniKeccak.sumRange 0 5 fun y ↦ (pcE CP).getD (x + 5 * y) 0)
    (fun x hx st' hs' ↦ (sumL_ph hs'.good (List.range 5) _ (fun y ↦ (pcE CP).getD (x + 5 * y) 0)
      (fun y hy ↦ getP hs'.good (hpc.pgrow hg hs') (by rw [hpcs]; have := List.mem_range.mp hy; omega))).mono
      fun _ _ _ h ↦ Rp.congrV h (sumRange_zero _ _))) as st61 colPc hs61 hcolPc
  phg (PH.mul hg (hrd.get (i := UniKeccak.rounds + 1) (by rw [hrds]; decide)) (hkd.get (i := 0) (by rw [hkds]; decide)))
    as st62 c23 hs62 hc23
  phg (PH.mul hg (hkh.get (i := 1) (by rw [hkhs]; decide)) hrhoMid) as st63 vMid hs63 hvMid
  phg (PH.mul hg (hkh.get (i := 1) (by rw [hkhs]; decide)) (hrh.get (i := UniKeccak.rounds) (by rw [hrhs]; decide)))
    as st64 vLast hs64 hvLast
  phg (gS_ph hg hCI hCP ha hc23 hvMid hvLast (rpL_getD hci (i := 5) (by omega))
    ⟨hlr, hrd, hlh, hrh, hkd, hkh, hkrG, hkhG, hkrhG, hrx, hpc⟩ hcolLh hcolPc) as st65 g hs65 hgA
  obtain ⟨hgA, hgs⟩ := hgA
  phg (sumL_ph hg ((List.range 64).filter fun off ↦ UniKeccak.shiftOffsets.getD off false) _
    (fun off ↦ (gE CI CP A).getD off 0 * (corrE (some zE) RL S).getD off 0)
    (fun off hoff st' hs' ↦ by
      have hoff' : off < 64 := List.mem_range.mp (List.mem_filter.mp hoff).1
      exact PH.mul hs'.good ((hgA.pgrow hg hs').get (by rw [hgs]; exact hoff'))
        ((hcorr.pgrow hg hs').get (by rw [hcorrs]; exact hoff')))) as st66 shifts hs66 hshifts
  replace hshifts := Rp.congrV hshifts ((esum_filter _ _ _).trans (sumRange_zero _ _))
  phg (PH.mul hg hocol hoc) as st67 f1 hs67 hf1
  phg (PH.add hg hf1 hdiag) as st68 f2 hs68 hf2
  exact PH.add hg hf2 hshifts

end Terminal

end RecGraphKeccak.Sim
