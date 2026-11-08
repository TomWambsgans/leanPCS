-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecGraphKeccak.Sim.TerminalBase

/-!
# The structured terminal, simulated: a word's eq factors, ι's loop, the shifts' weights

* `kernelsS_ph`: the eq factors of a word's fields (`lr`, `rd`, `lh`, `rh`), the kind factors (`kd`, `kh`) and their
  products (`kr_g`, `kh_g`, `krh_g`, `rx`, `pc`) against `TerminalE`'s `lrE`, …, `pcE` (`KernR`);
* `rcS_ph`: ι's loop, step for step against `rcE`'s;
* `gS_ph`: the shifts' weights, lane by lane against `gE`'s loop.

`chi_in`, `chi_in'` have the Keccak-f block's 11 coordinates.
-/

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics UniStatement RecGraph RecGraph.Pi1 RecGraph.Sim RecGraphKeccak.Pi1
  RecGraphKeccak.TerminalE

theorem eqKernel_size_auxK (A : Array E) (xs : List E) :
    (xs.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) A).size = A.size * 2 ^ xs.length := by
  induction xs generalizing A with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih]; simp [Nat.pow_succ]; ring

theorem eqKernel_sizeK (xs : List E) : (UniStatement.eqKernel xs).size = 2 ^ xs.length := by
  unfold UniStatement.eqKernel
  rw [eqKernel_size_auxK]; simp

theorem laneOf_eq : RecGraphKeccak.Pi1.laneOf = laneOfE := rfl

section Kern

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **A word's eq factors, represented.** -/
structure KernR (st : RecState) (K : KernS) (CI CP : List E) : Prop where
  lr : RpA π iv publicInput stream st K.lr (lrE CI)
  rd : RpA π iv publicInput stream st K.rd (rdE CI)
  lh : RpA π iv publicInput stream st K.lh (lhE CP)
  rh : RpA π iv publicInput stream st K.rh (rhE CP)
  kd : RpA π iv publicInput stream st K.kd (kdE CI)
  kh : RpA π iv publicInput stream st K.kh (khE CP)
  krG : RpA π iv publicInput stream st K.krG (krGE CI)
  khG : RpA π iv publicInput stream st K.khG (khGE CP)
  krhG : RpA π iv publicInput stream st K.krhG (krhGE CI CP)
  rx : RpA π iv publicInput stream st K.rx (rxE CI)
  pc : RpA π iv publicInput stream st K.pc (pcE CP)

variable {π iv publicInput stream}

theorem KernR.pgrow {st st' : RecState} (hg : Good st) (hs : PStep st st') {K : KernS} {CI CP : List E}
    (h : KernR π iv publicInput stream st K CI CP) : KernR π iv publicInput stream st' K CI CP :=
  ⟨h.lr.pgrow hg hs, h.rd.pgrow hg hs, h.lh.pgrow hg hs, h.rh.pgrow hg hs, h.kd.pgrow hg hs, h.kh.pgrow hg hs,
    h.krG.pgrow hg hs, h.khG.pgrow hg hs, h.krhG.pgrow hg hs, h.rx.pgrow hg hs, h.pc.pgrow hg hs⟩

end Kern

section Terminal

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

local notation "Rp'" => Rp π iv publicInput stream
local notation "RpL'" => RpL π iv publicInput stream
local notation "RpA'" => RpA π iv publicInput stream
local notation "PZ" => PH.zero (π := π) (iv := iv) (publicInput := publicInput) (stream := stream)

theorem rpL_getD {st : RecState} {l : List Sym} {L : List E} (h : RpL' st l L) {i : ℕ} (hi : i < L.length) :
    Rp' st (l.getD i 0) (L.getD i 0) := by
  have hl := h.length
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hi]
  exact h.get i (by omega) hi

section Sizes

variable (CI CP : List E)

theorem lrE_size (h : CI.length = 11) : (lrE CI).size = 32 := by simp [lrE, eqKernel_sizeK, h]
theorem rdE_size (h : CI.length = 11) : (rdE CI).size = 32 := by simp [rdE, eqKernel_sizeK, h]
theorem lhE_size (h : CP.length = 11) : (lhE CP).size = 32 := by simp [lhE, eqKernel_sizeK, h]
theorem rhE_size (h : CP.length = 11) : (rhE CP).size = 32 := by simp [rhE, eqKernel_sizeK, h]

end Sizes

theorem and1_lt (g : ℕ) (hg : g < 4) : g &&& 1 < 2 := by interval_cases g <;> decide
theorem shr1_lt (g : ℕ) (hg : g < 4) : g >>> 1 < 2 := by interval_cases g <;> decide
theorem shr3_lt (q : ℕ) (hq : q < 25) : q >>> 3 < 4 := by interval_cases q <;> decide
theorem laneOfE_lt (q role : ℕ) : laneOfE q role < 32 := Nat.mod_lt _ (by norm_num)

/-- **A word's eq factors** (`chi_in`, `chi_in'` of 11 coordinates, `one` worth `1`). -/
theorem kernelsS_ph {st : RecState} (hg : Good st) {o : Sym} (ho : Rp' st o 1) {ci cp : List Sym} {CI CP : List E}
    (hci : RpL' st ci CI) (hcp : RpL' st cp CP) (hCI : CI.length = 11) (hCP : CP.length = 11) :
    PH (kernelsS o ci cp) st (fun st' K ↦ KernR π iv publicInput stream st' K CI CP) := by
  unfold kernelsS
  dsimp only
  phg (eqKernel_phA hg (List.forall₂_take _ hci)) as st1 lr hs1 hlr
  phg (eqKernel_phA hg (List.forall₂_drop _ hci)) as st2 rd hs2 hrd
  phg (eqKernel_phA hg (List.forall₂_take _ hcp)) as st3 lh hs3 hlh
  phg (eqKernel_phA hg (List.forall₂_drop _ hcp)) as st4 rh hs4 hrh
  have h5 := rpL_getD hci (i := 5) (by omega)
  have h5' := rpL_getD hcp (i := 5) (by omega)
  phg (PH.add hg ho h5) as st5 kd0 hs5 hkd0
  phg (PH.add hg ho h5') as st6 kh0 hs6 hkh0
  have hkd : RpA' st6 #[kd0, ci.getD 5 0] (kdE CI) := by
    refine ⟨rfl, fun i hi ↦ ?_⟩
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
    interval_cases i
    · exact hkd0
    · exact h5
  have hkh : RpA' st6 #[kh0, cp.getD 5 0] (khE CP) := by
    refine ⟨rfl, fun i hi ↦ ?_⟩
    simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
    interval_cases i
    · exact hkh0
    · exact h5'
  have hkds : (kdE CI).size = 2 := rfl
  have hkhs : (khE CP).size = 2 := rfl
  phg (buildS_ph hg 4 _ (fun g ↦ (kdE CI).getD (g &&& 1) 0 * (rdE CI).getD (g >>> 1) 0) fun g hg4 st' hs' ↦
    PH.mul hs'.good ((hkd.pgrow hg hs').get (by rw [hkds]; exact and1_lt g hg4))
      ((hrd.pgrow hg hs').get (by rw [show (UniStatement.eqKernel (List.drop 6 CI)).size = 32 from rdE_size CI hCI]; have := shr1_lt g hg4; omega))) as st7 krG hs7 hkrG
  phg (buildS_ph hg 4 _ (fun g ↦ (khE CP).getD (g &&& 1) 0 * (rhE CP).getD (g >>> 1) 0) fun g hg4 st' hs' ↦
    PH.mul hs'.good ((hkh.pgrow hg hs').get (by rw [hkhs]; exact and1_lt g hg4))
      ((hrh.pgrow hg hs').get (by rw [show (UniStatement.eqKernel (List.drop 6 CP)).size = 32 from rhE_size CP hCP]; have := shr1_lt g hg4; omega))) as st8 khG hs8 hkhG
  have hkrGs : (krGE CI).size = 4 := by simp [krGE]
  have hkhGs : (khGE CP).size = 4 := by simp [khGE]
  phg (buildS_ph hg 4 _ (fun g ↦ (krGE CI).getD g 0 * (khGE CP).getD g 0) fun g hg4 st' hs' ↦
    PH.mul hs'.good ((hkrG.pgrow hg hs').get (by simpa using hg4))
      ((hkhG.pgrow hg hs').get (by simpa using hg4))) as st9 krhG hs9 hkrhG
  rw [laneOf_eq]
  phg (buildS_ph hg UniKeccak.lanes _
    (fun q ↦ (lrE CI).getD (laneOfE q UniKeccak.roleX) 0 * (krGE CI).getD (q >>> 3) 0) fun q hq st' hs' ↦
    PH.mul hs'.good ((hlr.pgrow hg hs').get (by rw [show (UniStatement.eqKernel (List.take 5 CI)).size = 32 from lrE_size CI hCI]; exact laneOfE_lt _ _))
      ((hkrG.pgrow hg hs').get (by simpa using shr3_lt q hq))) as st10 rx hs10 hrx
  phg (buildS_ph hg UniKeccak.lanes _
    (fun q ↦ (lhE CP).getD (laneOfE q UniKeccak.roleC) 0 * (khGE CP).getD (q >>> 3) 0) fun q hq st' hs' ↦
    PH.mul hs'.good ((hlh.pgrow hg hs').get (by rw [show (UniStatement.eqKernel (List.take 5 CP)).size = 32 from lhE_size CP hCP]; exact laneOfE_lt _ _))
      ((hkhG.pgrow hg hs').get (by simpa using shr3_lt q hq))) as st11 pc hs11 hpc
  exact PH.ret hg ⟨hlr, hrd, hlh, hrh, hkd, hkh, hkrG, hkhG, hkrhG, hrx, hpc⟩

/-- `e_at(z)`. -/
theorem eAtS_ph {st : RecState} (hg : Good st) {eLow eHigh : Array Sym} {zS : Option E} {RL : List E}
    (hlen : RL.length = 3) (hel : RpA' st eLow (eLowE zS RL)) (hels : (eLowE zS RL).size = 8)
    (heh : RpA' st eHigh (eHighE RL)) (hehs : (eHighE RL).size = 8) {z : ℕ} (hz : z < 64) :
    PH (eAtS eLow eHigh 8 z) st (fun st' v ↦ Rp' st' v (eAtE zS RL z)) := by
  unfold eAtS eAtE
  rw [loE_3 hlen]
  exact PH.mul hg (hel.get (by omega)) (heh.get (by omega))

/-- **ι's loop**, step for step against `rcE`'s. -/
theorem rcS_ph {st : RecState} (hg : Good st) {eLow eHigh rd : Array Sym} {zS : Option E} {RL CI : List E}
    (hlen : RL.length = 3) (hel : RpA' st eLow (eLowE zS RL)) (hels : (eLowE zS RL).size = 8)
    (heh : RpA' st eHigh (eHighE RL)) (hehs : (eHighE RL).size = 8) (hrd : RpA' st rd (rdE CI))
    (hrds : (rdE CI).size = 32) :
    PH (rcS eLow eHigh 8 rd) st
      (fun st' r ↦ Rp' st' r.1 (rcE zS RL CI).1 ∧ Rp' st' r.2 (rcE zS RL CI).2) := by
  unfold rcS
  dsimp only
  phg (PZ hg) as st1 m0 hs1 hm0
  phg (PZ hg) as st2 l0 hs2 hl0
  rw [List.range_eq_range']
  refine PH.bind' (PH.forIn_rel (List.range' 0 64) (m0, l0) _ ((0 : E), (0 : E)) (rcBodyE zS RL CI)
    (U := rcE zS RL CI) (by unfold rcE; rw [forIn_range_list]) st2
    (fun st' b u ↦ PStep st2 st' ∧ Rp' st' b.1 u.1 ∧ Rp' st' b.2 u.2) hg ⟨PStep.refl _ hg, hm0, hl0⟩ ?_) ?_
  · intro j hj st' b u hs' ⟨hst, h1, h2⟩
    grow_all hg hs'
    simp only [List.length_range'] at hj
    simp only [List.getElem_range', Nat.zero_add, Nat.one_mul]
    unfold rcBodyE
    dsimp only
    split
    · rename_i hemp
      simp only [hemp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact PH.ret hg ⟨_, _, rfl, rfl, hst, h1, h2⟩
    · rename_i hemp
      simp only [hemp, Bool.not_false, ↓reduceIte]
      phg (eAtS_ph hg hlen hel hels heh hehs hj) as st3 ez hs3 hez
      phg (sumL_ph hg _ _ (fun jj ↦ (rdE CI).getD (jj + 2) 0) (fun x hx st' hs' ↦ PH.ret hs'.good
        ((hrd.pgrow hg hs').get (by
          have := of_decide_eq_true (List.mem_filter.mp hx).2
          unfold UniKeccak.rounds at this
          omega)))) as st4 ms hs4 hms
      phg (PH.mul hg hez hms) as st5 em hs5 hem
      phg (PH.add hg h1 hem) as st6 rm hs6 hrm
      split
      · phg (PH.add hg h2 hez) as st7 rl hs7 hrl
        exact PH.ret hg ⟨_, _, rfl, rfl, hst, hrm, hrl⟩
      · exact PH.ret hg ⟨_, _, rfl, rfl, hst, hrm, h2⟩
  · rintro st3 b hs3 ⟨_, h1, h2⟩
    exact PH.ret hs3.good ⟨h1, h2⟩

/-- `ρ ∘ π`'s source lanes and rotations are in range. -/
theorem source_lt : ∀ i < 25, (UniKeccak.source.getD i (0, 0)).1 < 25 ∧ (UniKeccak.source.getD i (0, 0)).2 < 64 := by
  decide +kernel

theorem getD_modifyB (x : Array E) (i j : ℕ) (f : E → E) (hj : j < x.size) :
    (x.modify i f).getD j 0 = if i = j then f (x.getD j 0) else x.getD j 0 := by
  have hj' : j < (x.modify i f).size := by simpa using hj
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj',
    Array.getElem?_eq_getElem hj, Option.getD_some, Option.getD_some, Array.getElem_modify]

/-- Setting a node where `E`'s array is modified. -/
theorem RpA.modifyB {st : RecState} {a : Array Sym} {x : Array E} (h : RpA' st a x) {i : ℕ}
    {s : Sym} {f : E → E} (hv : Rp' st s (f (x.getD i 0))) : RpA' st (a.set! i s) (x.modify i f) := by
  refine ⟨by simp [h.1], fun j hj ↦ ?_⟩
  rw [size_setB] at hj
  rw [getD_setB, getD_modifyB _ _ _ _ (h.1 ▸ hj)]
  by_cases hij : i = j
  · subst hij; rw [iteT ⟨rfl, hj⟩, iteT rfl]; exact hv
  · rw [iteF (fun h' ↦ hij h'.1), iteF hij]; exact h.2 j hj

/-- **The shifts' weights**, lane by lane against `gE`'s loop. -/
theorem gS_ph {st : RecState} (hg : Good st) {alpha c23 vMid vLast kr5 : Sym} {K : KernS} {colLh colPc : Array Sym}
    {A : E} {CI CP : List E} (hCI : CI.length = 11) (hCP : CP.length = 11) (ha : Rp' st alpha A)
    (hc23 : Rp' st c23 (c23E CI)) (hvm : Rp' st vMid (vMidE CI CP)) (hvl : Rp' st vLast (vLastE CP))
    (hk5 : Rp' st kr5 (CI.getD 5 0)) (hK : KernR π iv publicInput stream st K CI CP)
    (hcl : RpA' st colLh (colLhE CP)) (hcp : RpA' st colPc (colPcE CP)) :
    PH (gS alpha c23 vMid vLast kr5 K colLh colPc) st
      (fun st' g ↦ RpA' st' g (gE CI CP A) ∧ (gE CI CP A).size = 64) := by
  have hlrs : (lrE CI).size = 32 := lrE_size CI hCI
  have hrds : (rdE CI).size = 32 := rdE_size CI hCI
  have hlhs : (lhE CP).size = 32 := lhE_size CP hCP
  have hrxs : (rxE CI).size = 25 := by simp [rxE, UniKeccak.lanes]
  have hpcs : (pcE CP).size = 25 := by simp [pcE, UniKeccak.lanes]
  have hcls : (colLhE CP).size = 5 := by simp [colLhE]
  have hcps : (colPcE CP).size = 5 := by simp [colPcE]
  obtain ⟨hlr, hrd, hlh, -, -, -, -, -, -, hrx, hpc⟩ := hK
  unfold gS
  dsimp only
  phg (PZ hg) as st1 zg hs1 hzg
  rw [List.range_eq_range']
  refine PH.bind' (PH.forIn_rel (List.range' 0 UniKeccak.lanes) (Array.replicate 64 zg) _ (Array.replicate 64 (0 : E))
    (gBodyE CI CP A) (U := gE CI CP A) (by unfold gE; rw [forIn_range_list, Nat.sub_zero]) st1
    (fun st' b u ↦ PStep st1 st' ∧ RpA' st' b u ∧ u.size = 64) hg
    ⟨PStep.refl _ hg, RpA.replicate hzg 64, by simp⟩ ?_) fun st' b hs' h ↦ PH.ret hs'.good ⟨h.2.1, h.2.2⟩
  intro j hj st' b u hs' ⟨hst, hb, hu⟩
  grow_all hg hs'
  simp only [List.length_range', UniKeccak.lanes] at hj
  simp only [List.getElem_range', Nat.zero_add, Nat.one_mul]
  obtain ⟨hsrc, hrot⟩ := source_lt j hj
  have hx3 : (j % 5 + 3) % 5 + 5 * (j / 5) < (lrE CI).size := by rw [hlrs]; omega
  have hx4 : (j % 5 + 4) % 5 + 5 * (j / 5) < (lrE CI).size := by rw [hlrs]; omega
  have hjl : j < (lrE CI).size := by rw [hlrs]; omega
  have hjr : j < (rxE CI).size := by rw [hrxs]; omega
  have h2r : 2 < (rdE CI).size := by rw [hrds]; omega
  phg (PH.mul hg ha (hlr.get hx3)) as s1 at_ hs1 hat
  phg (PH.add hg (hlr.get hx4) hat) as s2 t hs2 ht
  phg (PH.add hg ht (hlr.get hjl)) as s3 tl hs3 htl
  phg (PH.mul hg hk5 htl) as s4 ktl hs4 hktl
  phg (PH.add hg ht hktl) as s5 u' hs5 hu'
  phg (PH.mul hg hc23 ht) as s6 ct hs6 hct
  phg (PH.add hg hct (hrx.get hjr)) as s7 last hs7 hlast
  phg (PH.mul hg hvm hu') as s8 vm hs8 hvm'
  phg (PH.mul hg hvl hlast) as s9 vl hs9 hvl'
  phg (PH.add hg hvm' hvl') as s10 v hs10 hv
  phg (PH.mul hg (hrd.get h2r) hu') as s11 w0 hs11 hw0
  rcases hsr : UniKeccak.source.getD j (0, 0) with ⟨src, rot⟩
  rw [hsr] at hsrc hrot
  simp only at hsrc hrot
  have hsr' : (if h : j < UniKeccak.source.size then UniKeccak.source.getInternal j h else (0, 0)) = (src, rot) :=
    hsr
  simp only [hsr']
  have hsl : src < (lhE CP).size := by rw [hlhs]; omega
  have hsp : src < (pcE CP).size := by rw [hpcs]; omega
  have h4 : (src % 5 + 4) % 5 < (colLhE CP).size := by rw [hcls]; omega
  have h4' : (src % 5 + 4) % 5 < (colPcE CP).size := by rw [hcps]; omega
  have h1 : (src % 5 + 1) % 5 < (colLhE CP).size := by rw [hcls]; omega
  have h1' : (src % 5 + 1) % 5 < (colPcE CP).size := by rw [hcps]; omega
  phg (PH.add hg (hlh.get hsl) (hcl.get h4)) as s12 a1 hs12 ha1
  phg (PH.mul hg hv ha1) as s13 va hs13 hva
  phg (PH.add hg (hpc.get hsp) (hcp.get h4')) as s14 a2 hs14 ha2
  phg (PH.mul hg hw0 ha2) as s15 wa hs15 hwa
  phg (PH.add hg hva hwa) as s16 r hs16 hr
  phg (PH.add hg (hb.get (by rw [hu]; exact hrot)) hr) as s17 gr hs17 hgr
  have hb1 := RpA.modifyB hb (i := rot) (f := (· + _)) hgr
  phg (PH.mul hg hv (hcl.get h1)) as s18 vb hs18 hvb
  phg (PH.mul hg hw0 (hcp.get h1')) as s19 wb hs19 hwb
  phg (PH.add hg hvb hwb) as s20 r' hs20 hr'
  phg (PH.add hg (hb1.get (by simp [hu]; omega)) hr') as s21 gr2 hs21 hgr2
  refine PH.ret hg ⟨_, _, rfl, ?_, hst, RpA.modifyB hb1 (i := (rot + 1) % 64) (f := (· + _)) hgr2, by simp [hu]⟩
  unfold gBodyE
  rw [hsr]
  rfl

end Terminal

end RecGraphKeccak.Sim
