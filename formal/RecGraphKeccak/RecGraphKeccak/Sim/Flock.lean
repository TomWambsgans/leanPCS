-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecGraph.Sim.Flock
import RecGraphKeccak.Sim.Terminal
import UniKeccak.Verifier

/-!
# Flock on the Keccak-f block, simulated: `verifyWalkedK` against `UniKeccak.verifyWalkedK`

At the Keccak verifier's shape (`log_n = 17 + 15 = 32`, a skip of 3, `.rec3`), as `RecGraph.Sim`'s `Sim` instances:

* the zerocheck is `RecGraph.Sim.zerocheck_sim` (the same `zerocheck(32, 3, rec3)`);
* `frontK_sim`: `α`, the lincheck's claim, its **11** rounds, the 64 slices: 3696 bytes, 43 challenge nodes, the 43rd
  the lincheck's last round, Flock's point's first coordinate;
* `verifyWalkedK_sim`: the front, the structured terminal (`structuredTerminal_ph`) against the lincheck's last claim,
  a zero, the ring switch's end (`RecGraph.Sim.ringEnd_sim`): Flock's point (26 coordinates), the map and the target;
  49 challenges. `flockSpecK` is it for every permutation, IV, public input and stream.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics UniStatement RecGraph RecGraph.Pi1 RecGraph.Sim RecGraphKeccak.Pi1

section Flock

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

local notation "Rp'" => Rp π iv publicInput stream
local notation "RpL'" => RpL π iv publicInput stream
local notation "OptRp'" => OptRp π iv publicInput stream

section FrontDefs

variable (π iv publicInput stream)

/-- **What the Keccak front leaves, related** (the skip's point drawn, 3 low row coordinates, the 11 lincheck ones and
their 11 rounds' challenges, the 64 slices sent, Flock's point of 26 coordinates). -/
structure FrontRK (st : RecState) (fr : FrontS) (f : Flock.Front) : Prop where
  zSkip : OptRp' st fr.zSkip f.zSkip
  zSome : ∃ z, f.zSkip = some z
  rowLow : RpL' st fr.rowLow f.rowLow
  rowLowLen : f.rowLow.length = 3
  chiIn : RpL' st fr.chiIn f.chiIn
  chiInLen : f.chiIn.length = 11
  chiInPrime : RpL' st fr.chiInPrime f.chiInPrime
  chiInPrimeLen : f.chiInPrime.length = 11
  alpha : Rp' st fr.alpha f.alpha
  rLc : Rp' st fr.rLc f.rLc
  slices : ∃ S, f.slices = some S ∧ RpL' st fr.slices S ∧ S.length = 64
  point : RpL' st fr.point f.point
  pointLen : f.point.length = 26

end FrontDefs

local notation "FrontRK'" => FrontRK π iv publicInput stream

theorem FrontRK.grow {st st' : RecState} (hg : Good st) (hgr : Grows st st') {fr : FrontS} {f : Flock.Front}
    (h : FrontRK' st fr f) : FrontRK' st' fr f := by
  have hk := hg.inv.kinv
  obtain ⟨S, hS1, hS2, hS3⟩ := h.slices
  exact ⟨h.zSkip.grow hk hgr, h.zSome, h.rowLow.grow π iv publicInput stream hk hgr, h.rowLowLen,
    h.chiIn.grow π iv publicInput stream hk hgr, h.chiInLen, h.chiInPrime.grow π iv publicInput stream hk hgr,
    h.chiInPrimeLen, h.alpha.grow π iv publicInput stream hk hgr, h.rLc.grow π iv publicInput stream hk hgr,
    ⟨S, hS1, hS2.grow π iv publicInput stream hk hgr, hS3⟩, h.point.grow π iv publicInput stream hk hgr, h.pointLen⟩

theorem head_rev_appendK (l rest : List ℕ) (h : l.length = 11) : (l.reverse ++ rest).headD 0 = l.getD 10 0 := by
  have hne : l.reverse ≠ [] := by intro h'; have := congrArg List.length h'; simp [h] at this
  rw [List.headD_eq_head?_getD, List.head?_append_of_ne_nil _ hne, List.head?_reverse, List.getLast?_eq_getElem?,
    List.getD_eq_getElem?_getD, h]

theorem getD_42 (L1 : List ℕ) (a : ℕ) (l : List ℕ) (h1 : L1.length = 31) :
    (L1 ++ [a] ++ l).getD 42 0 = l.getD 10 0 := by
  rw [List.getD_append_right _ _ _ _ (by simp [h1])]; simp [h1]

/-- **`front_with(32, KECCAK_REC3, 17)`**: the zerocheck, `α`, the lincheck's 11 rounds, the 64 slices; 43 challenge
nodes, the 43rd the lincheck's last round, Flock's point's first coordinate. -/
theorem frontK_sim (st : RecState) :
    Sim π iv publicInput stream st (Pi1.frontK 32 3 .rec3) (UniKeccak.frontK (Fp π) 32 UniKeccak.keccakRec3)
      3696 43
      (fun st' fr f ↦ FrontRK' st' fr f ∧
        ∃ L, chIds st' = chIds st ++ L ∧ L.length = 43 ∧ L.getD 42 0 = fr.point.headD 0) := by
  refine Sim.of_good fun hg ↦ ?_
  unfold Pi1.frontK UniKeccak.frontK
  dsimp only
  refine Sim.cast (n := 1632 + (0 + (528 + (24 * Flock.kBits + 0))))
    (ch := 31 + (1 + (11 + (0 + 0)))) (by simp [Flock.kBits]) rfl ?_
  refine Sim.bind (zerocheck_sim st) fun st1 x xU hg1 hgr1 ⟨⟨hz, hchi, hvA, hvB, hvC, hchil, hzs⟩, L1, hL1, hL1l⟩ ↦ ?_
  refine Sim.bind (sim_sample π iv publicInput stream st1) fun st2 al alU hg2 hgr2 ⟨hal, hal2, _⟩ ↦ ?_
  have hk1 := hg1.inv.kinv
  refine Sim.pbind' (PSim.mul hg2 hal (hvB.grow π iv publicInput stream hk1 hgr2)) fun st3 t1 hs3 ht1 ↦ ?_
  refine Sim.pbind' (PSim.add hs3.good ((hvA.grow π iv publicInput stream hk1 hgr2).pgrow hg2 hs3) ht1)
    fun st4 s1 hs4 hs1 ↦ ?_
  have hal4 := (hal.pgrow hg2 hs3).pgrow hs3.good hs4
  refine Sim.pbind' (pow_psim st4 hs4.good hal4 2 (by norm_num)) fun st5 a2 hs5 ha2 ↦ ?_
  have hvC5 := ((((hvC.grow π iv publicInput stream hk1 hgr2).pgrow hg2 hs3).pgrow hs3.good hs4).pgrow hs4.good hs5)
  refine Sim.pbind' (PSim.mul hs5.good ha2 hvC5) fun st6 t2 hs6 ht2 ↦ ?_
  refine Sim.pbind' (PSim.add hs6.good ((hs1.pgrow hs4.good hs5).pgrow hs5.good hs6) ht2) fun st7 s2 hs7 hs2 ↦ ?_
  have hal7 := ((hal4.pgrow hs4.good hs5).pgrow hs5.good hs6).pgrow hs6.good hs7
  refine Sim.pbind' (pow_psim st7 hs7.good hal7 3 (by norm_num)) fun st8 a3 hs8 ha3 ↦ ?_
  refine Sim.pbind' (PSim.add hs8.good (hs2.pgrow hs7.good hs8) ha3) fun st9 cl hs9 hcl ↦ ?_
  have hch29 : chIds st9 = chIds st2 :=
    (((((hs9.chal.trans hs8.chal).trans hs7.chal).trans hs6.chal).trans hs5.chal).trans hs4.chal).trans hs3.chal
  rw [← UniStatement.sumcheckDrawn_false]
  refine Sim.bind (Sim.cast (n' := 528) (ch' := 11) (by
      rw [sumcheckBytes_none]; simp [rpBytes, RecGraphKeccak.Pi1.lincheckRoundsK, keccakR1csLogSize, Flock.packing])
    (by simp [RecGraphKeccak.Pi1.lincheckRoundsK, keccakR1csLogSize, Flock.packing])
    (sim_sumcheckDrawn_ch st9 3 false hcl (forall₂_none _)).chIds_len)
    fun st10 sc scU hg10 hgr10 ⟨⟨hpt, hrl, hch⟩, Lsc, hLsc, hLscl⟩ ↦ ?_
  have hlin : sc.1.length = 11 := by
    rw [hch] at hLsc
    rw [List.append_cancel_left hLsc, hLscl]
    simp [RecGraphKeccak.Pi1.lincheckRoundsK, keccakR1csLogSize, Flock.packing]
  refine Sim.bind (sim_nextScalars_len st10 Flock.kBits).chIds_len
    fun st11 sl slU hg11 hgr11 ⟨⟨hsl, hsll⟩, Lsl, hLsl, hLsll⟩ ↦ ?_
  rw [List.length_eq_zero_iff.mp hLsll, List.append_nil] at hLsl
  refine Sim.pure_of_pstep (PStep.refl st11 hg11) ?_
  have hs39 := hs3.trans (hs4.trans (hs5.trans (hs6.trans (hs7.trans (hs8.trans hs9)))))
  have hgr := hgr2.trans (hs39.grows.trans (hgr10.trans hgr11))
  have hchi' := hchi.grow π iv publicInput stream hk1 hgr
  have hptU := hpt.grow π iv publicInput stream hg10.inv.kinv hgr11
  have hsclen : scU.1.length = 11 := by rw [← hpt.length, hlin]
  refine ⟨⟨hz.grow hk1 hgr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hzs
  · exact List.forall₂_take _ hchi'
  · simp [hchil, Flock.packing, UniKeccak.keccakRec3]
  · exact List.forall₂_take _ (List.forall₂_drop _ hchi')
  · simp [hchil, Flock.packing, UniKeccak.keccakRec3, UniKeccak.lincheckRoundsK, keccakR1csLogSize]
  · exact List.rel_reverse hptU
  · simp [hsclen]
  · exact (hal.pgrow hg2 hs39).grow π iv publicInput stream hs39.good.inv.kinv (hgr10.trans hgr11)
  · exact hrl.grow π iv publicInput stream hg10.inv.kinv hgr11
  · exact ⟨slU, rfl, hsl, hsll⟩
  · exact List.rel_append (List.rel_reverse hptU) (List.forall₂_drop _ (List.forall₂_drop _ hchi'))
  · simp [hchil, hsclen, Flock.packing, UniKeccak.keccakRec3, UniKeccak.lincheckRoundsK, keccakR1csLogSize]
  · refine ⟨L1 ++ [al] ++ sc.1, ?_, ?_, ?_⟩
    · show chIds st11 = _
      rw [hLsl, hch, hch29, hal2, hL1, List.append_assoc, List.append_assoc, List.append_assoc]
    · simp [hL1l, hlin]
    · rw [getD_42 _ _ _ hL1l]
      exact (head_rev_appendK _ _ hlin).symm

/-- **`verify_walked_with::<S, Keccak>(32, KECCAK_REC3)`**: the front, the structured terminal against the lincheck's
last claim (its zero), the ring switch's end: Flock's point (26 coordinates), the map and the target; 3696 bytes, 49
challenges, the 43rd Flock's point's first coordinate. -/
theorem verifyWalkedK_sim (st : RecState) :
    Sim π iv publicInput stream st (Pi1.verifyWalkedK 32 3 .rec3)
      (UniKeccak.verifyWalkedK (Fp π) 32 UniKeccak.keccakRec3) 3696 49
      (fun st' a b ↦ RpL' st' a.1 b.1 ∧ b.1.length = 26 ∧
        (∃ mapE tgtE, b.2 = .ring mapE tgtE ∧ RpL' st' a.2.1 mapE ∧ Rp' st' a.2.2 tgtE) ∧
        val π iv publicInput stream st' ((chIds st').getD ((chIds st).length + 42) 0) = b.1.headD 0) := by
  refine Sim.of_good fun hg ↦ ?_
  unfold Pi1.verifyWalkedK UniKeccak.verifyWalkedK
  dsimp only
  refine Sim.cast (n := 3696 + (0 + (0 + 0))) (ch := 43 + (0 + (6 + 0))) rfl rfl ?_
  refine Sim.bind (frontK_sim st) fun st1 fr f hg1 hgr1 ⟨hF, L, hL, hLl, hL42⟩ ↦ ?_
  obtain ⟨S, hS1, hS2, hS3⟩ := hF.slices
  obtain ⟨z, hz⟩ := hF.zSome
  rw [hS1, Option.getD_some]
  have hzS := hF.zSkip
  rw [hz] at hzS
  cases hfz : fr.zSkip with
  | none => rw [hfz] at hzS; exact absurd hzS id
  | some zs =>
  rw [hfz] at hzS
  have hzs : Rp' st1 zs z := hzS
  rw [hz]
  refine Sim.pbind' (PH.psim (R := Rp π iv publicInput stream)
    (structuredTerminal_ph hg1 hzs hF.rowLow hF.rowLowLen hF.chiIn hF.chiInLen hF.chiInPrime hF.chiInPrimeLen hS2 hS3
      hF.alpha))
    fun st2 t hs2 ht ↦ ?_
  generalize UniKeccak.structuredTerminal (some z) f.rowLow f.chiIn f.chiInPrime S f.alpha = WT at ht ⊢
  have hF2 := hF.grow hg1 hs2.grows
  refine Sim.pbind' (PSim.add hs2.good ht hF2.rLc) fun st3 v hs3 hv ↦ ?_
  refine Sim.bind (sim_requireZero π iv publicInput stream st3 v _ hv) fun st4 _ _ hg4 hgr4 ⟨_, hn4⟩ ↦ ?_
  have hgr14 := hs2.grows.trans (hs3.grows.trans hgr4)
  refine Sim.bind (ringEnd_sim st4 (hS2.grow π iv publicInput stream hg1.inv.kinv hgr14) hS3)
    fun st5 r rU hg5 hgr5 ⟨hr, Lm, hLm, hLml⟩ ↦ ?_
  obtain ⟨mapE, tgtE, hrU, hmap, htgt⟩ := hr
  refine Sim.pure_of_pstep (PStep.refl st5 hg5) ?_
  have hpt := hF.point.grow π iv publicInput stream hg1.inv.kinv (hgr14.trans hgr5)
  refine ⟨hpt, hF.pointLen, ⟨mapE, tgtE, hrU, hmap, htgt⟩, ?_⟩
  show val π iv publicInput stream st5 ((chIds st5).getD ((chIds st).length + 42) 0) = f.point.headD 0
  have hc : chIds st5 = chIds st ++ (L ++ Lm) := by
    rw [hLm, chIds_of_nodes hn4, hs3.chal, hs2.chal, hL, List.append_assoc]
  rw [hc, List.getD_append_right _ _ _ _ (by omega), show (chIds st).length + 42 - (chIds st).length = 42 by omega,
    List.getD_append _ _ _ _ (by omega), hL42]
  have key : ∀ (l : List Sym) (l' : List E), RpL' st5 l l' → l'.length = 26 →
      val π iv publicInput stream st5 (l.headD 0) = l'.headD 0 := by
    intro l l' h hl
    cases h with
    | nil => simp at hl
    | cons hab _ => exact hab.2
  exact key _ _ hpt hF.pointLen

end Flock

/-- **Flock on the Keccak-f block, as the composition assumes it**: for every permutation, IV, public input and
stream, `verifyWalkedK` simulates `UniKeccak.verifyWalkedK` at the Keccak verifier's shape. -/
def FlockSpecK : Prop :=
  ∀ (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8) (st : RecState),
    Sim π iv publicInput stream st (Pi1.verifyWalkedK 32 3 .rec3)
      (UniKeccak.verifyWalkedK (Fp π) 32 UniKeccak.keccakRec3) 3696 49
      (fun st' a b ↦ RpL π iv publicInput stream st' a.1 b.1 ∧ b.1.length = 26 ∧
        (∃ mapE tgtE, b.2 = .ring mapE tgtE ∧ RpL π iv publicInput stream st' a.2.1 mapE ∧
          Rp π iv publicInput stream st' a.2.2 tgtE) ∧
        val π iv publicInput stream st' ((chIds st').getD ((chIds st).length + 42) 0) = b.1.headD 0)

theorem flockSpecK : FlockSpecK := fun _ _ _ _ st ↦ verifyWalkedK_sim st

end RecGraphKeccak.Sim
