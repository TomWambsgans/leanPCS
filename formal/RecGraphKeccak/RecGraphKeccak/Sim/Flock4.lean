-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proofs are `Sim/Flock.lean`'s and
-- `RecGraph/Sim/Flock.lean`'s (`zerocheck_sim0`, `frontK_sim`, `verifyWalkedK_sim`) with the zerocheck's first
-- coordinate given.
import RecGraphKeccak.Sim.Flock
import RecGraphKeccak.Pi1.Verifier4
import UniKeccak.Verifier4

/-!
# Flock on the Keccak-f block at π1-rec4, simulated: `verifyWalkedK4` against `UniKeccak.verifyWalkedK4`

π1-rec4's Flock is π1-rec3's with the zerocheck's coordinates after the seven fixed ones the squares of a challenge
drawn before Flock (with the bus's, one wide draw), and no ring switch after the slices:

* `zerocheck4_sim`: the seven fixed coordinates, `c` and its squares (pure: no challenge), the coset, `z`, the rounds,
  `v_a, v_b, v_c`: 1632 bytes, **30** challenge nodes;
* `frontK4_sim`: `α`, the lincheck's 11 rounds, the 64 slices: 3696 bytes, 42 challenge nodes, the 42nd Flock's point's
  first coordinate;
* **`verifyWalkedK4_sim`** (`flockSpecK4`): the front, the structured terminal's zero; Flock's point (26 coordinates)
  and the 64 slices.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics UniStatement RecGraph RecGraph.Pi1 RecGraph.Sim RecGraphKeccak.Pi1

section Flock4

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

local notation "Rp'" => Rp π iv publicInput stream
local notation "RpL'" => RpL π iv publicInput stream
local notation "OptRp'" => OptRp π iv publicInput stream
local notation "FrontRK'" => FrontRK π iv publicInput stream

/-- **`zerocheck(32, 3, rec4, Some(c))`**, without the challenge nodes. -/
theorem zerocheck4_sim0 (st : RecState) {cS : Sym} {cE : E} (hc : Rp' st cS cE) :
    Sim π iv publicInput stream st (Pi1.zerocheck4 32 3 cS) (Flock.zerocheckFirst (Fp π) 32 3 cE) 1632 30
      (fun st' a b ↦ OptRp' st' a.1 b.1 ∧ RpL' st' a.2.1 b.2.1 ∧ Rp' st' a.2.2.1 b.2.2.1 ∧
        Rp' st' a.2.2.2.1 b.2.2.2.1 ∧ Rp' st' a.2.2.2.2 b.2.2.2.2 ∧ b.2.1.length = 29 ∧ ∃ z, b.1 = some z) := by
  refine Sim.of_good fun hg ↦ ?_
  unfold Pi1.zerocheck4 Flock.zerocheckFirst
  dsimp only
  simp only [show (3 : ℕ) > 0 by norm_num, ↓reduceIte]
  refine Sim.cast (n := 24 * 2 ^ 3 + (0 + (0 + (1392 + (24 + (24 + 0))))))
    (ch := 0 + (1 + (0 + (29 + (0 + (0 + 0)))))) (by norm_num) (by norm_num) ?_
  refine Sim.pbind (b := ()) (R := fun st' (acc : Array (Option Sym)) _ ↦
    List.Forall₂ (OptRp' st') acc.toList (Flock.fixedChallenges.map some)) (by
      refine PH.psim ((PH.forIn_list _ _ _ st (fun j st' (acc : Array (Option Sym)) ↦
        List.Forall₂ (OptRp' st') acc.toList ((Flock.fixedChallenges.take j).map some)) hg (by simp) ?_).mono
        fun st' acc _ h ↦ ?_)
      · intro j hj st' acc hs' hacc
        refine PH.bind' (PH.const (π := π) (iv := iv) (publicInput := publicInput) (stream := stream) hs'.good _)
          fun st'' d hs'' hd ↦ PH.ret hs''.good ⟨_, rfl, ?_⟩
        rw [Array.toList_push, take_succ_getElem _ _ hj, List.map_append]
        exact List.rel_append (forall₂_optRp_grow hs'.good hs''.grows hacc) (List.Forall₂.cons hd List.Forall₂.nil)
      · rwa [List.take_length] at h) fun st1 acc hg1 hgr1 hacc ↦ ?_
  have hc1 := hc.grow π iv publicInput stream hg.inv.kinv hgr1
  refine Sim.pbind (squares_psim st1 hg1 hc1 (32 - 3 - Flock.nFixed)) fun st2 drawn hg2 hgr2 hdr ↦ ?_
  have hsl : (UniStatement.squares cE (32 - 3 - Flock.nFixed)).length = 32 - 3 - Flock.nFixed := squares_length _ _
  generalize UniStatement.squares cE (32 - 3 - Flock.nFixed) = sampled at hdr hsl ⊢
  refine Sim.bind (sim_nextScalars π iv publicInput stream st2 (2 ^ 3)) fun st3 cs cU hg3 hgr3 hcs ↦ ?_
  refine Sim.bind (sim_sample π iv publicInput stream st3) fun st4 z zU hg4 hgr4 ⟨hz, _⟩ ↦ ?_
  refine Sim.pbind (zeroP π iv publicInput stream hg4) fun st5 zz hg5 hgr5 hzz ↦ ?_
  have hz5 := hz.grow π iv publicInput stream hg4.inv.kinv hgr5
  have hcs5 := (hcs.grow π iv publicInput stream hg3.inv.kinv hgr4).grow π iv publicInput stream hg4.inv.kinv hgr5
  refine Sim.pbind (PH.psim (R := Rp π iv publicInput stream)
    (lagrangeInterpolate_ph hg5 hz5 (2 ^ (3 + 1)) (show RpL' st5 (List.replicate (2 ^ 3) zz ++ cs)
      (List.replicate (2 ^ 3) 0 ++ cU) from List.rel_append (forall₂_replicate hzz _) hcs5)))
    fun st6 lg hg6 hgr6 hlg ↦ ?_
  generalize Flock.lagrangeInterpolate (2 ^ (3 + 1)) (List.replicate (2 ^ 3) 0 ++ cU) zU = LU at hlg ⊢
  refine Sim.bind (Sim.pure_of_pstep (PStep.refl st6 hg6)
    (R := fun st' (a : Option Sym × Sym) (b : Option E × E) ↦ OptRp' st' a.1 b.1 ∧ Rp' st' a.2 b.2 ∧
      ∃ z', b.1 = some z')
    ?_) fun st7 x xU hg7 hgr7 ⟨hx1, hx2, hx3⟩ ↦ ?_
  · exact ⟨hz5.grow π iv publicInput stream hg5.inv.kinv hgr6, hlg, zU, rfl⟩
  rw [← UniStatement.sumcheckDrawn_false]
  have hgr17 := hgr2.trans (hgr3.trans (hgr4.trans (hgr5.trans (hgr6.trans hgr7))))
  have heqs : List.Forall₂ (OptRp' st7) (acc ++ (List.map some drawn).toArray).toList
      (List.map some (Flock.fixedChallenges ++ sampled)) := by
    rw [Array.toList_append, List.map_append]
    refine List.rel_append (forall₂_optRp_grow hg1 hgr17 hacc) ?_
    exact forall₂_some (hdr.grow π iv publicInput stream hg2.inv.kinv
      (hgr3.trans (hgr4.trans (hgr5.trans (hgr6.trans hgr7)))))
  refine Sim.bind (Sim.cast (n' := 1392) (ch' := 29) (by
      rw [sumcheckBytes_some, List.length_append, fixedChallenges_length, hsl]; simp [rpBytes, Flock.nFixed])
    (by simp [fixedChallenges_length, hsl, Flock.nFixed]) (sim_sumcheckDrawn_ch st7 3 false hx2 heqs).chIds_len)
    fun st8 sc scU hg8 hgr8 ⟨⟨hpt, hcl, hch⟩, L, hL, hLl⟩ ↦ ?_
  have hptl : scU.1.length = 29 := by
    rw [hch] at hL
    rw [← hpt.length, List.append_cancel_left hL, hLl]
    simp [fixedChallenges_length, hsl, Flock.nFixed]
  refine Sim.bind (sim_nextScalar π iv publicInput stream st8) fun st9 vA vAU hg9 hgr9 hvA ↦ ?_
  refine Sim.bind (sim_nextScalar π iv publicInput stream st9) fun st10 vB vBU hg10 hgr10 hvB ↦ ?_
  have hvA' := hvA.grow π iv publicInput stream hg9.inv.kinv hgr10
  refine Sim.of_psim (PSim.bind (PSim.mul hg10 hvA' hvB) fun st11 ab hst11 hab ↦ ?_)
  have hcl' := ((hcl.grow π iv publicInput stream hg8.inv.kinv (hgr9.trans hgr10)).pgrow hg10 hst11)
  refine PSim.bind (PSim.add hst11.good hcl' hab) fun st12 vC hst12 hvC ↦ PSim.pure hst12.good ?_
  have hgr812 := (hgr9.trans hgr10).trans (hst11.grows.trans hst12.grows)
  refine ⟨?_, (hpt.grow π iv publicInput stream hg8.inv.kinv hgr812), ?_, ?_, hvC, hptl, hx3⟩
  · exact hx1.grow hg7.inv.kinv (hgr8.trans hgr812)
  · exact ((hvA'.pgrow hg10 hst11).pgrow hst11.good hst12)
  · exact ((hvB.pgrow hg10 hst11).pgrow hst11.good hst12)

/-- **`zerocheck(32, 3, rec4, Some(c))`**: 30 challenge nodes appended. -/
theorem zerocheck4_sim (st : RecState) {cS : Sym} {cE : E} (hc : Rp' st cS cE) :
    Sim π iv publicInput stream st (Pi1.zerocheck4 32 3 cS) (Flock.zerocheckFirst (Fp π) 32 3 cE) 1632 30
      (fun st' a b ↦ (OptRp' st' a.1 b.1 ∧ RpL' st' a.2.1 b.2.1 ∧ Rp' st' a.2.2.1 b.2.2.1 ∧
        Rp' st' a.2.2.2.1 b.2.2.2.1 ∧ Rp' st' a.2.2.2.2 b.2.2.2.2 ∧ b.2.1.length = 29 ∧ ∃ z, b.1 = some z) ∧
        ∃ L, chIds st' = chIds st ++ L ∧ L.length = 30) :=
  (zerocheck4_sim0 st hc).chIds_len

theorem getD_41 (L1 : List ℕ) (a : ℕ) (l : List ℕ) (h1 : L1.length = 30) :
    (L1 ++ [a] ++ l).getD 41 0 = l.getD 10 0 := by
  rw [List.getD_append_right _ _ _ _ (by simp [h1])]; simp [h1]

/-- **`front_with(32, KECCAK_REC4, 17, Some(c))`**: the zerocheck, `α`, the lincheck's 11 rounds, the 64 slices; 42
challenge nodes, the 42nd the lincheck's last round, Flock's point's first coordinate. -/
theorem frontK4_sim (st : RecState) {cS : Sym} {cE : E} (hc : Rp' st cS cE) :
    Sim π iv publicInput stream st (Pi1.frontK4 32 3 cS) (UniKeccak.frontK4 (Fp π) 32 UniKeccak.keccakRec4 cE)
      3696 42
      (fun st' fr f ↦ FrontRK' st' fr f ∧
        ∃ L, chIds st' = chIds st ++ L ∧ L.length = 42 ∧ L.getD 41 0 = fr.point.headD 0) := by
  refine Sim.of_good fun hg ↦ ?_
  unfold Pi1.frontK4 UniKeccak.frontK4
  dsimp only
  refine Sim.cast (n := 1632 + (0 + (528 + (24 * Flock.kBits + 0))))
    (ch := 30 + (1 + (11 + (0 + 0)))) (by simp [Flock.kBits]) rfl ?_
  refine Sim.bind (zerocheck4_sim st hc) fun st1 x xU hg1 hgr1 ⟨⟨hz, hchi, hvA, hvB, hvC, hchil, hzs⟩, L1, hL1, hL1l⟩ ↦ ?_
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
  · simp [hchil, Flock.packing, UniKeccak.keccakRec4]
  · exact List.forall₂_take _ (List.forall₂_drop _ hchi')
  · simp [hchil, Flock.packing, UniKeccak.keccakRec4, UniKeccak.lincheckRoundsK, keccakR1csLogSize]
  · exact List.rel_reverse hptU
  · simp [hsclen]
  · exact (hal.pgrow hg2 hs39).grow π iv publicInput stream hs39.good.inv.kinv (hgr10.trans hgr11)
  · exact hrl.grow π iv publicInput stream hg10.inv.kinv hgr11
  · exact ⟨slU, rfl, hsl, hsll⟩
  · exact List.rel_append (List.rel_reverse hptU) (List.forall₂_drop _ (List.forall₂_drop _ hchi'))
  · simp [hchil, hsclen, Flock.packing, UniKeccak.keccakRec4, UniKeccak.lincheckRoundsK, keccakR1csLogSize]
  · refine ⟨L1 ++ [al] ++ sc.1, ?_, ?_, ?_⟩
    · show chIds st11 = _
      rw [hLsl, hch, hch29, hal2, hL1, List.append_assoc, List.append_assoc, List.append_assoc]
    · simp [hL1l, hlin]
    · rw [getD_41 _ _ _ hL1l]
      exact (head_rev_appendK _ _ hlin).symm

/-- **`verify_walked::<S, Keccak>(32, KECCAK_REC4, Some(c))`**: the front, the structured terminal against the
lincheck's last claim (its zero); Flock's point (26 coordinates) and the 64 slices; 3696 bytes, 42 challenges, the
42nd Flock's point's first coordinate. -/
theorem verifyWalkedK4_sim (st : RecState) {cS : Sym} {cE : E} (hc : Rp' st cS cE) :
    Sim π iv publicInput stream st (Pi1.verifyWalkedK4 32 3 cS)
      (UniKeccak.verifyWalkedK4 (Fp π) 32 UniKeccak.keccakRec4 cE) 3696 42
      (fun st' a b ↦ RpL' st' a.1 b.1 ∧ b.1.length = 26 ∧ RpL' st' a.2 b.2 ∧ b.2.length = 64 ∧
        val π iv publicInput stream st' ((chIds st').getD ((chIds st).length + 41) 0) = b.1.headD 0) := by
  refine Sim.of_good fun hg ↦ ?_
  unfold Pi1.verifyWalkedK4 UniKeccak.verifyWalkedK4
  dsimp only
  refine Sim.cast (n := 3696 + (0 + (0 + 0))) (ch := 42 + (0 + (0 + 0))) rfl rfl ?_
  refine Sim.bind (frontK4_sim st hc) fun st1 fr f hg1 hgr1 ⟨hF, L, hL, hLl, hL41⟩ ↦ ?_
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
  refine Sim.pure_of_pstep (PStep.refl st4 hg4) ?_
  have hpt := hF.point.grow π iv publicInput stream hg1.inv.kinv hgr14
  refine ⟨hpt, hF.pointLen, hS2.grow π iv publicInput stream hg1.inv.kinv hgr14, hS3, ?_⟩
  show val π iv publicInput stream st4 ((chIds st4).getD ((chIds st).length + 41) 0) = f.point.headD 0
  have hc' : chIds st4 = chIds st ++ L := by
    rw [chIds_of_nodes hn4, hs3.chal, hs2.chal, hL]
  rw [hc', List.getD_append_right _ _ _ _ (by omega), show (chIds st).length + 41 - (chIds st).length = 41 by omega,
    hL41]
  have key : ∀ (l : List Sym) (l' : List E), RpL' st4 l l' → l'.length = 26 →
      val π iv publicInput stream st4 (l.headD 0) = l'.headD 0 := by
    intro l l' h hl
    cases h with
    | nil => simp at hl
    | cons hab _ => exact hab.2
  exact key _ _ hpt hF.pointLen

end Flock4

end RecGraphKeccak.Sim
