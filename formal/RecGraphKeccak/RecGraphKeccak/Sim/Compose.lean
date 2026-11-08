-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraphKeccak.Sim.ComposeSpec

/-!
# The Keccak π1-rec3 verifier, composed: `reduceK` against `UniKeccak.reduceWithK`

`reduce_simQK`: from the parts (`Sim/ComposeSpec.lean`; Flock is `flockSpecK`, proved), `Pi1.reduceK keccak128 words`
simulates `UniKeccak.reduceWithK (Fp π) keccak128 publicWords keccakRec3 .point` for the runs ending off the hazard
(`SimE … NoHazardAtK`), the outputs related by `RedRK` (the roots at their stream offsets `24` and `3752`, the
openings, no pending matrices). The proof is `RecGraph.Sim.reduce_simQ`'s, step for step, at the Keccak shape: the
tables `tablesKeccak`, Flock's 3696 bytes and 49 challenges, `t` the challenge 52 and `p_0` the challenge 45.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph RecGraph.Pi1
  RecGraph.Sim RecGraphKeccak.Pi1

/-! ## The shape's facts -/

theorem hvalidK : (!keccak128.validate true) = false := by decide

theorem hlogNK : keccakR1csLogSize + keccak128.heights.getD opBlake2s 0 = 32 := by decide

theorem heights_lengthK : keccak128.heights.length = 6 := by decide

theorem heights_leK (r : Nat) (hr : r ∈ keccak128.heights) : r ≤ 16 := by
  rw [show keccak128.heights = [15, 16, 15, 16, 14, 15] by decide] at hr
  simp at hr
  omega

theorem constraintVars_eqK : keccak128.constraintVars = 20 := by decide

theorem wLenK_ge : 26 ≤ wLenK := by
  unfold wLenK
  rw [constraintVars_eqK]
  omega

/-! ## `Z_act`, the tail, the hazard -/

section Pieces

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

/-- **`Z_act`** at the Keccak shape. -/
theorem active_psimK (st : RecState) (hg : Good st) {w : List Nat} {wE : List E}
    (hw : RpL π iv publicInput stream st w wE) (hwl : wE.length = wLenK) {counts : List (List Nat)}
    {countsE : List (List E)} (hc : List.Forall₂ (RpL π iv publicInput stream st) counts countsE)
    (hcl : List.Forall₂ (fun bs r ↦ bs.length = r + 1) countsE keccak128.heights) :
    PSim st (forIn (counts.zip keccak128.heights) (#[] : Array Nat) fun x s ↦ do
        let a ← RecGraph.Pi1.activeVanishingFromBits w x.1 x.2
        pure (ForInStep.yield (s.push a))) ()
      (fun st' a _ ↦ RpL π iv publicInput stream st' a.toList
        ((countsE.zip keccak128.heights).map fun x ↦ UniStatement.activeVanishingFromBits wE x.1 x.2)) := by
  have hl1 := List.Forall₂.length_eq hc
  have hl2 := List.Forall₂.length_eq hcl
  refine PSim.mono (PSim.forIn_inv st (counts.zip keccak128.heights)
    (fun i st (s : Array Nat) ↦ RpL π iv publicInput stream st s.toList
      (((countsE.zip keccak128.heights).take i).map fun x ↦ UniStatement.activeVanishingFromBits wE x.1 x.2)) _
    ?_ st #[] (PStep.refl st hg) List.Forall₂.nil) fun st' a _ h ↦ ?_
  · intro i hi st1 s hst hI
    simp only [List.length_zip] at hi
    have hci : i < counts.length := by omega
    have hcE : i < countsE.length := by omega
    have hhi : i < keccak128.heights.length := by omega
    simp only [List.getElem_zip]
    have hbs := ((List.forall₂_iff_get.mp hc).2 i hci hcE).pgrow hg hst
    have hbl := (List.forall₂_iff_get.mp hcl).2 i hcE hhi
    simp only [List.get_eq_getElem] at hbs hbl
    have hr := heights_leK _ (List.getElem_mem hhi)
    have := wLenK_ge
    refine PSim.bind (activeVanishingFromBits_psim st1 hst.good (hw.pgrow hg hst) hbs keccak128.heights[i]
      (by omega) (by omega)) fun st2 a hst2 ha ↦ PSim.pure hst2.good ⟨_, rfl, ?_⟩
    rw [Array.toList_push, take_succ_map _ _ i (by simp; omega)]
    simp only [List.getElem_zip]
    exact (hI.pgrow hst.good hst2).snoc ha
  · simp only [List.length_zip] at h
    rw [List.take_of_length_le (by simp only [List.length_zip]; omega)] at h
    exact h

/-- The tail's `Sim`, in continuation form (the shape `reduceK`'s do-block has). -/
theorem tail_cpsK {OK : List Relation → List (Column × Nat × Bool) → Prop}
    {nB chB : List Relation → List (Column × Nat × Bool) → Nat} (hTail : TailSpecK OK nB chB)
    {st : RecState} (hg : Good st) (h0 : 0 < st.nodes.size) {relsS : List RelationS} {rels : List Relation}
    {rhoS : Nat} {ρ : E} {c2 : List (Column × Nat × Bool)} {mapS : List Nat} {mapE : List E}
    (hr : RpRels π iv publicInput stream st relsS rels) (hrho : Rp π iv publicInput stream st rhoS ρ)
    (hm : RpL π iv publicInput stream st mapS mapE) (hok : OK rels c2)
    {γ δ : Type} {K : List (Commitment × List Sym × Sym) → Prog γ}
    {Kc : List (Commitment × Opening) → ChanM Id δ} {m ch : Nat}
    {S : RecState → γ → δ → Prop}
    (hK : ∀ st' a b, Good st' → Grows st st' → OpeningsR π iv publicInput stream st' a b →
      Sim π iv publicInput stream st' (K a) (Kc b) m ch S) :
    Sim π iv publicInput stream st
      (forIn commitments (#[] : Array (Commitment × CombinedS)) (fun c s ↦ do
          let x ← RecGraph.Pi1.combine relsS c rhoS
          match x with
          | some claim => pure (ForInStep.yield (s.push (c, claim)))
          | _ => pure (ForInStep.yield s)) >>= fun s ↦
        one >>= fun _ ↦ Pi1.batchK s.toList (UniKeccak.layoutsK keccak128 c2) (some mapS) >>= K)
      (tailUK π rels ρ c2 mapE >>= Kc) (nB rels c2 + m) (chB rels c2 + ch) S := by
  have h := Sim.bind (hTail π iv publicInput stream st relsS rels rhoS ρ c2 mapS mapE hg h0 hr hrho hm hok)
    (k := K) (f := Kc) fun st' a b hg' hgr ho ↦ hK st' a b hg' hgr ho
  refine Sim.congr ?_ rfl h
  simp only [tailPK, prog_bind_assoc]
  rfl

end Pieces

/-- `UniKeccak.batchK` only extends the challenges. -/
theorem Mono.batchK (π : KeccakState → KeccakState) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (ringMap : Option (List E)) :
    Mono (UniKeccak.batchK (Fp π) .rec3 combined layouts ringMap) := by
  unfold UniKeccak.batchK
  refine Mono.bind (Mono.sample π) fun lambda ↦ ?_
  dsimp only
  refine Mono.bind (Mono.sumcheckPairsDrawn π _ _ _ _) fun x ↦ ?_
  refine Mono.bind (Mono.ret _) fun x ↦ ?_
  refine Mono.bind (Mono.nextScalars _) fun values ↦ ?_
  exact Mono.bind (Mono.requireZero _) fun _ ↦ Mono.ret _

/-- **On the hazard, no run ends off it**: a run only extends the challenges, so the final channel keeps challenges
45 and 52. -/
theorem not_noHazard_of_monoK {β : Type} {u : ChanM Id β} (hm : Mono u) {c : Chan} (h53 : 53 ≤ c.challenges.size)
    (hz : HazardK (c.challenges.getD 45 0) (c.challenges.getD 52 0)) : ¬ NoHazardAtK ((u.run).run c).2 := by
  obtain ⟨l, hl⟩ := hm c
  unfold NoHazardAtK
  rw [getD_of_prefix hl (by omega), getD_of_prefix hl (by omega), not_not]
  refine ⟨?_, hz⟩
  have e := congrArg List.length hl
  simp only [Array.length_toList, List.length_append] at e
  omega

section Reduce

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

theorem hmodeK : (ClaimsMode.point == ClaimsMode.point) = true := rfl

end Reduce

set_option maxHeartbeats 1000000 in
/-- **`reduce` against `reduceWithFs`**, from the parts: for the runs ending off the hazard at challenges 42 and 49
(`SimE … NoHazardAt`), the roots at their offsets, the openings and no pending matrices (`RedR`). -/
theorem reduce_simQK (PR : PartRep) (hPR : PartRepGrows PR) {TS : Table → List E → TablePart × List Relation → Prop}
    {CS : List E → E → Relation → Prop} {HS : List E → List Relation × List (Column × Nat × Bool) → Prop}
    {OK : List Relation → List (Column × Nat × Bool) → Prop} {nT : Table → Nat}
    {nB chB : List Relation → List (Column × Nat × Bool) → Nat}
    (hT : TableSpecK PR TS nT) (hC : ConstraintSpecK PR CS) (hD : DegreeSpecK) (hH : HeapSpecK PR HS)
    (hTail : TailSpecK OK nB chB) (hS : ShapeSpecK TS CS HS OK)
    {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}
    (st : RecState) (words : List Nat) (wordsE : List E) (hg : Good st) (hseed : st.nodes[0]? = some Node.seed)
    (hcur : st.cursor = 0) (hch : chIds st = []) (hw : RpL π iv publicInput stream st words wordsE)
    (hwl : wordsE.length = 4) :
    SimE π iv publicInput stream NoHazardAtK st (Pi1.reduceK keccak128 words)
      (UniKeccak.reduceWithK (Fp π) keccak128 wordsE UniKeccak.keccakRec3 .point)
      (RedRK π iv publicInput stream) := by
  have hG0 : Grows st st := Grows.refl st
  unfold Pi1.reduceK
  simp only [UniKeccak.reduceWithK, hvalidK, Bool.false_eq_true, ↓reduceIte, hmodeK]
  rw [hlogNK]
  -- 0. The row counts.
  refine SimE.bind ((sim_countBits st keccak128.heights).withChIds.withCursor) ?_
  intro s1 counts countsE g1 gr1 hR
  obtain ⟨⟨⟨hcnt, hcntl⟩, l1, hl1, hl1n⟩, hcur1⟩ := hR
  regrow hg gr1
  have hch1 : chIds s1 = [] := by rw [hl1, hch, List.eq_nil_of_length_eq_zero hl1n]; rfl
  have hcur1' : s1.cursor = 24 := by rw [hcur1, hcur, heights_lengthK]
  have hG1 : Grows s1 s1 := Grows.refl s1
  -- 1. C1's root, α, β, γ.
  refine SimE.bind ((sim_nextRoot π iv publicInput stream s1).withChIds.withCursor) ?_
  intro s2 root1 root1E g2 gr2 hR
  obtain ⟨⟨⟨hr1a, hr1b, hr1na, hr1nb⟩, l2, hl2, hl2n⟩, hcur2⟩ := hR
  regrow g1 gr2
  have hch2 : chIds s2 = [] := by rw [hl2, hch1, List.eq_nil_of_length_eq_zero hl2n]; rfl
  have hG2 : Grows s2 s2 := Grows.refl s2
  refine SimE.bind ((sim_drawRun_rec3 s2 4).withChIds.withCursor) ?_
  intro s3 alphas alphasE g3 gr3 hR
  obtain ⟨⟨⟨halpha, halphal⟩, l3, hl3, hl3n⟩, hcur3⟩ := hR
  regrow g2 gr3
  refine SimE.bind (sim_sample π iv publicInput stream s3).withCursor ?_
  intro s4 beta betaE g4 gr4 hR
  obtain ⟨⟨hbeta, hch4, -, -⟩, hcur4⟩ := hR
  regrow g3 gr4
  refine SimE.bind (sim_sample π iv publicInput stream s4).withCursor ?_
  intro s5 gamma gammaE g5 gr5 hR
  obtain ⟨⟨hgamma, hch5, -, -⟩, hcur5⟩ := hR
  regrow g4 gr5
  have hlen5 : (chIds s5).length = 3 := by
    rw [hch5, hch4, hl3, hch2]; simp at hl3n ⊢; omega
  refine SimE.pbind (eqKernel_psim s5 g5 halpha) ?_
  intro s6 weights ps6 hwts
  have gr6 := ps6.grows
  have g6 := ps6.good
  regrow g5 gr6
  have hlen6 : (chIds s6).length = 3 := by rw [ps6.chal, hlen5]
  -- 2. Flock.
  refine SimE.bind ((flockSpecK π iv publicInput stream s6).withChIds.withCursor) ?_
  intro s7 fl flE g7 gr7 hR
  obtain ⟨⟨⟨hfp, hfpl, ⟨mapE, tgtE, hend, hmap, htgt⟩, hp0⟩, l7, hl7, hl7n⟩, hcur7⟩ := hR
  regrow g6 gr7
  obtain ⟨fp, map, tgt⟩ := fl
  obtain ⟨fpE, endE⟩ := flE
  simp only at hend hfp hfpl hmap htgt hp0
  subst hend
  rw [hlen6] at hp0
  have hlen7 : (chIds s7).length = 52 := by rw [hl7, List.length_append, hlen6, hl7n]
  have hG7 : Grows s7 s7 := Grows.refl s7
  have hcur7' : s7.cursor = 3752 := by
    rw [hcur7, ps6.cursor, hcur5, hcur4, hcur3, hcur2, hcur1']
  clear hcur7 hcur5 hcur4 hcur3 hcur2 hcur1 hcur hl1 hl1n hl2 hl2n hl3 hl3n hch1 hch2 hch4 hch5 hlen5 hlen6 hl7 hl7n
  dsimp only
  -- 3. C2's root, t, the digits, Z_act.
  refine SimE.bind ((sim_nextRoot π iv publicInput stream s7).withChIds) ?_
  intro s8 root2 root2E g8 gr8 hR
  obtain ⟨⟨hr2a, hr2b, hr2na, hr2nb⟩, l8, hl8, hl8n⟩ := hR
  regrow g7 gr8
  have hlen8 : (chIds s8).length = 52 := by rw [hl8, List.length_append, hlen7, hl8n]
  have hG8 : Grows s8 s8 := Grows.refl s8
  rw [hcur7'] at hr2na hr2nb
  refine SimE.bind (sim_sample π iv publicInput stream s8) ?_
  intro s9 t tE g9 gr9 hR
  obtain ⟨ht, hch9, -, -⟩ := hR
  regrow g8 gr9
  have hG9 : Grows s9 s9 := Grows.refl s9
  have ht49 : (chIds s9).getD 52 0 = t := by
    rw [hch9, List.getD_eq_getElem _ _ (by simp [hlen8]), List.getElem_append_right (by omega)]
    simp [hlen8]
  have hlen9 : (chIds s9).length = 53 := by rw [hch9]; simp [hlen8]
  clear hch9 hl8 hl8n hlen8
  refine SimE.pbind (digits_psim s9 g9 ht wLenK) ?_
  intro s10 w ps10 hw10
  have gr10 := ps10.grows
  have g10 := ps10.good
  regrow g9 gr10
  have hcnt10 := RpLL.sg g1.inv.kinv hG1 hcnt
  refine SimE.pbind (active_psimK s10 g10 hw10 (digits_length _ _) hcnt10 hcntl) ?_
  intro s11 active ps11 hact
  have gr11 := ps11.grows
  have g11 := ps11.good
  regrow g10 gr11
  clear hcnt10
  -- 4. The tables.
  have hws : (UniStatement.eqKernel alphasE).size = 16 := by simp [eqKernel_sizeC, halphal]
  have hG11 : Grows s11 s11 := Grows.refl s11
  refine SimE.bind (Sim.forIn_list s11 tablesKeccak tablesKeccak
    (fun i st (s : Array RelationS × Array TablePartS) (u : Array Relation × Array TablePart) ↦
      RpRels π iv publicInput stream st s.1.toList u.1.toList ∧
      List.Forall₂ (PR π iv publicInput stream st) s.2.toList u.2.toList ∧
      ∃ outs : List (TablePart × List Relation),
        List.Forall₂ (fun tb o ↦ TS tb (UniStatement.digits tE wLenK) o) (tablesKeccak.take i) outs ∧
        u.1 = tabRels outs ∧ u.2.toList = outs.map (·.1))
    (fun i ↦ (tablesKeccak.map nT).getD i 0) (fun _ ↦ 0) _ _ rfl ?_ s11 (#[], #[]) (#[], #[]) g11 (Grows.refl s11)
    ⟨List.Forall₂.nil, List.Forall₂.nil, [], List.Forall₂.nil, rfl, rfl⟩) ?_
  · intro i hi _ st' s u g' gr' hI
    obtain ⟨hrels, hparts, outs, hts, hu1, hu2⟩ := hI
    have hk11 := g11.inv.kinv
    refine Sim.cast (n := nT tablesKeccak[i] + 0) (ch := 0 + 0)
      (by rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]; rfl) rfl ?_
    refine Sim.bind (hT π iv publicInput stream st' tablesKeccak[i] (List.getElem_mem hi) weights
      (UniStatement.eqKernel alphasE) beta betaE w (UniStatement.digits tE wLenK) (nodes_grow (hG0.trans gr') hseed)
      (hwts.sg hk11 gr') hws (hbeta.sg hk11 gr') (hw10.sg hk11 gr') (digits_length _ _)) ?_
    intro st'' a b g'' gr'' hR
    obtain ⟨hpr, hrr, hts1⟩ := hR
    refine Sim.pure_of_pstep (PStep.refl st'' g'') ⟨_, _, rfl, rfl, ?_⟩
    refine ⟨RpRels.append (hrels.sg g'.inv.kinv gr'') hrr, ?_, outs ++ [b], ?_, ?_, ?_⟩
    · rw [Array.toList_push, Array.toList_push]
      exact List.rel_append (hparts.imp fun _ _ h ↦ hPR π iv publicInput stream st' st'' _ _ g'.inv.kinv gr'' h)
        (List.Forall₂.cons hpr List.Forall₂.nil)
    · rw [List.take_add_one, List.getElem?_eq_getElem hi]
      exact List.rel_append hts (List.Forall₂.cons hts1 List.Forall₂.nil)
    · rw [hu1]; unfold tabRels; rw [List.foldl_append]; rfl
    · rw [Array.toList_push, hu2, List.map_append]; rfl
  intro s12 S T g12 gr12 hI
  obtain ⟨hrelsT, hpartsT, outs, htsT, hT1, hT2⟩ := hI
  rw [hT1] at hrelsT
  regrow g11 gr12
  have hG12 : Grows s12 s12 := Grows.refl s12
  have htabs : List.Forall₂ (fun tb o ↦ TS tb (UniStatement.digits tE wLenK) o) tablesKeccak outs := by
    rw [List.take_length] at htsT; exact htsT
  have houtl : outs.length = 6 := by rw [← htabs.length_eq]; rfl
  have hpl : T.2.toList.length = 6 := by rw [hT2, List.length_map, houtl]
  -- The memory's and the bytecode's values.
  refine SimE.pbind (oneP π iv publicInput stream g12) ?_
  intro s13 o ps13 ho
  have gr13 := ps13.grows; have g13 := ps13.good; regrow g12 gr13
  refine SimE.bind (sim_nextScalar π iv publicInput stream s13) ?_
  intro s14 mfc mfcE g14 gr14 hmfc
  regrow g13 gr14
  refine SimE.bind (sim_nextScalar π iv publicInput stream s14) ?_
  intro s15 addr addrE g15 gr15 haddr
  regrow g14 gr15
  refine SimE.bind (sim_nextScalar π iv publicInput stream s15) ?_
  intro s16 mpl mplE g16 gr16 hmpl
  regrow g15 gr16
  refine SimE.pbind (equalS_psim s16 g16 (.memory 3)
    (RpL.takeC π iv publicInput stream hw10 keccak128.logMemory) hmfc) ?_
  intro s17 d1 ps17 hd1
  have gr17 := ps17.grows; have g17 := ps17.good; regrow g16 gr17
  refine SimE.pbind (equalS_psim s17 g17 .address
    (RpL.takeC π iv publicInput stream hw10 keccak128.logMemory) haddr) ?_
  intro s18 d2 ps18 hd2
  have gr18 := ps18.grows; have g18 := ps18.good; regrow g17 gr18
  refine SimE.pbind (PSim.add g18 hmpl hbeta) ?_
  intro s19 mp1 ps19 hmp1
  have gr19 := ps19.grows; have g19 := ps19.good; regrow g18 gr19
  refine SimE.pbind (constP π iv publicInput stream g19 sepMem) ?_
  intro s20 cm ps20 hcm
  have gr20 := ps20.grows; have g20 := ps20.good; regrow g19 gr20
  refine SimE.pbind (PSim.mul g20 (hwts.arr (k := 0) (by rw [hws]; omega)) hcm) ?_
  intro s21 w0m ps21 hw0m
  have gr21 := ps21.grows; have g21 := ps21.good; regrow g20 gr21
  refine SimE.pbind (PSim.add g21 hmp1 hw0m) ?_
  intro s22 mp2 ps22 hmp2
  have gr22 := ps22.grows; have g22 := ps22.good; regrow g21 gr22
  refine SimE.pbind (PSim.mul g22 (hwts.arr (k := 1) (by rw [hws]; omega)) haddr) ?_
  intro s23 w1a ps23 hw1a
  have gr23 := ps23.grows; have g23 := ps23.good; regrow g22 gr23
  refine SimE.pbind (PSim.add g23 hmp2 hw1a) ?_
  intro s24 mp3 ps24 hmp3
  have gr24 := ps24.grows; have g24 := ps24.good; regrow g23 gr24
  refine SimE.pbind (PSim.mul g24 (hwts.arr (k := 2) (by rw [hws]; omega)) hmfc) ?_
  intro s25 w2m ps25 hw2m
  have gr25 := ps25.grows; have g25 := ps25.good; regrow g24 gr25
  refine SimE.pbind (PSim.add g25 hmp3 hw2m) ?_
  intro s26 mp4 ps26 hmp4
  have gr26 := ps26.grows; have g26 := ps26.good; regrow g25 gr26
  refine SimE.pbind (PSim.add g26 ho hmfc) ?_
  intro s27 om ps27 hom
  have gr27 := ps27.grows; have g27 := ps27.good; regrow g26 gr27
  refine SimE.pbind (PSim.mul g27 (hwts.arr (k := 2) (by rw [hws]; omega)) hom) ?_
  intro s28 w2om ps28 hw2om
  have gr28 := ps28.grows; have g28 := ps28.good; regrow g27 gr28
  refine SimE.pbind (PSim.add g28 hmpl hw2om) ?_
  intro s29 mps ps29 hmps
  have gr29 := ps29.grows; have g29 := ps29.good; regrow g28 gr29
  refine SimE.bind (sim_nextScalar π iv publicInput stream s29) ?_
  intro s30 bfc bfcE g30 gr30 hbfc
  regrow g29 gr30
  refine SimE.bind (sim_nextScalar π iv publicInput stream s30) ?_
  intro s31 bpl bplE g31 gr31 hbpl
  regrow g30 gr31
  refine SimE.pbind (equalS_psim s31 g31 .bytecodeFinal
    (RpL.takeC π iv publicInput stream hw10 keccak128.logBytecode) hbfc) ?_
  intro s32 d3 ps32 hd3
  have gr32 := ps32.grows; have g32 := ps32.good; regrow g31 gr32
  refine SimE.pbind (PSim.add g32 hbpl hbeta) ?_
  intro s33 bp1 ps33 hbp1
  have gr33 := ps33.grows; have g33 := ps33.good; regrow g32 gr33
  refine SimE.pbind (PSim.mul g33 (hwts.arr (k := 2) (by rw [hws]; omega)) hbfc) ?_
  intro s34 w2b ps34 hw2b
  have gr34 := ps34.grows; have g34 := ps34.good; regrow g33 gr34
  refine SimE.pbind (PSim.add g34 hbp1 hw2b) ?_
  intro s35 bp2 ps35 hbp2
  have gr35 := ps35.grows; have g35 := ps35.good; regrow g34 gr35
  refine SimE.pbind (equalS_psim s35 g35 .bytecodeTuple
    (RpL.appendC π iv publicInput stream halpha (RpL.takeC π iv publicInput stream hw10 keccak128.logBytecode))
    hbp2) ?_
  intro s36 d4 ps36 hd4
  have gr36 := ps36.grows; have g36 := ps36.good; regrow g35 gr36
  refine SimE.pbind (PSim.add g36 ho hbfc) ?_
  intro s37 ob ps37 hob
  have gr37 := ps37.grows; have g37 := ps37.good; regrow g36 gr37
  refine SimE.pbind (PSim.mul g37 (hwts.arr (k := 2) (by rw [hws]; omega)) hob) ?_
  intro s38 w2ob ps38 hw2ob
  have gr38 := ps38.grows; have g38 := ps38.good; regrow g37 gr38
  refine SimE.pbind (PSim.add g38 hbpl hw2ob) ?_
  intro s39 bps ps39 hbps
  have gr39 := ps39.grows; have g39 := ps39.good; regrow g38 gr39
  refine SimE.bind (sim_nextScalar π iv publicInput stream s39) ?_
  intro s40 hv hvE g40 gr40 hhv
  regrow g39 gr40
  refine SimE.bind (sim_nextScalar π iv publicInput stream s40) ?_
  intro s41 cv cvE g41 gr41 hcv
  regrow g40 gr41
  -- 5. The constraint quotient's relation.
  have hparts41 := hpartsT.imp fun _ _ h ↦ hPR π iv publicInput stream s12 s41 _ _ g12.inv.kinv hG12 h
  refine SimE.pbind (hC π iv publicInput stream s41 S.2.toList T.2.toList words wordsE gamma t cv gammaE tE cvE w
    (UniStatement.digits tE wLenK) g41 (nodes_grow hG0 hseed) hparts41 hw hwl hgamma ht hcv hw10 rfl) ?_
  intro s42 constraint ps42 hcons
  obtain ⟨hconsR, hCS⟩ := hcons
  have gr42 := ps42.grows; have g42 := ps42.good; regrow g41 gr42
  clear hparts41
  rw [hD T.2.toList wordsE gammaE tE cvE (UniStatement.digits tE wLenK) hpl]
  -- 6. The heap's relations.
  have hparts42 := hpartsT.imp fun _ _ h ↦ hPR π iv publicInput stream s12 s42 _ _ g12.inv.kinv hG12 h
  have hactl : ((countsE.zip keccak128.heights).map fun x ↦
      UniStatement.activeVanishingFromBits (UniStatement.digits tE wLenK) x.1 x.2).length = 6 := by
    simp [hcntl.length_eq, heights_lengthK]
  refine SimE.pbind (hH π iv publicInput stream s42 active.toList _ S.2.toList T.2.toList weights
    (UniStatement.eqKernel alphasE) beta hv cv mpl mps bpl bps betaE hvE cvE mplE _ bplE _ w
    (UniStatement.digits tE wLenK) g42 (nodes_grow hG0 hseed) hact hactl hparts42 hpl hwts hws hbeta hhv hcv hmpl
    hmps hbpl hbps hw10 (digits_length _ _)) ?_
  intro s43 heapP ps43 hheap
  obtain ⟨hheapR, hcols, hHS⟩ := hheap
  have gr43 := ps43.grows; have g43 := ps43.good; regrow g42 gr43
  clear hparts42
  rw [hcols]
  -- 7. Flock's claim on q_flock.
  refine SimE.pbind (oneP π iv publicInput stream g43) ?_
  intro s44 o4 ps44 ho4
  have gr44 := ps44.grows; have g44 := ps44.good; regrow g43 gr44
  -- The hazard at the recorder's challenges 42 and 49.
  obtain ⟨l9, hl9⟩ := chIds_grows hG9
  have hlen44 : 53 ≤ (chIds s44).length := by rw [hl9, List.length_append, hlen9]; omega
  have h42 : (chIds s44).getD 45 0 = (chIds s7).getD 45 0 := chIds_getD_grow hG7 (by omega)
  have h49 : (chIds s44).getD 52 0 = t := by rw [chIds_getD_grow hG9 (by omega), ht49]
  have h42lt : (chIds s7).getD 45 0 < s7.nodes.size := by
    apply chIds_lt
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hp0' : val π iv publicInput stream s44 ((chIds s44).getD 45 0) = fpE.headD 0 := by
    rw [h42, val_sg g7.inv.kinv hG7 h42lt]
    exact hp0
  have ht44 : val π iv publicInput stream s44 ((chIds s44).getD 52 0) = tE := by rw [h49]; exact ht.2
  refine SimE.of_cond (¬ HazardK (val π iv publicInput stream s44 ((chIds s44).getD 45 0))
    (val π iv publicInput stream s44 ((chIds s44).getD 52 0))) ?_ ?_
  · intro hP
    rw [hp0', ht44] at hP
    refine SimE.bind (sim_sample π iv publicInput stream s44) ?_
    intro s45 rho rhoE g45 gr45 hR
    obtain ⟨hrho, -, -, -⟩ := hR
    regrow g44 gr45
    have hok := hS tE alphasE betaE fpE tgtE outs mfcE addrE mplE bfcE bplE _ _ halphal hfpl htabs hCS hHS hP
    rw [hT1]
    have h0' : 0 < s45.nodes.size := by
      have := nodes_grow hG0 hseed
      rcases Nat.lt_or_ge 0 s45.nodes.size with h | h
      · exact h
      · simp [Array.getElem?_eq_none h] at this
    refine SimE.of_sim (tail_cpsK (m := 0) (ch := 0) hTail g45 h0' (RpRels.push (RpRels.append (RpRels.push (RpRels.push (RpRels.push
      (RpRels.push (RpRels.push (RpRels.push hrelsT hd1) hd2) (memRel_rp hw10 hwts hws hmp4 keccak128.logMemory))
        hd3) hd4) hconsR) hheapR) (ringRel_rp hfp ho4 htgt)) hrho hmap hok ?_)
    intro s46 openings b g46 gr46 hop
    have hk45 := g45.inv.kinv
    refine Sim.pure_of_pstep (PStep.refl s46 g46) ⟨⟨hr1a.sg hk45 gr46, hr1b.sg hk45 gr46, ?_, ?_⟩,
      ⟨hr2a.sg hk45 gr46, hr2b.sg hk45 gr46, nodes_grow (hG8.trans gr46) hr2na,
        nodes_grow (hG8.trans gr46) hr2nb⟩, hop, rfl⟩
    · rw [← hcur1']; exact nodes_grow (hG2.trans gr46) hr1na
    · rw [← hcur1']; exact nodes_grow (hG2.trans gr46) hr1nb
  · intro hnP c hc
    rw [not_not] at hnP
    have hsize : (chIds s44).length = c.challenges.size := by
      have e := congrArg List.length hc.chal
      simpa using e.symm
    refine not_noHazard_of_monoK (Mono.bind (Mono.sample π) fun _ ↦ Mono.bind (Mono.batchK π _ _ _) fun x ↦ Mono.ret _) (by omega) ?_
    rw [couple_getD hc (by omega), couple_getD hc (by omega)]
    exact hnP

end RecGraphKeccak.Sim
