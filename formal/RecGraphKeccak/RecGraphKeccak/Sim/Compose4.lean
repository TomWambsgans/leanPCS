-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proof is `Sim/Compose.lean`'s `reduce_simQK`, step for
-- step, with π1-rec4's draws.
import RecGraphKeccak.Sim.Compose
import RecGraphKeccak.Sim.Flock4
import RecGraphKeccak.Sim.BatchK4
import RecGraphKeccak.Main4
import RecGraph.Sim.Wide

/-!
# The Keccak π1-rec4 verifier, composed: `reduceK4` against `UniKeccak.reduceWithK4`

`reduce_simQK4`: from the parts (`Sim/ComposeSpec.lean`'s `TableSpecK`, `ConstraintSpecK`, `DegreeSpecK`, `HeapSpecK`,
`ShapeSpecK`, the same as π1-rec3's: π1-rec4 states the same relations; Flock is `verifyWalkedK4_sim`, the tail
`TailSpecK4`), `Pi1.reduceK4 keccak128 words` simulates `UniKeccak.reduceWithK4 (Fp π) keccak128 publicWords
keccakRec4 .point` for the runs ending off the hazard (`SimE … NoHazardAtK4`: `p_0` the challenge 45, `t` the challenge
46), the outputs related by `RedRK` (the roots at their stream offsets `24` and `3776`, as π1-rec3's). Its steps are
`reduce_simQK`'s but for the draws: the bus's wide draw (`sim_sampleWide 4`: `c`, `β`, `γ`, the zerocheck's `c'`),
`α` the squares of `c` (pure), Flock with `c'` (`verifyWalkedK4_sim`, 42 challenges), the wide draw after `C2`'s
commitment (`t`, `f_0 … f_3`), and after the heap's relations the wide draw of `ρ`, `λ`, `f_4`, `f_5`, the ring switch's
target (`towerTarget_ph`) and its relation, then the tail with `λ` given.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph RecGraph.Pi1
  RecGraph.Sim RecGraphKeccak.Pi1

/-- No hazard at a channel's challenges `45` (`p_0`) and `46` (`t`), `t` drawn: `MergeHazardK4`'s condition. -/
def NoHazardAtK4 (c : Chan) : Prop :=
  ¬ (47 ≤ c.challenges.size ∧ HazardK (c.challenges.getD 45 0) (c.challenges.getD 46 0))

/-- `UniStatement.sampleWide` only extends the challenges. -/
theorem Mono.sampleWide (π : KeccakState → KeccakState) (n : Nat) : Mono (UniStatement.sampleWide (Fp π) n) :=
  fun c ↦ ⟨wideChalsOf π n c, by rw [sampleWide_run]; simp⟩

/-- `UniKeccak.batchK4` only extends the challenges. -/
theorem Mono.batchK4 (π : KeccakState → KeccakState) (lambda : E) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (ringMap : Option (List E)) :
    Mono (UniKeccak.batchK4 (Fp π) lambda combined layouts ringMap) := by
  unfold UniKeccak.batchK4
  dsimp only
  refine Mono.bind (Mono.sumcheckPairsDrawn π _ _ _ _) fun x ↦ ?_
  refine Mono.bind (Mono.nextScalars _) fun values ↦ ?_
  exact Mono.bind (Mono.requireZero _) fun _ ↦ Mono.ret _

/-- **On the hazard, no run ends off it** (π1-rec4's challenges 45 and 46). -/
theorem not_noHazard_of_monoK4 {β : Type} {u : ChanM Id β} (hm : Mono u) {c : Chan} (h47 : 47 ≤ c.challenges.size)
    (hz : HazardK (c.challenges.getD 45 0) (c.challenges.getD 46 0)) : ¬ NoHazardAtK4 ((u.run).run c).2 := by
  obtain ⟨l, hl⟩ := hm c
  unfold NoHazardAtK4
  rw [getD_of_prefix hl (by omega), getD_of_prefix hl (by omega), not_not]
  refine ⟨?_, hz⟩
  have e := congrArg List.length hl
  simp only [Array.length_toList, List.length_append] at e
  omega

section Pieces

variable {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}

/-- The tail's `Sim` at π1-rec4, in continuation form (the shape `reduceK4`'s do-block has). -/
theorem tail_cpsK4 {OK : List Relation → List (Column × Nat × Bool) → Prop}
    {nB chB : List Relation → List (Column × Nat × Bool) → Nat} (hTail : TailSpecK4 OK nB chB)
    {st : RecState} (hg : Good st) (h0 : 0 < st.nodes.size) {relsS : List RelationS} {rels : List Relation}
    {rhoS lamS : Nat} {ρ lamE : E} {c2 : List (Column × Nat × Bool)} {mapS : List Nat} {mapE : List E}
    (hr : RpRels π iv publicInput stream st relsS rels) (hrho : Rp π iv publicInput stream st rhoS ρ)
    (hlam : Rp π iv publicInput stream st lamS lamE)
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
        one >>= fun _ ↦ Pi1.batchK4 lamS s.toList (UniKeccak.layoutsK keccak128 c2) (some mapS) >>= K)
      (tailUK4 π rels ρ lamE c2 mapE >>= Kc) (nB rels c2 + m) (chB rels c2 + ch) S := by
  have h := Sim.bind (hTail π iv publicInput stream st relsS rels rhoS lamS ρ lamE c2 mapS mapE hg h0 hr hrho hlam hm
    hok) (k := K) (f := Kc) fun st' a b hg' hgr ho ↦ hK st' a b hg' hgr ho
  refine Sim.congr ?_ rfl h
  simp only [tailPK4, prog_bind_assoc]
  rfl

end Pieces

set_option maxHeartbeats 2000000 in
/-- **`reduce` at π1-rec4 against `reduceWithK4`**, from the parts: for the runs ending off the hazard at challenges
45 and 46 (`SimE … NoHazardAtK4`), the roots at their offsets, the openings and no pending matrices (`RedRK`). -/
theorem reduce_simQK4 (PR : PartRep) (hPR : PartRepGrows PR) {TS : Table → List E → TablePart × List Relation → Prop}
    {CS : List E → E → Relation → Prop} {HS : List E → List Relation × List (Column × Nat × Bool) → Prop}
    {OK : List Relation → List (Column × Nat × Bool) → Prop} {nT : Table → Nat}
    {nB chB : List Relation → List (Column × Nat × Bool) → Nat}
    (hT : TableSpecK PR TS nT) (hC : ConstraintSpecK PR CS) (hD : DegreeSpecK) (hH : HeapSpecK PR HS)
    (hTail : TailSpecK4 OK nB chB) (hS : ShapeSpecK TS CS HS OK)
    {π : KeccakState → KeccakState} {iv publicInput : List UInt8} {stream : Array UInt8}
    (st : RecState) (words : List Nat) (wordsE : List E) (hg : Good st) (hseed : st.nodes[0]? = some Node.seed)
    (hcur : st.cursor = 0) (hch : chIds st = []) (hw : RpL π iv publicInput stream st words wordsE)
    (hwl : wordsE.length = 4) :
    SimE π iv publicInput stream NoHazardAtK4 st (Pi1.reduceK4 keccak128 words)
      (UniKeccak.reduceWithK4 (Fp π) keccak128 wordsE UniKeccak.keccakRec4 .point)
      (RedRK π iv publicInput stream) := by
  have hG0 : Grows st st := Grows.refl st
  unfold Pi1.reduceK4
  simp only [UniKeccak.reduceWithK4, hvalidK, Bool.false_eq_true, ↓reduceIte, hmodeK]
  rw [hlogNK]
  -- 0. The row counts.
  refine SimE.bind ((sim_countBits st keccak128.heights).withChIds.withCursor) ?_
  intro s1 counts countsE g1 gr1 hR
  obtain ⟨⟨⟨hcnt, hcntl⟩, l1, hl1, hl1n⟩, hcur1⟩ := hR
  regrow hg gr1
  have hch1 : chIds s1 = [] := by rw [hl1, hch, List.eq_nil_of_length_eq_zero hl1n]; rfl
  have hcur1' : s1.cursor = 24 := by rw [hcur1, hcur, heights_lengthK]
  have hG1 : Grows s1 s1 := Grows.refl s1
  -- 1. C1's root and out-of-domain answer, then the bus's wide draw.
  refine SimE.bind ((sim_nextRoot π iv publicInput stream s1).withChIds.withCursor) ?_
  intro s2r root1 root1E g2r gr2r hR
  obtain ⟨⟨⟨hr1a, hr1b, hr1na, hr1nb⟩, l2r, hl2r, hl2rn⟩, hcur2r⟩ := hR
  regrow g1 gr2r
  have hch2r : chIds s2r = [] := by rw [hl2r, hch1, List.eq_nil_of_length_eq_zero hl2rn]; rfl
  have hG2r : Grows s2r s2r := Grows.refl s2r
  refine SimE.bind ((sim_nextScalar π iv publicInput stream s2r).withChIds.withCursor) ?_
  intro s2 ood1 ood1E g2 gr2 hR
  obtain ⟨⟨hood1, l2, hl2, hl2n⟩, hcur2⟩ := hR
  regrow g2r gr2
  have hch2 : chIds s2 = [] := by rw [hl2, hch2r, List.eq_nil_of_length_eq_zero hl2n]; rfl
  have hG2 : Grows s2 s2 := Grows.refl s2
  refine SimE.bind ((sim_sampleWide s2 4 (by norm_num)).withCursor) ?_
  intro s3 bus busE g3 gr3 hR
  obtain ⟨⟨hbus, hbusl, hchb, -⟩, hcur3⟩ := hR
  regrow g2 gr3
  have hblen : bus.length = 4 := by rw [hbus.length_eq, hbusl]
  have hc0 := RpL.getDC π iv publicInput stream hbus (k := 0) (by omega)
  have hbeta := RpL.getDC π iv publicInput stream hbus (k := 1) (by omega)
  have hgamma := RpL.getDC π iv publicInput stream hbus (k := 2) (by omega)
  have hc3 := RpL.getDC π iv publicInput stream hbus (k := 3) (by omega)
  have hlen3 : (chIds s3).length = 4 := by rw [hchb, hch2, List.nil_append, hblen]
  refine SimE.pbind (squares_psim s3 g3 hc0 4) ?_
  intro s4 alphas ps4 halpha
  have gr4 := ps4.grows
  have g4 := ps4.good
  regrow g3 gr4
  have halphal : (UniStatement.squares (busE.getD 0 0) 4).length = 4 := squares_length _ _
  have hlen4 : (chIds s4).length = 4 := by rw [ps4.chal, hlen3]
  generalize UniStatement.squares (busE.getD 0 0) 4 = alphasE at halpha halphal ⊢
  generalize busE.getD 1 0 = betaE at hbeta ⊢
  generalize busE.getD 2 0 = gammaE at hgamma ⊢
  generalize bus.getD 1 0 = beta at hbeta ⊢
  generalize bus.getD 2 0 = gamma at hgamma ⊢
  refine SimE.pbind (eqKernel_psim s4 g4 halpha) ?_
  intro s6 weights ps6 hwts
  have gr6 := ps6.grows
  have g6 := ps6.good
  regrow g4 gr6
  have hlen6 : (chIds s6).length = 4 := by rw [ps6.chal, hlen4]
  -- 2. Flock, its zerocheck's first coordinate from the bus's draw.
  refine SimE.bind ((verifyWalkedK4_sim s6 hc3).withChIds.withCursor) ?_
  intro s7 fl flE g7 gr7 hR
  obtain ⟨⟨⟨hfp, hfpl, hsl, hsll, hp0⟩, l7, hl7, hl7n⟩, hcur7⟩ := hR
  regrow g6 gr7
  obtain ⟨fp, slices⟩ := fl
  obtain ⟨fpE, slicesE⟩ := flE
  simp only at hfp hfpl hsl hsll hp0
  rw [hlen6] at hp0
  have hlen7 : (chIds s7).length = 46 := by rw [hl7, List.length_append, hlen6, hl7n]
  have hG7 : Grows s7 s7 := Grows.refl s7
  have hcur7' : s7.cursor = 3776 := by
    rw [hcur7, ps6.cursor, ps4.cursor, hcur3, hcur2, hcur2r, hcur1']
  clear hcur7 hcur3 hcur2 hcur2r hcur1 hcur hl1 hl1n hl2 hl2n hl2r hl2rn hch1 hch2 hch2r hchb
    hlen3 hlen4 hlen6 hl7 hl7n
  dsimp only
  -- 3. C2's root and out-of-domain answer, then the wide draw of t and the map's f_0 … f_3; the digits, Z_act.
  refine SimE.bind ((sim_nextRoot π iv publicInput stream s7).withChIds) ?_
  intro s8r root2 root2E g8r gr8r hR
  obtain ⟨⟨hr2a, hr2b, hr2na, hr2nb⟩, l8r, hl8r, hl8rn⟩ := hR
  regrow g7 gr8r
  have hlen8r : (chIds s8r).length = 46 := by rw [hl8r, List.length_append, hlen7, hl8rn]
  have hG8r : Grows s8r s8r := Grows.refl s8r
  rw [hcur7'] at hr2na hr2nb
  refine SimE.bind ((sim_nextScalar π iv publicInput stream s8r).withChIds) ?_
  intro s8 ood2 ood2E g8 gr8 hR
  obtain ⟨hood2, l8, hl8, hl8n⟩ := hR
  regrow g8r gr8
  have hlen8 : (chIds s8).length = 46 := by rw [hl8, List.length_append, hlen8r, hl8n]
  have hG8 : Grows s8 s8 := Grows.refl s8
  refine SimE.bind (sim_sampleWide s8 5 (by norm_num)) ?_
  intro s9 pd pdE g9 gr9 hR
  obtain ⟨hpd, hpdl, hch9, -⟩ := hR
  regrow g8 gr9
  have hG9 : Grows s9 s9 := Grows.refl s9
  have hpdlen : pd.length = 5 := by rw [hpd.length_eq, hpdl]
  have ht := RpL.getDC π iv publicInput stream hpd (k := 0) (by omega)
  have hmap4 : RpL π iv publicInput stream s9 (pd.drop 1) (pdE.drop 1) := List.forall₂_drop 1 hpd
  have ht49 : (chIds s9).getD 46 0 = pd.getD 0 0 := by
    rw [hch9, List.getD_append_right _ _ _ _ (by omega), hlen8]
  have hlen9 : (chIds s9).length = 51 := by rw [hch9, List.length_append, hlen8, hpdlen]
  clear hch9 hl8 hl8n hlen8
  generalize pdE.getD 0 0 = tE at ht ⊢
  generalize pd.getD 0 0 = t at ht ht49 ⊢
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
  -- The hazard at the recorder's challenges 45 and 46.
  obtain ⟨l9, hl9⟩ := chIds_grows hG9
  have hlen43 : 47 ≤ (chIds s43).length := by rw [hl9, List.length_append, hlen9]; omega
  have h45 : (chIds s43).getD 45 0 = (chIds s7).getD 45 0 := chIds_getD_grow hG7 (by omega)
  have h46 : (chIds s43).getD 46 0 = t := by rw [chIds_getD_grow hG9 (by omega), ht49]
  have h45lt : (chIds s7).getD 45 0 < s7.nodes.size := by
    apply chIds_lt
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hp0' : val π iv publicInput stream s43 ((chIds s43).getD 45 0) = fpE.headD 0 := by
    rw [h45, val_sg g7.inv.kinv hG7 h45lt]
    exact hp0
  have ht43 : val π iv publicInput stream s43 ((chIds s43).getD 46 0) = tE := by rw [h46]; exact ht.2
  refine SimE.of_cond (¬ HazardK (val π iv publicInput stream s43 ((chIds s43).getD 45 0))
    (val π iv publicInput stream s43 ((chIds s43).getD 46 0))) ?_ ?_
  · intro hP
    rw [hp0', ht43] at hP
    -- 8 (π1-rec4). The wide draw of ρ, λ, f_4, f_5; the ring switch's target at the whole map.
    refine SimE.bind (sim_sampleWide s43 4 (by norm_num)) ?_
    intro s44 late lateE g44 gr44 hR
    obtain ⟨hlate, hlatel, -, -⟩ := hR
    regrow g43 gr44
    have hll : late.length = 4 := by rw [hlate.length_eq, hlatel]
    have hrho := RpL.getDC π iv publicInput stream hlate (k := 0) (by omega)
    have hlam := RpL.getDC π iv publicInput stream hlate (k := 1) (by omega)
    have hf4 := RpL.getDC π iv publicInput stream hlate (k := 2) (by omega)
    have hf5 := RpL.getDC π iv publicInput stream hlate (k := 3) (by omega)
    have hmapR : RpL π iv publicInput stream s44 (pd.drop 1 ++ [late.getD 2 0, late.getD 3 0])
        (pdE.drop 1 ++ [lateE.getD 2 0, lateE.getD 3 0]) :=
      List.rel_append hmap4 (List.Forall₂.cons hf4 (List.Forall₂.cons hf5 List.Forall₂.nil))
    have hmapl : (pdE.drop 1 ++ [lateE.getD 2 0, lateE.getD 3 0]).length = Flock.towerStages := by
      simp [hpdl]; rfl
    refine SimE.pbind (PH.psim (R := Rp π iv publicInput stream) (towerTarget_ph g44 hsl hmapR hsll hmapl)) ?_
    intro s45 tgt ps45 htgt
    have gr45 := ps45.grows
    have g45 := ps45.good
    regrow g44 gr45
    generalize Flock.towerTarget slicesE (pdE.drop 1 ++ [lateE.getD 2 0, lateE.getD 3 0]) = tgtE at htgt ⊢
    -- 7. Flock's claim on q_flock.
    refine SimE.pbind (oneP π iv publicInput stream g45) ?_
    intro s46 o4 ps46 ho4
    have gr46 := ps46.grows
    have g46 := ps46.good
    regrow g45 gr46
    have hok := hS tE alphasE betaE fpE tgtE outs mfcE addrE mplE bfcE bplE _ _ halphal hfpl htabs hCS hHS hP
    rw [hT1]
    have h0' : 0 < s46.nodes.size := by
      have := nodes_grow hG0 hseed
      rcases Nat.lt_or_ge 0 s46.nodes.size with h | h
      · exact h
      · simp [Array.getElem?_eq_none h] at this
    refine SimE.of_sim (tail_cpsK4 (m := 0) (ch := 0) hTail g46 h0' (RpRels.push (RpRels.append (RpRels.push
      (RpRels.push (RpRels.push (RpRels.push (RpRels.push (RpRels.push hrelsT hd1) hd2)
        (memRel_rp hw10 hwts hws hmp4 keccak128.logMemory)) hd3) hd4) hconsR) hheapR) (ringRel_rp hfp ho4 htgt))
      hrho hlam hmapR hok ?_)
    intro s47 openings b g47 gr47 hop
    have hk46 := g46.inv.kinv
    refine Sim.pure_of_pstep (PStep.refl s47 g47) ⟨⟨hr1a.sg hk46 gr47, hr1b.sg hk46 gr47, ?_, ?_⟩,
      ⟨hr2a.sg hk46 gr47, hr2b.sg hk46 gr47, nodes_grow (hG8r.trans gr47) hr2na,
        nodes_grow (hG8r.trans gr47) hr2nb⟩, hop, rfl, hood1.sg hk46 gr47, hood2.sg hk46 gr47⟩
    · rw [← hcur1']; exact nodes_grow (hG2r.trans gr47) hr1na
    · rw [← hcur1']; exact nodes_grow (hG2r.trans gr47) hr1nb
  · intro hnP c hc
    rw [not_not] at hnP
    have hsize : (chIds s43).length = c.challenges.size := by
      have e := congrArg List.length hc.chal
      simpa using e.symm
    refine not_noHazard_of_monoK4 (Mono.bind (Mono.sampleWide π 4) fun _ ↦
      Mono.bind (Mono.batchK4 π _ _ _ _) fun x ↦ Mono.ret _) (by omega) ?_
    rw [couple_getD hc (by omega), couple_getD hc (by omega)]
    exact hnP

end RecGraphKeccak.Sim
