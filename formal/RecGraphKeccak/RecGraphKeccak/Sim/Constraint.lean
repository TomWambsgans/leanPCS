-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The proof is `RecGraph.Sim.constraintRelation_phc`'s,
-- at any shape, with the Keccak tables and the `SHA3` lanes' copies (`END_BIT`'s known part).
import RecGraphKeccak.Sim.ConstraintFold

/-!
# `Q_W`'s identity on the Keccak VM, simulated

`constraintRelationK_phc`: the program's `constraintRelationK` (any shape) represents `UniKeccak.constraintRelationK`
(as folds, `constraintRelationK_eq`), step for step: `RecGraph.Sim.constraintRelation_phc`'s proof, with the six
Keccak tables and, in the `SHA3` table's copies, the constant `END_BIT` times the slot's weight added to the known part
(`copyStepK`). **`constraintSpecK : ConstraintSpecK partRK constraintShapeK`**.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph RecGraph.Pi1 RecGraph.Sim
  RecGraphKeccak.Pi1

section Rel

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **The constraint quotient's identity** (`constraintRelation` at π1-rec3's shape): the program's relation
represents `UniStatement`'s. -/
theorem constraintRelationK_phc (S : UniStatement.Shape) {st : RecState} (hg : Good st) (h0 : Rp π iv publicInput stream st 0 0)
    {parts : List TablePartS} {partsE : List TablePart} (hp : List.Forall₂ (RpPart π iv publicInput stream st) parts partsE)
    {pw : List Nat} {pwE : List E} (hpw : RpL π iv publicInput stream st pw pwE) {gamma t cv : Nat} {gammaE tE cvE : E}
    (hgam : Rp π iv publicInput stream st gamma gammaE) (ht : Rp π iv publicInput stream st t tE)
    (hcv : Rp π iv publicInput stream st cv cvE) {w : List Nat} {wE : List E} (hw : RpL π iv publicInput stream st w wE)
    (hwlen : S.constraintVars ≤ wE.length) :
    PHc st (Pi1.constraintRelationK S parts pw gamma t cv w) fun a st' ↦
      RpRel π iv publicInput stream st' a (UniKeccak.constraintRelationK S partsE pwE gammaE tE cvE wE).1 := by
  rw [constraintRelationK_eq]
  unfold Pi1.constraintRelationK crOfK
  dsimp only
  refine phc_bind (phc_zero π iv publicInput stream hg) fun k0 st1 hs1 hk0 ↦ ?_
  refine phc_bind (phc_one π iv publicInput stream hs1.good) fun p0 st2 hs2 hp0 ↦ ?_
  refine phc_bind (phc_one π iv publicInput stream hs2.good) fun o st3 hs3 ho ↦ ?_
  have hs03 := hs1.trans (hs2.trans hs3)
  have hc3 : CrCtx π iv publicInput stream st3 w wE gamma t o gammaE tE :=
    ⟨Rp.pgrow hg hs03 h0, RpL.pgrow hg hs03 hw, Rp.pgrow hg hs03 hgam, Rp.pgrow hg hs03 ht, ho⟩
  refine phc_bind (phc_forIn (fun a a' s ↦ (a.1 = a'.1 ∧ RpPart π iv publicInput stream s a.2 a'.2) ∧
      CrCtx π iv publicInput stream s w wE gamma t o gammaE tE)
    (fun _ _ _ _ hg hs h ↦ ⟨⟨h.1.1, RpPart.pgrow π iv publicInput stream hg hs h.1.2⟩,
      CrCtx.pgrow π iv publicInput stream hg hs h.2⟩) _
    (crStepK S gammaE tE wE)
    (fun (b : Nat × Array TermS × Nat) (c : E × Array Term × E × ℕ) s ↦ Rp π iv publicInput stream s b.1 c.1 ∧
      RpTermsC π iv publicInput stream s b.2.1.toList c.2.1.toList ∧ Rp π iv publicInput stream s b.2.2 c.2.2.1)
    ?_ (tablesKeccak.zip parts) (tablesKeccak.zip partsE) st3 (k0, #[], p0) (0, #[], 1, 0) hs3.good
    ((forall₂_zip_leftC tablesKeccak (hp.imp fun _ _ h ↦ RpPart.pgrow π iv publicInput stream hg hs03 h)).imp
      fun _ _ h ↦ ⟨h, hc3⟩)
    ⟨Rp.pgrow hs1.good (hs2.trans hs3) hk0, List.Forall₂.nil, Rp.pgrow hs2.good hs3 hp0⟩)
    fun res st4 hs4 hres ↦ ?_
  · rintro ⟨table, part⟩ ⟨tableE, partE⟩ ⟨kn, tm, pwr⟩ ⟨knE, tmE, pwrE, dg⟩ s hg' ⟨⟨htab, hpart⟩, hcs⟩
      ⟨hkn, htm, hpwr⟩
    dsimp only at htab hpart hkn htm hpwr ⊢
    rw [← htab]
    unfold crStepK
    dsimp only
    refine phc_bind (psim_phcC (vanishingRatio_psim s hg' hcs.hw _ _ hwlen)) fun lift s1 hs1 hlift ↦ ?_
    have hc1 := CrCtx.pgrow π iv publicInput stream hg' hs1 hcs
    have hp1 := RpPart.pgrow π iv publicInput stream hg' hs1 hpart
    have hsent := fun c ↦ RpO.getD0 π iv publicInput stream (RpSent.getD π iv publicInput stream hp1.2.2.2.2 c) hc1.h0
    by_cases hj : table.opcode = opJump
    · rw [ite_eq_left hj, ite_eq_left hj]
      refine phc_bind (phc_mul π iv publicInput stream hs1.good (Rp.pgrow hg' hs1 hpwr) hc1.hgam)
        fun pw1 s2 hs2 hpw1 ↦ ?_
      refine phc_bind (phc_mul π iv publicInput stream hs2.good (Rp.pgrow hg' (hs1.trans hs2) hpwr)
        (Rp.pgrow hs1.good hs2 hlift)) fun g1 s3 hs3 hg1 ↦ ?_
      have hs13 := hs2.trans hs3
      refine phc_bind (phc_mul π iv publicInput stream hs3.good hg1 (Rp.pgrow hs1.good hs13 (hsent _)))
        fun d1 s4 hs4 hd1 ↦ ?_
      refine phc_bind (phc_add π iv publicInput stream hs4.good (Rp.pgrow hg' (hs1.trans (hs13.trans hs4)) hkn) hd1)
        fun kn1 s5 hs5 hkn1 ↦ ?_
      have hs15 := hs13.trans (hs4.trans hs5)
      refine phc_bind (phc_mul π iv publicInput stream hs5.good (Rp.pgrow hs3.good (hs4.trans hs5) hg1)
        (Rp.pgrow hs1.good hs15 (hsent _))) fun d2 s6 hs6 hd2 ↦ ?_
      have hs16 := hs15.trans hs6
      refine phc_bind (phc_mul π iv publicInput stream hs6.good (Rp.pgrow hs2.good (hs3.trans (hs4.trans
        (hs5.trans hs6))) hpw1) (Rp.pgrow hs1.good hs16 hc1.hgam)) fun pw2 s7 hs7 hpw2 ↦ ?_
      have hs17 := hs16.trans hs7
      refine phc_bind (phc_mul π iv publicInput stream hs7.good (Rp.pgrow hs2.good (hs3.trans (hs4.trans
        (hs5.trans (hs6.trans hs7)))) hpw1) (Rp.pgrow hs1.good hs17 hlift)) fun g2 s8 hs8 hg2 ↦ ?_
      have hs18 := hs17.trans hs8
      refine phc_bind (phc_mul π iv publicInput stream hs8.good hg2 (Rp.pgrow hs1.good hs18 (hsent _)))
        fun g2c s9 hs9 hg2c ↦ ?_
      have hs19 := hs18.trans hs9
      refine phc_bind (phc_add π iv publicInput stream hs9.good (Rp.pgrow hs1.good hs19 (hsent _))
        (Rp.pgrow hs1.good hs19 hc1.ho)) fun f1 s10 hs10 hf1 ↦ ?_
      refine phc_bind (phc_mul π iv publicInput stream hs10.good (Rp.pgrow hs9.good hs10 hg2c) hf1)
        fun d3 s11 hs11 hd3 ↦ ?_
      have hs511 := hs6.trans (hs7.trans (hs8.trans (hs9.trans (hs10.trans hs11))))
      refine phc_bind (phc_add π iv publicInput stream hs11.good (Rp.pgrow hs5.good hs511 hkn1) hd3)
        fun kn2 s12 hs12 hkn2 ↦ ?_
      have hs112 := hs19.trans (hs10.trans (hs11.trans hs12))
      have hsX := hs1.trans hs112
      have hgX := hs12.good
      have hcX := CrCtx.pgrow π iv publicInput stream hs1.good hs112 hc1
      have hpX := RpPart.pgrow π iv publicInput stream hs1.good hs112 hp1
      have hliftX := Rp.pgrow hs1.good hs112 hlift
      have hk' := hkn2
      have hp' := Rp.pgrow hs7.good (hs8.trans (hs9.trans (hs10.trans (hs11.trans hs12)))) hpw2
      have ht' : RpTermsC π iv publicInput stream s12
          (tm.push (termS (Column.table table.opcode (colIdx table.columns "w"))
            (List.take (S.heights.getD table.opcode 0) w) d2)).toList
          (tmE.push (term (Column.table table.opcode (colIdx table.columns "w"))
            (List.take (S.heights.getD table.opcode 0) wE)
            (pwrE * vanishingRatio wE (S.heights.getD table.opcode 0) S.constraintVars *
              (partE.sent.getD (colIdx table.columns "v_cond") none).getD 0))).toList := by
        rw [Array.toList_push, Array.toList_push]
        exact List.rel_append (RpTermsC.pgrow π iv publicInput stream hg' (hs1.trans hs112) htm)
          (List.Forall₂.cons ⟨rfl, rfl, RpL.takeC π iv publicInput stream hcX.hw _,
            Rp.pgrow hs6.good (hs7.trans (hs8.trans (hs9.trans (hs10.trans (hs11.trans hs12))))) hd2⟩ List.Forall₂.nil)
      refine phc_bind (phc_forIn_same (fun _ ↦ True) (fun s' ↦ RpPart π iv publicInput stream s' part partE ∧
          Rp π iv publicInput stream s' 0 0)
        (fun _ _ hg hs h ↦ ⟨RpPart.pgrow π iv publicInput stream hg hs h.1, Rp.pgrow hg hs h.2⟩) _
        (fun acc c ↦ acc * (partE.sent.getD c none).getD 0) (fun (b : Nat) (e : E) s' ↦ Rp π iv publicInput stream s' b e)
        ?_ table.countColumns (fun _ _ ↦ trivial) s12 o 1 hgX ⟨hpX, hcX.h0⟩ hcX.ho) fun ctr sA hsA hctr ↦ ?_
      · intro c b e s' hg'' _ ⟨hps, h0s⟩ hbe
        exact phc_bind (phc_mul π iv publicInput stream hg'' hbe (RpO.getD0 π iv publicInput stream
          (RpSent.getD π iv publicInput stream hps.2.2.2.2 c) h0s)) fun _ s'' hs'' h ↦ phc_pure _ hs''.good ⟨_, rfl, h⟩
      refine phc_bind (phc_mul π iv publicInput stream hsA.good (Rp.pgrow hgX hsA hp') (Rp.pgrow hgX hsA hcX.hgam))
        fun pw3 sB hsB hpw3 ↦ ?_
      refine phc_bind (phc_mul π iv publicInput stream hsB.good (Rp.pgrow hgX (hsA.trans hsB) hp')
        (Rp.pgrow hgX (hsA.trans hsB) hliftX)) fun g sC hsC hgg ↦ ?_
      refine phc_bind (phc_mul π iv publicInput stream hsC.good hgg (Rp.pgrow hsA.good (hsB.trans hsC) hctr))
        fun d sD hsD hd ↦ ?_
      have hsAD := hsA.trans (hsB.trans (hsC.trans hsD))
      refine phc_bind (phc_add π iv publicInput stream hsD.good (Rp.pgrow hgX hsAD hk') (Rp.pgrow hsC.good hsD hgg))
        fun kn3 sF hsF hkn3 ↦ ?_
      have hsXF := hsAD.trans hsF
      have hpw3F := Rp.pgrow hsB.good (hsC.trans (hsD.trans hsF)) hpw3
      have hcF := CrCtx.pgrow π iv publicInput stream hgX hsXF hcX
      have hliftF := Rp.pgrow hgX hsXF hliftX
      by_cases hb : table.opcode = opBlake2s
      · rw [ite_eq_left hb, ite_eq_left hb]
        refine phc_bind (psim_phcC (coordinatesAt_psim sF hsF.good hcF.ht _)) fun y sG hsG hy ↦ ?_
        refine phc_bind (phc_forIn (fun a c s' ↦ a = (table.columns.getD c "", c) ∧
            (RpL π iv publicInput stream s' w wE ∧ Rp π iv publicInput stream s' gamma gammaE ∧
              Rp π iv publicInput stream s' lift
                (vanishingRatio wE (S.heights.getD table.opcode 0) S.constraintVars) ∧
              RpL π iv publicInput stream s' y
                (coordinatesAt tE (coordinateFunctionals (S.heights.getD table.opcode 0)))))
          (fun _ _ _ _ hg hs h ↦ ⟨h.1, RpL.pgrow hg hs h.2.1, Rp.pgrow hg hs h.2.2.1, Rp.pgrow hg hs h.2.2.2.1,
            RpL.pgrow hg hs h.2.2.2.2⟩) _
          (copyStepK table.opcode (S.heights.getD table.opcode 0) table.columns wE
            (coordinatesAt tE (coordinateFunctionals (S.heights.getD table.opcode 0)))
            (vanishingRatio wE (S.heights.getD table.opcode 0) S.constraintVars) gammaE)
          (fun (b : Nat × Array TermS × Nat) (c : E × Array Term × E) s' ↦ Rp π iv publicInput stream s' b.1 c.1 ∧
            RpTermsC π iv publicInput stream s' b.2.1.toList c.2.1.toList ∧
            Rp π iv publicInput stream s' b.2.2 c.2.2) ?_ (table.columns.zip (List.range table.width))
          (List.range table.width) sG _ _ hsG.good ((forall₂_zip_rangeC table.columns).imp fun _ _ h ↦
            ⟨h, RpL.pgrow hsF.good hsG hcF.hw, Rp.pgrow hsF.good hsG hcF.hgam, Rp.pgrow hsF.good hsG hliftF, hy⟩)
          ⟨Rp.pgrow hsF.good hsG hkn3,
            RpTermsC.pushC π iv publicInput stream (RpTermsC.pgrow π iv publicInput stream hgX (hsXF.trans hsG) ht')
            ⟨rfl, rfl, RpL.takeC π iv publicInput stream (RpL.pgrow hgX (hsXF.trans hsG) hcX.hw) _,
              Rp.pgrow hsD.good (hsF.trans hsG) hd⟩, Rp.pgrow hsF.good hsG hpw3F⟩)
          fun inner sH hsH ⟨hin1, hin2, hin3⟩ ↦ phc_pure _ hsH.good ⟨_, rfl, hin1, hin2, hin3⟩
        rintro ⟨name, col⟩ c ⟨knI, tmI, pwI⟩ ⟨knIE, tmIE, pwIE⟩ s' hg'' ⟨heq, hwI, hgI, hlI, hyI⟩ ⟨hkI, htI, hpwI⟩
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hn, hc⟩ := heq
        subst hn
        subst hc
        dsimp only at hkI htI hpwI ⊢
        unfold copyStepK
        cases hq : keccakSlot (table.columns.getD col "") with
        | none => exact phc_pure _ hg'' ⟨_, rfl, hkI, htI, hpwI⟩
        | some slot =>
          dsimp only
          refine phc_bind (phc_mul π iv publicInput stream hg'' hpwI hgI) fun pw4 s5 hs5 hpw4 ↦ ?_
          refine phc_bind (phc_mul π iv publicInput stream hs5.good (Rp.pgrow hg'' hs5 hpwI) (Rp.pgrow hg'' hs5 hlI))
            fun g4 s6 hs6 hg4 ↦ ?_
          have hs56 := hs5.trans hs6
          have hterms : RpTermsC π iv publicInput stream s6
              (((tmI.push (termS (Column.table table.opcode col) (List.take (S.heights.getD table.opcode 0) w) g4)).push
                (termS (Column.qflockSlot slot) y g4)).toList)
              (((tmIE.push (term (Column.table table.opcode col) (List.take (S.heights.getD table.opcode 0) wE)
                (pwIE * vanishingRatio wE (S.heights.getD table.opcode 0) S.constraintVars))).push
                (term (Column.qflockSlot slot) (coordinatesAt tE (coordinateFunctionals (S.heights.getD table.opcode 0)))
                  (pwIE * vanishingRatio wE (S.heights.getD table.opcode 0) S.constraintVars))).toList) := by
            rw [Array.toList_push, Array.toList_push, Array.toList_push, Array.toList_push, List.append_assoc,
              List.append_assoc]
            exact List.rel_append (RpTermsC.pgrow π iv publicInput stream hg'' hs56 htI)
              (List.Forall₂.cons ⟨rfl, rfl, RpL.takeC π iv publicInput stream (RpL.pgrow hg'' hs56 hwI) _, hg4⟩
                (List.Forall₂.cons ⟨rfl, rfl, RpL.pgrow hg'' hs56 hyI, hg4⟩ List.Forall₂.nil))
          by_cases ho : (keccakSlotOffset (table.columns.getD col "") != 0) = true
          · simp only [ho, ↓reduceIte]
            refine phc_bind (phc_const π iv publicInput stream hs6.good (eK (keccakSlotOffset (table.columns.getD col ""))))
              fun c7 s7 hs7 hc7 ↦ ?_
            refine phc_bind (phc_mul π iv publicInput stream hs7.good (Rp.pgrow hs6.good hs7 hg4) hc7)
              fun m8 s8 hs8 hm8 ↦ ?_
            refine phc_bind (phc_add π iv publicInput stream hs8.good (Rp.pgrow hg'' (hs56.trans (hs7.trans hs8)) hkI) hm8)
              fun k9 s9 hs9 hk9 ↦ ?_
            exact phc_pure _ hs9.good ⟨_, rfl, hk9,
              RpTermsC.pgrow π iv publicInput stream hs6.good (hs7.trans (hs8.trans hs9)) hterms,
              Rp.pgrow hs5.good (hs6.trans (hs7.trans (hs8.trans hs9))) hpw4⟩
          · simp only [ho, Bool.false_eq_true, ↓reduceIte]
            exact phc_pure _ hs6.good ⟨_, rfl, Rp.pgrow hg'' hs56 hkI, hterms, Rp.pgrow hs5.good hs6 hpw4⟩
      · rw [ite_eq_right hb, ite_eq_right hb]
        exact phc_pure _ hsF.good ⟨_, rfl, hkn3, RpTermsC.pushC π iv publicInput stream
          (RpTermsC.pgrow π iv publicInput stream hgX hsXF ht')
          ⟨rfl, rfl, RpL.takeC π iv publicInput stream (RpL.pgrow hgX hsXF hcX.hw) _, Rp.pgrow hsD.good hsF hd⟩, hpw3F⟩
    · rw [ite_eq_right hj, ite_eq_right hj]
      have hgX := hs1.good
      have hcX := hc1
      have hpX := hp1
      have hliftX := hlift
      have hk' := Rp.pgrow hg' hs1 hkn
      have hp' := Rp.pgrow hg' hs1 hpwr
      have ht' := RpTermsC.pgrow π iv publicInput stream hg' hs1 htm
      refine phc_bind (phc_forIn_same (fun _ ↦ True) (fun s' ↦ RpPart π iv publicInput stream s' part partE ∧
          Rp π iv publicInput stream s' 0 0)
        (fun _ _ hg hs h ↦ ⟨RpPart.pgrow π iv publicInput stream hg hs h.1, Rp.pgrow hg hs h.2⟩) _
        (fun acc c ↦ acc * (partE.sent.getD c none).getD 0) (fun (b : Nat) (e : E) s' ↦ Rp π iv publicInput stream s' b e)
        ?_ table.countColumns (fun _ _ ↦ trivial) s1 o 1 hgX ⟨hpX, hcX.h0⟩ hcX.ho) fun ctr sA hsA hctr ↦ ?_
      · intro c b e s' hg'' _ ⟨hps, h0s⟩ hbe
        exact phc_bind (phc_mul π iv publicInput stream hg'' hbe (RpO.getD0 π iv publicInput stream
          (RpSent.getD π iv publicInput stream hps.2.2.2.2 c) h0s)) fun _ s'' hs'' h ↦ phc_pure _ hs''.good ⟨_, rfl, h⟩
      refine phc_bind (phc_mul π iv publicInput stream hsA.good (Rp.pgrow hgX hsA hp') (Rp.pgrow hgX hsA hcX.hgam))
        fun pw3 sB hsB hpw3 ↦ ?_
      refine phc_bind (phc_mul π iv publicInput stream hsB.good (Rp.pgrow hgX (hsA.trans hsB) hp')
        (Rp.pgrow hgX (hsA.trans hsB) hliftX)) fun g sC hsC hgg ↦ ?_
      refine phc_bind (phc_mul π iv publicInput stream hsC.good hgg (Rp.pgrow hsA.good (hsB.trans hsC) hctr))
        fun d sD hsD hd ↦ ?_
      have hsAD := hsA.trans (hsB.trans (hsC.trans hsD))
      refine phc_bind (phc_add π iv publicInput stream hsD.good (Rp.pgrow hgX hsAD hk') (Rp.pgrow hsC.good hsD hgg))
        fun kn3 sF hsF hkn3 ↦ ?_
      have hsXF := hsAD.trans hsF
      have hpw3F := Rp.pgrow hsB.good (hsC.trans (hsD.trans hsF)) hpw3
      have hcF := CrCtx.pgrow π iv publicInput stream hgX hsXF hcX
      have hliftF := Rp.pgrow hgX hsXF hliftX
      by_cases hb : table.opcode = opBlake2s
      · rw [ite_eq_left hb, ite_eq_left hb]
        refine phc_bind (psim_phcC (coordinatesAt_psim sF hsF.good hcF.ht _)) fun y sG hsG hy ↦ ?_
        refine phc_bind (phc_forIn (fun a c s' ↦ a = (table.columns.getD c "", c) ∧
            (RpL π iv publicInput stream s' w wE ∧ Rp π iv publicInput stream s' gamma gammaE ∧
              Rp π iv publicInput stream s' lift
                (vanishingRatio wE (S.heights.getD table.opcode 0) S.constraintVars) ∧
              RpL π iv publicInput stream s' y
                (coordinatesAt tE (coordinateFunctionals (S.heights.getD table.opcode 0)))))
          (fun _ _ _ _ hg hs h ↦ ⟨h.1, RpL.pgrow hg hs h.2.1, Rp.pgrow hg hs h.2.2.1, Rp.pgrow hg hs h.2.2.2.1,
            RpL.pgrow hg hs h.2.2.2.2⟩) _
          (copyStepK table.opcode (S.heights.getD table.opcode 0) table.columns wE
            (coordinatesAt tE (coordinateFunctionals (S.heights.getD table.opcode 0)))
            (vanishingRatio wE (S.heights.getD table.opcode 0) S.constraintVars) gammaE)
          (fun (b : Nat × Array TermS × Nat) (c : E × Array Term × E) s' ↦ Rp π iv publicInput stream s' b.1 c.1 ∧
            RpTermsC π iv publicInput stream s' b.2.1.toList c.2.1.toList ∧
            Rp π iv publicInput stream s' b.2.2 c.2.2) ?_ (table.columns.zip (List.range table.width))
          (List.range table.width) sG _ _ hsG.good ((forall₂_zip_rangeC table.columns).imp fun _ _ h ↦
            ⟨h, RpL.pgrow hsF.good hsG hcF.hw, Rp.pgrow hsF.good hsG hcF.hgam, Rp.pgrow hsF.good hsG hliftF, hy⟩)
          ⟨Rp.pgrow hsF.good hsG hkn3,
            RpTermsC.pushC π iv publicInput stream (RpTermsC.pgrow π iv publicInput stream hgX (hsXF.trans hsG) ht')
            ⟨rfl, rfl, RpL.takeC π iv publicInput stream (RpL.pgrow hgX (hsXF.trans hsG) hcX.hw) _,
              Rp.pgrow hsD.good (hsF.trans hsG) hd⟩, Rp.pgrow hsF.good hsG hpw3F⟩)
          fun inner sH hsH ⟨hin1, hin2, hin3⟩ ↦ phc_pure _ hsH.good ⟨_, rfl, hin1, hin2, hin3⟩
        rintro ⟨name, col⟩ c ⟨knI, tmI, pwI⟩ ⟨knIE, tmIE, pwIE⟩ s' hg'' ⟨heq, hwI, hgI, hlI, hyI⟩ ⟨hkI, htI, hpwI⟩
        simp only [Prod.mk.injEq] at heq
        obtain ⟨hn, hc⟩ := heq
        subst hn
        subst hc
        dsimp only at hkI htI hpwI ⊢
        unfold copyStepK
        cases hq : keccakSlot (table.columns.getD col "") with
        | none => exact phc_pure _ hg'' ⟨_, rfl, hkI, htI, hpwI⟩
        | some slot =>
          dsimp only
          refine phc_bind (phc_mul π iv publicInput stream hg'' hpwI hgI) fun pw4 s5 hs5 hpw4 ↦ ?_
          refine phc_bind (phc_mul π iv publicInput stream hs5.good (Rp.pgrow hg'' hs5 hpwI) (Rp.pgrow hg'' hs5 hlI))
            fun g4 s6 hs6 hg4 ↦ ?_
          have hs56 := hs5.trans hs6
          have hterms : RpTermsC π iv publicInput stream s6
              (((tmI.push (termS (Column.table table.opcode col) (List.take (S.heights.getD table.opcode 0) w) g4)).push
                (termS (Column.qflockSlot slot) y g4)).toList)
              (((tmIE.push (term (Column.table table.opcode col) (List.take (S.heights.getD table.opcode 0) wE)
                (pwIE * vanishingRatio wE (S.heights.getD table.opcode 0) S.constraintVars))).push
                (term (Column.qflockSlot slot) (coordinatesAt tE (coordinateFunctionals (S.heights.getD table.opcode 0)))
                  (pwIE * vanishingRatio wE (S.heights.getD table.opcode 0) S.constraintVars))).toList) := by
            rw [Array.toList_push, Array.toList_push, Array.toList_push, Array.toList_push, List.append_assoc,
              List.append_assoc]
            exact List.rel_append (RpTermsC.pgrow π iv publicInput stream hg'' hs56 htI)
              (List.Forall₂.cons ⟨rfl, rfl, RpL.takeC π iv publicInput stream (RpL.pgrow hg'' hs56 hwI) _, hg4⟩
                (List.Forall₂.cons ⟨rfl, rfl, RpL.pgrow hg'' hs56 hyI, hg4⟩ List.Forall₂.nil))
          by_cases ho : (keccakSlotOffset (table.columns.getD col "") != 0) = true
          · simp only [ho, ↓reduceIte]
            refine phc_bind (phc_const π iv publicInput stream hs6.good (eK (keccakSlotOffset (table.columns.getD col ""))))
              fun c7 s7 hs7 hc7 ↦ ?_
            refine phc_bind (phc_mul π iv publicInput stream hs7.good (Rp.pgrow hs6.good hs7 hg4) hc7)
              fun m8 s8 hs8 hm8 ↦ ?_
            refine phc_bind (phc_add π iv publicInput stream hs8.good (Rp.pgrow hg'' (hs56.trans (hs7.trans hs8)) hkI) hm8)
              fun k9 s9 hs9 hk9 ↦ ?_
            exact phc_pure _ hs9.good ⟨_, rfl, hk9,
              RpTermsC.pgrow π iv publicInput stream hs6.good (hs7.trans (hs8.trans hs9)) hterms,
              Rp.pgrow hs5.good (hs6.trans (hs7.trans (hs8.trans hs9))) hpw4⟩
          · simp only [ho, Bool.false_eq_true, ↓reduceIte]
            exact phc_pure _ hs6.good ⟨_, rfl, Rp.pgrow hg'' hs56 hkI, hterms, Rp.pgrow hs5.good hs6 hpw4⟩
      · rw [ite_eq_right hb, ite_eq_right hb]
        exact phc_pure _ hsF.good ⟨_, rfl, hkn3, RpTermsC.pushC π iv publicInput stream
          (RpTermsC.pgrow π iv publicInput stream hgX hsXF ht')
          ⟨rfl, rfl, RpL.takeC π iv publicInput stream (RpL.pgrow hgX hsXF hcX.hw) _, Rp.pgrow hsD.good hsF hd⟩, hpw3F⟩
  · obtain ⟨hk4, ht4, hp4⟩ := hres
    have hc4 := CrCtx.pgrow π iv publicInput stream hs3.good hs4 hc3
    have hs04 := hs03.trans hs4
    refine phc_bind (phc_zero π iv publicInput stream hs4.good) fun z1 st5 hs5 hz1 ↦ ?_
    refine phc_bind (phc_zero π iv publicInput stream hs5.good) fun z2 st6 hs6 hz2 ↦ ?_
    have hs46 := hs5.trans hs6
    refine phc_bind (psim_phcC (vanishingRatio_psim st6 hs6.good (RpL.pgrow hs3.good (hs4.trans hs46) hc3.hw) 1
      S.constraintVars hwlen)) fun lift st7 hs7 hlift ↦ ?_
    have hs47 := hs46.trans hs7
    have hpw7 := RpL.pgrow hg (hs04.trans hs47) hpw
    have hpwd := fun k ↦ RpL.getDz π iv publicInput stream hpw7 (Rp.pgrow hg (hs04.trans hs47) h0) k
    have hlines : List.Forall₂ (fun a a' ↦ Rp π iv publicInput stream st7 a.1.1 a'.1.1 ∧
        Rp π iv publicInput stream st7 a.1.2 a'.1.2 ∧ a.2 = a'.2)
        ([(pw.getD 0 0, pw.getD 2 0), (pw.getD 1 0, pw.getD 3 0), (z1, z2)].zip (List.range 3))
        ((UniSound.Ids.linesOf pwE).zip (List.range 3)) :=
      List.Forall₂.cons ⟨hpwd 0, hpwd 2, rfl⟩ (List.Forall₂.cons ⟨hpwd 1, hpwd 3, rfl⟩
        (List.Forall₂.cons ⟨Rp.pgrow hs5.good (hs6.trans hs7) hz1, Rp.pgrow hs6.good hs7 hz2, rfl⟩ List.Forall₂.nil))
    refine phc_bind (phc_forIn (fun a a' s ↦ (Rp π iv publicInput stream s a.1.1 a'.1.1 ∧
        Rp π iv publicInput stream s a.1.2 a'.1.2 ∧ a.2 = a'.2) ∧
        (CrCtx π iv publicInput stream s w wE gamma t o gammaE tE ∧
          Rp π iv publicInput stream s lift (vanishingRatio wE 1 S.constraintVars)))
      (fun _ _ _ _ hg hs h ↦ ⟨⟨Rp.pgrow hg hs h.1.1, Rp.pgrow hg hs h.1.2.1, h.1.2.2⟩,
        CrCtx.pgrow π iv publicInput stream hg hs h.2.1, Rp.pgrow hg hs h.2.2⟩) _
      (UniSound.Ids.Eval.lineStep S gammaE tE wE)
      (fun (b : Nat × Array TermS × Nat) (c : E × Array Term × E) s ↦ Rp π iv publicInput stream s b.1 c.1 ∧
        RpTermsC π iv publicInput stream s b.2.1.toList c.2.1.toList ∧ Rp π iv publicInput stream s b.2.2 c.2.2)
      ?_ _ _ st7 (res.1, res.2.1, res.2.2)
      ((List.foldl (crStepK S gammaE tE wE) (0, #[], 1, 0) (tablesKeccak.zip partsE)).1,
        (List.foldl (crStepK S gammaE tE wE) (0, #[], 1, 0) (tablesKeccak.zip partsE)).2.1,
        (List.foldl (crStepK S gammaE tE wE) (0, #[], 1, 0) (tablesKeccak.zip partsE)).2.2.1)
      hs7.good (hlines.imp fun _ _ h ↦ ⟨h, CrCtx.pgrow π iv publicInput stream hs4.good hs47 hc4, hlift⟩)
      ⟨Rp.pgrow hs4.good hs47 hk4, RpTermsC.pgrow π iv publicInput stream hs4.good hs47 ht4,
        Rp.pgrow hs4.good hs47 hp4⟩) fun res2 st8 hs8 ⟨hk8, ht8, _⟩ ↦ ?_
    · rintro ⟨⟨low, high⟩, k⟩ ⟨⟨lowE, highE⟩, kE⟩ ⟨kn, tm, pwr⟩ ⟨knE, tmE, pwrE⟩ s hg' ⟨⟨hlo, hhi, hk⟩, hcs, hl⟩
        ⟨hkn, htm, hpwr⟩
      dsimp only at hlo hhi hk hkn htm hpwr ⊢
      subst hk
      unfold UniSound.Ids.Eval.lineStep
      dsimp only
      refine phc_bind (phc_mul π iv publicInput stream hg' hpwr hcs.hgam) fun pw1 s1 hs1 hpw1 ↦ ?_
      refine phc_bind (phc_mul π iv publicInput stream hs1.good (Rp.pgrow hg' hs1 hpwr) (Rp.pgrow hg' hs1 hl))
        fun g s2 hs2 hgg ↦ ?_
      have hs12 := hs1.trans hs2
      refine phc_bind (phc_add π iv publicInput stream hs2.good (Rp.pgrow hg' hs12 hlo) (Rp.pgrow hg' hs12 hhi))
        fun lh s3 hs3 hlh ↦ ?_
      refine phc_bind (phc_mul π iv publicInput stream hs3.good (Rp.pgrow hg' (hs12.trans hs3) hcs.ht) hlh)
        fun tlh s4 hs4 htlh ↦ ?_
      have hs14 := hs12.trans (hs3.trans hs4)
      refine phc_bind (phc_add π iv publicInput stream hs4.good (Rp.pgrow hg' hs14 hlo) htlh) fun l2 s5 hs5 hl2 ↦ ?_
      refine phc_bind (phc_mul π iv publicInput stream hs5.good (Rp.pgrow hs2.good (hs3.trans (hs4.trans hs5)) hgg) hl2)
        fun d s6 hs6 hd ↦ ?_
      have hs16 := hs14.trans (hs5.trans hs6)
      refine phc_bind (phc_add π iv publicInput stream hs6.good (Rp.pgrow hg' hs16 hkn) hd) fun kn' s7 hs7 hkn' ↦ ?_
      have hs17 := hs16.trans hs7
      refine phc_pure _ hs7.good ⟨_, rfl, hkn', ?_, Rp.pgrow hs1.good (hs2.trans (hs3.trans (hs4.trans
        (hs5.trans (hs6.trans hs7))))) hpw1⟩
      rw [Array.toList_push, Array.toList_push]
      exact List.rel_append (RpTermsC.pgrow π iv publicInput stream hg' hs17 htm)
        (List.Forall₂.cons ⟨rfl, rfl, RpL.takeC π iv publicInput stream (RpL.pgrow hg' hs17 hcs.hw) _,
          Rp.pgrow hs2.good (hs3.trans (hs4.trans (hs5.trans (hs6.trans hs7)))) hgg⟩ List.Forall₂.nil)
    · have hs08 := (hs04.trans hs47).trans hs8
      refine phc_bind (phc_mul π iv publicInput stream hs8.good (Rp.pgrow hg hs08 hcv)
        (RpL.getDz π iv publicInput stream (RpL.pgrow hg hs08 hw) (Rp.pgrow hg hs08 h0) S.constraintVars))
        fun cw st9 hs9 hcw ↦ ?_
      exact phc_bind (phc_add π iv publicInput stream hs9.good hcw (Rp.pgrow hs8.good hs9 hk8)) fun v st10 hs10 hv ↦
        phc_pure _ hs10.good ⟨RpTermsC.pgrow π iv publicInput stream hs8.good (hs9.trans hs10) ht8, hv⟩

end Rel

/-- **The constraint relation at the Keccak shape, its shape**: `UniKeccak.constraintRelationK` at `keccak128`, at some
inputs, the point `tE` and the digits `wE`. -/
def constraintShapeK (wE : List E) (tE : E) (b : Relation) : Prop :=
  ∃ (partsE : List TablePart) (pwE : List E) (gammaE cvE : E),
    b = (UniKeccak.constraintRelationK keccak128 partsE pwE gammaE tE cvE wE).1

/-- **`ConstraintSpecK`**, the Keccak composition's interface for `Q_W`'s identity. -/
theorem constraintSpecK : ConstraintSpecK partRK constraintShapeK := by
  intro π iv publicInput stream st parts partsE pw pwE gamma t cv gammaE tE cvE w wE hg hseed hp hpw _ hgam ht hcv hw hwE
  have h0 := rp_zero_of_seed π iv publicInput stream hg hseed
  have hwlen : keccak128.constraintVars ≤ wE.length := by
    rw [hwE, digits_lengthC]
    unfold wLenK
    omega
  have h := constraintRelationK_phc π iv publicInput stream keccak128 hg h0 (hp.imp fun _ _ h ↦ h.1) hpw hgam ht hcv
    hw hwlen
  exact ⟨h.1, h.2, partsE, pwE, gammaE, cvE, rfl⟩

end RecGraphKeccak.Sim
