-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `RecGraph.Sim`'s `Batch.lean` (`sim_batch`, `sim_tail`,
-- `tailSpec`), ported to the Keccak verifier's batch (`batchK`, `weightAtK`) and its stacks (`layoutsK`).
import RecGraph.Sim.Batch
import RecGraphKeccak.Sim.ClaimsK
import RecGraphKeccak.Sim.ComposeSpec
import UniSound.Ids.Deployed

/-!
# The Keccak verifier's tail: one claim per commitment, then the paired batch

* `sim_batchK`: `batchK` (π1-rec3's paired, narrow rounds; `weight_at` with `q_flock`'s slot bits) against
  `UniKeccak.batchK`'s `.rec3` branch, the claims entering through `CombRepK`;
* `sim_tailK`: `reduceK`'s tail after `ρ` (`combine_weightK` per commitment, then `sim_batchK`) against
  `UniKeccak`'s, for relations satisfying `TailOKK` (each commitment's layout `LayoutOK`, its terms of their kind
  `TermKindK`, no point extending a slot term's);
* **`tailSpecK : TailSpecK TailOKK tailBytesK tailChK`**.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph RecGraph.Pi1
  RecGraph.Sim RecGraphKeccak.Pi1

section Batch

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **The paired batch** (`batchK`) against `UniKeccak.batchK`'s `.rec3` branch (no pending matrices, no bit-slice
claim): the combined claims related commitment by commitment (`CombRep` at the commitment's layout), every block of
every layout within its stack, the ring map represented. It reads the paired sumcheck's bytes and the claims' values,
draws `λ` and the sumcheck's challenges, pushes the terminal zero; its openings are `UniStatement`'s point claims
(`RpOpening`), and no matrices' claim is left. -/
theorem sim_batchK (st : RecState) {combS : List (Commitment × CombinedS)} {comb : List (Commitment × Combined)}
    (layouts : List (Commitment × StackLayout))
    (hc : List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ CombRepK π iv publicInput stream st (layoutAt layouts a.1) a.2 b.2)
      combS comb)
    (hV : ∀ c col, ∀ b ∈ (layoutAt layouts c).limbs col, b.2.1 ≤ (layoutAt layouts c).vars)
    {mapS : List Nat} {map : List E} (hm : RpL π iv publicInput stream st mapS map) (h0 : 0 < st.nodes.size) :
    Sim π iv publicInput stream st (RecGraphKeccak.Pi1.batchK combS layouts (some mapS))
      (UniKeccak.batchK (Fp π) .rec3 comb layouts (some map))
      (pairsBytes 2 (bvars layouts) + 24 * comb.length) (1 + pairsCh (bvars layouts))
      (fun st' a b ↦ List.Forall₂ (RpOpening π iv publicInput stream st') a b) := by
  refine Sim.of_good fun hg ↦ ?_
  have hk := hg.inv.kinv
  have hlen := List.Forall₂.length_eq hc
  have hz0 : Rp π iv publicInput stream st 0 (val π iv publicInput stream st 0) := rp_val π iv publicInput stream h0
  unfold RecGraphKeccak.Pi1.batchK UniKeccak.batchK
  dsimp only
  refine Sim.cast (n := 0 + (pairsBytes 2 (bvars layouts) + (24 * comb.length + (0 + 0))))
    (ch := 1 + (pairsCh (bvars layouts) + (0 + (0 + 0)))) (by omega) (by omega) ?_
  refine Sim.bind (sim_sample π iv publicInput stream st) fun st1 lam lamE hg1 hgr1 ⟨hlam, _⟩ ↦ ?_
  refine Sim.pbind (phc_psim (b := (0 : E)) (R := fun st' a b ↦ Rp π iv publicInput stream st' a b)
    (phc_zero π iv publicInput stream hg1)) fun st2 t0 hg2 hgr2 ht0 ↦ ?_
  refine Sim.pbind (phc_psim (b := (1 : E)) (R := fun st' a b ↦ Rp π iv publicInput stream st' a b)
    (phc_one π iv publicInput stream hg2)) fun st3 s0 hg3 hgr3 hs0 ↦ ?_
  have hgr03 := hgr1.trans (hgr2.trans hgr3)
  have hlam3 := Rp.grow π iv publicInput stream hg1.inv.kinv (hgr2.trans hgr3) hlam
  have hc3 : List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ CombRepK π iv publicInput stream st3 (layoutAt layouts a.1) a.2 b.2)
      combS comb :=
    hc.imp fun _ _ h ↦ ⟨h.1, CombRepK.grow π iv publicInput stream hk hgr03 h.2⟩
  -- `λ`'s combination of the claims' values: the sumcheck's target.
  refine Sim.pbind (phc_psim (b := comb.foldl (fun acc x ↦ (acc.1 + acc.2 * x.2.value, acc.2 * lamE)) (0, 1))
    (R := fun st' (a : Nat × Nat) (b : E × E) ↦ Rp π iv publicInput stream st' a.1 b.1 ∧
      Rp π iv publicInput stream st' a.2 b.2)
    (phc_forIn (fun a a' s ↦ (a.1 = a'.1 ∧ CombRepK π iv publicInput stream s (layoutAt layouts a.1) a.2 a'.2) ∧
        Rp π iv publicInput stream s lam lamE)
      (fun _ _ _ _ hg hs h ↦ ⟨⟨h.1.1, CombRepK.grow π iv publicInput stream hg.inv.kinv hs.grows h.1.2⟩,
        Rp.pgrow hg hs h.2⟩) _
      (fun acc (x : Commitment × Combined) ↦ (acc.1 + acc.2 * x.2.value, acc.2 * lamE))
      (fun (b : Nat × Nat) (acc : E × E) s ↦ Rp π iv publicInput stream s b.1 acc.1 ∧
        Rp π iv publicInput stream s b.2 acc.2) ?_ combS comb st3 (t0, s0) (0, 1) hg3
      (hc3.imp fun _ _ h ↦ ⟨h, hlam3⟩) ⟨Rp.grow π iv publicInput stream hg2.inv.kinv hgr3 ht0, hs0⟩))
    fun st4 ts hg4 hgr4 hts ↦ ?_
  · rintro ⟨com, claim⟩ ⟨com', cb⟩ ⟨t, s⟩ ⟨tE, sE⟩ st' hg' ⟨⟨-, hcr⟩, hl⟩ ⟨ht, hs⟩
    dsimp only at ht hs ⊢
    exact phc_bind (phc_mul π iv publicInput stream hg' hs hcr.value) fun sv st1 hs1 hsv ↦
      phc_bind (phc_add π iv publicInput stream hs1.good (Rp.pgrow hg' hs1 ht) hsv) fun t' st2 hs2 ht' ↦
        phc_bind (phc_mul π iv publicInput stream hs2.good (Rp.pgrow hs1.good hs2 (Rp.pgrow hg' hs1 hs))
          (Rp.pgrow hs1.good hs2 (Rp.pgrow hg' hs1 hl))) fun s' st3 hs3 hs' ↦
          phc_pure _ hs3.good ⟨_, rfl, Rp.pgrow hs2.good hs3 ht', hs'⟩
  -- The paired sumcheck.
  have hgr04 := hgr03.trans hgr4
  refine Sim.bind (Sim.withRecord π iv publicInput stream (sim_sumcheckPairsDrawn st4 2 (bvars layouts) true hts.1))
    fun st5 sc scE hg5 hgr5 ⟨⟨hr, _, hlast⟩, hrec⟩ ↦ ?_
  have hrlen : sc.1.length = bvars layouts := by
    have := sumcheckPairsDrawn_out ts.1 2 (List.foldl max 0 (List.map (fun x ↦ x.2.vars) layouts)) true st4
    rw [← hrec] at this
    exact this
  obtain ⟨rS, chS, lastS⟩ := sc
  obtain ⟨rE, chE, lastE⟩ := scE
  dsimp only at hr hlast hrlen ⊢
  have hrElen : rE.length = bvars layouts := (RpL.lengthC π iv publicInput stream hr).symm.trans hrlen
  rw [pure_bind, show combS.length = comb.length from hlen]
  have hgr05 := hgr04.trans hgr5
  refine Sim.bind (sim_nextScalars π iv publicInput stream st5 comb.length) fun st6 vS vE hg6 hgr6 hv ↦ ?_
  have hgr56 := hgr6
  have hgr06 := hgr05.trans hgr6
  have hr6 := RpL.grow π iv publicInput stream hg5.inv.kinv hgr6 hr
  have hlast6 := Rp.grow π iv publicInput stream hg5.inv.kinv hgr6 hlast
  have hlam6 := Rp.grow π iv publicInput stream hg1.inv.kinv ((hgr2.trans hgr3).trans (hgr4.trans (hgr5.trans hgr6))) hlam
  have hm6 := RpL.grow π iv publicInput stream hk hgr06 hm
  have hz06 := Rp.grow π iv publicInput stream hk hgr06 hz0
  have hc6 : List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ CombRepK π iv publicInput stream st6 (layoutAt layouts a.1) a.2 b.2)
      combS comb :=
    hc.imp fun _ _ h ↦ ⟨h.1, CombRepK.grow π iv publicInput stream hk hgr06 h.2⟩
  have hzip := forall₂_zipC hc6 hv
  -- The weights, the extensions, the openings.
  refine Sim.pbind (phc_psim (b := (0 : E)) (R := fun st' a b ↦ Rp π iv publicInput stream st' a b)
    (phc_zero π iv publicInput stream hg6)) fun st7 m0 hg7 hgr7 hm0 ↦ ?_
  refine Sim.pbind (phc_psim (b := (1 : E)) (R := fun st' a b ↦ Rp π iv publicInput stream st' a b)
    (phc_one π iv publicInput stream hg7)) fun st8 n0 hg8 hgr8 hn0 ↦ ?_
  have hgr68 := hgr7.trans hgr8
  have hctx8 : RpL π iv publicInput stream st8 rS rE ∧ Rp π iv publicInput stream st8 lam lamE ∧
      RpL π iv publicInput stream st8 mapS map ∧
      Rp π iv publicInput stream st8 0 (val π iv publicInput stream st 0) :=
    ⟨RpL.grow π iv publicInput stream hg6.inv.kinv hgr68 hr6, Rp.grow π iv publicInput stream hg6.inv.kinv hgr68 hlam6,
      RpL.grow π iv publicInput stream hg6.inv.kinv hgr68 hm6, Rp.grow π iv publicInput stream hg6.inv.kinv hgr68 hz06⟩
  have hzip8 := hzip.imp fun _ _ h ↦ (show ((_ ∧ CombRepK π iv publicInput stream st8 _ _ _) ∧ _) ∧ _ from
    ⟨⟨⟨h.1.1, CombRepK.grow π iv publicInput stream hg6.inv.kinv hgr68 h.1.2⟩,
      Rp.grow π iv publicInput stream hg6.inv.kinv hgr68 h.2⟩, hctx8⟩)
  refine Sim.pbind (phc_psim
    (b := (comb.zip vE).foldl (fun (acc : E × E × Array (Commitment × Opening))
      (x : (Commitment × Combined) × E) ↦
      (acc.1 + acc.2.1 * UniKeccak.weightAtK x.1.2 (layoutAt layouts x.1.1) rE (some map) *
          List.foldl (fun e j ↦ e * (1 + rE.getD j 0)) 1
            (List.range' (layoutAt layouts x.1.1).vars (bvars layouts - (layoutAt layouts x.1.1).vars)) * x.2,
        acc.2.1 * lamE,
        acc.2.2.push (x.1.1, Opening.point (List.take (layoutAt layouts x.1.1).vars rE) x.2 none))) (0, 1, #[]))
    (R := fun st' (a : Nat × Nat × Array (Commitment × List Nat × Nat))
      (b : E × E × Array (Commitment × Opening)) ↦
      Rp π iv publicInput stream st' a.1 b.1 ∧ Rp π iv publicInput stream st' a.2.1 b.2.1 ∧
        List.Forall₂ (RpOpening π iv publicInput stream st') a.2.2.toList b.2.2.toList)
    (phc_forIn (fun a a' s ↦ ((a.1.1 = a'.1.1 ∧
          CombRepK π iv publicInput stream s (layoutAt layouts a.1.1) a.1.2 a'.1.2) ∧
        Rp π iv publicInput stream s a.2 a'.2) ∧
        (RpL π iv publicInput stream s rS rE ∧ Rp π iv publicInput stream s lam lamE ∧
          RpL π iv publicInput stream s mapS map ∧ Rp π iv publicInput stream s 0 (val π iv publicInput stream st 0)))
      (fun _ _ _ _ hg hs h ↦ ⟨⟨⟨h.1.1.1, CombRepK.grow π iv publicInput stream hg.inv.kinv hs.grows h.1.1.2⟩,
        Rp.pgrow hg hs h.1.2⟩, RpL.pgrow hg hs h.2.1, Rp.pgrow hg hs h.2.2.1, RpL.pgrow hg hs h.2.2.2.1,
          Rp.pgrow hg hs h.2.2.2.2⟩) _ _
      (fun (b : Nat × Nat × Array (Commitment × List Nat × Nat))
        (acc : E × E × Array (Commitment × Opening)) s ↦
        Rp π iv publicInput stream s b.1 acc.1 ∧ Rp π iv publicInput stream s b.2.1 acc.2.1 ∧
          List.Forall₂ (RpOpening π iv publicInput stream s) b.2.2.toList acc.2.2.toList)
      ?_ (combS.zip vS) (comb.zip vE) st8 (m0, n0, #[]) (0, 1, #[]) hg8 hzip8
      ⟨Rp.grow π iv publicInput stream hg7.inv.kinv hgr8 hm0, hn0, List.Forall₂.nil⟩))
    fun st9 res hg9 hgr9 hres ↦ ?_
  · rintro ⟨⟨com, claim⟩, value⟩ ⟨⟨com', cb⟩, x⟩ ⟨sm, sc2, ops⟩ ⟨smE, scE2, opsE⟩ s hg
      ⟨⟨⟨hcom, hcr⟩, hval⟩, hrS, hlamS, hmS, hz0S⟩ ⟨hsm, hsc, hops⟩
    dsimp only at hcom hcr hval hsm hsc hops ⊢
    rw [← hcom]
    have hLv := layoutAt_vars_le layouts com
    have hrl : ∀ col, ∀ b ∈ (layoutAt layouts com).limbs col, b.2.1 ≤ rE.length := fun col b hb ↦
      (hV com col b hb).trans (hLv.trans hrElen.symm.le)
    refine phc_bind (weightAtK_phc π iv publicInput stream hg hcr.held (layoutAt layouts com) hrS hmS hz0S)
      fun w s1 hs1 hw ↦ ?_
    rw [hcr.weight rE map _ hrl] at hw
    refine phc_bind (phc_one π iv publicInput stream hs1.good) fun e0 s2 hs2 he0 ↦ ?_
    rw [forIn_range]
    have hs12 := hs1.trans hs2
    refine phc_bind (phc_forIn_same (fun j ↦ j < bvars layouts)
      (fun s' ↦ RpL π iv publicInput stream s' rS rE) (fun _ _ hg hs h ↦ RpL.pgrow hg hs h) _
      (fun e j ↦ e * (1 + rE.getD j 0)) (fun (b : Nat) (c : E) s ↦ Rp π iv publicInput stream s b c) ?_ _ ?_ s2 e0 1
      hs2.good (RpL.pgrow hg hs12 hrS) he0) fun ext s3 hs3 hext ↦ ?_
    · intro j b c s' hg' hj hr' hbc
      have hrj := RpL.getDC π iv publicInput stream hr' (k := j) (by rw [RpL.lengthC π iv publicInput stream hr', hrElen]; exact hj)
      exact phc_bind (phc_one π iv publicInput stream hg') fun o s4 hs4 ho ↦
        phc_bind (phc_add π iv publicInput stream hs4.good ho (Rp.pgrow hg' hs4 hrj)) fun t s5 hs5 ht ↦
          phc_bind (phc_mul π iv publicInput stream hs5.good (Rp.pgrow hs4.good hs5 (Rp.pgrow hg' hs4 hbc)) ht)
            fun _ s6 hs6 h ↦ phc_pure _ hs6.good ⟨_, rfl, h⟩
    · intro j hj
      rw [List.mem_range'_1] at hj
      have hLv' := layoutAt_vars_le layouts com
      unfold layoutAt bvars at hLv'
      unfold bvars
      omega
    have hs13 := hs12.trans hs3
    refine phc_bind (phc_mul π iv publicInput stream hs3.good (Rp.pgrow hg hs13 hsc)
      (Rp.pgrow hs2.good hs3 (Rp.pgrow hs1.good hs2 hw))) fun sw s4 hs4 hsw ↦ ?_
    refine phc_bind (phc_mul π iv publicInput stream hs4.good hsw (Rp.pgrow hs3.good hs4 hext)) fun swe s5 hs5 hswe ↦ ?_
    have hs15 := hs13.trans (hs4.trans hs5)
    refine phc_bind (phc_mul π iv publicInput stream hs5.good hswe (Rp.pgrow hg hs15 hval)) fun swev s6 hs6 hswev ↦ ?_
    have hs16 := hs15.trans hs6
    refine phc_bind (phc_add π iv publicInput stream hs6.good (Rp.pgrow hg hs16 hsm) hswev) fun sm' s7 hs7 hsm' ↦ ?_
    have hs17 := hs16.trans hs7
    refine phc_bind (phc_mul π iv publicInput stream hs7.good (Rp.pgrow hg hs17 hsc) (Rp.pgrow hg hs17 hlamS))
      fun sc' s8 hs8 hsc' ↦ phc_pure _ hs8.good ⟨_, rfl, Rp.pgrow hs7.good hs8 hsm', hsc', ?_⟩
    have hs18 := hs17.trans hs8
    rw [Array.toList_push, Array.toList_push]
    exact List.rel_append ((hops.imp fun _ _ h ↦ RpOpening.pgrow π iv publicInput stream hg hs18 h))
      (List.Forall₂.cons ⟨rfl, _, _, rfl, RpL.takeC π iv publicInput stream (RpL.pgrow hg hs18 hrS) _,
        Rp.pgrow hg hs18 hval⟩ List.Forall₂.nil)
  · obtain ⟨hsum, -, hops⟩ := hres
    have hlast9 := Rp.grow π iv publicInput stream hg6.inv.kinv (hgr68.trans hgr9) hlast6
    refine Sim.pbind (phc_psim (R := fun st' a b ↦ Rp π iv publicInput stream st' a b)
      (phc_add π iv publicInput stream hg9 hsum hlast9)) fun st10 d hg10 hgr10 hd ↦ ?_
    refine Sim.bind (sim_requireZero π iv publicInput stream st10 d _ hd) fun st11 _ _ hg11 hgr11 _ ↦ ?_
    exact Sim.pure_of_pstep (PStep.refl st11 hg11) (hops.imp fun _ _ h ↦
      RpOpening.grow π iv publicInput stream hg9.inv.kinv (hgr10.trans hgr11) h)

end Batch

/-- The Keccak layouts' blocks lie inside their stacks, at every `C2` column list. -/
theorem layoutsK_vars_le (c2 : List (Column × ℕ × Bool)) (c : Commitment) (col : Column) :
    ∀ b ∈ (layoutAt (UniKeccak.layoutsK keccak128 c2) c).limbs col,
      b.2.1 ≤ (layoutAt (UniKeccak.layoutsK keccak128 c2) c).vars := by
  cases c
  · exact limbs_vars_le (UniSound.Ids.layoutAligned_new _) col
  · exact limbs_vars_le (UniSound.Ids.layoutAligned_new _) col
  · exact limbs_vars_le (UniSound.Ids.layoutAligned_new _) col

section Tail

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)


variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **The terms' kinds and the hazard's absence**, for every commitment, at the Keccak layouts (`layoutsK keccak128`) with `C2`'s
columns `c2`: what `combine_weight` asks of the relations. -/
def TailOKK (rels : List Relation) (c2 : List (Column × ℕ × Bool)) : Prop :=
  ∀ c ∈ commitments, LayoutOK (layoutAt (UniKeccak.layoutsK keccak128 c2) c) ∧
    (∀ r ∈ UniSound.Ids.mine rels c, ∀ tm ∈ r.terms,
      TermKindK (layoutAt (UniKeccak.layoutsK keccak128 c2) c) tm.column tm.point tm.twist) ∧
    (∀ r ∈ UniSound.Ids.mine rels c, ∀ tm ∈ r.terms, (∃ j, tm.column = .qflockSlot j) →
      ∀ r' ∈ UniSound.Ids.mine rels c, ∀ tm' ∈ r'.terms, tm.point.length < tm'.point.length →
        tm'.point.take tm.point.length ≠ tm.point)

theorem filterMap_length_congrK {α β γ : Type} (f : α → Option β) (g : α → Option γ)
    (h : ∀ x, (f x).isSome = (g x).isSome) : ∀ l : List α, (l.filterMap f).length = (l.filterMap g).length
  | [] => rfl
  | x :: l => by
    rw [List.filterMap_cons, List.filterMap_cons]
    have hx := h x
    cases hf : f x <;> cases hg : g x <;> rw [hf, hg] at hx <;> simp at hx <;>
      simp [filterMap_length_congrK f g h l]

/-- `combine` has a claim exactly when its commitment has relations, whatever `ρ`. -/
theorem combine_isSomeK (rels : List Relation) (c : Commitment) (ρ ρ' : E) :
    (combine rels c ρ).isSome = (combine rels c ρ').isSome := by
  rw [UniSound.Ids.Weights.combine_eq, UniSound.Ids.Weights.combine_eq]
  by_cases h : (UniSound.Ids.mine rels c).isEmpty = true
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, Option.isSome_some, Option.isSome_some]

/-- The tail's bytes: the paired sumcheck's and the claims' values. -/
def tailBytesK (rels : List Relation) (c2 : List (Column × ℕ × Bool)) : ℕ :=
  pairsBytes 2 (bvars (UniKeccak.layoutsK keccak128 c2)) +
    24 * (commitments.filterMap fun x ↦ (combine rels x 0).map ((x, ·))).length

/-- The tail's challenges: `λ` and the paired sumcheck's. -/
def tailChK (_rels : List Relation) (c2 : List (Column × ℕ × Bool)) : ℕ :=
  1 + pairsCh (bvars (UniKeccak.layoutsK keccak128 c2))

theorem openingsR_ofK {st : RecState} {a : List (Commitment × List Nat × Nat)} {b : List (Commitment × Opening)}
    (h : List.Forall₂ (RpOpening π iv publicInput stream st) a b) : OpeningsR π iv publicInput stream st a b := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h _ ih =>
    obtain ⟨h1, pt, v, h2, h3, h4⟩ := h
    exact List.Forall₂.cons ⟨pt, v, Prod.ext h1.symm h2, h3, h4⟩ ih

/-- **`reduce`'s tail, off the merge hazard**: one claim per commitment (`combine_weight`), then the batch
(`sim_batch`), against `UniStatement`'s `filterMap` of `combine` and `batchFs`'s `.rec3` branch (`tailP`, `tailU`). -/
theorem sim_tailK (st : RecState) {relsS : List RelationS} {rels : List Relation}
    (hr : RpRels π iv publicInput stream st relsS rels) {rhoS : Nat} {ρ : E}
    (hrho : Rp π iv publicInput stream st rhoS ρ) (c2 : List (Column × ℕ × Bool)) {mapS : List Nat} {map : List E}
    (hm : RpL π iv publicInput stream st mapS map) (h0 : 0 < st.nodes.size) (hok : TailOKK rels c2) :
    Sim π iv publicInput stream st (tailPK relsS rhoS c2 mapS) (tailUK π rels ρ c2 map) (tailBytesK rels c2)
      (tailChK rels c2) (fun st' a b ↦ OpeningsR π iv publicInput stream st' a b) := by
  refine Sim.of_good fun hg ↦ ?_
  unfold tailPK tailUK
  refine Sim.pbind (phc_psim (b := commitments.filterMap fun x ↦ (combine rels x ρ).map ((x, ·)))
    (R := fun st' (a : Array (Commitment × CombinedS)) (b : List (Commitment × Combined)) ↦
      List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ CombRepK π iv publicInput stream st'
        (layoutAt (UniKeccak.layoutsK keccak128 c2) a.1) a.2 b.2) a.toList b) ?_) fun st1 cS hg1 hgr1 hcS ↦ ?_
  · rw [← List.nil_append (commitments.filterMap _), ← foldl_filterMapC]
    refine phc_forIn_same (fun c ↦ c ∈ commitments)
      (fun s ↦ RpRels π iv publicInput stream s relsS rels ∧ Rp π iv publicInput stream s rhoS ρ)
      (fun _ _ hg hs h ↦ ⟨RpRels.pgrow π iv publicInput stream hg hs h.1, Rp.pgrow hg hs h.2⟩) _ _
      (fun (b : Array (Commitment × CombinedS)) (acc : List (Commitment × Combined)) s ↦
        List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ CombRepK π iv publicInput stream s
          (layoutAt (UniKeccak.layoutsK keccak128 c2) a.1) a.2 b.2) b.toList acc) ?_ commitments (fun _ h ↦ h) st #[] [] hg
      ⟨hr, hrho⟩ List.Forall₂.nil
    intro c b acc s hg' hc ⟨hr', hrho'⟩ hb
    obtain ⟨hL, hK, hself⟩ := hok c hc
    refine phc_bind (combine_weightK π iv publicInput stream hg' hr' c hrho' _ hL hK hself) fun out s' hs hout ↦ ?_
    have hb' : List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ CombRepK π iv publicInput stream s'
        (layoutAt (UniKeccak.layoutsK keccak128 c2) a.1) a.2 b.2) b.toList acc :=
      hb.imp fun _ _ h ↦ ⟨h.1, CombRepK.grow π iv publicInput stream hg'.inv.kinv hs.grows h.2⟩
    cases hcb : combine rels c ρ with
    | none =>
      rw [hcb] at hout
      cases out with
      | none => exact phc_pure _ hs.good ⟨_, rfl, by simpa using hb'⟩
      | some _ => exact hout.elim
    | some cb =>
      rw [hcb] at hout
      cases out with
      | none => exact hout.elim
      | some cS =>
        refine phc_pure _ hs.good ⟨_, rfl, ?_⟩
        rw [Array.toList_push]
        exact List.rel_append hb' (List.Forall₂.cons ⟨rfl, hout⟩ List.Forall₂.nil)
  · refine Sim.pbind (phc_psim (b := ()) (R := fun _ _ _ ↦ True) (phc_conseq (phc_one π iv publicInput stream hg1)
      fun _ _ _ _ ↦ trivial)) fun st2 _ hg2 hgr2 _ ↦ ?_
    have hgr02 := hgr1.trans hgr2
    have hc2 : List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ CombRepK π iv publicInput stream st2
        (layoutAt (UniKeccak.layoutsK keccak128 c2) a.1) a.2 b.2) cS.toList
        (commitments.filterMap fun x ↦ (combine rels x ρ).map ((x, ·))) :=
      hcS.imp fun _ _ h ↦ ⟨h.1, CombRepK.grow π iv publicInput stream hg1.inv.kinv hgr2 h.2⟩
    refine Sim.mono (Sim.cast ?_ rfl (sim_batchK π iv publicInput stream st2 (UniKeccak.layoutsK keccak128 c2) hc2
      (layoutsK_vars_le c2) (RpL.grow π iv publicInput stream hg.inv.kinv hgr02 hm)
      (lt_of_lt_of_le h0 (Grows.size_le hgr02)))) fun st' a b _ _ hops ↦ ?_
    · unfold tailBytesK
      rw [filterMap_length_congrC (fun x ↦ (combine rels x ρ).map ((x, ·))) (fun x ↦ (combine rels x 0).map ((x, ·)))
        (fun x ↦ by rw [Option.isSome_map, Option.isSome_map]; exact combine_isSomeK rels x ρ 0)]
    · exact openingsR_ofK π iv publicInput stream hops

/-- **`TailSpecK`**, the Keccak composition's interface for the tail. -/
theorem tailSpecK : TailSpecK TailOKK tailBytesK tailChK :=
  fun π iv publicInput stream st _ _ _ _ c2 _ _ _ h0 hr hrho hm hok ↦
    sim_tailK π iv publicInput stream st hr hrho c2 hm h0 hok

end Tail

end RecGraphKeccak.Sim
