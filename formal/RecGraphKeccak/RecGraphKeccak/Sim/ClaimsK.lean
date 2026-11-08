-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `RecGraph.Sim`'s `Claims.lean` weight part (`weightAt_phc`,
-- `termP_eq`, `CombRep`, `combine_weight`), ported to the Keccak verifier's `weight_at` (its slot terms' slot bits
-- `q_flock`'s variables minus their point's) and to `UniKeccak.weightAtK`.
import RecGraph.Sim.Claims
import RecGraphKeccak.Sim.WeightsK
import RecGraphKeccak.Pi1.Verifier

/-!
# The Keccak verifier's combined claims and their weights

The program's `combine` is `RecGraph.Pi1.combine` (`RecGraph.Sim.combine_phc`, generic); its `weight_at` is
`RecGraphKeccak.Pi1.weightAtK`, `RecGraph.Pi1.weightAt` with a slot term's `8` slot bits replaced by `q_flock`'s
variables minus the term's point's (`qvOf L − |pt|`, 11 at the Keccak shape's `y(t)`):

* `weightAtK_phc`: on a held claim, the program's weight is `progWK` of the claim's values (`accWK`, `instWK`: the slot
  bits' and the instance's eq at `qvOf L − |pt|`);
* `termPK_eq`: a term's weight as the program reads it is `UniKeccak.weightAtK`'s (`TermKindK`: a slot term's point
  shorter than `q_flock`'s variables);
* `combine_weightK`: off the merge hazard, the program's combined claim (points by node) and `UniStatement.combine`'s
  (by value) have the same value, count and `weightAtK` (`CombRepK`).
-/

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement RecGraph RecGraph.Pi1
  RecGraph.Sim

/-- `q_flock`'s slot `j`'s `sb` low coordinates' `eq`, as the program computes it. -/
def accWK (r : List E) (z0 : E) (j sb : ℕ) : E :=
  (List.range' 0 sb).foldl (fun a b ↦ a * (if j.testBit b = true then r.getD b z0 else (r.map (1 + ·)).getD b z0)) 1

/-- A slot point's instance coordinates' `eq` past `sb` slot bits, as the program computes it. -/
def instWK (r point : List E) (sb : ℕ) : E :=
  (point.zip ((r.map (1 + ·)).drop sb)).foldl (fun a xa ↦ a * (xa.2 + xa.1)) 1

/-- **One term's weight as the Keccak program reads it** (coefficient `1`). -/
def termPK (L : StackLayout) (r map : List E) (z0 : E) (column : Column) (point : List E) (twist : ℕ) : E :=
  match column with
  | .qflockSlot j => accWK r z0 j (qvOf L - point.length) *
      (instWK r point (qvOf L - point.length) * partV r z0 L .qflock)
  | _ => rowW r map z0 point (headVars L column) twist * partV r z0 L column

/-- **The Keccak program's weight, on values.** -/
def progWK (C : Combined) (L : StackLayout) (r map : List E) (z0 : E) : E :=
  (C.terms.map fun x ↦ x.2.2.2 * termPK L r map z0 x.1 (C.points.getD x.2.1 []) x.2.2.1).sum

/-- The slots' part of a prefix of the terms. -/
def slotTK (L : StackLayout) (C : Combined) (r : List E) (z0 : E) (g : ℕ → E) (x : Column × ℕ × ℕ × E) : E :=
  match x.1 with
  | .qflockSlot j => g x.2.1 * (x.2.2.2 * accWK r z0 j (qvOf L - (C.points.getD x.2.1 []).length))
  | _ => 0

theorem qvOf_eq (L : StackLayout) : headVars L .qflock = qvOf L := by
  unfold headVars qvOf
  cases L.limbs .qflock <;> rfl

theorem slotTK_of_ne {L : StackLayout} {C : Combined} {r : List E} {z0 : E} {g : ℕ → E} {x : Column × ℕ × ℕ × E}
    (hx : ∀ j, x.1 ≠ .qflockSlot j) : slotTK L C r z0 g x = 0 := by
  unfold slotTK
  split
  · rename_i j h
    exact absurd h (hx j)
  · rfl

theorem termPK_of_ne {L : StackLayout} {r map : List E} {z0 : E} {column : Column} (hx : ∀ j, column ≠ .qflockSlot j)
    (point : List E) (twist : ℕ) :
    termPK L r map z0 column point twist = rowW r map z0 point (headVars L column) twist * partV r z0 L column := by
  unfold termPK
  split
  · exact absurd rfl (hx _)
  · rfl

/-- **The program's weight, split**: its rows' part and its slots' part. -/
theorem progWK_split (C : Combined) (L : StackLayout) (r map : List E) (z0 : E) :
    progWK C L r map z0 =
      (C.terms.map (rowT L r z0 fun key ↦ rowW r map z0 (C.points.getD key.1 []) key.2.1 key.2.2)).sum +
        (C.terms.map (slotTK L C r z0 fun p ↦ instWK r (C.points.getD p []) (qvOf L - (C.points.getD p []).length) *
          partV r z0 L .qflock)).sum := by
  unfold progWK
  rw [← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun x _ ↦ ?_)
  obtain ⟨col, p, tw, k⟩ := x
  cases col <;> simp only [rowT, slotTK, termPK] <;> ring

section Lengths

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

theorem valC_points_getD_length {st : RecState} {cS : CombinedS} {p : ℕ} :
    ((valC π iv publicInput stream st cS).points.getD p []).length = (cS.points.getD p []).length := by
  show ((cS.points.map (·.map (val π iv publicInput stream st))).getD p ([].map (val π iv publicInput stream st))).length = _
  rw [List.getD_map, List.length_map]

end Lengths

section WeightSim2

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

theorem keyed_get {K : Type} [BEq K] [LawfulBEq K] {st : RecState} {A : Array (K × Nat)} {V : List (K × E)}
    (h : RpKeyed π iv publicInput stream st A.toList V) {k : K} {i : ℕ}
    (hi : A.findIdx? (fun x ↦ x.1 == k) = some i) (d : K × Nat) :
    ∃ hiV : i < V.length, V[i].1 = k ∧ Rp π iv publicInput stream st (A.getD i d).2 V[i].2 := by
  obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hi
  have hlen : A.toList.length = V.length := List.Forall₂.length_eq h
  have hltA : i < A.toList.length := by simpa using hlt
  have hiV : i < V.length := by omega
  have he := forall₂_getElemC h i hltA hiV
  refine ⟨hiV, ?_, ?_⟩
  · simp only [beq_iff_eq] at hp
    rw [← he.1]
    simpa using hp
  · have hget : A.getD i d = A.toList[i]'hltA := by
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, List.getElem?_eq_getElem hltA, Option.getD_some]
    rw [hget]
    exact he.2

theorem keyed_set {K : Type} {st : RecState} {A : Array (K × Nat)} {V : List (K × E)}
    (h : RpKeyed π iv publicInput stream st A.toList V) {k : K} {i : ℕ} (hiV : i < V.length) (hk : V[i].1 = k)
    {v : Nat} {c : E} (hv : Rp π iv publicInput stream st v (V[i].2 + c)) :
    RpKeyed π iv publicInput stream st (A.set! i (k, v)).toList (V.modify i fun e ↦ (e.1, e.2 + c)) := by
  rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  exact forall₂_set_modifyC h i _ _ fun _ ↦ ⟨hk.symm, hv⟩

theorem keyed_push {K : Type} {st : RecState} {A : Array (K × Nat)} {V : List (K × E)}
    (h : RpKeyed π iv publicInput stream st A.toList V) (k : K) {v : Nat} {c : E}
    (hv : Rp π iv publicInput stream st v c) :
    RpKeyed π iv publicInput stream st (A.push (k, v)).toList (V ++ [(k, c)]) := by
  rw [Array.toList_push]
  exact List.rel_append h (List.Forall₂.cons ⟨rfl, hv⟩ List.Forall₂.nil)

/-- The claim's points at the start, represented. -/
theorem pts_val {st : RecState} {cS : CombinedS} (hh : HeldC st cS) (p : ℕ) :
    RpL π iv publicInput stream st (cS.points.getD p []) ((valC π iv publicInput stream st cS).points.getD p []) := by
  show RpL π iv publicInput stream st (cS.points.getD p [])
    ((cS.points.map (·.map (val π iv publicInput stream st))).getD p ([].map (val π iv publicInput stream st)))
  rw [List.getD_map]
  apply rpL_val
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi
  cases hq : cS.points[p]? with
  | none => rw [hq] at hi; simp at hi
  | some q =>
    rw [hq, Option.getD_some] at hi
    exact hh.points q (List.mem_of_getElem? hq) i hi

/-- **`weight_at`**: on a held claim, the program's weight is `progW` of the claim's values (node `0` worth `z0`). -/
theorem weightAtK_phc {st : RecState} (hg : Good st) {cS : CombinedS} (hh : HeldC st cS) (L : StackLayout)
    {rS : List Nat} {r : List E} (hr : RpL π iv publicInput stream st rS r) {mapS : List Nat} {map : List E}
    (hm : RpL π iv publicInput stream st mapS map) {z0 : E} (h0 : Rp π iv publicInput stream st 0 z0) :
    PHc st (RecGraphKeccak.Pi1.weightAtK cS L rS (some mapS)) fun w st' ↦
      Rp π iv publicInput stream st' w (progWK (valC π iv publicInput stream st cS) L r map z0) := by
  unfold RecGraphKeccak.Pi1.weightAtK
  -- `1 + r`.
  refine phc_bind (phc_forIn (fun a a' st ↦ Rp π iv publicInput stream st a a')
    (fun _ _ _ _ hg hs h ↦ Rp.pgrow hg hs h) _ (fun (l : List E) x ↦ l ++ [1 + x])
    (fun (b : Array Nat) (l : List E) st ↦ RpL π iv publicInput stream st b.toList l) ?_ rS r st #[] [] hg hr
    List.Forall₂.nil) fun opS st1 hs1 hop ↦ ?_
  · intro a a' b l st hg ha hb
    exact phc_bind (phc_one π iv publicInput stream hg) fun o st1 hs1 ho ↦
      phc_bind (phc_add π iv publicInput stream hs1.good ho (Rp.pgrow hg hs1 ha)) fun s st2 hs2 hs ↦
        phc_pure _ hs2.good ⟨_, rfl, by
          rw [Array.toList_push]
          exact List.rel_append (RpL.pgrow hs1.good hs2 (RpL.pgrow hg hs1 hb)) (List.Forall₂.cons hs List.Forall₂.nil)⟩
  rw [foldl_snoc_oneC, List.nil_append] at hop
  -- The basis.
  refine phc_bind (phc_const π iv publicInput stream hs1.good _) fun b0 st2 hs2 hb0 ↦ ?_
  refine phc_bind (phc_const π iv publicInput stream hs2.good _) fun b1 st3 hs3 hb1 ↦ ?_
  refine phc_bind (phc_const π iv publicInput stream hs3.good _) fun b2 st4 hs4 hb2 ↦ ?_
  have hs04 : PStep st st4 := hs1.trans (hs2.trans (hs3.trans hs4))
  have hg4 := hs4.good
  have ctx : WCtx π iv publicInput stream st st4 cS rS opS.toList [b0, b1, b2] mapS r map z0 :=
    ⟨RpL.pgrow hg hs04 hr,
      RpL.pgrow hs3.good hs4 (RpL.pgrow hs2.good hs3 (RpL.pgrow hs1.good hs2 hop)),
      List.Forall₂.cons (Rp.pgrow hs3.good hs4 (Rp.pgrow hs2.good hs3 hb0))
        (List.Forall₂.cons (Rp.pgrow hs3.good hs4 hb1) (List.Forall₂.cons hb2 List.Forall₂.nil)),
      Rp.pgrow hg hs04 h0, fun p ↦ RpL.pgrow hg hs04 (pts_val π iv publicInput stream hh p), RpL.pgrow hg hs04 hm⟩
  have hsbAll : ∀ p, headVars L .qflock - (cS.points.getD p []).length =
      qvOf L - ((valC π iv publicInput stream st cS).points.getD p []).length := fun p ↦ by
    rw [qvOf_eq, valC_points_getD_length π iv publicInput stream]
  -- The terms, grouped by row and by slot.
  have hterms : List.Forall₂ (fun a a' ↦ (a' = valTm π iv publicInput stream st a ∧
      Rp π iv publicInput stream st4 a.2.2.2 a'.2.2.2) ∧
      WCtx π iv publicInput stream st st4 cS rS opS.toList [b0, b1, b2] mapS r map z0) cS.terms
      (valC π iv publicInput stream st cS).terms := by
    show List.Forall₂ _ cS.terms (cS.terms.map (valTm π iv publicInput stream st))
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro x hx
    exact ⟨⟨rfl, Rp.pgrow hg hs04 (rp_val π iv publicInput stream (hh.terms x hx))⟩, ctx⟩
  refine phc_bind (phc_forIn (fun a a' st' ↦ (a' = valTm π iv publicInput stream st a ∧
      Rp π iv publicInput stream st' a.2.2.2 a'.2.2.2) ∧
      WCtx π iv publicInput stream st st' cS rS opS.toList [b0, b1, b2] mapS r map z0)
    (fun _ _ _ _ hg hs h ↦ ⟨⟨h.1.1, Rp.pgrow hg hs h.1.2⟩, WCtx.pgrow π iv publicInput stream hg hs h.2⟩) _
    (fun (acc : List (Column × ℕ × ℕ × E)) x ↦ acc ++ [x])
    (fun (b : Array ((ℕ × ℕ × ℕ) × Nat) × Array (ℕ × Nat)) (acc : List (Column × ℕ × ℕ × E)) st' ↦
      ∃ V W, RpKeyed π iv publicInput stream st' b.1.toList V ∧ RpKeyed π iv publicInput stream st' b.2.toList W ∧
        (∀ f, rdK f V = (acc.map (rowT L r z0 f)).sum) ∧ (∀ g, rdK g W = (acc.map (slotTK L (valC π iv publicInput stream st cS) r z0 g)).sum))
    ?_ _ _ st4 (#[], #[]) [] hg4 hterms ⟨[], [], List.Forall₂.nil, List.Forall₂.nil, fun _ ↦ rfl, fun _ ↦ rfl⟩)
    fun res st5 hs5 hres ↦ ?_
  · rintro ⟨column, p, twist, coeff⟩ x' ⟨rowsS, slotsS⟩ acc st' hg' ⟨⟨rfl, hco⟩, ctx'⟩ ⟨V, W, hV, hW, hrow, hslot⟩
    dsimp only [valTm] at hco hV hW ⊢
    split
    · rename_i j
      refine phc_bind (phc_one π iv publicInput stream hg') fun a0 st1 hs1 ha0 ↦ ?_
      rw [forIn_range]
      refine phc_bind (phc_forIn_same (fun _ ↦ True)
        (fun s' ↦ WCtx π iv publicInput stream st s' cS rS opS.toList [b0, b1, b2] mapS r map z0) (fun _ _ hg hs h ↦
          WCtx.pgrow π iv publicInput stream hg hs h) _
        (fun a b ↦ a * (if j.testBit b = true then r.getD b z0 else (r.map (1 + ·)).getD b z0))
        (fun (s : Nat) (e : E) st ↦ Rp π iv publicInput stream st s e) ?_ _ (fun _ _ ↦ trivial) st1 a0 1 hs1.good
        (WCtx.pgrow π iv publicInput stream hg' hs1 ctx') ha0) fun accS st2 hs2 hacc ↦ ?_
      · intro b s e st hg _ ctx hse
        by_cases hb : j.testBit b = true
        · simp only [hb, ↓reduceIte]
          exact phc_bind (phc_mul π iv publicInput stream hg hse (RpL.getDz π iv publicInput stream ctx.hr ctx.hz0 b))
            fun _ st' hs' h ↦ phc_pure _ hs'.good ⟨_, rfl, h⟩
        · simp only [hb, Bool.false_eq_true, ↓reduceIte]
          exact phc_bind (phc_mul π iv publicInput stream hg hse
            (RpL.arrGetDz π iv publicInput stream ctx.hop ctx.hz0 b)) fun _ st' hs' h ↦ phc_pure _ hs'.good ⟨_, rfl, h⟩
      have hacc' : Rp π iv publicInput stream st2 accS
          (accWK r z0 j (qvOf L - ((valC π iv publicInput stream st cS).points.getD p []).length)) := by
        rw [← hsbAll p]; exact hacc
      have hs12 : PStep st' st2 := hs1.trans hs2
      refine phc_bind (phc_mul π iv publicInput stream hs2.good (Rp.pgrow hg' hs12 hco) hacc') fun cv st3 hs3 hcv ↦ ?_
      have hV3 := RpKeyed.pgrow π iv publicInput stream hs2.good hs3 (RpKeyed.pgrow π iv publicInput stream hg' hs12 hV)
      have hW3 := RpKeyed.pgrow π iv publicInput stream hs2.good hs3 (RpKeyed.pgrow π iv publicInput stream hg' hs12 hW)
      have hx1 : ∀ f, rowT L r z0 f (Column.qflockSlot j, p, twist, val π iv publicInput stream st coeff) = 0 :=
        fun _ ↦ rfl
      have hx2 : ∀ g, slotTK L (valC π iv publicInput stream st cS) r z0 g (Column.qflockSlot j, p, twist, val π iv publicInput stream st coeff) =
          g p * (val π iv publicInput stream st coeff *
            accWK r z0 j (qvOf L - ((valC π iv publicInput stream st cS).points.getD p []).length)) := fun _ ↦ rfl
      have hrow' : ∀ f, rdK f V =
          ((acc ++ [(Column.qflockSlot j, p, twist, val π iv publicInput stream st coeff)]).map (rowT L r z0 f)).sum := by
        intro f
        rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hx1, add_zero, hrow f]
      cases hf : slotsS.findIdx? (fun x ↦ x.1 == p) with
      | none =>
        refine phc_pure _ hs3.good ⟨_, rfl, V, _, hV3, keyed_push π iv publicInput stream hW3 p hcv, hrow', fun g ↦ ?_⟩
        rw [rdK_snoc, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hx2, hslot g]
      | some i =>
        obtain ⟨hiW, hk, hget⟩ := keyed_get π iv publicInput stream hW3 hf (0, 0)
        refine phc_bind (phc_add π iv publicInput stream hs3.good hget hcv) fun v st4 hs4 hv ↦
          phc_pure _ hs4.good ⟨_, rfl, V, _, RpKeyed.pgrow π iv publicInput stream hs3.good hs4 hV3,
            keyed_set π iv publicInput stream (RpKeyed.pgrow π iv publicInput stream hs3.good hs4 hW3) hiW hk hv,
            hrow', fun g ↦ ?_⟩
        rw [rdK_modify _ _ _ hiW, hk, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hx2,
          hslot g]
    · rename_i hns
      refine phc_bind (partS_phc π iv publicInput stream hg' ctx'.hr ctx'.hbasis ctx'.hz0 L _) fun vs st1 hs1 hvs ↦ ?_
      obtain ⟨vars, sm⟩ := vs
      obtain ⟨hvars, hsm⟩ := hvs
      dsimp only at hvars hsm ⊢
      subst hvars
      refine phc_bind (phc_mul π iv publicInput stream hs1.good (Rp.pgrow hg' hs1 hco) hsm) fun cv st2 hs2 hcv ↦ ?_
      have hV2 := RpKeyed.pgrow π iv publicInput stream hs1.good hs2 (RpKeyed.pgrow π iv publicInput stream hg' hs1 hV)
      have hW2 := RpKeyed.pgrow π iv publicInput stream hs1.good hs2 (RpKeyed.pgrow π iv publicInput stream hg' hs1 hW)
      have hne : ∀ j, (column, p, twist, val π iv publicInput stream st coeff).1 ≠ .qflockSlot j := fun j h ↦ hns j h
      have hx1 : ∀ f, rowT L r z0 f (column, p, twist, val π iv publicInput stream st coeff) =
          f (p, headVars L column, twist) * (val π iv publicInput stream st coeff * partV r z0 L column) :=
        fun _ ↦ rowT_of_ne hne
      have hx2 : ∀ g, slotTK L (valC π iv publicInput stream st cS) r z0 g (column, p, twist, val π iv publicInput stream st coeff) = 0 :=
        fun _ ↦ slotTK_of_ne hne
      have hslot' : ∀ g, rdK g W =
          ((acc ++ [(column, p, twist, val π iv publicInput stream st coeff)]).map (slotTK L (valC π iv publicInput stream st cS) r z0 g)).sum := by
        intro g
        rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hx2, add_zero, hslot g]
      cases hf : rowsS.findIdx? (fun x ↦ x.1 == (p, headVars L column, twist)) with
      | none =>
        refine phc_pure _ hs2.good ⟨_, rfl, _, W, keyed_push π iv publicInput stream hV2 _ hcv, hW2, fun f ↦ ?_, hslot'⟩
        rw [rdK_snoc, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hx1, hrow f]
      | some i =>
        obtain ⟨hiV, hk, hget⟩ := keyed_get π iv publicInput stream hV2 hf ((0, 0, 0), 0)
        refine phc_bind (phc_add π iv publicInput stream hs2.good hget hcv) fun v st3 hs3 hv ↦
          phc_pure _ hs3.good ⟨_, rfl, _, W,
            keyed_set π iv publicInput stream (RpKeyed.pgrow π iv publicInput stream hs2.good hs3 hV2) hiV hk hv,
            RpKeyed.pgrow π iv publicInput stream hs2.good hs3 hW2, fun f ↦ ?_, hslot'⟩
        rw [rdK_modify _ _ _ hiV, hk, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hx1,
          hrow f]
  · obtain ⟨V, W, hV, hW, hrow, hslot⟩ := hres
    rw [foldl_snocC, List.nil_append] at hrow hslot
    have ctx5 := WCtx.pgrow π iv publicInput stream hg4 hs5 ctx
    refine phc_bind (phc_zero π iv publicInput stream hs5.good) fun t0 st6 hs6 ht0 ↦ ?_
    have ctx6 := WCtx.pgrow π iv publicInput stream hs5.good hs6 ctx5
    rw [← Array.forIn_toList]
    refine phc_bind (phc_forIn (fun a a' s ↦ (a.1 = a'.1 ∧ Rp π iv publicInput stream s a.2 a'.2) ∧
        WCtx π iv publicInput stream st s cS rS opS.toList [b0, b1, b2] mapS r map z0)
      (fun _ _ _ _ hg hs h ↦ ⟨⟨h.1.1, Rp.pgrow hg hs h.1.2⟩, WCtx.pgrow π iv publicInput stream hg hs h.2⟩) _
      (fun t (e : (ℕ × ℕ × ℕ) × E) ↦
        t + (fun key : ℕ × ℕ × ℕ ↦ rowW r map z0 ((valC π iv publicInput stream st cS).points.getD key.1 [])
          key.2.1 key.2.2) e.1 * e.2)
      (fun (b : Nat) (a : E) s ↦ Rp π iv publicInput stream s b a) ?_ res.1.toList V st6 t0 0 hs6.good
      ((RpKeyed.pgrow π iv publicInput stream hs5.good hs6 hV).imp fun _ _ h ↦ ⟨h, ctx6⟩) ht0)
      fun t1 st7 hs7 ht1 ↦ ?_
    · rintro ⟨⟨p, len, twist⟩, sm⟩ e' t a s hg ⟨⟨h1, h2⟩, ctx⟩ hta
      dsimp only at h1 h2 ⊢
      rw [← h1]
      by_cases htw : twist = ringTwist
      · rw [ite_eq_left htw]
        have hp := ctx.hpts p
        refine phc_bind (phc_ringWeight π iv publicInput stream hg (RpL.takeC π iv publicInput stream hp len)
          (RpL.takeC π iv publicInput stream ctx.hop len) ctx.hmap) fun row s1 hs1 hrw ↦ ?_
        rw [RpL.lengthC π iv publicInput stream (RpL.takeC π iv publicInput stream hp len)] at hrw
        have hrw' : Rp π iv publicInput stream s1 row
            (rowW r map z0 ((valC π iv publicInput stream st cS).points.getD p []) len twist) := by
          unfold rowW
          rw [ite_eq_left htw]
          exact hrw
        exact phc_bind (phc_mul π iv publicInput stream hs1.good hrw' (Rp.pgrow hg hs1 h2)) fun rs s2 hs2 hrs ↦
          phc_bind (phc_add π iv publicInput stream hs2.good (Rp.pgrow hs1.good hs2 (Rp.pgrow hg hs1 hta)) hrs)
            fun _ s3 hs3 h ↦ phc_pure _ hs3.good ⟨_, rfl, h⟩
      · rw [ite_eq_right htw]
        refine phc_bind (phc_one π iv publicInput stream hg) fun o s1 hs1 ho ↦ ?_
        rw [forIn_range]
        refine phc_bind (phc_forIn_same (fun _ ↦ True)
          (fun s' ↦ WCtx π iv publicInput stream st s' cS rS opS.toList [b0, b1, b2] mapS r map z0)
          (fun _ _ hg hs h ↦ WCtx.pgrow π iv publicInput stream hg hs h) _
          (fun a k ↦ a * ((r.map (1 + ·)).getD k z0 + ((valC π iv publicInput stream st cS).points.getD p []).getD k z0))
          (fun (b : Nat) (c : E) s ↦ Rp π iv publicInput stream s b c) ?_ _ (fun _ _ ↦ trivial) s1 o 1 hs1.good
          (WCtx.pgrow π iv publicInput stream hg hs1 ctx) ho) fun prod s2 hs2 hprod ↦ ?_
        · intro k b c s hg _ ctx hbc
          exact phc_bind (phc_add π iv publicInput stream hg (RpL.arrGetDz π iv publicInput stream ctx.hop ctx.hz0 k)
            (RpL.getDz π iv publicInput stream (ctx.hpts p) ctx.hz0 k)) fun sS s1 hs1 hsS ↦
            phc_bind (phc_mul π iv publicInput stream hs1.good (Rp.pgrow hg hs1 hbc) hsS) fun _ s2 hs2 h ↦
              phc_pure _ hs2.good ⟨_, rfl, h⟩
        · have hrw' : Rp π iv publicInput stream s2 prod
              (rowW r map z0 ((valC π iv publicInput stream st cS).points.getD p []) len twist) := by
            unfold rowW
            rw [ite_eq_right htw]
            exact hprod
          have hs12 : PStep s s2 := hs1.trans hs2
          refine phc_bind (phc_pure (Q := fun i st' ↦ Rp π iv publicInput stream st' i
            (rowW r map z0 ((valC π iv publicInput stream st cS).points.getD p []) len twist)) _ hs2.good hrw')
            fun row s3 hs3 hrow ↦ ?_
          have hs13 : PStep s s3 := hs12.trans hs3
          exact phc_bind (phc_mul π iv publicInput stream hs3.good hrow (Rp.pgrow hg hs13 h2)) fun rs s4 hs4 hrs ↦
            phc_bind (phc_add π iv publicInput stream hs4.good (Rp.pgrow hs3.good hs4 (Rp.pgrow hg hs13 hta)) hrs)
              fun _ s5 hs5 h ↦ phc_pure _ hs5.good ⟨_, rfl, h⟩
    · have ctx7 := WCtx.pgrow π iv publicInput stream hs6.good hs7 ctx6
      dsimp only
      rw [← Array.forIn_toList]
      refine phc_bind (phc_forIn (fun a a' s ↦ (a.1 = a'.1 ∧ Rp π iv publicInput stream s a.2 a'.2) ∧
          WCtx π iv publicInput stream st s cS rS opS.toList [b0, b1, b2] mapS r map z0)
        (fun _ _ _ _ hg hs h ↦ ⟨⟨h.1.1, Rp.pgrow hg hs h.1.2⟩, WCtx.pgrow π iv publicInput stream hg hs h.2⟩) _
        (fun t (e : ℕ × E) ↦
          t + e.2 * instWK r ((valC π iv publicInput stream st cS).points.getD e.1 [])
            (qvOf L - ((valC π iv publicInput stream st cS).points.getD e.1 []).length) * partV r z0 L .qflock)
        (fun (b : Nat) (a : E) s ↦ Rp π iv publicInput stream s b a) ?_ res.2.toList W st7 t1 _ hs7.good
        ((RpKeyed.pgrow π iv publicInput stream hs6.good hs7
            (RpKeyed.pgrow π iv publicInput stream hs5.good hs6 hW)).imp fun _ _ h ↦ ⟨h, ctx7⟩) ht1)
        fun t2 st8 hs8 ht2 ↦ ?_
      · rintro ⟨p, sm⟩ e' t a s hg ⟨⟨h1, h2⟩, ctx⟩ hta
        dsimp only at h1 h2 ⊢
        rw [← h1]
        refine phc_bind (partS_phc π iv publicInput stream hg ctx.hr ctx.hbasis ctx.hz0 L .qflock)
          fun vs s1 hs1 hvs ↦ ?_
        obtain ⟨fst, qf⟩ := vs
        obtain ⟨-, hqf⟩ := hvs
        dsimp only at hqf ⊢
        refine phc_bind (phc_one π iv publicInput stream hs1.good) fun o s2 hs2 ho ↦ ?_
        have ctx2 := WCtx.pgrow π iv publicInput stream hs1.good hs2 (WCtx.pgrow π iv publicInput stream hg hs1 ctx)
        refine phc_bind (phc_forIn (fun a a' s ↦ Rp π iv publicInput stream s a.1 a'.1 ∧
            Rp π iv publicInput stream s a.2 a'.2)
          (fun _ _ _ _ hg hs h ↦ ⟨Rp.pgrow hg hs h.1, Rp.pgrow hg hs h.2⟩) _ (fun a (xa : E × E) ↦ a * (xa.2 + xa.1))
          (fun (b : Nat) (c : E) s ↦ Rp π iv publicInput stream s b c) ?_ _ _ s2 o 1 hs2.good
          (forall₂_zipC (ctx2.hpts p) (by
            have h := RpL.dropC π iv publicInput stream ctx2.hop (headVars L .qflock - (cS.points.getD p []).length)
            have e : (List.map (fun x ↦ 1 + x) r).drop (headVars L .qflock - (cS.points.getD p []).length) =
                (List.map (fun x ↦ 1 + x) r).drop
                  (qvOf L - ((valC π iv publicInput stream st cS).points.getD p []).length) := by rw [hsbAll p]
            exact e ▸ h)) ho) fun inst s3 hs3 hinst ↦ ?_
        · rintro ⟨x, a⟩ ⟨x', a''⟩ b c s hg ⟨hx, ha⟩ hbc
          dsimp only at hx ha ⊢
          exact phc_bind (phc_add π iv publicInput stream hg ha hx) fun sS s1 hs1 hsS ↦
            phc_bind (phc_mul π iv publicInput stream hs1.good (Rp.pgrow hg hs1 hbc) hsS) fun _ s2 hs2 h ↦
              phc_pure _ hs2.good ⟨_, rfl, h⟩
        · have hs13 : PStep s s3 := hs1.trans (hs2.trans hs3)
          have hs23 : PStep s1 s3 := hs2.trans hs3
          exact phc_bind (phc_mul π iv publicInput stream hs3.good (Rp.pgrow hg hs13 h2) hinst) fun si s4 hs4 hsi ↦
            phc_bind (phc_mul π iv publicInput stream hs4.good hsi
              (Rp.pgrow hs3.good hs4 (Rp.pgrow hs1.good hs23 hqf))) fun siq s5 hs5 hsiq ↦
              phc_bind (phc_add π iv publicInput stream hs5.good
                (Rp.pgrow hs4.good hs5 (Rp.pgrow hs3.good hs4 (Rp.pgrow hg hs13 hta))) hsiq) fun _ s6 hs6 h ↦
                phc_pure _ hs6.good ⟨_, rfl, h⟩
      · have e1 : W.foldl (fun t (e : ℕ × E) ↦
            t + e.2 * instWK r ((valC π iv publicInput stream st cS).points.getD e.1 [])
            (qvOf L - ((valC π iv publicInput stream st cS).points.getD e.1 []).length) * partV r z0 L .qflock)
            (V.foldl (fun t (e : (ℕ × ℕ × ℕ) × E) ↦
              t + (fun key : ℕ × ℕ × ℕ ↦ rowW r map z0 ((valC π iv publicInput stream st cS).points.getD key.1 [])
                key.2.1 key.2.2) e.1 * e.2) 0) = progWK (valC π iv publicInput stream st cS) L r map z0 := by
          have h2 : (W.map fun (e : ℕ × E) ↦
              e.2 * instWK r ((valC π iv publicInput stream st cS).points.getD e.1 [])
                (qvOf L - ((valC π iv publicInput stream st cS).points.getD e.1 []).length) * partV r z0 L .qflock).sum =
              rdK (fun p ↦ instWK r ((valC π iv publicInput stream st cS).points.getD p [])
                (qvOf L - ((valC π iv publicInput stream st cS).points.getD p []).length) * partV r z0 L .qflock) W := by
            unfold rdK
            exact congrArg List.sum (List.map_congr_left fun e _ ↦ by ring)
          rw [UniSound.Ids.Weights.foldl_add_map, UniSound.Ids.Weights.foldl_add_map, zero_add, h2, progWK_split,
            ← hrow, ← hslot]
          rfl
        rw [← e1]
        exact phc_pure _ hs8.good ht2

end WeightSim2

/-! ## A term's weight as the program reads it is `UniKeccak.weightAtK`'s -/

section TermK

open UniSound.Ids (limbScale)
open UniSound.Ids.Weights (twistPt ringRow zero_ne_ringTwist rowEq_eq foldl_mul_map foldl_add_map getD_of_take)

/-- **A term's kind** at a layout: untwisted, not a slot, its point of at least its column's variables; or untwisted,
a slot, its point shorter than `q_flock`'s blocks' variables; or the ring-switch term on
a column of at most its point's variables. -/
def TermKindK (L : StackLayout) (col : Column) (pt : List E) (tw : ℕ) : Prop :=
  (tw = 0 ∧ (∀ j, col ≠ .qflockSlot j) ∧ ∀ b ∈ L.limbs col, b.2.1 ≤ pt.length) ∨
  (tw = 0 ∧ (∃ j, col = .qflockSlot j) ∧ ∀ b ∈ L.limbs .qflock, pt.length < b.2.1) ∨
  (tw = ringTwist ∧ (∀ j, col ≠ .qflockSlot j) ∧ ∀ b ∈ L.limbs col, b.2.1 ≤ pt.length)

theorem slotViewK_of_ne {col : Column} (h : ∀ j, col ≠ .qflockSlot j) (qv : ℕ) (pt point : List E) :
    slotViewK qv pt col point = (col, point, 0) := by
  unfold slotViewK
  split
  · exact absurd rfl (h _)
  · rfl

theorem instWK_eq (r pt : List E) (sb : ℕ) (hr : sb + pt.length ≤ r.length) :
    instWK r pt sb = ((List.range pt.length).map fun k ↦ 1 + pt.getD k 0 + r.getD (sb + k) 0).prod := by
  unfold instWK
  rw [zip_foldlC _ _ _ (by rw [List.length_drop, List.length_map]; omega), one_mul]
  refine congrArg List.prod (List.map_congr_left fun k hk ↦ ?_)
  have hk := List.mem_range.mp hk
  have e : ((r.map (1 + ·)).drop sb).getD k 0 = (r.map (1 + ·)).getD (sb + k) 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [e, opr_getD r (by omega)]
  ring

theorem accWK_eq (r : List E) (z0 : E) (j sb : ℕ) (hr : sb ≤ r.length) :
    accWK r z0 j sb = ((List.range sb).map fun k ↦ 1 + bitE j k + r.getD k 0).prod := by
  unfold accWK
  rw [foldl_mul_map, one_mul, ← List.range_eq_range']
  refine congrArg List.prod (List.map_congr_left fun k hk ↦ ?_)
  have hk := List.mem_range.mp hk
  have hkr : k < r.length := by omega
  unfold bitE
  by_cases hb : j.testBit k = true
  · simp only [hb, ↓reduceIte]
    rw [getD_lt_z hkr, CharTwo.add_self_eq_zero, zero_add]
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    rw [opr_getD r hkr, add_zero]

theorem rowEq_slotK (j sb : ℕ) (pt r : List E) :
    rowEq ((List.range sb).map (bitE j) ++ pt) ((List.range sb).map (bitE j) ++ pt).length r =
      ((List.range sb).map fun k ↦ 1 + bitE j k + r.getD k 0).prod *
        ((List.range pt.length).map fun k ↦ 1 + pt.getD k 0 + r.getD (sb + k) 0).prod := by
  rw [rowEq_eq, List.length_append, List.length_map, List.length_range, List.range_add, List.map_append,
    List.prod_append, List.map_map]
  refine congrArg₂ (· * ·) ?_ ?_
  · refine congrArg List.prod (List.map_congr_left fun k hk ↦ ?_)
    have hk := List.mem_range.mp hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hk), List.getElem?_map,
      List.getElem?_range hk]
    rfl
  · refine congrArg List.prod (List.map_congr_left fun k _ ↦ ?_)
    simp only [Function.comp_apply]
    rw [List.getD_eq_getElem?_getD (l := (List.range sb).map (bitE j) ++ pt),
      List.getElem?_append_right (by simp), List.getD_eq_getElem?_getD]
    simp

/-- **A term's weight as the Keccak program reads it is `UniKeccak.weightAtK`'s**, read at any extension `q` of its
point (its point itself for a slot term), at a point `r` of at least every block's variables. -/
theorem termPK_eq {L : StackLayout} (hL : LayoutOK L) (r map : List E) (z0 : E)
    (hr : ∀ col, ∀ b ∈ L.limbs col, b.2.1 ≤ r.length) {col : Column} {pt q : List E} {tw : ℕ}
    (hk : TermKindK L col pt tw) (hq : q.take pt.length = pt) (hs : (∃ j, col = .qflockSlot j) → q = pt) :
    termPK L r map z0 col q tw = UniKeccak.weightAtK ⟨[pt], [(col, 0, tw, 1)], 0, 1⟩ L r (some map) := by
  rw [weightAtK_single]
  rcases hk with ⟨rfl, hne, hlen⟩ | ⟨rfl, ⟨j, rfl⟩, hlen⟩ | ⟨rfl, hne, hlen⟩
  · rw [termPK_of_ne hne, partV_eq hL]
    unfold wSumK
    rw [ite_eq_right zero_ne_ringTwist, slotViewK_of_ne hne]
    dsimp only
    refine sum_factorC _ r _ _ fun b hb ↦ ?_
    obtain ⟨_, hbv⟩ := hL col b hb
    rw [ite_eq_right (lt_irrefl 0)]
    show rowEq pt b.2.1 r = _
    rw [hbv]
    exact (rowW_plain r map z0 pt q _ (hbv ▸ hr col b hb) (hbv ▸ hlen b hb) hq).symm
  · rw [hs ⟨j, rfl⟩]
    simp only [termPK]
    unfold wSumK
    rw [ite_eq_right zero_ne_ringTwist]
    simp only [slotViewK]
    rw [partV_eq hL, ← mul_assoc]
    refine sum_factorC _ r _ _ fun b hb ↦ ?_
    have hbq : b.2.1 = qvOf L := by rw [(hL .qflock b hb).2, qvOf_eq]
    have hlt : pt.length < qvOf L := hbq ▸ hlen b hb
    have hqv : qvOf L ≤ r.length := hbq ▸ hr .qflock b hb
    have hpos : ((List.range (qvOf L - pt.length)).map (bitE j) ++ twistPt pt 0).length > 0 := by
      simp; omega
    simp only [hpos, ↓reduceIte]
    show rowEq ((List.range (qvOf L - pt.length)).map (bitE j) ++ pt)
      ((List.range (qvOf L - pt.length)).map (bitE j) ++ pt).length r = _
    rw [rowEq_slotK, accWK_eq r z0 j _ (by omega), instWK_eq r pt _ (by omega)]
  · rw [termPK_of_ne hne, partV_eq hL]
    unfold wSumK
    rw [ite_eq_left rfl]
    refine sum_factorC _ r _ _ fun b hb ↦ ?_
    obtain ⟨_, hbv⟩ := hL col b hb
    show Flock.towerWeightAt (pt.take b.2.1) ((r.map (1 + ·)).take b.2.1) map = _
    rw [hbv]
    exact (rowW_ring r map z0 pt q _ (hbv ▸ hr col b hb) (hbv ▸ hlen b hb) hq).symm

end TermK

section CombineWeight

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

open Gen (TermG RelG CombG combineG mineG mergedPointG combineEqG mergedPrefixG combineG_points_mem combineG_relations)
open UniSound.Ids (mine)

/-- A kind is kept by an extension of the point (the point itself for a slot term). -/
theorem TermKindK.extend {L : StackLayout} {col : Column} {pt q : List E} {tw : ℕ} (hk : TermKindK L col pt tw)
    (hq : q.take pt.length = pt) (hs : (∃ j, col = .qflockSlot j) → q = pt) : TermKindK L col q tw := by
  have hl : pt.length ≤ q.length := by
    have := congrArg List.length hq
    rw [List.length_take] at this
    omega
  rcases hk with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1, h2, fun b hb ↦ (h3 b hb).trans hl⟩
  · exact Or.inr (Or.inl ⟨h1, h2, by rw [hs h2]; exact h3⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, fun b hb ↦ (h3 b hb).trans hl⟩)

/-- The batch's view of a combined claim. -/
structure CombRepK (st : RecState) (L : StackLayout) (cS : CombinedS) (cb : Combined) : Prop where
  held : HeldC st cS
  value : Rp π iv publicInput stream st cS.value cb.value
  relations : cS.relations = cb.relations
  weight : ∀ (r map : List E) (z0 : E), (∀ col, ∀ b ∈ L.limbs col, b.2.1 ≤ r.length) →
    progWK (valC π iv publicInput stream st cS) L r map z0 = UniKeccak.weightAtK cb L r (some map)

theorem CombRepK.grow {st st' : RecState} (hk : KInv st) (hgr : Grows st st') {L : StackLayout} {cS : CombinedS}
    {cb : Combined} (h : CombRepK π iv publicInput stream st L cS cb) : CombRepK π iv publicInput stream st' L cS cb :=
  ⟨h.held.grows hgr, Rp.grow π iv publicInput stream hk hgr h.value, h.relations, fun r map z0 hr ↦ by
    rw [valC_grow π iv publicInput stream hk hgr h.held]
    exact h.weight r map z0 hr⟩

theorem sum_zipIdx_forall₂GK {α β : Type} {R : α → β → Prop} (F : α × ℕ → E) (G : β × ℕ → E)
    (h : ∀ a b k, R a b → F (a, k) = G (b, k)) : ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ n,
      ((l.zipIdx n).map F).sum = ((m.zipIdx n).map G).sum
  | _, _, .nil, _ => rfl
  | _, _, .cons hr hl, n => by
    rw [List.zipIdx_cons, List.zipIdx_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, h _ _ n hr,
      sum_zipIdx_forall₂GK F G h hl (n + 1)]

theorem sum_map_forall₂GK {α β : Type} {R : α → β → Prop} (F : α → E) (G : β → E)
    (h : ∀ a b, R a b → F a = G b) : ∀ {l : List α} {m : List β}, List.Forall₂ R l m →
      (l.map F).sum = (m.map G).sum
  | _, _, .nil => rfl
  | _, _, .cons hr hl => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, h _ _ hr, sum_map_forall₂GK F G h hl]

/-- **Combine and the weights, off the hazard**: for each commitment, the program's combined claim (points compared by
node) and `UniStatement`'s (by value) have the same value, the same count, and the same weight at every batch point
of at least every block's variables (the program's by `weight_at`'s grouping, `progW`), when every term has its
kind and no point extends a slot term's (the merge hazard's absence). -/
theorem combine_weightK {st : RecState} (hg : Good st) {relsS : List RelationS} {rels : List Relation}
    (hr : RpRels π iv publicInput stream st relsS rels) (c : Commitment) {rhoS : Nat} {ρ : E}
    (hrho : Rp π iv publicInput stream st rhoS ρ) (L : StackLayout) (hL : LayoutOK L)
    (hK : ∀ r ∈ mine rels c, ∀ tm ∈ r.terms, TermKindK L tm.column tm.point tm.twist)
    (hself : ∀ r ∈ mine rels c, ∀ tm ∈ r.terms, (∃ j, tm.column = .qflockSlot j) →
      ∀ r' ∈ mine rels c, ∀ tm' ∈ r'.terms, tm.point.length < tm'.point.length →
        tm'.point.take tm.point.length ≠ tm.point) :
    PHc st (Pi1.combine relsS c rhoS) fun out st' ↦
      OptRel (CombRepK π iv publicInput stream st' L) out (combine rels c ρ) := by
  have hG : List.Forall₂ (RpRelN π iv publicInput stream st) relsS (relsS.map (toG π iv publicInput stream st)) := by
    rw [List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun r hr' ↦ by
      obtain ⟨u, -, hu⟩ := forall₂_mem_leftC hr r hr'
      exact toG_rpRelN π iv publicInput stream hu
  have hC : List.Forall₂ (Corr π iv publicInput stream st) (relsS.map (toG π iv publicInput stream st)) rels := by
    rw [List.forall₂_map_left_iff]
    exact hr.imp fun _ _ h ↦ toG_corr π iv publicInput stream h
  have hM : List.Forall₂ (Corr π iv publicInput stream st) (mineG (relsS.map (toG π iv publicInput stream st)) c)
      (mine rels c) :=
    forall₂_filterC _ _ (fun g u h ↦ by rw [Corr.commitment π iv publicInput stream h]) hC
  have hlen := List.Forall₂.length_eq hM
  refine phc_conseq (combine_phc π iv publicInput stream hg hG c hrho) fun out st' hs h ↦ ?_
  have hk := hg.inv.kinv
  by_cases he : mine rels c = []
  · have he' : mineG (relsS.map (toG π iv publicInput stream st)) c = [] := by
      rw [← List.length_eq_zero_iff, hlen, List.length_eq_zero_iff]
      exact he
    have h1 : combine rels c ρ = none := by
      rw [UniSound.Ids.Weights.combine_eq, ite_eq_left (by rw [he]; rfl)]
    have h2 : combineG (relsS.map (toG π iv publicInput stream st)) c ρ = none := by
      rw [Gen.combineG_eq, ite_eq_left (by rw [he']; rfl)]
    rw [h2] at h
    rw [h1]
    cases out with
    | none => trivial
    | some _ => exact h.elim
  · have he' : mineG (relsS.map (toG π iv publicInput stream st)) c ≠ [] := by
      rw [ne_eq, ← List.length_eq_zero_iff, hlen, List.length_eq_zero_iff]
      exact he
    obtain ⟨cG, hcG, hvalG, hFG⟩ := combineEqG _ c ρ he'
    obtain ⟨cb, hcb, hval, hF⟩ := UniSound.Ids.combineEq rels c ρ he
    rw [hcG] at h
    rw [hcb]
    cases out with
    | none => exact h.elim
    | some cS =>
      obtain ⟨hpts, hterms, hvalue, hrels⟩ := h
      have hsz := Grows.size_le hs.grows
      have hMm := forall₂_memC hM
      -- The points' nodes are held.
      have hheldP : ∀ q ∈ cG.points, ∀ i ∈ q, i < st.nodes.size := by
        intro q hq i hi
        obtain ⟨g, hg', tm, htm, rfl⟩ := combineG_points_mem hcG q hq
        obtain ⟨u, -, hgu⟩ := forall₂_mem_leftC hM g hg'
        obtain ⟨v, -, htv⟩ := forall₂_mem_leftC hgu.1 tm htm
        exact htv.2.2.2.1 i hi
      have hheld : HeldC st' cS := by
        refine ⟨fun q hq i hi ↦ lt_of_lt_of_le (hheldP q (hpts ▸ hq) i hi) hsz, fun x hx ↦ ?_, hvalue.1⟩
        obtain ⟨y, -, hxy⟩ := forall₂_mem_leftC hterms x hx
        exact hxy.2.2.2.1
      have hvals : ∀ q ∈ cG.points, q.map (val π iv publicInput stream st') = q.map (val π iv publicInput stream st) :=
        fun q hq ↦ List.map_congr_left fun i hi ↦ val_grow π iv publicInput stream hk hs.grows (hheldP q hq i hi)
      refine ⟨hheld, ?_, ?_, ?_⟩
      · rw [hval, ← sum_zipIdx_forall₂C ρ (fun g : RelG Nat ↦ g.value) (fun u : Relation ↦ u.value)
          (fun _ _ h ↦ h.2) hM 0, ← hvalG]
        exact hvalue
      · rw [hrels, combineG_relations hcG, hlen]
        rw [UniSound.Ids.Weights.combine_eq, ite_eq_right (by simpa [List.isEmpty_iff] using he)] at hcb
        rw [← Option.some.inj hcb]
      · intro r map z0 hrl
        -- The program's side: the claim over nodes.
        have hvC : (valC π iv publicInput stream st' cS).terms = cG.terms :=
          valTm_map π iv publicInput stream hterms
        have hvP : ∀ p, (valC π iv publicInput stream st' cS).points.getD p [] =
            (cG.points.getD p []).map (val π iv publicInput stream st') := by
          intro p
          show (cS.points.map (·.map (val π iv publicInput stream st'))).getD p
            ([].map (val π iv publicInput stream st')) = _
          rw [List.getD_map, hpts]
        have hP : progWK (valC π iv publicInput stream st' cS) L r map z0 =
            (cG.terms.map fun tm ↦ tm.2.2.2 * termPK L r map z0 tm.1
              ((cG.points.getD tm.2.1 []).map (val π iv publicInput stream st')) tm.2.2.1).sum := by
          unfold progWK
          rw [hvC]
          refine congrArg List.sum (List.map_congr_left fun x _ ↦ ?_)
          rw [hvP]
        have eG := hFG (fun col q tw ↦ termPK L r map z0 col (q.map (val π iv publicInput stream st')) tw)
        have eF := hF (fun col pt tw ↦ UniKeccak.weightAtK ⟨[pt], [(col, 0, tw, 1)], 0, 1⟩ L r (some map))
        have eL := weightAtK_linear cb L r (some map)
        beta_reduce at eG eF
        rw [hP, eG]
        rw [eL]
        refine Eq.trans ?_ eF.symm
        refine sum_zipIdx_forall₂GK _ _ (fun g u k h ↦ ?_) hMm 0
        obtain ⟨⟨hgt, -⟩, hgm, hum⟩ := h
        refine congrArg (ρ ^ k * ·) ?_
        refine sum_map_forall₂GK _ _ (fun t v htv ↦ ?_) (forall₂_memC hgt)
        obtain ⟨⟨hcol, htw, hpt, hheldt, hco⟩, htm, hvm⟩ := htv
        rw [hco, hcol, htw]
        refine congrArg (v.coefficient * ·) ?_
        -- The term's point merged, by node and by value.
        have hkind := hK u hum v hvm
        obtain ⟨hpre, g', hg', t', ht', hpt'⟩ := mergedPrefixG _ t.point ⟨g, hgm, t, htm, rfl⟩
        obtain ⟨u', hu', hgu'⟩ := forall₂_mem_leftC hM g' hg'
        obtain ⟨v', hv', htv'⟩ := forall₂_mem_leftC hgu'.1 t' ht'
        set qN := mergedPointG (mineG (relsS.map (toG π iv publicInput stream st)) c) t.point with hqN
        have hqv : qN.map (val π iv publicInput stream st') = v'.point := by
          rw [← htv'.2.2.1, ← hpt']
          exact List.map_congr_left fun i hi ↦ val_grow π iv publicInput stream hk hs.grows (htv'.2.2.2.1 i hi)
        have hlen' : t.point.length = v.point.length := by rw [← hpt, List.length_map]
        have hext : v'.point.take v.point.length = v.point := by
          rw [← hqv, ← List.map_take, ← hlen', hpre, ← hpt]
          exact List.map_congr_left fun i hi ↦ val_grow π iv publicInput stream hk hs.grows (hheldt i hi)
        have hslot : (∃ j, v.column = .qflockSlot j) → v'.point = v.point := by
          intro hj
          by_contra hne
          have hle : v.point.length ≤ v'.point.length := by
            have := congrArg List.length hext
            rw [List.length_take] at this
            omega
          have hlt : v.point.length < v'.point.length := by
            rcases Nat.lt_or_eq_of_le hle with h | h
            · exact h
            · exact absurd ((List.take_of_length_le (by omega)).symm.trans hext) hne
          exact hself u hum v hvm hj u' hu' v' hv' hlt hext
        rw [hqv, termPK_eq hL r map z0 hrl hkind hext hslot]
        -- `UniStatement`'s side: its merged point extends the term's, and is the term's for a slot.
        obtain ⟨hpreE, u2, hu2, v2, hv2, hpt2⟩ := UniSound.Ids.mergedPrefix (mine rels c) v.point ⟨u, hum, v, hvm, rfl⟩
        have hslotE : (∃ j, v.column = .qflockSlot j) →
            UniSound.Ids.mergedPoint (mine rels c) v.point = v.point := by
          intro hj
          by_contra hne
          have hle : v.point.length ≤ (UniSound.Ids.mergedPoint (mine rels c) v.point).length := by
            have := congrArg List.length hpreE
            rw [List.length_take] at this
            omega
          have hlt : v.point.length < (UniSound.Ids.mergedPoint (mine rels c) v.point).length := by
            rcases Nat.lt_or_eq_of_le hle with h | h
            · exact h
            · exact absurd ((List.take_of_length_le (by omega)).symm.trans hpreE) hne
          exact hself u hum v hvm hj u2 hu2 v2 hv2 (hpt2 ▸ hlt) (hpt2 ▸ hpreE)
        rw [← termPK_eq hL r map z0 hrl (hkind.extend hpreE hslotE) (List.take_of_length_le le_rfl)
          (fun _ ↦ rfl), termPK_eq hL r map z0 hrl hkind hpreE hslotE]



end CombineWeight

end RecGraphKeccak.Sim
