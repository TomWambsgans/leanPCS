-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The heap's blocks at a shape are computed as
-- `formal/UniSound`'s `heap_reference` computes the reference shape's (`HeapLayout.new`'s sort, without evaluating
-- `mergeSort`); `heapRelations_phcS` is `RecGraph.Sim.heapRelations_phc` for any shape whose table blocks are among the
-- six tables.
import RecGraph.Sim.Relations
import RecGraphKeccak.Sim.Tables
import UniSound.Ids.Deployed

/-!
# The heap's relations at the Keccak shape, simulated

* `heap_keccak128`: `keccak128`'s heap, `2^22` positions, its ten blocks (memory, bytecode, the six tables largest
  first, two unused), and `heapTables_keccak128`: its table blocks are among the six tables;
* `heapRelations_phcS`: `RecGraph.Sim.heapRelations_phc` at any such shape (its proof, the shape a parameter);
* **`heapSpecK : HeapSpecK partRK heapShapeK`**.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph RecGraph.Pi1 RecGraph.Sim
  RecGraphKeccak.Pi1 UniSound.Ids

theorem keccak128_eq : keccak128 = ⟨20, 18, [15, 16, 15, 16, 14, 15]⟩ := by
  unfold keccak128 UniKeccak.keccakShapeOf shapeWith
  congr 1

/-- The used blocks of `keccak128`, sorted. -/
def heapSortedK : List (Leaves × ℕ) :=
  [(.memory, 20), (.bytecode, 18), (.table 1, 16), (.table 3, 16), (.table 0, 15), (.table 2, 15), (.table 5, 15),
    (.table 4, 14)]

theorem heapLe_antisymmK : ∀ a ∈ heapSortedK, ∀ b ∈ heapSortedK, heapLe a b = true →
    heapLe b a = true → a = b := by
  decide +kernel

/-- **`keccak128`'s used blocks, sorted** (no evaluation of `mergeSort`). -/
theorem heapSortedK_eq :
    ([(Leaves.memory, 20), (.bytecode, 18)] ++ (List.range [15, 16, 15, 16, 14, 15].length).map
        fun t ↦ (Leaves.table t, [15, 16, 15, 16, 14, 15].getD t 0)).mergeSort
      (fun a b ↦ b.2 < a.2 || (a.2 == b.2 && a.1.order ≤ b.1.order)) = heapSortedK := by
  have hp := List.mergeSort_perm
    ([(Leaves.memory, 20), (.bytecode, 18)] ++ (List.range [15, 16, 15, 16, 14, 15].length).map
        fun t ↦ (Leaves.table t, [15, 16, 15, 16, 14, 15].getD t 0)) heapLe
  have hu : ([(Leaves.memory, 20), (.bytecode, 18)] ++ (List.range [15, 16, 15, 16, 14, 15].length).map
        fun t ↦ (Leaves.table t, [15, 16, 15, 16, 14, 15].getD t 0)).Perm heapSortedK := by
    decide +kernel
  refine List.Perm.eq_of_pairwise (le := fun a b ↦ heapLe a b = true) (fun a b ha hb h1 h2 ↦ ?_)
    (List.pairwise_mergeSort heapLe_trans heapLe_total _) (by decide +kernel) (hp.trans hu)
  exact heapLe_antisymmK a ((hp.trans hu).mem_iff.mp ha) b hb h1 h2

/-- `keccak128`'s heap blocks. -/
def heapBlocksK : List (Leaves × ℕ × ℕ) :=
  [(.memory, 20, 2097152), (.bytecode, 18, 3145728), (.table 1, 16, 3407872), (.table 3, 16, 3473408),
    (.table 0, 15, 3538944), (.table 2, 15, 3571712), (.table 5, 15, 3604480), (.table 4, 14, 3637248),
    (.unused, 14, 3653632), (.unused, 19, 3670016)]

/-- **`keccak128`'s heap**: `2^22` positions, its blocks. -/
theorem heap_keccak128 : keccak128.heap.h = 22 ∧ keccak128.heap.blocks.map Block.toTuple = heapBlocksK := by
  rw [keccak128_eq]
  unfold Shape.heap HeapLayout.new
  dsimp only
  rw [heapSortedK_eq]
  decide +kernel

/-- `keccak128`'s table blocks are among the six tables. -/
theorem heapTables_keccak128 :
    ∀ b ∈ keccak128.heap.blocks, match b.leaves with | .table t => t < 6 | _ => True := by
  intro b hb
  have hm : Block.toTuple b ∈ heapBlocksK := heap_keccak128.2 ▸ List.mem_map_of_mem hb
  have key : ∀ x ∈ heapBlocksK, match x.1 with | .table t => t < 6 | _ => True := by
    intro x hx
    simp only [heapBlocksK, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have := key _ hm
  exact this

section Rel

variable (π : KeccakState → KeccakState) (iv publicInput : List UInt8) (stream : Array UInt8)

/-- **The heap's relations** (`heapRelations` at π1-rec3's shape): the program's represent `UniStatement`'s, and its
leaf columns are `UniStatement`'s. -/
theorem heapRelations_phcS (S : UniStatement.Shape)
    (hS : ∀ b ∈ S.heap.blocks, match b.leaves with | .table t => t < 6 | _ => True) {st : RecState} (hg : Good st) {active : List Nat} {activeE : List E}
    {parts : List TablePartS} {partsE : List TablePart} {weights : Array Nat} {weightsE : Array E}
    {w : List Nat} {wE : List E}
    (hc : HeapCtx π iv publicInput stream st active activeE parts partsE weights weightsE w wE)
    (hp6 : partsE.length = 6) {beta hv cv mpl mps bpl bps : Nat} {betaE hvE cvE mplE mpsE bplE bpsE : E}
    (hbeta : Rp π iv publicInput stream st beta betaE) (hhv : Rp π iv publicInput stream st hv hvE)
    (hcv : Rp π iv publicInput stream st cv cvE) (hmpl : Rp π iv publicInput stream st mpl mplE)
    (hmps : Rp π iv publicInput stream st mps mpsE) (hbpl : Rp π iv publicInput stream st bpl bplE)
    (hbps : Rp π iv publicInput stream st bps bpsE) (cc : List ℕ) :
    PHc st (Pi1.heapRelations S active parts weights beta hv cv mpl mps bpl bps w cc) fun a st' ↦
      RpRels π iv publicInput stream st' a.1
        (UniStatement.heapRelations S activeE partsE weightsE betaE hvE cvE mplE mpsE bplE bpsE wE cc).1 ∧
      a.2 = (UniStatement.heapRelations S activeE partsE weightsE betaE hvE cvE mplE mpsE bplE bpsE wE
        cc).2 := by
  rw [UniSound.Ids.Eval.heapRelations_fst, heapRelations_sndC]
  unfold Pi1.heapRelations
  dsimp only
  have hT := RpL.takeC π iv publicInput stream hc.hwE S.heap.h
  -- `T(t)`.
  refine phc_bind (phc_one π iv publicInput stream hg) fun o st1 hs1 ho ↦ ?_
  have hc1 := HeapCtx.pgrow π iv publicInput stream hg hs1 hc
  refine phc_bind (equalS_phcC π iv publicInput stream hs1.good .heap (RpL.pgrow hg hs1 hT)
    (Rp.pgrow hg hs1 hhv)) fun r1 st2 hs2 hr1 ↦ ?_
  have hs02 := hs1.trans hs2
  -- The tree.
  refine phc_bind (phc_add π iv publicInput stream hs2.good
    (RpL.getDz π iv publicInput stream (RpL.pgrow hg hs02 hT) (Rp.pgrow hg hs02 hc.h0) 0)
    (Rp.pgrow hs1.good hs2 ho)) fun n0 st3 hs3 hn0 ↦ ?_
  have hs03 := hs02.trans hs3
  refine phc_bind (phc_mul π iv publicInput stream hs3.good
    (RpL.getDz π iv publicInput stream (RpL.pgrow hg hs03 hc.hwE) (Rp.pgrow hg hs03 hc.h0) 1)
    (Rp.pgrow hg hs03 hhv)) fun w1v st4 hs4 hw1v ↦ ?_
  have hs04 := hs03.trans hs4
  have hwh4 := RpL.getDz π iv publicInput stream (RpL.pgrow hg hs04 hc.hwE) (Rp.pgrow hg hs04 hc.h0)
    S.heap.h
  refine phc_bind (phc_mul π iv publicInput stream hs4.good hwh4 hwh4) fun whh st5 hs5 hwhh ↦ ?_
  refine phc_bind (phc_zero π iv publicInput stream hs5.good) fun z st6 hs6 hz ↦ ?_
  have hs06 := hs04.trans (hs5.trans hs6)
  have hs36 := hs4.trans (hs5.trans hs6)
  have hr2 : RpRel π iv publicInput stream st6
      { terms := [termS .heap ((w.drop 1).take S.heap.h) (w.getD 1 0),
          termS .heap ((w.take S.heap.h).set 0 n0) w1v,
          termS (.treeQuotient 0) (w.take S.heap.h) (w.getD S.heap.h 0),
          termS (.treeQuotient 1) [] whh], value := z }
      { terms := [term .heap ((wE.drop 1).take S.heap.h) (wE.getD 1 0),
          term .heap ((wE.take S.heap.h).modify 0 (· + 1)) (wE.getD 1 0 * hvE),
          term (.treeQuotient 0) (wE.take S.heap.h) (wE.getD S.heap.h 0),
          term (.treeQuotient 1) [] (wE.getD S.heap.h 0 * wE.getD S.heap.h 0)], value := 0 } := by
    have hw6 := RpL.pgrow hg hs06 hc.hwE
    have h06 := Rp.pgrow hg hs06 hc.h0
    refine ⟨?_, hz⟩
    refine List.Forall₂.cons ⟨rfl, rfl, RpL.takeC π iv publicInput stream (RpL.dropC π iv publicInput stream hw6 1) _,
      RpL.getDz π iv publicInput stream hw6 h06 1⟩ ?_
    refine List.Forall₂.cons ⟨rfl, rfl, ?_, Rp.pgrow hs4.good (hs5.trans hs6) hw1v⟩ ?_
    · refine forall₂_set_modifyC (RpL.takeC π iv publicInput stream hw6 _) 0 _ _ fun hi ↦ ?_
      have := Rp.pgrow hs3.good hs36 hn0
      rw [← List.getD_eq_getElem _ 0 hi]
      exact this
    refine List.Forall₂.cons ⟨rfl, rfl, RpL.takeC π iv publicInput stream hw6 _,
      RpL.getDz π iv publicInput stream hw6 h06 _⟩ ?_
    exact List.Forall₂.cons ⟨rfl, rfl, List.Forall₂.nil, Rp.pgrow hs5.good hs6 hwhh⟩ List.Forall₂.nil
  -- The root.
  have ho6 := Rp.pgrow hs1.good (hs2.trans (hs3.trans hs36)) ho
  refine phc_bind (phc_snoc_range π iv publicInput stream hs6.good (fun s ↦ Rp π iv publicInput stream s o 1)
    (fun _ _ hg hs h ↦ Rp.pgrow hg hs h) ho6 S.heap.h (fun l ↦ if l = 0 then (1 : E) else 0) _ ?_)
    fun atOne st7 hs7 ⟨hatOne, ho7⟩ ↦ ?_
  · intro k b s hg' hos _
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte]
      exact phc_bind (phc_pure _ hg' hos) fun v s' hs' hv ↦ phc_pure _ hs'.good ⟨v, rfl, hv⟩
    · simp only [hk, ↓reduceIte]
      exact phc_bind (phc_zero π iv publicInput stream hg') fun v s' hs' hv ↦ phc_pure _ hs'.good ⟨v, rfl, hv⟩
  have hs07 := hs06.trans hs7
  have hc7 := HeapCtx.pgrow π iv publicInput stream hg hs07 hc
  have hw07 := fun k ↦ RpL.arrGetD0 π iv publicInput stream hc7.hw hc7.h0 k
  refine phc_bind (phc_const π iv publicInput stream hs7.good sepState) fun c1 st8 hs8 hc1' ↦ ?_
  refine phc_bind (phc_mul π iv publicInput stream hs8.good (Rp.pgrow hs7.good hs8 (hw07 0)) hc1')
    fun w0s st9 hs9 hw0s ↦ ?_
  have hs79 := hs8.trans hs9
  refine phc_bind (phc_add π iv publicInput stream hs9.good (Rp.pgrow hg (hs07.trans hs79) hbeta) hw0s)
    fun i1 st10 hs10 hi1 ↦ ?_
  have hs710 := hs79.trans hs10
  refine phc_bind (phc_add π iv publicInput stream hs10.good hi1 (Rp.pgrow hs7.good hs710 (hw07 1)))
    fun i2 st11 hs11 hi2 ↦ ?_
  have hs711 := hs710.trans hs11
  refine phc_bind (phc_add π iv publicInput stream hs11.good hi2 (Rp.pgrow hs7.good hs711 (hw07 2)))
    fun init st12 hs12 hinit ↦ ?_
  refine phc_bind (phc_const π iv publicInput stream hs12.good _) fun last st13 hs13 hlast ↦ ?_
  refine phc_bind (phc_const π iv publicInput stream hs13.good sepState) fun c2 st14 hs14 hc2' ↦ ?_
  have hs714 := hs711.trans (hs12.trans (hs13.trans hs14))
  refine phc_bind (phc_mul π iv publicInput stream hs14.good (Rp.pgrow hs7.good hs714 (hw07 0)) hc2')
    fun w0s' st15 hs15 hw0s' ↦ ?_
  have hs715 := hs714.trans hs15
  refine phc_bind (phc_add π iv publicInput stream hs15.good (Rp.pgrow hg (hs07.trans hs715) hbeta) hw0s')
    fun f1 st16 hs16 hf1 ↦ ?_
  have hs716 := hs715.trans hs16
  refine phc_bind (phc_mul π iv publicInput stream hs16.good (Rp.pgrow hs7.good hs716 (hw07 1))
    (Rp.pgrow hs13.good (hs14.trans (hs15.trans hs16)) hlast)) fun w1l st17 hs17 hw1l ↦ ?_
  refine phc_bind (phc_add π iv publicInput stream hs17.good (Rp.pgrow hs16.good hs17 hf1) hw1l)
    fun f2 st18 hs18 hf2 ↦ ?_
  have hs718 := hs716.trans (hs17.trans hs18)
  refine phc_bind (phc_add π iv publicInput stream hs18.good hf2 (Rp.pgrow hs7.good hs718 (hw07 2)))
    fun fin st19 hs19 hfin ↦ ?_
  have hs719 := hs718.trans hs19
  have hs1219 := hs13.trans (hs14.trans (hs15.trans (hs16.trans (hs17.trans (hs18.trans hs19)))))
  have hr3 : RpRel π iv publicInput stream st19 { terms := [termS .heap atOne.toList init], value := fin }
      { terms := [term .heap ((List.range S.heap.h).map fun l ↦ if l = 0 then (1 : E) else 0)
          (UniSound.Ids.rootInit weightsE betaE)], value := UniSound.Ids.rootFin S weightsE betaE } :=
    ⟨List.Forall₂.cons ⟨rfl, rfl, RpL.pgrow hs7.good hs719 hatOne, Rp.pgrow hs12.good hs1219 hinit⟩
      List.Forall₂.nil, hfin⟩
  have hs619 := hs7.trans hs719
  have hs019 := hs06.trans hs619
  have hc19 := HeapCtx.pgrow π iv publicInput stream hg hs019 hc
  have hpre : RpRels π iv publicInput stream st19 (#[r1, _, _] : Array RelationS).toList
      [Relation.equal .heap (wE.take S.heap.h) hvE, _, _] :=
    List.Forall₂.cons (RpRel.pgrow π iv publicInput stream hs2.good ((hs3.trans hs36).trans hs619) hr1)
      (List.Forall₂.cons (RpRel.pgrow π iv publicInput stream hs6.good hs619 hr2) (List.Forall₂.cons hr3 List.Forall₂.nil))
  refine phc_bind (phc_forIn_same (fun x ↦ x ∈ S.heap.blocks.zip (List.range S.heap.blocks.length))
    (fun s ↦ HeapCtx π iv publicInput stream s active activeE parts partsE weights weightsE w wE ∧
      Rp π iv publicInput stream s o 1 ∧ Rp π iv publicInput stream s mpl mplE ∧
      Rp π iv publicInput stream s mps mpsE ∧ Rp π iv publicInput stream s bpl bplE ∧
      Rp π iv publicInput stream s bps bpsE)
    (fun _ _ hg hs h ↦ ⟨HeapCtx.pgrow π iv publicInput stream hg hs h.1, Rp.pgrow hg hs h.2.1,
      Rp.pgrow hg hs h.2.2.1, Rp.pgrow hg hs h.2.2.2.1, Rp.pgrow hg hs h.2.2.2.2.1, Rp.pgrow hg hs h.2.2.2.2.2⟩) _
    (fun (acc : List Relation × List (Column × ℕ × Bool)) (x : Block × ℕ) ↦
      (acc.1 ++ [UniSound.Ids.Eval.blockRel S activeE partsE mplE mpsE bplE bpsE wE x],
        acc.2 ++ (leafColsC partsE x.1 x.2).toList))
    (fun (b : Array RelationS × Array (Column × ℕ × Bool)) (acc : List Relation × List (Column × ℕ × Bool)) s ↦
      RpRels π iv publicInput stream s b.1.toList acc.1 ∧ b.2.toList = acc.2) ?_ _ (fun _ h ↦ h) st19 (_, #[])
    (_, []) hs19.good ⟨hc19, Rp.pgrow hs6.good hs619 ho6, Rp.pgrow hg hs019 hmpl, Rp.pgrow hg hs019 hmps,
      Rp.pgrow hg hs019 hbpl, Rp.pgrow hg hs019 hbps⟩ ⟨hpre, rfl⟩) fun res st20 hs20 ⟨hres1, hres2⟩ ↦ ?_
  · rintro ⟨⟨leaves, r, position⟩, index⟩ ⟨R, C⟩ ⟨RE, CE⟩ s hg' hmem ⟨hcs, hos, hmpls, hmpss, hbpls, hbpss⟩ ⟨hR, hC⟩
    dsimp only at hR hC ⊢
    refine phc_bind (phc_snoc_range π iv publicInput stream hg'
      (fun s ↦ RpL π iv publicInput stream s w wE ∧ Rp π iv publicInput stream s 0 0)
      (fun _ _ hg hs h ↦ ⟨RpL.pgrow hg hs h.1, Rp.pgrow hg hs h.2⟩) ⟨hcs.hwE, hcs.h0⟩ S.heap.h
      (fun l ↦ if l < r then wE.getD l 0 + pointE (position >>> l) else pointE (position >>> l)) _ ?_)
      fun mixed s1 hs1 ⟨hmixed, _⟩ ↦ ?_
    · intro k b s'' hg'' ⟨hw'', h0''⟩ _
      refine phc_bind (phc_const π iv publicInput stream hg'' (pointE (position >>> k))) fun c s2 hs2 hcst ↦ ?_
      by_cases hk : k < r
      · simp only [hk, ↓reduceIte]
        exact phc_bind (phc_add π iv publicInput stream hs2.good
          (RpL.getDz π iv publicInput stream (RpL.pgrow hg'' hs2 hw'') (Rp.pgrow hg'' hs2 h0'') k) hcst)
          fun v s3 hs3 hv ↦ phc_pure _ hs3.good ⟨v, rfl, hv⟩
      · simp only [hk, ↓reduceIte]
        exact phc_bind (phc_pure _ hs2.good hcst) fun v s3 hs3 hv ↦ phc_pure _ hs3.good ⟨v, rfl, hv⟩
    · cases leaves
      · -- The memory's leaves.
        dsimp only
        have h01 := Rp.pgrow hg' hs1 hcs.h0
        have hw1 := RpL.pgrow hg' hs1 hcs.hwE
        have hwr := RpL.getDz π iv publicInput stream hw1 h01 r
        rw [prog_pure_bind]
        dsimp only
        refine phc_bind (quotientTerms_phc π iv publicInput stream hs1.good h01 (Column.leafQuotient index) _ hw1 hwr)
          fun qt qs hqs hqt ↦ phc_pure _ hqs.good ⟨_, rfl, ?_, ?_⟩
        · rw [Array.toList_push]
          refine List.rel_append (RpRels.pgrow π iv publicInput stream hg' (hs1.trans hqs) hR)
            (List.Forall₂.cons ⟨?_, Rp.pgrow hs1.good hqs (Rp.pgrow hg' hs1 hmpss)⟩ List.Forall₂.nil)
          exact List.rel_append (List.Forall₂.cons ⟨rfl, rfl, RpL.pgrow hs1.good ((PStep.refl s1 hs1.good).trans hqs) hmixed,
            Rp.pgrow hs1.good hqs (Rp.pgrow hg' hs1 hmpls)⟩ List.Forall₂.nil) hqt
        · rw [Array.toList_append, hC]
          rfl
      · -- The bytecode's leaves.
        dsimp only
        have h01 := Rp.pgrow hg' hs1 hcs.h0
        have hw1 := RpL.pgrow hg' hs1 hcs.hwE
        have hwr := RpL.getDz π iv publicInput stream hw1 h01 r
        rw [prog_pure_bind]
        dsimp only
        refine phc_bind (quotientTerms_phc π iv publicInput stream hs1.good h01 (Column.leafQuotient index) _ hw1 hwr)
          fun qt qs hqs hqt ↦ phc_pure _ hqs.good ⟨_, rfl, ?_, ?_⟩
        · rw [Array.toList_push]
          refine List.rel_append (RpRels.pgrow π iv publicInput stream hg' (hs1.trans hqs) hR)
            (List.Forall₂.cons ⟨?_, Rp.pgrow hs1.good hqs (Rp.pgrow hg' hs1 hbpss)⟩ List.Forall₂.nil)
          exact List.rel_append (List.Forall₂.cons ⟨rfl, rfl, RpL.pgrow hs1.good ((PStep.refl s1 hs1.good).trans hqs) hmixed,
            Rp.pgrow hs1.good hqs (Rp.pgrow hg' hs1 hbpls)⟩ List.Forall₂.nil) hqt
        · rw [Array.toList_append, hC]
          rfl
      · -- A table's leaves.
        rename_i t
        dsimp only
        have ht6 : t < partsE.length := by
          have hb := (List.of_mem_zip hmem).1
          rw [hp6]
          exact hS _ hb
        have hpart := forall₂_getD_partC π iv publicInput stream (hcs.hp.imp fun _ _ h ↦
          RpPart.pgrow π iv publicInput stream hg' hs1 h) ht6 ⟨0, 0, 0, 0, #[]⟩ default
        have h01 := Rp.pgrow hg' hs1 hcs.h0
        have hw1 := RpL.pgrow hg' hs1 hcs.hwE
        have hwr := RpL.getDz π iv publicInput stream hw1 h01 r
        have hz := RpL.getDz π iv publicInput stream (RpL.pgrow hg' hs1 hcs.ha) h01 t
        rw [hpart.2.2.1, hpart.2.2.2.1]
        refine phc_bind (phc_mul π iv publicInput stream hs1.good hz hz) fun sq s2 hs2 hsq ↦ ?_
        refine phc_bind (phc_mul π iv publicInput stream hs2.good (Rp.pgrow hs1.good hs2 hpart.1)
          (Rp.pgrow hs1.good hs2 hwr)) fun pw s3 hs3 hpw ↦ ?_
        refine phc_bind (phc_add π iv publicInput stream hs3.good hpw (Rp.pgrow hs2.good hs3 hsq))
          fun pl s4 hs4 hpl ↦ ?_
        have hs14 := hs2.trans (hs3.trans hs4)
        refine phc_bind (phc_mul π iv publicInput stream hs4.good (Rp.pgrow hs1.good hs14 hpart.2.1)
          (Rp.pgrow hs1.good hs14 hwr)) fun qw s5 hs5 hqw ↦ ?_
        refine phc_bind (phc_add π iv publicInput stream hs5.good hqw
          (Rp.pgrow hs2.good (hs3.trans (hs4.trans hs5)) hsq)) fun ps s6 hs6 hps ↦ ?_
        have hs16 := hs14.trans (hs5.trans hs6)
        refine phc_bind (phc_mul π iv publicInput stream hs6.good (Rp.pgrow hs1.good hs16 hwr)
          (Rp.pgrow hs1.good hs16 hz)) fun sc s7 hs7 hsc ↦ ?_
        have hs17 := hs16.trans hs7
        rw [prog_pure_bind]
        dsimp only
        refine phc_bind (quotientTerms_phc π iv publicInput stream hs7.good (Rp.pgrow hs1.good hs17 h01) (Column.leafQuotient index) _ (RpL.pgrow hs1.good hs17 hw1) hsc)
          fun qt qs hqs hqt ↦ phc_pure _ hqs.good ⟨_, rfl, ?_, ?_⟩
        · rw [Array.toList_push]
          refine List.rel_append (RpRels.pgrow π iv publicInput stream hg' ((hs1.trans hs17).trans hqs) hR)
            (List.Forall₂.cons ⟨?_, Rp.pgrow hs7.good hqs (Rp.pgrow hs6.good hs7 hps)⟩ List.Forall₂.nil)
          exact List.rel_append (List.Forall₂.cons ⟨rfl, rfl, RpL.pgrow hs1.good (hs17.trans hqs) hmixed,
            Rp.pgrow hs7.good hqs (Rp.pgrow hs4.good (hs5.trans (hs6.trans hs7)) hpl)⟩ List.Forall₂.nil) hqt
        · rw [Array.toList_append, hC]
          rfl
      · -- An unused block.
        dsimp only
        refine phc_pure _ hs1.good ⟨_, rfl, ?_, ?_⟩
        · rw [Array.toList_push]
          exact List.rel_append (RpRels.pgrow π iv publicInput stream hg' hs1 hR)
            (List.Forall₂.cons ⟨List.Forall₂.cons ⟨rfl, rfl, hmixed, Rp.pgrow hg' hs1 hos⟩ List.Forall₂.nil,
              Rp.pgrow hg' hs1 hos⟩ List.Forall₂.nil)
        · rw [hC]
          simp [leafColsC]
  · have hc20 := HeapCtx.pgrow π iv publicInput stream hs19.good hs20 hc19
    have ho20 := Rp.pgrow hs6.good (hs619.trans hs20) ho6
    refine phc_bind (quotientTerms_phc π iv publicInput stream hs20.good hc20.h0 .constraintQuotient cc hc20.hwE ho20)
      fun qt st21 hs21 hqt ↦ phc_pure _ hs21.good ⟨?_, ?_⟩
    · rw [Array.toList_push]
      rw [heap_foldlC] at hres1
      exact List.rel_append (RpRels.pgrow π iv publicInput stream hs20.good hs21 hres1)
        (List.Forall₂.cons ⟨hqt, Rp.pgrow hg (hs019.trans (hs20.trans hs21)) hcv⟩ List.Forall₂.nil)
    · rw [heap_foldlC] at hres2
      show res.2.toList = _
      rw [hres2]
      simp

end Rel

/-- **The heap's output at the Keccak shape, its shape**: `UniStatement`'s `heapRelations` at `keccak128`, at some
inputs (six tables' parts with a Keccak table's degrees and active factors, sixteen weights) and the digits `wE`. -/
def heapShapeK (wE : List E) (b : List Relation × List (Column × ℕ × Bool)) : Prop :=
  ∃ (activeE : List E) (partsE : List TablePart) (weightsE : Array E) (betaE hvE cvE mplE mpsE bplE bpsE : E),
    activeE.length = 6 ∧ partsE.length = 6 ∧ (∀ p ∈ partsE, PartDegK p) ∧ weightsE.size = 16 ∧
      b = UniStatement.heapRelations keccak128 activeE partsE weightsE betaE hvE cvE mplE mpsE bplE bpsE wE
        (chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1))

/-- **`HeapSpecK`**, the Keccak composition's interface for the heap's relations. -/
theorem heapSpecK : HeapSpecK partRK heapShapeK := by
  intro π iv publicInput stream st active activeE parts partsE weights weightsE beta hv cv mpl mps bpl bps betaE hvE
    cvE mplE mpsE bplE bpsE w wE hg hseed ha ha6 hp hp6 hw hw16 hbeta hhv hcv hmpl hmps hbpl hbps hwE _
  have h0 := rp_zero_of_seed π iv publicInput stream hg hseed
  have h := heapRelations_phcS π iv publicInput stream keccak128 heapTables_keccak128 hg
    ⟨h0, ha, hp.imp fun _ _ h ↦ h.1, hw, hwE⟩ hp6 hbeta hhv hcv hmpl hmps hbpl hbps
    (chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1))
  exact ⟨h.1, h.2.1, h.2.2, activeE, partsE, weightsE, betaE, hvE, cvE, mplE, mpsE, bplE, bpsE, ha6, hp6,
    forall₂_rightC (fun _ _ h ↦ h.2) hp, hw16, rfl⟩

end RecGraphKeccak.Sim
