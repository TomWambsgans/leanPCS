-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `RecGraph.Sim`'s `Shape.lean` (`shapeSpec`), ported to the
-- Keccak shape `keccak128` (its layouts `layoutsK`, its tables `tablesKeccak`, `Q_W`'s folds `crOfK`); its generic
-- pieces (`limbs_new_memC`, `layoutOK_newC`, `leafDegC`, `PointFact`, `relCommitC`, `y0_neGenC`, …) are reused.
import RecGraph.Sim.Shape
import RecGraphKeccak.Sim.BatchK
import RecGraphKeccak.Sim.Constraint
import RecGraphKeccak.Sim.Heap

/-!
# The Keccak verifier's relations satisfy the tail's conditions off the hazard

**`shapeSpecK : ShapeSpecK tableShapeK constraintShapeK heapShapeK TailOKK`**: as `RecGraph.Sim.shapeSpec`, at
`keccak128`: every layout is `LayoutOK` (`C1`'s columns `c1ColsK`, `q_flock` of `15 + 11 = 26` variables), every term
has its kind (`TermKindK`: a plain term's column has at most its point's variables, the leaf and constraint quotients'
chunks at most `26 = |w|` from the parts' degrees (at most `55`, the `SHA3` table's); a slot is at `y(t)`, `15 < 26`;
the ring term at Flock's point), and no `C1` point extends `y(t)`: `C1`'s points are prefixes of `w` (first coordinate
`t`), `y(t)` or Flock's point (first coordinate `p_0`), and off the hazard `y_0 ≠ t, p_0`.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph RecGraph.Pi1 RecGraph.Sim
  RecGraphKeccak.Pi1

/-! ## `C1`'s columns at the Keccak shape -/

/-- `C1`'s columns at `keccak128` (`layoutsK`'s `c1`). -/
def c1ColsK : List (Column × ℕ × Bool) :=
  [(.qflock, keccak128.heights.getD opSha3 0 + UniKeccak.qflockRowBits, false)] ++
    tablesKeccak.flatMap (fun t ↦
      (List.range t.width).map (fun c ↦ (Column.table t.opcode c, keccak128.heights.getD t.opcode 0, false)) ++
        [(.inverse t.opcode, keccak128.heights.getD t.opcode 0, false)]) ++
    (List.range 4).map (fun k ↦ (Column.memory k, keccak128.logMemory, false)) ++
    [(.bytecodeFinal, keccak128.logBytecode, false)]

theorem layoutsK_c1 (c2 : List (Column × ℕ × Bool)) :
    layoutAt (UniKeccak.layoutsK keccak128 c2) .c1 = StackLayout.new c1ColsK := rfl

/-- `C1`'s column names. -/
def c1NamesK : List Column :=
  [.qflock] ++ tablesKeccak.flatMap (fun t ↦
      (List.range t.width).map (fun c ↦ Column.table t.opcode c) ++ [.inverse t.opcode]) ++
    (List.range 4).map Column.memory ++ [.bytecodeFinal]

/-- A `C1` column's variables at `keccak128`. -/
def c1VarsK : Column → ℕ
  | .qflock => keccak128.heights.getD opSha3 0 + UniKeccak.qflockRowBits
  | .table o _ => keccak128.heights.getD o 0
  | .inverse o => keccak128.heights.getD o 0
  | .memory _ => keccak128.logMemory
  | .bytecodeFinal => keccak128.logBytecode
  | _ => 0

theorem c1ColsK_eq : c1ColsK = c1NamesK.map fun c ↦ (c, c1VarsK c, false) := by
  simp only [c1ColsK, c1NamesK, List.map_append, List.map_flatMap, List.map_cons, List.map_nil,
    List.map_map]
  rfl

/-- **`C2`'s columns' variables** at π1-rec3's shape, the leaf quotients' from `parts`. -/
def c2VarsK (parts : List TablePart) : Column → ℕ
  | .heap => keccak128.heap.h
  | .treeQuotient 0 => keccak128.heap.h
  | .treeQuotient _ => 0
  | .constraintQuotient c => (chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1)).getD c 0
  | .leafQuotient i c => (chunks (leafDegC parts (keccak128.heap.blocks.getD i default) + 1)).getD c 0
  | _ => 0

/-- **The setup's columns' variables.** -/
def setupVarsK : Column → ℕ
  | .bytecodeTuple => keccak128.logBytecode + 4
  | .address => keccak128.logMemory
  | _ => 0

/-- A column's variables in any of π1-rec3's layouts. -/
def colVarsK (parts : List TablePart) (col : Column) : ℕ :=
  max (c1VarsK col) (max (c2VarsK parts col) (setupVarsK col))

/-- **`C2`'s entries** (`c2UniK` of the heap's leaf columns): on `C2`, at `c2VarsK`. -/
theorem c2Uni_entryK (activeE : List E) (partsE : List TablePart) (weightsE : Array E)
    (betaE hvE cvE mplE mpsE bplE bpsE : E) (wE : List E) (col : Column) (v : ℕ) (e : Bool)
    (h : (col, v, e) ∈ c2UniK (UniStatement.heapRelations keccak128 activeE partsE weightsE betaE hvE cvE mplE mpsE
      bplE bpsE wE (chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1))).2) :
    col.commitment = .c2 ∧ v = c2VarsK partsE col := by
  rw [heapRelations_sndC] at h
  unfold c2UniK at h
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map, List.mem_flatMap,
    Prod.mk.injEq] at h
  rcases h with ((⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩) | ⟨x, hx, rfl, rfl, -⟩) | ⟨⟨blk, idx⟩, hx, hm⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, (UniSound.Ids.Eval.mem_zip_range_iff _ 0 x hx).2.symm⟩
  · have hget := (UniSound.Ids.Eval.mem_zip_range_iff _ default _ hx).2
    dsimp only at hget hm
    unfold leafColsC chunkColsC at hm
    cases hl : blk.leaves
    case unused => simp [hl] at hm
    all_goals
      simp only [hl] at hm
      rw [Array.toList_map, List.toList_toArray] at hm
      obtain ⟨⟨ee, ch⟩, hy, hq⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, -⟩ := hq
      refine ⟨rfl, ?_⟩
      show _ = (chunks (leafDegC partsE (keccak128.heap.blocks.getD idx default) + 1)).getD ch 0
      rw [hget, leafDegC, hl]
      exact (UniSound.Ids.Eval.mem_zip_range_iff _ 0 _ hy).2.symm

/-- **A limb's variables**: at most its column's, and `q_flock`'s `26`. -/
theorem limb_varsK {c2 : List (Column × ℕ × Bool)} {parts : List TablePart}
    (hc2 : ∀ col v e, (col, v, e) ∈ c2 → col.commitment = .c2 ∧ v = c2VarsK parts col) (c : Commitment)
    (col : Column) (b : ℕ × ℕ × ℕ) (hb : b ∈ (layoutAt (UniKeccak.layoutsK keccak128 c2) c).limbs col) :
    b.2.1 ≤ colVarsK parts col ∧ (col = .qflock → b.2.1 = 26) := by
  cases c
  · change b ∈ (StackLayout.new (c1ColsK)).limbs col at hb
    obtain ⟨-, e, he⟩ := limbs_new_memC _ col b hb
    rw [c1ColsK_eq] at he
    obtain ⟨c, _, hc⟩ := List.mem_map.mp he
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, h2, -⟩ := hc
    refine ⟨by rw [← h2]; exact le_max_left _ _, fun h ↦ ?_⟩
    subst h
    rw [← h2]
    decide
  · change b ∈ (StackLayout.new c2).limbs col at hb
    obtain ⟨-, e, he⟩ := limbs_new_memC _ col b hb
    obtain ⟨hcm, hv⟩ := hc2 _ _ _ he
    refine ⟨by rw [hv]; exact (le_max_left _ _).trans (le_max_right _ _), fun h ↦ ?_⟩
    subst h
    cases hcm
  · change b ∈ (StackLayout.new (UniSound.Ids.setupCols keccak128)).limbs col at hb
    obtain ⟨-, e, he⟩ := limbs_new_memC _ col b hb
    simp only [UniSound.Ids.setupCols, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at he
    rcases he with ⟨rfl, h, -⟩ | ⟨rfl, h, -⟩
    · exact ⟨by rw [h]; exact (le_max_right _ _).trans (le_max_right _ _), fun h' ↦ by cases h'⟩
    · exact ⟨by rw [h]; exact (le_max_right _ _).trans (le_max_right _ _), fun h' ↦ by cases h'⟩

/-- **Every layout is `LayoutOK`.** -/
theorem layoutsOKK {c2 : List (Column × ℕ × Bool)} {parts : List TablePart}
    (hc2 : ∀ col v e, (col, v, e) ∈ c2 → col.commitment = .c2 ∧ v = c2VarsK parts col) (c : Commitment) :
    LayoutOK (layoutAt (UniKeccak.layoutsK keccak128 c2) c) := by
  cases c
  · show LayoutOK (StackLayout.new (c1ColsK))
    refine layoutOK_newC (c1VarsK) fun col v e h ↦ ?_
    rw [c1ColsK_eq] at h
    obtain ⟨c, _, hc⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, -⟩ := hc
    rfl
  · exact layoutOK_newC (c2VarsK parts) fun col v e h ↦ (hc2 col v e h).2
  · show LayoutOK (StackLayout.new (UniSound.Ids.setupCols keccak128))
    refine layoutOK_newC setupVarsK fun col v e h ↦ ?_
    simp only [UniSound.Ids.setupCols, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> rfl

/-! ## The terms' facts -/

/-- **A term's kind at π1-rec3's layouts**: plain, its column's variables at most its point's; a slot at `y`; or the
ring-switch term on `q_flock` at Flock's point. -/
def TermFactK (parts : List TablePart) (y fp : List E) (tm : Term) : Prop :=
  (tm.twist = 0 ∧ (∀ j, tm.column ≠ .qflockSlot j) ∧ colVarsK parts tm.column ≤ tm.point.length) ∨
  (tm.twist = 0 ∧ (∃ j, tm.column = .qflockSlot j) ∧ tm.point = y) ∨
  (tm.twist = ringTwist ∧ tm.column = .qflock ∧ tm.point = fp)

/-- **A relation's facts**: its terms on one commitment, each with its kind and its point. -/
def RelFactK (parts : List TablePart) (wE y fp : List E) (r : Relation) : Prop :=
  (∃ c, ∀ tm ∈ r.terms, tm.column.commitment = c) ∧ ∀ tm ∈ r.terms, TermFactK parts y fp tm ∧ PointFact wE y fp tm

theorem termKind_ofK {c2 : List (Column × ℕ × Bool)} {parts : List TablePart}
    (hc2 : ∀ col v e, (col, v, e) ∈ c2 → col.commitment = .c2 ∧ v = c2VarsK parts col) (c : Commitment)
    {y fp : List E} (hy : y.length = 15) (hfp : fp.length = 26) {tm : Term} (h : TermFactK parts y fp tm) :
    TermKindK (layoutAt (UniKeccak.layoutsK keccak128 c2) c) tm.column tm.point tm.twist := by
  rcases h with ⟨htw, hns, hle⟩ | ⟨htw, hs, hpt⟩ | ⟨htw, hq, hpt⟩
  · exact Or.inl ⟨htw, hns, fun b hb ↦ (limb_varsK hc2 c _ b hb).1.trans hle⟩
  · refine Or.inr (Or.inl ⟨htw, hs, fun b hb ↦ ?_⟩)
    have := (limb_varsK hc2 c _ b hb).2 rfl
    rw [hpt, hy]
    omega
  · refine Or.inr (Or.inr ⟨htw, fun j h ↦ (by rw [hq] at h; cases h), fun b hb ↦ ?_⟩)
    rw [hq] at hb
    have := (limb_varsK hc2 c _ b hb).2 rfl
    rw [hpt, hfp]
    omega

/-- **The tail's conditions from the relations' facts**, and no prefix of the digits or Flock's point extending `y`. -/
theorem tailOK_ofK {rels : List Relation} {c2 : List (Column × ℕ × Bool)} {parts : List TablePart} {wE y fp : List E}
    (hc2 : ∀ col v e, (col, v, e) ∈ c2 → col.commitment = .c2 ∧ v = c2VarsK parts col) (hy : y.length = 15)
    (hfp : fp.length = 26) (hR : ∀ r ∈ rels, RelFactK parts wE y fp r)
    (hw : ∀ k, y.length < (wE.take k).length → (wE.take k).take y.length ≠ y)
    (hf : fp.take y.length ≠ y) : TailOKK rels c2 := by
  intro c _
  refine ⟨layoutsOKK hc2 c, fun r hr tm htm ↦ ?_, fun r hr tm htm hs r' hr' tm' htm' hlt heq ↦ ?_⟩
  · exact termKind_ofK hc2 c hy hfp ((hR r (List.mem_filter.mp hr).1).2 tm htm).1
  · obtain ⟨hr1, hrc⟩ := List.mem_filter.mp hr
    obtain ⟨hr1', hrc'⟩ := List.mem_filter.mp hr'
    rw [beq_iff_eq] at hrc hrc'
    obtain ⟨⟨c0, hc0⟩, hfacts⟩ := hR r hr1
    obtain ⟨⟨c0', hc0'⟩, hfacts'⟩ := hR r' hr1'
    obtain ⟨j, hj⟩ := hs
    have hpt : tm.point = y := by
      rcases (hfacts tm htm).1 with ⟨-, hns, -⟩ | ⟨-, -, hpt⟩ | ⟨-, hq, -⟩
      · exact absurd hj (hns j)
      · exact hpt
      · rw [hq] at hj; cases hj
    have hc1 : c0 = .c1 := by rw [← hc0 tm htm, hj]; rfl
    have hc' : c0' = .c1 := by rw [← relCommitC hc0' htm', hrc', ← hrc, relCommitC hc0 htm, hc1]
    rw [hpt] at hlt heq
    rcases (hfacts' tm' htm').2 (by rw [hc0' tm' htm', hc']) with ⟨k, hk⟩ | hk | hk
    · rw [hk] at hlt heq
      exact hw k hlt heq
    · rw [hk] at hlt
      exact lt_irrefl _ hlt
    · rw [hk] at heq
      exact hf heq

/-! ## π1-rec3's numbers -/

theorem heights_leK2 (o : ℕ) : keccak128.heights.getD o 0 ≤ 16 := by
  rw [keccak128_eq]
  rcases o with _ | _ | _ | _ | _ | _ | o <;> simp

theorem logMemory_eqK : keccak128.logMemory = 20 := by rw [keccak128_eq]

theorem logBytecode_eqK : keccak128.logBytecode = 18 := by rw [keccak128_eq]

theorem wLen_eqK : wLenK = 26 := by
  unfold wLenK
  have h1 := heap_keccak128.1
  have h2 : keccak128.constraintVars = 20 := by rw [keccak128_eq]; decide
  omega

theorem tdegK : ∀ t ∈ tablesKeccak, (tableDegrees t).1 ≤ 55 ∧ (tableDegrees t).2 ≤ 55 := by decide +kernel

theorem blocks_rK : ∀ b ∈ keccak128.heap.blocks, b.r ≤ 20 := by
  intro b hb
  have hm : UniSound.Ids.Block.toTuple b ∈ heapBlocksK := heap_keccak128.2 ▸ List.mem_map_of_mem hb
  have key : ∀ x ∈ heapBlocksK, x.2.1 ≤ 20 := by decide
  exact key _ hm

theorem constraintDegree_ltK : UniKeccak.Shape.constraintDegreeK keccak128 + 1 < 2 ^ 27 := by
  rw [keccak128_eq]
  decide +kernel

theorem partDeg_leK {partsE : List TablePart} (hparts : ∀ p ∈ partsE, PartDegK p) (t : ℕ) :
    max (partsE.getD t default).pullDegree (partsE.getD t default).pushDegree ≤ 55 := by
  rcases Nat.lt_or_ge t partsE.length with h | h
  · obtain ⟨t', ht', h1, h2⟩ := hparts (partsE.getD t default)
      (by rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
    rw [h1, h2]
    have := tdegK t' ht'
    omega
  · rw [List.getD_eq_default _ _ h]
    show max 0 0 ≤ 55
    omega

/-- **A leaf quotient's chunks** are fewer than `2^27` coefficients' (so each at most `26` variables). -/
theorem leafDeg_ltK {partsE : List TablePart} (hparts : ∀ p ∈ partsE, PartDegK p) {blk : Block}
    (hb : blk ∈ keccak128.heap.blocks) : leafDegC partsE blk + 1 < 2 ^ 27 := by
  have hX : 2 ^ blk.r ≤ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) (blocks_rK blk hb)
  have e21 : (2 : ℕ) ^ 20 = 1048576 := by norm_num
  have e28 : (2 : ℕ) ^ 27 = 134217728 := by norm_num
  rw [e21] at hX
  rw [e28]
  unfold leafDegC degree
  split
  · omega
  · generalize 2 ^ blk.r = X at hX ⊢
    omega
  · generalize 2 ^ blk.r = X at hX ⊢
    omega
  · rename_i t _
    have hm := Nat.mul_le_mul_right (2 ^ blk.r - 1) (partDeg_leK hparts t)
    generalize max (partsE.getD t default).pullDegree (partsE.getD t default).pushDegree * (2 ^ blk.r - 1) = P
      at hm ⊢
    generalize Shape.leastRows blk.r = L
    generalize 2 ^ blk.r = X at hX hm ⊢
    omega

/-! ## Columns' variables -/

theorem colVars_tableK (parts : List TablePart) (o i : ℕ) :
    colVarsK parts (.table o i) = keccak128.heights.getD o 0 := by
  show max (keccak128.heights.getD o 0) (max 0 0) = _
  omega

theorem colVars_inverseK (parts : List TablePart) (o : ℕ) :
    colVarsK parts (.inverse o) = keccak128.heights.getD o 0 := by
  show max (keccak128.heights.getD o 0) (max 0 0) = _
  omega

theorem colVars_memoryK (parts : List TablePart) (k : ℕ) : colVarsK parts (.memory k) = keccak128.logMemory := by
  show max keccak128.logMemory (max 0 0) = _
  omega

theorem colVars_bytecodeFinalK (parts : List TablePart) :
    colVarsK parts .bytecodeFinal = keccak128.logBytecode := by
  show max keccak128.logBytecode (max 0 0) = _
  omega

theorem colVars_addressK (parts : List TablePart) : colVarsK parts .address = keccak128.logMemory := by
  show max 0 (max 0 keccak128.logMemory) = _
  omega

theorem colVars_bytecodeTupleK (parts : List TablePart) :
    colVarsK parts .bytecodeTuple = keccak128.logBytecode + 4 := by
  show max 0 (max 0 (keccak128.logBytecode + 4)) = _
  omega

theorem colVars_heapK (parts : List TablePart) : colVarsK parts .heap = keccak128.heap.h := by
  show max 0 (max keccak128.heap.h 0) = _
  omega

theorem colVars_tq0K (parts : List TablePart) : colVarsK parts (.treeQuotient 0) = keccak128.heap.h := by
  show max 0 (max keccak128.heap.h 0) = _
  omega

theorem colVars_tq1K (parts : List TablePart) : colVarsK parts (.treeQuotient 1) = 0 := rfl

theorem colVars_cqK (parts : List TablePart) (c : ℕ) :
    colVarsK parts (.constraintQuotient c) = (chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1)).getD c 0 := by
  show max 0 (max ((chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1)).getD c 0) 0) = _
  omega

theorem colVars_leafK (parts : List TablePart) (i c : ℕ) :
    colVarsK parts (.leafQuotient i c) =
      (chunks (leafDegC parts (keccak128.heap.blocks.getD i default) + 1)).getD c 0 := by
  show max 0 (max ((chunks (leafDegC parts (keccak128.heap.blocks.getD i default) + 1)).getD c 0) 0) = _
  omega

/-! ## The constraint relation's terms -/

/-- `y(t)`, the coordinates of `t` at `SHA3`'s height. -/
abbrev yK (tE : E) : List E := coordinatesAt tE (coordinateFunctionals (keccak128.heights.getD opSha3 0))

/-- **A constraint term**: untwisted; a table's column or its inverse at its height's prefix of `w`, the memory's at
`w[..lm]`, or a slot at `y`. -/
def CrTmK (w y : List E) (tm : Term) : Prop :=
  tm.twist = 0 ∧ ((∃ o c, tm.column = .table o c ∧ tm.point = w.take (keccak128.heights.getD o 0)) ∨
    (∃ o, tm.column = .inverse o ∧ tm.point = w.take (keccak128.heights.getD o 0)) ∨
    (∃ k, tm.column = .memory k ∧ tm.point = w.take keccak128.logMemory) ∨
    (∃ j, tm.column = .qflockSlot j ∧ tm.point = y))

theorem copyFold_CrK (o : ℕ) (columns : List String) (w y : List E) (lift gamma : E) :
    ∀ (l : List ℕ) (s : E × Array Term × E),
      ∀ tm ∈ (l.foldl (copyStepK o (keccak128.heights.getD o 0) columns w y lift gamma) s).2.1.toList,
        tm ∈ s.2.1.toList ∨ CrTmK w y tm
  | [], _, _, h => Or.inl h
  | c :: l, s, tm, h => by
    rw [List.foldl_cons] at h
    rcases copyFold_CrK o columns w y lift gamma l _ tm h with h1 | h1
    · unfold copyStepK at h1
      split at h1
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h1
        rcases h1 with (h1 | rfl) | rfl
        · exact Or.inl h1
        · exact Or.inr ⟨rfl, Or.inl ⟨o, c, rfl, rfl⟩⟩
        · exact Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr ⟨_, rfl, rfl⟩))⟩
      · exact Or.inl h1
    · exact Or.inr h1

theorem crStep_CrK (gamma t : E) (w : List E) (s : E × Array Term × E × ℕ) (x : Table × TablePart) :
    ∀ tm ∈ (crStepK keccak128 gamma t w s x).2.1.toList, tm ∈ s.2.1.toList ∨ CrTmK w (yK t) tm := by
  intro tm htm
  unfold crStepK at htm
  dsimp only at htm
  by_cases hj : x.1.opcode = opJump
  · have hb : ¬ x.1.opcode = opSha3 := by rw [hj]; decide
    simp only [ite_eq_left hj, ite_eq_right hb, Array.toList_push, List.mem_append, List.mem_singleton] at htm
    rcases htm with (h | rfl) | rfl
    · exact Or.inl h
    · exact Or.inr ⟨rfl, Or.inl ⟨_, _, rfl, rfl⟩⟩
    · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨_, rfl, rfl⟩)⟩
  · by_cases hb : x.1.opcode = opSha3
    · simp only [ite_eq_right hj, ite_eq_left hb] at htm
      rcases copyFold_CrK _ _ _ _ _ _ _ _ tm htm with h | h
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · exact Or.inl h
        · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨_, rfl, rfl⟩)⟩
      · rw [hb] at h
        exact Or.inr h
    · simp only [ite_eq_right hj, ite_eq_right hb, Array.toList_push, List.mem_append, List.mem_singleton] at htm
      rcases htm with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨_, rfl, rfl⟩)⟩

theorem crFold_CrK (gamma t : E) (w : List E) : ∀ (L : List (Table × TablePart)) (s : E × Array Term × E × ℕ),
    ∀ tm ∈ (L.foldl (crStepK keccak128 gamma t w) s).2.1.toList,
      tm ∈ s.2.1.toList ∨ CrTmK w (yK t) tm
  | [], _, _, h => Or.inl h
  | x :: L, s, tm, h => by
    rw [List.foldl_cons] at h
    rcases crFold_CrK gamma t w L _ tm h with h1 | h1
    · exact crStep_CrK gamma t w s x tm h1
    · exact Or.inr h1

theorem lineFold_CrK (gamma t : E) (w y : List E) : ∀ (l : List ((E × E) × ℕ)) (s : E × Array Term × E),
    ∀ tm ∈ (l.foldl (UniSound.Ids.Eval.lineStep keccak128 gamma t w) s).2.1.toList,
      tm ∈ s.2.1.toList ∨ CrTmK w y tm
  | [], _, _, h => Or.inl h
  | x :: l, s, tm, h => by
    rw [List.foldl_cons] at h
    rcases lineFold_CrK gamma t w y l _ tm h with h1 | h1
    · simp only [UniSound.Ids.Eval.lineStep, Array.toList_push, List.mem_append, List.mem_singleton] at h1
      rcases h1 with h1 | rfl
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))⟩
    · exact Or.inr h1

theorem crOf_CrK (parts : List TablePart) (pw : List E) (gamma t cv : E) (w : List E) :
    ∀ tm ∈ (crOfK keccak128 parts pw gamma t cv w).1.terms, CrTmK w (yK t) tm := by
  intro tm htm
  unfold crOfK at htm
  dsimp only at htm
  rcases lineFold_CrK gamma t w (yK t) _ _ tm htm with h | h
  · rcases crFold_CrK gamma t w _ _ tm h with h' | h'
    · simp at h'
    · exact h'
  · exact h

/-! ## The relations' facts -/

theorem relFact_singleK {parts : List TablePart} {wE y fp : List E} {tm : Term} {v : E}
    (h1 : TermFactK parts y fp tm) (h2 : PointFact wE y fp tm) : RelFactK parts wE y fp ⟨[tm], v⟩ :=
  ⟨⟨tm.column.commitment, fun t ht ↦ by rw [List.mem_singleton.mp ht]⟩,
    fun t ht ↦ by rw [List.mem_singleton.mp ht]; exact ⟨h1, h2⟩⟩

theorem tf_takeK {parts : List TablePart} {y fp wE : List E} (hwl : wE.length = 26) {col : Column} {k : ℕ} {c : E}
    (hns : ∀ j, col ≠ .qflockSlot j) (hle : colVarsK parts col ≤ k) (hk : k ≤ 26) :
    TermFactK parts y fp (term col (wE.take k) c) :=
  Or.inl ⟨rfl, hns, by show colVarsK parts col ≤ (wE.take k).length; rw [List.length_take, hwl]; omega⟩

theorem tabRels_factK {outs : List (TablePart × List Relation)} {wE : List E} (hwl : wE.length = 26)
    (hTS : List.Forall₂ (fun t o ↦ tableShapeK t wE o) tablesKeccak outs) (parts : List TablePart) (y fp : List E) :
    ∀ r ∈ (tabRels outs).toList, RelFactK parts wE y fp r := by
  intro r hr
  unfold tabRels at hr
  rw [foldl_append_toListC (fun o : TablePart × List Relation ↦ o.2.toArray)] at hr
  simp only [List.nil_append, List.mem_flatMap] at hr
  obtain ⟨o, ho, hro⟩ := hr
  obtain ⟨t, -, hsh⟩ := forall₂_leftOfC hTS ho
  refine ⟨⟨.c1, fun tm htm ↦ ?_⟩, fun tm htm ↦ ?_⟩
  · obtain ⟨⟨i, hi⟩, -, -⟩ := hsh r hro tm htm
    rw [hi]
    rfl
  · obtain ⟨⟨i, hi⟩, hpt, htw⟩ := hsh r hro tm htm
    refine ⟨Or.inl ⟨htw, fun j h ↦ (by rw [hi] at h; cases h), ?_⟩, fun _ ↦ Or.inl ⟨_, hpt⟩⟩
    rw [hi, hpt, colVars_tableK, List.length_take, hwl]
    have := heights_leK2 t.opcode
    omega

theorem constraint_factK {wE : List E} (hwl : wE.length = 26) {tE : E} {constraint : Relation}
    (hCS : constraintShapeK wE tE constraint) (parts : List TablePart) (fp : List E) :
    RelFactK parts wE (yK tE) fp constraint := by
  obtain ⟨partsE, pwE, gammaE, cvE, rfl⟩ := hCS
  rw [constraintRelationK_eq]
  have hC := crOf_CrK partsE pwE gammaE tE cvE wE
  refine ⟨⟨.c1, fun tm htm ↦ ?_⟩, fun tm htm ↦ ?_⟩
  · obtain ⟨-, ⟨o, c, hc, -⟩ | ⟨o, hc, -⟩ | ⟨k, hc, -⟩ | ⟨j, hc, -⟩⟩ := hC tm htm <;> rw [hc] <;> rfl
  · obtain ⟨htw, ⟨o, c, hc, hp⟩ | ⟨o, hc, hp⟩ | ⟨k, hc, hp⟩ | ⟨j, hc, hp⟩⟩ := hC tm htm
    · refine ⟨Or.inl ⟨htw, fun j h ↦ (by rw [hc] at h; cases h), ?_⟩, fun _ ↦ Or.inl ⟨_, hp⟩⟩
      rw [hc, hp, colVars_tableK, List.length_take, hwl]
      have := heights_leK2 o
      omega
    · refine ⟨Or.inl ⟨htw, fun j h ↦ (by rw [hc] at h; cases h), ?_⟩, fun _ ↦ Or.inl ⟨_, hp⟩⟩
      rw [hc, hp, colVars_inverseK, List.length_take, hwl]
      have := heights_leK2 o
      omega
    · refine ⟨Or.inl ⟨htw, fun j h ↦ (by rw [hc] at h; cases h), ?_⟩, fun _ ↦ Or.inl ⟨_, hp⟩⟩
      rw [hc, hp, colVars_memoryK, List.length_take, hwl, logMemory_eqK]
      omega
    · exact ⟨Or.inr (Or.inl ⟨htw, ⟨j, hc⟩, hp⟩), fun _ ↦ Or.inr (Or.inl hp)⟩

/-- A leaf quotient's term: at its chunk's prefix of `w`, of its chunk's variables. -/
theorem leafTerm_factK {wE : List E} (hwl : wE.length = 26) {partsE : List TablePart}
    (hparts : ∀ p ∈ partsE, PartDegK p) {blk : Block} {idx : ℕ}
    (hx : (blk, idx) ∈ keccak128.heap.blocks.zip (List.range keccak128.heap.blocks.length)) {sizes : List ℕ}
    (hsz : sizes = chunks (leafDegC partsE blk + 1)) {sc : E} {tm : Term}
    (htm : tm ∈ quotientTerms (Column.leafQuotient idx) sizes wE sc) (y fp : List E) : TermFactK partsE y fp tm := by
  subst hsz
  rw [UniSound.Ids.Eval.quotientTerms_eq] at htm
  obtain ⟨c, hc, h1, h2, h3⟩ := UniSound.Ids.Eval.qTerms_mem _ wE _ 0 _ tm htm
  rw [Nat.zero_add] at h1
  have hmemc : (chunks (leafDegC partsE blk + 1)).getD c 0 ∈ chunks (leafDegC partsE blk + 1) := by
    rw [List.getD_eq_getElem _ _ hc]
    exact List.getElem_mem hc
  have hlt := UniSound.Ids.Eval.chunk_lt _ 27 (leafDeg_ltK hparts (List.of_mem_zip hx).1) _ hmemc
  have hget : keccak128.heap.blocks.getD idx default = blk := (UniSound.Ids.Eval.mem_zip_range_iff _ default _ hx).2
  refine Or.inl ⟨h3, fun j h ↦ (by rw [h1] at h; cases h), ?_⟩
  rw [h1, h2, colVars_leafK, hget, List.length_take, hwl]
  omega

theorem heap_factK {wE : List E} (hwl : wE.length = 26) (activeE : List E) (partsE : List TablePart)
    (weightsE : Array E) (betaE hvE cvE mplE mpsE bplE bpsE : E) (hparts : ∀ p ∈ partsE, PartDegK p) (y fp : List E) :
    ∀ r ∈ (UniStatement.heapRelations keccak128 activeE partsE weightsE betaE hvE cvE mplE mpsE bplE bpsE wE
      (chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1))).1, RelFactK partsE wE y fp r := by
  intro r hr
  have hc2 := UniSound.Ids.Eval.heap_terms keccak128 activeE partsE weightsE betaE hvE cvE mplE mpsE bplE bpsE wE _
    r hr
  refine ⟨⟨.c2, fun tm htm ↦ (hc2 tm htm).1⟩, fun tm htm ↦ ⟨?_, fun h ↦ by rw [(hc2 tm htm).1] at h; cases h⟩⟩
  have hh := heap_keccak128.1
  rw [UniSound.Ids.Eval.heapRelations_fst] at hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | hr) | rfl
  · simp only [Relation.equal, List.mem_singleton] at htm
    subst htm
    exact tf_takeK hwl (fun j h ↦ by cases h) (by rw [colVars_heapK]) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at htm
    rcases htm with rfl | rfl | rfl | rfl
    · refine Or.inl ⟨rfl, fun j h ↦ (by cases h), ?_⟩
      show colVarsK partsE .heap ≤ ((wE.drop 1).take keccak128.heap.h).length
      rw [colVars_heapK, List.length_take, List.length_drop, hwl]
      omega
    · refine Or.inl ⟨rfl, fun j h ↦ (by cases h), ?_⟩
      show colVarsK partsE .heap ≤ ((wE.take keccak128.heap.h).modify 0 (· + 1)).length
      rw [colVars_heapK, List.length_modify, List.length_take, hwl]
      omega
    · exact tf_takeK hwl (fun j h ↦ by cases h) (by rw [colVars_tq0K]) (by omega)
    · refine Or.inl ⟨rfl, fun j h ↦ (by cases h), ?_⟩
      show colVarsK partsE (.treeQuotient 1) ≤ ([] : List E).length
      rw [colVars_tq1K]
      exact Nat.zero_le _
  · simp only [List.mem_singleton] at htm
    subst htm
    refine Or.inl ⟨rfl, fun j h ↦ (by cases h), ?_⟩
    show colVarsK partsE .heap ≤ ((List.range keccak128.heap.h).map fun l ↦ if l = 0 then (1 : E) else 0).length
    rw [colVars_heapK, List.length_map, List.length_range]
  · obtain ⟨⟨blk, idx⟩, hx, rfl⟩ := List.mem_map.mp hr
    have hmixed : ∀ c : E, TermFactK partsE y fp (term .heap ((List.range keccak128.heap.h).map fun l ↦
        if l < blk.r then wE.getD l 0 + pointE (blk.position >>> l) else pointE (blk.position >>> l)) c) :=
      fun c ↦ Or.inl ⟨rfl, fun j h ↦ (by cases h), by
        show colVarsK partsE .heap ≤ ((List.range keccak128.heap.h).map _).length
        rw [colVars_heapK, List.length_map, List.length_range]⟩
    unfold UniSound.Ids.Eval.blockRel at htm
    dsimp only at htm
    cases hl : blk.leaves <;> simp only [hl, List.mem_append, List.mem_singleton] at htm
    all_goals first
      | (subst htm; exact hmixed _)
      | (rcases htm with rfl | htm
         · exact hmixed _
         · exact leafTerm_factK hwl hparts hx (by simp only [leafDegC, hl]) htm y fp)
  · rw [UniSound.Ids.Eval.quotientTerms_eq] at htm
    obtain ⟨c, hc, h1, h2, h3⟩ := UniSound.Ids.Eval.qTerms_mem _ wE _ 0 _ tm htm
    rw [Nat.zero_add] at h1
    have hmemc : (chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1)).getD c 0 ∈ chunks (UniKeccak.Shape.constraintDegreeK keccak128 + 1) := by
      rw [List.getD_eq_getElem _ _ hc]
      exact List.getElem_mem hc
    have hlt := UniSound.Ids.Eval.chunk_lt _ 27 constraintDegree_ltK _ hmemc
    refine Or.inl ⟨h3, fun j h ↦ (by rw [h1] at h; cases h), ?_⟩
    rw [h1, h2, colVars_cqK, List.length_take, hwl]
    omega

/-! ## Off the hazard, no `C1` point extends `y(t)` -/

theorem digits_getD0K (tE : E) : (digits tE wLenK).getD 0 0 = tE := by
  rw [digits_eq, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range, wLen_eqK]; omega),
    List.getElem_map, List.getElem_range]
  rfl

/-- **Off the hazard, `y(t)`'s first coordinate is neither `t` nor `p_0`.** -/
theorem y0_neK {tE p0 : E} (hhaz : ¬ HazardK p0 tE) : (yK tE).getD 0 0 ≠ tE ∧ (yK tE).getD 0 0 ≠ p0 :=
  y0_neGenC keccak128 (by decide) hhaz

/-! ## `Compose`'s interface: the shapes -/

/-- **`ShapeSpecK`**: off the hazard, reduce's relations satisfy the tail's conditions (`TailOKK`), from the parts'
shapes. -/
theorem shapeSpecK : ShapeSpecK tableShapeK constraintShapeK heapShapeK TailOKK := by
  intro tE alphasE betaE flockPt target outs mfc addr mpl bfc bpl constraint heapOut hα hfp hTS hCS hHS hhaz
  obtain ⟨activeE, partsE, weightsE, betaH, hvE, cvE, mplE, mpsE, bplE, bpsE, -, -, hparts, -, rfl⟩ := hHS
  have hwl : (digits tE wLenK).length = 26 := by rw [digits_lengthC, wLen_eqK]
  have hy : (yK tE).length = 15 := by
    rw [UniSound.Ids.Eval.coordinatesAt_length, UniSound.Ids.Eval.coordinateFunctionals_size,
      show keccak128.heights.getD opSha3 0 = 15 by decide]
  obtain ⟨hne1, hne2⟩ := y0_neK hhaz
  have hlm := logMemory_eqK
  have hlb := logBytecode_eqK
  refine tailOK_ofK (parts := partsE) (wE := digits tE wLenK) (y := yK tE) (fp := flockPt)
    (c2Uni_entryK activeE partsE weightsE betaH hvE cvE mplE mpsE bplE bpsE (digits tE wLenK)) hy hfp ?_ ?_ ?_
  · intro r hr
    unfold relsUniK at hr
    simp only [Array.toList_push, Array.toList_append, List.mem_append, List.mem_singleton] at hr
    rcases hr with ((((((((hr | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | hr) | rfl)
    · exact tabRels_factK hwl hTS partsE _ _ r hr
    · exact relFact_singleK (tf_takeK hwl (fun j h ↦ by cases h) (by rw [colVars_memoryK]) (by omega))
        (fun _ ↦ Or.inl ⟨_, rfl⟩)
    · exact relFact_singleK (tf_takeK hwl (fun j h ↦ by cases h) (by rw [colVars_addressK]) (by omega))
        (fun h ↦ by cases h)
    · refine ⟨⟨.c1, fun tm htm ↦ ?_⟩, fun tm htm ↦ ?_⟩
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp htm
        rfl
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp htm
        exact ⟨tf_takeK hwl (fun j h ↦ by cases h) (by rw [colVars_memoryK]) (by omega), fun _ ↦ Or.inl ⟨_, rfl⟩⟩
    · exact relFact_singleK (tf_takeK hwl (fun j h ↦ by cases h) (by rw [colVars_bytecodeFinalK]) (by omega))
        (fun _ ↦ Or.inl ⟨_, rfl⟩)
    · refine relFact_singleK (Or.inl ⟨rfl, fun j h ↦ (by cases h), ?_⟩) (fun h ↦ by cases h)
      show colVarsK partsE .bytecodeTuple ≤ (alphasE ++ (digits tE wLenK).take keccak128.logBytecode).length
      rw [colVars_bytecodeTupleK, List.length_append, List.length_take, hwl, hα]
      omega
    · exact constraint_factK hwl hCS partsE flockPt
    · exact heap_factK hwl activeE partsE weightsE betaH hvE cvE mplE mpsE bplE bpsE hparts _ _ r hr
    · exact relFact_singleK (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (fun _ ↦ Or.inr (Or.inr rfl))
  · intro k hlt heq
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hlt
      · exact hk
    have h0 := congrArg (fun l ↦ l.getD 0 0) heq
    rw [take_getD0C _ (yK tE).length (by omega), take_getD0C (digits tE wLenK) k hk, digits_getD0K] at h0
    exact hne1 h0.symm
  · intro heq
    have h0 := congrArg (fun l ↦ l.getD 0 0) heq
    rw [take_getD0C flockPt (yK tE).length (by omega)] at h0
    apply hne2
    rw [← h0]
    cases flockPt <;> rfl


end RecGraphKeccak.Sim
