-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The proofs are `UniSound/Ids/Eval.lean`'s (`wP_eval`,
-- `blockP_eval`, `diffsEval`, `diffsEvalP_of_heapGood`) on the Keccak identity model.
import UniKeccakSound.IdsEval.Ev

/-!
# `DiffsEvalK`: the Keccak relations at `t`, all zero, give every identity at `t`

**`diffsEvalK_of_heapGood`**: for a deployment whose heap's blocks fill the leaves (`HeapGood`), where every
relation's difference vanishes (`diffsK`) and round `0` has at least four challenges, every identity polynomial of
`polysK` vanishes at `t`: the tree (`treePK_eval`), the root (`rootPK_eval`), the constraint quotient's with the
Keccak lanes' copies (`wPK_eval`, trivially at `Z_bad`'s roots), each heap block's leaf on the Keccak tables
(`blockPK_eval`). The tables' facts (`tablesLinK`), the bytecode inside the heap (`UniSound.Ids.Eval.lbFits`) and
the quotients' chunks inside the digits (`chunksFitK`) are proved.

**`DiffsEvalK` as stated** (`Ids/Build.lean`) quantifies over round `0`'s challenges of every length; for fewer than
four the relations (`relsAtK`: `α = ch.take 4`, shorter) and the identities (`polysK`: `α = alphasOf ch`, padded with
zeros) read the bytecode's tuples at different points, and the implication does not follow. **`DiffsEvalK4`** is
`DiffsEvalK` for `4 ≤ ch.length` (every transcript the PIOP reads has six challenges in round `0`), proved here.
-/

namespace UniKeccakSound.IdsEval

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.Eval UniKeccak UniKeccakSound.Ids Finset
  Polynomial

/-! ## The quotients at `t` -/

theorem quotPK_cons (S : Shape) (c2 : Stk) (column : ℕ → Column) (e : ℕ) (rest : List ℕ) :
    quotPK S c2 column (e :: rest) =
      c2PK S c2 (column 0) digitP + digitP e * quotPK S c2 (fun c ↦ column (c + 1)) rest := by
  unfold quotPK
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
    List.range_zero, List.map_nil, List.prod_nil, mul_one, ← List.sum_map_mul_left]
  refine congrArg (fun z ↦ c2PK S c2 (column 0) digitP + z) ?_
  refine congrArg List.sum (List.map_congr_left fun c _ ↦ ?_)
  show c2PK S c2 (column (c + 1)) digitP *
      ((List.range (c + 1)).map fun c' ↦ digitP ((e :: rest).getD c' 0)).prod =
    digitP e * (c2PK S c2 (column (c + 1)) digitP * ((List.range c).map fun c' ↦ digitP (rest.getD c' 0)).prod)
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  have h : ((fun c' ↦ digitP ((e :: rest).getD c' 0)) ∘ Nat.succ) = fun c' ↦ digitP (rest.getD c' 0) :=
    funext fun c' ↦ by simp
  rw [h, List.getD_cons_zero]
  ring

/-- **A quotient's terms at `t`** on the Keccak `C2` (`qTerms_val` for `c2PK`, `quotPK`). -/
theorem qTerms_val' (S : Shape) (c2 : Stk) (ev : Column → List E → E) (w : List E) (t : E) :
    ∀ (column : ℕ → Column) (sizes : List ℕ) (sc : E),
      (∀ c < sizes.length, ev (column c) (w.take (sizes.getD c 0)) = (c2PK S c2 (column c) digitP).eval t) →
      (∀ c < sizes.length, w.getD (sizes.getD c 0) 0 = (digitP (sizes.getD c 0)).eval t) →
      ((qTerms column w sizes 0 sc).map fun tm ↦ tm.coefficient * ev tm.column tm.point).sum =
        sc * (quotPK S c2 column sizes).eval t
  | _, [], _, _, _ => by simp [qTerms, quotPK]
  | column, e :: rest, sc, hev, hw => by
    simp only [qTerms, List.map_cons, List.sum_cons, term]
    rw [qTerms_shift, qTerms_val' S c2 ev w t (fun c ↦ column (c + 1)) rest (sc * w.getD e 0)
      (fun c hc ↦ by simpa using hev (c + 1) (by simp; omega))
      (fun c hc ↦ by simpa using hw (c + 1) (by simp; omega)), quotPK_cons]
    have h0 := hev 0 (by simp)
    have hw0 := hw 0 (by simp)
    simp only [List.getD_cons_zero] at h0 hw0
    rw [h0, hw0, Polynomial.eval_add, Polynomial.eval_mul]
    ring

section Ctx

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant} (Fl : KFlockSound F κ v)
  (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E) (vals : List E)

theorem tpK_length : tablesKeccak.length ≤ (tpK (inpK D Fl s ch fd t vals)).1.length := by
  show tablesKeccak.length ≤ (tablesPart _ _ _ _ tablesKeccak _).1.length
  rw [tablesPart_length]

/-- **The Keccak constraint quotient's identity at `t`.** -/
theorem wPK_eval (hC : ChunksFitK D.shape) (h2 : 1 ≤ D.shape.heights.getD opBlake2s 0)
    (hold : HoldAllK D Fl s c1 ch fd c2 t vals) :
    (wPK D.shape c1 c2 (publicWordsOf s.1.toList) (gammaOf ch) ((Fl.prog.out fd []).1.getD 0 0)).eval t = 0 := by
  unfold wPK
  rw [Polynomial.eval_mul]
  by_cases hz : (zBad D.shape ((Fl.prog.out fd []).1.getD 0 0)).eval t = 0
  · rw [hz, zero_mul]
  refine mul_eq_zero_of_right _ ?_
  have hplen := tpK_length D Fl s ch fd t vals
  have hdeg : (constraintK (inpK D Fl s ch fd t vals)).2 = UniKeccak.Shape.constraintDegreeK D.shape := by
    show (constraintRelationK _ _ _ _ _ _ _).2 = _
    rw [constraintRelationK_eq]
    exact crOfK_deg _ _ _ _ _ _ _ hplen
  -- The constraint quotient's value: its chunks at `t`.
  have mQ := mem_rels_heapK D Fl s ch fd t vals (by
    rw [heapK_fst]; exact List.mem_append_right _ (List.mem_singleton_self _))
  have hQ := hold _ mQ .c2 fun tm htm ↦ by
    rw [quotientTerms_eq] at htm
    obtain ⟨h1, h3⟩ := qTerms_c2 _ (fun _ ↦ rfl) _ _ 0 _ tm htm
    exact ⟨h3, h1⟩
  unfold RelHolds at hQ
  simp only [quotientTerms_eq] at hQ mQ
  rw [hdeg] at hQ mQ
  have hev : ∀ c < (chunks (UniKeccak.Shape.constraintDegreeK D.shape + 1)).length,
      evOfK D Fl s c1 ch fd c2 t vals (.constraintQuotient c)
        ((inpK D Fl s ch fd t vals).w.take ((chunks (UniKeccak.Shape.constraintDegreeK D.shape + 1)).getD c 0)) =
        (c2PK D.shape c2 (.constraintQuotient c) digitP).eval t := by
    intro c hc
    have he := hC.1 _ (getD_mem' (d := 0) hc)
    obtain ⟨tm, htm, hpt⟩ := qTerms_pt Column.constraintQuotient (inpK D Fl s ch fd t vals).w _ 0 1 c hc
    refine ev_c2K D Fl s c1 ch fd c2 t vals _ rfl _ digitP
      ⟨_, mQ, qrel_commitment _ (fun _ ↦ rfl) _ _ (List.ne_nil_of_length_pos (by omega)) _ _, tm, htm, hpt⟩
      (by rw [wtakeK_length D Fl s ch fd t vals _ he.le]; rfl) (fun l hl ↦ ?_)
    exact (wtakeK_getD D Fl s ch fd t vals _ he.le l hl).symm
  rw [qTerms_val' D.shape c2 _ _ t _ _ 1 hev
    (fun c hc ↦ wK_getD D Fl s ch fd t vals _ (hC.1 _ (getD_mem' (d := 0) hc))), one_mul] at hQ
  -- The constraint relation at `t`.
  have hyl : (yOfK D t).length = D.shape.heights.getD opBlake2s 0 := by
    rw [yOfK, coordinatesAt_length, coordinateFunctionals_size]
  have hok : ∀ x ∈ tablesKeccak.zip (tpK (inpK D Fl s ch fd t vals)).1,
      CrTableOkK D.shape c1 t (inpK D Fl s ch fd t vals).w (evOfK D Fl s c1 ch fd c2 t vals) x.1 x.2 := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
    have hi6 : i < 6 := by rw [List.length_zip] at hi; have := tablesKeccak_length; omega
    rw [← hxi, List.getElem_zip, ← List.getD_eq_getElem _ default, ← List.getD_eq_getElem _ default]
    obtain ⟨hpt, hsent, -⟩ := part_specK D Fl s c1 ch fd c2 t vals hold i hi6
    have hop := tablesKeccak_opcode i hi6
    refine ⟨?_, ?_, ?_, ?_, ?_, jumpSent _⟩
    · rw [hop]
      exact vanishingRatio_eval _ t _ _ fun j hj ↦ wK_getD D Fl s ch fd t vals j
        (by have := rW_lt_nDigitsK D.shape; omega)
    · rw [hop]
      intro c
      exact ev_c1K D Fl s c1 ch fd c2 t vals (.table i c) rfl (fun j h ↦ by cases h) _
        (height_lt_nDigitsK D i).le le_rfl hpt
    · rw [hop]
      exact ev_c1K D Fl s c1 ch fd c2 t vals (.inverse i) rfl (fun j h ↦ by cases h) _
        (height_lt_nDigitsK D i).le le_rfl hpt
    · intro hb c slot hc hs
      have hi5 : i = 5 := by rw [← hop, hb]; rfl
      subst hi5
      rw [hb]
      obtain ⟨tm, htm, hpt'⟩ := crOfK_slot D.shape (tpK (inpK D Fl s ch fd t vals)).1
        (inpK D Fl s ch fd t vals).publicWords (inpK D Fl s ch fd t vals).gamma t
        (cvK (inpK D Fl s ch fd t vals)) (inpK D Fl s ch fd t vals).w hplen c slot hc hs
      refine ev_slotK D Fl s c1 ch fd c2 t vals slot (yOfK D t) _ ⟨_, mem_rels_constraintK D Fl s ch fd t vals,
        ?_, tm, ?_, hpt'⟩ (y_selfK D Fl s ch fd t vals h2 hz) ?_ ?_ ?_
      · show (constraintRelationK _ _ _ _ _ _ _).1.commitment = _
        rw [constraintRelationK_eq]
        exact commitment_c1 fun tm' htm' ↦ (crOfK_terms _ _ _ _ _ _ _ tm' htm').2.1
      · show tm ∈ (constraintRelationK _ _ _ _ _ _ _).1.terms
        rw [constraintRelationK_eq]
        exact htm
      · intro b hb'
        obtain ⟨h1, h3⟩ := c1_limbsK D.shape .qflock b hb'
        refine ⟨?_, h3⟩
        rw [h1, hyl]
        simp only [c1VarsK]
        omega
      · rw [qvOf_c1K, hyl]
        omega
      · intro m hm
        rw [hyl] at hm
        rw [yOfK, coordinatesAt_getD _ _ _ (by rw [coordinateFunctionals_size]; exact hm)]
    · rw [hop]
      exact hsent
  have hmem : ∀ k < 3, evOfK D Fl s c1 ch fd c2 t vals (.memory k)
      ((inpK D Fl s ch fd t vals).w.take D.shape.logMemory) = (c1PK D.shape c1 (.memory k)).eval t := by
    intro k _
    refine ev_c1K D Fl s c1 ch fd c2 t vals (.memory k) rfl (fun j h ↦ by cases h) _ (lm_lt_nDigitsK D).le le_rfl
      ⟨_, mem_rels_memK D Fl s ch fd t vals (List.mem_cons_self ..), rfl, _, List.mem_singleton_self _, rfl⟩
  have mC := mem_rels_constraintK D Fl s ch fd t vals
  have hCr := hold _ mC .c1 fun tm htm ↦ by
    have := crOfK_terms _ _ _ _ _ _ _ tm (by rw [← constraintRelationK_eq]; exact htm)
    exact ⟨this.1, this.2.1⟩
  have hc := crOfK_holds D.shape c1 (tpK (inpK D Fl s ch fd t vals)).1 (inpK D Fl s ch fd t vals).publicWords
    (inpK D Fl s ch fd t vals).gamma t (cvK (inpK D Fl s ch fd t vals)) (inpK D Fl s ch fd t vals).w
    (evOfK D Fl s c1 ch fd c2 t vals) hplen hok hmem
    (vanishingRatio_eval _ t _ _ fun j hj ↦ wK_getD D Fl s ch fd t vals j
      (by have := rW_lt_nDigitsK D.shape; omega))
    (by rw [← constraintRelationK_eq]; exact hCr)
  rw [Polynomial.eval_add, eval_batched, Polynomial.eval_mul,
    ← wK_getD D Fl s ch fd t vals _ (by have := rW_lt_nDigitsK D.shape; omega)]
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  have e1 : (inpK D Fl s ch fd t vals).publicWords = publicWordsOf s.1.toList := rfl
  have e2 : (inpK D Fl s ch fd t vals).gamma = gammaOf ch := rfl
  rw [e1, e2] at hc
  linear_combination hc + (inpK D Fl s ch fd t vals).w.getD D.shape.constraintVars 0 * hQ -
    cvK (inpK D Fl s ch fd t vals) * (inpK D Fl s ch fd t vals).w.getD D.shape.constraintVars 0 * two

/-! ### The heap's blocks -/

/-- A block's leaf relation (`blockRel`) at the relations' input. -/
abbrev blkK (b : Block) (i : ℕ) : Relation :=
  blockRel D.shape (inpK D Fl s ch fd t vals).active (tpK (inpK D Fl s ch fd t vals)).1
    (mpullK (inpK D Fl s ch fd t vals)) (mpushK (inpK D Fl s ch fd t vals))
    (bpullK (inpK D Fl s ch fd t vals)) (bpushK (inpK D Fl s ch fd t vals)) (inpK D Fl s ch fd t vals).w (b, i)

theorem blockK_mem (b : Block) (i : ℕ)
    (hbi : (b, i) ∈ D.shape.heap.blocks.zip (List.range D.shape.heap.blocks.length)) :
    blkK D Fl s ch fd t vals b i ∈ (heapK (inpK D Fl s ch fd t vals)).1 := by
  rw [heapK_fst]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨(b, i), hbi, rfl⟩))

theorem blockK_holds (hold : HoldAllK D Fl s c1 ch fd c2 t vals) (b : Block) (i : ℕ)
    (hbi : (b, i) ∈ D.shape.heap.blocks.zip (List.range D.shape.heap.blocks.length)) :
    RelHolds (evOfK D Fl s c1 ch fd c2 t vals) (blkK D Fl s ch fd t vals b i) := by
  refine hold _ (mem_rels_heapK D Fl s ch fd t vals (blockK_mem D Fl s ch fd t vals b i hbi)) .c2 fun tm htm ↦ ?_
  obtain ⟨h1, h2⟩ := heap_terms _ _ _ _ _ _ _ _ _ _ _ _ _ _ (blockK_mem D Fl s ch fd t vals b i hbi) tm htm
  exact ⟨h2, h1⟩

/-- **A block's mixed point**: the heap's polynomial at the restriction's point. -/
theorem ev_mixedK (hH : HeapGood D.shape) (b : Block) (i : ℕ)
    (hbi : (b, i) ∈ D.shape.heap.blocks.zip (List.range D.shape.heap.blocks.length)) :
    evOfK D Fl s c1 ch fd c2 t vals .heap (mixedOf D.shape (inpK D Fl s ch fd t vals).w b) =
      (c2PK D.shape c2 .heap (mixP b)).eval t := by
  have hb := block_r_lt D.shape hH b (List.of_mem_zip hbi).1
  have hN := h_lt_nDigitsK D.shape
  obtain ⟨c, hc⟩ := blockRel_heap D.shape (inpK D Fl s ch fd t vals).active
    (tpK (inpK D Fl s ch fd t vals)).1 (mpullK (inpK D Fl s ch fd t vals))
    (mpushK (inpK D Fl s ch fd t vals)) (bpullK (inpK D Fl s ch fd t vals))
    (bpushK (inpK D Fl s ch fd t vals)) (inpK D Fl s ch fd t vals).w (b, i)
  refine ev_c2K D Fl s c1 ch fd c2 t vals .heap rfl _ (mixP b)
    ⟨_, mem_rels_heapK D Fl s ch fd t vals (blockK_mem D Fl s ch fd t vals b i hbi),
      blockRel_commitment _ _ _ _ _ _ _ _ _, _, hc, rfl⟩
    (by simp [mixedOf, c2VarsK]) (fun l hl ↦ ?_)
  change l < D.shape.heap.h at hl
  unfold mixedOf
  rw [getD_map_range _ hl]
  unfold mixP
  split_ifs with h
  · rw [Polynomial.eval_add, Polynomial.eval_C, wK_getD D Fl s ch fd t vals l (by omega)]
  · rw [Polynomial.eval_C]

/-- **A leaf quotient's chunks** at the digits: their polynomials at `t`. -/
theorem ev_leafQK (hC : ChunksFitK D.shape) (b : Block) (i : ℕ)
    (hbi : (b, i) ∈ D.shape.heap.blocks.zip (List.range D.shape.heap.blocks.length)) (d : ℕ)
    (hd : UniKeccak.Shape.leafDegreeK b = some d) (sc : E)
    (hsub : ∀ tm ∈ qTerms (Column.leafQuotient i) (inpK D Fl s ch fd t vals).w (chunks (d + 1)) 0 sc,
      tm ∈ (blkK D Fl s ch fd t vals b i).terms) :
    ∀ c < (chunks (d + 1)).length, evOfK D Fl s c1 ch fd c2 t vals (.leafQuotient i c)
        ((inpK D Fl s ch fd t vals).w.take ((chunks (d + 1)).getD c 0)) =
      (c2PK D.shape c2 (.leafQuotient i c) digitP).eval t := by
  intro c hc
  have hget : D.shape.heap.blocks.getD i default = b := (mem_zip_range_iff _ default _ hbi).2
  have he := hC.2 b (List.of_mem_zip hbi).1 d hd _ (getD_mem' (d := 0) hc)
  obtain ⟨tm, htm, hpt⟩ := qTerms_pt (Column.leafQuotient i) (inpK D Fl s ch fd t vals).w _ 0 sc c hc
  have hv : c2VarsK D.shape (.leafQuotient i c) = (chunks (d + 1)).getD c 0 := by
    simp only [c2VarsK, hget, hd]
  refine ev_c2K D Fl s c1 ch fd c2 t vals _ rfl _ digitP
    ⟨_, mem_rels_heapK D Fl s ch fd t vals (blockK_mem D Fl s ch fd t vals b i hbi),
      blockRel_commitment _ _ _ _ _ _ _ _ _, tm, hsub tm htm, hpt⟩
    (by rw [hv, wtakeK_length D Fl s ch fd t vals _ he.le]) (fun l hl ↦ ?_)
  rw [hv] at hl
  exact (wtakeK_getD D Fl s ch fd t vals _ he.le l hl).symm

/-- **The memory's values at `t`**: the final count and the pull fingerprint. -/
theorem mem_factsK (hold : HoldAllK D Fl s c1 ch fd c2 t vals) :
    mfcK (inpK D Fl s ch fd t vals) = (c1PK D.shape c1 (.memory 3)).eval t ∧
      mpullK (inpK D Fl s ch fd t vals) =
        (memPullPK D.shape c1 (setupStkK D) (inpK D Fl s ch fd t vals).weights
          (inpK D Fl s ch fd t vals).beta).eval t := by
  have hlm := lm_lt_nDigitsK D
  have m1 := mem_rels_memK D Fl s ch fd t vals (List.mem_cons_self ..)
  have m2 := mem_rels_memK D Fl s ch fd t vals (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have m3 := mem_rels_memK D Fl s ch fd t vals
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hs : (inpK D Fl s ch fd t vals).shape = D.shape := rfl
  rw [hs] at m1 m2 m3
  have hpt : IsPtK D Fl s ch fd t vals .c1 ((inpK D Fl s ch fd t vals).w.take D.shape.logMemory) :=
    ⟨_, m1, rfl, _, List.mem_singleton_self _, rfl⟩
  have h1 := holds_equal (hold _ m1 .c1 (by simp [Relation.equal, term, Column.commitment]))
  have h2 := holds_equal (hold _ m2 .setup (by simp [Relation.equal, term, Column.commitment]))
  have h3 := hold _ m3 .c1 fun tm htm ↦ by
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp htm
    exact ⟨rfl, rfl⟩
  have ek : ∀ k, evOfK D Fl s c1 ch fd c2 t vals (.memory k)
      ((inpK D Fl s ch fd t vals).w.take D.shape.logMemory) = (c1PK D.shape c1 (.memory k)).eval t := fun k ↦
    ev_c1K D Fl s c1 ch fd c2 t vals (.memory k) rfl (fun j h ↦ by cases h) _ hlm.le le_rfl hpt
  have ea := ev_setupK D Fl s c1 ch fd c2 t vals .address rfl
    ((inpK D Fl s ch fd t vals).w.take D.shape.logMemory) digitP ⟨_, m2, rfl, _, List.mem_singleton_self _, rfl⟩
    (fun b hb ↦ by rw [(setup_limbsK D.shape _ b hb).2.1 rfl, wtakeK_length D Fl s ch fd t vals _ hlm.le])
    (fun b hb l hl ↦ by
      rw [(setup_limbsK D.shape _ b hb).2.1 rfl] at hl
      rw [wtakeK_getD D Fl s ch fd t vals _ hlm.le l hl])
  rw [ek] at h1
  rw [ea] at h2
  refine ⟨h1.symm, ?_⟩
  unfold RelHolds at h3
  simp only [List.map_map, Function.comp_def, term, ek] at h3
  unfold memPullPK
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, eval_listSum, List.map_map,
    Function.comp_def]
  rw [h2, h1]
  rw [← add_eq_zero_iff']
  linear_combination h3

/-- **The bytecode's values at `t`**: the final count and the pull fingerprint. -/
theorem bc_factsK (hLb : LbFits D.shape) (hold : HoldAllK D Fl s c1 ch fd c2 t vals) :
    bfcK (inpK D Fl s ch fd t vals) = (c1PK D.shape c1 .bytecodeFinal).eval t ∧
      bpullK (inpK D Fl s ch fd t vals) =
        (bcPullPK D.shape c1 (setupStkK D) (alphasOf ch) (inpK D Fl s ch fd t vals).weights
          (inpK D Fl s ch fd t vals).beta).eval t := by
  have hlb : D.shape.logBytecode < nDigits D.shape := by
    have := h_lt_nDigitsK D.shape
    unfold LbFits at hLb
    omega
  have m1 := mem_rels_bcK D Fl s ch fd t vals (List.mem_cons_self ..)
  have m2 := mem_rels_bcK D Fl s ch fd t vals (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hs : (inpK D Fl s ch fd t vals).shape = D.shape := rfl
  rw [hs] at m1 m2
  have h1 := holds_equal (hold _ m1 .c1 (by simp [Relation.equal, term, Column.commitment]))
  have h2 := holds_equal (hold _ m2 .setup (by simp [Relation.equal, term, Column.commitment]))
  have e1 := ev_c1K D Fl s c1 ch fd c2 t vals .bytecodeFinal rfl (fun j h ↦ by cases h) _ hlb.le le_rfl
    ⟨_, m1, rfl, _, List.mem_singleton_self _, rfl⟩
  have halen : (alphasOf ch).length = 4 := by simp [alphasOf]
  have e2 := ev_setupK D Fl s c1 ch fd c2 t vals .bytecodeTuple rfl
    ((inpK D Fl s ch fd t vals).alphas ++ (inpK D Fl s ch fd t vals).w.take D.shape.logBytecode)
    (fun l ↦ if l < 4 then Polynomial.C ((alphasOf ch).getD l 0) else digitP (l - 4))
    ⟨_, m2, rfl, _, List.mem_singleton_self _, rfl⟩
    (fun b hb ↦ by
      rw [(setup_limbsK D.shape _ b hb).1 rfl, List.length_append,
        wtakeK_length D Fl s ch fd t vals _ hlb.le]
      show _ ≤ (alphasOf ch).length + _
      rw [halen]; omega)
    (fun b hb l hl ↦ by
      rw [(setup_limbsK D.shape _ b hb).1 rfl] at hl
      show _ = ((alphasOf ch) ++ _).getD l 0
      by_cases h4 : l < 4
      · rw [ite_eq_left h4, Polynomial.eval_C, List.getD_append _ _ _ _ (by rw [halen]; exact h4)]
      · rw [ite_eq_right h4, List.getD_append_right _ _ _ _ (by rw [halen]; omega), halen,
          wtakeK_getD D Fl s ch fd t vals _ hlb.le _ (by omega)])
  rw [e1] at h1
  rw [e2] at h2
  refine ⟨h1.symm, ?_⟩
  unfold bcPullPK
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rw [h2, h1]
  have two : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination (-(inpK D Fl s ch fd t vals).beta -
    (inpK D Fl s ch fd t vals).weights.getD 2 0 * bfcK (inpK D Fl s ch fd t vals)) * two

/-- **A table's `Z_act(t)`** (F1b): the verifier's, from the count's bits, is `zActP`'s. -/
theorem active_evalK (hfit : CountsFit D.shape s.2) (o : ℕ) (ho : o < 6) :
    (inpK D Fl s ch fd t vals).active.getD o 0 =
      (zActP ((List.range (D.shape.heights.getD o 0 + 1)).map fun j ↦ intBits (s.2.getD o 0) j 1)
        (D.shape.heights.getD o 0)).eval t := by
  have hh6 : D.shape.heights.length = 6 := D.valid.1
  have hr6 : s.2.length = 6 := hfit.1
  have hlen : o < ((countsOf D.shape s.2).zip D.shape.heights).length := by
    simp [countsOf, hh6, hr6, ho]
  show (((countsOf D.shape s.2).zip D.shape.heights).map fun p ↦
    activeVanishingFromBits (inpK D Fl s ch fd t vals).w p.1 p.2).getD o 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa using hlen), List.getElem_map, List.getElem_zip]
  simp only [countsOf, List.getElem_map, List.getElem_zip]
  rw [← List.getD_eq_getElem s.2 0, ← List.getD_eq_getElem D.shape.heights 0]
  exact activeVanishing_eval _ _ t _ fun j hj ↦ wK_getD D Fl s ch fd t vals j
    (by have := height_lt_nDigitsK D o; omega)

theorem blkK_terms_sub (b : Block) (i : ℕ) (sizes : List ℕ) (X sc : E)
    (h : (blkK D Fl s ch fd t vals b i).terms =
      [term .heap (mixedOf D.shape (inpK D Fl s ch fd t vals).w b) X] ++
        quotientTerms (Column.leafQuotient i) sizes (inpK D Fl s ch fd t vals).w sc) :
    ∀ tm ∈ qTerms (Column.leafQuotient i) (inpK D Fl s ch fd t vals).w sizes 0 sc,
      tm ∈ (blkK D Fl s ch fd t vals b i).terms := by
  intro tm htm
  rw [h, quotientTerms_eq]
  exact List.mem_append_right _ htm

/-- **Each heap block's leaf identity at `t`** on the Keccak tables. -/
theorem blockPK_eval (hC : ChunksFitK D.shape) (hLb : LbFits D.shape) (hH : HeapGood D.shape)
    (hfit : CountsFit D.shape s.2) (hold : HoldAllK D Fl s c1 ch fd c2 t vals) (b : Block) (i : ℕ)
    (hbi : (b, i) ∈ D.shape.heap.blocks.zip (List.range D.shape.heap.blocks.length)) :
    (blockPK D.shape c1 c2 (setupStkK D) s.2 (alphasOf ch) (betaOf ch) b i).eval t = 0 := by
  have hb := (List.of_mem_zip hbi).1
  have hbr := block_r_lt D.shape hH b hb
  have hN := h_lt_nDigitsK D.shape
  have hR := ev_mixedK D Fl s c1 ch fd c2 t vals hH b i hbi
  unfold mixedOf at hR
  have hrel := blockK_holds D Fl s c1 ch fd c2 t vals hold b i hbi
  have hwq : ∀ d, UniKeccak.Shape.leafDegreeK b = some d → ∀ c < (chunks (d + 1)).length,
      (inpK D Fl s ch fd t vals).w.getD ((chunks (d + 1)).getD c 0) 0 =
        (digitP ((chunks (d + 1)).getD c 0)).eval t :=
    fun d hd c hc ↦ wK_getD D Fl s ch fd t vals _ (hC.2 b hb d hd _ (getD_mem' (d := 0) hc))
  have hwr := wK_getD D Fl s ch fd t vals b.r (by omega)
  have hblk := hH.2.2.2.2.2 b hb
  have hw : (inpK D Fl s ch fd t vals).weights = eqKernel (alphasOf ch) := rfl
  have hbeta : (inpK D Fl s ch fd t vals).beta = betaOf ch := rfl
  unfold RelHolds at hrel
  unfold blockPK
  dsimp only
  rcases hlv : b.leaves with _ | _ | tt | _
  · -- The memory's block.
    have hd : UniKeccak.Shape.leafDegreeK b = some (degree (2 * (2 ^ b.r - 1)) (2 ^ b.r)) := by
      unfold UniKeccak.Shape.leafDegreeK; rw [hlv]
    have ht : blkK D Fl s ch fd t vals b i =
        ⟨[term .heap (mixedOf D.shape (inpK D Fl s ch fd t vals).w b) (mpullK (inpK D Fl s ch fd t vals))] ++
          quotientTerms (Column.leafQuotient i) (chunks (degree (2 * (2 ^ b.r - 1)) (2 ^ b.r) + 1))
            (inpK D Fl s ch fd t vals).w ((inpK D Fl s ch fd t vals).w.getD b.r 0),
          mpushK (inpK D Fl s ch fd t vals)⟩ := by
      unfold blkK blockRel mixedOf; dsimp only; rw [hlv]
    have hq := qTerms_val' D.shape c2 (evOfK D Fl s c1 ch fd c2 t vals) (inpK D Fl s ch fd t vals).w t
      (Column.leafQuotient i) _ ((inpK D Fl s ch fd t vals).w.getD b.r 0)
      (ev_leafQK D Fl s c1 ch fd c2 t vals hC b i hbi _ hd _
        (blkK_terms_sub D Fl s ch fd t vals b i _ _ _ (by rw [ht])))
      (hwq _ hd)
    rw [ht] at hrel
    simp only [quotientTerms_eq, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, term, hq] at hrel
    obtain ⟨hmfc, hmpull⟩ := mem_factsK D Fl s c1 ch fd c2 t vals hold
    unfold mixedOf at hrel
    rw [hR] at hrel
    unfold mpushK at hrel
    rw [hmfc, hmpull, hwr, hw, hbeta] at hrel
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one]
    linear_combination hrel
  · -- The bytecode's block.
    have hd : UniKeccak.Shape.leafDegreeK b = some (degree (2 * (2 ^ b.r - 1)) (2 ^ b.r)) := by
      unfold UniKeccak.Shape.leafDegreeK; rw [hlv]
    have ht : blkK D Fl s ch fd t vals b i =
        ⟨[term .heap (mixedOf D.shape (inpK D Fl s ch fd t vals).w b) (bpullK (inpK D Fl s ch fd t vals))] ++
          quotientTerms (Column.leafQuotient i) (chunks (degree (2 * (2 ^ b.r - 1)) (2 ^ b.r) + 1))
            (inpK D Fl s ch fd t vals).w ((inpK D Fl s ch fd t vals).w.getD b.r 0),
          bpushK (inpK D Fl s ch fd t vals)⟩ := by
      unfold blkK blockRel mixedOf; dsimp only; rw [hlv]
    have hq := qTerms_val' D.shape c2 (evOfK D Fl s c1 ch fd c2 t vals) (inpK D Fl s ch fd t vals).w t
      (Column.leafQuotient i) _ ((inpK D Fl s ch fd t vals).w.getD b.r 0)
      (ev_leafQK D Fl s c1 ch fd c2 t vals hC b i hbi _ hd _
        (blkK_terms_sub D Fl s ch fd t vals b i _ _ _ (by rw [ht])))
      (hwq _ hd)
    rw [ht] at hrel
    simp only [quotientTerms_eq, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, term, hq] at hrel
    obtain ⟨hbfc, hbpull⟩ := bc_factsK D Fl s c1 ch fd c2 t vals hLb hold
    unfold mixedOf at hrel
    rw [hR] at hrel
    unfold bpushK at hrel
    rw [hbfc, hbpull, hwr, hw, hbeta] at hrel
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one]
    linear_combination hrel
  · -- A table's block.
    have htt : tt < 6 ∧ b.r = D.shape.heights.getD tt 0 := by rw [hlv] at hblk; exact hblk
    obtain ⟨-, -, hpull, hpush, hpd, hppd⟩ := part_specK D Fl s c1 ch fd c2 t vals hold tt htt.1
    have hop := tablesKeccak_opcode tt htt.1
    have hd : UniKeccak.Shape.leafDegreeK b = some (degree (max (tableDegrees (tablesKeccak.getD tt default)).1
        (tableDegrees (tablesKeccak.getD tt default)).2 * (2 ^ b.r - 1) + (2 ^ b.r - Shape.leastRows b.r))
        (2 ^ b.r)) := by
      unfold UniKeccak.Shape.leafDegreeK; rw [hlv]
    have ht : blkK D Fl s ch fd t vals b i =
        ⟨[term .heap (mixedOf D.shape (inpK D Fl s ch fd t vals).w b)
            (((tpK (inpK D Fl s ch fd t vals)).1.getD tt default).pull * (inpK D Fl s ch fd t vals).w.getD b.r 0 +
              (inpK D Fl s ch fd t vals).active.getD tt 0 * (inpK D Fl s ch fd t vals).active.getD tt 0)] ++
          quotientTerms (Column.leafQuotient i) (chunks (degree (max (tableDegrees (tablesKeccak.getD tt default)).1
            (tableDegrees (tablesKeccak.getD tt default)).2 * (2 ^ b.r - 1) + (2 ^ b.r - Shape.leastRows b.r))
            (2 ^ b.r) + 1))
            (inpK D Fl s ch fd t vals).w
            ((inpK D Fl s ch fd t vals).w.getD b.r 0 * (inpK D Fl s ch fd t vals).active.getD tt 0),
          ((tpK (inpK D Fl s ch fd t vals)).1.getD tt default).push * (inpK D Fl s ch fd t vals).w.getD b.r 0 +
            (inpK D Fl s ch fd t vals).active.getD tt 0 * (inpK D Fl s ch fd t vals).active.getD tt 0⟩ := by
      unfold blkK blockRel mixedOf; dsimp only; rw [hlv]; dsimp only; rw [hpd, hppd]
    have hq := qTerms_val' D.shape c2 (evOfK D Fl s c1 ch fd c2 t vals) (inpK D Fl s ch fd t vals).w t
      (Column.leafQuotient i) _
      ((inpK D Fl s ch fd t vals).w.getD b.r 0 * (inpK D Fl s ch fd t vals).active.getD tt 0)
      (ev_leafQK D Fl s c1 ch fd c2 t vals hC b i hbi _ hd _
        (blkK_terms_sub D Fl s ch fd t vals b i _ _ _ (by rw [ht])))
      (hwq _ hd)
    rw [ht] at hrel
    simp only [quotientTerms_eq, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, term, hq] at hrel
    unfold mixedOf at hrel
    rw [hR, hpull, hpush, hwr, hw, hbeta, active_evalK D Fl s ch fd t vals hfit tt htt.1, ← htt.2] at hrel
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, pullP_evalE, pushP_evalE, hop]
    linear_combination hrel
  · -- An unused block.
    have ht : blkK D Fl s ch fd t vals b i = ⟨[term .heap (mixedOf D.shape (inpK D Fl s ch fd t vals).w b) 1], 1⟩ := by
      unfold blkK blockRel mixedOf; dsimp only; rw [hlv]
    rw [ht] at hrel
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, term, one_mul] at hrel
    unfold mixedOf at hrel
    rw [hR] at hrel
    simp only [Polynomial.eval_add, Polynomial.eval_one]
    exact hrel

end Ctx

/-! ## `DiffsEvalK` -/

/-- **`DiffsEvalK` where round `0` has at least four challenges** (`Ids/Build.lean`'s `DiffsEvalK`, `4 ≤ ch.length`
added): where every relation's difference vanishes, every identity polynomial vanishes at `t`. -/
def DiffsEvalK4 (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) : Prop :=
  ∀ s c1 ch fd c2 t vals, 4 ≤ ch.length → (∀ d ∈ diffsK D Fl s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    ∀ P ∈ polysK D Fl s c1 ch fd c2, P.eval t = 0

/-- **The Keccak relations at `t`, all zero, give every identity polynomial at `t`** (`DiffsEvalK4`), from the
heap's layout (`HeapGood`) and the quotients' chunks within the digits (`ChunksFitK`). -/
theorem diffsEvalK4_of (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (hC : ChunksFitK D.shape) (hH : HeapGood D.shape) : DiffsEvalK4 D Fl := by
  intro s c1 ch fd c2 t vals hch hd P hP
  by_cases hg : CountsFit D.shape s.2 ∧ FlockGoodK κ (Fl.prog.out fd [])
  swap
  · exfalso
    have := hd [1] (by unfold diffsK; rw [ite_eq_right hg]; exact List.mem_singleton_self _) 1
      (List.mem_singleton_self _)
    exact one_ne_zero this
  have hold : HoldAllK D Fl s c1 ch fd c2 t vals :=
    fun r hr c hc ↦ holds_of_diffsK D Fl s c1 ch fd c2 t vals hch hg hd r hr c hc
  unfold polysK at hP
  rw [ite_eq_left hg.1] at hP
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hP
  rcases hP with (rfl | rfl | rfl) | ⟨⟨b, i⟩, hbi, rfl⟩
  · exact treePK_eval D Fl s c1 ch fd c2 t vals hold
  · exact rootPK_eval D Fl s c1 ch fd c2 t vals hold
  · exact wPK_eval D Fl s c1 ch fd c2 t vals hC (hB_posK D) hold
  · exact blockPK_eval D Fl s c1 ch fd c2 t vals hC (lbFits D.shape) hH hg.1 hold b i hbi

/-- **`DiffsEvalK4`** for a deployment whose heap's blocks fill the leaves (`HeapGood`). -/
theorem diffsEvalK4_of_heapGood (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (hH : HeapGood D.shape) : DiffsEvalK4 D Fl :=
  diffsEvalK4_of D Fl (chunksFitK D hH) hH

end UniKeccakSound.IdsEval

/-- info: 'UniKeccakSound.IdsEval.diffsEvalK4_of_heapGood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsEval.diffsEvalK4_of_heapGood
