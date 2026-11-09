-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The statement is `UniKeccakSound/FsK.lean`'s
-- `UniFinalK`; the proof is `UniSound/FinalLink.lean`'s `uniFinal` for `formal/UniKeccak`'s `batchK` (no pending
-- matrices, three values in the tail).
import UniSound.FinalLink
import UniKeccakSound.Ids.Build
import UniKeccakSound.Code.Link

/-!
# The last link on the Keccak VM (`UniFinalK`)

**`uniFinalK_of`**: `UniFinalK D Fl (uniIdsK …) C` for every code-level link `C` whose chain program's checks and
claims are the Keccak main line's (`CodeIsMainK`), given Flock's result the main line's (`FlockGoodDoneK`), the
weights multilinear off `Z_bad`'s roots (`WeightMleK`) and the stacks' variables below `256` (`LayoutVarsSmall3K`).

* **`batchPureK`** is what `batchK` computes from `λ`, its rounds and the three values: the terminal zero
  `Σ_k λ^k W_k(r) ext_k(r) v_k + last` and the three point claims at `r` cut to each stack's variables;
  **`mainBatchK`** is it on the run's combined claims (`runClaimsK`: `combine` of `relsAtK` per commitment), the
  Keccak layouts (`layoutsOfK`) and Flock's ring map.
* **`CodeIsMainK C`** is the interface to the code-level link: on a completed transcript of `C.prog`, its zeros
  vanishing give the counts in range (`readCounts`' checks), Flock's zeros (the structured terminal) and
  `mainBatchK`'s terminal zero, and its result's openings are `mainBatchK`'s. A chain program written from
  `reduceWithK` (as `UniSound.mainProg` from `reduceWith`) has them by definition.
* **`terminal_sumStateK`** (the algebra, independent of the transcript): the terminal with true claims makes the
  batch's last claim the partial sum of `prodK` at its point (`SumState`).
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters LeanVM.Semantics UniStatement UniSound UniSound.Ids UniKeccak Finset FlockSound.Uni

/-! ## The run's batch -/

section Run

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant} (Fl : KFlockSound F κ v)

/-- **The run's combined claims**: `combine` of the relations at `t` for each commitment that has one. -/
def runClaimsK (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) (rho : E) :
    List (Commitment × Combined) :=
  commitments.filterMap fun c => (combine (relsAtK D Fl s ch fd t vals) c rho).map fun x => (c, x)

/-- **The main line's batch** from its rounds' records (`C1`'s round `r0`, Flock's `fd`, `C2`'s `r2`, the values'
`r3`, the batch's `brs`) and the tail `tl`. -/
def mainBatchK (s : USt) (r0 : UMsg × List E) (fd : Done) (r2 r3 : UMsg × List E) (brs : Done) (tl : List E) :
    List E × List (Commitment × Opening) :=
  batchPureK (runClaimsK D Fl s r0.2 fd (r2.2.headD 0) r3.1.2 (r3.2.headD 0)) (layoutsOfK D.shape)
    (ringMapAtK Fl fd) (r3.2.getD 1 0) brs tl

end Run

/-! ## The hypotheses -/

/-- **The code-level link's checks and claims are the Keccak main line's** (`CodeIsMainK`): on every completed
transcript `[r0] ++ fd ++ [r2, r3] ++ brs` of `C.prog` and its tail of three, its zeros vanishing gives the counts
in range, Flock's zeros (the structured terminal) and the batch's terminal zero (`mainBatchK`), and its result's
openings are `mainBatchK`'s. -/
def CodeIsMainK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (nV V : ℕ) (C : UniCodeK D Fl nV V) : Prop :=
  ∀ (s : USt) (r0 : UMsg × List E) (fd : Done) (r2 r3 : UMsg × List E) (brs : Done) (tl : List E),
    fd.length = Fl.prog.rounds.length →
    DoneFits (uniRounds Fl.prog.rounds nV V) ([r0] ++ fd ++ [r2, r3] ++ brs) → tl.length = 3 →
    (C.prog s.1 s.2).ZerosVanish ([r0] ++ fd ++ [r2, r3] ++ brs) tl →
      CountsFit D.shape s.2 ∧ Fl.prog.ZerosVanish fd [] ∧
        (∀ z ∈ (mainBatchK D Fl s r0 fd r2 r3 brs tl).1, z = 0) ∧
        ((C.prog s.1 s.2).out ([r0] ++ fd ++ [r2, r3] ++ brs) tl).openings =
          (mainBatchK D Fl s r0 fd r2 r3 brs tl).2

/-- **Flock's result is the main line's** on every completed Flock transcript: a ring end, a point of `11 + κ`
coordinates (a fact of Flock's phase on the Keccak-f block). -/
def FlockGoodDoneK {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant} (Fl : KFlockSound F κ v) : Prop :=
  ∀ fd, DoneFits Fl.prog.rounds fd → FlockGoodK κ (Fl.prog.out fd [])

/-- **The weights are multilinear at the batch's point** off `Z_bad`'s roots: each commitment's combined claim's
`weightAtK` at a point of the batch's variables is the fold of its values on the cube. -/
def WeightMleK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) : Prop :=
  ∀ (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) (rho : E) (r : List E),
    CountsFit D.shape s.2 → FlockGoodK κ (Fl.prog.out fd []) → ch.length = 6 → vals.length = valsCountK →
      (zbK D Fl fd).eval t ≠ 0 → r.length = batchVarsK D.shape → ∀ c ∈ commitments,
      foldAll (fun u => weightAtK (combAtK D Fl s ch fd t vals rho c) (layoutOfK D.shape c)
          (bitsE u (batchVarsK D.shape)) (ringMapAtK Fl fd)) r 0 =
        weightAtK (combAtK D Fl s ch fd t vals rho c) (layoutOfK D.shape c) r (ringMapAtK Fl fd)

/-- **The stacks have fewer than `256` variables** (a layout word carries them in one byte). -/
def LayoutVarsSmall3K (D : KDeployment) : Prop := ∀ c, (layoutOfK D.shape c).vars < 256

/-! ## The layout words -/

theorem layoutWordsK_word (S : Shape) (c : Commitment) :
    (layoutWordsK S).getD (wordIndex c) [] =
      layoutWord S (layoutCode c) (layoutOfK S c).vars (layoutOfK S c).words := by
  cases c <;> rfl

theorem claimVarsK (D : KDeployment) (hsmall : LayoutVarsSmall3K D) (c : Commitment) :
    layoutWordVars ((layoutWordsK D.shape).getD (wordIndex c) []) = (layoutOfK D.shape c).vars := by
  rw [layoutWordsK_word, layoutWordVars_layoutWord _ _ _ _ (hsmall c)]

/-! ## The terminal -/

/-- The batch's products for the combined claims `X c` of the three commitments and the stacks `stk`: `prodK`'s
form. -/
def prodOfKX (X : Commitment → Combined) (L : List (Commitment × StackLayout)) (rm : Option (List E))
    (stk : Commitment → Stk) (lam : E) : ProdSum where
  vars := varsOf L
  n := 3
  coef k := lam ^ k
  A k u := weightAtK (X (cm k)) (UniSound.layoutOf L (cm k)) (bitsE u (varsOf L)) rm
  B k u := stE (stk (cm k)) (UniSound.layoutOf L (cm k)).vars u

/-- **The batch's terminal check with true claims is the last state** on the Keccak VM (the algebra of
`UniFinalK`): for the combined claims `X c` of the three commitments, the stacks `stk`, the batch's rounds `brs`
and values `t0, t1, t2`. -/
theorem terminal_sumStateK (X : Commitment → Combined) (L : List (Commitment × StackLayout))
    (rm : Option (List E)) (lam : E) (brs : Done) (t0 t1 t2 : E) (stk : Commitment → Stk)
    (hbrs : brs.length = varsOf L) (h2 : ∀ x ∈ brs, x.1.2.length = 2)
    (hz : ∀ z ∈ (batchPureK [(.c1, X .c1), (.c2, X .c2), (.setup, X .setup)] L rm lam brs [t0, t1, t2]).1,
      z = 0)
    (hclaims : ∀ o ∈ (batchPureK [(.c1, X .c1), (.c2, X .c2), (.setup, X .setup)] L rm lam brs
      [t0, t1, t2]).2, ∀ pt w bs, o.2 = .point pt w bs → mleStk (stk o.1) (UniSound.layoutOf L o.1).vars pt = w)
    (hW : ∀ c, foldAll (fun u => weightAtK (X c) (UniSound.layoutOf L c) (bitsE u (varsOf L)) rm)
      (pointAfter (roundsOf brs)) 0 = weightAtK (X c) (UniSound.layoutOf L c) (pointAfter (roundsOf brs)) rm) :
    SumState (prodOfKX X L rm stk lam).oracle (∑ k ∈ range 3, lam ^ k * (X (cm k)).value) (roundsOf brs) := by
  have hsc := decodeSC_none (batchTarget [(.c1, X .c1), (.c2, X .c2), (.setup, X .setup)] lam).1 brs h2
  rw [hbrs] at hsc
  have hrl : (pointAfter (roundsOf brs)).length = varsOf L := by
    rw [length_pointAfter]
    simp [roundsOf, hbrs]
  generalize hrdef : pointAfter (roundsOf brs) = r at hsc hrl hW
  simp only [batchPureK, batchFoldK, hsc, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil] at hz hclaims
  have hcl := eq_of_add_eq_zero_char2 (hz _ (List.mem_singleton_self _))
  simp only [Array.toList_push, List.nil_append, List.cons_append,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hclaims
  obtain ⟨hc1, hc2, hc3⟩ := hclaims
  have hc1 := hc1 _ _ _ rfl
  have hc2 := hc2 _ _ _ rfl
  have hc3 := hc3 _ _ _ rfl
  have hv1 := layoutOf_vars_le L .c1
  have hv2 := layoutOf_vars_le L .c2
  have hv3 := layoutOf_vars_le L .setup
  have htg : ∑ k ∈ range 3, lam ^ k * (X (cm k)).value =
      (batchTarget [(.c1, X .c1), (.c2, X .c2), (.setup, X .setup)] lam).1 := by
    simp only [batchTarget, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ, Finset.sum_range_zero, cm,
      commitments, List.getD_cons_zero, List.getD_cons_succ]
    ring
  unfold SumState
  rw [htg, hrdef, hcl]
  show _ = ProdSum.T (prodOfKX X L rm stk lam) r
  rw [ProdSum.T_full _ r hrl]
  simp only [prodOfKX, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cm, commitments, List.getD_cons_zero,
    List.getD_cons_succ]
  simp only [stE]
  rw [hW .c1, hW .c2, hW .setup,
    foldAll_stackExt _ _ r (by omega), foldAll_stackExt _ _ r (by omega), foldAll_stackExt _ _ r (by omega),
    hc1, hc2, hc3, ← hrl, extension_eq_cubeEq, extension_eq_cubeEq, extension_eq_cubeEq]
  ring

/-! ## The run's claims -/

section RunClaims

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant} (Fl : KFlockSound F κ v)

/-- **One claim per commitment in the run**, each the commitment's combined claim. -/
theorem runClaimsK_eq (s : USt) (ch : List E) (fd : Done) (t : E) (vals : List E) (rho : E) :
    runClaimsK D Fl s ch fd t vals rho =
      [(.c1, combAtK D Fl s ch fd t vals rho .c1), (.c2, combAtK D Fl s ch fd t vals rho .c2),
        (.setup, combAtK D Fl s ch fd t vals rho .setup)] := by
  have hs : ∀ c, (∃ r ∈ relsAtK D Fl s ch fd t vals, r.commitment = c) →
      ∃ x, combine (relsAtK D Fl s ch fd t vals) c rho = some x ∧ combAtK D Fl s ch fd t vals rho c = x := by
    intro c hc
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (combine_isSome _ c rho hc)
    exact ⟨x, hx, by rw [combAtK, hx, Option.getD_some]⟩
  obtain ⟨x1, h1, e1⟩ := hs .c1 ⟨Relation.equal (.memory 3) ((digits t (max D.shape.heap.h
    (D.shape.constraintVars + 4) + 2)).take D.shape.logMemory) (vals.getD tablesReadsK 0),
    flockClaimK_mem _ _ _ (by unfold mainRelsK; simp), rfl⟩
  obtain ⟨x2, h2, e2⟩ := hs .c2 ⟨Relation.equal .heap ((digits t (max D.shape.heap.h
    (D.shape.constraintVars + 4) + 2)).take D.shape.heap.h) (vals.getD (tablesReadsK + 5) 0),
    flockClaimK_mem _ _ _ (by
      unfold mainRelsK
      simp only [Array.toList_append, List.mem_append]
      exact Or.inr (heapRelations_mem _ _ _ _ _ _ _ _ _ _ _ _ _)), rfl⟩
  obtain ⟨x3, h3, e3⟩ := hs .setup ⟨Relation.equal .address ((digits t (max D.shape.heap.h
    (D.shape.constraintVars + 4) + 2)).take D.shape.logMemory) (vals.getD (tablesReadsK + 1) 0),
    flockClaimK_mem _ _ _ (by unfold mainRelsK; simp), rfl⟩
  rw [e1, e2, e3]
  simp [runClaimsK, commitments, h1, h2, h3]

end RunClaims

/-! ## The last link -/

/-- **The last link on the Keccak VM** (`UniFinalK`), for the identity model `uniIdsK` and a code-level link whose
checks and claims are the main line's. -/
theorem uniFinalK_of (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (N : ℕ) (h : IdsHypsK F D κ N) (d n : ℕ) (g : IdsGapsK D Fl d n)
    (C : UniCodeK D Fl (uniIdsK D Fl N h d n g).nV (uniIdsK D Fl N h d n g).V)
    (hC : CodeIsMainK D Fl _ _ C) (hgood : FlockGoodDoneK Fl) (hW : WeightMleK D Fl)
    (hsmall : LayoutVarsSmall3K D) :
    UniFinalK D Fl (uniIdsK D Fl N h d n g) C := by
  intro s done tl c1 c2 hd htl hz hc
  have hd' := hd
  simp only [uniRounds] at hd
  obtain ⟨d012, brs, rfl, h012, hbr⟩ := doneFits_append_split _ _ _ hd
  obtain ⟨d01, d23, rfl, h01, h23⟩ := doneFits_append_split _ _ _ h012
  obtain ⟨d0, G, rfl, h0, hG⟩ := doneFits_append_split _ _ _ h01
  rcases d0 with _ | ⟨x0, _ | ⟨y0, d0⟩⟩ <;> simp only [DoneFits, and_false] at h0
  rcases d23 with _ | ⟨x2, _ | ⟨x3, _ | ⟨y3, d23⟩⟩⟩ <;> simp only [DoneFits, and_false] at h23
  have hGl : G.length = Fl.prog.rounds.length := doneFits_length _ _ hG
  have hbl : brs.length = batchVarsK D.shape := by simpa [uniIdsK] using doneFits_length _ _ hbr
  obtain ⟨hcf, hzF, hzB, hop⟩ := hC s x0 G x2 x3 brs tl hGl hd' htl hz
  -- The opened transcript's reads.
  have hpre : ([x0] ++ G ++ [x2, x3]).length = Fl.prog.rounds.length + 3 := by simp [hGl]
  have hr0 : (rd (openedOf Fl.prog.rounds.length c1 c2 ([x0] ++ G ++ [x2, x3] ++ brs)) 0).2 = x0.2 := by
    rw [rd_openedOf _ _ _ _ 0 (by simp)]
    simp
  have hr2 : (rd (openedOf Fl.prog.rounds.length c1 c2 ([x0] ++ G ++ [x2, x3] ++ brs))
      (Fl.prog.rounds.length + 1)).2 = x2.2 := by
    rw [rd_openedOf _ _ _ _ _ (by simp [hGl])]
    simp [List.getElem_append_right, hGl]
  have hr3 : rd (openedOf Fl.prog.rounds.length c1 c2 ([x0] ++ G ++ [x2, x3] ++ brs))
      (Fl.prog.rounds.length + 2) = ((none, x3.1.2), x3.2) := by
    rw [rd_openedOf _ _ _ _ _ (by simp [hGl])]
    simp [List.getElem_append_right, hGl]
  have hfd : fdOf Fl.prog.rounds.length (openedOf Fl.prog.rounds.length c1 c2 ([x0] ++ G ++ [x2, x3] ++ brs)) =
      G := by
    rw [fdOf_openedOf]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_one, List.tail_cons]
    rw [List.take_left' hGl]
    exact doneFits_noRoot_eq _ _ Fl.rounds_root hG
  rw [hr0, hfd, hr2, hr3, brOf_openedOf _ _ _ _ _ hpre]
  refine ⟨hzF, ?_⟩
  by_cases hzb : (zbK D Fl G).eval (x2.2.headD 0) = 0
  · exact Or.inl hzb
  refine Or.inr ?_
  have hch : x0.2.length = 6 := h0.2.1
  have hvl : x3.1.2.length = valsCountK := h23.2.2.1.2
  have hg := hgood G hG
  change SumState (prodK D Fl s c1 x0.2 G c2 (x2.2.headD 0) x3.1.2 (x3.2.headD 0) (x3.2.getD 1 0)).oracle
    (targetK D Fl s c1 x0.2 G c2 (x2.2.headD 0) x3.1.2 (x3.2.headD 0) (x3.2.getD 1 0)) (roundsOf brs)
  unfold prodK targetK
  rw [ite_eq_left ⟨hcf, hg⟩, ite_eq_left ⟨hcf, hg⟩]
  -- The tail: three values.
  obtain ⟨t0, t1, t2, rfl⟩ := List.length_eq_three.mp htl
  have hzB' := hzB
  unfold mainBatchK at hzB' hop
  rw [runClaimsK_eq] at hzB' hop
  have hc' : ∀ o ∈ (batchPureK [(.c1, combAtK D Fl s x0.2 G (x2.2.headD 0) x3.1.2 (x3.2.headD 0) .c1),
      (.c2, combAtK D Fl s x0.2 G (x2.2.headD 0) x3.1.2 (x3.2.headD 0) .c2),
      (.setup, combAtK D Fl s x0.2 G (x2.2.headD 0) x3.1.2 (x3.2.headD 0) .setup)] (layoutsOfK D.shape)
      (ringMapAtK Fl G) (x3.2.getD 1 0) brs [t0, t1, t2]).2, ∀ pt w bs, o.2 = .point pt w bs →
        mleStk (stackForK D c1 c2 o.1) (UniSound.layoutOf (layoutsOfK D.shape) o.1).vars pt = w := by
    intro o ho pt w bs hob
    have h1 := hc o (by rw [hop]; exact ho) pt w bs hob
    rwa [claimVarsK D hsmall] at h1
  exact terminal_sumStateK (combAtK D Fl s x0.2 G (x2.2.headD 0) x3.1.2 (x3.2.headD 0)) (layoutsOfK D.shape)
    (ringMapAtK Fl G) (x3.2.getD 1 0) brs t0 t1 t2 (stackForK D c1 c2) hbl (doneFits_replicate_two _ _ hbr)
    hzB' hc' fun c => hW s x0.2 G (x2.2.headD 0) x3.1.2 (x3.2.headD 0) _ hcf hg hch hvl hzb
      (by rw [length_pointAfter]; simp [roundsOf, hbl]) c (by cases c <;> simp [commitments])

/-! ## The code-level link's checks and claims are the main line's -/

theorem flockClaimK_snd (rels : Array Relation) (fl : List E × Flock.End) :
    (flockClaimK rels fl).2 = (flockClaimK #[] fl).2 := by
  unfold flockClaimK
  split <;> rfl

/-- **`mainOutK`'s batch is `mainBatchK`** (the run's layouts the shape's, `mainRelsK_c2`). -/
theorem mainOutK_eq (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain)
    (s : USt) (r0 : UMsg × List E) (fd : Done) (r2 r3 : UMsg × List E) (brs : Done) (tl : List E) :
    (mainOutK D Fl s.1 s.2 r0 fd r2 r3 brs tl).1 = (mainBatchK D Fl s r0 fd r2 r3 brs tl).1 ∧
      (mainOutK D Fl s.1 s.2 r0 fd r2 r3 brs tl).2.openings = (mainBatchK D Fl s r0 fd r2 r3 brs tl).2 := by
  unfold mainOutK mainBatchK runClaimsK relsAtK ringMapAtK
  simp only []
  rw [mainRelsK_c2 _ D.valid.1, flockClaimK_snd]
  exact ⟨rfl, rfl⟩

/-- **The Keccak code-level link `uniCodeKAt` has the main line's checks and claims** (`CodeIsMainK`): its chain
program is `mainProgK`, whose round-`0` zero is the counts', whose zeros in Flock's rounds and `C2`'s are Flock's,
and whose tail zero and result are `mainOutK`'s, `mainBatchK`'s. -/
theorem codeIsMainK_uniCodeKAt (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (hκ : D.shape.heights.getD opSha3 0 = κ) :
    CodeIsMainK D Fl valsCountK (varsOf (layoutsOfK D.shape)) (uniCodeKAt D Fl hκ _ _ rfl rfl) := by
  intro s r0 fd r2 r3 brs tl hfl hd htl hz
  change (mainProgK D Fl s.1 s.2).ZerosVanish _ tl at hz
  have hdl := hd.length_eq
  rw [length_uniRounds] at hdl
  simp only [List.length_append, List.length_cons, List.length_nil, hfl] at hdl
  have e : [r0] ++ fd ++ [r2, r3] ++ brs = r0 :: (fd ++ (r2 :: r3 :: brs)) := by simp
  have hcf : CountsFit D.shape s.2 := countsZeroK_of_fits D Fl s.1 s.2 _ tl hd hz
  rw [e] at hz
  have h0 := mainOutK_eq D Fl s r0 fd r2 r3 brs tl
  have hget : ∀ j (hj : j < fd.length), (r0 :: (fd ++ (r2 :: r3 :: brs)))[j + 1]'(by simp; omega) = fd[j] := by
    intro j hj
    simp [List.getElem_append_left hj]
  refine ⟨hcf, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro j hj z hzz
    have h1 := hz.1 (j + 1) (by simp; omega)
    rw [hget j hj, List.take_succ_cons, List.take_append_of_le_length (by omega),
      mainProgK_zeros_ne _ _ _ _ (List.cons_ne_nil _ _)] at h1
    have h2 := mainZerosK_flock Fl.prog r0 (fd.take j) (fd[j]).1 (by simp; omega)
    simp only [List.nil_append, List.singleton_append] at h2
    rw [h2] at h1
    exact h1 z hzz
  · intro z hzz
    have h1 := hz.1 (fd.length + 1) (by simp)
    rw [List.take_succ_cons, List.take_append_of_le_length le_rfl, List.take_length,
      mainProgK_zeros_ne _ _ _ _ (List.cons_ne_nil _ _)] at h1
    have h2 := mainZerosK_c2 Fl.prog r0 fd hfl
    simp only [List.singleton_append] at h2
    rw [h2] at h1
    exact h1 z hzz
  · intro z hzz
    have h1 := hz.2
    rw [mainProgK_tailZeros] at h1
    have hfd : ((fd ++ r2 :: r3 :: brs).take Fl.prog.rounds.length) = fd := by
      rw [← hfl, List.take_left]
    have h2 : (r0 :: (fd ++ r2 :: r3 :: brs)).getD (Fl.prog.rounds.length + 1) default = r2 := by
      simp [List.getD_eq_getElem?_getD, ← hfl]
    have h3 : (r0 :: (fd ++ r2 :: r3 :: brs)).getD (Fl.prog.rounds.length + 2) default = r3 := by
      simp [List.getD_eq_getElem?_getD, ← hfl]
    have h4 : (r0 :: (fd ++ r2 :: r3 :: brs)).drop (Fl.prog.rounds.length + 3) = brs := by
      simp [← hfl, List.drop_append]
    simp only [List.getD_cons_zero, List.drop_one, List.tail_cons, hfd, h2, h3, h4] at h1
    rw [h0.1] at h1
    exact h1 z hzz
  · change ((mainProgK D Fl s.1 s.2).out _ tl).openings = _
    rw [e, mainProgK_out]
    have hfd : ((fd ++ r2 :: r3 :: brs).take Fl.prog.rounds.length) = fd := by
      rw [← hfl, List.take_left]
    have h2 : (r0 :: (fd ++ r2 :: r3 :: brs)).getD (Fl.prog.rounds.length + 1) default = r2 := by
      simp [List.getD_eq_getElem?_getD, ← hfl]
    have h3 : (r0 :: (fd ++ r2 :: r3 :: brs)).getD (Fl.prog.rounds.length + 2) default = r3 := by
      simp [List.getD_eq_getElem?_getD, ← hfl]
    have h4 : (r0 :: (fd ++ r2 :: r3 :: brs)).drop (Fl.prog.rounds.length + 3) = brs := by
      simp [← hfl, List.drop_append]
    simp only [List.getD_cons_zero, List.drop_one, List.tail_cons, hfd, h2, h3, h4]
    exact h0.2

/-- **The last link on the Keccak VM for the Keccak code-level link** (`UniFinalK` at `uniCodeKAt`). -/
theorem uniFinalK_uniCodeKAt (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (Fl : KFlockSound F κ keccakMain) (hκ : D.shape.heights.getD opSha3 0 = κ)
    (N : ℕ) (h : IdsHypsK F D κ N) (d n : ℕ) (g : IdsGapsK D Fl d n) (hgood : FlockGoodDoneK Fl)
    (hW : WeightMleK D Fl) (hsmall : LayoutVarsSmall3K D) :
    UniFinalK D Fl (uniIdsK D Fl N h d n g) (uniCodeKAt D Fl hκ _ _ rfl rfl) :=
  uniFinalK_of D Fl N h d n g _ (codeIsMainK_uniCodeKAt D Fl hκ) hgood hW hsmall

end UniKeccakSound.Ids
