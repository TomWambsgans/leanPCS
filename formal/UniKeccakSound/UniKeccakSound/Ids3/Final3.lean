-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The statement is `UniKeccakSound/FinalK3.lean`'s
-- `UniFinalK3`; the proof is `UniSound/Rec3/FinalLink3.lean`'s `uniFinal3` for `formal/UniKeccak`'s `batchK` at
-- `.rec3` (`Code/Link3.lean`'s `main3ProgK`, `batchPureWK`), with the Keccak main line's model and lemmas
-- (`Ids/Final.lean`).
import UniKeccakSound.Ids3.Model3
import UniKeccakSound.Ids.Final
import UniKeccakSound.Code.Link3
import UniSound.Rec3.Batch3
import UniSound.Rec3.FinalLink3

/-!
# The last link on the Keccak VM at π1-rec3's shape (`UniFinalK3`)

**`uniFinalK3_uniCodeK3At`**: `UniFinalK3 D F3 (uniIdsK3 …) (pairBatchRec3 np) (uniCodeK3At …)`, under the main
line's hypotheses at `F3`: Flock's result the main line's (`FlockGoodDoneK F3`), the weights multilinear off
`Z_bad`'s roots (`WeightMleK D F3`), the stacks' variables below `256` (`LayoutVarsSmall3K D`). On a completed
transcript of `main3ProgK` whose zeros vanish and whose three claims are true:

* the counts are in range (`countsZeroK3_of_fits`);
* **Flock's zeros vanish** (the structured terminal among them): they are the chain program's in Flock's rounds and
  `C2`'s (`mainZerosK_flock`, `mainZerosK_c2`, `UniSound.zerosVanish_flock`);
* **the batch's last state holds** (`BatchState3 cantorBeta1 narrowE` at the paired batch's point `pointAfter3`),
  unless `t` is a root of the merge polynomial: the run's result is the model's batch (`main3OutK_aligned`: the run's
  claims are `combAtK` at `expandCh [c, β, γ]`, `runClaimsK_eq`), the terminal zero with true claims and the
  weights multilinear make the last claim the products' value at the full point (`batchState3_full_np`,
  `terminal3K`).
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters LeanVM.Semantics UniStatement UniSound UniSound.Ids UniKeccak Finset FlockSound.Uni

/-! ## The terminal -/

/-- **The batch's terminal check with true claims is the last claim's value** at π1-rec3's shape on the Keccak VM
(`UniSound.terminal3` for `batchPureWK`): the terminal `sum + last = 0` with the stacks' point claims and the weights
multilinear at the point makes `last` the products' value there. -/
theorem terminal3K (X : Commitment → Combined) (L : List (Commitment × StackLayout)) (rm : Option (List E))
    (lam : E) (brs : Done) (tl : List E) (stk : Commitment → Stk) (np : ℕ) (hnp : varsOf L / 2 = np)
    (htl : tl.length = 3) (hrl : (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)).length = varsOf L)
    (hz : ∀ z ∈ (batchPureWK narrowE [(.c1, X .c1), (.c2, X .c2), (.setup, X .setup)] L rm lam brs tl).1, z = 0)
    (hclaims : ∀ o ∈ (batchPureWK narrowE [(.c1, X .c1), (.c2, X .c2), (.setup, X .setup)] L rm lam brs tl).2,
      ∀ pt v bs', o.2 = .point pt v bs' → mleStk (stk o.1) (UniSound.layoutOf L o.1).vars pt = v)
    (hW : ∀ c, foldAll (fun u => weightAtK (X c) (UniSound.layoutOf L c) (bitsE u (varsOf L)) rm)
        (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) 0 =
      weightAtK (X c) (UniSound.layoutOf L c) (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) rm) :
    claimAfter3 narrowE np (∑ k ∈ range 3, lam ^ k * (X (cm k)).value) (roundsOf brs) =
      ∑ k ∈ range 3, lam ^ k *
        (foldAll (fun u => weightAtK (X (cm k)) (UniSound.layoutOf L (cm k)) (bitsE u (varsOf L)) rm)
            (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) 0 *
          foldAll (fun u => stE (stk (cm k)) (UniSound.layoutOf L (cm k)).vars u)
            (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) 0) := by
  have htg : ∑ k ∈ range 3, lam ^ k * (X (cm k)).value =
      (batchTarget [(.c1, X .c1), (.c2, X .c2), (.setup, X .setup)] lam).1 := by
    simp only [batchTarget, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ, Finset.sum_range_zero, cm,
      commitments, List.getD_cons_zero, List.getD_cons_succ]
    ring
  rw [htg]
  subst hnp
  unfold batchPureWK at hz hclaims
  generalize pointAfter3 cantorBeta1 narrowE (varsOf L / 2) (roundsOf brs) = r at hz hclaims hrl hW ⊢
  generalize claimAfter3 narrowE (varsOf L / 2) (batchTarget [(.c1, X .c1), (.c2, X .c2), (.setup, X .setup)]
    lam).1 (roundsOf brs) = cl at hz ⊢
  obtain ⟨t0, t1, t2, rfl⟩ := List.length_eq_three.mp htl
  simp only [batchFoldK, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil] at hz hclaims
  have hcl := eq_of_add_eq_zero_char2 (hz _ (List.mem_singleton_self _))
  simp only [Array.toList_push, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hclaims
  obtain ⟨hc1, hc2, hc3⟩ := hclaims
  have hc1 := hc1 _ _ _ rfl
  have hc2 := hc2 _ _ _ rfl
  have hc3 := hc3 _ _ _ rfl
  have hv1 := layoutOf_vars_le L .c1
  have hv2 := layoutOf_vars_le L .c2
  have hv3 := layoutOf_vars_le L .setup
  rw [hcl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cm, commitments, List.getD_cons_zero,
    List.getD_cons_succ, zero_add]
  rw [hW .c1, hW .c2, hW .setup]
  unfold stE
  rw [foldAll_stackExt _ _ r (by omega), foldAll_stackExt _ _ r (by omega), foldAll_stackExt _ _ r (by omega),
    hc1, hc2, hc3, ← hrl, extension_eq_cubeEq, extension_eq_cubeEq, extension_eq_cubeEq]
  ring

/-! ## The run's result is the model's batch -/

/-- **The run's result at π1-rec3's shape is the identity model's batch**: its terminal zero and its openings are
`batchPureWK narrowE` of the run's combined claims at `expandCh [c, β, γ]` (`runClaimsK`), the shape's layouts and
Flock's ring map. -/
theorem main3OutK_aligned (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (s : USt) (m0 : UMsg) (cc bb gg : E) (G : Done) (r2 r3 : UMsg × List E)
    (brs : Done) (tl : List E) :
    (main3OutK D F3 s.1 s.2 (m0, [cc, bb, gg]) G r2 r3 brs tl).1 =
        (batchPureWK narrowE (runClaimsK D F3 s (expandCh [cc, bb, gg]) G (r2.2.headD 0) r3.1.2 (r3.2.headD 0))
          (layoutsOfK D.shape) (ringMapAtK F3 G) (r3.2.getD 1 0) brs tl).1 ∧
      (main3OutK D F3 s.1 s.2 (m0, [cc, bb, gg]) G r2 r3 brs tl).2.openings =
        (batchPureWK narrowE (runClaimsK D F3 s (expandCh [cc, bb, gg]) G (r2.2.headD 0) r3.1.2 (r3.2.headD 0))
          (layoutsOfK D.shape) (ringMapAtK F3 G) (r3.2.getD 1 0) brs tl).2 := by
  unfold main3OutK runClaimsK relsAtK ringMapAtK
  simp only []
  rw [mainRelsK_c2 _ D.valid.1, flockClaimK_snd, expandCh_take]
  exact ⟨rfl, rfl⟩

/-! ## The last link -/

/-- **The last link on the Keccak VM at π1-rec3's shape** (`UniFinalK3`), for the identity model `uniIdsK3`, the
paired batch `pairBatchRec3 np` and the code-level link `uniCodeK3At`. -/
theorem uniFinalK3_uniCodeK3At (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ}
    (F3 : KFlockSound F κ keccakRec3) (hκ : D.shape.heights.getD opBlake2s 0 = κ) (N : ℕ) (h : IdsHypsK F D κ N)
    (d n : ℕ) (g : IdsGapsK D F3 d n) (np : ℕ) (hV : varsOf (layoutsOfK D.shape) = 2 * np + 1)
    (hgood : FlockGoodDoneK F3) (hW : WeightMleK D F3) (hsmall : LayoutVarsSmall3K D) :
    UniFinalK3 D F3 (uniIdsK3 D F3 N h d n g np hV) (pairBatchRec3 np)
      (uniCodeK3At D F3 hκ (uniIdsK3 D F3 N h d n g np hV).nV np rfl hV) := by
  intro s done tl c1 c2 hd htl hz hc
  change (main3ProgK D F3 np s.1 s.2).ZerosVanish done tl at hz
  change ClaimsHoldK D ((main3ProgK D F3 np s.1 s.2).out done tl) c1 c2 at hc
  have hcf : CountsFit D.shape s.2 := countsZeroK3_of_fits D F3 np s.1 s.2 done tl hd hz
  have hd' : DoneFits ([⟨true, 0, 2⟩] ++ F3.prog.rounds ++ [⟨true, 0, 0⟩, ⟨false, valsCountK, 1⟩] ++
      (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩])) done := by
    have hd2 : DoneFits (rec3Rounds F3.prog.rounds valsCountK np) done := hd
    rw [rec3Rounds, List.append_assoc] at hd2
    exact hd2
  obtain ⟨d012, brs, rfl, h012, hbr⟩ := doneFits_append_split _ _ _ hd'
  obtain ⟨d01, d23, rfl, h01, h23⟩ := doneFits_append_split _ _ _ h012
  obtain ⟨d0, G, rfl, h0, hG⟩ := doneFits_append_split _ _ _ h01
  rcases d0 with _ | ⟨x0, _ | ⟨y0, d0⟩⟩ <;> simp only [DoneFits, and_false] at h0
  rcases d23 with _ | ⟨x2, _ | ⟨x3, _ | ⟨y3, d23⟩⟩⟩ <;> simp only [DoneFits, and_false] at h23
  obtain ⟨m0, ch0⟩ := x0
  obtain ⟨cc, bb, gg, rfl⟩ := List.length_eq_three.mp h0.2.1
  have hGl : G.length = F3.prog.rounds.length := doneFits_length _ _ hG
  have hbl : brs.length = np + 1 := by simpa using doneFits_length _ _ hbr
  have hvl : x3.1.2.length = valsCountK := h23.2.2.1.2
  -- The opened transcript's reads.
  have hpre : ([(m0, [cc, bb, gg])] ++ G ++ [x2, x3]).length = F3.prog.rounds.length + 3 := by
    simp [hGl]
  have hr0 : (rd (openedOf F3.prog.rounds.length c1 c2
      ([(m0, [cc, bb, gg])] ++ G ++ [x2, x3] ++ brs)) 0).2 = [cc, bb, gg] := by
    rw [rd_openedOf _ _ _ _ 0 (by simp)]
    simp
  have hr2 : (rd (openedOf F3.prog.rounds.length c1 c2
      ([(m0, [cc, bb, gg])] ++ G ++ [x2, x3] ++ brs)) (F3.prog.rounds.length + 1)).2 = x2.2 := by
    rw [rd_openedOf _ _ _ _ _ (by simp [hGl])]
    simp [List.getElem_append_right, hGl]
  have hr3 : rd (openedOf F3.prog.rounds.length c1 c2
      ([(m0, [cc, bb, gg])] ++ G ++ [x2, x3] ++ brs)) (F3.prog.rounds.length + 2) =
      ((none, x3.1.2), x3.2) := by
    rw [rd_openedOf _ _ _ _ _ (by simp [hGl])]
    simp [List.getElem_append_right, hGl]
  have hfd : fdOf F3.prog.rounds.length (openedOf F3.prog.rounds.length c1 c2
      ([(m0, [cc, bb, gg])] ++ G ++ [x2, x3] ++ brs)) = G := by
    rw [fdOf_openedOf]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_one, List.tail_cons]
    rw [List.take_left' hGl]
    exact doneFits_noRoot_eq _ _ F3.rounds_root hG
  rw [hr0, hfd, hr2, hr3, brOf_openedOf _ _ _ _ _ hpre]
  -- The transcript as the program reads it.
  have e : [(m0, [cc, bb, gg])] ++ G ++ [x2, x3] ++ brs = (m0, [cc, bb, gg]) :: (G ++ x2 :: x3 :: brs) := by
    simp
  rw [e] at hz hc
  -- Flock's zeros are among the program's.
  have hzv : F3.prog.ZerosVanish G [] := by
    refine zerosVanish_flock (main3ProgK D F3 np s.1 s.2) F3.prog (m0, [cc, bb, gg]) x2 G (x3 :: brs) hGl
      (fun e' msg he => ?_) (fun msg => ?_) hz.1
    · rw [main3ProgK_zeros_ne D F3 np s.1 s.2 (List.cons_ne_nil _ _)]
      have h2 := mainZerosK_flock F3.prog (m0, [cc, bb, gg]) e' msg he
      simpa only [List.nil_append, List.singleton_append] using h2
    · rw [main3ProgK_zeros_ne D F3 np s.1 s.2 (List.cons_ne_nil _ _)]
      have h2 := mainZerosK_c2 F3.prog (m0, [cc, bb, gg]) G hGl msg
      simpa only [List.singleton_append] using h2
  refine ⟨hzv, ?_⟩
  by_cases hzb : ((uniIdsK3 D F3 N h d n g np hV).zb G).eval (x2.2.headD 0) = 0
  · exact Or.inl hzb
  refine Or.inr ?_
  -- The program's terminal zero and result at this transcript.
  have hfd' : ((G ++ x2 :: x3 :: brs).take F3.prog.rounds.length) = G := by
    rw [← hGl, List.take_left]
  have h2' : ((m0, [cc, bb, gg]) :: (G ++ x2 :: x3 :: brs)).getD (F3.prog.rounds.length + 1) default = x2 := by
    simp [List.getD_eq_getElem?_getD, ← hGl]
  have h3' : ((m0, [cc, bb, gg]) :: (G ++ x2 :: x3 :: brs)).getD (F3.prog.rounds.length + 2) default = x3 := by
    simp [List.getD_eq_getElem?_getD, ← hGl]
  have h4' : ((m0, [cc, bb, gg]) :: (G ++ x2 :: x3 :: brs)).drop (F3.prog.rounds.length + 3) = brs := by
    simp [← hGl, List.drop_append]
  have hz' := hz.2
  rw [main3ProgK_tailZeros] at hz'
  rw [main3ProgK_out] at hc
  simp only [List.getD_cons_zero, List.drop_one, List.tail_cons, hfd', h2', h3', h4'] at hz' hc
  have hal := main3OutK_aligned D F3 s m0 cc bb gg G x2 x3 brs tl
  rw [hal.1, runClaimsK_eq] at hz'
  have hop := hal.2
  rw [runClaimsK_eq] at hop
  have hg : FlockGoodK κ (F3.prog.out G []) := hgood G hG
  have hnp : varsOf (layoutsOfK D.shape) / 2 = np := by omega
  -- The batch's last state.
  change BatchState3 cantorBeta1 narrowE
    (prodK D F3 s c1 (expandCh [cc, bb, gg]) G c2 (x2.2.headD 0) x3.1.2 (x3.2.headD 0) (x3.2.getD 1 0))
    (targetK D F3 s c1 (expandCh [cc, bb, gg]) G c2 (x2.2.headD 0) x3.1.2 (x3.2.headD 0) (x3.2.getD 1 0))
    (roundsOf brs)
  have hBS := batchState3_full_np
    (prodK D F3 s c1 (expandCh [cc, bb, gg]) G c2 (x2.2.headD 0) x3.1.2 (x3.2.headD 0) (x3.2.getD 1 0))
    np cantorBeta1 narrowE
    (targetK D F3 s c1 (expandCh [cc, bb, gg]) G c2 (x2.2.headD 0) x3.1.2 (x3.2.headD 0) (x3.2.getD 1 0))
    (roundsOf brs) (by rw [prodK_vars]; exact hV) (by simp [roundsOf, hbl])
  have hrl := hBS.1
  rw [prodK_vars] at hrl
  rw [hBS.2]
  unfold prodK targetK
  rw [ite_eq_left ⟨hcf, hg⟩, ite_eq_left ⟨hcf, hg⟩]
  dsimp only
  refine terminal3K (combAtK D F3 s (expandCh [cc, bb, gg]) G (x2.2.headD 0) x3.1.2 (x3.2.headD 0))
    (layoutsOfK D.shape) (ringMapAtK F3 G) (x3.2.getD 1 0) brs tl (stackForK D c1 c2) np hnp htl hrl hz'
    (fun o ho pt v bs hob => ?_) (fun c => ?_)
  · have h1 := hc o (by rw [hop]; exact ho) pt v bs hob
    rwa [claimVarsK D hsmall] at h1
  · exact hW s (expandCh [cc, bb, gg]) G (x2.2.headD 0) x3.1.2 (x3.2.headD 0) _ hcf hg (by simp [expandCh]) hvl
      hzb hrl c (by cases c <;> simp [commitments])

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.uniFinalK3_uniCodeK3At' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.uniFinalK3_uniCodeK3At

/-- info: 'UniKeccakSound.Ids.terminal3K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.terminal3K
