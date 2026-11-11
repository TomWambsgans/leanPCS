-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Implementation.Blocks
import Implementation.Constants

/-!
# The graph's nodes hold the Statement's formulas

`reduceIds_spec`: the program of `Program.lean`, which `reduceIds_eq` checks against the graph, leaves
nodes whose elements (in `E`, with its Rust limbs) are the Statement's claims (`Formula.claims`, which
is `PcsQuotient.claimsAt` by `Formula.claimsAt_eq`), given leaves that hold the leaves' values
(`LeafOK`), when the denominators do not vanish; and `checkId_spec`: the node the contract requires
nonzero is the product of the Statement's denominators.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Implementation

open LeanVM.Parameters PcsQuotient PcsQuotient.Domain Program Emitted

variable {e : Env}

local notation "V" => val limbsEquiv e
local notation "EL" => elem limbsEquiv
local notation "hF" => isF192_primitives
local notation "MUL" => mul_spec (e := e) isF192_primitives
local notation "ADD" => add_spec (e := e) isF192_primitives
local notation "CNST" => cnst_spec (e := e) isF192_primitives

/-- **The leaves hold `I`**: the statement's halves, the challenges, the four values, `next`, and `Q`'s and
`G`'s values. -/
structure LeafOK (e : Env) (I : Formula.Vals) : Prop where
  s0 : val limbsEquiv e 2 = (halves I.stmt.y).1
  s1 : val limbsEquiv e 3 = (halves I.stmt.y).2
  s2 : val limbsEquiv e 4 = (halves I.stmt.root).1
  s3 : val limbsEquiv e 5 = (halves I.stmt.root).2
  α : val limbsEquiv e 10 = I.α
  β : val limbsEquiv e 12 = I.β
  γ : val limbsEquiv e 14 = I.γ
  t : val limbsEquiv e 25 = I.t
  a0 : val limbsEquiv e 26 = I.a[0]
  a1 : val limbsEquiv e 27 = I.a[1]
  a2 : val limbsEquiv e 28 = I.a[2]
  a3 : val limbsEquiv e 29 = I.a[3]
  next : val limbsEquiv e 30 = I.next
  ρ : val limbsEquiv e 32 = I.ρ
  qv : val limbsEquiv e 651 = I.qValue
  gv : val limbsEquiv e 652 = I.gValue

/-! ## The `w` chain -/

theorem wfold_spec (t : E) : ∀ n,
    (((List.range n).foldl (fun ws _ ↦ ws ++ [ws.getLastD t * ws.getLastD t + ws.getLastD t]) [t]).length
      = n + 1) ∧
    ∀ k ≤ n, ((List.range n).foldl (fun ws _ ↦ ws ++ [ws.getLastD t * ws.getLastD t + ws.getLastD t])
      [t]).getD k 0 = sq^[k] t
  | 0 => ⟨rfl, fun k hk => by obtain rfl : k = 0 := Nat.le_zero.mp hk; rfl⟩
  | n + 1 => by
    obtain ⟨hlen, hw⟩ := wfold_spec t n
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set ws := (List.range n).foldl (fun ws _ ↦ ws ++ [ws.getLastD t * ws.getLastD t + ws.getLastD t]) [t]
    have hlast : ws.getLastD t = sq^[n] t := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hlen]
      have := hw n le_rfl
      rw [List.getD_eq_getElem?_getD] at this
      simp only [Nat.add_sub_cancel]
      rw [List.getElem?_eq_getElem (by omega)] at this ⊢
      simpa using this
    refine ⟨by simp [hlen], fun k hk => ?_⟩
    by_cases hkn : k ≤ n
    · rw [List.getD_append _ _ _ _ (by omega)]
      exact hw k hkn
    · obtain rfl : k = n + 1 := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [hlast, Function.iterate_succ_apply']
      rfl

theorem length_w (I : Formula.Vals) : (Formula.w I).length = 26 := (wfold_spec I.t 25).1

theorem wAt_eq (I : Formula.Vals) (k : ℕ) (hk : k < 26) : Formula.wAt I k = sq^[k] I.t :=
  (wfold_spec I.t 25).2 k (by omega)

theorem w_eq (I : Formula.Vals) : Formula.w I = (List.range 26).map (Formula.wAt I) := by
  apply List.ext_getElem (by simp [length_w])
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range, Formula.wAt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-! ## The stages -/

variable (e) in
/-- What the first stage leaves (`stageA`). -/
structure AOK (I : Formula.Vals) (A : StageA) : Prop where
  w : ∀ k < 26, val limbsEquiv e (A.w.getD k 0) = Formula.wAt I k
  x : val limbsEquiv e A.x = Formula.x I
  gate : val limbsEquiv e A.gate = Formula.gate I
  target : val limbsEquiv e A.target = Formula.target I
  rows : val limbsEquiv e A.rows = Formula.rows I
  product : val limbsEquiv e A.product = Formula.product I
  copies : val limbsEquiv e A.copies = Formula.copies I

variable (e) in
/-- What the second stage leaves (`stageB`): the denominators and their prefix products. -/
structure BOK (I : Formula.Vals) (B : StageB) : Prop where
  dens : B.dens.map (val limbsEquiv e) = Formula.denominators I
  pre : ∀ i ≤ B.dens.length, val limbsEquiv e (B.pre.getD i 0) =
    ((B.dens.take i).map (val limbsEquiv e)).prod
  total : B.total = B.pre.getD B.dens.length 0

/-- A step of a program: bind, with the spec of its first operation. -/
macro "stp " h:term:max " => " x:ident hx:ident : tactic =>
  `(tactic| ((try dsimp only); apply Spec.bind; refine Spec.weaken $h fun $x $hx => ?_))

theorem one_val : V leaves₀.one = 1 := by
  show V 1 = 1
  rw [val_const hF (k := 1) (c := 1) (by decide +kernel), elem_one hF]

theorem stageA_spec (I : Formula.Vals) (hI : LeafOK e I) : Spec (stageA leaves₀) (AOK e I) := by
  unfold stageA
  have hone := one_val (e := e)
  -- the `w` chain
  stp (wChain_spec (e := e) hF 25 25) => w hw
  obtain ⟨hwlen, hwv⟩ := hw
  have hW : ∀ k < 26, V (w.getD k 0) = Formula.wAt I k := fun k hk => by
    rw [hwv k hk, wAt_eq I k hk]
    show sq^[k] (V 25) = _
    rw [hI.t]
  -- the cells and the gate
  have ha : V (leaves₀.a.getD 0 0) = I.a[0] ∧ V (leaves₀.a.getD 1 0) = I.a[1] ∧
      V (leaves₀.a.getD 2 0) = I.a[2] ∧ V (leaves₀.a.getD 3 0) = I.a[3] :=
    ⟨hI.a0, hI.a1, hI.a2, hI.a3⟩
  have hcell : ∀ (sh : Nat) (s : K) (hs : EL sh = ofK s) (second : Bool) (c : Nat),
      V c = V (leaves₀.a.getD 0 0) + (V leaves₀.t + EL sh) * V (leaves₀.a.getD 1 0) +
        (if second then V (w.getD 1 0) + 1 else V (w.getD 1 0)) *
          (V (leaves₀.a.getD 2 0) + (V leaves₀.t + EL sh) * V (leaves₀.a.getD 3 0)) →
      V c = Formula.cell I s second := by
    intro sh s hs second c h
    rw [h, hW 1 (by norm_num), hs, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
    show _ = I.a[0] + (I.t + ofK s) * I.a[1] + _ * (I.a[2] + (I.t + ofK s) * I.a[3])
    rw [show V leaves₀.t = I.t from hI.t]
  stp (cell_spec (e := e) hF leaves₀ hone _ _ _) => c0 hc0
  stp (cell_spec (e := e) hF leaves₀ hone _ _ _) => c1 hc1
  stp (cell_spec (e := e) hF leaves₀ hone _ _ _) => c2 hc2
  stp (cell_spec (e := e) hF leaves₀ hone _ _ _) => c3 hc3
  have hx : V c0 = Formula.x I := hcell 0 0 (by rw [elem_zero hF, ofK_zero]) _ _ hc0
  have hy : V c1 = Formula.y I := hcell 1 1 (by rw [elem_one hF, ofK_one]) _ _ hc1
  have hc : V c2 = Formula.c I := hcell _ _ elem_theta _ _ hc2
  have hv : V c3 = Formula.v I := hcell _ _ elem_theta1 _ _ hc3
  stp (ADD _ _) => g1 hg1
  stp (ADD _ _) => g2 hg2
  stp (MUL _ _) => g3 hg3
  stp (ADD _ _) => gate hgate
  have hG : V gate = Formula.gate I := by
    rw [hgate, hg2, hg1, hg3, hx, hy, hc, hv]; rfl
  -- the public weight
  stp (MUL _ _) => gamma2 hgamma2
  stp (MUL _ _) => gamma4 hgamma4
  have hγ : V leaves₀.gamma = I.γ := hI.γ
  stp (foldO_spec (e := e) hF (fun acc k => acc * (1 + Formula.wAt I k))
    (List.range' 11 (24 - 11)) (fun acc k hk => by
      stp (ADD _ _) => o ho
      refine (MUL _ _).weaken fun r hr => ?_
      rw [hr, ho, hone, hW k (by simp at hk; omega)]) leaves₀.one) => pub0 hpub0
  stp (foldO_spec (e := e) hF
    (fun acc k => acc * (1 + Formula.coordinate I k * Formula.slope I k))
    (List.range 11) (fun acc k hk => by
      have hk11 : k < 11 := by simpa using hk
      stp (foldO_spec (e := e) hF
        (fun s j => s + ofK ((coordinates region).getD (j - k) 0) * Formula.wAt I j)
        (List.range' (k + 1) (11 - (k + 1))) (fun acc' j hj => by
          have hj11 : j < 11 := by simp at hj; omega
          stp (CNST _) => bc hbc
          stp (MUL _ _) => p hp
          refine (ADD _ _).weaken fun r hr => ?_
          rw [hr, hp, hbc, hW j (by omega), elem_coords]) (w.getD k 0)) => coordinate hcoord
      stp (Spec.weaken (P := fun r => V r = Formula.slope I k) (by
          unfold slopeOf
          split_ifs with h8
          · refine (CNST _).weaken fun r hr => ?_
            rw [hr]
            have hs := slopes k h8
            unfold Formula.slope
            cases hcw : coordinateWeight k with
            | none => rw [hcw] at hs; cases hs
            | some wt => rw [hcw] at hs; exact (Option.some.inj hs).symm
          · refine (ADD _ _).weaken fun r hr => ?_
            rw [hr, hone]
            unfold Formula.slope
            rw [coordinateWeight_none h8]
            have : k - 8 < 3 := by omega
            interval_cases hk' : k - 8
            · simp [Formula.gammas, hγ]
            · simp [Formula.gammas, hgamma2, hγ]
            · simp [Formula.gammas, hgamma4, hgamma2, hγ]) fun r hr => hr) => slope hslope
      stp (MUL _ _) => cs hcs
      stp (ADD _ _) => o ho
      refine (MUL _ _).weaken fun r hr => ?_
      rw [hr, ho, hcs, hslope, hcoord, hone, hW k (by omega)]
      rfl) pub0) => pubW hpubW
  have hP : V pubW = Formula.publicWeight I := by
    rw [hpubW, hpub0, hone]; rfl
  -- the target
  stp (MUL _ _) => tg1 htg1
  stp (ADD _ _) => tg2 htg2
  stp (MUL _ _) => tg3 htg3
  stp (ADD _ _) => tg4 htg4
  stp (MUL _ _) => tg5 htg5
  stp (ADD _ _) => tg6 htg6
  stp (ADD _ _) => target htarget
  have hT : V target = Formula.target I := by
    rw [htarget, htg6, htg5, htg4, htg3, htg2, htg1, hgamma4, hgamma2]
    simp only [Formula.target, statementWords, Statement.halves, List.cons_append, List.nil_append,
      List.foldr_cons, List.foldr_nil]
    rw [show V (leaves₀.s.getD 0 0) = _ from hI.s0, show V (leaves₀.s.getD 1 0) = _ from hI.s1,
      show V (leaves₀.s.getD 2 0) = _ from hI.s2, show V (leaves₀.s.getD 3 0) = _ from hI.s3, hγ]
    ring
  -- the rows' polynomial
  stp (CNST _) => zr hzr
  stp (foldO_spec (e := e) hF
    (fun acc k => acc + ofK ((rowVanishing 24).getD k 0) * Formula.wAt I k) (List.range (24 - 1))
    (fun acc k hk => by
      stp (CNST _) => tk htk
      stp (MUL _ _) => p hp
      refine (ADD _ _).weaken fun r hr => ?_
      rw [hr, hp, htk, hW k (by simp at hk; omega), elem_tau]) zr) => rows hrows
  have hR : V rows = Formula.rows I := by
    rw [hrows, hzr, elem_zero hF]; rfl
  -- the copy identity
  stp (ADD _ _) => ax hax
  stp (MUL _ _) => bt hbt
  stp (ADD _ _) => dd0 hd
  stp (MUL _ _) => bn hbn
  stp (ADD _ _) => dNext hdNext
  stp (MUL _ _) => product hproduct
  stp (ADD _ _) => dd hdd
  stp (MUL _ _) => px hpx
  stp (MUL _ _) => pxp hpxp
  stp (ADD _ _) => copies hcopies
  have hα : V leaves₀.alpha = I.α := hI.α
  have hβ : V leaves₀.beta = I.β := hI.β
  have ht : V leaves₀.t = I.t := hI.t
  have hn : V leaves₀.next = I.next := hI.next
  have hD : V dd0 = Formula.d I := by rw [hd, hax, hbt, hx, hα, hβ, ht]; rfl
  have hDN : V dNext = Formula.dNext I := by rw [hdNext, hax, hbn, hx, hα, hβ, hn]; rfl
  have hPr : V product = Formula.product I := by rw [hproduct, hD, hDN]; rfl
  have hC : V copies = Formula.copies I := by
    rw [hcopies, hdd, hpxp, hpx, hD, hDN, hPr, hP, hx]; rfl
  apply Spec.pure
  exact ⟨hW, hx, hG, hT, hR, hPr, hC⟩

theorem stageB_spec (I : Formula.Vals) (hI : LeafOK e I) (A : StageA) (hA : AOK e I A) :
    Spec (stageB leaves₀ A) (BOK e I) := by
  have hone := one_val (e := e)
  unfold stageB
  stp (mapO_spec (e := e) hF (fun k => 1 + Formula.wAt I k) (List.range (24 + 2))
    (fun k hk => (ADD _ _).weaken fun r hr => by rw [hr, hone, hA.w k (by simpa using hk)])) => ws hws
  stp (ADD _ _) => cw hcw
  stp (ADD _ _) => r1 hr1
  stp (prefixes_spec (e := e) hF (ws ++ [cw, A.rows, A.product, r1]) leaves₀.one) => pre hpre
  obtain ⟨-, hprev⟩ := hpre
  apply Spec.pure
  refine ⟨?_, fun i hi => by rw [hprev i hi, hone, one_mul], rfl⟩
  rw [List.map_append, hws]
  simp only [List.map_cons, List.map_nil, Formula.denominators, hcw, hA.product, hA.w 24 (by norm_num),
    hA.rows, hr1, hone, show V leaves₀.rho = I.ρ from hI.ρ, w_eq, List.map_map]
  rfl

theorem dens_length (I : Formula.Vals) (B : StageB) (hB : BOK e I B) : B.dens.length = 30 := by
  have := congrArg List.length hB.dens
  simp only [List.length_map, Formula.denominators, List.length_append, length_w] at this
  simpa using this

theorem total_val (I : Formula.Vals) (B : StageB) (hB : BOK e I B) :
    V B.total = (Formula.denominators I).prod := by
  rw [hB.total, hB.pre _ le_rfl, List.take_length, hB.dens]

/-- **What the graph requires nonzero** is the product of the Statement's denominators. -/
theorem checkId_spec (I : Formula.Vals) (hI : LeafOK e I) :
    Spec checkId fun c => V c = (Formula.denominators I).prod := by
  unfold checkId
  rw [chain_eq]
  apply Spec.bind
  apply Spec.some
  stp (stageA_spec (e := e) I hI) => A hA
  stp (stageB_spec (e := e) I hI A hA) => B hB
  exact Spec.pure (total_val I B hB)

theorem getD_of_map_eq {l : List Nat} {g : List E} (h : l.map V = g) (i : Nat) (hi : i < g.length) :
    V (l.getD i 0) = g.getD i 0 := by
  have hl : l.length = g.length := by simpa using congrArg List.length h
  have := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show i < l.length by omega),
    List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact this

/-- `quotient_parts` on the graph: its three points and two weights. -/
theorem parts_spec (I : Formula.Vals) (point : List Nat) (hp : point.map V = Formula.quotientPoint I) :
    Spec (parts leaves₀ point) fun r =>
      r.1.map V = (Formula.parts I).1.1 ∧ r.2.1.map V = (Formula.parts I).2.1.1 ∧
        r.2.2.1.map V = (Formula.parts I).2.2.1 ∧ V r.2.2.2.1 = (Formula.parts I).2.1.2 ∧
        V r.2.2.2.2 = (Formula.parts I).2.2.2 := by
  have hone := one_val (e := e)
  have hlen : (Formula.quotientPoint I).length = 30 := by
    simp [Formula.quotientPoint, Formula.u, Formula.m, cellVars, PcsQuotient.logRows]
  have hat : ∀ k < 6, V (point.getD (24 + k) 0) = (Formula.quotientPoint I).getD (24 + k) 0 :=
    fun k hk => getD_of_map_eq hp _ (by omega)
  have hlow : (point.take 24).map V = (Formula.quotientPoint I).take 24 := by rw [List.map_take, hp]
  unfold parts
  dsimp only
  stp (ADD _ _) => ok1 hok1
  stp (MUL _ _) => qW hqW
  stp (ADD _ _) => od1 hod1
  stp (ADD _ _) => ok0 hok0
  stp (MUL _ _) => g1 hg1
  stp (MUL _ _) => g2 hg2
  stp (ADD _ _) => oe0 hoe0
  stp (MUL _ _) => g3 hg3
  stp (ADD _ _) => oe1 hoe1
  stp (MUL _ _) => gW hgW
  apply Spec.pure
  have h0 := hat 0 (by norm_num)
  have h1 := hat 1 (by norm_num)
  have h2 := hat 2 (by norm_num)
  have h3 := hat 3 (by norm_num)
  have h4 := hat 4 (by norm_num)
  have h5 := hat 5 (by norm_num)
  simp only [Formula.parts, quotientParts, List.map_append, List.map_cons, List.map_nil, hlow]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h0, h4, h5]; rfl
  · rw [h0, h1, h4, h5]; rfl
  · rw [h0]; rfl
  · rw [hqW, hok1, hone, h2, h3]; rfl
  · rw [hgW, hoe1, hg3, hoe0, hg2, hg1, hod1, hok0, hone, h1, h2, h3, h4, h5]; rfl

theorem prod_take_eq (l : List Nat) (i : Nat) (hi : i ≤ l.length) :
    ((l.take i).map V).prod = ((List.range i).map fun j => V (l.getD j 0)).prod := by
  have e : (l.take i).map V = (List.range i).map fun j => V (l.getD j 0) := by
    apply List.ext_getElem (by simp; omega)
    intro j h1 h2
    simp only [List.length_map, List.length_take, List.length_range] at h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < l.length by omega)]
  rw [e]

theorem foldl_mul_eq {α : Type} (f : α → E) : ∀ (l : List α) (a : E),
    l.foldl (fun acc k => acc * f k) a = a * (l.map f).prod
  | [], a => by simp
  | k :: l, a => by rw [List.foldl_cons, foldl_mul_eq f l, List.map_cons, List.prod_cons, mul_assoc]

/-- **The claims' nodes** (`stageC`): when the denominators do not vanish, the nodes it leaves hold the
Statement's claims. -/
theorem stageC_spec (I : Formula.Vals) (hI : LeafOK e I) (A : StageA) (hA : AOK e I A) (B : StageB)
    (hB : BOK e I B) (hnz : (Formula.denominators I).prod ≠ 0) :
    Spec (stageC leaves₀ A B) fun o =>
      o.wPt.map V = (Formula.claims I).witness.point ∧ V o.wVal = (Formula.claims I).witness.value ∧
      o.fPt.map V = (Formula.claims I).wiring.point ∧ V o.fVal = (Formula.claims I).wiring.value ∧
      o.hPt.map V = (Formula.claims I).h.point ∧ V o.hVal = (Formula.claims I).h.value ∧
      o.qPt.map V = (Formula.claims I).q.point ∧ o.gPt.map V = (Formula.claims I).g.point ∧
      V o.sum = (Formula.claims I).sum.value := by
  have hone := one_val (e := e)
  have hW := hA.w
  have hdlen := dens_length I B hB
  have hcheck := total_val I B hB
  have hρ : V leaves₀.rho = I.ρ := hI.ρ
  unfold stageC
  -- the inverses
  stp (inverse_spec (e := e) hF (frobOK hF) _) => running hrunning
  set P : Nat → E := fun i => ((List.range i).map fun j => V (B.dens.getD j 0)).prod with hPdef
  have hPs : ∀ i, P (i + 1) = P i * V (B.dens.getD i 0) := fun i => by
    simp [hPdef, List.range_succ]
  have hP30 : P B.dens.length = (Formula.denominators I).prod := by
    rw [hPdef]; dsimp only
    rw [← prod_take_eq _ _ le_rfl, List.take_length, hB.dens]
  stp (backInv_spec (e := e) hF (fun i => B.pre.getD i 0)
    (fun i => B.dens.getD i 0) P hPs _ running
    (fun i hi => by rw [hB.pre i hi.le, prod_take_eq _ _ hi.le])
    (by rw [hrunning, hcheck, hP30]) (by rw [hP30]; exact hnz)) => invsRev hinvs
  obtain ⟨-, hinvs⟩ := hinvs
  rw [hdlen] at hinvs
  have hInv : ∀ i < 30, V (invsRev.reverse.getD i 0) = Formula.inv I i := fun i hi => by
    rw [hinvs i hi, getD_of_map_eq hB.dens i (by rw [← hB.dens]; simp [hdlen, hi]), Formula.inv,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i < (Formula.denominators I).length by rw [← hB.dens]; simp [hdlen, hi])]
    rfl
  stp (mapO_spec (e := e) hF (fun k => Formula.wAt I k * Formula.inv I k) (List.range (24 + 2))
    (fun k hk => (MUL _ _).weaken fun r hr => by
      have hk' : k < 26 := by simpa using hk
      rw [hr, hW k hk', hInv k (by omega)])) => u hu
  have hU : u.map V = Formula.u I := hu
  stp (foldO_spec (e := e) hF (fun acc k => acc * Formula.inv I k)
    (List.range' 3 (24 - 3)) (fun acc k hk => (MUL _ _).weaken fun r hr => by
      have hk' : k < 26 := by simp at hk; omega
      rw [hr, hInv k (by omega)]) (invsRev.reverse.getD 2 0)) => middle hmiddle
  have hMid : V middle = Formula.middle I := by rw [hmiddle, hInv 2 (by norm_num)]; rfl
  stp (MUL _ _) => ws0 hws0
  stp (MUL _ _) => wiringScale hwiringScale
  have hWS : V wiringScale = Formula.wiringScale I := by
    rw [hwiringScale, hws0, hMid, hInv 0 (by norm_num), hInv 1 (by norm_num)]; rfl
  stp (MUL _ _) => qs0 hqs0
  stp (MUL _ _) => quotientScale hquotientScale
  have hQS : V quotientScale = Formula.quotientScale I := by
    rw [hquotientScale, hqs0, hWS, hInv 24 (by norm_num), hInv 25 (by norm_num)]; rfl
  -- the claims
  stp (MUL _ _) => rho2 hrho2
  have hR2 : V rho2 = Formula.rho2 I := by rw [hrho2, hρ]; rfl
  stp (ADD _ _) => o1 ho1
  stp (ADD _ _) => o2 ho2
  stp (MUL _ _) => o3 ho3
  stp (ADD _ _) => o4 ho4
  stp (MUL _ _) => o5 ho5
  stp (ADD _ _) => o6 ho6
  stp (MUL _ _) => o7 ho7
  stp (ADD _ _) => o8 ho8
  stp (MUL _ _) => o9 ho9
  stp (ADD _ _) => opened hopened
  have hOp : V opened = Formula.opened I := by
    rw [hopened, ho5, ho9, ho1, ho4, ho8, ho3, ho7, ho2, ho6, hR2, hone, hρ,
      show V (leaves₀.a.getD 0 0) = _ from hI.a0, show V (leaves₀.a.getD 1 0) = _ from hI.a1,
      show V (leaves₀.a.getD 2 0) = _ from hI.a2, show V (leaves₀.a.getD 3 0) = _ from hI.a3]
    rfl
  stp (CNST _) => sc hsc
  have hSc : V sc = extension.2 := by rw [hsc, elem_scale]
  stp (ADD _ _) => i1 hi1
  stp (MUL _ _) => i2 hi2
  stp (MUL _ _) => i3 hi3
  stp (MUL _ _) => i4 hi4
  stp (MUL _ _) => i5 hi5
  stp (ADD _ _) => identities hidentities
  have hId : V identities = Formula.identities I := by
    rw [hidentities, hi3, hi2, hi1, hi5, hi4, hone, hρ, hA.copies, hA.rows, hA.product, hA.gate]; rfl
  stp (MUL _ _) => wmc hwmc
  stp (CNST _) => cy0 hcy0
  stp (CNST _) => cy1 hcy1
  stp (MUL _ _) => qv0 hqv0
  stp (MUL _ _) => qv1 hqv1
  stp (MUL _ _) => qv2 hqv2
  stp (MUL _ _) => quotientValue hquotientValue
  have hQV : V quotientValue = Formula.quotientValue I := by
    rw [hquotientValue, hqv2, hqv1, hqv0, hSc, hQS, hInv 26 (by norm_num), hInv 27 (by norm_num), hId]
    rfl
  have hQP : (u ++ [wmc, leaves₀.rho, cy0, cy1]).map V = Formula.quotientPoint I := by
    rw [List.map_append, hU]
    simp only [List.map_cons, List.map_nil, Formula.quotientPoint]
    rw [hwmc, hW 24 (by norm_num), hInv 26 (by norm_num), hρ, hcy0, hcy1, elem_y0, elem_y1]
    rfl
  stp (parts_spec (e := e) I _ hQP) => pr hpr
  obtain ⟨hPt, qPt, gPt, qW, gW⟩ := pr
  obtain ⟨hhPt, hqPt, hgPt, hqW, hgW⟩ := hpr
  dsimp only at hhPt hqPt hgPt hqW hgW ⊢
  stp (ADD _ _) => hi0 hhi0
  stp (ADD _ _) => cw hcw
  stp (MUL _ _) => hi1 hhi1
  stp (MUL _ _) => hi2 hhi2
  stp (MUL _ _) => hInverse hhInverse
  have hHI : V hInverse = Formula.hInverse I := by
    rw [hhInverse, hhi2, hhi1, hhi0, hcw, hone, hW 25 (by norm_num), hW 24 (by norm_num), hA.product,
      hInv 28 (by norm_num), hInv 29 (by norm_num)]
    rfl
  stp (MUL _ _) => hv0 hhv0
  stp (ADD _ _) => hv1 hhv1
  stp (MUL _ _) => hv2 hhv2
  stp (ADD _ _) => hv3 hhv3
  stp (MUL _ _) => hVal hhVal
  stp (MUL _ _) => wv0 hwv0
  stp (MUL _ _) => wVal hwVal
  stp (MUL _ _) => fVal hfVal
  stp (MUL _ _) => sum hsum
  apply Spec.pure
  refine ⟨?_, ?_, ?_, ?_, hhPt, ?_, hqPt, hgPt, ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil, List.map_take, List.map_drop, hU, hR2, hρ]
    rfl
  · rw [hwVal, hwv0, hOp, hMid, hInv 24 (by norm_num)]; rfl
  · rw [List.map_take, hU]; rfl
  · rw [hfVal, hWS, show V leaves₀.next = I.next from hI.next]; rfl
  · rw [hhVal, hhv3, hhv1, hhv0, hhv2, hQV, hqW, hgW, hHI, show V leaves₀.qv = I.qValue from hI.qv,
      show V leaves₀.gv = I.gValue from hI.gv]
    rfl
  · rw [hsum, hSc, hA.target]; rfl

/-- **What the graph's claim nodes hold.** The nodes `reduceIds` leaves (the graph's, `reduceIds_eq`)
hold the Statement's claims at the leaves' values, when the denominators do not vanish. -/
theorem reduceIds_spec (I : Formula.Vals) (hI : LeafOK e I) (hnz : (Formula.denominators I).prod ≠ 0) :
    Spec reduceIds fun o =>
      o.wPt.map V = (Formula.claims I).witness.point ∧ V o.wVal = (Formula.claims I).witness.value ∧
      o.fPt.map V = (Formula.claims I).wiring.point ∧ V o.fVal = (Formula.claims I).wiring.value ∧
      o.hPt.map V = (Formula.claims I).h.point ∧ V o.hVal = (Formula.claims I).h.value ∧
      o.qPt.map V = (Formula.claims I).q.point ∧ o.gPt.map V = (Formula.claims I).g.point ∧
      V o.sum = (Formula.claims I).sum.value := by
  unfold reduceIds
  rw [chain_eq]
  apply Spec.bind
  apply Spec.some
  stp (stageA_spec (e := e) I hI) => A hA
  stp (stageB_spec (e := e) I hI A hA) => B hB
  exact stageC_spec I hI A hA B hB hnz

end Implementation
