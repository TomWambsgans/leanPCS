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
set_option maxHeartbeats 4000000

namespace Implementation

open LeanVM.Parameters PcsQuotient PcsQuotient.Domain Program Emitted

variable {e : Env}

local notation "V" => val limbsEquiv e
local notation "EL" => elem limbsEquiv
local notation "hF" => isF192_primitives
local notation "MUL" => mul_spec (e := e) isF192_primitives
local notation "ADD" => add_spec (e := e) isF192_primitives
local notation "CNST" => cnst_spec (e := e) isF192_primitives

/-- **The leaves hold `I`**: the statement's eight words, the challenges, the three values, `next`. -/
structure LeafOK (e : Env) (I : Formula.Vals) : Prop where
  s : ∀ k < 8, val limbsEquiv e (leaves₀.s.getD k 0) = ofK (I.stmt.words.getD k 0)
  α : val limbsEquiv e 14 = I.α
  β : val limbsEquiv e 16 = I.β
  μ : val limbsEquiv e 18 = I.μ
  t : val limbsEquiv e 23 = I.t
  x : val limbsEquiv e 24 = I.v[0]
  c : val limbsEquiv e 25 = I.v[1]
  vy : val limbsEquiv e 26 = I.v[2]
  next : val limbsEquiv e 27 = I.next
  ρ : val limbsEquiv e 29 = I.ρ

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

theorem wAt_eq (I : Formula.Vals) (k : ℕ) (hk : k < 25) : Formula.wAt I k = sq^[k] I.t :=
  (wfold_spec I.t 24).2 k (by omega)

/-! ## The stages -/

variable (e) in
/-- What the first stage leaves (`stageA`). -/
structure AOK (I : Formula.Vals) (A : StageA) : Prop where
  w : ∀ k < 25, val limbsEquiv e (A.w.getD k 0) = Formula.wAt I k
  gate : val limbsEquiv e A.gate = Formula.gate I
  rows : val limbsEquiv e A.rows = Formula.rows I
  d : val limbsEquiv e A.d = Formula.d I
  dNext : val limbsEquiv e A.dNext = Formula.dNext I
  product : val limbsEquiv e A.product = Formula.product I
  zeta : val limbsEquiv e A.zeta = Formula.zeta I
  theta : val limbsEquiv e A.theta = ofK (betaAt 1)
  conicA : val limbsEquiv e A.conicA = Formula.conicA I
  conicB : val limbsEquiv e A.conicB = Formula.conicB I

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
  have hx : V (leaves₀.v.getD 0 0) = Formula.x I := hI.x
  have hc : V (leaves₀.v.getD 1 0) = Formula.c I := hI.c
  have hvy : V (leaves₀.v.getD 2 0) = Formula.vy I := hI.vy
  have ht : V leaves₀.t = I.t := hI.t
  have hρ : V leaves₀.rho = I.ρ := hI.ρ
  -- the `w` chain
  stp (wChain_spec (e := e) hF 23 24) => w hw
  obtain ⟨hwlen, hwv⟩ := hw
  have hW : ∀ k < 25, V (w.getD k 0) = Formula.wAt I k := fun k hk => by
    rw [hwv k hk, wAt_eq I k hk]
    show sq^[k] (V 23) = _
    rw [hI.t]
  -- the gate
  stp (ADD _ _) => g1 hg1
  stp (MUL _ _) => g2 hg2
  stp (ADD _ _) => gate hgate
  have hG : V gate = Formula.gate I := by rw [hgate, hg1, hg2, hx, hc, hvy]; rfl
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
  -- the denominators' pieces
  stp (ADD _ _) => ax hax
  stp (MUL _ _) => bt hbt
  stp (ADD _ _) => d hd
  stp (MUL _ _) => bn hbn
  stp (ADD _ _) => dNext hdNext
  stp (MUL _ _) => product hproduct
  stp (MUL _ _) => zeta hzeta
  have hα : V leaves₀.alpha = I.α := hI.α
  have hβ : V leaves₀.beta = I.β := hI.β
  have hn : V leaves₀.next = I.next := hI.next
  have hD : V d = Formula.d I := by rw [hd, hax, hbt, hx, hα, hβ, ht]; rfl
  have hDN : V dNext = Formula.dNext I := by rw [hdNext, hax, hbn, hx, hα, hβ, hn]; rfl
  have hPr : V product = Formula.product I := by rw [hproduct, hD, hDN]; rfl
  have hZ : V zeta = Formula.zeta I := by rw [hzeta, hW 24 (by norm_num), ht]; rfl
  -- the conic
  stp (CNST _) => theta htheta
  have hθ : V theta = ofK (betaAt 1) := by rw [htheta, elem_theta]
  stp (ADD _ _) => rho1 hrho1
  stp (MUL _ _) => ot hot
  stp (ADD _ _) => tot htot
  stp (MUL _ _) => ca0 hca0
  stp (ADD _ _) => conicA hconicA
  stp (MUL _ _) => conicB hconicB
  apply Spec.pure
  refine ⟨hW, hG, hR, hD, hDN, hPr, hZ, hθ, ?_, ?_⟩
  · rw [hconicA, hca0, htot, hot, hrho1, hW 1 (by norm_num), hθ, hone, ht, hρ]; rfl
  · rw [hconicB, hrho1, hθ, hone, hρ]; rfl

theorem pinPoints_length : PcsQuotient.pinPoints.length = 11 := by
  simp [PcsQuotient.pinPoints, publicRows, publicWords]

theorem denominators_length (I : Formula.Vals) : (Formula.denominators I).length = 39 := by
  simp [Formula.denominators, pinPoints_length, Formula.m, cellVars, PcsQuotient.logRows]

theorem stageB_spec (I : Formula.Vals) (hI : LeafOK e I) (A : StageA) (hA : AOK e I A) :
    Spec (stageB leaves₀ A) (BOK e I) := by
  have hone := one_val (e := e)
  have ht : V leaves₀.t = I.t := hI.t
  unfold stageB
  stp (mapO_spec (e := e) hF (fun k => 1 + Formula.wAt I k) (List.range 24)
    (fun k hk => (ADD _ _).weaken fun r hr => by rw [hr, hone, hA.w k (by simp at hk; omega)])) => ws hws
  stp (ADD _ _) => oz hoz
  stp (ADD _ _) => zp hzp
  stp (mapO_spec (e := e) hF (fun k => I.t + ofK (PcsQuotient.pinPoints.getD k 0)) (List.range 11)
    (fun k hk => by
      stp (CNST _) => p hp
      exact (ADD _ _).weaken fun r hr => by rw [hr, hp, ht, elem_pinPoint])) => ps hps
  stp (ADD _ _) => ab hab
  stp (prefixes_spec (e := e) hF (ws ++ [oz, zp, A.rows] ++ ps ++ [ab]) leaves₀.one) => pre hpre
  obtain ⟨-, hprev⟩ := hpre
  apply Spec.pure
  refine ⟨?_, fun i hi => by rw [hprev i hi, hone, one_mul], rfl⟩
  have hpp : PcsQuotient.pinPoints.map (fun p ↦ I.t + ofK p) =
      (List.range 11).map (fun k => I.t + ofK (PcsQuotient.pinPoints.getD k 0)) := by
    apply List.ext_getElem (by simp [pinPoints_length])
    intro k h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < PcsQuotient.pinPoints.length by
      simpa using h1)]
  simp only [List.map_append, List.map_cons, List.map_nil, hws, hps, hoz, hzp, hab, hone, hA.zeta, hA.product,
    hA.rows, hA.conicA, hA.conicB, Formula.denominators, hpp, Formula.m, cellVars, PcsQuotient.logRows]

theorem dens_length (I : Formula.Vals) (B : StageB) (hB : BOK e I B) : B.dens.length = 39 := by
  have := congrArg List.length hB.dens
  simp only [List.length_map, denominators_length] at this
  exact this

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

theorem prod_take_eq (l : List Nat) (i : Nat) (hi : i ≤ l.length) :
    ((l.take i).map V).prod = ((List.range i).map fun j => V (l.getD j 0)).prod := by
  have e : (l.take i).map V = (List.range i).map fun j => V (l.getD j 0) := by
    apply List.ext_getElem (by simp; omega)
    intro j h1 h2
    simp only [List.length_map, List.length_take, List.length_range] at h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < l.length by omega)]
  rw [e]

/-- The pins' fold step on the graph is the Statement's. -/
theorem pinStep_spec (I : Formula.Vals) (hI : LeafOK e I) (pinInv : Nat → Nat)
    (hpi : ∀ k < 11, V (pinInv k) = Formula.pinInverse I k) (acc k : Nat) (hk : k < 11) :
    Spec (pinStep leaves₀ pinInv acc k) fun r => V r = Formula.pinStep I (V acc) k := by
  unfold pinStep Formula.pinStep
  by_cases h8 : k < 8
  · rw [if_pos h8, if_pos (show k < publicWords by simp [publicWords]; omega)]
    stp (CNST _) => lam hlam
    stp (MUL _ _) => weight hweight
    stp (MUL _ _) => term hterm
    refine (ADD _ _).weaken fun r hr => ?_
    rw [hr, hterm, hweight, hlam, hI.s k h8, elem_pinWeight k hk, hpi k hk]
  · rcases (by omega : k = 8 ∨ k = 9 ∨ k = 10) with rfl | rfl | rfl
    · have hv : anchorValues I.stmt.words 8 = 0 := rfl
      rw [if_neg (show ¬ (8 : ℕ) < 8 by decide), if_pos rfl, if_neg (show ¬ (8 : ℕ) < publicWords by decide), hv,
        if_pos rfl]
      exact Spec.some rfl
    · have hv : anchorValues I.stmt.words 9 = 1 := rfl
      have hc := elem_pinConst 9 (by omega) I.stmt.words
      rw [if_pos rfl] at hc
      rw [if_neg (show ¬ (9 : ℕ) < 8 by decide), if_neg (show ¬ (9 : ℕ) = 8 by decide),
        if_neg (show ¬ (9 : ℕ) < publicWords by decide), hv, if_neg one_ne_zero, if_pos rfl]
      stp (CNST _) => weight hweight
      stp (MUL _ _) => term hterm
      refine (ADD _ _).weaken fun r hr => ?_
      rw [hr, hterm, hweight, hc, hpi 9 hk, hv]
    · have hv : anchorValues I.stmt.words 10 = three := rfl
      have h3 : three ≠ 0 := by decide
      have hc := elem_pinConst 10 (by omega) I.stmt.words
      rw [if_neg (show ¬ (10 : ℕ) = 9 by decide)] at hc
      rw [if_neg (show ¬ (10 : ℕ) < 8 by decide), if_neg (show ¬ (10 : ℕ) = 8 by decide),
        if_neg (show ¬ (10 : ℕ) < publicWords by decide), hv, if_neg h3,
        if_neg (show ¬ (10 : ℕ) = 9 by decide)]
      stp (CNST _) => weight hweight
      stp (MUL _ _) => term hterm
      refine (ADD _ _).weaken fun r hr => ?_
      rw [hr, hterm, hweight, hc, hpi 10 hk, hv]

/-- **The claims' nodes** (`stageC`): when the denominators do not vanish, the nodes it leaves hold the
Statement's claims. -/
theorem stageC_spec (I : Formula.Vals) (hI : LeafOK e I) (A : StageA) (hA : AOK e I A) (B : StageB)
    (hB : BOK e I B) (hnz : (Formula.denominators I).prod ≠ 0) :
    Spec (stageC leaves₀ A B) fun o =>
      o.wPt.map V = (Formula.claims I).witness.point ∧ V o.wVal = (Formula.claims I).witness.value ∧
      o.fPt.map V = (Formula.claims I).wiring.point ∧ V o.fVal = (Formula.claims I).wiring.value ∧
      o.cPt.map V = (Formula.claims I).copy.point ∧ V o.cVal = (Formula.claims I).copy.value := by
  have hone := one_val (e := e)
  have hW := hA.w
  have hdlen := dens_length I B hB
  have hcheck := total_val I B hB
  have hρ : V leaves₀.rho = I.ρ := hI.ρ
  have ht : V leaves₀.t = I.t := hI.t
  have hx : V (leaves₀.v.getD 0 0) = Formula.x I := hI.x
  have hc : V (leaves₀.v.getD 1 0) = Formula.c I := hI.c
  have hvy : V (leaves₀.v.getD 2 0) = Formula.vy I := hI.vy
  unfold stageC
  -- the inverses
  stp (inverse_spec (e := e) hF (frobOK hF) _) => running hrunning
  set P : Nat → E := fun i => ((List.range i).map fun j => V (B.dens.getD j 0)).prod with hPdef
  have hPs : ∀ i, P (i + 1) = P i * V (B.dens.getD i 0) := fun i => by
    simp [hPdef, List.range_succ]
  have hPn : P B.dens.length = (Formula.denominators I).prod := by
    rw [hPdef]; dsimp only
    rw [← prod_take_eq _ _ le_rfl, List.take_length, hB.dens]
  stp (backInv_spec (e := e) hF (fun i => B.pre.getD i 0)
    (fun i => B.dens.getD i 0) P hPs _ running
    (fun i hi => by rw [hB.pre i hi.le, prod_take_eq _ _ hi.le])
    (by rw [hrunning, hcheck, hPn]) (by rw [hPn]; exact hnz)) => invsRev hinvs
  obtain ⟨-, hinvs⟩ := hinvs
  rw [hdlen] at hinvs
  have hInv : ∀ i < 39, V (invsRev.reverse.getD i 0) = Formula.inv I i := fun i hi => by
    rw [hinvs i hi, getD_of_map_eq hB.dens i (by rw [denominators_length]; exact hi), Formula.inv,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i < (Formula.denominators I).length by rw [denominators_length]; exact hi)]
    rfl
  stp (mapO_spec (e := e) hF (fun k => Formula.wAt I k * Formula.inv I k) (List.range 24)
    (fun k hk => (MUL _ _).weaken fun r hr => by
      have hk' : k < 24 := by simpa using hk
      rw [hr, hW k (by omega), hInv k (by omega)])) => u0 hu0
  stp (MUL _ _) => um hum
  have hU : (u0 ++ [um]).map V = Formula.u I := by
    rw [List.map_append, hu0, List.map_singleton, hum, hA.zeta, hInv 24 (by norm_num)]
    rfl
  stp (foldO_spec (e := e) hF (fun acc k => acc * Formula.inv I k)
    (List.range' 3 (24 - 3)) (fun acc k hk => (MUL _ _).weaken fun r hr => by
      have hk' : k < 24 := by simp at hk; omega
      rw [hr, hInv k (by omega)]) (invsRev.reverse.getD 2 0)) => middle hmiddle
  have hMid : V middle = Formula.middle I := by rw [hmiddle, hInv 2 (by norm_num)]; rfl
  stp (MUL _ _) => ws0 hws0
  stp (MUL _ _) => wiringScale hwiringScale
  have hWS : V wiringScale = Formula.wiringScale I := by
    rw [hwiringScale, hws0, hMid, hInv 0 (by norm_num), hInv 1 (by norm_num)]; rfl
  stp (MUL _ _) => tableScale htableScale
  have hTS : V tableScale = Formula.tableScale I := by
    rw [htableScale, hWS, hInv 24 (by norm_num)]; rfl
  -- `g(t)`
  have hpi : ∀ k < 11, V (invsRev.reverse.getD (24 + 3 + k) 0) = Formula.pinInverse I k := fun k hk => by
    rw [hInv _ (by omega)]; rfl
  stp (foldO_spec (e := e) hF (fun acc k => acc * Formula.pinInverse I k) (List.range 11)
    (fun acc k hk => (MUL _ _).weaken fun r hr => by
      rw [hr, hpi k (by simpa using hk)]) leaves₀.one) => pp hpp
  stp (MUL _ _) => p0 hp0
  stp (foldO_spec (e := e) hF (Formula.pinStep I) (List.range 11)
    (fun acc k hk => pinStep_spec I hI _ hpi acc k (by simpa using hk)) p0) => pinned hpinned
  have hPin : V pinned = Formula.pinned I := by
    rw [hpinned, hp0, hpp, hone, hx]; rfl
  stp (MUL _ _) => gr hgr
  stp (ADD _ _) => g hg
  have hG : V g = Formula.g I := by
    rw [hg, hgr, hA.gate, hInv 26 (by norm_num), hPin]; rfl
  -- the copy claim
  stp (CNST _) => sc hsc
  have hSc : V sc = extension.2 := by rw [hsc, elem_scale]
  stp (MUL _ _) => kappa hkappa
  have hK : V kappa = Formula.kappa I := by rw [hkappa, hA.product, hInv 25 (by norm_num)]; rfl
  stp (MUL _ _) => cv0 hcv0
  stp (MUL _ _) => cv1 hcv1
  stp (ADD _ _) => dd hdd
  stp (MUL _ _) => mz hmz
  stp (MUL _ _) => mzg hmzg
  stp (ADD _ _) => r hr
  stp (MUL _ _) => cv2 hcv2
  stp (MUL _ _) => cVal hcVal
  have hCV : V cVal = Formula.copyValue I := by
    rw [hcVal, hcv2, hcv1, hcv0, hr, hdd, hmzg, hmz, hSc, hTS, ht, hA.d, hA.dNext, hG, hW 24 (by norm_num),
      show V leaves₀.mu = I.μ from hI.μ, hInv 25 (by norm_num)]
    rfl
  -- the witness claim on the conic
  stp (MUL _ _) => z1 hz1
  have hZ1 : V z1 = Formula.z1 I := by rw [hz1, hA.conicA, hInv 38 (by norm_num)]; rfl
  stp (ADD _ _) => rho1 hrho1
  stp (ADD _ _) => z11 hz11
  stp (MUL _ _) => e00 he00
  stp (MUL _ _) => e01 he01
  stp (MUL _ _) => e11 he11
  stp (MUL _ _) => tho htho
  stp (ADD _ _) => k30 hk30
  stp (ADD _ _) => k31 hk31
  stp (ADD _ _) => k3 hk3
  stp (MUL _ _) => tw htw
  stp (MUL _ _) => twe htwe
  stp (ADD _ _) => l0 hl0
  stp (MUL _ _) => we hwe
  stp (ADD _ _) => ewe hewe
  stp (MUL _ _) => kk hkk
  stp (ADD _ _) => lambda1 hlambda1
  stp (ADD _ _) => lx hlx
  stp (ADD _ _) => lvy hlvy
  stp (MUL _ _) => o1 ho1
  stp (MUL _ _) => o2 ho2
  stp (ADD _ _) => o3 ho3
  stp (MUL _ _) => o4 ho4
  stp (ADD _ _) => opened hopened
  have hOp : V opened = Formula.opened I := by
    have hω : V (A.w.getD 1 0) = Formula.wAt I 1 := hW 1 (by norm_num)
    rw [hopened, ho3, ho4, ho1, ho2, hlvy, hlx, hlambda1, hl0, hkk, hewe, hwe, htwe, htw, hk3, hk31, hk30,
      htho, he11, he01, he00, hz11, hrho1, hZ1, hA.theta, hω, hone, hρ, ht, hx, hc, hvy]
    simp only [Formula.opened, Formula.lam, witnessWeights]
    try simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    try ring
  stp (MUL _ _) => wVal hwVal
  stp (MUL _ _) => fVal hfVal
  stp (CNST _) => cy0 hcy0
  stp (CNST _) => cy1 hcy1
  apply Spec.pure
  refine ⟨?_, ?_, ?_, ?_, ?_, hCV⟩
  · simp only [List.map_append, List.map_cons, List.map_nil, List.map_take, List.map_drop, hU, hρ, hZ1]
    rfl
  · rw [hwVal, hOp, hMid]; rfl
  · rw [List.map_take, hU]; rfl
  · rw [hfVal, hWS, show V leaves₀.next = I.next from hI.next]; rfl
  · simp only [List.map_append, List.map_cons, List.map_nil, hU, hcy0, hcy1, elem_y0, elem_y1, hK]
    rfl

/-- **What the graph's claim nodes hold.** The nodes `reduceIds` leaves (the graph's, `reduceIds_eq`)
hold the Statement's claims at the leaves' values, when the denominators do not vanish. -/
theorem reduceIds_spec (I : Formula.Vals) (hI : LeafOK e I) (hnz : (Formula.denominators I).prod ≠ 0) :
    Spec reduceIds fun o =>
      o.wPt.map V = (Formula.claims I).witness.point ∧ V o.wVal = (Formula.claims I).witness.value ∧
      o.fPt.map V = (Formula.claims I).wiring.point ∧ V o.fVal = (Formula.claims I).wiring.value ∧
      o.cPt.map V = (Formula.claims I).copy.point ∧ V o.cVal = (Formula.claims I).copy.value := by
  unfold reduceIds
  rw [chain_eq]
  apply Spec.bind
  apply Spec.some
  stp (stageA_spec (e := e) I hI) => A hA
  stp (stageB_spec (e := e) I hI A hA) => B hB
  exact stageC_spec I hI A hA B hB hnz

end Implementation
