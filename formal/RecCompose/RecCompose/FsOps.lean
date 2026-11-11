-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md; conventions: see AGENTS.md. The port of
-- `formal/UniSound/UniSound/FsOps.lean` and `FsProof.lean`'s facts (`hok_uni`, `hcov_uni`, `hS_uni`, `maxErrK_uni`) to
-- π2's openings on the EIP's PCS claims, after `formal/UniKeccakSound/UniKeccakSound/Fs/ProofK.lean` (`hok_uniK`,
-- `hU_uniK`: the openings charged once through `WhirBridge.Pcs.pcs_union_sound`).
import RecCompose.FsDefs
import RecCompose.Tables
import Bridge.Verifier

/-!
# π2's openings: what the framework needs of them

* **the run's points** have their stacks' variables (`p2Out_witnessPoint_length`, …: `24`, `25`, `28`);
* **a PCS claim's point claim on a stack is `ClaimOn`** (`colEval_iff_claimOn`): the stack's polynomial
  (`WhirBridge.Pcs.colEval`, `eq` of the point and a word's bits) is its multilinear extension (`UniSound.mleStk`);
* **the openings' `OKP`** (`okp_W`, `okp_Q`: the decoders list the candidates' stacks, a stack satisfying the
  opening's claims is good; π1's three: no stack, `okp_pi1`); `hcov`, `hfit`, and **`hS`** (the setup's claim on its
  table, from its opening);
* **the eight openings once** (`hU_pcs`): each opening's statement is one of `WhirBridge.Pcs.pcs_union_sound`'s
  union over version 1's sizes `2^23 ..= 2^28` at `εExact` (`UniKeccakSound.pcsKShapes`), for any list of
  `PcsOp`s: `Compose.GUnionSound` at `(QA + 10122) (εExact + 5 (QA + 10122) / 2^256)`;
* the decoders' lists (`L_W = 9952`, `L_Q = 3564`) and `maxErrK` (`maxErrK_p2`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

-- `Layers.lean`'s instance of `SampleableType E` (the one `Pi2FsLayer`'s protocols are at), not `Completeness`'s.
attribute [local instance high] LeanVM.Protocol.instSampleableTypeE

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge Finset
open OracleSpec OracleComp
open LeanVM.Protocol.Rom (romExperiment romExperiment_map romExperiment_eq)
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.setupStack

theorem cc_logN : cc.logN = 24 := rfl

theorem cc_logRow : cc.logRow = 4 := rfl

/-! ## The run's points -/

theorem padded_length {F : Type} [Field F] (p : List F) (n : ℕ) : (padded p n).length = n := by
  simp [padded]

theorem p2Out_witnessPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).witnessPoint.length = 24 := by
  unfold p2Out
  rw [run_witnessPoint, padded_length, spec_core_logN, cc_logN]
  rfl

theorem p2Out_setupPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).setupPoint.length = 25 := by
  unfold p2Out
  rw [run_setupPoint, padded_length, spec_core_logN, cc_logN]
  rfl

theorem p2Out_quotientPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).quotientPoint.length = 28 := by
  unfold p2Out
  rw [run_quotientPoint, padded_length, spec_core_logN, cc_logN]
  rfl

theorem p2Out_pushesPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).pushesPoint.length = 28 := by
  unfold p2Out
  rw [run_pushesPoint, padded_length, spec_core_logN, cc_logN]
  rfl

theorem p2Out_sumPoint_length (π : P2Pf) (ch : List (List E)) : (p2Out π ch).sumPoint.length = 28 := by
  unfold p2Out
  rw [run_sumPoint, padded_length, spec_core_logN, cc_logN]
  rfl

/-! ## A PCS claim's point claim is `ClaimOn` -/

/-- **A stack's polynomial at a point of its variables is its multilinear extension** (`UniSound.mleStk`, `ClaimOn`'s),
for a stack whose words below `2^n` are the column's. -/
theorem colEval_eq_mle {n : ℕ} (q : Column n) (s : Stk) (hs : ∀ i < 2 ^ n, q.values.getD i 0 = s i)
    (pt : List E) (hp : pt.length = n) : Pcs.colEval q pt = UniSound.mleStk s n pt := by
  unfold Pcs.colEval UniSound.mleStk
  refine Finset.sum_congr rfl fun x _ => ?_
  have he := UniSound.eqEval_boolPoint x.val pt
  rw [hp] at he
  rw [LeanVM.Protocol.Whir.Complete.eqEval_comm, he, hs x.val x.isLt]

theorem colEval_iff_claimOn {n : ℕ} (q : Column n) (s : Stk) (hs : ∀ i < 2 ^ n, q.values.getD i 0 = s i)
    (pt : List E) (v : E) (hp : pt.length = n) : Pcs.colEval q pt = v ↔ ClaimOn n s (pt, v) := by
  rw [colEval_eq_mle q s hs pt hp]
  rfl

/-- A round's candidate read back is the column's words (`rdP`, the plain layout's table, `2^23 ..= 2^28` words). -/
theorem rdP_getD (n : ℕ) (h1 : 23 ≤ n) (h2 : n ≤ 28) (q : Column n) (i : ℕ) (hi : i < 2 ^ n) :
    q.values.getD i 0 = rdP n q i := by
  unfold rdP UniSound.rdTab
  have hi' : i < 2 ^ (UniSound.plainL n).vars := hi
  rw [dite_eq_left hi']
  simp only [tabOf, Vector.getElem_ofFn]
  exact (UniKeccakSound.plainL_tableK n h1 h2 q i hi).symm

/-- A column of an array's words is the array's words below `2^n`. -/
theorem colOf_getD (a : Array K) (n i : ℕ) (hi : i < 2 ^ n) :
    (UniSound.colOf a n).values.getD i 0 = a.getD i 0 := by
  simp [UniSound.colOf, Vector.getD, hi]

/-! ## The openings' `OKP` -/

section Facts

variable (D : RecDeployment) (hs : UniKeccakSound.UniShapesK D.pi1)

/-- `W`'s opening (`p2Pcs5`'s fourth). -/
noncomputable abbrev wOp : GOp P2Pf E Stk :=
  PcsOp.gop ⟨24, by norm_num, by norm_num, wCl, fun π => π.proof.w, .round 0 (rdP 24)⟩

theorem p2Tc_zero : p2Tc 0 = tableCode (UniSound.plainL 24) logInvRate (shK 24 (by norm_num) (by norm_num)).adm
    UniSound.rdTab := by
  unfold p2Tc
  rw [ite_eq_left rfl]

theorem p2Tc_one : p2Tc 1 = tableCode (UniSound.plainL 28) logInvRate (shK 28 (by norm_num) (by norm_num)).adm
    UniSound.rdTab := by
  unfold p2Tc
  rw [ite_eq_right (by decide)]

/-- **`W`'s opening's `OKP`**: its decoder lists the candidates' stacks, and a stack its claim holds of satisfies
`W`'s claim (`ClaimOn`). -/
theorem okp_W : GOp.OKP p2Tc p2Good (p2Setup D hs) p2Fix (p2Stk D) wOp := by
  refine gop_okp_tableCode (UniSound.plainL 24) logInvRate (shK 24 (by norm_num) (by norm_num)).adm _ _ _
    (fun r π ch => PcsOp.queries _ r π ch) (fun r π ch => PcsOp.duplex _ r π ch) 0 UniSound.rdTab p2Tc p2Tc_zero
    p2Good (fun π ch q h => ?_) _ _ _
  obtain ⟨ood, pt, v, hcl, hl, -, hv⟩ := h
  simp only [wCl, Option.some.injEq, Prod.mk.injEq] at hcl
  obtain ⟨-, rfl, rfl⟩ := hcl
  rw [p2Good, ite_eq_left rfl]
  exact ⟨_, rfl, (colEval_iff_claimOn q _ (rdP_getD 24 (by norm_num) (by norm_num) q) _ _ hl).1 hv⟩

theorem claim_of_holdsQ (o : PcsOp) (ho : o.n = 28) (pt : List E) (v : E) {π : P2Pf} {ch : List (List E)}
    {q : Column 28} (hcl : ∀ ood pt' v', o.cl π ch = some (ood, pt', v') → pt' = pt ∧ v' = v)
    (h : o.holds π ch (cast (by rw [ho]) q)) : ClaimOn 28 (rdP 28 q) (pt, v) := by
  obtain ⟨n, lo, hi, cl, prf, tgt⟩ := o
  simp only at ho
  subst ho
  obtain ⟨ood, pt', v', hc, hl, -, hv⟩ := h
  obtain ⟨rfl, rfl⟩ := hcl _ _ _ hc
  exact (colEval_iff_claimOn q _ (rdP_getD 28 (by norm_num) (by norm_num) q) _ _ hl).1 hv

/-- **`Q`'s opening's `OKP`** (its three claims as one opening): its decoder lists the candidates' stacks, and a
stack its three claims hold of satisfies `Q`'s three (`ClaimOn`). -/
theorem okp_Q : GOp.OKP p2Tc p2Good (p2Setup D hs) p2Fix (p2Stk D) qOp := by
  refine gop_okp_tableCode (UniSound.plainL 28) logInvRate (shK 28 (by norm_num) (by norm_num)).adm _ _ _
    qOp.queries qOp.duplex 1 UniSound.rdTab p2Tc p2Tc_one p2Good (fun π ch q h => ?_) _ _ _
  obtain ⟨h1, h2, h3⟩ := h
  rw [p2Good, ite_eq_right (by decide), ite_eq_left rfl]
  refine ⟨_, rfl, claim_of_holdsQ qIdOp rfl _ _ (fun _ _ _ hc => ?_) h1,
    claim_of_holdsQ qPushOp rfl _ _ (fun _ _ _ hc => ?_) h2, claim_of_holdsQ qSumOp rfl _ _ (fun _ _ _ hc => ?_) h3⟩
  · simp only [qIdOp, qIdCl, Option.some.injEq, Prod.mk.injEq] at hc
    exact ⟨hc.2.1.symm, hc.2.2.symm⟩
  · simp only [qPushOp, qPushCl, Option.some.injEq, Prod.mk.injEq] at hc
    exact ⟨hc.2.1.symm, hc.2.2.symm⟩
  · simp only [qSumOp, qSumCl, Option.some.injEq, Prod.mk.injEq] at hc
    exact ⟨hc.2.1.symm, hc.2.2.symm⟩

/-- **The other openings carry no stack** (their stacks are not of `2^25` words). -/
theorem p2StkNone (o : GOp P2Pf E Stk) (h : o.μ ≠ 25) : p2Stk D o = none := by
  unfold p2Stk
  split
  · next h' => exact absurd h' h
  · rfl

/-- **π1's openings' `OKP`**: setup openings without a stack. -/
theorem okp_pi1 (n : ℕ) (lo : 23 ≤ n) (hi : n ≤ 28) (hn : n ≠ 25)
    (cl : P2Pf → List (List E) → Option (E × List E × E)) (prf : P2Pf → Compile.Proof) (r : P2Pf → Bytes32)
    (q₀ : Column n) :
    GOp.OKP p2Tc p2Good (p2Setup D hs) p2Fix (p2Stk D) (PcsOp.gop ⟨n, lo, hi, cl, prf, .setup r q₀⟩) :=
  gop_okp_none _ _ _ _ _ _ r q₀ rfl (p2StkNone D _ hn)

/-- **Every round with a root is opened**: `W`'s and `Q`'s. -/
theorem hcov_p2 : ∀ i < pi2Spec.K.rounds.length, (pi2Spec.K.spec i).root →
    ∃ o ∈ p2Ops D, ∃ rd, o.tgt = .round i rd := by
  intro i hi hr
  have hi3 : i < 3 := hi
  interval_cases i
  · exact ⟨wOp, by simp [p2Ops, p2Pcs5, wOp], rdP 24, rfl⟩
  · exact ⟨qOp, by simp [p2Ops], rdP 28, rfl⟩
  · exact absurd hr (by decide)

/-- **The stream's messages fit the rounds.** -/
theorem hfit_p2 (π : P2Pf) : FitsAll pi2Spec.K.rounds (p2View π).2 :=
  UniSound.fitsAll_msgsAt _ _ _

/-- **The setup's claim on its table, from its opening's** (`GOp.SetupHoldsP` of the setup's opening, its stack the
setup's table at the proof's commitments). -/
theorem hS_p2 (π : P2Pf) (ch : List (List E))
    (h : ∀ o ∈ p2Ops D, GOp.SetupHoldsP (p2Stk D) o π ch) : p2GoodS D π ch := by
  have hm : (PcsOp.gop ⟨25, by norm_num, by norm_num, sCl, fun π => π.proof.setup,
      .setup (fun π => toB π.roots.pi2) (col0 _)⟩) ∈ p2Ops D := by
    simp [p2Ops, p2Pcs5]
  have h5 := h _ hm
  unfold GOp.SetupHoldsP at h5
  obtain ⟨ood, pt, v, hcl, hl, -, hv⟩ := h5 (fun π => setupCol D π.roots.pi1) rfl
  simp only [sCl, Option.some.injEq, Prod.mk.injEq] at hcl
  obtain ⟨-, rfl, rfl⟩ := hcl
  exact (colEval_iff_claimOn _ _ (fun i hi => colOf_getD _ 25 i hi) _ _ hl).1 hv

/-! ## The lists, `maxErrK` -/

theorem p2Tc_bound_zero : (p2Tc 0).commit.bound = 9952 := by
  rw [TableCode.commit_bound, p2Tc_zero]
  exact listHi_large 24 le_rfl (by decide)

theorem p2Tc_bound_one : (p2Tc 1).commit.bound = 3564 := by
  rw [TableCode.commit_bound, p2Tc_one]
  exact listHi_large 28 (by decide) le_rfl

/-- **The lists of the roots before round `j`** (`facL`): `L_W`, then `L_W L_Q`. -/
theorem facL_p2 : ∀ j < 3, facL (fun i => (p2Tc i).commit) 0 (pi2Spec.K.rounds.take (j + 1)) = pi2Fac j := by
  intro j hj
  interval_cases j
  · rw [show pi2Spec.K.rounds.take (0 + 1) = [⟨true, 1, 2⟩] from rfl]
    simp only [facL, ite_true, p2Tc_bound_zero, mul_one]
    rfl
  · rw [show pi2Spec.K.rounds.take (1 + 1) = [⟨true, 1, 2⟩, ⟨true, 1, 0⟩] from rfl]
    simp only [facL, ite_true, Nat.reduceAdd, p2Tc_bound_zero, p2Tc_bound_one, mul_one]
    rfl
  · rw [show pi2Spec.K.rounds.take (2 + 1) = RecPiop.pi2Rounds 4 from rfl]
    simp only [RecPiop.pi2Rounds, facL, ite_true, Nat.reduceAdd, p2Tc_bound_zero, p2Tc_bound_one, mul_one,
      Bool.false_eq_true, ite_false]
    rfl

/-- **The rounds' errors times their lists** are at most `e` when each round's error times `pi2Fac` is. -/
theorem maxErrK_p2 (R : Compose.Piop pi2Spec.K Stk) (e : ℝ≥0∞)
    (herr : ∀ j < 3, (pi2Fac j : ℝ≥0∞) * R.err j ≤ e) :
    maxErrK pi2Spec.K (fun i => (p2Tc i).commit) R ≤ e := by
  unfold maxErrK
  refine Finset.sup_le fun j hj => ?_
  have hj3 : j < 3 := Finset.mem_range.mp hj
  rw [facL_p2 j hj3]
  exact herr j hj3

end Facts

/-! ## The openings once: the PCS union -/

section Union

/-- **An opening's statement in the PCS union**: its size's index, its PCS claim (the root it reads, the
out-of-domain answer, the point and value), its opening proof; a dummy claim where it has no claim or its point has not
its stack's variables (the opening rejects there). -/
noncomputable def PcsOp.stmt (o : PcsOp) (π : P2Pf) (ch : List (List E)) : Pcs.PSt UniKeccakSound.pcsKShapes × Proof :=
  match o.cl π ch with
  | some (ood, pt, v) =>
    if h : pt.length = o.n then
      (⟨UniKeccakSound.pcsIdxK o.n, ⟨ofB (o.rootB π), ood, pt, v,
        h.trans (UniKeccakSound.pcsIdxK_n _ o.lo o.hi).symm⟩⟩, o.prf π)
    else (⟨UniKeccakSound.pcsIdxK 23, Pcs.dummy _⟩, o.prf π)
  | none => (⟨UniKeccakSound.pcsIdxK 23, Pcs.dummy _⟩, o.prf π)

/-- An opening has a claim of its stack's variables. -/
def PcsOp.Ok (o : PcsOp) (π : P2Pf) (ch : List (List E)) : Prop :=
  ∃ ood pt v, o.cl π ch = some (ood, pt, v) ∧ pt.length = o.n

/-- The root a `PcsOp`'s `GOp` reads is its `rootB`. -/
theorem PcsOp.root_gop (o : PcsOp) (π : P2Pf) : GOp.root p2View o.gop π = o.rootB π := by
  obtain ⟨n, lo, hi, cl, prf, tgt⟩ := o
  cases tgt <;> rfl

/-- **An opening's run is the union's verifier on its statement**, where it has a claim of its stack's variables. -/
theorem PcsOp.run_ok (o : PcsOp) (π : P2Pf) (ch : List (List E)) (hok : o.Ok π ch) :
    GOp.run p2View o.gop π ch = Pcs.pUVer UniKeccakSound.pcsKShapes Pcs.oodPoint (o.stmt π ch) := by
  obtain ⟨ood, pt, v, hc, hl⟩ := hok
  unfold GOp.run
  rw [PcsOp.root_gop]
  show o.ver _ π ch = _
  unfold PcsOp.ver PcsOp.stmt
  rw [hc]
  dsimp only
  rw [dite_eq_left hl]
  unfold UniKeccakSound.pcsOpenC Pcs.pUVer
  rw [dite_eq_left hl]
  exact (UniKeccakSound.pcsVerifier_congrK (UniKeccakSound.pcsIdxK_n _ o.lo o.hi) _ _ _ _ hl _ _).symm

/-- **An opening without a claim of its stack's variables rejects.** -/
theorem PcsOp.run_nok (o : PcsOp) (π : P2Pf) (ch : List (List E)) (hok : ¬ o.Ok π ch) :
    GOp.run p2View o.gop π ch = pure false := by
  unfold GOp.run
  show o.ver _ π ch = _
  unfold PcsOp.ver
  rcases hc : o.cl π ch with _ | ⟨ood, pt, v⟩
  · rfl
  · dsimp only
    unfold UniKeccakSound.pcsOpenC
    have hl : ¬ pt.length = o.n := fun hl => hok ⟨ood, pt, v, hc, hl⟩
    rw [dite_eq_right hl]

/-- **An opening's doom is the union's on its statement**, where it has a claim of its stack's variables. -/
theorem PcsOp.doomed_imp (o : PcsOp) (π : P2Pf) (ch : List (List E)) (c : KeccakCalls.QueryCache)
    (hok : o.Ok π ch) (hd : GDoomed p2View o.gop π ch c) :
    Pcs.PUDoomed UniKeccakSound.pcsKShapes Pcs.oodPoint (o.stmt π ch) c := by
  obtain ⟨ood, pt, v, hc, hl⟩ := hok
  unfold Pcs.PUDoomed PcsOp.stmt
  rw [hc]
  dsimp only
  rw [dite_eq_left hl]
  refine (UniKeccakSound.pcsDoomed_congrK (UniKeccakSound.pcsIdxK_n _ o.lo o.hi) _ _ _ _ hl _ _ c).2
    fun q hq => ?_
  by_contra hn
  simp only [not_or, not_not] at hn
  refine hd q ?_ ⟨ood, pt, v, hc, hl, hn.1, hn.2⟩
  rw [PcsOp.root_gop]
  exact hq

/-- The union's bound at `QA` queries: `(QA + 10122) (εExact + 5 (QA + 10122) / 2^256)`. -/
noncomputable def bndU (QA : ℕ) : ℝ≥0∞ :=
  ((QA + 10122 : ℕ) : ℝ≥0∞) * (εExact + ((5 * (QA + 10122) : ℕ) : ℝ≥0∞) / 2 ^ 256)

/-- **Any list of PCS claims' openings, charged once**: their union is sound at `bndU`
(`WhirBridge.Pcs.pcs_union_sound` over `UniKeccakSound.pcsKShapes`). -/
theorem hU_pcs (L : List PcsOp) : GUnionSound p2View (L.map PcsOp.gop) bndU := by
  classical
  intro A QA hA
  set f : GUIn (L.map PcsOp.gop) → PcsOp := fun w => L[w.1.val]'(by simpa using w.1.isLt) with hf
  have hget : ∀ w : GUIn (L.map PcsOp.gop), (L.map PcsOp.gop).get w.1 = (f w).gop := by
    intro w
    simp [hf]
  refine (UniKeccakSound.romExperiment_le_map A _ (Pcs.pUVer UniKeccakSound.pcsKShapes Pcs.oodPoint)
    (fun w => (f w).stmt w.2.1 w.2.2) (fun w => (f w).Ok w.2.1 w.2.2) (fun w => ?_) _
    (Pcs.PUDoomed UniKeccakSound.pcsKShapes Pcs.oodPoint) (fun w c hok hd => ?_)).trans
    (Pcs.pcs_union_sound UniKeccakSound.pcsKShapes Pcs.oodPoint _ QA ((isQueryBound_map_iff _ _ _ _ _).mpr hA)
      10122 UniKeccakSound.pcsKShapes_QO)
  · show GOp.run p2View ((L.map PcsOp.gop).get w.1) w.2.1 w.2.2 = _
    rw [hget]
    by_cases hok : (f w).Ok w.2.1 w.2.2
    · rw [ite_eq_left hok]
      exact PcsOp.run_ok _ _ _ hok
    · rw [ite_eq_right hok]
      exact PcsOp.run_nok _ _ _ hok
  · refine PcsOp.doomed_imp _ _ _ c hok ?_
    have : GDoomed p2View ((L.map PcsOp.gop).get w.1) w.2.1 w.2.2 c := hd
    rwa [hget] at this

end Union

/-! ## The openings' runs -/

/-- The openings' verdicts have their count. -/
theorem length_of_mem_gopsRun (π : P2Pf) (ch : List (List E)) :
    ∀ (L : List (GOp P2Pf E Stk)) (bs : List Bool), bs ∈ support (gopsRun p2View L π ch) → bs.length = L.length
  | [], bs, h => by
    simp only [gopsRun, support_pure, Set.mem_singleton_iff] at h
    subst h
    rfl
  | o :: L, bs, h => by
    simp only [gopsRun, mem_support_bind_iff, support_map, Set.mem_image] at h
    obtain ⟨b, -, bs', hbs', rfl⟩ := h
    simp [length_of_mem_gopsRun π ch L bs' hbs']

/-- The eight verdicts as the composition's six: the first five, then `Q`'s three and-ed. -/
def mergeB (bs : List Bool) : List Bool :=
  (List.range 5).map (bs.getD · false) ++ [bs.getD 5 false && (bs.getD 6 false && bs.getD 7 false)]

/-- **The composition's openings run the eight**, `Q`'s three as one. -/
theorem gopsRun_p2Ops (D : RecDeployment) (π : P2Pf) (ch : List (List E)) :
    gopsRun p2View (p2Ops D) π ch = mergeB <$> gopsRun p2View (p2Ops8 D) π ch := by
  simp only [p2Ops, p2Ops8, p2Pcs, p2Pcs5, List.map_cons, List.map_nil, List.cons_append, List.nil_append, gopsRun,
    map_bind, map_pure]
  refine bind_congr fun b1 => bind_congr fun b2 => bind_congr fun b3 => bind_congr fun b4 =>
    bind_congr fun b5 => ?_
  simp only [GOp.run, qOp, PcsOp.gop, bind_assoc, pure_bind]
  rfl

end RecCompose

/-- info: 'RecCompose.hS_p2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.hS_p2

/-- info: 'RecCompose.maxErrK_p2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.maxErrK_p2

/-- info: 'RecCompose.hU_pcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.hU_pcs
