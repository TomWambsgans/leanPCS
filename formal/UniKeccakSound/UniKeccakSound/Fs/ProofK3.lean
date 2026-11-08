-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The Keccak main line's `Fs/ProofK.lean` at π1-rec3's
-- shape, as `UniSound/Rec3/FsProof3.lean` is the BLAKE2s main line's `FsProof.lean`.
import UniKeccakSound.Fs.OpsK3
import UniKeccakSound.Fs.ProofK
import UniSound.Rec3.FsProof3

/-!
# The Keccak verifier at π1-rec3's shape: the composition's facts, the numbers

`ProofK.lean`'s facts at π1-rec3's rounds: the setup (`setupK1`, `uSetupK`, `uFixK`, `colFK`, `setupQSK_le`), the
claims (`claimsHoldK_of`) and the decoders' bound (`uniTcK_bound`) are the main line's; the openings match
(`hok_uniK3`), every round with a root is opened (`hcov_uniK3`: `root_rec3Rounds`), the setup's stack satisfies its
claim (`hS_uniK3`), the last link (`hlink_uniK3`, from `FsLayer128K3`'s), the event (`UniBreaksRelK3`), the numbers
(`UniNumbersK3`, `uniNumbersK3_of`), the chain's lists (`maxErrK_uniK3`: two roots, `countP_root_rec3Rounds`).
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open LeanVM.Rpm (Short hashBlocks)
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.layoutWordsK UniKeccak.setupStackK

/-! ## The composition's facts -/

section Facts

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (F3 : KFlockSound F κ keccakRec3) (nV np : ℕ)
  (C : UniCodeK3 D F3 nV np) (hs : UniShapesK D)

/-- The three openings at the honest setup column. -/
noncomputable abbrev uOpsK3 : List (WhirOp UPf E Stk) := uniOpsK3 F3 nV np C hs (colFK D)

/-- The chain of π1-rec3's rounds. -/
noncomputable abbrev uSpecK3 : ChainSpecU E FSt := uniSpec (uRoundsK3 F3 nV np)

theorem hcov_uniK3 : ∀ i < (uSpecK3 F3 nV np).K.rounds.length, ((uSpecK3 F3 nV np).K.spec i).root →
    ∃ o ∈ uOpsK3 D F3 nV np C hs, ∃ rd, o.tgt = .round i rd := by
  intro i _ hr
  rcases root_rec3Rounds F3.prog.rounds F3.rounds_root nV np i hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, _, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, _, rfl⟩

theorem hok_uniK3 : ∀ o ∈ uOpsK3 D F3 nV np C hs,
    WhirOp.OK (uniTcK hs) (uniGoodK3 D F3 nV np C) (uSetupK D hs) (uFixK D) o := by
  intro o ho
  simp only [uOpsK3, uniOpsK3, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · refine whirOp_ok_tableCode _ _ _ 0 rdTab (uniTcK hs) (by unfold uniTcK; rw [ite_eq_left rfl]) _
      (fun π ch t h => ?_) _ _
    rw [uniGoodK3, ite_eq_left rfl]
    exact ⟨rdTab t, rfl, fun cl hcl =>
      (tabEval_rdTab _ t _ ((cl1K3 D F3 nV np C π ch).wide cl hcl)).symm.trans (h cl hcl)⟩
  · refine whirOp_ok_tableCode _ _ _ (F3.prog.rounds.length + 1) rdTab (uniTcK hs)
      (by unfold uniTcK; rw [ite_eq_right (Nat.succ_ne_zero _)]) _ (fun π ch t h => ?_) _ _
    rw [uniGoodK3, ite_eq_right (Nat.succ_ne_zero _), ite_eq_left rfl]
    exact ⟨rdTab t, rfl, fun cl hcl =>
      (tabEval_rdTab _ t _ ((cl2K3 D F3 nV np C π ch).wide cl hcl)).symm.trans (h cl hcl)⟩
  · exact whirOp_ok_stack _ _ _ _ _ _ _ (uFixK D) fun s _ => LeanVM.Rpm.digestToRpm_ofRpm s

theorem hS_uniK3 (π : UPf) (ch : List (List E))
    (h : ∀ o ∈ uOpsK3 D F3 nV np C hs, WhirOp.SetupHolds o π ch) : uniGoodSK3 D F3 nV np C π ch := by
  have h3 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  intro cl hcl
  have := h3 cl hcl
  rw [← this]
  exact (plain_tableEvalK _ (hs.lo 2 (by decide)) (hs.hi 2 (by decide)) _ _
    ((cl3K3 D F3 nV np C π ch).wide cl hcl)).symm

/-! ### The last link -/

/-- **The composition's last link from `FsLayer128K3`'s**: candidates good at `C1`'s and `C2`'s rounds and `none` at
the others, the setup's stack good, and the check, make the opened transcript the one `FsLayer128K3`'s link reads
(`openedOf`), its claims true (`ClaimsHoldK`). -/
theorem hlink_uniK3 (R : RbrPiop (uRoundsK3 F3 nV np) USt Stk)
    (hFin : ∀ (s : USt) done tl c1 c2, DoneFits (uRoundsK3 F3 nV np) done → tl.length = 3 →
      (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHoldK D ((C.prog s.1 s.2).out done tl) c1 c2 →
        ∃ p m ch, openedOf F3.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧ R.post s p m ch)
    (π : UPf) (ch : List (List E)) (cs : List (Option Stk)) (hc : uniCheckK3 D F3 nV np C π ch)
    (hl : cs.length = (uSpecK3 F3 nV np).K.rounds.length)
    (hg : ∀ i (h : i < cs.length), ((uSpecK3 F3 nV np).K.spec i).root →
      uniGoodK3 D F3 nV np C i π ch cs[i])
    (hn : ∀ i (h : i < cs.length), ((uSpecK3 F3 nV np).K.spec i).root = false → cs[i] = none)
    (hgS : uniGoodSK3 D F3 nV np C π ch) :
    ∃ p m c, opened cs (uView (uRoundsK3 F3 nV np) π).2 ch = p ++ [(m, c)] ∧
      (liftPiop (uSpecK3 F3 nV np).K R rfl).post (uView (uRoundsK3 F3 nV np) π).1 p m c := by
  obtain ⟨hdf, hzv, hwf⟩ := hc
  have hlen : cs.length = F3.prog.rounds.length + 4 + np := by
    rw [hl]
    exact length_rec3Rounds _ _ _
  have h0 : 0 < cs.length := by omega
  have h1 : F3.prog.rounds.length + 1 < cs.length := by omega
  have hs0 : ((uSpecK3 F3 nV np).K.spec 0).root := by
    show ((rec3Rounds F3.prog.rounds nV np).getD 0 ⟨false, 0, 0⟩).root = true
    rw [rec3Rounds_zero]
  have hs1 : ((uSpecK3 F3 nV np).K.spec (F3.prog.rounds.length + 1)).root := by
    show ((rec3Rounds F3.prog.rounds nV np).getD (F3.prog.rounds.length + 1)
      ⟨false, 0, 0⟩).root = true
    rw [rec3Rounds_c2]
  have g0 := hg 0 h0 hs0
  rw [uniGoodK3, ite_eq_left rfl] at g0
  obtain ⟨q1, hq1, hc1⟩ := g0
  have g1 := hg _ h1 hs1
  rw [uniGoodK3, ite_eq_right (Nat.succ_ne_zero _), ite_eq_left rfl] at g1
  obtain ⟨q2, hq2, hc2⟩ := g1
  have hcand : ∀ i (h : i < cs.length), cs[i] = candAt F3.prog.rounds.length q1 q2 i := by
    intro i h
    by_cases hi0 : i = 0
    · subst hi0
      rw [hq1]
      simp [candAt]
    by_cases hi1 : i = F3.prog.rounds.length + 1
    · subst hi1
      rw [hq2]
      simp [candAt]
    · rcases Bool.eq_false_or_eq_true ((uSpecK3 F3 nV np).K.spec i).root with hr | hr
      · rcases root_rec3Rounds F3.prog.rounds F3.rounds_root nV np i hr with h' | h'
        · exact absurd h' hi0
        · exact absurd h' hi1
      · rw [hn i h hr]
        simp [candAt, hi0, hi1]
  have hlu : (msgsAt π.proof.stream 24 (uRoundsK3 F3 nV np)).length = (uRoundsK3 F3 nV np).length :=
    length_msgsAt _ _ _
  have hch : (msgsAt π.proof.stream 24 (uRoundsK3 F3 nV np)).length ≤ ch.length := by
    have := hdf.length_eq
    simp only [uDone, List.length_zip] at this
    omega
  have hop : opened cs (uView (uRoundsK3 F3 nV np) π).2 ch =
      openedOf F3.prog.rounds.length q1 q2 (uDone (uRoundsK3 F3 nV np) π ch) :=
    opened_eq_openedOf _ q1 q2 _ ch cs hch (by rw [hlu]; exact hl) hcand
  obtain ⟨hwo, hw1, hw2, hw3, -⟩ := hwf
  have e1 : (cl1K3 D F3 nV np C π ch).claims = claimsOf (uOutK3 D F3 nV np C π ch) .c1 :=
    mkStmt_claims (plainL (wvK D 0)) (extra_plainL _) _ (claimsOf_length_le _ hwo _) hw1
  have e2 : (cl2K3 D F3 nV np C π ch).claims = claimsOf (uOutK3 D F3 nV np C π ch) .c2 :=
    mkStmt_claims (plainL (wvK D 1)) (extra_plainL _) _ (claimsOf_length_le _ hwo _) hw2
  have e3 : (cl3K3 D F3 nV np C π ch).claims = claimsOf (uOutK3 D F3 nV np C π ch) .setup :=
    mkStmt_claims (plainL (wvK D 2)) (extra_plainL _) _ (claimsOf_length_le _ hwo _) hw3
  have hCH : ClaimsHoldK D (uOutK3 D F3 nV np C π ch) q1 q2 :=
    claimsHoldK_of D _ q1 q2 (by rw [← e1]; exact hc1) (by rw [← e2]; exact hc2)
      (by rw [← e3]; exact hgS)
  obtain ⟨p, m, ch', he, hpost⟩ :=
    hFin (uStK3 F3 nV np π) _ _ q1 q2 hdf (length_uTailK _ _) hzv hCH
  exact ⟨p, m, ch', hop.trans he, hpost⟩

/-! ### The event, the numbers -/

/-- **The Keccak verifier's break on the composed game's outcome**: the check, the three openings accept, and no
candidate of `C1`'s root read off the transcript satisfies the Keccak VM's relation (`RelK`). -/
def UniBreaksRelK3 (z : OutK UPf E (List Bool)) : Prop :=
  uniCheckK3 D F3 nV np C z.1.1 z.1.2.1 ∧
    (∀ k < (uOpsK3 D F3 nV np C hs).length, z.1.2.2.getD k false = true) ∧
    ∀ c ∈ extractorK (fun i => (uniTcK hs i).commit) (uView (uRoundsK3 F3 nV np)) z,
      ∀ q, c = some q → ¬ RelK F D (uStK3 F3 nV np z.1.1) q

/-- **The deployment's numbers**: the chain's queries below `2^10`, the composed verifier's calls of `π` below
`2^80`. -/
structure UniNumbersK3 : Prop where
  chain : (uSpecK3 F3 nV np).K.nQ ≤ 2 ^ 10
  verifier : ∀ π, Common.QueryCostAtMost (verU (uSpecK3 F3 nV np) (uView (uRoundsK3 F3 nV np))
    (opsRun (uView (uRoundsK3 F3 nV np)) (uOpsK3 D F3 nV np C hs)) π) LeanVM.Rpm.hashBlocks (2 ^ 80)

theorem breaksOK_of_relK3 (R : RbrPiop (uRoundsK3 F3 nV np) USt Stk)
    (hpre : ∀ s c m, R.pre s [] (some c, m) → RelK F D s c) (z : OutK UPf E (List Bool))
    (hz : UniBreaksRelK3 D F3 nV np C hs z) :
    BreaksOK (uSpecK3 F3 nV np).K (fun i => (uniTcK hs i).commit) (liftPiop (uSpecK3 F3 nV np).K R rfl)
      (uView (uRoundsK3 F3 nV np)) (uniCheckK3 D F3 nV np C)
      (fun bs => ∀ k < (uOpsK3 D F3 nV np C hs).length, bs.getD k false = true) z := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨h1, h2, fun c hc hpre' => ?_⟩
  have hr : ∃ r, (msgK (uView (uRoundsK3 F3 nV np)) z.1.1 0).1 = some r := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := hr
  have hc' := hc
  simp only [extractorK, optC, hr, List.mem_map] at hc'
  obtain ⟨q, -, rfl⟩ := hc'
  exact h3 _ hc q rfl (hpre _ _ _ hpre')

theorem sumQO_leK3 : ((uOpsK3 D F3 nV np C hs).map fun o => o.S.QO).sum ≤ 3 * 10122 := by
  have q : ∀ k (hk : k < 3), kQueries (wvK D k) ≤ 10122 := fun k hk =>
    kQueries_le _ (hs.lo k hk) (hs.hi k hk)
  have q0 := q 0 (by decide)
  have q1 := q 1 (by decide)
  have q2 := q 2 (by decide)
  simp only [uOpsK3, uniOpsK3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  try dsimp only [shapeKK, plainShapeK]
  omega

theorem maxErrK_uniK3 (R : RbrPiop (uRoundsK3 F3 nV np) USt Stk) (e : ℝ≥0∞) (herr : ∀ j, R.err j ≤ e) :
    maxErrK (uSpecK3 F3 nV np).K (fun i => (uniTcK hs i).commit) (liftPiop (uSpecK3 F3 nV np).K R rfl) ≤
      ((9952 ^ 2 : ℕ) : ℝ≥0∞) * e := by
  unfold maxErrK
  refine Finset.sup_le fun j _ => mul_le_mul' (Nat.cast_le.mpr ?_) (herr j)
  refine (facL_le_pow _ 9952 (fun k => uniTcK_bound D hs k) 0 _).trans
    (Nat.pow_le_pow_right (by norm_num) ?_)
  exact (List.take_sublist _ _).countP_le.trans
    (le_of_eq (countP_root_rec3Rounds F3.prog.rounds F3.rounds_root nV np))

/-- **The composed verifier's calls of `π`**: at most `2^80`, when the chain asks at most `2^10` queries and every
round sends at most `2^30` scalars (`(2^10 + 3 · 10122) · 2^32 ≤ 2^80`). -/
theorem uniNumbersK3_of (hnQ : (uSpecK3 F3 nV np).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRoundsK3 F3 nV np, r.nv ≤ 2 ^ 30) : UniNumbersK3 D F3 nV np C hs := by
  refine ⟨hnQ, fun π => ?_⟩
  have htot : IsTotalQueryBound (verU (uSpecK3 F3 nV np) (uView (uRoundsK3 F3 nV np))
      (opsRun (uView (uRoundsK3 F3 nV np)) (uOpsK3 D F3 nV np C hs)) π)
      ((uSpecK3 F3 nV np).K.nQ + ((uOpsK3 D F3 nV np C hs).map fun o => o.S.QO).sum) := by
    unfold verU
    exact isTotalQueryBound_bind (isTotalQueryBound_chainU _ _ _) fun ch =>
      isTotalQueryBound_bind (n₂ := 0) (isTotalQueryBound_opsRun _ _ _ _) fun _ => trivial
  have hmsg : ∀ m ∈ (uView (uRoundsK3 F3 nV np) π).2, m.2.length ≤ 2 ^ 30 := by
    intro m hm
    have hfit := fitsAll_uView (uRoundsK3 F3 nV np) π
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
    have hl := hfit.length_eq
    have := fitsAll_getD hfit i (by omega)
    have hi' : i < (uRoundsK3 F3 nV np).length := by omega
    rw [List.getD_eq_getElem _ _ hi] at this
    rw [this.2, List.getD_eq_getElem _ _ hi']
    exact hnv _ (List.getElem_mem hi')
  have hops : ∀ ch, ∀ o ∈ uOpsK3 D F3 nV np C hs,
      (o.cl π ch).claims.length ≤ 2 ∧ o.S.L.vars ≤ 2 ^ 30 := by
    intro ch o ho
    simp only [uOpsK3, uniOpsK3, List.mem_cons, List.mem_nil_iff, or_false] at ho
    have hk : ∀ k < 3, wvK D k ≤ 2 ^ 30 := fun k hk => (hs.hi k hk).trans (by norm_num)
    rcases ho with rfl | rfl | rfl
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 0 (by decide)⟩
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 1 (by decide)⟩
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 2 (by decide)⟩
  have hall : AllQueriesSatisfy (verU (uSpecK3 F3 nV np) (uView (uRoundsK3 F3 nV np))
      (opsRun (uView (uRoundsK3 F3 nV np)) (uOpsK3 D F3 nV np C hs)) π) Short := by
    unfold verU ChainSpecU.chain
    rw [map_eq_bind_pure_comp, bind_assoc]
    refine allQueriesSatisfy_bind (allQ_runM _ _ ?_ ?_) fun sts => ?_
    · show (uniLabel _).length ≤ _
      simp [uniLabel, name_length]
    · intro e he
      have := length_mem_absorbsI _ (2 ^ 30) 0 _ _ hmsg e he
      omega
    · simp only [Function.comp_apply, pure_bind]
      exact allQueriesSatisfy_bind (allQ_opsRun _ _ _ _ (hops _)) fun _ => LeanVM.Rpm.allQ_pure _
  have hq := sumQO_leK3 D F3 nV np C hs
  refine (LeanVM.Rpm.isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 32) htot
    (hall.mono fun _ h => LeanVM.Rpm.hashBlocks_le_of_short h)).mono ?_
  have h80 : (2 ^ 10 + 3 * 10122) * 2 ^ 32 ≤ (2 : ℕ) ^ 80 := by norm_num
  exact (Nat.mul_le_mul_right _ (by omega)).trans h80

end Facts

end UniKeccakSound

/-- info: 'UniKeccakSound.hok_uniK3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.hok_uniK3

/-- info: 'UniKeccakSound.hlink_uniK3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.hlink_uniK3

/-- info: 'UniKeccakSound.uniNumbersK3_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniNumbersK3_of
