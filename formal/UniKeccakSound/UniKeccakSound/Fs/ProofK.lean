-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The main line's `UniSound/FsProof.lean` (the
-- composition's facts, the setup), `UniSound/FsCost.lean` (`uniNumbers_of`) and π1-rec3's `Rec3/FsProof3.lean`
-- (three openings) for the Keccak verifier, whose setup is one tree.
import UniKeccakSound.Fs.OpsK

/-!
# The Keccak verifier: the setup, the composition's facts, the numbers

* **The setup is one tree** (`setupK1`: `stackSetupS` of the setup's stack `setupStackK` at its plain shape); the
  proof records its root and the deployment's constants `A0`, `B0` (`uFixK`, `rootsK`: `KDeployment.setupRoots`).
* **The composition's facts** for the three openings (`uOpsK`), the decoders (`uniTcK`), the chain (`uSpecK`, on
  `uniRounds`): the openings match (`hok_uniK`: `C1`, `C2` by `whirOp_ok_tableCode`, the setup's by
  `whirOp_ok_stack`), every round with a root is opened (`hcov_uniK`), the setup's stack satisfies its claim
  (`hS_uniK`: the plain layout's table is its stack at `2^23 ..= 2^28`, `plain_tableEvalK`), the last link
  (`hlink_uniK`, from `FsLayer128K`'s, its claims `ClaimsHoldK`).
* **The event** (`UniBreaksRelK`), **the numbers** (`UniNumbersK`, `uniNumbersK_of`: the composed verifier's calls of
  `π` below `(2^10 + 3 · 10122) · 2^32 ≤ 2^80`), the setup's `≤ 2^24` Keccak-256 calls (`setupQSK_le`), the
  openings' `≤ 3 · 10122` queries (`sumQO_leK`), the chain's lists `≤ 9952²` (`maxErrK_uniK`).
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open LeanVM.Rpm (Short hashBlocks)
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.layoutWordsK UniKeccak.setupStackK

/-! ## The plain layout's table is its stack, at `2^23 ..= 2^28` -/

theorem newBlocks_plainK (v : ℕ) (h1 : 23 ≤ v) (h2 : v ≤ 28) :
    WhirBridge.Layout.newBlocks v v [(0, 2 ^ v)] = List.range 64 := by
  interval_cases v <;> decide +kernel

theorem toBlocks_plainLK (v : ℕ) (h1 : 23 ≤ v) (h2 : v ≤ 28) :
    (plainL v).toBlocks.blocks = List.range 64 := by
  simp only [WhirBridge.Layout.toBlocks, plainL, WhirBridge.Layout.new, newBlocks_plainK v h1 h2,
    List.map_map]
  exact (List.map_congr_left fun _ _ => rfl).trans (List.map_id _)

theorem plainL_tableK (v : ℕ) (h1 : 23 ≤ v) (h2 : v ≤ 28) (q : LeanVM.Protocol.Column v) (t : ℕ)
    (ht : t < 2 ^ v) : (plainL v).table q t = q.values.getD t 0 := by
  have hb := toBlocks_plainLK v h1 h2
  have hl : 2 ^ v = 2 ^ (v - laneFold) * 64 := by
    rw [show (64 : ℕ) = 2 ^ laneFold from rfl, ← pow_add, Nat.sub_add_cancel (by
      unfold laneFold
      omega)]
  have hlt : t / 2 ^ (v - laneFold) < 64 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), mul_comm, ← hl]
    exact ht
  show (plainL v).toBlocks.table q t = _
  unfold WhirBridge.Blocks.table WhirBridge.Blocks.lanes WhirBridge.Blocks.logLane
  rw [hb, List.length_range]
  have hc : ∀ l ∈ Finset.range 64, ((if (List.range 64).getD l 0 = t / 2 ^ (v - laneFold) then
      q.values.getD (t % 2 ^ (v - laneFold) + 2 ^ (v - laneFold) * l) 0 else 0 : K)) =
      if t / 2 ^ (v - laneFold) = l then
        q.values.getD (t % 2 ^ (v - laneFold) + 2 ^ (v - laneFold) * l) 0 else 0 := by
    intro l hl'
    rw [List.getD_eq_getElem _ _ (by simpa using hl'), List.getElem_range]
    simp only [eq_comm]
  show (∑ l ∈ Finset.range 64, if (List.range 64).getD l 0 = t / 2 ^ (v - laneFold) then
      q.values.getD (t % 2 ^ (v - laneFold) + 2 ^ (v - laneFold) * l) 0 else 0) = _
  rw [Finset.sum_congr rfl hc, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr hlt),
    Nat.mod_add_div]

/-- **A plain layout's evaluation of an array's column is the array's multilinear extension**, at
`2^23 ..= 2^28` words. -/
theorem plain_tableEvalK (v : ℕ) (h1 : 23 ≤ v) (h2 : v ≤ 28) (a : Array K) (p : List E)
    (hp : p.length = v) : (plainL v).tableEval (colOf a v) p = mleStk (fun i => a.getD i 0) v p := by
  refine (tabEval_tabOf (plainL v) (colOf a v) p).symm.trans ?_
  rw [tabEval_rdTab _ _ _ hp]
  unfold mleStk
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 2
  show rdTab (tabOf (plainL v) (colOf a v)) x.val = _
  have hx : x.val < 2 ^ (plainL v).vars := x.isLt
  have hx' : x.val < 2 ^ v := x.isLt
  simp only [rdTab, hx, ↓reduceDIte, tabOf, Vector.getElem_ofFn]
  rw [plainL_tableK v h1 h2 _ _ hx']
  simp [colOf, Vector.getD, hx']

/-! ## The setup: one tree -/

/-- **The setup's roots the proof records**: the setup tree's root and the deployment's constants `A0`, `B0`
(`KDeployment.setupRoots`). -/
def rootsK (D : KDeployment) (s : Bytes32) : SetupRoots := ⟨ofB s, D.a0Root, D.b0Root⟩

/-- **The proof with the setup's roots** (`fix`). -/
def uFixK (D : KDeployment) (s : Bytes32) (π : UPf) : UPf := { π with roots := rootsK D s }

/-- The setup's Keccak-256 queries. -/
def setupQSK (D : KDeployment) : ℕ := 2 ^ (rootHeight (wvK D 2) logInvRate + 1)

section Setup

variable {D : KDeployment} (hs : UniShapesK D)

/-- **The setup**: the tree of the setup's stack (the Merkle tree of its encoding on its plain shape), its root. -/
noncomputable def setupK1 (qF : LeanVM.Protocol.Column (wvK D 2)) : OracleComp KeccakCalls Bytes32 :=
  stackSetupS (shapeKK hs 2 (by decide)) qF

variable (qF : LeanVM.Protocol.Column (wvK D 2))

theorem hOnly_setupK1 : LeanVM.Rpm.HOnly (setupK1 hs qF) := hOnly_stackSetupS _ _

theorem isTotalQueryBound_setupK1 : IsTotalQueryBound (setupK1 hs qF) (setupQSK D) :=
  isTotalQueryBound_stackSetupS _ _

theorem cost_setupK1 : Common.QueryCostAtMost (setupK1 hs qF) LeanVM.Rpm.hashBlocks (setupQSK D * 2 ^ 32) :=
  LeanVM.Rpm.isWeightBound_of_isTotalQueryBound LeanVM.Rpm.hashBlocks (2 ^ 32)
    (isTotalQueryBound_setupK1 hs qF)
    ((allQ_stackSetupS _ _).mono fun _ h => LeanVM.Rpm.hashBlocks_le_of_short h)

end Setup

/-! ## The composition's facts -/

section Facts

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (Fl : KFlockSound F κ keccakMain) (nV V : ℕ)
  (C : UniCodeK D Fl nV V) (hs : UniShapesK D)

/-- The setup's honest column. -/
def colFK : LeanVM.Protocol.Column (wvK D 2) := colOf (setupStackK D.prog D.shape) (wvK D 2)

/-- The three openings at the honest setup column. -/
noncomputable abbrev uOpsK : List (WhirOp UPf E Stk) := uniOpsK Fl nV V C hs (colFK D)

/-- The setup at the honest column. -/
noncomputable abbrev uSetupK : OracleComp KeccakCalls Bytes32 := setupK1 hs (colFK D)

/-- The chain of the main line's rounds. -/
noncomputable abbrev uSpecK : ChainSpecU E FSt := uniSpec (uRoundsK Fl nV V)

theorem hcov_uniK : ∀ i < (uSpecK Fl nV V).K.rounds.length, ((uSpecK Fl nV V).K.spec i).root →
    ∃ o ∈ uOpsK D Fl nV V C hs, ∃ rd, o.tgt = .round i rd := by
  intro i _ hr
  rcases root_uniRounds Fl.prog.rounds Fl.rounds_root nV V i hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, _, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, _, rfl⟩

theorem hok_uniK : ∀ o ∈ uOpsK D Fl nV V C hs,
    WhirOp.OK (uniTcK hs) (uniGoodK D Fl nV V C) (uSetupK D hs) (uFixK D) o := by
  intro o ho
  simp only [uOpsK, uniOpsK, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · refine whirOp_ok_tableCode _ _ _ 0 rdTab (uniTcK hs) (by unfold uniTcK; rw [ite_eq_left rfl]) _
      (fun π ch t h => ?_) _ _
    rw [uniGoodK, ite_eq_left rfl]
    exact ⟨rdTab t, rfl, fun cl hcl =>
      (tabEval_rdTab _ t _ ((cl1K D Fl nV V C π ch).wide cl hcl)).symm.trans (h cl hcl)⟩
  · refine whirOp_ok_tableCode _ _ _ (Fl.prog.rounds.length + 1) rdTab (uniTcK hs)
      (by unfold uniTcK; rw [ite_eq_right (Nat.succ_ne_zero _)]) _ (fun π ch t h => ?_) _ _
    rw [uniGoodK, ite_eq_right (Nat.succ_ne_zero _), ite_eq_left rfl]
    exact ⟨rdTab t, rfl, fun cl hcl =>
      (tabEval_rdTab _ t _ ((cl2K D Fl nV V C π ch).wide cl hcl)).symm.trans (h cl hcl)⟩
  · exact whirOp_ok_stack _ _ _ _ _ _ _ (uFixK D) fun s _ => LeanVM.Rpm.digestToRpm_ofRpm s

theorem hS_uniK (π : UPf) (ch : List (List E))
    (h : ∀ o ∈ uOpsK D Fl nV V C hs, WhirOp.SetupHolds o π ch) : uniGoodSK D Fl nV V C π ch := by
  have h3 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  intro cl hcl
  have := h3 cl hcl
  rw [← this]
  exact (plain_tableEvalK _ (hs.lo 2 (by decide)) (hs.hi 2 (by decide)) _ _
    ((cl3K D Fl nV V C π ch).wide cl hcl)).symm

/-! ### The last link -/

theorem claimsHoldK_of (r : Reduced) (q1 q2 : Stk)
    (h1 : ∀ cl ∈ claimsOf r .c1, mleStk q1 (wvK D 0) cl.point = cl.value)
    (h2 : ∀ cl ∈ claimsOf r .c2, mleStk q2 (wvK D 1) cl.point = cl.value)
    (h3 : ∀ cl ∈ claimsOf r .setup,
      mleStk (fun i => (setupStackK D.prog D.shape).getD i 0) (wvK D 2) cl.point = cl.value) :
    ClaimsHoldK D r q1 q2 := by
  intro o ho pt v bs hpt
  have hm := mem_claimsOf ho hpt
  obtain ⟨c, o'⟩ := o
  cases c
  · have h := h1 _ hm
    rw [show wordIndex Commitment.c1 = 0 from rfl]
    exact h
  · have h := h2 _ hm
    rw [show wordIndex Commitment.c2 = 1 from rfl]
    exact h
  · have h := h3 _ hm
    rw [show wordIndex Commitment.setup = 2 from rfl]
    exact h

/-- **The composition's last link from `FsLayer128K`'s**: candidates good at `C1`'s and `C2`'s rounds and `none` at
the others, the setup's stack good, and the check, make the opened transcript the one `FsLayer128K`'s link reads
(`openedOf`), its claims true (`ClaimsHoldK`). -/
theorem hlink_uniK (R : RbrPiop (uRoundsK Fl nV V) USt Stk)
    (hFin : ∀ (s : USt) done tl c1 c2, DoneFits (uRoundsK Fl nV V) done → tl.length = 3 →
      (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHoldK D ((C.prog s.1 s.2).out done tl) c1 c2 →
        ∃ p m ch, openedOf Fl.prog.rounds.length c1 c2 done = p ++ [(m, ch)] ∧ R.post s p m ch)
    (π : UPf) (ch : List (List E)) (cs : List (Option Stk)) (hc : uniCheckK D Fl nV V C π ch)
    (hl : cs.length = (uSpecK Fl nV V).K.rounds.length)
    (hg : ∀ i (h : i < cs.length), ((uSpecK Fl nV V).K.spec i).root →
      uniGoodK D Fl nV V C i π ch cs[i])
    (hn : ∀ i (h : i < cs.length), ((uSpecK Fl nV V).K.spec i).root = false → cs[i] = none)
    (hgS : uniGoodSK D Fl nV V C π ch) :
    ∃ p m c, opened cs (uView (uRoundsK Fl nV V) π).2 ch = p ++ [(m, c)] ∧
      (liftPiop (uSpecK Fl nV V).K R rfl).post (uView (uRoundsK Fl nV V) π).1 p m c := by
  obtain ⟨hdf, hzv, hwf⟩ := hc
  have hlen : cs.length = Fl.prog.rounds.length + 3 + V := by
    rw [hl]
    exact length_uniRounds _ _ _
  have h0 : 0 < cs.length := by omega
  have h1 : Fl.prog.rounds.length + 1 < cs.length := by omega
  have hs0 : ((uSpecK Fl nV V).K.spec 0).root := by
    show ((uniRounds Fl.prog.rounds nV V).getD 0 ⟨false, 0, 0⟩).root = true
    rw [uniRounds_getD_zero]
  have hs1 : ((uSpecK Fl nV V).K.spec (Fl.prog.rounds.length + 1)).root := by
    show ((uniRounds Fl.prog.rounds nV V).getD (Fl.prog.rounds.length + 1)
      ⟨false, 0, 0⟩).root = true
    rw [uniRounds_getD_c2]
  have g0 := hg 0 h0 hs0
  rw [uniGoodK, ite_eq_left rfl] at g0
  obtain ⟨q1, hq1, hc1⟩ := g0
  have g1 := hg _ h1 hs1
  rw [uniGoodK, ite_eq_right (Nat.succ_ne_zero _), ite_eq_left rfl] at g1
  obtain ⟨q2, hq2, hc2⟩ := g1
  have hcand : ∀ i (h : i < cs.length), cs[i] = candAt Fl.prog.rounds.length q1 q2 i := by
    intro i h
    by_cases hi0 : i = 0
    · subst hi0
      rw [hq1]
      simp [candAt]
    by_cases hi1 : i = Fl.prog.rounds.length + 1
    · subst hi1
      rw [hq2]
      simp [candAt]
    · rcases Bool.eq_false_or_eq_true ((uSpecK Fl nV V).K.spec i).root with hr | hr
      · rcases root_uniRounds Fl.prog.rounds Fl.rounds_root nV V i hr with h' | h'
        · exact absurd h' hi0
        · exact absurd h' hi1
      · rw [hn i h hr]
        simp [candAt, hi0, hi1]
  have hlu : (msgsAt π.proof.stream 24 (uRoundsK Fl nV V)).length = (uRoundsK Fl nV V).length :=
    length_msgsAt _ _ _
  have hch : (msgsAt π.proof.stream 24 (uRoundsK Fl nV V)).length ≤ ch.length := by
    have := hdf.length_eq
    simp only [uDone, List.length_zip] at this
    omega
  have hop : opened cs (uView (uRoundsK Fl nV V) π).2 ch =
      openedOf Fl.prog.rounds.length q1 q2 (uDone (uRoundsK Fl nV V) π ch) :=
    opened_eq_openedOf _ q1 q2 _ ch cs hch (by rw [hlu]; exact hl) hcand
  obtain ⟨hwo, hw1, hw2, hw3, -⟩ := hwf
  have e1 : (cl1K D Fl nV V C π ch).claims = claimsOf (uOutK D Fl nV V C π ch) .c1 :=
    mkStmt_claims (plainL (wvK D 0)) (extra_plainL _) _ (claimsOf_length_le _ hwo _) hw1
  have e2 : (cl2K D Fl nV V C π ch).claims = claimsOf (uOutK D Fl nV V C π ch) .c2 :=
    mkStmt_claims (plainL (wvK D 1)) (extra_plainL _) _ (claimsOf_length_le _ hwo _) hw2
  have e3 : (cl3K D Fl nV V C π ch).claims = claimsOf (uOutK D Fl nV V C π ch) .setup :=
    mkStmt_claims (plainL (wvK D 2)) (extra_plainL _) _ (claimsOf_length_le _ hwo _) hw3
  have hCH : ClaimsHoldK D (uOutK D Fl nV V C π ch) q1 q2 :=
    claimsHoldK_of D _ q1 q2 (by rw [← e1]; exact hc1) (by rw [← e2]; exact hc2)
      (by rw [← e3]; exact hgS)
  obtain ⟨p, m, ch', he, hpost⟩ :=
    hFin (uStK Fl nV V π) _ _ q1 q2 hdf (length_uTailK _ _) hzv hCH
  exact ⟨p, m, ch', hop.trans he, hpost⟩

/-! ### The event, the numbers -/

/-- **The Keccak verifier's break on the composed game's outcome**: the check, the three openings accept, and no
candidate of `C1`'s root read off the transcript satisfies the Keccak VM's relation (`RelK`). -/
def UniBreaksRelK (z : OutK UPf E (List Bool)) : Prop :=
  uniCheckK D Fl nV V C z.1.1 z.1.2.1 ∧
    (∀ k < (uOpsK D Fl nV V C hs).length, z.1.2.2.getD k false = true) ∧
    ∀ c ∈ extractorK (fun i => (uniTcK hs i).commit) (uView (uRoundsK Fl nV V)) z,
      ∀ q, c = some q → ¬ RelK F D (uStK Fl nV V z.1.1) q

/-- **The deployment's numbers**: the chain's queries below `2^10`, the composed verifier's calls of `π` below
`2^80`. -/
structure UniNumbersK : Prop where
  chain : (uSpecK Fl nV V).K.nQ ≤ 2 ^ 10
  verifier : ∀ π, Common.QueryCostAtMost (verU (uSpecK Fl nV V) (uView (uRoundsK Fl nV V))
    (opsRun (uView (uRoundsK Fl nV V)) (uOpsK D Fl nV V C hs)) π) LeanVM.Rpm.hashBlocks (2 ^ 80)

theorem breaksOK_of_relK (R : RbrPiop (uRoundsK Fl nV V) USt Stk)
    (hpre : ∀ s c m, R.pre s [] (some c, m) → RelK F D s c) (z : OutK UPf E (List Bool))
    (hz : UniBreaksRelK D Fl nV V C hs z) :
    BreaksOK (uSpecK Fl nV V).K (fun i => (uniTcK hs i).commit) (liftPiop (uSpecK Fl nV V).K R rfl)
      (uView (uRoundsK Fl nV V)) (uniCheckK D Fl nV V C)
      (fun bs => ∀ k < (uOpsK D Fl nV V C hs).length, bs.getD k false = true) z := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨h1, h2, fun c hc hpre' => ?_⟩
  have hr : ∃ r, (msgK (uView (uRoundsK Fl nV V)) z.1.1 0).1 = some r := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := hr
  have hc' := hc
  simp only [extractorK, optC, hr, List.mem_map] at hc'
  obtain ⟨q, -, rfl⟩ := hc'
  exact h3 _ hc q rfl (hpre _ _ _ hpre')

include hs in
theorem setupQSK_le : setupQSK D ≤ 2 ^ 24 := by
  unfold setupQSK rootHeight laneFold logInvRate
  have h2 := hs.hi 2 (by decide)
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem sumQO_leK : ((uOpsK D Fl nV V C hs).map fun o => o.S.QO).sum ≤ 3 * 10122 := by
  have q : ∀ k (hk : k < 3), kQueries (wvK D k) ≤ 10122 := fun k hk =>
    kQueries_le _ (hs.lo k hk) (hs.hi k hk)
  have q0 := q 0 (by decide)
  have q1 := q 1 (by decide)
  have q2 := q 2 (by decide)
  simp only [uOpsK, uniOpsK, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  try dsimp only [shapeKK, plainShapeK]
  omega

theorem uniTcK_bound (i : ℕ) : (uniTcK hs i).commit.bound ≤ 9952 := by
  unfold uniTcK
  split_ifs
  · exact (tableCode_bound_large (wvK D 0) (wvK D 0) (wvK D 0) [(0, 2 ^ wvK D 0)]
      (newOK_plainK _ (hs.lo 0 (by decide)) (hs.hi 0 (by decide))) hs.c1
      (hs.hi 0 (by decide)) rdTab).le.trans
      (largeList_le _ hs.c1 (hs.hi 0 (by decide)))
  · exact (tableCode_bound_large (wvK D 1) (wvK D 1) (wvK D 1) [(0, 2 ^ wvK D 1)]
      (newOK_plainK _ (hs.lo 1 (by decide)) (hs.hi 1 (by decide))) hs.c2
      (hs.hi 1 (by decide)) rdTab).le.trans
      (largeList_le _ hs.c2 (hs.hi 1 (by decide)))

theorem maxErrK_uniK (R : RbrPiop (uRoundsK Fl nV V) USt Stk) (e : ℝ≥0∞) (herr : ∀ j, R.err j ≤ e) :
    maxErrK (uSpecK Fl nV V).K (fun i => (uniTcK hs i).commit) (liftPiop (uSpecK Fl nV V).K R rfl) ≤
      ((9952 ^ 2 : ℕ) : ℝ≥0∞) * e := by
  unfold maxErrK
  refine Finset.sup_le fun j _ => mul_le_mul' (Nat.cast_le.mpr ?_) (herr j)
  refine (facL_le_pow _ 9952 (fun k => uniTcK_bound D hs k) 0 _).trans
    (Nat.pow_le_pow_right (by norm_num) ?_)
  exact (List.take_sublist _ _).countP_le.trans
    (le_of_eq (countP_root_uniRounds Fl.prog.rounds Fl.rounds_root nV V))

/-- **The composed verifier's calls of `π`**: at most `2^80`, when the chain asks at most `2^10` queries and every
round sends at most `2^30` scalars (`(2^10 + 3 · 10122) · 2^32 ≤ 2^80`). -/
theorem uniNumbersK_of (hnQ : (uSpecK Fl nV V).K.nQ ≤ 2 ^ 10)
    (hnv : ∀ r ∈ uRoundsK Fl nV V, r.nv ≤ 2 ^ 30) : UniNumbersK D Fl nV V C hs := by
  refine ⟨hnQ, fun π => ?_⟩
  have htot : IsTotalQueryBound (verU (uSpecK Fl nV V) (uView (uRoundsK Fl nV V))
      (opsRun (uView (uRoundsK Fl nV V)) (uOpsK D Fl nV V C hs)) π)
      ((uSpecK Fl nV V).K.nQ + ((uOpsK D Fl nV V C hs).map fun o => o.S.QO).sum) := by
    unfold verU
    exact isTotalQueryBound_bind (isTotalQueryBound_chainU _ _ _) fun ch =>
      isTotalQueryBound_bind (n₂ := 0) (isTotalQueryBound_opsRun _ _ _ _) fun _ => trivial
  have hmsg : ∀ m ∈ (uView (uRoundsK Fl nV V) π).2, m.2.length ≤ 2 ^ 30 := by
    intro m hm
    have hfit := fitsAll_uView (uRoundsK Fl nV V) π
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
    have hl := hfit.length_eq
    have := fitsAll_getD hfit i (by omega)
    have hi' : i < (uRoundsK Fl nV V).length := by omega
    rw [List.getD_eq_getElem _ _ hi] at this
    rw [this.2, List.getD_eq_getElem _ _ hi']
    exact hnv _ (List.getElem_mem hi')
  have hops : ∀ ch, ∀ o ∈ uOpsK D Fl nV V C hs,
      (o.cl π ch).claims.length ≤ 2 ∧ o.S.L.vars ≤ 2 ^ 30 := by
    intro ch o ho
    simp only [uOpsK, uniOpsK, List.mem_cons, List.mem_nil_iff, or_false] at ho
    have hk : ∀ k < 3, wvK D k ≤ 2 ^ 30 := fun k hk => (hs.hi k hk).trans (by norm_num)
    rcases ho with rfl | rfl | rfl
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 0 (by decide)⟩
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 1 (by decide)⟩
    · exact ⟨(mkStmt_length_le _ (extra_plainL _) _).trans (by norm_num), hk 2 (by decide)⟩
  have hall : AllQueriesSatisfy (verU (uSpecK Fl nV V) (uView (uRoundsK Fl nV V))
      (opsRun (uView (uRoundsK Fl nV V)) (uOpsK D Fl nV V C hs)) π) Short := by
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
  have hq := sumQO_leK D Fl nV V C hs
  refine (LeanVM.Rpm.isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 32) htot
    (hall.mono fun _ h => LeanVM.Rpm.hashBlocks_le_of_short h)).mono ?_
  have h80 : (2 ^ 10 + 3 * 10122) * 2 ^ 32 ≤ (2 : ℕ) ^ 80 := by norm_num
  exact (Nat.mul_le_mul_right _ (by omega)).trans h80

end Facts

end UniKeccakSound

/-- info: 'UniKeccakSound.hok_uniK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.hok_uniK

/-- info: 'UniKeccakSound.hlink_uniK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.hlink_uniK

/-- info: 'UniKeccakSound.uniNumbersK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniNumbersK_of
