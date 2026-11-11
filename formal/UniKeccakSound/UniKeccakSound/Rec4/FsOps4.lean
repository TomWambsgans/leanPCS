-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `Fs/OpsK3.lean`'s and `Fs/ProofK3.lean`'s openings,
-- check and composition facts at π1-rec4's rounds (`rec4Rounds`, the wide chain's view `uView4`).
import UniKeccakSound.Rec4.FsSpec4
import UniKeccakSound.Fs.ProofK3

/-!
# π1-rec4's three openings, its check, and the composition's facts

`Fs/OpsK3.lean`'s and `Fs/ProofK3.lean`'s at π1-rec4's rounds (`rec4Rounds κ nV np`), its view (`uView4`: `C2`'s
`64` slices before its root) and its code-level link `UniCodeK4`: `C1` opened at round `0`, `C2` at round `28 + κ`,
the setup's stack at the setup's root; the check (`uniCheck4`); the facts the composition takes (`hok_uni4`,
`hcov_uni4`, `hS_uni4`, `hlink_uni4` from π1-rec4's last link, `breaksOK_of_rel4`, `maxErrK_uni4`: two roots) and
the PCS union (`hU_uni4`).
-/

namespace UniKeccakSound.Rec4

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniKeccak.setupStackK UniKeccak.setupOodK

/-! ## π1-rec4's roots -/

theorem kRoundsMid_root (κ : ℕ) : ∀ r ∈ kRoundsMid κ, r.root = false := by
  intro r hr
  simp only [kRoundsMid, List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil, or_false] at hr
  aesop

theorem root_rec4Rounds (κ nV np i : ℕ) (h : ((rec4Rounds κ nV np).getD i ⟨false, 0, 0⟩).root = true) :
    i = 0 ∨ i = 28 + κ := by
  have e : rec4Rounds κ nV np = (⟨true, 1, 3⟩ :: kRoundsMid κ) ++ (⟨true, 65, 4⟩ :: ⟨false, nV, 3⟩ ::
      (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩])) := by
    simp [rec4Rounds]
  rw [e, List.getD_eq_getElem?_getD] at h
  by_cases h1 : i < 28 + κ
  · rw [List.getElem?_append_left (by simp [length_kRoundsMid]; omega)] at h
    rcases i with _ | i
    · exact Or.inl rfl
    · rw [List.getElem?_cons_succ] at h
      have hi : i < (kRoundsMid κ).length := by rw [length_kRoundsMid]; omega
      rw [List.getElem?_eq_getElem hi, Option.getD_some] at h
      rw [kRoundsMid_root κ _ (List.getElem_mem hi)] at h
      exact absurd h (by decide)
  · rw [List.getElem?_append_right (by simp [length_kRoundsMid]; omega)] at h
    simp only [List.length_cons, length_kRoundsMid] at h
    by_cases h2 : i = 28 + κ
    · exact Or.inr h2
    · exfalso
      obtain ⟨k, hk⟩ : ∃ k, i - (27 + κ + 1) = k + 1 := ⟨i - (27 + κ + 1) - 1, by omega⟩
      rw [hk, List.getElem?_cons_succ] at h
      rcases k with _ | k
      · simp at h
      · rw [List.getElem?_cons_succ] at h
        by_cases hk' : k < np
        · rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate] at h
          simp [hk'] at h
        · rw [List.getElem?_append_right (by simp; omega)] at h
          simp only [List.length_replicate] at h
          rcases hk2 : k - np with _ | j
          · rw [hk2] at h; simp at h
          · rw [hk2] at h; simp at h

theorem countP_root_rec4Rounds (κ nV np : ℕ) : (rec4Rounds κ nV np).countP (fun r => r.root) = 2 := by
  have h0 : (kRoundsMid κ).countP (fun r => r.root) = 0 :=
    List.countP_eq_zero.mpr fun r hr => by simp [kRoundsMid_root κ r hr]
  simp [rec4Rounds, List.countP_append, h0]

theorem rec4Rounds_zero (κ nV np : ℕ) : (rec4Rounds κ nV np).getD 0 ⟨false, 0, 0⟩ = ⟨true, 1, 3⟩ := rfl

/-! ## The verifier's openings -/

section Ops

variable (D : KDeployment) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np)

/-- The PIOP's statement a proof announces. -/
def uSt4 (π : UPf) : USt := ustOf (uView4 κ nV np π).1

/-- π1-rec4's transcript of a proof and challenges. -/
def uDone4 (π : UPf) (ch : List (List E)) : Done := uDoneW (rec4Rounds κ nV np) (pv4 κ) π ch

/-- π1-rec4's tail of a proof. -/
def uTail4 (π : UPf) : List E := uTailW (rec4Rounds κ nV np) π

/-- **The chain program's result** on a proof and challenges. -/
def uOut4 (π : UPf) (ch : List (List E)) : Reduced :=
  (C.prog (uSt4 κ nV np π).1 (uSt4 κ nV np π).2).out (uDone4 κ nV np π ch) (uTail4 κ nV np π)

/-- **The verifier's check** (what an accepting run satisfies). -/
def uniCheck4 (π : UPf) (ch : List (List E)) : Prop :=
  DoneFits (rec4Rounds κ nV np) (uDone4 κ nV np π ch) ∧
    (C.prog (uSt4 κ nV np π).1 (uSt4 κ nV np π).2).ZerosVanish (uDone4 κ nV np π ch) (uTail4 κ nV np π) ∧
    WellFormedK D (uOut4 D κ nV np C π ch)

/-- **The `k`-th commitment's out-of-domain answer.** -/
def ood4 (π : UPf) (ch : List (List E)) : Commitment → E
  | .c1 => (uOut4 D κ nV np C π ch).oods.1
  | .c2 => (uOut4 D κ nV np C π ch).oods.2
  | .setup => setupOodK D π.roots.bytecode

/-- **What the `k`-th opening's claim says of a stack.** -/
def holds4 (k : ℕ) (π : UPf) (ch : List (List E)) (q : Column (plainL (wvK D k)).logN) : Prop :=
  (ptvK (uOut4 D κ nV np C π ch) (comK k)).1.length = wvK D k ∧
    (plainL (wvK D k)).tableEval q (ptvK (uOut4 D κ nV np C π ch) (comK k)).1 =
      (ptvK (uOut4 D κ nV np C π ch) (comK k)).2

/-- **The `k`-th opening's verifier**, at the root it reads. -/
def ver4 (k : ℕ) (r : Digest) (π : UPf) (ch : List (List E)) : OracleComp KeccakCalls Bool :=
  pcsOpenC (wvK D k) r (ood4 D κ nV np C π ch (comK k)) (ptvK (uOut4 D κ nV np C π ch) (comK k)).1
    (ptvK (uOut4 D κ nV np C π ch) (comK k)).2 ((kpOf π).openingOf (comK k))

variable {D} in
/-- **The `k`-th opening** on what it opens (`t`). -/
noncomputable def op4 (hs : UniShapesK D) (k : ℕ) (hk : k < 3) (t : Tgt UPf Stk (shapeKK hs k hk).L.logN) :
    GOp UPf E Stk :=
  ⟨(shapeKK hs k hk).L.logN, (shapeKK hs k hk).R, (shapeKK hs k hk).adm, holds4 D κ nV np C k,
    ver4 D κ nV np C k, 10122, fun _ _ _ => isTotalQueryBound_pcsOpenC _ _ _ _ _ _,
    fun _ _ _ => duplexVm_pcsOpenC _ _ _ _ _ _, t⟩

variable {D} in
/-- **π1-rec4's three openings**: `C1` and `C2` (rounds `0`, `28 + κ`), the setup's stack. -/
noncomputable def uniOps4 (hs : UniShapesK D) (qF : LeanVM.Protocol.Column (wvK D 2)) : List (GOp UPf E Stk) :=
  [op4 κ nV np C hs 0 (by decide) (.round 0 fun q => rdTab (tabOf _ q)),
    op4 κ nV np C hs 1 (by decide) (.round (28 + κ) fun q => rdTab (tabOf _ q)),
    op4 κ nV np C hs 2 (by decide) (.setup (fun π => toB π.roots.bytecode) qF)]

/-- **A candidate is good**: at `C1`'s and `C2`'s rounds, a stack satisfying its PCS claim's point claim. -/
def uniGood4 (i : ℕ) (π : UPf) (ch : List (List E)) (c : Option Stk) : Prop :=
  if i = 0 then ∃ q, c = some q ∧
      mleStk q (wvK D 0) (ptvK (uOut4 D κ nV np C π ch) .c1).1 = (ptvK (uOut4 D κ nV np C π ch) .c1).2
  else if i = 28 + κ then ∃ q, c = some q ∧
      mleStk q (wvK D 1) (ptvK (uOut4 D κ nV np C π ch) .c2).1 = (ptvK (uOut4 D κ nV np C π ch) .c2).2
  else True

/-- **The setup's stack is good.** -/
def uniGoodS4 (π : UPf) (ch : List (List E)) : Prop :=
  mleStk (fun i => (setupStackK D.prog D.shape).getD i 0) (wvK D 2) (ptvK (uOut4 D κ nV np C π ch) .setup).1 =
    (ptvK (uOut4 D κ nV np C π ch) .setup).2

end Ops

/-! ## The composition's facts -/

section Facts

variable (D : KDeployment) (κ nV np : ℕ) (C : UniCodeK4 D κ nV np) (hs : UniShapesK D)

/-- The three openings at the honest setup column. -/
noncomputable abbrev uOps4 : List (GOp UPf E Stk) := uniOps4 κ nV np C hs (colFK D)

theorem hcov_uni4 : ∀ i < (uSpec4 κ nV np).K.rounds.length, ((uSpec4 κ nV np).K.spec i).root →
    ∃ o ∈ uOps4 D κ nV np C hs, ∃ rd, o.tgt = .round i rd := by
  intro i _ hr
  rcases root_rec4Rounds κ nV np i hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, _, rfl⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, _, rfl⟩

theorem hok_uni4 : ∀ o ∈ uOps4 D κ nV np C hs,
    GOp.OK (uniTcK hs) (uniGood4 D κ nV np C) (uSetupK D hs) (uFixK D) o := by
  intro o ho
  simp only [uOps4, uniOps4, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · refine gop_ok_tableCode _ _ _ _ _ _ _ _ 0 rdTab (uniTcK hs) (by unfold uniTcK; rw [ite_eq_left rfl]) _
      (fun π ch q h => ?_) _ _
    rw [uniGood4, ite_eq_left rfl]
    exact ⟨_, rfl, (tabEval_rdTab _ _ _ h.1).symm.trans ((tabEval_tabOf _ _ _).trans h.2)⟩
  · refine gop_ok_tableCode _ _ _ _ _ _ _ _ (28 + κ) rdTab (uniTcK hs)
      (by unfold uniTcK; rw [ite_eq_right (by omega)]) _ (fun π ch q h => ?_) _ _
    rw [uniGood4, ite_eq_right (by omega), ite_eq_left rfl]
    exact ⟨_, rfl, (tabEval_rdTab _ _ _ h.1).symm.trans ((tabEval_tabOf _ _ _).trans h.2)⟩
  · exact gop_ok_stack _ _ _ _ _ _ _ _ _ _ (uFixK D) fun s _ => LeanVM.Rpm.digestToRpm_ofRpm s

theorem hS_uni4 (π : UPf) (ch : List (List E))
    (h : ∀ o ∈ uOps4 D κ nV np C hs, GOp.SetupHolds o π ch) : uniGoodS4 D κ nV np C π ch := by
  have h3 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  exact (plain_tableEvalK _ (hs.lo 2 (by decide)) (hs.hi 2 (by decide)) _ _ h3.1).symm.trans h3.2

/-- **The composition's last link from π1-rec4's**: candidates good at `C1`'s and `C2`'s rounds and `none` at the
others, the setup's stack good, and the check, make the opened transcript the one π1-rec4's last link reads
(`openedOf (27 + κ)`), its claims true. -/
theorem hlink_uni4 (R : RbrPiop (rec4Rounds κ nV np) USt Stk)
    (hFin : ∀ (s : USt) done tl c1 c2, DoneFits (rec4Rounds κ nV np) done → tl.length = 3 →
      (C.prog s.1 s.2).ZerosVanish done tl → ClaimsHoldK D ((C.prog s.1 s.2).out done tl) c1 c2 →
        ∃ p m ch, openedOf (27 + κ) c1 c2 done = p ++ [(m, ch)] ∧ R.post s p m ch)
    (π : UPf) (ch : List (List E)) (cs : List (Option Stk)) (hc : uniCheck4 D κ nV np C π ch)
    (hl : cs.length = (uSpec4 κ nV np).K.rounds.length)
    (hg : ∀ i (h : i < cs.length), ((uSpec4 κ nV np).K.spec i).root → uniGood4 D κ nV np C i π ch cs[i])
    (hn : ∀ i (h : i < cs.length), ((uSpec4 κ nV np).K.spec i).root = false → cs[i] = none)
    (hgS : uniGoodS4 D κ nV np C π ch) :
    ∃ p m c, opened cs (uView4 κ nV np π).2 ch = p ++ [(m, c)] ∧
      (liftPiop (uSpec4 κ nV np).K R rfl).post (uView4 κ nV np π).1 p m c := by
  obtain ⟨hdf, hzv, hwf⟩ := hc
  have hlen : cs.length = 31 + κ + np := by
    rw [hl]
    exact length_rec4Rounds _ _ _
  have h0 : 0 < cs.length := by omega
  have h1 : 28 + κ < cs.length := by omega
  have hs0 : ((uSpec4 κ nV np).K.spec 0).root := by
    show ((rec4Rounds κ nV np).getD 0 ⟨false, 0, 0⟩).root = true
    rw [rec4Rounds_zero]
  have hs1 : ((uSpec4 κ nV np).K.spec (28 + κ)).root := by
    show ((uniK (rec4Rounds κ nV np)).spec (28 + κ)).root = true
    rw [rec4Rounds_spec_c2]
  have g0 := hg 0 h0 hs0
  rw [uniGood4, ite_eq_left rfl] at g0
  obtain ⟨q1, hq1, hc1⟩ := g0
  have g1 := hg _ h1 hs1
  rw [uniGood4, ite_eq_right (by omega), ite_eq_left rfl] at g1
  obtain ⟨q2, hq2, hc2⟩ := g1
  have hcand : ∀ i (h : i < cs.length), cs[i] = candAt (27 + κ) q1 q2 i := by
    intro i h
    by_cases hi0 : i = 0
    · subst hi0
      rw [hq1]
      simp [candAt]
    by_cases hi1 : i = 28 + κ
    · subst hi1
      rw [hq2, candAt, ite_eq_right (by omega), ite_eq_left (by omega)]
    · rcases Bool.eq_false_or_eq_true ((uSpec4 κ nV np).K.spec i).root with hr | hr
      · rcases root_rec4Rounds κ nV np i hr with h' | h'
        · exact absurd h' hi0
        · exact absurd h' hi1
      · rw [hn i h hr]
        simp only [candAt, hi0, ite_false]
        rw [ite_eq_right (by omega)]
  have hlu : (msgsAtW π.proof.stream (pv4 κ) 0 24 (rec4Rounds κ nV np)).length = (rec4Rounds κ nV np).length :=
    length_msgsAtW _ _ _ _ _
  have hch : (msgsAtW π.proof.stream (pv4 κ) 0 24 (rec4Rounds κ nV np)).length ≤ ch.length := by
    have := hdf.length_eq
    simp only [uDone4, uDoneW, List.length_zip] at this
    omega
  have hop : opened cs (uView4 κ nV np π).2 ch = openedOf (27 + κ) q1 q2 (uDone4 κ nV np π ch) :=
    opened_eq_openedOf _ q1 q2 _ ch cs hch (by rw [hlu]; exact hl) hcand
  obtain ⟨hwo, -, -, -, -⟩ := hwf
  have hCH : ClaimsHoldK D (uOut4 D κ nV np C π ch) q1 q2 :=
    claimsHoldK_of D _ hwo q1 q2 hc1 hc2 hgS
  obtain ⟨p, m, ch', he, hpost⟩ := hFin (uSt4 κ nV np π) _ _ q1 q2 hdf (length_uTailW _ _) hzv hCH
  exact ⟨p, m, ch', hop.trans he, hpost⟩

/-! ### The event, the numbers -/

/-- **π1-rec4's break on the composed game's outcome**: the check, the three openings accept, and no candidate of
`C1`'s root read off the transcript satisfies the Keccak VM's relation. -/
def UniBreaksRel4 (F : KeccakVm.KeccakFlockSpec) (z : OutK UPf E (List Bool)) : Prop :=
  uniCheck4 D κ nV np C z.1.1 z.1.2.1 ∧
    (∀ k < (uOps4 D κ nV np C hs).length, z.1.2.2.getD k false = true) ∧
    ∀ c ∈ extractorK (fun i => (uniTcK hs i).commit) (uView4 κ nV np) z,
      ∀ q, c = some q → ¬ RelK F D (uSt4 κ nV np z.1.1) q

theorem breaksOK_of_rel4 {F : KeccakVm.KeccakFlockSpec} (R : RbrPiop (rec4Rounds κ nV np) USt Stk)
    (hpre : ∀ s c m, R.pre s [] (some c, m) → RelK F D s c) (z : OutK UPf E (List Bool))
    (hz : UniBreaksRel4 D κ nV np C hs F z) :
    BreaksOK (uSpec4 κ nV np).K (fun i => (uniTcK hs i).commit) (liftPiop (uSpec4 κ nV np).K R rfl)
      (uView4 κ nV np) (uniCheck4 D κ nV np C)
      (fun bs => ∀ k < (uOps4 D κ nV np C hs).length, bs.getD k false = true) z := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨h1, h2, fun c hc hpre' => ?_⟩
  have hr : ∃ r, (msgK (uView4 κ nV np) z.1.1 0).1 = some r := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := hr
  have hc' := hc
  simp only [extractorK, optC, hr, List.mem_map] at hc'
  obtain ⟨q, -, rfl⟩ := hc'
  exact h3 _ hc q rfl (hpre _ _ _ hpre')

theorem sumQO_le4 : ((uOps4 D κ nV np C hs).map fun o => o.QO).sum ≤ 3 * 10122 := by
  simp only [uOps4, uniOps4, op4, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

theorem maxErrK_uni4 (R : RbrPiop (rec4Rounds κ nV np) USt Stk) (e : ℝ≥0∞) (herr : ∀ j, R.err j ≤ e) :
    maxErrK (uSpec4 κ nV np).K (fun i => (uniTcK hs i).commit) (liftPiop (uSpec4 κ nV np).K R rfl) ≤
      ((9952 ^ 2 : ℕ) : ℝ≥0∞) * e := by
  unfold maxErrK
  refine Finset.sup_le fun j _ => mul_le_mul' (Nat.cast_le.mpr ?_) (herr j)
  refine (facL_le_pow _ 9952 (fun k => uniTcK_bound D hs k) 0 _).trans
    (Nat.pow_le_pow_right (by norm_num) ?_)
  exact (List.take_sublist _ _).countP_le.trans (le_of_eq (countP_root_rec4Rounds κ nV np))

/-! ### The openings, once: the PCS union -/

theorem uOps_ver4 (k : Fin (uOps4 D κ nV np C hs).length) :
    ((uOps4 D κ nV np C hs).get k).ver = ver4 D κ nV np C k.val := by
  obtain ⟨k, hk⟩ := k
  have hk3 : k < 3 := hk
  interval_cases k <;> rfl

theorem gDoomed_uOps4 (k : Fin (uOps4 D κ nV np C hs).length) (π : UPf) (ch : List (List E))
    (c : KeccakCalls.QueryCache) :
    GDoomed (uView4 κ nV np) ((uOps4 D κ nV np C hs).get k) π ch c ↔
      ∀ q ∈ Candidates (wvK D k.val) logInvRate (code₀ (wvK D k.val) logInvRate).thr
          (Rom.extract (fun x ↦ c (.inl x))
            (ofB (GOp.root (uView4 κ nV np) ((uOps4 D κ nV np C hs).get k) π))
            (rootHeight (wvK D k.val) logInvRate) (2 ^ laneFold)),
        ¬ holds4 D κ nV np C k.val π ch q := by
  obtain ⟨k, hk⟩ := k
  have hk3 : k < 3 := hk
  interval_cases k <;> exact Iff.rfl

/-- **An opening's statement in the PCS union.** -/
noncomputable def pcsStmt4 (w : GUIn (uOps4 D κ nV np C hs)) : Pcs.PSt pcsKShapes × Proof :=
  if h : (ptvK (uOut4 D κ nV np C w.2.1 w.2.2) (comK w.1.val)).1.length = wvK D w.1.val then
    (⟨pcsIdxK (wvK D w.1.val),
      ⟨ofB (GOp.root (uView4 κ nV np) ((uOps4 D κ nV np C hs).get w.1) w.2.1),
        ood4 D κ nV np C w.2.1 w.2.2 (comK w.1.val), (ptvK (uOut4 D κ nV np C w.2.1 w.2.2) (comK w.1.val)).1,
        (ptvK (uOut4 D κ nV np C w.2.1 w.2.2) (comK w.1.val)).2,
        h.trans (pcsIdxK_n _ (hs.lo w.1.val w.1.isLt) (hs.hi w.1.val w.1.isLt)).symm⟩⟩,
      (kpOf w.2.1).openingOf (comK w.1.val))
  else (⟨pcsIdxK 23, Pcs.dummy _⟩, (kpOf w.2.1).openingOf (comK w.1.val))

theorem pcsStmt_pos4 (w : GUIn (uOps4 D κ nV np C hs))
    (h : (ptvK (uOut4 D κ nV np C w.2.1 w.2.2) (comK w.1.val)).1.length = wvK D w.1.val) :
    pcsStmt4 D κ nV np C hs w =
      (⟨pcsIdxK (wvK D w.1.val),
        ⟨ofB (GOp.root (uView4 κ nV np) ((uOps4 D κ nV np C hs).get w.1) w.2.1),
          ood4 D κ nV np C w.2.1 w.2.2 (comK w.1.val), (ptvK (uOut4 D κ nV np C w.2.1 w.2.2) (comK w.1.val)).1,
          (ptvK (uOut4 D κ nV np C w.2.1 w.2.2) (comK w.1.val)).2,
          h.trans (pcsIdxK_n _ (hs.lo w.1.val w.1.isLt) (hs.hi w.1.val w.1.isLt)).symm⟩⟩,
        (kpOf w.2.1).openingOf (comK w.1.val)) := by
  unfold pcsStmt4
  split
  · rfl
  · contradiction

/-- **The three PCS openings, charged once.** -/
theorem hU_uni4 : GUnionSound (uView4 κ nV np) (uOps4 D κ nV np C hs)
    (fun QA => ((QA + 10122 : ℕ) : ℝ≥0∞) * (εExact + ((5 * (QA + 10122) : ℕ) : ℝ≥0∞) / 2 ^ 256)) := by
  intro A QA hA
  refine (romExperiment_le_map A _ (Pcs.pUVer pcsKShapes Pcs.oodPoint) (pcsStmt4 D κ nV np C hs)
    (fun w => (ptvK (uOut4 D κ nV np C w.2.1 w.2.2) (comK w.1.val)).1.length = wvK D w.1.val)
    (fun w => ?_) _ (Pcs.PUDoomed pcsKShapes Pcs.oodPoint) (fun w c hok hd => ?_)).trans
    (Pcs.pcs_union_sound pcsKShapes Pcs.oodPoint _ QA ((isQueryBound_map_iff _ _ _ _ _).mpr hA) 10122
      pcsKShapes_QO)
  · show GOp.run _ _ _ _ = _
    unfold GOp.run
    rw [uOps_ver4]
    unfold ver4 pcsOpenC pcsStmt4
    split_ifs with h
    · exact (pcsVerifier_congrK (pcsIdxK_n _ (hs.lo w.1.val w.1.isLt) (hs.hi w.1.val w.1.isLt)) _ _ _ _ h _
        _).symm
    · rfl
  · have hd' := (gDoomed_uOps4 D κ nV np C hs w.1 w.2.1 w.2.2 c).1 hd
    unfold Pcs.PUDoomed
    rw [pcsStmt_pos4 D κ nV np C hs w hok]
    refine (pcsDoomed_congrK (pcsIdxK_n _ (hs.lo w.1.val w.1.isLt) (hs.hi w.1.val w.1.isLt)) _ _ _ _ hok
      _ _ c).2 fun q hq => Or.inr fun he => hd' q hq
        ⟨hok, (colEval_plainL _ (hs.lo w.1.val w.1.isLt) (hs.hi w.1.val w.1.isLt) q _ hok).symm.trans he⟩

end Facts

end UniKeccakSound.Rec4

/-- info: 'UniKeccakSound.Rec4.hlink_uni4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.hlink_uni4

/-- info: 'UniKeccakSound.Rec4.hU_uni4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.hU_uni4
