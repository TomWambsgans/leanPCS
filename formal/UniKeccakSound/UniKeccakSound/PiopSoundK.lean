-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The proof is `UniSound/PiopSound.lean`'s, for the
-- Keccak verifier's main line (no pending term; Flock's zeros carried from `C2` on).
import UniSound.PiopSound
import UniKeccakSound.PiopK

/-!
# The Keccak verifier's PIOP is round-by-round sound (main line)

**`uniPiopK Fl I`**: the states `uniPreK`, `uniPostK` and the errors `uniErrK` form a `RbrPiop` on the main line's
rounds, for the Flock phase `Fl` on the Keccak-f block and any identity model `I`, each round as `UniSound.uniPiop`'s
(`mainSound`; Flock's `step`; Schwartz–Zippel for the identities and the merge polynomial; the two combinations over
three commitments; the sumcheck's rounds), and `pre_post` from `main_of_polys` and Flock's `finish` (its ring claim
and its zeros) at the boundary of `C2`'s round.
-/

namespace UniKeccakSound

open LeanVM.Parameters UniStatement UniSound UniKeccak Finset
open scoped ENNReal

variable {F : KeccakVm.KeccakFlockSpec} {D : KDeployment} {κ : ℕ} {v : KeccakVariant} (Fl : KFlockSound F κ v)
  (I : UniIdsK F D Fl)

theorem uniPreK_pre_post (s : USt) (p : Op Stk) (m : Option Stk × List E) (c : List E)
    (m' : Option Stk × List E) (h : uniPreK Fl I s (p ++ [(m, c)]) m') : uniPostK Fl I s p m c := by
  unfold uniPreK at h
  unfold uniPostK
  have hl : (p ++ [(m, c)]).length ≠ 0 := by simp
  rw [ite_eq_right hl] at h
  by_cases hq : (p ++ [(m, c)]).length = Fl.prog.rounds.length + 1
  · rw [ite_eq_left hq] at h
    obtain ⟨c1, c2, h1, -, hP, hEnd, hDone⟩ := h
    refine ⟨c1, h1, ?_⟩
    rw [ite_eq_left (le_of_eq hq), hq, Nat.add_sub_cancel, List.take_length]
    exact ⟨I.main_of_polys _ _ _ _ _ hP, hDone.1, Fl.finish _ _ hDone.1 hDone.2 hEnd⟩
  · rw [ite_eq_right hq] at h
    exact h

/-! ## Each round -/

theorem uniPreK_ne (s : USt) (p : Op Stk) (m : Option Stk × List E) (h0 : p.length ≠ 0)
    (h1 : p.length ≠ Fl.prog.rounds.length + 1) : uniPreK Fl I s p m = uniSK Fl I s p := by
  unfold uniPreK
  rw [ite_eq_right h0, ite_eq_right h1]

/-- **Round `0`**: the bus and the constraints (`mainSound`), Flock's predicate from its state's
start (`S_nil`). -/
theorem uniSoundK_zero (s : USt) (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 6}[¬ uniPreK Fl I s [] m ∧ uniPostK Fl I s [] m c] ≤ I.errMain := by
  have hpre : uniPreK Fl I s [] m = ∃ c, m.1 = some c ∧ RelK F D s c := by
    unfold uniPreK
    rw [ite_eq_left (List.length_nil : ([] : Op Stk).length = 0)]
  rcases hm : m.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, h1, -⟩ := hpost
    simp [rd, hm] at h1
  · refine (prEvent_mono _ _ _ fun c ⟨hn, hpost⟩ => ?_).trans (I.mainSound s c1)
    obtain ⟨c1', h1, hpost⟩ := hpost
    have hx : rd ([] ++ [(m, c)] : Op Stk) 0 = (m, c) := rfl
    rw [hx, hm] at h1
    cases h1
    rw [ite_eq_left (by simp)] at hpost
    obtain ⟨hOK, -, hS⟩ := hpost
    rw [hx] at hOK
    rw [show fdOf Fl.prog.rounds.length ([] ++ [(m, c)] : Op Stk) = [] by simp [fdOf]] at hS
    rw [hpre] at hn
    exact ⟨fun hmain => hn ⟨c1, hm, I.rel_of s c1 hmain (Fl.S_nil _ hS)⟩, hOK⟩

/-- **Flock's round `j − 1`**: Flock's `step`. -/
theorem uniSoundK_flock (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ Fl.prog.rounds.length) (s : USt) (p : Op Stk)
    (hp : p.length = j) (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E ((Fl.prog.rounds[j - 1]'(by omega)).ns + 1)}[
      ¬ uniPreK Fl I s p m ∧ uniPostK Fl I s p m c] ≤ Fl.err (j - 1) := by
  rw [uniPreK_ne Fl I s p m (by omega) (by omega)]
  have hlt : 0 < p.length := by omega
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, hc1, -⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
  have hfd : ∀ c : List E, fdOf Fl.prog.rounds.length (p ++ [(m, c)]) =
      fdOf Fl.prog.rounds.length p ++ [((none, m.2), c)] := fun c =>
    fdOf_append_le _ p _ (by omega) (by omega)
  by_cases hfit : DoneFits (Fl.prog.rounds.take (j - 1)) (fdOf Fl.prog.rounds.length p) ∧
      UMsg.Fits (Fl.prog.rounds[j - 1]'(by omega)) (none, m.2)
  · have hb := Fl.step (j - 1) (by omega) (I.qf c1) _ (none, m.2) hfit.1 hfit.2
    refine (prEvent_mono _ _ _ ?_).trans hb
    rintro c ⟨hn, hpost⟩
    obtain ⟨c1', hc1, hpost⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
    rw [ite_eq_left (by simp; omega)] at hpost
    obtain ⟨hOK, -, hS⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt] at hOK
    rw [hfd] at hS
    refine ⟨fun hS0 => hn ⟨c1, h0, ?_⟩, hS⟩
    rw [ite_eq_left (by omega), hp]
    exact ⟨hOK, hfit.1, hS0⟩
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => hfit ?_
    obtain ⟨c1', -, hpost⟩ := hpost
    rw [ite_eq_left (by simp; omega)] at hpost
    obtain ⟨-, hfits, -⟩ := hpost
    rw [hfd, List.length_append, List.length_singleton, hp, Nat.add_sub_cancel,
      show j = (j - 1) + 1 by omega] at hfits
    exact doneFits_take_succ _ (j - 1) (by omega) _ _ hfits

/-- **`C2`'s round, the point `t`**: Schwartz–Zippel for every identity and the merge
polynomial. -/
theorem uniSoundK_c2 (s : USt) (p : Op Stk) (hp : p.length = Fl.prog.rounds.length + 1)
    (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 1}[¬ uniPreK Fl I s p m ∧ uniPostK Fl I s p m c] ≤
      ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have hpre : uniPreK Fl I s p m = ∃ c1 c2, (rd p 0).1.1 = some c1 ∧ m.1 = some c2 ∧
      (∀ P ∈ I.polys s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2, P = 0) ∧
      FlockEndHoldsK (I.qf c1) (Fl.prog.out (fdOf Fl.prog.rounds.length p) []) ∧
      FlockDoneZ Fl (fdOf Fl.prog.rounds.length p) := by
    unfold uniPreK
    rw [ite_eq_right (by omega), ite_eq_left hp]
  rw [hpre]
  have hlt : 0 < p.length := by omega
  have hx : ∀ c : List E, rd (p ++ [(m, c)]) (Fl.prog.rounds.length + 1) = (m, c) := fun c => by
    rw [← hp, rd_append_self]
  have hfd : ∀ c : List E, fdOf Fl.prog.rounds.length (p ++ [(m, c)]) =
      fdOf Fl.prog.rounds.length p := fun c => fdOf_append_gt _ p _ (by omega)
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, hc1, -⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
  rcases hm : m.1 with _ | c2
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1', -, hpost⟩ := hpost
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, -⟩ := hpost
    rw [hx, hm] at hc2
    cases hc2
  have hb : Pr{let c ← Compose.draws E 1}[∃ P ∈ I.polys s c1 (rd p 0).2
      (fdOf Fl.prog.rounds.length p) c2 ++ [I.zb (fdOf Fl.prog.rounds.length p)], P ≠ 0 ∧
        P.eval (c.headD 0) = 0] ≤
      ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
    refine (prEvent_root_le (I.polys s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2 ++
      [I.zb (fdOf Fl.prog.rounds.length p)])).trans
        (ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _)
    rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    exact Nat.add_le_add (I.deg_le s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2)
      (I.zb_deg _)
  refine (prEvent_mono _ _ _ ?_).trans hb
  rintro c ⟨hn, hpost⟩
  obtain ⟨c1', hc1, hpost⟩ := hpost
  rw [rd_append_lt _ _ 0 hlt, h0] at hc1
  cases hc1
  rw [ite_eq_right (by simp; omega)] at hpost
  obtain ⟨c2', hc2, hDone, hl6, hrest⟩ := hpost
  rw [hx, hm] at hc2
  cases hc2
  rw [ite_eq_left (by simp; omega)] at hrest
  rcases hrest with hzb | hrest
  · rw [hfd, hx] at hzb
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), I.zb_ne _, hzb⟩
  obtain ⟨vals, hz⟩ := hrest
  rw [rd_append_lt _ _ 0 hlt, hfd, hx] at hz
  rw [hfd] at hDone
  have hev := I.diffs_eval _ _ _ _ _ _ _ (by rwa [rd_append_lt _ _ 0 hlt] at hl6) hz
  have hEnd := I.diffs_flock _ _ _ _ _ _ _ hz
  by_contra hno
  refine hn ⟨c1, c2, rfl, rfl, fun P hP => ?_, hEnd, hDone⟩
  by_contra hP0
  exact hno ⟨P, List.mem_append_left _ hP, hP0, hev P hP⟩

/-- **The values' round, `ρ` and `λ`**: the two combinations. -/
theorem uniSoundK_vals (s : USt) (p : Op Stk) (hp : p.length = Fl.prog.rounds.length + 2)
    (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 2}[¬ uniPreK Fl I s p m ∧ uniPostK Fl I s p m c] ≤
      ((I.nRel - 1 + (3 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  rw [uniPreK_ne Fl I s p m (by omega) (by omega)]
  have hlt : 0 < p.length := by omega
  have hlt1 : Fl.prog.rounds.length + 1 < p.length := by omega
  have hx : ∀ c : List E, rd (p ++ [(m, c)]) (Fl.prog.rounds.length + 2) = (m, c) := fun c => by
    rw [← hp, rd_append_self]
  have hfd : ∀ c : List E, fdOf Fl.prog.rounds.length (p ++ [(m, c)]) =
      fdOf Fl.prog.rounds.length p := fun c => fdOf_append_gt _ p _ (by omega)
  have hbr : ∀ c : List E, brOf Fl.prog.rounds.length (p ++ [(m, c)]) = [] := fun c =>
    brOf_of_length _ _ (by simp; omega)
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, hc1, -⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
  rcases h2 : (rd p (Fl.prog.rounds.length + 1)).1.1 with _ | c2
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1', -, hpost⟩ := hpost
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, h2] at hc2
    cases hc2
  by_cases hzb : (I.zb (fdOf Fl.prog.rounds.length p)).eval
      ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) = 0
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨hn, hpost⟩ => hn ?_
    obtain ⟨c1', hc1, hpost⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, hDone, hl6, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, h2] at hc2
    cases hc2
    refine ⟨c1, h0, ?_⟩
    rw [ite_eq_right (by omega)]
    exact ⟨c2, h2, by rwa [hfd] at hDone, by rwa [rd_append_lt _ _ 0 hlt] at hl6, Or.inl hzb⟩
  by_cases hbad : ∃ d ∈ I.diffs s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2
      ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) m.2, ∃ x ∈ d, x ≠ 0
  · have hb := prEvent_twoLevel_le (I.diffs s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2
      ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) m.2) I.nRel 3
      (I.diffs_len s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2
        ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) m.2)
      (I.diffs_count s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2
        ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) m.2) hbad
    refine (prEvent_mono _ _ _ ?_).trans hb
    rintro c ⟨-, hpost⟩
    obtain ⟨c1', hc1, hpost⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, -, -, hrest⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, h2] at hc2
    cases hc2
    rw [ite_eq_right (by simp; omega)] at hrest
    rcases hrest with hz | hrest
    · rw [rd_append_lt _ _ _ hlt1, hfd] at hz
      exact absurd hz hzb
    rw [hbr, rd_append_lt _ _ 0 hlt, rd_append_lt _ _ _ hlt1, hfd, hx] at hrest
    unfold SumState claimAfter pointAfter at hrest
    simp only [List.map_nil] at hrest
    rw [← I.batch_start, show (I.prod _ _ _ _ _ _ _ _ _).T [] = _ from hrest.symm]
    exact CharTwo.add_self_eq_zero _
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨hn, hpost⟩ => hn ?_
    obtain ⟨c1', hc1, hpost⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, hDone, hl6, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, h2] at hc2
    cases hc2
    refine ⟨c1, h0, ?_⟩
    rw [ite_eq_right (by omega)]
    refine ⟨c2, h2, by rwa [hfd] at hDone, by rwa [rd_append_lt _ _ 0 hlt] at hl6, Or.inr ?_⟩
    rw [ite_eq_left hp]
    refine ⟨m.2, fun d hd x hx => ?_⟩
    by_contra hx0
    exact hbad ⟨d, hd, x, hx, hx0⟩

/-- **A round of the batching sumcheck**: `2 / |E|`. -/
theorem uniSoundK_batch (j : ℕ) (h1 : Fl.prog.rounds.length + 3 ≤ j)
    (h2 : j < Fl.prog.rounds.length + 3 + I.V) (s : USt) (p : Op Stk) (hp : p.length = j)
    (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 1}[¬ uniPreK Fl I s p m ∧ uniPostK Fl I s p m c] ≤
      ((2 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  rw [uniPreK_ne Fl I s p m (by omega) (by omega)]
  have hlt : 0 < p.length := by omega
  have hlt1 : Fl.prog.rounds.length + 1 < p.length := by omega
  have hlt2 : Fl.prog.rounds.length + 2 < p.length := by omega
  have hfd : ∀ c : List E, fdOf Fl.prog.rounds.length (p ++ [(m, c)]) =
      fdOf Fl.prog.rounds.length p := fun c => fdOf_append_gt _ p _ (by omega)
  have hbr : ∀ c : List E, brOf Fl.prog.rounds.length (p ++ [(m, c)]) =
      brOf Fl.prog.rounds.length p ++ [(m.2, c)] := fun c => brOf_append _ _ _ (by omega)
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1, hc1, -⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
  rcases hc2' : (rd p (Fl.prog.rounds.length + 1)).1.1 with _ | c2
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hpost⟩ => ?_
    obtain ⟨c1', -, hpost⟩ := hpost
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, hc2'] at hc2
    cases hc2
  by_cases hzb : (I.zb (fdOf Fl.prog.rounds.length p)).eval
      ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) = 0
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨hn, hpost⟩ => hn ?_
    obtain ⟨c1', hc1, hpost⟩ := hpost
    rw [rd_append_lt _ _ 0 hlt, h0] at hc1
    cases hc1
    rw [ite_eq_right (by simp; omega)] at hpost
    obtain ⟨c2', hc2, hDone, hl6, -⟩ := hpost
    rw [rd_append_lt _ _ _ hlt1, hc2'] at hc2
    cases hc2
    refine ⟨c1, h0, ?_⟩
    rw [ite_eq_right (by omega)]
    exact ⟨c2, hc2', by rwa [hfd] at hDone, by rwa [rd_append_lt _ _ 0 hlt] at hl6, Or.inl hzb⟩
  set O := (I.prod s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2
    ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) (rd p (Fl.prog.rounds.length + 2)).1.2
    ((rd p (Fl.prog.rounds.length + 2)).2.headD 0)
    ((rd p (Fl.prog.rounds.length + 2)).2.getD 1 0)).oracle with hO
  set tg := I.target s c1 (rd p 0).2 (fdOf Fl.prog.rounds.length p) c2
    ((rd p (Fl.prog.rounds.length + 1)).2.headD 0) (rd p (Fl.prog.rounds.length + 2)).1.2
    ((rd p (Fl.prog.rounds.length + 2)).2.headD 0)
    ((rd p (Fl.prog.rounds.length + 2)).2.getD 1 0) with htg
  have hvars : (brOf Fl.prog.rounds.length p).length < O.vars := by
    rw [length_brOf, hO]
    show _ < (I.prod _ _ _ _ _ _ _ _ _).vars
    rw [I.prod_vars]
    omega
  have hb := O.step_sound tg (brOf Fl.prog.rounds.length p) hvars m.2
  refine (prEvent_mono _ _ _ ?_).trans hb
  rintro c ⟨hn, hpost⟩
  obtain ⟨c1', hc1, hpost⟩ := hpost
  rw [rd_append_lt _ _ 0 hlt, h0] at hc1
  cases hc1
  rw [ite_eq_right (by simp; omega)] at hpost
  obtain ⟨c2', hc2, hDone, hl6, hrest⟩ := hpost
  rw [rd_append_lt _ _ _ hlt1, hc2'] at hc2
  cases hc2
  rw [ite_eq_right (by simp; omega)] at hrest
  rcases hrest with hz | hrest
  · rw [rd_append_lt _ _ _ hlt1, hfd] at hz
    exact absurd hz hzb
  rw [hbr, rd_append_lt _ _ 0 hlt, rd_append_lt _ _ _ hlt1, rd_append_lt _ _ _ hlt2, hfd] at hrest
  refine ⟨fun hS => hn ⟨c1, h0, ?_⟩, hrest⟩
  rw [ite_eq_right (by omega)]
  refine ⟨c2, hc2', by rwa [hfd] at hDone, by rwa [rd_append_lt _ _ 0 hlt] at hl6, Or.inr ?_⟩
  rw [ite_eq_right (by omega)]
  exact hS

/-! ## The protocol -/

/-- **The univariate PIOP, round by round** (main line), for the Flock phase `Fl` and the identity
model `I`. -/
noncomputable def uniPiopK : RbrPiop (uniRounds Fl.prog.rounds I.nV I.V) USt Stk where
  pre := uniPreK Fl I
  post := uniPostK Fl I
  pre_post := uniPreK_pre_post Fl I
  err := uniErrK Fl I
  sound j s p m hj hp := by
    rw [length_uniRounds] at hj
    unfold uniErrK
    by_cases h0 : j = 0
    · subst h0
      rw [ite_eq_left rfl, uniRounds_zero]
      obtain rfl : p = [] := List.length_eq_zero_iff.mp hp
      exact uniSoundK_zero Fl I s m
    rw [ite_eq_right h0]
    by_cases h1 : j ≤ Fl.prog.rounds.length
    · rw [ite_eq_left h1, uniRounds_flock _ _ _ j (by omega) h1,
        List.getD_eq_getElem _ _ (by omega)]
      exact uniSoundK_flock Fl I j (by omega) h1 s p hp m
    rw [ite_eq_right h1]
    by_cases h2 : j = Fl.prog.rounds.length + 1
    · subst h2
      rw [ite_eq_left rfl, uniRounds_c2]
      exact uniSoundK_c2 Fl I s p hp m
    rw [ite_eq_right h2]
    by_cases h3 : j = Fl.prog.rounds.length + 2
    · subst h3
      rw [ite_eq_left rfl, uniRounds_vals]
      exact uniSoundK_vals Fl I s p hp m
    rw [ite_eq_right h3, uniRounds_batch _ _ _ j (by omega) hj]
    exact uniSoundK_batch Fl I j (by omega) hj s p hp m

end UniKeccakSound
