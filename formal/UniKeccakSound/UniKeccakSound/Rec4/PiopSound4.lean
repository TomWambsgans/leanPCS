-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proofs follow `PiopSoundK3.lean`'s (which they call
-- on π1-rec4's transcript read as π1-rec3's) and `Flock/RoundByRound.lean`'s bad-family steps.
import UniKeccakSound.Rec4.Piop4

/-!
# π1-rec4's PIOP is round-by-round sound

**`uniPiopK4 hT I BR hzb hpolys : RbrPiop (rec4Rounds κ I.nV np) USt Stk`**: the states `uniSK4` (π1-rec3's on `opT`,
and `c2St` after `C2`'s round), `uniPreK4`, `uniErrK4`, round by round: round `0` the bus's error and Flock's first
round's; Flock's rounds and the batch's π1-rec3's (`uniSoundK3_flock`, `uniSoundK3_batch` on `opT`); `C2`'s the
identities' Schwartz–Zippel at `t` (`degSum + degBad`) and the bad sets of `f_0 … f_3` (`4 · 15`); the values' the
two combinations (`nRel − 1 + 2`) and the bad sets of `f_4, f_5` (`2 · 15`), the challenges of a wide draw
independent (`Draws.lean`).
-/

namespace UniKeccakSound.Rec4

open LeanVM.Parameters UniStatement UniSound UniKeccak Finset
open UniKeccakSound.KF (stateOfK kBad3 HitInK HitRoundK dBound3K)
open scoped ENNReal

/-! ## Flock's state, a round extended -/

section Hit

variable {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} (B : KF.KBadFamily κ) (qf : LeanVM.Protocol.Column (KeccakVm.kWords + κ))

theorem hitInK_of_round (done : Done) (msg : UMsg) (c : List E) (h : HitRoundK B qf done msg c) :
    HitInK B qf (done ++ [(msg, c)]) := by
  unfold HitInK
  split
  · simp_all
  · refine ⟨done.length, by simp, ?_⟩
    rw [List.take_left' rfl, List.getElem_append_right (le_refl _)]
    simpa using h

theorem hitInK_of_prefix (done : Done) (x : UMsg × List E) (h : HitInK B qf done) :
    HitInK B qf (done ++ [x]) := by
  have h' : ∃ j, ∃ hj : j < done.length, HitRoundK B qf (done.take j) (done[j]'hj).1 (done[j]'hj).2 := by
    unfold HitInK at h
    split at h
    · exact h.elim
    · exact h
  obtain ⟨j, hj, hr⟩ := h'
  unfold HitInK
  split
  · simp_all
  · refine ⟨j, by simp; omega, ?_⟩
    rw [List.take_append_of_le_length hj.le, List.getElem_append_left hj]
    exact hr

/-- **A round extended**: a hit in it is a hit in its first challenges or in the new ones, after them. -/
theorem hitRound_append (done : Done) (msg : UMsg) (fs y : List E) (h : HitRoundK B qf done msg (fs ++ y)) :
    HitRoundK B qf done msg fs ∨ ∃ i < y.length, y.getD i 0 ∈ B qf done msg (fs ++ y.take i) := by
  obtain ⟨i, hi, hm⟩ := h
  by_cases hlt : i < fs.length
  · left
    refine ⟨i, hlt, ?_⟩
    rwa [List.getD_append _ _ _ _ hlt, List.take_append_of_le_length hlt.le] at hm
  · right
    simp only [List.length_append] at hi
    refine ⟨i - fs.length, by omega, ?_⟩
    rw [List.getD_append_right _ _ _ _ (by omega), List.take_append, List.take_of_length_le (by omega)] at hm
    exact hm

theorem state_extend {done : Done} {msg : UMsg} {fs : List E} {y : List E}
    (hn : ¬ stateOfK F B qf (done ++ [(msg, fs)])) (h : stateOfK F B qf (done ++ [(msg, fs ++ y)])) :
    ∃ i < y.length, y.getD i 0 ∈ B qf done msg (fs ++ y.take i) := by
  simp only [KF.stateOfK, not_or] at hn
  rcases h with h | h
  · exact absurd h hn.1
  rcases KF.hitInK_append B qf done msg _ h with h | h
  · exact absurd (hitInK_of_prefix B qf done _ h) hn.2
  rcases hitRound_append B qf done msg fs y h with h | h
  · exact absurd (hitInK_of_round B qf done msg fs h) hn.2
  · exact h

theorem state_of_empty {done : Done} {msg : UMsg} (h : stateOfK F B qf (done ++ [(msg, [])])) :
    stateOfK F B qf done := by
  rcases h with h | h
  · exact Or.inl h
  rcases KF.hitInK_append B qf done msg [] h with h | h
  · exact Or.inr h
  · obtain ⟨i, hi, -⟩ := h
    simp at hi

theorem state_empty_of {done : Done} {msg : UMsg} (h : stateOfK F B qf done) :
    stateOfK F B qf (done ++ [(msg, [])]) := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (hitInK_of_prefix B qf done _ h)

end Hit

/-! ## The states -/

section States

variable {F : KeccakVm.KeccakFlockSpec} {D : KDeployment} {κ : ℕ} (hT : KF.TerminalSpecK F) {np : ℕ}
  (I : UniIdsK3 F D (KF.kFlockSoundRec3 F hT κ) np) (BR : PairBatch np)

theorem nF3 : (KF.kFlockSoundRec3 F hT κ).prog.rounds.length = 29 + κ := KF.length_kRounds κ _

/-- **The state after `C2`'s round**: `C1`'s and `C2`'s candidates, Flock's front done and its structured terminal
zero, and either `t` a root of the merge polynomial, or Flock's state with `f_0 … f_3` and the identities vanishing
at `t` for some values and some further map. -/
def c2St (s : USt) (q : Op Stk) : Prop :=
  ∃ c1, (rd q 0).1.1 = some c1 ∧ ∃ c2, (rd q (28 + κ)).1.1 = some c2 ∧
    DoneFits (KF.kRoundsPre κ KF.r0Rec3) (vFrontO κ q) ∧ ((rd q (28 + κ)).1.2.take 64).length = 64 ∧
    KF.kTerm κ (KF.sampRec3 κ) (vFrontO κ q) ((rd q (28 + κ)).1.2.take 64) = 0 ∧
    ((I.zb (vFrontO κ q ++ [((none, (rd q (28 + κ)).1.2.take 64), (rd q (28 + κ)).2.drop 1)])).eval
        ((rd q (28 + κ)).2.headD 0) = 0 ∨
      (stateOfK F (kBad3 F κ) (I.qf c1)
          (vFrontO κ q ++ [((none, (rd q (28 + κ)).1.2.take 64), (rd q (28 + κ)).2.drop 1)]) ∧
        ∃ vals g, ∀ d ∈ I.diffs s c1 ((rd q 0).2.take 3)
          (vFrontO κ q ++ [((none, (rd q (28 + κ)).1.2.take 64), (rd q (28 + κ)).2.drop 1 ++ g)]) c2
          ((rd q (28 + κ)).2.headD 0) vals, ∀ x ∈ d, x = 0))

/-- **The state after the opened rounds `q`**: π1-rec3's on `q` read as π1-rec3's, but after `C2`'s round. -/
def uniSK4 (s : USt) (q : Op Stk) : Prop :=
  if q.length = 29 + κ then c2St hT I s q else uniSK3 (KF.kFlockSoundRec3 F hT κ) I BR s (opT κ q)

/-- **The state before a round's challenges**: before round `0`, the relation of `C1`'s candidate; before `C2`'s
round's, the identities as polynomials for `C2`'s candidate, Flock's state on its front, its front done and its
terminal zero; else the state after the rounds before. -/
def uniPreK4 (s : USt) (p : Op Stk) (m : Option Stk × List E) : Prop :=
  if p.length = 0 then ∃ c, m.1 = some c ∧ RelK F D s c
  else if p.length = 28 + κ then ∃ c1 c2, (rd p 0).1.1 = some c1 ∧ m.1 = some c2 ∧
      (∀ P ∈ I.polys s c1 ((rd p 0).2.take 3) (vFrontO κ p ++ [((none, m.2.take 64), [])]) c2, P = 0) ∧
      stateOfK F (kBad3 F κ) (I.qf c1) (vFrontO κ p) ∧ DoneFits (KF.kRoundsPre κ KF.r0Rec3) (vFrontO κ p) ∧
      (m.2.take 64).length = 64 ∧ KF.kTerm κ (KF.sampRec3 κ) (vFrontO κ p) (m.2.take 64) = 0
  else uniSK4 hT I BR s p

/-- **The state after a round's challenges.** -/
def uniPostK4 (s : USt) (p : Op Stk) (m : Option Stk × List E) (c : List E) : Prop :=
  uniSK4 hT I BR s (p ++ [(m, c)])

/-- **The rounds' errors.** -/
noncomputable def uniErrK4 (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then I.errMain + (KF.kFlockSoundRec3 F hT κ).err 0
  else if j ≤ 27 + κ then (KF.kFlockSoundRec3 F hT κ).err j
  else if j = 28 + κ then
    ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) + ((60 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
  else if j = 29 + κ then
    ((I.nRel - 1 + (3 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) + ((30 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞)
  else if j < 30 + κ + np then BR.errPair else BR.errLast

theorem uniSK4_ne (s : USt) (q : Op Stk) (h : q.length ≠ 29 + κ) :
    uniSK4 hT I BR s q = uniSK3 (KF.kFlockSoundRec3 F hT κ) I BR s (opT κ q) := by
  unfold uniSK4
  rw [ite_eq_right h]

theorem uniPreK4_ne (s : USt) (p : Op Stk) (m : Option Stk × List E) (h0 : p.length ≠ 0)
    (h1 : p.length ≠ 28 + κ) : uniPreK4 hT I BR s p m = uniSK4 hT I BR s p := by
  unfold uniPreK4
  rw [ite_eq_right h0, ite_eq_right h1]

theorem vFrontO_append (p : Op Stk) (x : (Option Stk × List E) × List E) (h : 28 + κ ≤ p.length) :
    vFrontO κ (p ++ [x]) = vFrontO κ p := by
  have hr : rd (p ++ [x]) 0 = rd p 0 := rd_append_lt _ _ 0 (by omega)
  unfold vFrontO
  rw [hr, List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- `uniSK3` at a transcript of at most `nF + 1` rounds. -/
theorem uniSK3_le (s : USt) (q : Op Stk) (hq : q.length ≤ 30 + κ) :
    uniSK3 (KF.kFlockSoundRec3 F hT κ) I BR s q ↔ ∃ c1, (rd q 0).1.1 = some c1 ∧
      I.MainOK s c1 (rd q 0).2 ∧
      DoneFits ((KF.kFlockSoundRec3 F hT κ).prog.rounds.take (q.length - 1)) (fdOf (29 + κ) q) ∧
      (KF.kFlockSoundRec3 F hT κ).S (I.qf c1) (fdOf (29 + κ) q) := by
  unfold uniSK3
  rw [nF3 hT]
  refine exists_congr fun c1 => and_congr_right fun _ => ?_
  rw [ite_eq_left (by omega)]

/-- `uniSK3` at a transcript past the values' round. -/
theorem uniSK3_ge (s : USt) (q : Op Stk) (hq : 32 + κ ≤ q.length) :
    uniSK3 (KF.kFlockSoundRec3 F hT κ) I BR s q ↔ ∃ c1, (rd q 0).1.1 = some c1 ∧
      ∃ c2, (rd q (30 + κ)).1.1 = some c2 ∧ FlockDoneK3 (KF.kFlockSoundRec3 F hT κ) (fdOf (29 + κ) q) ∧
      (KF.kFlockSoundRec3 F hT κ).prog.ZerosVanish (fdOf (29 + κ) q) [] ∧
      ((I.zb (fdOf (29 + κ) q)).eval ((rd q (30 + κ)).2.headD 0) = 0 ∨
        BR.St (I.prod s c1 (rd q 0).2 (fdOf (29 + κ) q) c2 ((rd q (30 + κ)).2.headD 0)
            (rd q (31 + κ)).1.2 ((rd q (31 + κ)).2.headD 0) ((rd q (31 + κ)).2.getD 1 0))
          (I.target s c1 (rd q 0).2 (fdOf (29 + κ) q) c2 ((rd q (30 + κ)).2.headD 0)
            (rd q (31 + κ)).1.2 ((rd q (31 + κ)).2.headD 0) ((rd q (31 + κ)).2.getD 1 0))
          (brOf (29 + κ) q)) := by
  unfold uniSK3
  rw [nF3 hT]
  refine exists_congr fun c1 => and_congr_right fun _ => ?_
  rw [ite_eq_right (by omega)]
  refine exists_congr fun c2 => ?_
  rw [show 29 + κ + 1 = 30 + κ by omega, show 29 + κ + 2 = 31 + κ by omega, ite_eq_right (by omega)]

/-! ## Draws of one -/

theorem prEvent_draws_one (Q : List E → Prop) :
    Pr{let y ← Compose.draws E 1}[Q [y.headD 0]] = Pr{let y ← Compose.draws E 1}[Q y] := by
  simp [Compose.draws]

theorem getD_three (c : List E) : c.getD 3 0 = (c.drop 3).headD 0 := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩ <;> rfl

/-! ## The rounds' soundness -/

section Sound

variable (hzb : ∀ (fd : Done) (x y : UMsg × List E), fd.length = 28 + κ → I.zb (fd ++ [x]) = I.zb (fd ++ [y]))
  (hpolys : ∀ (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (x y : UMsg × List E) (c2 : Stk),
    fd.length = 28 + κ → I.polys s c1 ch (fd ++ [x]) c2 = I.polys s c1 ch (fd ++ [y]) c2)

/-- **Round `0`**: the bus at `c, β, γ` (`mainSound`) and Flock's first challenge `c'` (its first round's bad set). -/
theorem uniSoundK4_zero (s : USt) (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E (3 + 1)}[¬ uniPreK4 hT I BR s [] m ∧ uniPostK4 hT I BR s [] m c] ≤
      I.errMain + (KF.kFlockSoundRec3 F hT κ).err 0 := by
  have hpre : uniPreK4 hT I BR s [] m = ∃ c, m.1 = some c ∧ RelK F D s c := by
    unfold uniPreK4
    rw [ite_eq_left (List.length_nil : ([] : Op Stk).length = 0)]
  have hpost : ∀ c : List E, uniPostK4 hT I BR s [] m c ↔ ∃ c1, m.1 = some c1 ∧ I.MainOK s c1 (c.take 3) ∧
      DoneFits ((KF.kFlockSoundRec3 F hT κ).prog.rounds.take 1) [((none, []), [c.getD 3 0])] ∧
      (KF.kFlockSoundRec3 F hT κ).S (I.qf c1) [((none, []), [c.getD 3 0])] := by
    intro c
    unfold uniPostK4
    rw [uniSK4_ne hT I BR s _ (by simp; omega), uniSK3_le hT I BR s _ (by rw [length_opT_le _ (by simp) (by simp; omega)]; simp; omega),
      length_opT_le _ (by simp) (by simp; omega), fdOf_opT_le _ (by simp) (by simp; omega), rd_opT_zero]
    simp [r0Op, rd, vFrontO]
  rcases hm : m.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hp⟩ => ?_
    obtain ⟨c1, h1, -⟩ := (hpost c).mp hp
    rw [hm] at h1
    cases h1
  have hb1 : Pr{let c ← Compose.draws E (3 + 1)}[¬ I.MainHolds s c1 ∧ I.MainOK s c1 (c.take 3)] ≤ I.errMain := by
    rw [prEvent_draws_take 3 1 (fun x => ¬ I.MainHolds s c1 ∧ I.MainOK s c1 x)]
    exact I.mainSound s c1
  have hb2 : Pr{let c ← Compose.draws E (3 + 1)}[¬ (KF.kFlockSoundRec3 F hT κ).S (I.qf c1) [] ∧
      (KF.kFlockSoundRec3 F hT κ).S (I.qf c1) [((none, []), [c.getD 3 0])]] ≤
        (KF.kFlockSoundRec3 F hT κ).err 0 := by
    simp only [getD_three]
    rw [prEvent_draws_drop 3 1 (fun y => ¬ (KF.kFlockSoundRec3 F hT κ).S (I.qf c1) [] ∧
      (KF.kFlockSoundRec3 F hT κ).S (I.qf c1) [((none, []), [y.headD 0])]),
      prEvent_draws_one (fun y => ¬ (KF.kFlockSoundRec3 F hT κ).S (I.qf c1) [] ∧
        (KF.kFlockSoundRec3 F hT κ).S (I.qf c1) [((none, []), y)])]
    have h := (KF.kFlockSoundRec3 F hT κ).step 0 (by rw [nF3 hT]; omega) (I.qf c1) [] (none, [])
      (by simp [DoneFits]) (by simp [UMsg.Fits, KF.kFlockSoundRec3, KF.ofFamilyK, KF.kProg3, KF.kProgWith,
        KF.kRounds, KF.kRoundsPre])
    simpa [KF.kFlockSoundRec3, KF.ofFamilyK, KF.kProg3, KF.kProgWith, KF.kRounds, KF.kRoundsPre] using h
  refine (prEvent_mono _ _ _ fun c ⟨hn, hp⟩ => ?_).trans ((prEvent_or_le _ _ _).trans (add_le_add hb1 hb2))
  obtain ⟨c1', h1, hOK, -, hS⟩ := (hpost c).mp hp
  rw [hm] at h1
  cases h1
  rw [hpre] at hn
  by_cases hmain : I.MainHolds s c1
  · right
    refine ⟨fun hS0 => hn ⟨c1, hm, I.rel_of s c1 hmain ((KF.kFlockSoundRec3 F hT κ).S_nil _ hS0)⟩, hS⟩
  · exact Or.inl ⟨hmain, hOK⟩

/-- **Flock's round `j`** (`1 ≤ j ≤ 27 + κ`): π1-rec3's Flock round `j` on `opT`. -/
theorem uniSoundK4_mid (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 27 + κ) (s : USt) (p : Op Stk) (hp : p.length = j)
    (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E (((KF.kFlockSoundRec3 F hT κ).prog.rounds[j]'(by rw [nF3 hT]; omega)).ns + 1)}[
      ¬ uniPreK4 hT I BR s p m ∧ uniPostK4 hT I BR s p m c] ≤ (KF.kFlockSoundRec3 F hT κ).err j := by
  rw [uniPreK4_ne hT I BR s p m (by omega) (by omega), uniSK4_ne hT I BR s p (by omega)]
  have hpost : ∀ c, uniPostK4 hT I BR s p m c =
      uniSK3 (KF.kFlockSoundRec3 F hT κ) I BR s (opT κ p ++ [(m, c)]) := fun c => by
    unfold uniPostK4
    rw [uniSK4_ne hT I BR s _ (by simp; omega), opT_append_le _ _ (by omega) (by omega)]
  simp only [hpost]
  have hl : (opT κ p).length = j + 1 := by rw [length_opT_le p (by omega) (by omega), hp]
  have h := uniSoundK3_flock (KF.kFlockSoundRec3 F hT κ) I BR (j + 1) (by omega) (by rw [nF3 hT]; omega) s
    (opT κ p) hl m
  rw [uniPreK3_ne (KF.kFlockSoundRec3 F hT κ) I BR s (opT κ p) m (by omega) (by rw [nF3 hT]; omega)] at h
  simpa [uniPostK3] using h

/-- **A round of the batch** (`30 + κ ≤ j ≤ 30 + κ + np`): π1-rec3's on `opT`. -/
theorem uniSoundK4_batch (j : ℕ) (h1 : 30 + κ ≤ j) (h2 : j ≤ 30 + κ + np) (s : USt) (p : Op Stk)
    (hp : p.length = j) (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E 1}[¬ uniPreK4 hT I BR s p m ∧ uniPostK4 hT I BR s p m c] ≤
      if j < 30 + κ + np then BR.errPair else BR.errLast := by
  rw [uniPreK4_ne hT I BR s p m (by omega) (by omega), uniSK4_ne hT I BR s p (by omega)]
  have hpost : ∀ c, uniPostK4 hT I BR s p m c =
      uniSK3 (KF.kFlockSoundRec3 F hT κ) I BR s (opT κ p ++ [(m, c)]) := fun c => by
    unfold uniPostK4
    rw [uniSK4_ne hT I BR s _ (by simp; omega), opT_append_ge _ _ (by omega)]
  simp only [hpost]
  have hl : (opT κ p).length = j + 2 := by rw [length_opT_ge p (by omega), hp]
  have h := uniSoundK3_batch (KF.kFlockSoundRec3 F hT κ) I BR (j + 2) (by rw [nF3 hT]; omega)
    (by rw [nF3 hT]; omega) s (opT κ p) hl m
  rw [uniPreK3_ne (KF.kFlockSoundRec3 F hT κ) I BR s (opT κ p) m (by omega) (by rw [nF3 hT]; omega)] at h
  have hif : (if j + 2 < (KF.kFlockSoundRec3 F hT κ).prog.rounds.length + 3 + np then BR.errPair
      else BR.errLast) = if j < 30 + κ + np then BR.errPair else BR.errLast := by
    rw [nF3 hT]
    by_cases hj : j < 30 + κ + np
    · rw [ite_eq_left hj, ite_eq_left (by omega)]
    · rw [ite_eq_right hj, ite_eq_right (by omega)]
  rw [hif] at h
  simpa [uniPostK3] using h

theorem dBound3K_le_15 (j i : ℕ) (hj : j ≠ 0) : dBound3K κ j i ≤ 15 := by
  unfold dBound3K
  rw [ite_eq_right hj]
  exact KF.dBoundK_le κ j i

theorem doneFits_last : ∀ (rs : List Compose.RoundSpec) (r : Compose.RoundSpec) (d : Done) (x : UMsg × List E),
    DoneFits (rs ++ [r]) (d ++ [x]) → x.1.Fits r ∧ x.2.length = r.ns + 1
  | [], r, [], x, h => ⟨h.1, h.2.1⟩
  | _ :: rs, r, _ :: d, x, h => doneFits_last rs r d x h.2.2
  | [], _, _ :: d, _, h => by
    rcases d with _ | ⟨y, d⟩ <;> exact h.2.2.elim
  | _ :: rs, _, [], _, h => by
    rcases rs with _ | ⟨y, rs⟩ <;> exact h.2.2.elim


include hzb hpolys in
/-- **`C2`'s round, `t` and `f_0 … f_3`**: the identities' Schwartz–Zippel and the merge polynomial at `t`, the
ring map's first four bad sets. -/
theorem uniSoundK4_c2 (s : USt) (p : Op Stk) (hp : p.length = 28 + κ) (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E (4 + 1)}[¬ uniPreK4 hT I BR s p m ∧ uniPostK4 hT I BR s p m c] ≤
      ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) + ((60 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have hpre : uniPreK4 hT I BR s p m ↔ ∃ c1 c2, (rd p 0).1.1 = some c1 ∧ m.1 = some c2 ∧
      (∀ P ∈ I.polys s c1 ((rd p 0).2.take 3) (vFrontO κ p ++ [((none, m.2.take 64), [])]) c2, P = 0) ∧
      stateOfK F (kBad3 F κ) (I.qf c1) (vFrontO κ p) ∧ DoneFits (KF.kRoundsPre κ KF.r0Rec3) (vFrontO κ p) ∧
      (m.2.take 64).length = 64 ∧ KF.kTerm κ (KF.sampRec3 κ) (vFrontO κ p) (m.2.take 64) = 0 := by
    unfold uniPreK4
    rw [ite_eq_right (by omega), ite_eq_left hp]
  have e0 : ∀ c : List E, rd (p ++ [(m, c)]) 0 = rd p 0 := fun c => rd_append_lt _ _ 0 (by omega)
  have e2 : ∀ c : List E, rd (p ++ [(m, c)]) (28 + κ) = (m, c) := fun c => by rw [← hp, rd_append_self]
  have ev : ∀ c : List E, vFrontO κ (p ++ [(m, c)]) = vFrontO κ p := fun c => vFrontO_append p _ (by omega)
  have hpost : ∀ c : List E, uniPostK4 hT I BR s p m c ↔ c2St hT I s (p ++ [(m, c)]) := fun c => by
    unfold uniPostK4 uniSK4
    rw [ite_eq_left (by simp; omega)]
  have hvf : (vFrontO κ p).length = 28 + κ := length_vFrontO p (by omega)
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hq⟩ => ?_
    obtain ⟨c1, h1, -⟩ := (hpost c).mp hq
    rw [e0, h0] at h1
    cases h1
  rcases hm : m.1 with _ | c2
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hq⟩ => ?_
    obtain ⟨c1, -, c2, h2, -⟩ := (hpost c).mp hq
    rw [e2, hm] at h2
    cases h2
  generalize hvfd : vFrontO κ p = vf at hpre ev hvf
  generalize hchd : (rd p 0).2.take 3 = ch at hpre
  have hincl : ∀ c : List E, ¬ uniPreK4 hT I BR s p m ∧ uniPostK4 hT I BR s p m c →
      (∃ P ∈ I.polys s c1 ch (vf ++ [((none, m.2.take 64), [])]) c2 ++
          [I.zb (vf ++ [((none, m.2.take 64), [])])], P ≠ 0 ∧ P.eval ((c.take 1).headD 0) = 0) ∨
        (∃ i < (c.drop 1).length, (c.drop 1).getD i 0 ∈
          kBad3 F κ (I.qf c1) vf (none, m.2.take 64) ((c.drop 1).take i)) := by
    intro c ⟨hn, hq⟩
    obtain ⟨c1', h1, c2', h2, hFD, hSL, hFZ, hrest⟩ := (hpost c).mp hq
    rw [e0, h0] at h1
    cases h1
    rw [e2, hm] at h2
    cases h2
    rw [e2, ev, e0, hchd] at hrest
    rw [ev] at hFD hFZ
    rw [e2] at hSL hFZ
    have ht : (c.take 1).headD 0 = c.headD 0 := by cases c <;> rfl
    rcases hrest with hz | ⟨hS, vals, g, hD⟩
    · left
      refine ⟨I.zb (vf ++ [((none, m.2.take 64), [])]), List.mem_append_right _ (List.mem_singleton_self _),
        I.zb_ne _, ?_⟩
      rw [ht, ← hzb vf _ _ hvf]
      exact hz
    · have hev := I.diffs_eval _ _ _ _ _ _ _ hD
      rw [hpolys s c1 ch vf _ ((none, m.2.take 64), []) c2 hvf] at hev
      by_cases hall : ∀ P ∈ I.polys s c1 ch (vf ++ [((none, m.2.take 64), [])]) c2, P = 0
      · right
        have hS0 : ¬ stateOfK F (kBad3 F κ) (I.qf c1) vf := fun hS0 =>
          hn ((hpre).mpr ⟨c1, c2, h0, hm, hall, hS0, hFD, hSL, hFZ⟩)
        have hS0' : ¬ stateOfK F (kBad3 F κ) (I.qf c1) (vf ++ [((none, m.2.take 64), [])]) := fun h =>
          hS0 (state_of_empty (kBad3 F κ) (I.qf c1) h)
        have hS' : stateOfK F (kBad3 F κ) (I.qf c1) (vf ++ [((none, m.2.take 64), [] ++ c.drop 1)]) := by
          rw [List.nil_append]
          exact hS
        obtain ⟨i, hi, hm'⟩ := state_extend (kBad3 F κ) (I.qf c1) (fs := []) hS0' hS'
        rw [List.nil_append] at hm'
        exact ⟨i, hi, hm'⟩
      · left
        push Not at hall
        obtain ⟨P, hP, hP0⟩ := hall
        exact ⟨P, List.mem_append_left _ hP, hP0, by rw [ht]; exact hev P hP⟩
  have hA : Pr{let c ← Compose.draws E (4 + 1)}[∃ P ∈ I.polys s c1 ch (vf ++ [((none, m.2.take 64), [])]) c2 ++
      [I.zb (vf ++ [((none, m.2.take 64), [])])], P ≠ 0 ∧ P.eval ((c.take 1).headD 0) = 0] ≤
      ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
    rw [show (4 + 1 : ℕ) = 1 + 4 from rfl, prEvent_draws_take 1 4 (fun x => ∃ P ∈ I.polys s c1 ch
      (vf ++ [((none, m.2.take 64), [])]) c2 ++ [I.zb (vf ++ [((none, m.2.take 64), [])])], P ≠ 0 ∧
        P.eval (x.headD 0) = 0)]
    refine (prEvent_root_le _).trans (ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _)
    rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    exact Nat.add_le_add (I.deg_le s c1 ch _ c2) (I.zb_deg _)
  have hH : Pr{let c ← Compose.draws E (4 + 1)}[∃ i < (c.drop 1).length, (c.drop 1).getD i 0 ∈
      kBad3 F κ (I.qf c1) vf (none, m.2.take 64) ((c.drop 1).take i)] ≤
      ((60 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
    rw [show (4 + 1 : ℕ) = 1 + 4 from rfl, prEvent_draws_drop 1 4 (fun y => ∃ i < y.length, y.getD i 0 ∈
      kBad3 F κ (I.qf c1) vf (none, m.2.take 64) (y.take i))]
    have h := FlockSound.Uni.prob_hit_le 3 (kBad3 F κ (I.qf c1) vf (none, m.2.take 64)) (fun _ => 15) fun pre =>
      (KF.card_kBad3 F κ _ _ _ pre).trans (by rw [hvf]; exact dBound3K_le_15 _ _ (by omega))
    have h60 : (∑ _i ∈ range (3 + 1), (15 : ℕ)) = 60 := by simp
    rw [h60] at h
    exact h
  calc _ ≤ _ := prEvent_mono _ _ _ hincl
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := add_le_add hA hH

include hzb in
/-- **The values' round, `ρ, λ, f_4, f_5`**: the ring map's last two bad sets, then the two combinations. -/
theorem uniSoundK4_vals (s : USt) (p : Op Stk) (hp : p.length = 29 + κ) (m : Option Stk × List E) :
    Pr{let c ← Compose.draws E (3 + 1)}[¬ uniPreK4 hT I BR s p m ∧ uniPostK4 hT I BR s p m c] ≤
      ((I.nRel - 1 + (3 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) +
        ((30 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  have hpre : uniPreK4 hT I BR s p m = c2St hT I s p := by
    rw [uniPreK4_ne hT I BR s p m (by omega) (by omega)]
    unfold uniSK4
    rw [ite_eq_left hp]
  have hq30 : ∀ c : List E, 30 + κ ≤ (p ++ [(m, c)]).length := fun c => by simp; omega
  have hpost : ∀ c : List E, uniPostK4 hT I BR s p m c ↔
      uniSK3 (KF.kFlockSoundRec3 F hT κ) I BR s (opT κ (p ++ [(m, c)])) := fun c => by
    unfold uniPostK4
    rw [uniSK4_ne hT I BR s _ (by simp; omega)]
  have eA : ∀ c : List E, rd (p ++ [(m, c)]) 0 = rd p 0 := fun c => rd_append_lt _ _ 0 (by omega)
  have eC : ∀ c : List E, rd (p ++ [(m, c)]) (28 + κ) = rd p (28 + κ) := fun c =>
    rd_append_lt _ _ _ (by omega)
  have eV : ∀ c : List E, rd (p ++ [(m, c)]) (29 + κ) = (m, c) := fun c => by rw [← hp, rd_append_self]
  have ev : ∀ c : List E, vFrontO κ (p ++ [(m, c)]) = vFrontO κ p := fun c => vFrontO_append p _ (by omega)
  have hvf : (vFrontO κ p).length = 28 + κ := length_vFrontO p (by omega)
  -- The post-state, read.
  have hpost' : ∀ c : List E, uniPostK4 hT I BR s p m c ↔ ∃ c1, (rd p 0).1.1 = some c1 ∧
      ∃ c2, (rd p (28 + κ)).1.1 = some c2 ∧
      FlockDoneK3 (KF.kFlockSoundRec3 F hT κ)
        (vFrontO κ p ++ [((none, (rd p (28 + κ)).1.2.take 64), (rd p (28 + κ)).2.drop 1 ++ c.drop 2)]) ∧
      (KF.kFlockSoundRec3 F hT κ).prog.ZerosVanish
        (vFrontO κ p ++ [((none, (rd p (28 + κ)).1.2.take 64), (rd p (28 + κ)).2.drop 1 ++ c.drop 2)]) [] ∧
      ((I.zb (vFrontO κ p ++ [((none, (rd p (28 + κ)).1.2.take 64), (rd p (28 + κ)).2.drop 1 ++ c.drop 2)])).eval
          (((rd p (28 + κ)).2.take 1).headD 0) = 0 ∨
        BR.St (I.prod s c1 ((rd p 0).2.take 3)
            (vFrontO κ p ++ [((none, (rd p (28 + κ)).1.2.take 64), (rd p (28 + κ)).2.drop 1 ++ c.drop 2)]) c2
            (((rd p (28 + κ)).2.take 1).headD 0) m.2 ((c.take 2).headD 0) ((c.take 2).getD 1 0))
          (I.target s c1 ((rd p 0).2.take 3)
            (vFrontO κ p ++ [((none, (rd p (28 + κ)).1.2.take 64), (rd p (28 + κ)).2.drop 1 ++ c.drop 2)]) c2
            (((rd p (28 + κ)).2.take 1).headD 0) m.2 ((c.take 2).headD 0) ((c.take 2).getD 1 0)) []) := by
    intro c
    rw [hpost c, uniSK3_ge hT I BR s _ (by rw [length_opT_ge _ (hq30 c)]; simp; omega), rd_opT_zero,
      rd_opT_c2 _ (hq30 c), rd_opT_v _ (hq30 c), fdOf_opT_ge _ (hq30 c), brOf_opT _ (hq30 c),
      brOf_of_length _ _ (by simp; omega)]
    simp only [r0Op, lastOp, eA, eC, eV, ev]
  rcases h0 : (rd p 0).1.1 with _ | c1
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hq⟩ => ?_
    obtain ⟨c1, h1, -⟩ := (hpost' c).mp hq
    rw [h0] at h1
    cases h1
  rcases h2 : (rd p (28 + κ)).1.1 with _ | c2
  · refine prEvent_le_of_forall_not _ _ _ fun c ⟨_, hq⟩ => ?_
    obtain ⟨c1, -, c2, h2', -⟩ := (hpost' c).mp hq
    rw [h2] at h2'
    cases h2'
  have ht : ((rd p (28 + κ)).2.take 1).headD 0 = (rd p (28 + κ)).2.headD 0 := by
    cases (rd p (28 + κ)).2 <;> rfl
  rw [hpre]
  simp only [ht] at hpost'
  unfold c2St
  rw [h0, h2]
  generalize hvfd : vFrontO κ p = vf at hpost' hvf ⊢
  generalize hsld : (rd p (28 + κ)).1.2.take 64 = sl at hpost' ⊢
  generalize hfsd : (rd p (28 + κ)).2.drop 1 = fs at hpost' ⊢
  generalize hchd : (rd p 0).2.take 3 = ch at hpost' ⊢
  generalize htd : (rd p (28 + κ)).2.headD 0 = t at hpost' ⊢
  have hincl : ∀ c : List E, ¬ (∃ c1', some c1 = some c1' ∧ ∃ c2', some c2 = some c2' ∧
      DoneFits (KF.kRoundsPre κ KF.r0Rec3) vf ∧ sl.length = 64 ∧ KF.kTerm κ (KF.sampRec3 κ) vf sl = 0 ∧
      ((I.zb (vf ++ [((none, sl), fs)])).eval t = 0 ∨
        (stateOfK F (kBad3 F κ) (I.qf c1') (vf ++ [((none, sl), fs)]) ∧
          ∃ vals g, ∀ d ∈ I.diffs s c1' ch (vf ++ [((none, sl), fs ++ g)]) c2' t vals, ∀ x ∈ d, x = 0))) ∧
      uniPostK4 hT I BR s p m c →
      (∃ i < (c.drop 2).length, (c.drop 2).getD i 0 ∈
          kBad3 F κ (I.qf c1) vf (none, sl) (fs ++ (c.drop 2).take i)) ∨
        ((∃ d ∈ I.diffs s c1 ch (vf ++ [((none, sl), fs ++ c.drop 2)]) c2 t m.2, ∃ x ∈ d, x ≠ 0) ∧
          powComb ((I.diffs s c1 ch (vf ++ [((none, sl), fs ++ c.drop 2)]) c2 t m.2).map
            fun d => powComb d ((c.take 2).headD 0)) ((c.take 2).getD 1 0) = 0) := by
    intro c ⟨hn, hq⟩
    obtain ⟨c1', h1, c2', h2', hFD, hZV, hrest⟩ := (hpost' c).mp hq
    rw [h0] at h1
    cases h1
    rw [h2] at h2'
    cases h2'
    -- Flock's front done, the slices' length, the terminal: from the completed transcript.
    have hFD' : DoneFits (KF.kRounds κ KF.r0Rec3) (vf ++ [((none, sl), fs ++ c.drop 2)]) := hFD
    have hFront : DoneFits (KF.kRoundsPre κ KF.r0Rec3) vf := by
      have h := doneFits_append_take _ _ _ hFD'
      rwa [KF.length_kRoundsPre, ← hvf, List.take_left' rfl] at h
    have hSL : sl.length = 64 := (doneFits_last _ _ _ _ hFD').1.2
    have hFZ : KF.kTerm κ (KF.sampRec3 κ) vf sl = 0 := by
      have hz := hZV.1 (28 + κ) (by simp; omega)
      have htk : (vf ++ [((none, sl), fs ++ c.drop 2)]).take (28 + κ) = vf := List.take_left' hvf
      rw [htk, show (KF.kFlockSoundRec3 F hT κ).prog = KF.kProgWith κ KF.r0Rec3 (KF.sampRec3 κ) from rfl,
        KF.kProgWith_zeros _ _ _ _ hvf] at hz
      have hz' := hz _ (List.mem_singleton_self _)
      rw [List.getElem_append_right (by omega)] at hz'
      simpa [hvf] using hz'
    -- Not the merge polynomial: else the state before held.
    rcases hrest with hz | hSt
    · exfalso
      refine hn ⟨c1, rfl, c2, rfl, hFront, hSL, hFZ, Or.inl ?_⟩
      rw [hzb vf _ _ hvf]
      exact hz
    -- The batch's start: the combination vanishes.
    rw [BR.St_nil] at hSt
    have hb := I.batch_start s c1 ch _ c2 t m.2 ((c.take 2).headD 0) ((c.take 2).getD 1 0) hZV
    have hcomb : powComb ((I.diffs s c1 ch (vf ++ [((none, sl), fs ++ c.drop 2)]) c2 t m.2).map
        fun d => powComb d ((c.take 2).headD 0)) ((c.take 2).getD 1 0) = 0 := by
      rw [← hb, ← hSt]
      exact CharTwo.add_self_eq_zero _
    by_cases hnz : ∃ d ∈ I.diffs s c1 ch (vf ++ [((none, sl), fs ++ c.drop 2)]) c2 t m.2, ∃ x ∈ d, x ≠ 0
    · exact Or.inr ⟨hnz, hcomb⟩
    · left
      push Not at hnz
      have hEnd := I.diffs_flock _ _ _ _ _ _ _ hnz
      have hS := (KF.kFlockSoundRec3 F hT κ).finish _ _ hFD hZV hEnd
      have hS0 : ¬ stateOfK F (kBad3 F κ) (I.qf c1) (vf ++ [((none, sl), fs)]) := fun hS0 =>
        hn ⟨c1, rfl, c2, rfl, hFront, hSL, hFZ, Or.inr ⟨hS0, m.2, c.drop 2, hnz⟩⟩
      exact state_extend (kBad3 F κ) (I.qf c1) hS0 hS
  have hH : Pr{let c ← Compose.draws E (3 + 1)}[∃ i < (c.drop 2).length, (c.drop 2).getD i 0 ∈
      kBad3 F κ (I.qf c1) vf (none, sl) (fs ++ (c.drop 2).take i)] ≤
      ((30 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
    rw [show (3 + 1 : ℕ) = 2 + 2 from rfl, prEvent_draws_drop 2 2 (fun y => ∃ i < y.length, y.getD i 0 ∈
      kBad3 F κ (I.qf c1) vf (none, sl) (fs ++ y.take i))]
    have h := FlockSound.Uni.prob_hit_le 1 (fun pre => kBad3 F κ (I.qf c1) vf (none, sl) (fs ++ pre))
      (fun _ => 15) fun pre =>
        (KF.card_kBad3 F κ _ _ _ _).trans (by rw [hvf]; exact dBound3K_le_15 _ _ (by omega))
    have h30 : (∑ _i ∈ range (1 + 1), (15 : ℕ)) = 30 := by simp
    rw [h30] at h
    exact h
  have hB : Pr{let c ← Compose.draws E (3 + 1)}[
      (∃ d ∈ I.diffs s c1 ch (vf ++ [((none, sl), fs ++ c.drop 2)]) c2 t m.2, ∃ x ∈ d, x ≠ 0) ∧
        powComb ((I.diffs s c1 ch (vf ++ [((none, sl), fs ++ c.drop 2)]) c2 t m.2).map
          fun d => powComb d ((c.take 2).headD 0)) ((c.take 2).getD 1 0) = 0] ≤
      ((I.nRel - 1 + (3 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
    rw [show (3 + 1 : ℕ) = 2 + 2 from rfl]
    refine prEvent_draws_fubini 2 2 (fun x y =>
      (∃ d ∈ I.diffs s c1 ch (vf ++ [((none, sl), fs ++ y)]) c2 t m.2, ∃ z ∈ d, z ≠ 0) ∧
        powComb ((I.diffs s c1 ch (vf ++ [((none, sl), fs ++ y)]) c2 t m.2).map
          fun d => powComb d (x.headD 0)) (x.getD 1 0) = 0) _ fun y => ?_
    by_cases hnz : ∃ d ∈ I.diffs s c1 ch (vf ++ [((none, sl), fs ++ y)]) c2 t m.2, ∃ z ∈ d, z ≠ 0
    · refine (prEvent_mono _ _ _ fun x hx => hx.2).trans ?_
      exact prEvent_twoLevel_le _ I.nRel 3 (I.diffs_len _ _ _ _ _ _ _) (I.diffs_count _ _ _ _ _ _ _) hnz
    · exact prEvent_le_of_forall_not _ _ _ fun x hx => hnz hx.1
  calc _ ≤ _ := prEvent_mono _ _ _ hincl
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ _ := add_le_add hH hB
    _ = _ := add_comm _ _

theorem uniPreK4_pre_post (s : USt) (p : Op Stk) (m : Option Stk × List E) (c : List E)
    (m' : Option Stk × List E) (h : uniPreK4 hT I BR s (p ++ [(m, c)]) m') : uniPostK4 hT I BR s p m c := by
  unfold uniPostK4
  by_cases hq : (p ++ [(m, c)]).length = 28 + κ
  · unfold uniPreK4 at h
    rw [ite_eq_right (by simp), ite_eq_left hq] at h
    obtain ⟨c1, c2, h1, -, hP, hS, hFD, -, -⟩ := h
    rw [uniSK4_ne hT I BR s _ (by omega),
      uniSK3_le hT I BR s _ (by rw [length_opT_le _ (by simp) (by omega)]; omega)]
    refine ⟨c1, by rw [rd_opT_zero]; exact h1, by rw [rd_opT_zero]; exact I.main_of_polys _ _ _ _ _ hP, ?_, ?_⟩
    · rw [length_opT_le _ (by simp) (by omega), fdOf_opT_le _ (by simp) (by omega), hq,
        show 28 + κ + 1 - 1 = 28 + κ by omega]
      have ht : (KF.kFlockSoundRec3 F hT κ).prog.rounds.take (28 + κ) = KF.kRoundsPre κ KF.r0Rec3 :=
        List.take_left' (KF.length_kRoundsPre κ _)
      rw [ht]
      exact hFD
    · rw [fdOf_opT_le _ (by simp) (by omega)]
      exact hS
  · unfold uniPreK4 at h
    rw [ite_eq_right (by simp), ite_eq_right hq] at h
    exact h

/-! ## The rounds -/

theorem rec4_eq (nV : ℕ) : rec4Rounds κ nV np = ⟨true, 1, 3⟩ :: (kRoundsMid κ ++
    (⟨true, 65, 4⟩ :: ⟨false, nV, 3⟩ :: (List.replicate np ⟨false, 8, 0⟩ ++ [⟨false, 2, 0⟩]))) := by
  simp [rec4Rounds]

theorem rec4_getD_mid (nV j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 27 + κ) :
    (rec4Rounds κ nV np).getD j ⟨false, 0, 0⟩ = (KF.kRounds κ KF.r0Rec3)[j]'(by rw [KF.length_kRounds]; omega) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < (kRoundsMid κ).length := by rw [length_kRoundsMid]; omega
  rw [rec4_eq, List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_append_left hi]
  simp only [KF.kRounds, kRoundsPre_eq, List.cons_append, List.getElem_cons_succ,
    List.getElem_append_left hi, List.getElem?_eq_getElem hi, Option.getD_some]

theorem rec4_getD_c2 (nV : ℕ) : (rec4Rounds κ nV np).getD (28 + κ) ⟨false, 0, 0⟩ = ⟨true, 65, 4⟩ := by
  rw [rec4_eq, show 28 + κ = (27 + κ) + 1 by omega, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [length_kRoundsMid]), length_kRoundsMid, Nat.sub_self]
  rfl

theorem rec4_getD_v (nV : ℕ) : (rec4Rounds κ nV np).getD (29 + κ) ⟨false, 0, 0⟩ = ⟨false, nV, 3⟩ := by
  rw [rec4_eq, show 29 + κ = (28 + κ) + 1 by omega, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [length_kRoundsMid]; omega), length_kRoundsMid,
    show 28 + κ - (27 + κ) = 1 by omega]
  rfl

theorem rec4_getD_batch (nV j : ℕ) (h1 : 30 + κ ≤ j) (h2 : j ≤ 30 + κ + np) :
    ((rec4Rounds κ nV np).getD j ⟨false, 0, 0⟩).ns = 0 := by
  rw [rec4_eq, List.getD_eq_getElem?_getD]
  obtain ⟨i, rfl⟩ : ∃ i, j = (30 + κ + i) := ⟨j - (30 + κ), by omega⟩
  rw [show 30 + κ + i = (29 + κ + i) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [length_kRoundsMid]; omega), length_kRoundsMid,
    show 29 + κ + i - (27 + κ) = i + 2 by omega, List.getElem?_cons_succ, List.getElem?_cons_succ]
  by_cases hi : i < np
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate]
    simp [hi]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate]
    rw [show i - np = 0 by omega]
    rfl

/-! ## The protocol -/

/-- **π1-rec4's PIOP, round by round**, for Flock on the Keccak-f block, the identity model `I` (its merge polynomial
and identities read off Flock's front: `hzb`, `hpolys`) and the batch `BR`. -/
noncomputable def uniPiopK4 : RbrPiop (rec4Rounds κ I.nV np) USt Stk where
  pre := uniPreK4 hT I BR
  post := uniPostK4 hT I BR
  pre_post := uniPreK4_pre_post hT I BR
  err := uniErrK4 hT I BR
  sound j s p m hj hp := by
    rw [length_rec4Rounds] at hj
    unfold uniErrK4
    by_cases h0 : j = 0
    · subst h0
      rw [ite_eq_left rfl]
      obtain rfl : p = [] := List.length_eq_zero_iff.mp hp
      exact uniSoundK4_zero hT I BR s m
    rw [ite_eq_right h0]
    by_cases h1 : j ≤ 27 + κ
    · rw [ite_eq_left h1, rec4_getD_mid I.nV j (by omega) h1]
      exact uniSoundK4_mid hT I BR j (by omega) h1 s p hp m
    rw [ite_eq_right h1]
    by_cases h2 : j = 28 + κ
    · subst h2
      rw [ite_eq_left rfl, rec4_getD_c2]
      exact uniSoundK4_c2 hT I BR hzb hpolys s p hp m
    rw [ite_eq_right h2]
    by_cases h3 : j = 29 + κ
    · subst h3
      rw [ite_eq_left rfl, rec4_getD_v]
      exact uniSoundK4_vals hT I BR hzb s p hp m
    rw [ite_eq_right h3, rec4_getD_batch I.nV j (by omega) (by omega)]
    exact uniSoundK4_batch hT I BR j (by omega) (by omega) s p hp m

/-- **The first state is the Keccak VM's relation.** -/
theorem hpre_uniPiopK4 (s : USt) (c : Stk) (m : List E)
    (h : (uniPiopK4 hT I BR hzb hpolys).pre s [] (some c, m)) : RelK F D s c := by
  change uniPreK4 hT I BR s [] (some c, m) at h
  unfold uniPreK4 at h
  rw [ite_eq_left (List.length_nil : ([] : Op Stk).length = 0)] at h
  obtain ⟨c', hc', hr⟩ := h
  cases hc'
  exact hr

/-- **Every round's error is at most `e`.** -/
theorem uniErrK4_le (e : ℝ≥0∞) (hMain : I.errMain + (KF.kFlockSoundRec3 F hT κ).err 0 ≤ e)
    (hFl : ∀ j, (KF.kFlockSoundRec3 F hT κ).err j ≤ e)
    (hdeg : ((I.degSum + I.degBad : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) +
      ((60 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤ e)
    (hrel : ((I.nRel - 1 + (3 - 1) : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) +
      ((30 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤ e)
    (hP : BR.errPair ≤ e) (hL : BR.errLast ≤ e) (j : ℕ) : uniErrK4 hT I BR j ≤ e := by
  unfold uniErrK4
  split_ifs
  · exact hMain
  · exact hFl _
  · exact hdeg
  · exact hrel
  · exact hP
  · exact hL

end Sound

end States

end UniKeccakSound.Rec4

/-- info: 'UniKeccakSound.Rec4.uniPiopK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Rec4.uniPiopK4
