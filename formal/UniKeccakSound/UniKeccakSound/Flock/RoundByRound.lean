-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The generic state and step are
-- `formal/FlockSound/FlockSoundUni/RoundByRound.lean`'s (BLAKE2s's, over `Column (8 + κ)` and `FlockHolds`), here
-- over the Keccak verifier's column `Column (11 + κ)` and `KFlockHolds F κ`; the counting (`prob_hit_le`) is reused.
import FlockSoundUni.RoundByRound
import UniKeccakSound.FlockInterfaceK

/-!
# Round by round, from bad challenges, on the Keccak-f block

`KFlockSound`'s round-by-round fields from a **bad family** (`KBadFamily κ`: the bad set of the challenge that follows
the completed rounds, the round's message and its challenges so far, for the column `qf`):

* **the state** `stateOfK F B qf done`: `KFlockHolds F κ qf`, or some challenge of `done` is in its bad set
  (`HitInK`); `stateOfK_nil`: at the start, only the relation;
* **`step_leK`**: a round of `ns + 1` challenges turns the state from false to true with probability at most
  `Σ_{i ≤ ns} d j i / |E|` (`FlockSound.Uni.prob_hit_le`);
* `CatchesK`: what `finish` needs: on a completed transcript whose zeros vanish and whose ring claim holds of the
  column, the relation holds or a challenge is bad;
* **`ofFamilyK`**: `KFlockSound F κ v` from a chain program, its link and a bad family that catches.
-/

namespace UniKeccakSound.KF

open UniSound UniKeccak LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol Finset FlockSound.Uni
open scoped ENNReal

variable {κ : ℕ}

/-- **A bad family** on the Keccak verifier's column: the bad set of the next challenge, for the column `qf`, given
the completed rounds, this round's message and its challenges so far. -/
abbrev KBadFamily (κ : ℕ) : Type := Column (KeccakVm.kWords + κ) → Done → UMsg → List E → Finset E

/-- Some challenge of a round's list is in its bad set. -/
def HitRoundK (B : KBadFamily κ) (qf : Column (KeccakVm.kWords + κ)) (done : Done) (msg : UMsg) (c : List E) :
    Prop :=
  ∃ i < c.length, c.getD i 0 ∈ B qf done msg (c.take i)

/-- **Some challenge of the transcript is in its bad set.** -/
def HitInK (B : KBadFamily κ) (qf : Column (KeccakVm.kWords + κ)) : Done → Prop
  | [] => False
  | done => ∃ j, ∃ hj : j < done.length, HitRoundK B qf (done.take j) (done[j]'hj).1 (done[j]'hj).2

theorem hitInK_append (B : KBadFamily κ) (qf : Column (KeccakVm.kWords + κ)) (done : Done) (msg : UMsg)
    (c : List E) :
    HitInK B qf (done ++ [(msg, c)]) → HitInK B qf done ∨ HitRoundK B qf done msg c := by
  intro h
  have h' : ∃ j, ∃ hj : j < (done ++ [(msg, c)]).length,
      HitRoundK B qf ((done ++ [(msg, c)]).take j) ((done ++ [(msg, c)])[j]'hj).1
        ((done ++ [(msg, c)])[j]'hj).2 := by
    unfold HitInK at h
    split at h
    · simp at *
    · exact h
  obtain ⟨j, hj, hr⟩ := h'
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < done.length
  · left
    have hd : done ≠ [] := List.ne_nil_of_length_pos (by omega)
    unfold HitInK
    split
    · exact absurd rfl hd
    · refine ⟨j, hlt, ?_⟩
      rw [List.take_append_of_le_length hlt.le, List.getElem_append_left hlt] at hr
      exact hr
  · right
    have hj' : j = done.length := by omega
    subst hj'
    rw [List.take_left' rfl, List.getElem_append_right (le_refl _)] at hr
    simpa using hr

/-- **The state**: the block's relation holds, or some challenge so far was bad. -/
def stateOfK (F : KeccakVm.KeccakFlockSpec) (B : KBadFamily κ) (qf : Column (KeccakVm.kWords + κ))
    (done : Done) : Prop :=
  KFlockHolds F κ qf ∨ HitInK B qf done

theorem stateOfK_nil (F : KeccakVm.KeccakFlockSpec) (B : KBadFamily κ) (qf : Column (KeccakVm.kWords + κ)) :
    stateOfK F B qf [] → KFlockHolds F κ qf := by
  rintro (h | h)
  · exact h
  · exact h.elim

/-- **The interface's `step`** for the state of a bad family. -/
theorem step_leK (F : KeccakVm.KeccakFlockSpec) (B : KBadFamily κ) (d : ℕ → ℕ → ℕ)
    (hB : ∀ qf done msg pre, (B qf done msg pre).card ≤ d done.length pre.length)
    (qf : Column (KeccakVm.kWords + κ)) (done : Done) (msg : UMsg) (ns : ℕ) :
    Pr{let c ← Compose.draws E (ns + 1)}[¬ stateOfK F B qf done ∧ stateOfK F B qf (done ++ [(msg, c)])] ≤
      ((∑ i ∈ range (ns + 1), d done.length i : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  refine (prEvent_mono _ _ _ fun c ⟨hn, hpost⟩ ↦ ?_).trans
    (prob_hit_le ns (B qf done msg) (d done.length) fun pre ↦ hB qf done msg pre)
  simp only [stateOfK, not_or] at hn
  rcases hpost with h | h
  · exact absurd h hn.1
  · rcases hitInK_append B qf done msg c h with h | h
    · exact absurd h hn.2
    · exact h

/-- **What the interface's `finish` needs of a bad family**: on a completed transcript whose zeros vanish and whose
ring claim holds of the column, the relation holds or a challenge is bad. -/
def CatchesK (F : KeccakVm.KeccakFlockSpec) (P : ChainProg (List E × UniStatement.Flock.End)) (B : KBadFamily κ) : Prop :=
  ∀ (qf : Column (KeccakVm.kWords + κ)) (done : Done), DoneFits P.rounds done → P.ZerosVanish done [] →
    FlockEndHoldsK qf (P.out done []) → KFlockHolds F κ qf ∨ HitInK B qf done

/-- **The interface from a bad family that catches**: the program, its link, the family and its sizes give
`KFlockSound F κ v`, round `j`'s error `Σ_{i ≤ ns_j} d j i / |E|`. -/
noncomputable def ofFamilyK (F : KeccakVm.KeccakFlockSpec) (v : KeccakVariant) (P : ChainProg (List E × UniStatement.Flock.End))
    (hroot : ∀ s ∈ P.rounds, s.root = false) (htail : P.tail = 0)
    (hlink : ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (Pm : KeccakState → m KeccakState),
      verifyWalkedK Pm (UniStatement.keccakR1csLogSize + κ) v = P.run Pm)
    (B : KBadFamily κ) (d : ℕ → ℕ → ℕ)
    (hB : ∀ qf done msg pre, (B qf done msg pre).card ≤ d done.length pre.length)
    (hcatch : CatchesK F P B) : KFlockSound F κ v where
  prog := P
  rounds_root := hroot
  tail_eq := htail
  link := hlink
  S := stateOfK F B
  err j := ((∑ i ∈ range ((((P.rounds[j]?).map (·.ns)).getD 0) + 1), d j i : ℕ) : ℝ≥0∞) /
    (Fintype.card E : ℝ≥0∞)
  S_nil := stateOfK_nil F B
  step j hj qf done msg hfit _ := by
    have hlen : done.length = j := by
      rw [doneFits_length hfit, List.length_take]
      omega
    have h := step_leK F B d hB qf done msg (P.rounds[j]'hj).ns
    rw [hlen] at h
    simpa [List.getElem?_eq_getElem hj] using h
  finish qf done hfit hz hend := hcatch qf done hfit hz hend

/-- **Its rounds' errors**, by the family's sizes. -/
theorem ofFamilyK_err (F : KeccakVm.KeccakFlockSpec) (v : KeccakVariant) (P : ChainProg (List E × UniStatement.Flock.End))
    (hroot : ∀ s ∈ P.rounds, s.root = false) (htail : P.tail = 0)
    (hlink : ∀ {m : Type → Type} [Monad m] [LawfulMonad m] (Pm : KeccakState → m KeccakState),
      verifyWalkedK Pm (UniStatement.keccakR1csLogSize + κ) v = P.run Pm)
    (B : KBadFamily κ) (d : ℕ → ℕ → ℕ)
    (hB : ∀ qf done msg pre, (B qf done msg pre).card ≤ d done.length pre.length)
    (hcatch : CatchesK F P B) (j : ℕ) :
    (ofFamilyK F v P hroot htail hlink B d hB hcatch).err j =
      ((∑ i ∈ range ((((P.rounds[j]?).map (·.ns)).getD 0) + 1), d j i : ℕ) : ℝ≥0∞) /
        (Fintype.card E : ℝ≥0∞) := rfl

end UniKeccakSound.KF

/-- info: 'UniKeccakSound.KF.ofFamilyK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.ofFamilyK
