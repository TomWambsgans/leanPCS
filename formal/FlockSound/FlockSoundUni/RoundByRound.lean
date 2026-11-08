-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The interface (`UniSound.FlockSound`,
-- `Done`, `UMsg`, `ChainProg`) and the counting lemma `prEvent_draws_le_of_card` are `formal/UniSound`'s.
import UniSound.Prob
import FlockSound.Main

/-!
# Round by round, from bad challenges

`FlockSound`'s theorems are deterministic: a run whose checks pass and whose claims are true has
a satisfied relation or a challenge in its bad set, each bad set a function of the run before its
challenge, of a bounded size. The interface (`UniSound.FlockSound`) asks for Flock's soundness
**round by round** on the transcript `Done`. This module turns the first into the second, for any
chain program:

* a **bad family** `B qf done msg pre`: the bad set of the challenge that follows the completed
  rounds `done`, the round's message `msg` and its challenges `pre` so far, for the column `qf`;
* **the state** `stateOf B qf done`: `FlockHolds κ qf`, or some challenge of `done` is in its bad
  set (`HitIn`);
* `stateOf_nil`: at the start, only the relation (the interface's `S_nil`);
* **`step_le`**: a round of `ns + 1` challenges turns the state from false to true with
  probability at most `Σ_{i ≤ ns} d j i / |E|`, `d j i` the size bound of round `j`'s challenge
  `i` (the interface's `step`), by counting: `card_hit_le`;
* `finish_of_catches`: the interface's `finish` is the deterministic theorem on the transcript
  (`Catches`).

`ofFamily` assembles a `FlockSound κ` from a chain program, its link, and a bad family that
catches: what is left of the instance is the code-level link and the reading of Flock's
deterministic theorem (`FlockSound.flockHolds_v1`, `flockHolds_merged`) on `Done`.
-/

namespace FlockSound.Uni

open UniSound LeanVM.Parameters LeanVM.Semantics UniStatement Finset
open scoped ENNReal

variable {κ : ℕ}

/-- **A bad family**: the bad set of the next challenge, for the column `qf`, given the completed
rounds, this round's message and its challenges so far. -/
abbrev BadFamily (κ : ℕ) : Type := LeanVM.Protocol.Column (8 + κ) → Done → UMsg → List E → Finset E

/-- Some challenge of a round's list is in its bad set. -/
def HitRound (B : BadFamily κ) (qf : LeanVM.Protocol.Column (8 + κ)) (done : Done) (msg : UMsg)
    (c : List E) : Prop :=
  ∃ i < c.length, c.getD i 0 ∈ B qf done msg (c.take i)

/-- **Some challenge of the transcript is in its bad set.** -/
def HitIn (B : BadFamily κ) (qf : LeanVM.Protocol.Column (8 + κ)) : Done → Prop
  | [] => False
  | done => ∃ j, ∃ hj : j < done.length, HitRound B qf (done.take j) (done[j]'hj).1 (done[j]'hj).2

theorem hitIn_append (B : BadFamily κ) (qf : LeanVM.Protocol.Column (8 + κ)) (done : Done)
    (msg : UMsg) (c : List E) :
    HitIn B qf (done ++ [(msg, c)]) → HitIn B qf done ∨ HitRound B qf done msg c := by
  intro h
  have h' : ∃ j, ∃ hj : j < (done ++ [(msg, c)]).length,
      HitRound B qf ((done ++ [(msg, c)]).take j) ((done ++ [(msg, c)])[j]'hj).1
        ((done ++ [(msg, c)])[j]'hj).2 := by
    unfold HitIn at h
    split at h
    · simp at *
    · exact h
  obtain ⟨j, hj, hr⟩ := h'
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < done.length
  · left
    have hd : done ≠ [] := List.ne_nil_of_length_pos (by omega)
    unfold HitIn
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

/-! ## Counting the bad challenges of a round -/

open Classical in
/-- **`n + 1` challenges, one bad set each** (a function of the challenges before it, of size at
most `d i`): at most `Σ_{i ≤ n} d i · |E|^n` of the `|E|^(n+1)` tuples hit one. -/
theorem card_hit_le : ∀ (n : ℕ) (B' : List E → Finset E) (d : ℕ → ℕ),
    (∀ pre, (B' pre).card ≤ d pre.length) →
    (univ.filter fun v : Fin (n + 1) → E ↦
      ∃ i < (List.ofFn v).length, (List.ofFn v).getD i 0 ∈ B' ((List.ofFn v).take i)).card ≤
      (∑ i ∈ range (n + 1), d i) * Fintype.card E ^ n
  | 0, B', d, hB => by
    simp only [zero_add, range_one, sum_singleton, pow_zero, mul_one]
    refine (card_le_card_of_injOn (fun v ↦ v 0) (fun v hv ↦ ?_) (fun v _ w _ h ↦ ?_)).trans
      ((hB []).trans (le_refl _))
    · simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hv
      obtain ⟨i, hi, hv⟩ := hv
      simp only [List.length_ofFn] at hi
      have : i = 0 := by omega
      subst this
      simpa [List.ofFn_succ] using hv
    · funext k
      have : k = 0 := Fin.ext (by have := k.isLt; omega)
      subst this
      exact h
  | n + 1, B', d, hB => by
    -- Split off the first challenge: hit there, or hit later in the tail's family.
    have hsplit : (univ.filter fun v : Fin (n + 2) → E ↦
        ∃ i < (List.ofFn v).length, (List.ofFn v).getD i 0 ∈ B' ((List.ofFn v).take i)) ⊆
        (univ.filter fun v : Fin (n + 2) → E ↦ v 0 ∈ B' []) ∪
          (univ.filter fun v : Fin (n + 2) → E ↦
            ∃ i < (List.ofFn (Fin.tail v)).length, (List.ofFn (Fin.tail v)).getD i 0 ∈
              B' (v 0 :: (List.ofFn (Fin.tail v)).take i)) := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and, mem_union] at hv ⊢
      obtain ⟨i, hi, hv⟩ := hv
      rw [List.ofFn_succ] at hv hi
      rcases i with _ | i
      · left
        simpa using hv
      · right
        refine ⟨i, by simpa using hi, ?_⟩
        simpa [Fin.tail] using hv
    refine (card_le_card hsplit).trans ((card_union_le _ _).trans ?_)
    -- The first: `|B' []| · |E|^(n+1)`.
    have h1 : (univ.filter fun v : Fin (n + 2) → E ↦ v 0 ∈ B' []).card ≤
        d 0 * Fintype.card E ^ (n + 1) := by
      have : (univ.filter fun v : Fin (n + 2) → E ↦ v 0 ∈ B' []) =
          (univ.filter fun v : Fin (n + 2) → E ↦ (Fin.consEquiv (fun _ ↦ E)).symm v ∈
            (B' []) ×ˢ (univ : Finset (Fin (n + 1) → E))) := by
        ext v
        simp [Fin.consEquiv]
      rw [this]
      refine (card_le_card_of_injOn (t := (B' []) ×ˢ (univ : Finset (Fin (n + 1) → E)))
        (Fin.consEquiv (fun _ ↦ E)).symm (fun v hv ↦ ?_)
        (fun v _ w _ h ↦ (Fin.consEquiv (fun _ ↦ E)).symm.injective h)).trans ?_
      · simp only [coe_filter, mem_univ, true_and] at hv
        exact hv
      · rw [card_product, card_univ, Fintype.card_fun, Fintype.card_fin]
        exact Nat.mul_le_mul_right _ (hB [])
    -- The second: for each first challenge, the tail's count.
    have h2 : (univ.filter fun v : Fin (n + 2) → E ↦
        ∃ i < (List.ofFn (Fin.tail v)).length, (List.ofFn (Fin.tail v)).getD i 0 ∈
          B' (v 0 :: (List.ofFn (Fin.tail v)).take i)).card ≤
        (∑ i ∈ range (n + 1), d (i + 1)) * Fintype.card E ^ (n + 1) := by
      have hcount : ∀ a : E, (univ.filter fun w : Fin (n + 1) → E ↦
          ∃ i < (List.ofFn w).length, (List.ofFn w).getD i 0 ∈ B' (a :: (List.ofFn w).take i)).card ≤
          (∑ i ∈ range (n + 1), d (i + 1)) * Fintype.card E ^ n :=
        fun a ↦ card_hit_le n (fun pre ↦ B' (a :: pre)) (fun i ↦ d (i + 1))
          fun pre ↦ by simpa using hB (a :: pre)
      calc _ = ∑ a : E, (univ.filter fun w : Fin (n + 1) → E ↦
            ∃ i < (List.ofFn w).length, (List.ofFn w).getD i 0 ∈
              B' (a :: (List.ofFn w).take i)).card := by
            rw [card_filter, ← Fintype.sum_equiv (Fin.consEquiv (fun _ ↦ E))
              (fun p ↦ if (∃ i < (List.ofFn p.2).length, (List.ofFn p.2).getD i 0 ∈
                B' (p.1 :: (List.ofFn p.2).take i)) then 1 else 0) _ (fun p ↦ by
                  simp [Fin.consEquiv, Fin.tail_cons, Fin.cons_zero])]
            rw [Fintype.sum_prod_type]
            exact Finset.sum_congr rfl fun a _ ↦ (card_filter _ _).symm
        _ ≤ ∑ _a : E, (∑ i ∈ range (n + 1), d (i + 1)) * Fintype.card E ^ n :=
            Finset.sum_le_sum fun a _ ↦ hcount a
        _ = (∑ i ∈ range (n + 1), d (i + 1)) * Fintype.card E ^ (n + 1) := by
            rw [sum_const, card_univ, smul_eq_mul, pow_succ]
            ring
    calc _ ≤ d 0 * Fintype.card E ^ (n + 1) +
          (∑ i ∈ range (n + 1), d (i + 1)) * Fintype.card E ^ (n + 1) := add_le_add h1 h2
      _ = (∑ i ∈ range (n + 2), d i) * Fintype.card E ^ (n + 1) := by
        rw [sum_range_succ' (fun i ↦ d i) (n + 1)]
        ring

open Classical in
/-- **A round's error**: `ns + 1` challenges, each bad with its own family, hit one with
probability at most `Σ_{i ≤ ns} d i / |E|`. -/
theorem prob_hit_le (ns : ℕ) (B' : List E → Finset E) (d : ℕ → ℕ)
    (hB : ∀ pre, (B' pre).card ≤ d pre.length) :
    Pr{let c ← Compose.draws E (ns + 1)}[∃ i < c.length, c.getD i 0 ∈ B' (c.take i)] ≤
      ((∑ i ∈ range (ns + 1), d i : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  prEvent_draws_le_of_card ns _ _ (card_hit_le ns B' d hB)

theorem doneFits_length : ∀ {rs : List Compose.RoundSpec} {done : Done}, DoneFits rs done →
    done.length = rs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [doneFits_length h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

end FlockSound.Uni
