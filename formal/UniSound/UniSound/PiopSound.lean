-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniSound.Piop

/-!
# The univariate PIOP is round-by-round sound

**`uniPiop Fl I`**: the states `uniPre`, `uniPost` and the errors `uniErr` of `Piop.lean` form a
`RbrPiop` on the main line's rounds (`uniRounds`), for the Flock phase `Fl` and any identity model
`I`: each round's soundness from its lemma (`mainSound`; Flock's `step`; Schwartz–Zippel,
`prEvent_root_le`, for the identities and the merge polynomial `zb`; the two combinations, `prEvent_twoLevel_le`; the sumcheck's rounds,
`SumOracle.step_sound`), and `pre_post` from `main_of_polys` and Flock's `finish` at the boundary
of `C2`'s round.
-/

namespace UniSound

open LeanVM.Parameters UniStatement Finset
open scoped ENNReal

variable {D : Deployment} {κ : ℕ}

theorem prEvent_le_of_forall_not {α : Type} (mx : ProbComp α) (P : α → Prop) (ε : ℝ≥0∞)
    (h : ∀ x, ¬ P x) : Pr{let x ← mx}[P x] ≤ ε :=
  (le_of_eq (prEvent_eq_zero_of_forall_not mx P h)).trans zero_le

theorem DoneFits.length_eq : ∀ {rs : List Compose.RoundSpec} {d : Done}, DoneFits rs d →
    d.length = rs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [h.2.2.length_eq]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem doneFits_append_single : ∀ (rs : List Compose.RoundSpec) (d : Done) (s : Compose.RoundSpec)
    (x : UMsg × List E), d.length = rs.length →
      (DoneFits (rs ++ [s]) (d ++ [x]) ↔ DoneFits rs d ∧ x.1.Fits s ∧ x.2.length = s.ns + 1)
  | [], [], s, x, _ => by simp [DoneFits]
  | r :: rs, y :: d, s, x, h => by
    simp only [List.cons_append, DoneFits]
    rw [doneFits_append_single rs d s x (by simpa using h)]
    tauto
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem doneFits_take_succ (rs : List Compose.RoundSpec) (j : ℕ) (h : j < rs.length)
    (done : Done) (x : UMsg × List E) (hd : DoneFits (rs.take (j + 1)) (done ++ [x])) :
    DoneFits (rs.take j) done ∧ x.1.Fits (rs[j]'h) := by
  have ht : rs.take (j + 1) = rs.take j ++ [rs[j]'h] := List.take_succ_eq_append_getElem h
  rw [ht] at hd
  have hl := hd.length_eq
  simp only [List.length_append, List.length_singleton, List.length_take] at hl
  have hl' : done.length = (rs.take j).length := by simp; omega
  obtain ⟨h1, h2, -⟩ := (doneFits_append_single _ done _ x hl').mp hd
  exact ⟨h1, h2⟩

/-! ## Each round -/

/-! ## The protocol -/

end UniSound
