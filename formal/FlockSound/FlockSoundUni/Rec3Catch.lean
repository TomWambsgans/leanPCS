-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The catch follows `Catch.lean`'s `catches_of_tx` (the
-- main line's), with `FlockSound.FlockSq`'s `flock_front_sq`.
import FlockSoundUni.Instance
import FlockSoundUni.Rec3Link
import FlockSound.FlockSq
import UniSound.Rec3.BusSq

/-!
# π1-rec3's Flock bad family catches

π1-rec3's Flock transcript `done` (rounds `flockRounds3 κ`) is read as the main line's (`expandFd κ done`: the first
round's one challenge `c` written out as `squares c (4 + κ)`), whose parse (`parse κ`) is `FlockSound`'s run with
`τs = sqPt (4 + κ) c` (`parse_expandFd_τs`).

**The bad family** (`flockBad3 κ`): round `0`'s one challenge is bad when the residual's sampled tables vanish at its
squares (`kronBad (4 + κ)`, at most `2^(4 + κ) − 1` values: Kronecker); every later challenge is bad as the main
line's (`flockBad κ`) on the expanded transcript. Sizes `dBound3`: `2^(4 + κ) − 1` for `c`, the main line's after.

**`catches3`**: on a completed transcript whose ring claim holds of the column and whose pending claim (the main
line's reading's, which π1-rec3's walk checks) is its sum, the column satisfies Flock's relation or a challenge is
bad: `flock_front_sq` at leanVM's constants on the expanded parse, each event of `Front.BadSq` a hit of `flockBad3`
(`hit_of_badSq`).
-/

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics Finset Polynomial
open LeanVM.Protocol (Column)

variable {κ : ℕ}

/-! ## The expanded transcript -/

theorem length_expandFd (κ : ℕ) (d : Done) : (expandFd κ d).length = d.length := by
  cases d <;> rfl

theorem expandFd_take (κ : ℕ) (d : Done) (j : ℕ) (hj : 1 ≤ j) : expandFd κ (d.take j) = (expandFd κ d).take j := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  cases d <;> rfl

theorem doneFits_expandFd {d : Done} (h : DoneFits (flockRounds3 κ) d) : DoneFits (flockRounds κ) (expandFd κ d) := by
  rcases d with _ | ⟨⟨msg, c⟩, d⟩
  · exact h.elim
  · obtain ⟨hm, hc, hd⟩ := h
    refine ⟨hm, ?_, ?_⟩
    · show (squares (c.headD 0) (4 + κ)).length = 3 + κ + 1
      rw [length_squares]
      omega
    · exact hd

theorem getD_ofFn_sq (n : ℕ) (c : E) (a : ℕ) (ha : a < n) :
    (List.ofFn (FlockSound.sqPt n c)).getD a 0 = FlockSound.sqPt n c ⟨a, ha⟩ := by
  simp [List.getD_eq_getElem?_getD, ha]

/-- **The expanded parse's sampled coordinates are the squares of the first challenge.** -/
theorem parse_expandFd_τs (d : Done) (hd : d ≠ []) :
    (parse κ (expandFd κ d)).τs = FlockSound.sqPt (4 + κ) ((rd d 0).2.headD 0) := by
  funext a
  show (rd (expandFd κ d) 0).2.getD a 0 = _
  rw [rd_expandFd_zero κ d hd, squares_eq_ofFn, getD_ofFn_sq _ _ _ a.isLt]

/-! ## The bad family -/

/-- **The bad sets' sizes**: `2^(4 + κ) − 1` for the squares' challenge, the main line's after. -/
def dBound3 (κ : ℕ) (j i : ℕ) : ℕ := if j = 0 then 2 ^ (4 + κ) - 1 else dBound κ j i

end FlockSound.Uni

namespace FlockSound.Uni

open UniStatement UniSound LeanVM.Parameters LeanVM.Semantics Finset Polynomial
open LeanVM.Protocol (Column)

variable {κ : ℕ}

/-! ## The catch -/

/-! ## The rounds' errors -/

theorem flockRounds3_ns_le (κ : ℕ) : ∀ s ∈ flockRounds3 κ, s.ns ≤ 5 := by
  intro s hs
  simp only [flockRounds3, flockRounds3Pre, List.mem_append, List.mem_cons, List.mem_replicate,
    List.not_mem_nil, or_false] at hs
  aesop

theorem dBound_le (κ j i : ℕ) : dBound κ j i ≤ 15 := by
  unfold dBound
  split_ifs <;> omega

/-- **Round `j`'s error, times `|E|`**: `2^(4 + κ) − 1` for the squares' challenge, at most `90` after. -/
theorem sum_dBound3_le (κ j : ℕ) :
    ∑ i ∈ range ((((flockRounds3 κ)[j]?).map (·.ns)).getD 0 + 1), dBound3 κ j i ≤ 2 ^ (4 + κ) + 90 := by
  by_cases h0 : j = 0
  · subst h0
    have e : ((((flockRounds3 κ)[0]?).map (·.ns)).getD 0) = 0 := by
      simp [flockRounds3, flockRounds3Pre]
    rw [e]
    simp [dBound3]
    omega
  · have hns : (((flockRounds3 κ)[j]?).map (·.ns)).getD 0 ≤ 5 := by
      cases h : (flockRounds3 κ)[j]? with
      | none => simp
      | some s => exact flockRounds3_ns_le κ s (List.mem_of_getElem? h)
    generalize (((flockRounds3 κ)[j]?).map (·.ns)).getD 0 = n at hns ⊢
    calc ∑ i ∈ range (n + 1), dBound3 κ j i
        ≤ ∑ _i ∈ range (n + 1), 15 :=
          Finset.sum_le_sum fun i _ ↦ by unfold dBound3; rw [ite_eq_right h0]; exact dBound_le κ j i
      _ ≤ 2 ^ (4 + κ) + 90 := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
          exact le_trans (by omega : (n + 1) * 15 ≤ 90) (Nat.le_add_left 90 _)

end FlockSound.Uni
