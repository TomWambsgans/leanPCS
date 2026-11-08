-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `Z_bad`, its degree and its nonvanishing are
-- `formal/UniSound`'s (`zBad`, `natDegree_zBad_le`, `zBad_ne_zero`); the argument is `RecGraph.Hazard`'s.
import RecGraphKeccak.Main
import RecGraphKeccak.Functionals15
import UniSound.Ids.Main
import UniSound.Ids.Build

/-!
# The merge hazard at the Keccak shape, and its probability

* `hazardPolyK_ne_zero`, `hazardPolyK_natDegree`: `Z_bad` at `keccak128` (`UniSound.Ids.zBad`, `y(t)` of 15
  coordinates) is nonzero (`zBad_ne_zero` with `functionalsCorrect15`), of degree at most `2^16`;
* **`hazard_cardK`**: for every `p_0`, at most `2^16` values of `t` are hazardous; **`hazard_probK`**: `t` uniform,
  `p_0` fixed (Flock's point is drawn before `C2`'s root, `t` after it), the hazard has probability at most
  `2^16 / |E| = 2^-176`.
-/

namespace RecGraphKeccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement Polynomial UniSound.Ids RecGraphKeccak.Pi1
open scoped ENNReal

/-! ## The hazard's probability -/

theorem keccak128_sha3_height : keccak128.heights.getD opBlake2s 0 = 15 := by decide

/-- `Z_bad` at the Keccak shape is nonzero. -/
theorem hazardPolyK_ne_zero (p0 : E) : hazardPolyK p0 ≠ 0 :=
  zBad_ne_zero keccak128 betaCantor (by rw [keccak128_sha3_height]; exact functionalsCorrect15)
    (by rw [keccak128_sha3_height]; decide) p0

/-- `Z_bad`'s degree at the Keccak shape: at most `2^16`. -/
theorem hazardPolyK_natDegree (p0 : E) : (hazardPolyK p0).natDegree ≤ 2 ^ 16 := by
  have h := natDegree_zBad_le keccak128 p0
  unfold zBadDeg at h
  rw [UniSound.Ids.Eval.coordinateFunctionals_size, keccak128_sha3_height] at h
  exact h

noncomputable instance (p0 : E) : DecidablePred (HazardK p0) :=
  fun t ↦ inferInstanceAs (Decidable ((hazardPolyK p0).eval t = 0))

/-- **Schwartz–Zippel in `t`**: for every `p_0`, at most `2^16` values of `t` are hazardous. -/
theorem hazard_cardK (p0 : E) : (Finset.univ.filter fun t : E ↦ HazardK p0 t).card ≤ 2 ^ 16 := by
  have hne := hazardPolyK_ne_zero p0
  have hsub : (Finset.univ.filter fun t : E ↦ HazardK p0 t) ⊆ (hazardPolyK p0).roots.toFinset := by
    intro t ht
    have ht' : (hazardPolyK p0).eval t = 0 := (Finset.mem_filter.mp ht).2
    simp only [Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
    exact ht'
  calc (Finset.univ.filter fun t : E ↦ HazardK p0 t).card
      ≤ (hazardPolyK p0).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (hazardPolyK p0).roots := Multiset.toFinset_card_le _
    _ ≤ (hazardPolyK p0).natDegree := card_roots' _
    _ ≤ 2 ^ 16 := hazardPolyK_natDegree p0

/-- **The hazard's probability at the Keccak shape**: `t` uniform in `E`, `p_0` fixed (drawn before `t`), at most
`2^16 / |E|` (`|E| = 2^192`: `2^-176`). -/
theorem hazard_probK (p0 : E) :
    ((Finset.univ.filter fun t : E ↦ HazardK p0 t).card : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) ≤
      (2 ^ 16 : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) := by
  gcongr
  exact_mod_cast hazard_cardK p0

end RecGraphKeccak
