-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. New for the Keccak VM port (the role of
-- `formal/UniComplete/UniComplete/DomainCoord18.lean`'s `coordinateFunctionalsBasis_18` at the Keccak heights).
import UniComplete.DomainCoord18
import UniKeccakSound.IdsNum.Functionals15

/-!
# The coordinate functionals at the Keccak reference height `15` (milestone 4, the domain facts)

The Keccak reference shape's `SHA3` table has height `15` (`keccakRefShape`, heights `15 16 15 16 14 15`), so the
copies' identities read `coordinateFunctionals 15`. `UniKeccakSound` checks by the kernel that these functionals
invert the Moore matrix (`UniKeccakSound.IdsNum.functionalsCorrect15 : FunctionalsCorrect 15`). Here:

* **`coordinateFunctionalsBasis_of_correct`** (every `r ≤ 32`): `FunctionalsCorrect r` gives
  `CoordinateFunctionalsBasis r`, the domain's hypothesis (`y_l(ω_{2^j}) = [l = j]`): `ω_{2^j} = β_j`
  (`Domain.point_two_pow`), `coordinatesAt` at a point of `K` is computed in `K` (`Domain.coordinatesAt_ofK`), and
  its fold `Σ_{a ≠ 0} a x` is the sum `Σ_m a_{l,m} β_j^(2^m)` (`foldIte_eq_sum`, `zipMul_eq_map`);
* **`coordinateFunctionalsBasis_15`**: hence at `15`.
-/

namespace UniKeccakComplete.AlgC

open UniComplete

open UniStatement LeanVM.Parameters

/-- `coordinatesAt`'s fold skipping the zero coefficients is the plain sum. -/
theorem foldIte_eq_sum : ∀ (as xs : List K) (c : K),
    (as.zip xs).foldl (fun acc (a, x) ↦ if a ≠ 0 then acc + a * x else acc) c =
      c + ((as.zip xs).map fun p ↦ p.1 * p.2).sum
  | [], _, c => by simp
  | _ :: _, [], c => by simp
  | a :: as, x :: xs, c => by
    rw [List.zip_cons_cons, List.foldl_cons, List.map_cons, List.sum_cons, foldIte_eq_sum as xs]
    by_cases ha : a = 0
    · simp [ha]
    · simp only [ne_eq, ha, not_false_eq_true, ite_true]
      ring

/-- A row of `r` coefficients paired with `r` values, multiplied: the sum over `m < r`. -/
theorem zipMul_eq_map {r : ℕ} (row : Array K) (f : ℕ → K) (hr : row.size = r) :
    ((row.toList.zip ((List.range r).map f)).map fun p ↦ p.1 * p.2) =
      (List.range r).map fun m ↦ row.getD m 0 * f m := by
  apply List.ext_getElem
  · simp [hr]
  · intro m h1 h2
    simp only [List.getElem_map, List.getElem_zip, List.getElem_range, Array.getElem_toList]
    have hm : m < row.size := by simp at h2; omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hm, Option.getD_some]

/-- **`coordinatesAtK` at `β_j` reads the basis** when the functionals invert the Moore matrix. -/
theorem coordinatesAtK_basis {r : ℕ} (hF : UniSound.Ids.FunctionalsCorrect r) {j : ℕ} (hj : j < r) :
    Domain.coordinatesAtK (UniStatement.beta.getD j 0) (coordinateFunctionals r) =
      (List.range r).map fun l ↦ if l = j then (1 : K) else 0 := by
  obtain ⟨hsize, hinv⟩ := hF
  have hrow : ∀ l < r, ((coordinateFunctionals r).getD l #[]).size = r := by
    intro l hl
    obtain ⟨g, hg⟩ : ∃ g : Fin r → Fin r → K, coordinateFunctionals r = Array.ofFn fun l ↦ Array.ofFn (g l) :=
      ⟨_, rfl⟩
    rw [hg, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    simp [hl]
  unfold Domain.coordinatesAtK
  dsimp only
  rw [hsize]
  apply List.ext_getElem
  · simp [hsize]
  · intro l h1 h2
    have hl : l < r := by simpa using h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    have hget : (coordinateFunctionals r)[l]'(by rw [hsize]; exact hl) = (coordinateFunctionals r).getD l #[] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hsize]; exact hl), Option.getD_some]
    rw [hget]
    refine (foldIte_eq_sum _ _ 0).trans ?_
    rw [zero_add, zipMul_eq_map _ _ (hrow l hl)]
    exact hinv l hl j hj

/-- **`FunctionalsCorrect r` gives the domain's hypothesis** `CoordinateFunctionalsBasis r` (`r ≤ 32`). -/
theorem coordinateFunctionalsBasis_of_correct {r : ℕ} (hr : r ≤ 32) (hF : UniSound.Ids.FunctionalsCorrect r) :
    Domain.CoordinateFunctionalsBasis r := by
  intro j hj
  rw [pointE, Domain.point_two_pow (by omega), Domain.coordinatesAt_ofK, coordinatesAtK_basis hF hj, List.map_map]
  refine List.map_congr_left fun l _ ↦ ?_
  simp only [Function.comp_apply]
  split_ifs
  · exact Domain.embed_one
  · exact Domain.embed_zero

/-- **The coordinate functionals of height `15` read the basis** (the Keccak reference `SHA3` height). -/
theorem coordinateFunctionalsBasis_15 : Domain.CoordinateFunctionalsBasis 15 :=
  coordinateFunctionalsBasis_of_correct (by norm_num) UniKeccakSound.IdsNum.functionalsCorrect15

end UniKeccakComplete.AlgC

/-- info: 'UniKeccakComplete.AlgC.coordinateFunctionalsBasis_15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgC.coordinateFunctionalsBasis_15
