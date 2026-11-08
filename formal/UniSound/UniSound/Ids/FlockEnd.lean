-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniSound.Ids.CvecOk
import UniSound.Ids.Weights

/-!
# `DiffsFlockP`: the ring-switch relation gives Flock's claim on `q_flock`

The main line's ring-switch relation `⟨[q_flock at p, twist ringTwist], target⟩` is one of `C1`'s
relations (`relsOf`'s `ringRels`); `combine` may merge its point into a longer one, which changes nothing
(`termWExtend`: the ring term reads `vars = 8 + (D.shape.heights.getD opBlake2s 0) = |p|` coordinates). Its weight on the cube is the tower
weight (`ringInner`), which is `Σ_k d_k eq(φ^k(p), ·)` (`TowerWeight`), so its difference is
`Σ_k d_k q̂(φ^k(p)) + target` (`FlockEndHolds`).
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset

theorem sqn_zero : ∀ k, sqn (0 : E) k = 0
  | 0 => rfl
  | k + 1 => by rw [sqn, mul_zero]; exact sqn_zero k

theorem twist_getD (p : List E) (k n : ℕ) : (twist p k).getD n 0 = sqn (p.getD n 0) k := by
  unfold twist
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases p[n]? with
  | none => simp only [Option.map_none, Option.getD_none]; exact (sqn_zero k).symm
  | some a => rfl

theorem bitsE_getD (x n i : ℕ) (hi : i < n) : (bitsE x n).getD i 0 = if x.testBit i then 1 else 0 := by
  unfold bitsE
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]

end UniSound.Ids
