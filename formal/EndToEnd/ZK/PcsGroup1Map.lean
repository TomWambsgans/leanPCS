-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsGroup1Weights
import ZK.PcsGroup1W
import Kc3Circuit.Honest
import E2ECompleteness.PcsHInstance

/-!
# Group 1 as an affine map of the random rows

`group1` (`W`'s answer at `zW`, `C`, `V + Y`, `X` at `t`) is a sum over the cells with weights of the challenges
(`PcsGroup1Weights.lean`): `wW`, `wC`, `wVY`, `wX`. The random rows (rows `2^22 − 1 − k`, `k < 16`) fill their cells
with their shape's linear forms of their two words, so each scalar is a constant plus `Lsum wt rows`, the words
weighed by `RW wt k` (`r`-word) and `SW wt k` (`s`-word): **`group1_eq`**.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open PcsQuotient.Domain QuotientSecurity Finset

-- The membership circuit is a closed term of `2^22` rows: never evaluate it.
attribute [local irreducible] PcsQuotient.membership PcsQuotient.membershipBuilder

namespace PcsQuotient.EndToEnd.Group1

/-! ### The random rows' words -/

/-- Word `i` of the random rows, zero past them (`randomizeCells`' `word`). -/
def wd (rows : Fin randomWords → K) (i : ℕ) : K := if h : i < randomWords then rows ⟨i, h⟩ else 0

/-- Random row `k`'s index, `2^22 − 1 − k`. -/
def Rk (k : ℕ) : ℕ := 2 ^ 22 - 1 - k

/-- The weight of row `k`'s `r`-word for the cell weights `wt` (cells `Y`, `V`). -/
def RW (wt : ℕ → E) (k : ℕ) : E := wt (4 * Rk k + 1) + wt (4 * Rk k + 3)

/-- The weight of row `k`'s `s`-word: cells `C`, `V` (sum), `X` (select), `C` (pass). -/
def SW (wt : ℕ → E) (k : ℕ) : E :=
  match RandomShape.of k with
  | .sum => wt (4 * Rk k + 2) + wt (4 * Rk k + 3)
  | .select => wt (4 * Rk k)
  | .pass => wt (4 * Rk k + 2)

/-- **The random words' contribution** with the cell weights `wt`. -/
noncomputable def Lsum (wt : ℕ → E) (rows : Fin randomWords → K) : E :=
  ∑ k ∈ range 16, (ofK (wd rows (2 * k)) * RW wt k + ofK (wd rows (2 * k + 1)) * SW wt k)

theorem wd_zero (i : ℕ) : wd 0 i = 0 := by unfold wd; split_ifs <;> rfl

/-- A random row's four cells, less those of zero words, are its words' linear forms. -/
theorem row_contrib (rows : Fin randomWords → K) (k : ℕ) (wt : ℕ → E) :
    ∑ j ∈ range 4, ofK (Kc3Closed.shapeVal rows k j - Kc3Closed.shapeVal 0 k j) * wt (4 * Rk k + j) =
      ofK (wd rows (2 * k)) * RW wt k + ofK (wd rows (2 * k + 1)) * SW wt k := by
  have hw : ∀ i, (if h : i < randomWords then (0 : Fin randomWords → K) ⟨i, h⟩ else 0) = 0 := fun i ↦ by
    split_ifs <;> rfl
  simp only [Kc3Closed.shapeVal, hw, sum_range_succ, sum_range_zero, zero_add, RW, SW]
  rw [show (if h : 2 * k < randomWords then rows ⟨2 * k, h⟩ else 0) = wd rows (2 * k) from rfl,
    show (if h : 2 * k + 1 < randomWords then rows ⟨2 * k + 1, h⟩ else 0) = wd rows (2 * k + 1) from rfl]
  generalize wd rows (2 * k) = r
  generalize wd rows (2 * k + 1) = s
  rcases RandomShape.of k with _ | _ | _ <;>
    simp only [RandomShape.cells, ofK_sub, ofK_add, ofK_zero, ofK_one, sub_self, sub_zero, zero_mul, add_zero,
      zero_add, mul_zero, Nat.add_zero, if_true, if_false, one_ne_zero, OfNat.ofNat_ne_zero,
      show (1 : ℕ) ≠ 0 from one_ne_zero, show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num,
      show (3 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 1 by norm_num, show (3 : ℕ) ≠ 2 by norm_num] <;> ring

/-- A sum over `4 n` numbers by blocks of four. -/
theorem sum_range_four_mul (f : ℕ → E) : ∀ n : ℕ,
    ∑ l ∈ range (4 * n), f l = ∑ q ∈ range n, ∑ j ∈ range 4, f (4 * q + j)
  | 0 => by simp
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 4 by ring, sum_range_add, sum_range_four_mul f n, sum_range_succ (n := n)]

/-- **The random words' part of a sum over the cells.** -/
theorem sum_cells_decomp (cells₀ : Array K) (hc : cells₀.size = 2 ^ 24) (rows : Fin randomWords → K)
    (wt : ℕ → E) :
    ∑ i ∈ range (2 ^ 24), ofK ((randomizeCells (membership logRows) cells₀ rows).getD i 0) * wt i =
      ∑ i ∈ range (2 ^ 24), ofK ((randomizeCells (membership logRows) cells₀ 0).getD i 0) * wt i +
        Lsum wt rows := by
  have hrs : (membership logRows).rows.size = 2 ^ 22 := E2ECompleteness.Pcs.membership_rows_size
  set dlt : ℕ → K := fun i ↦ if 2 ^ 22 - 16 ≤ i / 4 then
    Kc3Closed.shapeVal rows (2 ^ 22 - 1 - i / 4) (i % 4) - Kc3Closed.shapeVal 0 (2 ^ 22 - 1 - i / 4) (i % 4)
    else 0 with hdlt
  have hcell : ∀ i ∈ range (2 ^ 24), ofK ((randomizeCells (membership logRows) cells₀ rows).getD i 0) * wt i =
      ofK ((randomizeCells (membership logRows) cells₀ 0).getD i 0) * wt i + ofK (dlt i) * wt i := by
    intro i hi
    have hi' : i < 2 ^ 24 := mem_range.1 hi
    rw [Kc3Closed.randomize_getD _ _ _ i (by rw [hc]; exact hi') (by rw [hrs]; omega) (by rw [hrs]; norm_num),
      Kc3Closed.randomize_getD _ _ _ i (by rw [hc]; exact hi') (by rw [hrs]; omega) (by rw [hrs]; norm_num), hrs,
      ← add_mul, ← ofK_add]
    simp only [hdlt]
    split_ifs
    · rw [add_sub_cancel]
    · rw [add_zero]
  rw [sum_congr rfl hcell, sum_add_distrib, add_right_inj]
  -- The random words' part: the last `64` cells.
  rw [show (2 : ℕ) ^ 24 = 16777152 + 4 * 16 by norm_num, sum_range_add]
  have h0 : ∑ i ∈ range 16777152, ofK (dlt i) * wt i = 0 := sum_eq_zero fun i hi ↦ by
    have := mem_range.1 hi
    simp only [hdlt, show ¬ (2 ^ 22 - 16 ≤ i / 4) by norm_num; omega, if_false, ofK_zero, zero_mul]
  rw [h0, zero_add, sum_range_four_mul, Lsum, ← sum_range_reflect]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' : k < 16 := mem_range.1 hk
  rw [← row_contrib rows k wt]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' : j < 4 := mem_range.1 hj
  have hidx : 16777152 + (4 * (16 - 1 - k) + j) = 4 * Rk k + j := by unfold Rk; norm_num; omega
  rw [hidx]
  simp only [hdlt]
  rw [if_pos (by unfold Rk; norm_num; omega), show (4 * Rk k + j) / 4 = Rk k by omega,
    show (4 * Rk k + j) % 4 = j by omega, show 2 ^ 22 - 1 - Rk k = k by unfold Rk; norm_num; omega]

/-! ### Group 1 -/

/-- `W`'s weight of cell `i` at `z`. -/
noncomputable def wW (z : List E) (i : ℕ) : E := ∏ b ∈ range 24, (1 + (1 + xc z b) * pt (i / 2 ^ b))

/-- `X`'s weight of cell `i` at `t`. -/
noncomputable def wX (t : E) (i : ℕ) : E := lam t i

/-- `C`'s weight of cell `i` at `t`. -/
noncomputable def wC (t : E) (i : ℕ) : E := lam (t + θE) i

/-- `V + Y`'s weight of cell `i` at `t`. -/
noncomputable def wVY (t : E) (i : ℕ) : E := lam (t + 1) i + lam (t + θE + 1) i

/-- The constant part: the cells with zero random words. -/
noncomputable def G0 (cells₀ : Array K) (wt : ℕ → E) : E :=
  ∑ i ∈ range (2 ^ 24), ofK ((randomizeCells (membership logRows) cells₀ 0).getD i 0) * wt i

/-- **Group 1 is affine in the random rows' words.** -/
theorem group1_eq (stmt : Statement) (cells₀ : Array K) (hc : cells₀.size = 2 ^ 24) (coins : Coins)
    (c : Challenges) (hz : c.zW.length = 24) :
    group1 stmt cells₀ coins c =
      [G0 cells₀ (wW c.zW) + Lsum (wW c.zW) coins.rows, G0 cells₀ (wC c.t) + Lsum (wC c.t) coins.rows,
        G0 cells₀ (wVY c.t) + Lsum (wVY c.t) coins.rows, G0 cells₀ (wX c.t) + Lsum (wX c.t) coins.rows] := by
  have hv : (randomizeCells (membership logRows) cells₀ coins.rows).size = 2 ^ 24 := by
    rw [E2ECompleteness.Pcs.randomizeCells_size, hc]
  have hW : (witnessParts (membership logRows) cells₀ coins).2 =
      coefficients 24 0 (randomizeCells (membership logRows) cells₀ coins.rows) := by
    show coefficients (cellVars (membership logRows).logRows) 0
      (randomizeCells (membership logRows) cells₀ coins.rows) = _
    rw [E2ECompleteness.Pcs.H.membership_logRows']
    rfl
  have e0 : revealAnswer (membership logRows) stmt cells₀ coins (.oodW c.zW) =
      G0 cells₀ (wW c.zW) + Lsum (wW c.zW) coins.rows := by
    show tableEval (witnessTable (membership logRows) cells₀ coins) c.zW = _
    rw [witnessTable, hW, tableEval_coefficients 24 le_rfl _ hv _ hz]
    exact sum_cells_decomp cells₀ hc coins.rows (wW c.zW)
  obtain ⟨h0, h1, h2⟩ := valuesAt_cells (membership logRows) E2ECompleteness.Pcs.H.membership_logRows' cells₀
    coins c.t
  rw [hW, nov_coefficients_eval _ hv] at h0 h1 h2
  rw [nov_coefficients_eval _ hv] at h2
  have e1 : revealAnswer (membership logRows) stmt cells₀ coins (.value 1 c.t) =
      G0 cells₀ (wC c.t) + Lsum (wC c.t) coins.rows := by
    show (valuesAt (membership logRows) cells₀ coins c.t).1[1] = _
    rw [h1]
    exact sum_cells_decomp cells₀ hc coins.rows (wC c.t)
  have e2 : revealAnswer (membership logRows) stmt cells₀ coins (.value 2 c.t) =
      G0 cells₀ (wVY c.t) + Lsum (wVY c.t) coins.rows := by
    show (valuesAt (membership logRows) cells₀ coins c.t).1[2] = _
    rw [h2, ← sum_add_distrib]
    simp only [← mul_add]
    exact sum_cells_decomp cells₀ hc coins.rows (wVY c.t)
  have e3 : revealAnswer (membership logRows) stmt cells₀ coins (.value 0 c.t) =
      G0 cells₀ (wX c.t) + Lsum (wX c.t) coins.rows := by
    show (valuesAt (membership logRows) cells₀ coins c.t).1[0] = _
    rw [h0]
    exact sum_cells_decomp cells₀ hc coins.rows (wX c.t)
  show [_, _, _, _] = _
  rw [e0, e1, e2, e3]

end PcsQuotient.EndToEnd.Group1
