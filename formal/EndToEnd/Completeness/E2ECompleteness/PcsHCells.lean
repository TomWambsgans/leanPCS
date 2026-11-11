-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the honest witness table as F1's first message, and the relation on F1's cells.
import E2ECompleteness.PcsHInstance

/-!
# The honest witness table, and the relation on F1's cells

`cellsR w coins` are the circuit's cells with the random rows filled (`randomizeCells`), the witness table their
coefficients (`witnessTable = coefficients 24 0 cellsR`), `cW` the table in `E` by bits. `cW_eval_point`: its
polynomial takes the value of cell `c` at `B(c)`; `cells_cW`: F1's cells of `witnessOfTable cW` are F0's
`honestCells`; **`sat_cW`**: they satisfy F1's relation (F0's `sat_honest_of_relation`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

-- The membership circuit is a closed term of `2^22` rows: never evaluate it.
attribute [local irreducible] PcsQuotient.membership PcsQuotient.membershipBuilder

namespace E2ECompleteness.Pcs.H

/-- The circuit's cells with the random rows filled. -/
def cellsR (w : Secret) (coins : Coins) : Array K := randomizeCells (membership logRows) (cellsOf w) coins.rows

theorem cellsR_size (w : Secret) (coins : Coins) : (cellsR w coins).size = 2 ^ 24 := by
  rw [cellsR, E2ECompleteness.Pcs.randomizeCells_size, E2ECompleteness.Pcs.cellsOf_size]

/-! ## The witness table -/

theorem witnessTable_eq (w : Secret) (coins : Coins) :
    witnessTable (membership logRows) (cellsOf w) coins = coefficients 24 0 (cellsR w coins) := by
  show coefficients (cellVars (membership logRows).logRows) 0 (cellsR w coins) = _
  rw [membership_logRows']
  rfl

/-- The witness table in `E`, by bits. -/
noncomputable def cW (w : Secret) (coins : Coins) : (Fin 24 → Bool) → E :=
  fun b => ofK ((coefficients 24 0 (cellsR w coins)).getD (Completeness.idx b) 0)

theorem cW_eq (w : Secret) (coins : Coins) (b : Fin 24 → Bool) :
    cW w coins b = ofK ((witnessTable (membership logRows) (cellsOf w) coins).getD (Completeness.idx b) 0) := by
  rw [witnessTable_eq]; rfl

theorem tablePoly_cW (w : Secret) (coins : Coins) :
    tablePoly (cW w coins) = Novel.nov 0 24 (fun j => ofK ((coefficients 24 0 (cellsR w coins)).getD j 0)) :=
  tablePoly_idx 24 (fun j => ofK ((coefficients 24 0 (cellsR w coins)).getD j 0))

theorem cW_eval_point (w : Secret) (coins : Coins) {c : ℕ} (hc : c < 2 ^ 24) :
    (tablePoly (cW w coins)).eval (ofK (point c)) = ofK ((cellsR w coins).getD c 0) := by
  have h := nov_coefficients_K (m := 24) (by norm_num) 0 _ (cellsR_size w coins) hc
  rw [zero_add] at h
  rw [tablePoly_cW, h]

/-! ## F1's cells -/

/-- **F1's cells of the witness table's first message** are the filled cells, by number. -/
theorem cells_cW (w : Secret) (coins : Coins) (i : P0.T × Fin 4) :
    P0.cells (witnessOfTable (k := 22) (cW w coins)) i = Kc3Deployed.honestCells BE hm28 w coins.rows i := by
  have h1 := PcsBridge.Kc3.cells_witnessOfTable P0 (cW w coins) i
  have h2 := pt_idx i
  have hl : (Kc3Deployed.idxE BE hm28 i : ℕ) < 2 ^ 24 := by have := Kc3Deployed.idx_lt BE hm28 i; omega
  have h3 := cW_eval_point w coins hl
  exact h1.trans ((congrArg (fun x => (tablePoly (cW w coins)).eval x) h2).trans h3)

/-- **The honest first message satisfies F1's relation** (F0's `sat_honest`). -/
theorem sat_cW {stmt : Statement} {w : Secret} (h : Relation stmt w) (coins : Coins) :
    P0.Sat (Kc3Deployed.stmtOf stmt) (P0.cells (witnessOfTable (k := 22) (cW w coins))) := by
  have e : P0.cells (witnessOfTable (k := 22) (cW w coins)) = Kc3Deployed.honestCells BE hm28 w coins.rows :=
    funext (cells_cW w coins)
  rw [e]
  exact Kc3Deployed.sat_honest_of_relation BE hm28 h coins.rows

end E2ECompleteness.Pcs.H
