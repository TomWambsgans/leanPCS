-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the honest witness table as F1's first message, and the relation on F1's cells.
import E2ECompleteness.PcsHInstance

/-!
# The honest witness table, and the relation on F1's cells

`cellsR w coins` are the circuit's cells with the random rows filled (`randomizeCells`), the witness table their
coefficients (`witnessTable = coefficients 24 0 cellsR`), `cW` the table in `E` by bits. Then:

* `cW_eval_point`: the table's polynomial takes the value of cell `c` at `B(c)`;
* `cellPoly_eval`: F1's polynomial of role `r` of `witnessOfTable cW`, at `x`, is the table's polynomial at
  `x + shift θ r`; so F1's cell `cellAt c` holds cell `c` (`cells_cellAt`);
* **`sat_of_idx`**: cells satisfying the gates, the copies and the pins by index (`GatesIdx`, `CopiesIdx`,
  `PinsIdx`: F0's, `formal/Kc3Circuit/Cells.lean`) satisfy F1's relation `Sat`.

`HonestSat` is F0's `sat_honest`: for a secret of the statement and any random rows, the filled cells satisfy the
three by index.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

-- The membership circuit is a closed term of `2^22` rows: never evaluate it.
attribute [local irreducible] PcsQuotient.membership PcsQuotient.membershipBuilder

namespace E2ECompleteness.Pcs.H

/-! ## The relation by index (F0's) -/

/-- The gates hold on every row (`Kc3.gate`: `V + Y + C + X·C = 0`). -/
def GatesIdx (v : ℕ → E) : Prop :=
  ∀ r < 2 ^ 22, _root_.Kc3.gate (v (4 * r)) (v (4 * r + 1)) (v (4 * r + 2)) (v (4 * r + 3)) = 0

/-- σ keeps the values. -/
def CopiesIdx (v : ℕ → E) : Prop := ∀ c < 4 * 2 ^ 22, v (sig c) = v c

/-- The pinned cells hold the statement's words and the constants. -/
def PinsIdx (s : Statement) (v : ℕ → E) : Prop :=
  ∀ k < 11, v (4 * k + 2) = ofK (anchorValues s.words k)

/-- The circuit's cells with the random rows filled. -/
def cellsR (w : Secret) (coins : Coins) : Array K := randomizeCells (membership logRows) (cellsOf w) coins.rows

/-- **F0's `sat_honest`**: for a secret of the statement and any random rows, the filled cells satisfy the gates,
the copies and the pins. -/
def HonestSat : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w → ∀ coins : Coins,
    GatesIdx (fun c => ofK ((cellsR w coins).getD c 0)) ∧ CopiesIdx (fun c => ofK ((cellsR w coins).getD c 0)) ∧
      PinsIdx stmt (fun c => ofK ((cellsR w coins).getD c 0))

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

variable (hσ : SigmaPerm)

/-- **F1's polynomial of a role** of a witness table's first message is the table's polynomial, shifted. -/
theorem cellPoly_eval (c : (Fin 24 → Bool) → E) (r : Fin 4) (x : E) :
    ((deployedP hσ).cellPoly (witnessOfTable (k := 22) c) r).eval x =
      (tablePoly c).eval (x + shift (deployedP hσ).θ r) := by
  rw [← Completeness.witnessPoly_witnessOfTable_eval c]
  simp only [_root_.Kc3.Params.cellPoly, QuotientSecurity.Instance.witnessPoly, eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(deployedP hσ).rowPoly_eval_shift]

theorem cells_cellAt (c : (Fin 24 → Bool) → E) {i : ℕ} (hi : i < 2 ^ 24) :
    (deployedP hσ).cells (witnessOfTable (k := 22) c) (cellAt i) = (tablePoly c).eval (ofK (point i)) := by
  show ((deployedP hσ).cellPoly _ (cellAt i).2).eval ((cellAt i).1 : E) = _
  rw [cellPoly_eval, ← deployedP_pt_cellAt hσ hi]
  rfl

/-- **The relation on F1's cells**, from the relation by index. -/
theorem sat_of_idx (stmt : Statement) (g : Fin 4 → E[X]) (v : ℕ → E)
    (hv : ∀ i < 2 ^ 24, (deployedP hσ).cells g (cellAt i) = v i)
    (hg : GatesIdx v) (hc : CopiesIdx v) (hp : PinsIdx stmt v) :
    (deployedP hσ).Sat (fun k => ofK (anchorValues stmt.words k)) ((deployedP hσ).cells g) := by
  refine ⟨fun x => ?_, fun i => ?_, fun k => ?_⟩
  · obtain ⟨r, hr, rfl⟩ := exists_rowOf x
    have e : ∀ c : Fin 4, (deployedP hσ).cells g (rowOf r, c) = v (4 * r + c) := fun c => by
      have := hv (4 * r + c) (by have := c.2; omega)
      rw [cellAt_cell] at this
      exact this
    rw [e 0, e 1, e 2, e 3]
    exact hg r hr
  · obtain ⟨c, hc', hi⟩ := exists_cellAt i
    have h1 : (deployedP hσ).σ (cellAt c) = cellAt (sig c) := sigmaP_cellAt hσ hc'
    rw [← hi, h1, hv _ hc', hv _ (hσ.1 c hc')]
    exact hc c (by omega)
  · have hk := k.2
    simp only [_root_.Kc3.pinCount] at hk
    have e : cellAt (4 * k + 2) = (rowOf k, 2) := cellAt_cell k 2
    have h1 : (deployedP hσ).pinCell k = cellAt (4 * k + 2) := e.symm
    rw [h1, hv _ (by omega)]
    exact hp k hk

end E2ECompleteness.Pcs.H
