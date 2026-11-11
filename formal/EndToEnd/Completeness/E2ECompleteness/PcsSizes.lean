-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import E2ECompleteness.PcsStaging
import Bridge.Ntt

/-!
# The sizes of the prover's tables

The witness table and the wiring table have `2^24` words, the quotient table `2^28`: what each opening needs of its
table (`pcsOpeningWithH_commitmentWithH`). Read off the definitions' shapes; nothing of the deployed circuit is
evaluated (`membershipBuilder` is irreducible here).
-/

set_option autoImplicit false

open LeanVM.Parameters PcsQuotient PcsQuotient.Domain

-- The membership circuit is a closed term of `2^22` rows: never evaluate it.
attribute [local irreducible] PcsQuotient.membershipBuilder

namespace E2ECompleteness.Pcs

theorem coefficients_size' {M : Type} [Scalable M] (m : ℕ) (offset : K) (a : Array M) :
    (coefficients m offset a).size = a.size :=
  Bridge.Ntt.coefficients_size m offset a

theorem setIfInBounds_size {α : Type} (a : Array α) (i : ℕ) (x : α) : (a.setIfInBounds i x).size = a.size := by
  simp

theorem randomizeCells_size (circuit : Circuit) (cells : Array K) (rows : Fin randomWords → K) :
    (randomizeCells circuit cells rows).size = cells.size := by
  unfold randomizeCells
  generalize circuit.randomRows.zipIdx = l
  induction l generalizing cells with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    simp

theorem membership_rows_size : (membership logRows).rows.size = 2 ^ 22 := by
  simp [membership, finish, PcsQuotient.logRows]

theorem cells_size (circuit : Circuit) (inputs : List Bool) :
    (circuit.cells inputs).size = 4 * circuit.rows.size := by
  simp [Circuit.cells]

theorem cellsOf_size (w : Secret) : (cellsOf w).size = 2 ^ 24 := by
  rw [cellsOf, cells_size, membership_rows_size]; norm_num

theorem witnessTable_size (w : Secret) (coins : Coins) :
    (witnessTable (membership logRows) (cellsOf w) coins).size = 2 ^ 24 := by
  simp only [witnessTable, witnessParts]
  rw [coefficients_size', randomizeCells_size, cellsOf_size]

theorem forIn_list_inv {α σ : Type} (P : σ → Prop) :
    ∀ (l : List α) (init : σ) (f : α → σ → Id (ForInStep σ)), P init →
      (∀ a s, P s → P (f a s).run.value) → P (forIn l init f).run
  | [], init, f, h0, _ => by simpa using h0
  | a :: l, init, f, h0, hf => by
    rw [List.forIn_cons]
    have h1 := hf a init h0
    revert h1
    generalize f a init = r
    intro h1
    cases r with
    | done b => exact h1
    | yield b => exact forIn_list_inv P l b f h1 hf

theorem forIn_range_inv {σ : Type} (P : σ → Prop) (r : Std.Legacy.Range) (init : σ)
    (f : ℕ → σ → Id (ForInStep σ)) (h0 : P init) (hf : ∀ a s, P s → P (f a s).run.value) :
    P (forIn r init f).run := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn_list_inv P _ init f h0 hf

theorem wiring_size (l : ℕ) (rows : Array Row) : (wiring l rows).size = 4 * 2 ^ l := by
  unfold wiring
  let P : Array ℕ × Array ℕ × Array ℕ → Prop := fun s ↦ s.2.2.size = 4 * 2 ^ l
  simp only [Id.run_bind, Id.run_pure]
  refine forIn_range_inv P _ _ _ ?_ ?_
  · refine forIn_range_inv P _ _ _ (by simp [P]) fun a s hs ↦ ?_
    simp only [P] at hs ⊢
    split <;> simp [hs]
  · intro a s hs
    simp only [Id.run_bind]
    refine forIn_list_inv P _ _ _ hs fun x s' hs' ↦ ?_
    simp only [P] at hs' ⊢
    split
    · simpa using hs'
    · split <;> simp [hs']

theorem membership_sigma_size : (membership logRows).sigma.size = 2 ^ 24 := by
  simp only [membership, finish, wiring_size, PcsQuotient.logRows]
  norm_num

theorem wiringTable_size : (membership logRows).wiringTable.size = 2 ^ 24 := by
  rw [Circuit.wiringTable, coefficients_size', Array.size_map, membership_sigma_size]

theorem quotientTable_size (circuit : Circuit) (stmt : Statement) (cells₀ : Array K) (coins : Coins)
    (α β μ : E) :
    (quotientTable circuit stmt cells₀ coins α β μ).size = 2 ^ (cellVars circuit.logRows + 4) := by
  simp only [quotientTable, Array.size_ofFn]
  ring

end E2ECompleteness.Pcs
