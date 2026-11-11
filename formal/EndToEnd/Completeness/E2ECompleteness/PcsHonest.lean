-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Extends `formal/QuotientSecurity/Completeness.lean`'s honest second message (adapted from leanVM,
-- branch PCS-openings-aggregation, commit 651453c6) with the PCS claims' blinding of `h`. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the fields `K`, `E`.
import Completeness
import E2ECompleteness.PcsDefs

/-!
# The honest second message with the blinding of `h`

The PCS claims' prover blinds the sum's polynomial: `h = h₀ + X_{2^m}·b`, `X_{2^m}` the cells' vanishing
polynomial `digitPoly m` and `b` of degree below `8` (`blindPoly`, its coefficients the blinding words). In
F1's terms (`Params.Quotients`) this is `hHigh = b`; the copy quotient takes `d d' b` more
(`honestB`: `q + d d' b`, characteristic two), the gate quotient and the sum over the cells (`top`, of `h₀`)
are unchanged. **`honestB_consistent`**: the blinded message is consistent whenever the honest one is;
**`honestB_accepts`**: so it is accepted at non-degenerate challenges (`Reduction.honest_accepts`'s
argument). The degrees: **`natDegree_dd_le`**, `d d'` of degree at most `2^25 + 22` for a first message of
degree at most `2^22 + 2`, so `q + d d' b` stays below `2^26` (`natDegree_honestB_q_lt`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM.Parameters QuotientSecurity

namespace E2ECompleteness.Pcs

/-! ## The blinding polynomial -/

/-- **The blinding polynomial**: the table on `24` digits with the blinding words at `0 … 7`, over `E`. -/
noncomputable def blindPoly (blind : Fin 3 → Fin PcsQuotient.hBlind → K) : E[X] :=
  tablePoly (fun b : Fin (22 + 2) → Bool ↦ blindAt blind (Completeness.idx b))

theorem natDegree_blindPoly_lt (blind : Fin 3 → Fin PcsQuotient.hBlind → K) :
    (blindPoly blind).natDegree < 8 :=
  Completeness.natDegree_tablePoly_lt_of_support _ (by norm_num) fun b hb ↦ by
    unfold blindAt
    rw [dite_eq_right_iff.mpr fun h ↦ absurd h (by unfold PcsQuotient.hBlind; omega)]

/-! ## The blinded message -/

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2] [Fintype F]

/-- **The honest second message, `h` blinded by `b`**: `hHigh = b`, the copy quotient `q + d d' b`. -/
noncomputable def honestB (P : Params F) (g : Params.Witness F) (α β γ : F) (b : F[X]) :
    Params.Quotients F where
  h₀ := (Params.honest P g α β γ).h₀
  hHigh := b
  q := (Params.honest P g α β γ).q + Params.dPoly P g α β * Params.dNextPoly P g α β * b
  qGate := (Params.honest P g α β γ).qGate
  junk := 0

/-- **The blinded message is consistent** when the honest one is. -/
theorem honestB_consistent (P : Params F) (stmt : Fin P.words → F) (g : Params.Witness F)
    (α β γ : F) (b : F[X]) (h : P.Consistent stmt g (Params.honest P g α β γ) α β γ) :
    P.Consistent stmt g (honestB P g α β γ b) α β γ := by
  obtain ⟨hc, hg, ht⟩ := h
  refine ⟨?_, ?_, ht⟩
  · have e : Params.copyDefect P g (honestB P g α β γ b) α β γ =
        Params.copyDefect P g (Params.honest P g α β γ) α β γ +
          (Params.dPoly P g α β * Params.dNextPoly P g α β * P.vCells * b +
            Params.dPoly P g α β * Params.dNextPoly P g α β * P.vCells * b) := by
      simp only [Params.copyDefect, Params.Quotients.h, honestB, Params.honest]
      ring
    rw [e, hc, CharTwo.add_self_eq_zero, add_zero]
  · exact hg

/-- **The blinded message is accepted** at challenges where the sum exists and the Rust check passes. -/
theorem honestB_accepts (I : Instance E) (stmt : Fin 8 → E) (g : Fin 4 → E[X])
    (hsat : I.Relation stmt (I.cellsOf g)) (α β γ t ρ : E) (b : E[X])
    (hab : ¬ Completeness.Reduction.BadAB I g α β) (ht : ¬ Completeness.Reduction.Degenerate I g α β t) :
    I.params.Accepts stmt g (honestB I.params g α β γ b) α β γ t (Params.opened g t)
      (I.params.sigmaPoly.eval t) ρ := by
  have hsat' := I.sat_of_relation stmt g hsat
  have hd : ∀ i, α + I.params.cells g i + β * I.params.pt i ≠ 0 := fun i h => hab ⟨i, Or.inl h⟩
  have hd' : ∀ i, α + I.params.cells g i + β * I.params.pt (I.params.σ i) ≠ 0 :=
    fun i h => hab ⟨i, Or.inr h⟩
  have hcons := honestB_consistent I.params stmt g α β γ b
    (Params.honest_consistent I.exact stmt g α β γ hsat' hd hd')
  refine Params.accepts_of_consistent (P := I.params) stmt g _ α β γ t ρ hcons ?_
  have e := rejectPoly_eval (P := I.params) g α β t
  rw [Params.cellAt_opened] at e
  rw [← e]
  exact fun h0 => ht (Or.inr h0)

/-! ## Degrees -/

/-- `d` of a first message of degree at most `2^22 + 2`: at most `2^24 + 11`. -/
theorem natDegree_dPoly_le' (I : Instance F) (g : Fin 4 → F[X]) (hg : ∀ j, (g j).natDegree ≤ 2 ^ 22 + 2)
    (α β : F) : (Params.dPoly I.params g α β).natDegree ≤ 16777227 := by
  let B' : I.params.Bounds := { I.bounds with witness := 2 ^ 22 + 2 }
  have hc : (Params.cellPoly I.params g 0).natDegree ≤ 16777227 :=
    (Params.natDegree_cellPoly_le B' ⟨g, hg⟩ 0).trans (by show 3 + (2 ^ 22 + 2) * 4 ≤ 16777227; norm_num)
  unfold Params.dPoly
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ hc) ?_
  · rw [natDegree_C]; omega
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by omega))

/-- `d'`, for any parameters, from the degrees of the `X` cells' polynomial and of the wiring polynomial. -/
theorem natDegree_dNextPoly_le_of (P : Params F) (g : Fin 4 → F[X]) (α β : F) {D : ℕ}
    (hc : (Params.cellPoly P g 0).natDegree ≤ D) (hσ : P.sigmaPoly.natDegree ≤ D) :
    (Params.dNextPoly P g α β).natDegree ≤ D := by
  unfold Params.dNextPoly
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ hc) ?_
  · rw [natDegree_C]; omega
  · exact (natDegree_C_mul_le _ _).trans hσ

/-- `d'` of a first message of degree at most `2^22 + 2`: at most `2^24 + 11`. -/
theorem natDegree_dNextPoly_le' (I : Instance F) (g : Fin 4 → F[X])
    (hg : ∀ j, (g j).natDegree ≤ 2 ^ 22 + 2) (α β : F) :
    (Params.dNextPoly I.params g α β).natDegree ≤ 16777227 := by
  let B' : I.params.Bounds := { I.bounds with witness := 2 ^ 22 + 2 }
  have hc : (Params.cellPoly I.params g 0).natDegree ≤ 16777227 :=
    (Params.natDegree_cellPoly_le B' ⟨g, hg⟩ 0).trans (by show 3 + (2 ^ 22 + 2) * 4 ≤ 16777227; norm_num)
  have hσ : I.params.sigmaPoly.natDegree ≤ 16777227 :=
    I.bounds.hSigma.trans (by show 2 ^ (22 + 2) ≤ 16777227; norm_num)
  exact natDegree_dNextPoly_le_of I.params g α β hc hσ

/-- **`d d'`**: at most `2^25 + 22`. -/
theorem natDegree_dd_le (I : Instance F) (g : Fin 4 → F[X]) (hg : ∀ j, (g j).natDegree ≤ 2 ^ 22 + 2)
    (α β : F) :
    (Params.dPoly I.params g α β * Params.dNextPoly I.params g α β).natDegree ≤ 33554454 :=
  natDegree_mul_le.trans (by
    have h1 := natDegree_dPoly_le' I g hg α β
    have h2 := natDegree_dNextPoly_le' I g hg α β
    omega)

/-- The blinded copy quotient's degree, for any parameters. -/
theorem natDegree_honestB_q_lt_of (P : Params F) (g : Fin 4 → F[X]) (α β γ : F) (b : F[X])
    (hq : (Params.honest P g α β γ).q.natDegree ≤ 50340897)
    (hdd : (Params.dPoly P g α β * Params.dNextPoly P g α β).natDegree ≤ 33554454)
    (hb : b.natDegree < 8) : (honestB P g α β γ b).q.natDegree < 67108864 := by
  show ((Params.honest P g α β γ).q + Params.dPoly P g α β * Params.dNextPoly P g α β * b).natDegree <
    67108864
  refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt (by omega) ?_)
  exact lt_of_le_of_lt natDegree_mul_le (by omega)

/-- **The blinded copy quotient fits `2^26` coefficients**, for a blinding of degree below `8`. -/
theorem natDegree_honestB_q_lt (I : Instance F) (g : Fin 4 → F[X])
    (hg : ∀ j, (g j).natDegree ≤ 2 ^ 22 + 2) (α β γ : F) (b : F[X]) (hb : b.natDegree < 8) :
    (honestB I.params g α β γ b).q.natDegree < 67108864 :=
  natDegree_honestB_q_lt_of I.params g α β γ b
    ((Completeness.honest_degrees I g hg α β γ).2.1.trans (by norm_num))
    (natDegree_dd_le I g hg α β) hb

end E2ECompleteness.Pcs
