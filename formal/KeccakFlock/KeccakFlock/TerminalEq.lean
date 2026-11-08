-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import KeccakFlock.TerminalShifts

/-!
# The structured terminal's body is the walked form

`structuredCore_eq`: for any tables, with the packing weights summing to 1 (`Σ_z Ew_z = 1`, as Lagrange weights and an
eq table each do) and the word weights the factored eq tables (`wordW`), `structuredCore` with the correlations
`Corr[off] = Σ_z Ew_z sv_(z − off)` (zero off the needed offsets) is the walked form `WF` plus the `C = I` claim
`α² eq(chi_in, chi_in') Corr[0]` and the pin `α³ γ(1) sv_0`.
-/

namespace KeccakFlock.Core

open LeanVM.Parameters PcsCircuit PcsCircuit.Builder Finset KeccakFlock.Terminal UniStatement

/-! ## Regrouping sums -/

theorem sum_regroup1 (s : Finset ℕ) (f g : ℕ → E) (a b : E) :
    ∑ x ∈ s, f x * (a * g x + b) = a * ∑ x ∈ s, f x * g x + b * ∑ x ∈ s, f x := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

theorem sum_regroup2 (f p q : ℕ → ℕ → E) (c : E) :
    ∑ j ∈ range 24, ∑ l ∈ range 25, f j l * (c + p j l + q j l) =
      c * ∑ j ∈ range 24, ∑ l ∈ range 25, f j l + ∑ j ∈ range 24, ∑ l ∈ range 25, f j l * (p j l + q j l) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

theorem sum_regroup3 (f p g : ℕ → ℕ → E) (r : ℕ → E) (a b c1 : E) :
    ∑ j ∈ range 24, ∑ l ∈ range 25, f j l * (p j l + a * g j l + (if l = 0 then r j * c1 else 0) + b) =
      ∑ j ∈ range 24, ∑ l ∈ range 25, f j l * p j l + a * ∑ j ∈ range 24, ∑ l ∈ range 25, f j l * g j l +
        c1 * ∑ j ∈ range 24, f j 0 * r j + b * ∑ j ∈ range 24, ∑ l ∈ range 25, f j l := by
  have hj : ∀ j ∈ range 24, ∑ l ∈ range 25, f j l * (p j l + a * g j l + (if l = 0 then r j * c1 else 0) + b) =
      ∑ l ∈ range 25, f j l * p j l + a * ∑ l ∈ range 25, f j l * g j l + c1 * (f j 0 * r j) +
        b * ∑ l ∈ range 25, f j l := fun j _ ↦ by
    have e : ∀ l ∈ range 25, f j l * (p j l + a * g j l + (if l = 0 then r j * c1 else 0) + b) =
        f j l * p j l + a * (f j l * g j l) + (if l = 0 then c1 * (f j 0 * r j) else 0) + b * f j l :=
      fun l _ ↦ by split_ifs with h <;> [subst h; skip] <;> ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq' (range 25) 0, ite_eq_left (by simp), ← Finset.mul_sum, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl hj, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ## The identity -/

theorem wordW_one (lAt rAt : ℕ → E) (k5 : E) : wordW lAt rAt k5 1 = lAt 1 * groupW k5 rAt 0 := by
  unfold wordW groupW
  rw [show (1 : ℕ) % 32 = 1 from rfl, show (1 : ℕ) / 32 % 2 = 0 from rfl, show (1 : ℕ) / 64 = 0 from rfl]
  ring

/-- **The structured terminal's body is the walked form**, plus the `C = I` claim and the pin. -/
theorem structuredCore_eq (Ew sv lr rd lh rh : ℕ → E) (kr5 kh5 α cEq : E) (hE : ∑ z ∈ range 64, Ew z = 1) :
    structuredCore Ew (fun off ↦ if needed off then corr Ew sv off else 0) lr rd lh rh sv kr5 kh5 α cEq =
      WF Ew sv (wordW lr rd kr5) (wordW lh rh kh5) α + α * α * cEq * corr Ew sv 0 +
        α * α * α * (wordW lh rh kh5 1 * sv 0) := by
  have h0 : needed 0 = true := rfl
  rw [WF_eq, structuredCore, oneCoefficient, tOne_eq, rcOne_eq, constants_eq, bOne_eq, diagonal_eq, shifts_eq,
    ite_eq_left h0, hE, sum_regroup1, sum_regroup1, sum_regroup2, sum_regroup3, ← wordW_one,
    ← Finset.sum_mul (range 32)]
  simp only [Finset.sum_add_distrib]
  ring

end KeccakFlock.Core
