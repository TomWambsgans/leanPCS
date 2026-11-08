-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import KeccakFlock.Terminal

/-!
# The walked terminal is the matrices' bilinear form

`walkedTerminal_eq_bilinear`: for all inputs, `Terminal.walkedTerminal` (`walked_terminal_with::<_, KeccakWalked>`
with the specification's forward walk) is

`Σ_(k, j) e_k (A_kj + α B_kj) w_j + α² eq(chi_in, chi_in') ⟨lowWeights, s⟩ + α³ eq(word 1, chi_in') s_0`

with `A, B` the block's matrices (`matA`, `matB`), the row weights `e_k = lowWeights[k mod 64] · eq(chi_in)[k / 64]`
(`eRow`) and the column weights `w_j = s[j mod 64] · eq(chi_in')[j / 64]` (`wCol`): the terminal of the lincheck on
the block's R1CS. The walk is only the order of summation (`BlockR1CS.rows_fst`, `rows_snd`).
-/

namespace KeccakFlock.Terminal

open LeanVM.Parameters UniStatement UniStatement.Flock CompPoly Finset

/-! ## Folds as sums -/

theorem foldl_add_eq (l : List E) (a : E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem esum_eq (l : List E) : esum l = l.sum := by
  rw [esum, foldl_add_eq, zero_add]

theorem sum_map_range (f : ℕ → E) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem esum_map_range (f : ℕ → E) (n : ℕ) : esum ((List.range n).map f) = ∑ i ∈ range n, f i := by
  rw [esum_eq, sum_map_range]

/-- A double sum over `h < n` and `l < 64` is the sum over `h · 64 + l < 64 n`. -/
theorem sum_range_mul64 (F : ℕ → E) : ∀ n : ℕ,
    ∑ h ∈ range n, ∑ l ∈ range 64, F (h * 64 + l) = ∑ k ∈ range (n * 64), F k
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_mul64 F n, show (n + 1) * 64 = n * 64 + 64 by ring,
      Finset.sum_range_add]

/-! ## The weights -/

/-- The row weight of position `k`: `lowWeights[k mod 64] · eq(chi_in)[k / 64]`. -/
def eRow (zSkip : Option E) (rowLow chiIn : List E) (k : ℕ) : E :=
  (rowLowWeights zSkip rowLow).2.getD (k % 64) 0 * (eqKernel chiIn).getD (k / 64) 0

/-- The column weight of position `j`: `s[j mod 64] · eq(chi_in')[j / 64]`. -/
def wCol (chiInPrime s : List E) (j : ℕ) : E := s.getD (j % 64) 0 * (eqKernel chiInPrime).getD (j / 64) 0

/-- **The matrices' bilinear form** `Σ_(k, j) e_k (A_kj + α B_kj) w_j`. -/
def bilinear (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E) : E :=
  ∑ k : Pos, ∑ j : Pos, eRow zSkip rowLow chiIn k * ((if matA k j then wCol chiInPrime s j else 0) +
    alpha * (if matB k j then wCol chiInPrime s j else 0))

/-- **The walked terminal is the bilinear form of the block's matrices**, plus the `C = I` claim and the pin. -/
theorem walkedTerminal_eq_bilinear (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E) :
    walkedTerminal zSkip rowLow chiIn chiInPrime s alpha =
      bilinear zSkip rowLow chiIn chiInPrime s alpha +
        alpha * alpha * eqEval chiIn chiInPrime * dot (rowLowWeights zSkip rowLow).2 s +
        alpha * alpha * alpha * eqEval constantBits chiInPrime * s.getD 0 0 := by
  unfold walkedTerminal
  simp only [esum_map_range]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ rfl) rfl
  set w : CMlPolynomialEval E m :=
    (Vector.ofFn fun p : Pos ↦ s.getD (p.val % 64) 0 * (eqKernel chiInPrime).getD (p.val / 64) 0 :
      Vector E (2 ^ m))
  set entry := fun (v : CMlPolynomialEval E m) (i : ℕ) ↦ if h : i < 2 ^ m then v[(⟨i, h⟩ : Fin (2 ^ m))] else 0
  have hw : ∀ j : Pos, w[j] = wCol chiInPrime s j := fun j ↦ by
    simp only [w, wCol, Fin.getElem_fin, Vector.getElem_ofFn]
  -- The matrix part, as a sum over the positions.
  have h1 : ∀ h ∈ range 2048, (eqKernel chiIn).getD h 0 *
      (∑ low ∈ range 64, (rowLowWeights zSkip rowLow).2.getD low 0 * entry (r1cs.rows w).1 (h * 64 + low) +
        alpha * ∑ low ∈ range 64, (rowLowWeights zSkip rowLow).2.getD low 0 * entry (r1cs.rows w).2 (h * 64 + low)) =
      ∑ low ∈ range 64, eRow zSkip rowLow chiIn (h * 64 + low) *
        (entry (r1cs.rows w).1 (h * 64 + low) + alpha * entry (r1cs.rows w).2 (h * 64 + low)) := by
    intro h _
    rw [Finset.mul_sum (a := alpha), ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun low hlow ↦ ?_
    rw [Finset.mem_range] at hlow
    simp only [eRow, show (h * 64 + low) % 64 = low by omega, show (h * 64 + low) / 64 = h by omega]
    ring
  rw [Finset.sum_congr rfl h1, sum_range_mul64 (fun k ↦ eRow zSkip rowLow chiIn k *
    (entry (r1cs.rows w).1 k + alpha * entry (r1cs.rows w).2 k)) 2048,
    show 2048 * 64 = 2 ^ m from rfl, ← Fin.sum_univ_eq_sum_range]
  unfold bilinear
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [entry, k.isLt, dite_true, Fin.eta, Lv42.Protocol.BlockR1CS.rows_fst,
    Lv42.Protocol.BlockR1CS.rows_snd]
  rw [Finset.mul_sum (a := alpha), ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change _ * ((if matA k j then w[j] else 0) + alpha * (if matB k j then w[j] else 0)) = _
  rw [hw j]

end KeccakFlock.Terminal
