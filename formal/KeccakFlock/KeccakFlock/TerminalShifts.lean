-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import KeccakFlock.TerminalStruct

/-!
# The structured terminal's shifts, matched to the walked form

`shifts_eq`: `Σ_(off needed) g[off] Corr[off]` is the walked form's `b` terms
`Σ_(j, l) ρ(t_j[l]) (bz(x+1) + α bz(x+2)) + ρ(A_j[l]) bz(l)`:

* the offsets: each `b` lane `i` puts its two coefficients at `rot_i` and `rot_i + 1`, both needed
  (`sum_shifts`);
* the lanes: the rows reading `b[i]` are the `t` rows of lanes `x − 1` (left) and `x − 2` (right, times `α`) and the
  `A` row of lane `i` (`reindex1`, `reindex2`: the lane maps are bijections of the 25 lanes);
* the rounds: rounds `1..22` share the round factor `Σ rd[j+2] rh[j+1]`, round 0 reads the port `C` words, round 23
  writes the port `X` words (`laneA_eq`, `laneB_eq`).
-/

namespace KeccakFlock.Core

open LeanVM.Parameters PcsCircuit PcsCircuit.Builder Finset KeccakFlock.Terminal UniStatement

theorem source_getD : ∀ i < 25, source.getD i (0, 0) = (piInv i, rho (piInv i)) := by decide

theorem needed_rot : ∀ i < 25, needed (rho (piInv i)) = true ∧ needed (rho (piInv i) + 1) = true := by decide

theorem rhoTable_le : ∀ r ∈ rhoTable, r ≤ 62 := by decide

theorem needed_lt {off : ℕ} (h : needed off = true) : off < 64 := by
  obtain ⟨r, hr, h⟩ := List.any_eq_true.mp h
  have := rhoTable_le r hr
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  omega

section Lanes

variable (lr rd lh rh : ℕ → E) (kr5 kh5 α : E)

/-- The coefficient of `Corr[rot_i]`. -/
def laneA (i : ℕ) : E :=
  laneV lr rd rh kr5 kh5 α i * (lh (piInv i) + colSum lh ((piInv i % 5 + 4) % 5)) +
    rd 2 * laneU lr kr5 α i * (portW lh rh kh5 (piInv i) 2 + colSum (fun q ↦ portW lh rh kh5 q 2) ((piInv i % 5 + 4) % 5))

/-- The coefficient of `Corr[rot_i + 1]`. -/
def laneB (i : ℕ) : E :=
  laneV lr rd rh kr5 kh5 α i * colSum lh ((piInv i % 5 + 1) % 5) +
    rd 2 * laneU lr kr5 α i * colSum (fun q ↦ portW lh rh kh5 q 2) ((piInv i % 5 + 1) % 5)

theorem laneTerms_eq {i : ℕ} (hi : i < 25) :
    laneTerms lr rd lh rh kr5 kh5 α i =
      (rho (piInv i), laneA lr rd lh rh kr5 kh5 α i, rho (piInv i) + 1, laneB lr rd lh rh kr5 kh5 α i) := by
  have hr := rho_le i hi
  simp only [laneTerms, source_getD i hi, Nat.mod_eq_of_lt (show rho (piInv i) + 1 < 64 by omega), laneA, laneB]

/-- **The offsets**: the shifts are the lanes' two coefficients against their correlations. -/
theorem sum_shifts (c : ℕ → E) (hc : ∀ off, needed off = false → c off = 0) :
    shifts c lr rd lh rh kr5 kh5 α = ∑ i ∈ range 25, (laneA lr rd lh rh kr5 kh5 α i * c (rho (piInv i)) +
      laneB lr rd lh rh kr5 kh5 α i * c (rho (piInv i) + 1)) := by
  rw [shifts, esum_filter, esum_map_range]
  have h1 : ∀ off ∈ range 64, (if needed off then gAt lr rd lh rh kr5 kh5 α off * c off else 0) =
      gAt lr rd lh rh kr5 kh5 α off * c off := fun off _ ↦ by
    cases h : needed off
    · rw [hc off h, mul_zero]; rfl
    · rfl
  have hg : ∀ off, gAt lr rd lh rh kr5 kh5 α off = ∑ i ∈ range 25,
      ((if rho (piInv i) = off then laneA lr rd lh rh kr5 kh5 α i else 0) +
        (if rho (piInv i) + 1 = off then laneB lr rd lh rh kr5 kh5 α i else 0)) := fun off ↦ by
    rw [gAt, esum_map_range]
    exact Finset.sum_congr rfl fun i hi ↦ by rw [laneTerms_eq lr rd lh rh kr5 kh5 α (mem_range.mp hi)]
  rw [Finset.sum_congr rfl h1]
  simp only [hg, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi := mem_range.mp hi
  have hr := rho_le i hi
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, mem_range,
    show rho (piInv i) < 64 by omega, show rho (piInv i) + 1 < 64 by omega, ite_true]

/-- The rows reading `b[i]` in round `j`: the `t` rows of lanes `x − 1` (left) and `x − 2` (right, times `α`), the
`A` row of lane `i`. -/
def laneR (j i : ℕ) : E :=
  wordW lr rd kr5 (tWord j ((i % 5 + 4) % 5 + 5 * (i / 5))) + α * wordW lr rd kr5 (tWord j ((i % 5 + 3) % 5 + 5 * (i / 5))) +
    wordW lr rd kr5 (stWord (j + 1) i)

theorem laneR_mid {j i : ℕ} (hj : j < 23) (hi : i < 25) : laneR lr rd kr5 α j i = rd (j + 2) * laneU lr kr5 α i := by
  unfold laneR laneU
  rw [wordW_t _ _ _ (by omega), wordW_t _ _ _ (by omega), stWord_succ hj, wordW_a _ _ _ (by omega)]
  simp only [kindW, ite_true, show (1 : ℕ) ≠ 0 by decide, ite_false]
  ring

theorem laneR_last {i : ℕ} (hi : i < 25) : laneR lr rd kr5 α 23 i = laneLast lr rd kr5 α i := by
  unfold laneR laneLast
  rw [wordW_t _ _ _ (by omega), wordW_t _ _ _ (by omega), stWord_24, wordW_port _ _ _ (by decide)]
  ring

theorem colSum_five (f : ℕ → E) (x : ℕ) : colSum f x = f x + f (x + 5) + f (x + 10) + f (x + 15) + f (x + 20) := by
  rw [colSum_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.mul_zero, Nat.add_zero, Nat.mul_one,
    show 5 * 2 = 10 from rfl, show 5 * 3 = 15 from rfl, show 5 * 4 = 20 from rfl]

theorem gamL_zero (i : ℕ) : gamL (wordW lh rh kh5) 0 i =
    portW lh rh kh5 (piInv i) 2 + colSum (fun q ↦ portW lh rh kh5 q 2) ((piInv i % 5 + 4) % 5) := by
  unfold gamL colG
  simp only [stWord_0, wordW_port lh rh kh5 (show 2 < 4 by decide), colSum_five]

theorem gamR_zero (i : ℕ) : gamR (wordW lh rh kh5) 0 i =
    colSum (fun q ↦ portW lh rh kh5 q 2) ((piInv i % 5 + 1) % 5) := by
  unfold gamR colG
  simp only [stWord_0, wordW_port lh rh kh5 (show 2 < 4 by decide), colSum_five]

theorem gamL_succ {j i : ℕ} (hj : j < 23) (hi : i < 25) : gamL (wordW lh rh kh5) (j + 1) i =
    kindW kh5 1 * rh (j + 2) * (lh (piInv i) + colSum lh ((piInv i % 5 + 4) % 5)) := by
  have hp := piInv_lt i hi
  have hA : ∀ l < 25, wordW lh rh kh5 (stWord (j + 1) l) = lh l * kindW kh5 1 * rh (j + 2) := fun l hl ↦ by
    rw [stWord_succ hj, wordW_a _ _ _ (by omega)]
  unfold gamL colG
  rw [hA _ hp, hA ((piInv i % 5 + 4) % 5) (by omega), hA ((piInv i % 5 + 4) % 5 + 5) (by omega),
    hA ((piInv i % 5 + 4) % 5 + 10) (by omega), hA ((piInv i % 5 + 4) % 5 + 15) (by omega),
    hA ((piInv i % 5 + 4) % 5 + 20) (by omega), colSum_five]
  ring

theorem gamR_succ {j : ℕ} (i : ℕ) (hj : j < 23) : gamR (wordW lh rh kh5) (j + 1) i =
    kindW kh5 1 * rh (j + 2) * colSum lh ((piInv i % 5 + 1) % 5) := by
  have hA : ∀ l < 25, wordW lh rh kh5 (stWord (j + 1) l) = lh l * kindW kh5 1 * rh (j + 2) := fun l hl ↦ by
    rw [stWord_succ hj, wordW_a _ _ _ (by omega)]
  unfold gamR colG
  rw [hA ((piInv i % 5 + 1) % 5) (by omega), hA ((piInv i % 5 + 1) % 5 + 5) (by omega),
    hA ((piInv i % 5 + 1) % 5 + 10) (by omega), hA ((piInv i % 5 + 1) % 5 + 15) (by omega),
    hA ((piInv i % 5 + 1) % 5 + 20) (by omega), colSum_five]
  ring

/-- Splitting the rounds: round 0, rounds `1..22`, round 23. -/
theorem sum_rounds (f : ℕ → E) : ∑ j ∈ range 24, f j = f 0 + ∑ j ∈ range 22, f (j + 1) + f 23 := by
  rw [Finset.sum_range_succ f 23, Finset.sum_range_succ' f 22]
  ring

/-- **Lane `i`'s coefficient of `Corr[rot_i]`** is its rows' weights against the columns `b[i]` reads at
`z − rot_i`, over the 24 rounds. -/
theorem laneA_eq {i : ℕ} (hi : i < 25) : laneA lr rd lh rh kr5 kh5 α i =
    ∑ j ∈ range 24, laneR lr rd kr5 α j i * gamL (wordW lh rh kh5) j i := by
  have hmid : ∑ j ∈ range 22, laneR lr rd kr5 α (j + 1) i * gamL (wordW lh rh kh5) (j + 1) i =
      sumRange 1 23 (fun j ↦ rd (j + 2) * rh (j + 1)) *
        (kindW kh5 1 * laneU lr kr5 α i * (lh (piInv i) + colSum lh ((piInv i % 5 + 4) % 5))) := by
    rw [sumRange_eq, show 23 - 1 = 22 from rfl, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj := mem_range.mp hj
    rw [laneR_mid lr rd kr5 α (by omega) hi, gamL_succ lh rh kh5 (by omega) hi,
      show 1 + j + 2 = j + 1 + 2 by ring, show 1 + j + 1 = j + 2 by ring]
    ring
  have h0 : laneR lr rd kr5 α 0 i * gamL (wordW lh rh kh5) 0 i = rd 2 * laneU lr kr5 α i *
      (portW lh rh kh5 (piInv i) 2 + colSum (fun q ↦ portW lh rh kh5 q 2) ((piInv i % 5 + 4) % 5)) := by
    rw [laneR_mid lr rd kr5 α (by decide) hi, gamL_zero lh rh kh5 i]
  have h23 : laneR lr rd kr5 α 23 i * gamL (wordW lh rh kh5) 23 i = laneLast lr rd kr5 α i *
      (kindW kh5 1 * rh 24 * (lh (piInv i) + colSum lh ((piInv i % 5 + 4) % 5))) := by
    rw [laneR_last lr rd kr5 α hi]
    exact congrArg (laneLast lr rd kr5 α i * ·) (gamL_succ lh rh kh5 (j := 22) (by decide) hi)
  rw [sum_rounds, hmid, h0, h23, laneA, laneV]
  ring

/-- **Lane `i`'s coefficient of `Corr[rot_i + 1]`.** -/
theorem laneB_eq {i : ℕ} (hi : i < 25) : laneB lr rd lh rh kr5 kh5 α i =
    ∑ j ∈ range 24, laneR lr rd kr5 α j i * gamR (wordW lh rh kh5) j i := by
  have hmid : ∑ j ∈ range 22, laneR lr rd kr5 α (j + 1) i * gamR (wordW lh rh kh5) (j + 1) i =
      sumRange 1 23 (fun j ↦ rd (j + 2) * rh (j + 1)) *
        (kindW kh5 1 * laneU lr kr5 α i * colSum lh ((piInv i % 5 + 1) % 5)) := by
    rw [sumRange_eq, show 23 - 1 = 22 from rfl, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj := mem_range.mp hj
    rw [laneR_mid lr rd kr5 α (by omega) hi, gamR_succ lh rh kh5 i (by omega),
      show 1 + j + 2 = j + 1 + 2 by ring, show 1 + j + 1 = j + 2 by ring]
    ring
  have h0 : laneR lr rd kr5 α 0 i * gamR (wordW lh rh kh5) 0 i = rd 2 * laneU lr kr5 α i *
      colSum (fun q ↦ portW lh rh kh5 q 2) ((piInv i % 5 + 1) % 5) := by
    rw [laneR_mid lr rd kr5 α (by decide) hi, gamR_zero lh rh kh5 i]
  have h23 : laneR lr rd kr5 α 23 i * gamR (wordW lh rh kh5) 23 i = laneLast lr rd kr5 α i *
      (kindW kh5 1 * rh 24 * colSum lh ((piInv i % 5 + 1) % 5)) := by
    rw [laneR_last lr rd kr5 α hi]
    exact congrArg (laneLast lr rd kr5 α i * ·) (gamR_succ lh rh kh5 (j := 22) i (by decide))
  rw [sum_rounds, hmid, h0, h23, laneB, laneV]
  ring

/-- The `t` rows reading `b[x+1]` on the left, by `b` lane: lane `l ↦ x + 1` is a bijection with inverse
`i ↦ x − 1`. -/
theorem reindex1 (F : ℕ → ℕ → E) : ∑ l ∈ range 25, F l ((l % 5 + 1) % 5 + 5 * (l / 5)) =
    ∑ i ∈ range 25, F ((i % 5 + 4) % 5 + 5 * (i / 5)) i :=
  Finset.sum_nbij' (fun l ↦ (l % 5 + 1) % 5 + 5 * (l / 5)) (fun i ↦ (i % 5 + 4) % 5 + 5 * (i / 5))
    (fun l hl ↦ by simp only [mem_range] at hl ⊢; omega) (fun i hi ↦ by simp only [mem_range] at hi ⊢; omega)
    (fun l hl ↦ by simp only [mem_range] at hl; omega) (fun i hi ↦ by simp only [mem_range] at hi; omega)
    (fun l hl ↦ by
      simp only [mem_range] at hl
      rw [show ((l % 5 + 1) % 5 + 5 * (l / 5)) % 5 = (l % 5 + 1) % 5 by omega,
        show ((l % 5 + 1) % 5 + 5 * (l / 5)) / 5 = l / 5 by omega,
        show ((l % 5 + 1) % 5 + 4) % 5 + 5 * (l / 5) = l by omega])

/-- The `t` rows reading `b[x+2]` on the right, by `b` lane. -/
theorem reindex2 (F : ℕ → ℕ → E) : ∑ l ∈ range 25, F l ((l % 5 + 2) % 5 + 5 * (l / 5)) =
    ∑ i ∈ range 25, F ((i % 5 + 3) % 5 + 5 * (i / 5)) i :=
  Finset.sum_nbij' (fun l ↦ (l % 5 + 2) % 5 + 5 * (l / 5)) (fun i ↦ (i % 5 + 3) % 5 + 5 * (i / 5))
    (fun l hl ↦ by simp only [mem_range] at hl ⊢; omega) (fun i hi ↦ by simp only [mem_range] at hi ⊢; omega)
    (fun l hl ↦ by simp only [mem_range] at hl; omega) (fun i hi ↦ by simp only [mem_range] at hi; omega)
    (fun l hl ↦ by
      simp only [mem_range] at hl
      rw [show ((l % 5 + 2) % 5 + 5 * (l / 5)) % 5 = (l % 5 + 2) % 5 by omega,
        show ((l % 5 + 2) % 5 + 5 * (l / 5)) / 5 = l / 5 by omega,
        show ((l % 5 + 2) % 5 + 3) % 5 + 5 * (l / 5) = l by omega])

end Lanes

/-- **The shifts are the walked form's `b` terms.** -/
theorem shifts_eq (Ew sv lr rd lh rh : ℕ → E) (kr5 kh5 α : E) :
    shifts (fun off ↦ if needed off then corr Ew sv off else 0) lr rd lh rh kr5 kh5 α =
      ∑ j ∈ range 24, ∑ l ∈ range 25, (wordW lr rd kr5 (tWord j l) *
        (bz Ew sv (wordW lh rh kh5) j ((l % 5 + 1) % 5 + 5 * (l / 5)) +
          α * bz Ew sv (wordW lh rh kh5) j ((l % 5 + 2) % 5 + 5 * (l / 5))) +
        wordW lr rd kr5 (stWord (j + 1) l) * bz Ew sv (wordW lh rh kh5) j l) := by
  set γ := wordW lh rh kh5
  rw [sum_shifts lr rd lh rh kr5 kh5 α _ fun off h ↦ by rw [h]; rfl]
  have hj : ∀ j, ∑ l ∈ range 25, (wordW lr rd kr5 (tWord j l) *
      (bz Ew sv γ j ((l % 5 + 1) % 5 + 5 * (l / 5)) + α * bz Ew sv γ j ((l % 5 + 2) % 5 + 5 * (l / 5))) +
        wordW lr rd kr5 (stWord (j + 1) l) * bz Ew sv γ j l) =
      ∑ i ∈ range 25, laneR lr rd kr5 α j i * bz Ew sv γ j i := fun j ↦ by
    simp only [mul_add, Finset.sum_add_distrib]
    rw [reindex1 (fun l i ↦ wordW lr rd kr5 (tWord j l) * bz Ew sv γ j i),
      reindex2 (fun l i ↦ wordW lr rd kr5 (tWord j l) * (α * bz Ew sv γ j i)), ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by unfold laneR; ring
  rw [Finset.sum_congr rfl fun j _ ↦ hj j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi := mem_range.mp hi
  rw [ite_eq_left (needed_rot i hi).1, ite_eq_left (needed_rot i hi).2, laneA_eq lr rd lh rh kr5 kh5 α hi,
    laneB_eq lr rd lh rh kr5 kh5 α hi, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by unfold bz; ring

end KeccakFlock.Core
