-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The end is `formal/KeccakFlock`'s
-- `KeccakFlock.Core.structuredTerminal_eq_bilinear` (`TerminalMain.lean`) and `formal/UniKeccakSound`'s
-- `UniKeccakSound.KF.Br.structuredTerminal_eq` (`Flock/Bridge.lean`).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/FlockProverSumPure.lean`.
import UniKeccakComplete.K.FlockProverSumBasic
import KeccakFlock.TerminalMain
import UniKeccakSound.Flock.Bridge

/-!
# The lincheck's terminal is the structured terminal, given the lincheck's last claim

**`terminal_pure`**: if the lincheck's last claim `r_lc` is `Σ_y W'_y s_y` (the weights `W` folded, high variable
first, by its round challenges, `s` the slices), then the verifier's check vanishes:
`structuredTerminal zSkip row_low chi_in chi_in' s α + r_lc = 0`, `chi_in' = rounds.reverse`.

The weights are `W = Aᵀe + α Bᵀe + α² e + α³ [· = 64]` (`W_getD`), so with the column weights
`w(j) = s[j mod 64] eq(chi_in', j / 64)` (`KeccakFlock.Terminal.wCol`), `r_lc = Σ_j w(j) W(j)` (`rLc_sum`) is
the matrices' bilinear form `Σ_(k, j) e_k (A + α B)_kj w_j` (`bilinear_eq`) plus `α² eq(chi_in, chi_in') ⟨e_low, s⟩`
plus `α³ eq(word 1, chi_in') s_0` (`terminal_sum`): exactly `structuredTerminal`'s value
(`structuredTerminal_eq_bilinear`, through UniKeccakSound's bridge between the two transcriptions). In
characteristic two the sum of two equal values is zero.
-/

namespace UniKeccakComplete.FlockP

open UniComplete

open UniStatement UniStatement.Flock LeanVM.Parameters Finset
open LeanVM.Protocol.EndToEnd (boolPoint)

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## The verifier's helpers -/

theorem udot_gen : ∀ (L : List (E × E)) (c : E),
    L.foldl (fun acc (x, y) ↦ acc + x * y) c = c + L.foldl (fun acc (x, y) ↦ acc + x * y) 0
  | [], c => by simp
  | (u, v) :: L, c => by
    simp only [List.foldl_cons]
    rw [udot_gen L (c + u * v), udot_gen L (0 + u * v)]
    ring

/-- **`dot` is the sum of products.** -/
theorem dot_eq : ∀ (l r : List E), l.length = r.length →
    UniStatement.dot l r = ∑ i ∈ range l.length, l.getD i 0 * r.getD i 0
  | [], _, _ => by simp [UniStatement.dot]
  | _ :: _, [], h => absurd h (by simp)
  | x :: l, z :: r, h => by
    have hl : l.length = r.length := by simpa using h
    unfold UniStatement.dot
    rw [List.zip_cons_cons, List.foldl_cons, udot_gen, List.length_cons, sum_range_succ']
    have ih := dot_eq l r hl
    unfold UniStatement.dot at ih
    rw [ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero, zero_add]
    ring

/-! ## The weights -/

/-- **The lincheck's weights** at a position: `(Aᵀe)_j + α (Bᵀe)_j + α² e_j + α³ [j = 64]`. -/
theorem W_getD (lowW chiIn : List E) (α : E) {j : ℕ} (hj : j < 2 ^ 17) :
    (lincheckWeights (rowWeightsOf lowW chiIn) α).getD j 0 =
      (∑ row ∈ range (2 ^ 17), matE true row j * rowW lowW chiIn row) +
        α * (∑ row ∈ range (2 ^ 17), matE false row j * rowW lowW chiIn row) +
        epow α 2 * rowW lowW chiIn j + (if j = 64 then epow α 3 else 0) := by
  have hj' : j < 2 ^ keccakR1csLogSize := hj
  rw [lincheckWeights, E2ECompleteness.getD_ofFn' _ hj']
  simp only
  rw [cols_fst_getD _ hj, cols_snd_getD _ hj, rowWeightsOf_getD _ _ hj]
  have e1 : ∀ left, ∑ row ∈ range (2 ^ 17), matE left row j * (rowWeightsOf lowW chiIn).toArray.getD row 0 =
      ∑ row ∈ range (2 ^ 17), matE left row j * rowW lowW chiIn row := fun left ↦
    sum_congr rfl fun row hr ↦ by rw [rowWeightsOf_getD _ _ (mem_range.mp hr)]
  rw [e1 true, e1 false]
  rfl

/-- `e(y + 64 h) = lowW[y] eq(chi_in, h)`. -/
theorem rowW_high (lowW chiIn : List E) (hin : chiIn.length = 11) {y h : ℕ} (hy : y < 64) (hh : h < 2 ^ 11) :
    rowW lowW chiIn (y + 2 ^ 6 * h) = lowW.getD y 0 * eqB chiIn h := by
  unfold rowW
  have e1 : (y + 2 ^ 6 * h) % 64 = y := by
    rw [show (64 : ℕ) = 2 ^ 6 by rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simpa using hy)]
  have e2 : (y + 2 ^ 6 * h) / 64 = h := by
    rw [show (64 : ℕ) = 2 ^ 6 by rfl, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (by simpa using hy),
      zero_add]
  rw [e1, e2, eqKernel_getD _ (by rw [hin]; exact hh)]

/-- `w(y + 64 h) = s[y] eq(chi_in', h)`. -/
theorem wCol_high (cip s : List E) (hcip : cip.length = 11) {y h : ℕ} (hy : y < 64) (hh : h < 2 ^ 11) :
    KeccakFlock.Terminal.wCol cip s (y + 2 ^ 6 * h) = s.getD y 0 * eqB cip h := by
  unfold KeccakFlock.Terminal.wCol
  have e1 : (y + 2 ^ 6 * h) % 64 = y := by
    rw [show (64 : ℕ) = 2 ^ 6 by rfl, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by simpa using hy)]
  have e2 : (y + 2 ^ 6 * h) / 64 = h := by
    rw [show (64 : ℕ) = 2 ^ 6 by rfl, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (by simpa using hy),
      zero_add]
  rw [e1, e2, eqKernel_getD _ (by rw [hcip]; exact hh)]

/-- The low weights have `64` entries. -/
theorem lowW_length (zSkip : Option E) (low : List E) (k : ℕ) (hk : k ≤ 6)
    (hskip : (rowLowWeights zSkip low).1.length = 2 ^ k) (hlow : low.length = 6 - k) :
    (rowLowWeights zSkip low).2.length = 64 := by
  show ((eqKernel low).toList.flatMap fun a ↦ (rowLowWeights zSkip low).1.map fun l ↦ l * a).length = 64
  rw [List.length_flatMap]
  simp only [List.length_map, hskip, List.map_const', List.sum_replicate, Array.length_toList, eqKernel_size,
    hlow, smul_eq_mul]
  rw [← pow_add, show 6 - k + k = 6 by omega]
  rfl

/-! ## The last claim as a sum over the positions -/

/-- **The lincheck's last claim** `Σ_y W'_y s_y` is `Σ_j w(j) W(j)`, `w` the column weights at
`chi_in' = rounds.reverse`. -/
theorem rLc_sum (lowW chiIn χs s : List E) (α : E) (hχ : χs.length = 11) :
    ∑ y ∈ range 64, (χs.foldl foldHigh (lincheckWeights (rowWeightsOf lowW chiIn) α)).getD y 0 * s.getD y 0 =
      ∑ j ∈ range (2 ^ 17), KeccakFlock.Terminal.wCol χs.reverse s j *
        (lincheckWeights (rowWeightsOf lowW chiIn) α).getD j 0 := by
  have hWsize : (lincheckWeights (rowWeightsOf lowW chiIn) α).size = 2 ^ (χs.length + 6) := by
    simp [lincheckWeights, hχ, keccakR1csLogSize]
  have hcip : χs.reverse.length = 11 := by rw [List.length_reverse, hχ]
  rw [show (2 : ℕ) ^ 17 = 2 ^ (6 + 11) from rfl, sum_split 6 11, show (64 : ℕ) = 2 ^ 6 from rfl]
  rw [sum_congr rfl fun y hy ↦ by rw [foldl_foldHigh_getD χs 6 _ hWsize y (mem_range.mp hy)]]
  simp only [hχ, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun h hh ↦ sum_congr rfl fun y hy ↦ ?_
  rw [wCol_high χs.reverse s hcip (by simpa using mem_range.mp hy) (mem_range.mp hh)]
  ring

/-- **`Σ_j w(j) W(j)`**: the bilinear part, `α² eq(chi_in, chi_in') ⟨e_low, s⟩`, `α³ s_0 eq(chi_in', word 1)`. -/
theorem terminal_sum (lowW chiIn cip s : List E) (α : E) (hin : chiIn.length = 11) (hcip : cip.length = 11) :
    ∑ j ∈ range (2 ^ 17), KeccakFlock.Terminal.wCol cip s j * (lincheckWeights (rowWeightsOf lowW chiIn) α).getD j 0 =
      (∑ k ∈ range (2 ^ 17), ∑ j ∈ range (2 ^ 17), rowW lowW chiIn k *
          (matE true k j * KeccakFlock.Terminal.wCol cip s j +
            α * (matE false k j * KeccakFlock.Terminal.wCol cip s j))) +
        epow α 2 * (LeanVM.Protocol.Verifier.eqEval chiIn cip * ∑ y ∈ range 64, lowW.getD y 0 * s.getD y 0) +
        epow α 3 * (s.getD 0 0 * (eqKernel cip).getD 1 0) := by
  set wc := KeccakFlock.Terminal.wCol cip s with hwc
  have hterm : ∀ j ∈ range (2 ^ 17), wc j * (lincheckWeights (rowWeightsOf lowW chiIn) α).getD j 0 =
      (∑ k ∈ range (2 ^ 17), rowW lowW chiIn k * (matE true k j * wc j + α * (matE false k j * wc j))) +
        epow α 2 * (wc j * rowW lowW chiIn j) + wc j * (if j = 64 then epow α 3 else 0) := by
    intro j hj
    rw [W_getD lowW chiIn α (mem_range.mp hj)]
    have hA : wc j * ((∑ row ∈ range (2 ^ 17), matE true row j * rowW lowW chiIn row) +
        α * (∑ row ∈ range (2 ^ 17), matE false row j * rowW lowW chiIn row)) =
        ∑ k ∈ range (2 ^ 17), rowW lowW chiIn k * (matE true k j * wc j + α * (matE false k j * wc j)) := by
      rw [mul_add, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun k _ ↦ by ring
    rw [← hA]
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib, sum_comm (f := fun j k ↦ rowW lowW chiIn k *
    (matE true k j * wc j + α * (matE false k j * wc j))), ← mul_sum]
  have hpin : ∑ j ∈ range (2 ^ 17), wc j * (if j = 64 then epow α 3 else 0) = epow α 3 * (s.getD 0 0 *
      (eqKernel cip).getD 1 0) := by
    simp only [mul_ite, mul_zero]
    rw [sum_ite_eq' (range (2 ^ 17)) 64, if_pos (by simp), hwc]
    unfold KeccakFlock.Terminal.wCol
    rw [show (64 : ℕ) % 64 = 0 from rfl, show (64 : ℕ) / 64 = 1 from rfl]
    ring
  have hdiag : ∑ j ∈ range (2 ^ 17), wc j * rowW lowW chiIn j =
      LeanVM.Protocol.Verifier.eqEval chiIn cip * ∑ y ∈ range 64, lowW.getD y 0 * s.getD y 0 := by
    rw [show (2 : ℕ) ^ 17 = 2 ^ (6 + 11) from rfl, sum_split 6 11, ← sum_eqB_mul_eqB cip chiIn (by rw [hcip, hin]),
      hcip, sum_mul]
    refine sum_congr rfl fun h hh ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun y hy ↦ ?_
    have hy' : y < 64 := by simpa using mem_range.mp hy
    rw [hwc, wCol_high cip s hcip hy' (mem_range.mp hh), rowW_high lowW chiIn hin hy' (mem_range.mp hh)]
    ring
  rw [hpin, hdiag]

/-! ## The bilinear form -/

/-- **KeccakFlock's bilinear form** in the code's numbers: the matrices' entries `matE`, the row weights `rowW`. -/
theorem bilinear_eq (zSkip : Option E) (low chiIn cip s : List E) (α : E) :
    KeccakFlock.Terminal.bilinear zSkip low chiIn cip s α =
      ∑ k ∈ range (2 ^ 17), ∑ j ∈ range (2 ^ 17), rowW (rowLowWeights zSkip low).2 chiIn k *
        (matE true k j * KeccakFlock.Terminal.wCol cip s j +
          α * (matE false k j * KeccakFlock.Terminal.wCol cip s j)) := by
  unfold KeccakFlock.Terminal.bilinear
  rw [show (2 : ℕ) ^ 17 = 2 ^ KeccakFlock.m from rfl, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hA : matE true k j = if KeccakFlock.matA k j then 1 else 0 := by
    unfold matE
    rw [dif_pos ⟨k.isLt, j.isLt⟩]
    rfl
  have hB : matE false k j = if KeccakFlock.matB k j then 1 else 0 := by
    unfold matE
    rw [dif_pos ⟨k.isLt, j.isLt⟩]
    rfl
  rw [hA, hB]
  simp only [ite_mul, one_mul, zero_mul]
  rfl

/-! ## The terminal -/

/-- **The lincheck's terminal check vanishes**, purely: given the lincheck's last claim `Σ_y W'_y s_y`, the verifier's
`structuredTerminal zSkip row_low chi_in chi_in' s α + r_lc` is zero (`chi_in' = rounds.reverse`). -/
theorem terminal_pure (k : ℕ) (hk : k ≤ 6) (zSkip : Option E) (low chiIn χs : List E) (α rLc : E) (s : List E)
    (hskip : (rowLowWeights zSkip low).1.length = 2 ^ k) (hlow : low.length = 6 - k) (hin : chiIn.length = 11)
    (hχ : χs.length = 11) (hs : s.length = 64)
    (hrLc : rLc = ∑ y ∈ range 64,
      (χs.foldl foldHigh (lincheckWeights (rowWeightsOf (rowLowWeights zSkip low).2 chiIn) α)).getD y 0 *
        s.getD y 0) :
    UniKeccak.structuredTerminal zSkip low chiIn χs.reverse s α + rLc = 0 := by
  set lowW := (rowLowWeights zSkip low).2 with hlowW
  have hcip : χs.reverse.length = 11 := by rw [List.length_reverse, hχ]
  have hrl : low.length ≤ 6 := by omega
  have hz : zSkip = none → low.length = 6 := by
    intro h
    subst h
    have h1 : (1 : ℕ) = 2 ^ k := hskip
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · omega
    · have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h0
      omega
  have hlw : lowW.length = 64 := lowW_length zSkip low k hk hskip hlow
  rw [UniKeccakSound.KF.Br.structuredTerminal_eq,
    KeccakFlock.Core.structuredTerminal_eq_bilinear zSkip low chiIn χs.reverse s α hrl hz hin hcip,
    KeccakFlock.Core.eqEval_constantBits _ hcip, hrLc, rLc_sum lowW chiIn χs s α hχ,
    terminal_sum lowW chiIn χs.reverse s α hin hcip, ← bilinear_eq zSkip low chiIn χs.reverse s α,
    dot_eq lowW s (by rw [hlw, hs]), hlw, eqEval_eq, Tower.epow_eq, Tower.epow_eq]
  linear_combination (KeccakFlock.Terminal.bilinear zSkip low chiIn χs.reverse s α +
    α ^ 2 * (LeanVM.Protocol.Verifier.eqEval chiIn χs.reverse * ∑ y ∈ range 64, lowW.getD y 0 * s.getD y 0) +
    α ^ 3 * (s.getD 0 0 * (eqKernel χs.reverse).getD 1 0)) * two_eq_zero_E

end UniKeccakComplete.FlockP
