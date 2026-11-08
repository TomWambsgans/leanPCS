-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import KeccakFlock.TerminalFront

/-!
# The structured terminal is the walked terminal

**`structuredTerminal_eq_walked`**: under the Rust's assertions (`row_low` of at most 6, a skip point whenever the skip
has bits, `chi_in` and `chi_in'` of 11, `s` of 64), `Terminal.structuredTerminal` (`keccak_flock.rs::structured_terminal`)
equals `Terminal.walkedTerminal` (`walked_terminal_with::<_, KeccakWalked>` on the specification's walk), hence
(`walkedTerminal_eq_bilinear`) the bilinear form of the block's matrices plus the `C = I` claim and the pin.

The inputs: the packing weights split at `p = max(k, 3)` are `rowLowWeights` (`packingAt_eq`: the tensor product of
the skip's Lagrange weights and the eq table of `row_low`, the eq table of a concatenation the tensor product of the
tables); they sum to 1 (`packing_sum`: an eq table does, and the Lagrange weights at distinct nodes do,
`lagrangeWeights_sum`); the correlations through partial correlations are the direct ones (`correlation_eq`); the eq
tables of `chi_in`, `chi_in'` factor into lane, kind and round (`eqKernel_factor`).
-/

namespace KeccakFlock.Core

open LeanVM.Parameters PcsCircuit PcsCircuit.Builder Finset KeccakFlock.Terminal UniStatement UniStatement.Flock

/-! ## Lagrange weights sum to 1 -/

theorem lagrangeWeights_sum {k : ℕ} (hk : k ≤ 6) (z : E) :
    ∑ i ∈ range (2 ^ k), (lagrangeWeights (2 ^ k) z).getD i 0 = 1 := by
  have hN : 2 ^ k ≤ 64 := by
    calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hk
      _ = 64 := rfl
  have hinj : Set.InjOn (fun j ↦ phi j) (range (2 ^ k) : Set ℕ) := fun a ha b hb h ↦
    FlockSound.Uni.phi_injOn (by simp at ha; omega) (by simp at hb; omega) h
  have hb : ∀ i ∈ range (2 ^ k), (lagrangeWeights (2 ^ k) z).getD i 0 =
      (Lagrange.basis (range (2 ^ k)) (fun j ↦ phi j) i).eval z := fun i hi ↦ by
    rw [FlockSound.Uni.lagrangeWeights_getD (mem_range.mp hi), Lagrange.basis, Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    simp [Lagrange.basisDivisor]
  rw [Finset.sum_congr rfl hb, ← Polynomial.eval_finsetSum, Lagrange.sum_basis hinj ⟨0, by simp⟩,
    Polynomial.eval_one]

/-! ## Lists -/

theorem getD_flatMap_mul (S : List E) (hS : 0 < S.length) : ∀ (L : List E) (z : ℕ),
    (L.flatMap fun m ↦ S.map (· * m)).getD z 0 = S.getD (z % S.length) 0 * L.getD (z / S.length) 0
  | [], z => by simp
  | m :: L, z => by
    rw [List.flatMap_cons]
    by_cases hz : z < S.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hz), Nat.mod_eq_of_lt hz,
        Nat.div_eq_of_lt hz]
      simp [List.getD_eq_getElem?_getD, hz]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using hz), ← List.getD_eq_getElem?_getD,
        List.length_map, getD_flatMap_mul S hS L (z - S.length),
        show z / S.length = (z - S.length) / S.length + 1 by
          rw [Nat.div_eq_sub_div hS (by omega)],
        show z % S.length = (z - S.length) % S.length by rw [Nat.mod_eq_sub_mod (by omega)]]
      rfl

theorem length_flatMap_mul (S L : List E) : (L.flatMap fun m ↦ S.map (· * m)).length = L.length * S.length := by
  induction L with
  | nil => simp
  | cons m L ih => simp [List.flatMap_cons, ih, Nat.add_mul, Nat.add_comm]

theorem eqKernel_getD_ge (l : List E) {i : ℕ} (hi : 2 ^ l.length ≤ i) : (eqKernel l).getD i 0 = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [UniSound.Ids.Facts.size_eqKernel]; exact hi)]
  rfl

/-- **The eq table of a concatenated point** is the tensor product of the tables. -/
theorem eqKernel_append (a b : List E) (i : ℕ) :
    (eqKernel (a ++ b)).getD i 0 = (eqKernel a).getD (i % 2 ^ a.length) 0 * (eqKernel b).getD (i / 2 ^ a.length) 0 := by
  by_cases hi : i < 2 ^ (a.length + b.length)
  · have ha : i % 2 ^ a.length < 2 ^ a.length := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hb : i / 2 ^ a.length < 2 ^ b.length := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_comm]; exact hi
    rw [UniSound.Ids.Facts.eqKernel_getD _ _ (by rw [List.length_append]; exact hi),
      UniSound.Ids.Facts.eqKernel_getD _ _ ha, UniSound.Ids.Facts.eqKernel_getD _ _ hb, List.length_append,
      Finset.prod_range_add]
    congr 1
    · refine Finset.prod_congr rfl fun j hj ↦ ?_
      have hj := mem_range.mp hj
      rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    · refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [Nat.testBit_div_two_pow, Nat.add_comm j]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  · rw [eqKernel_getD_ge _ (by rw [List.length_append]; omega), eqKernel_getD_ge b, mul_zero]
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← pow_add, Nat.add_comm]; omega

/-! ## The packing weights -/

theorem toArray_getD (l : List E) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- The split at `p` of the tensor product `lag ⊗ eq(row_low)` is the tensor product. -/
theorem packing_split (lag rowLow : List E) {k p : ℕ} (hk : k + rowLow.length = 6) (hp : k ≤ p) (hp6 : p ≤ 6)
    (hlag : lag.length = 2 ^ k) (z : ℕ) :
    ((eqKernel (rowLow.take (p - k))).toList.flatMap fun m ↦ lag.map (· * m)).toArray.getD (z % 2 ^ p) 0 *
        (eqKernel (rowLow.drop (p - k))).getD (z / 2 ^ p) 0 =
      ((eqKernel rowLow).toList.flatMap fun m ↦ lag.map (· * m)).getD z 0 := by
  have hpos : 0 < lag.length := by rw [hlag]; exact Nat.two_pow_pos _
  have hmid : (rowLow.take (p - k)).length = p - k := by rw [List.length_take]; omega
  have hpow : 2 ^ p = 2 ^ k * 2 ^ (p - k) := by rw [← pow_add, Nat.add_sub_cancel' hp]
  rw [toArray_getD, getD_flatMap_mul lag hpos, getD_flatMap_mul lag hpos, hlag,
    ← FlockSound.Uni.tx_array_getD (eqKernel (rowLow.take (p - k))), ← FlockSound.Uni.tx_array_getD (eqKernel rowLow),
    show eqKernel rowLow = eqKernel (rowLow.take (p - k) ++ rowLow.drop (p - k)) by rw [List.take_append_drop],
    eqKernel_append, hmid, Nat.mod_mod_of_dvd z (pow_dvd_pow 2 hp), hpow, Nat.mod_mul_right_div_self,
    Nat.div_div_eq_div_mul]
  ring

/-- The skip's weights: Lagrange weights at the skip point, `[1]` without a skip. -/
def lagOf (zSkip : Option E) (rowLow : List E) : List E := match zSkip with
  | some z => lagrangeWeights (2 ^ (6 - rowLow.length)) z
  | none => [1]

theorem lagOf_length {zSkip : Option E} {rowLow : List E} (hz : zSkip = none → rowLow.length = 6) :
    (lagOf zSkip rowLow).length = 2 ^ (6 - rowLow.length) := by
  cases zSkip with
  | some z => exact FlockSound.Uni.lagrangeWeights_length _ _
  | none => simp [lagOf, hz rfl]

theorem lagOf_sum {zSkip : Option E} {rowLow : List E} (hz : zSkip = none → rowLow.length = 6) :
    ∑ i ∈ range (2 ^ (6 - rowLow.length)), (lagOf zSkip rowLow).getD i 0 = 1 := by
  cases zSkip with
  | some z => exact lagrangeWeights_sum (by omega) z
  | none => simp [lagOf, hz rfl]

theorem rowLowWeights_eq (zSkip : Option E) (rowLow : List E) :
    (rowLowWeights zSkip rowLow).2 = (eqKernel rowLow).toList.flatMap fun m ↦ (lagOf zSkip rowLow).map (· * m) := by
  cases zSkip <;> rfl

/-- **The packing weights** of the structured terminal are `rowLowWeights`. -/
theorem packingAt_eq {zSkip : Option E} {rowLow : List E} (hrl : rowLow.length ≤ 6)
    (hz : zSkip = none → rowLow.length = 6) (z : ℕ) :
    packingAt zSkip rowLow z = (rowLowWeights zSkip rowLow).2.getD z 0 := by
  rw [rowLowWeights_eq, ← packing_split (lagOf zSkip rowLow) rowLow (k := 6 - rowLow.length)
    (p := max (6 - rowLow.length) 3) (by omega) (by omega) (by omega) (lagOf_length hz) z]
  cases zSkip <;> rfl

theorem rowLowWeights_length {zSkip : Option E} {rowLow : List E} (hrl : rowLow.length ≤ 6)
    (hz : zSkip = none → rowLow.length = 6) : (rowLowWeights zSkip rowLow).2.length = 64 := by
  rw [rowLowWeights_eq, length_flatMap_mul, lagOf_length hz, Array.length_toList,
    UniSound.Ids.Facts.size_eqKernel, ← pow_add, Nat.add_sub_cancel' hrl]
  rfl

/-- **The packing weights sum to 1.** -/
theorem packing_sum {zSkip : Option E} {rowLow : List E} (hrl : rowLow.length ≤ 6)
    (hz : zSkip = none → rowLow.length = 6) : ∑ z ∈ range 64, (rowLowWeights zSkip rowLow).2.getD z 0 = 1 := by
  have hpos : 0 < (lagOf zSkip rowLow).length := by rw [lagOf_length hz]; exact Nat.two_pow_pos _
  rw [rowLowWeights_eq, show (64 : ℕ) = 2 ^ (6 - rowLow.length) * 2 ^ rowLow.length by
      rw [← pow_add, Nat.sub_add_cancel hrl]; rfl,
    ← sum_range_mul _ (2 ^ (6 - rowLow.length)) (2 ^ rowLow.length)]
  have e : ∀ h ∈ range (2 ^ rowLow.length), ∑ l ∈ range (2 ^ (6 - rowLow.length)),
      ((eqKernel rowLow).toList.flatMap fun m ↦ (lagOf zSkip rowLow).map (· * m)).getD
        (2 ^ (6 - rowLow.length) * h + l) 0 = (eqKernel rowLow).getD h 0 := fun h _ ↦ by
    rw [Finset.sum_congr rfl fun l hl ↦ by
      rw [getD_flatMap_mul _ hpos, lagOf_length hz,
        show (2 ^ (6 - rowLow.length) * h + l) % 2 ^ (6 - rowLow.length) = l by
          have := mem_range.mp hl; rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this],
        show (2 ^ (6 - rowLow.length) * h + l) / 2 ^ (6 - rowLow.length) = h by
          have := mem_range.mp hl
          rw [Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt this, zero_add]],
      ← Finset.sum_mul, lagOf_sum hz, one_mul, FlockSound.Uni.tx_array_getD]
  rw [Finset.sum_congr rfl e, eqKernel_sum]

/-! ## The correlations -/

theorem corr_index {p zh zl off : ℕ} (hp3 : 3 ≤ p) (hp6 : p ≤ 6) (hzh : zh < 2 ^ (6 - p)) (hzl : zl < 2 ^ p)
    (hoff : off < 64) :
    (2 ^ p * ((zh + 2 ^ (6 - p) - off / 2 ^ p) % 2 ^ (6 - p)) + zl + 64 - off % 2 ^ p) % 64 =
      (2 ^ p * zh + zl + 64 - off) % 64 := by
  interval_cases p <;> norm_num at hzh hzl ⊢ <;> omega

/-- Partial correlations through the split `E = E_low ⊗ E_high` are the correlations. -/
theorem corr_reindex (A B : Array E) (s : List E) {p : ℕ} (hp3 : 3 ≤ p) (hp6 : p ≤ 6) {off : ℕ} (hoff : off < 64) :
    ∑ zh ∈ range (2 ^ (6 - p)), B.getD zh 0 * ∑ zl ∈ range (2 ^ p), A.getD zl 0 *
        s.toArray.getD ((2 ^ p * ((zh + 2 ^ (6 - p) - off / 2 ^ p) % 2 ^ (6 - p)) + zl + 64 - off % 2 ^ p) % 64) 0 =
      ∑ z ∈ range 64, A.getD (z % 2 ^ p) 0 * B.getD (z / 2 ^ p) 0 * s.getD ((z + 64 - off) % 64) 0 := by
  have e : ∀ F : ℕ → E, ∑ z ∈ range 64, F z = ∑ z ∈ range (2 ^ p * 2 ^ (6 - p)), F z := fun F ↦ by
    rw [← pow_add, Nat.add_sub_cancel' hp6]
    rfl
  rw [e, ← sum_range_mul _ (2 ^ p) (2 ^ (6 - p))]
  refine Finset.sum_congr rfl fun zh hzh ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun zl hzl ↦ ?_
  have hzh := mem_range.mp hzh
  have hzl := mem_range.mp hzl
  rw [toArray_getD s, corr_index hp3 hp6 hzh hzl hoff, Nat.add_comm (2 ^ p * zh) zl, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hzl, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hzl, zero_add,
    Nat.add_comm zl]
  ring

/-- **The correlations** of the structured terminal are the direct ones at the needed offsets. -/
theorem correlation_eq (zSkip : Option E) (rowLow s : List E) (hrl : rowLow.length ≤ 6) (off : ℕ) :
    correlation zSkip rowLow s off =
      if needed off then corr (packingAt zSkip rowLow) (fun i ↦ s.getD i 0) off else 0 := by
  unfold correlation
  split_ifs with hn
  · simp only [esum_map_range, corr, packingAt]
    exact corr_reindex _ _ s (by omega) (by omega) (needed_lt hn)
  · rfl

/-! ## The theorem -/

/-- **The structured terminal is the walked terminal**: under the Rust's assertions, `structured_terminal` equals
`walked_terminal_with::<_, KeccakWalked>` on the specification's walk, i.e. (`walkedTerminal_eq_bilinear`) the
bilinear form of the block's matrices plus the `C = I` claim and the constant position's pin. -/
theorem structuredTerminal_eq_walked (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (α : E)
    (hrl : rowLow.length ≤ 6) (hz : zSkip = none → rowLow.length = 6) (hci : chiIn.length = 11)
    (hcp : chiInPrime.length = 11) :
    structuredTerminal zSkip rowLow chiIn chiInPrime s α = walkedTerminal zSkip rowLow chiIn chiInPrime s α := by
  have hpack : packingAt zSkip rowLow = fun z ↦ (rowLowWeights zSkip rowLow).2.getD z 0 :=
    funext (packingAt_eq hrl hz)
  have hcorr : correlation zSkip rowLow s = fun off ↦ if needed off then
      corr (fun z ↦ (rowLowWeights zSkip rowLow).2.getD z 0) (fun i ↦ s.getD i 0) off else 0 :=
    funext fun off ↦ by rw [correlation_eq zSkip rowLow s hrl, hpack]
  have hsA : (fun i ↦ s.toArray.getD i 0) = fun i ↦ s.getD i 0 := funext (toArray_getD s)
  have hc0 : corr (fun z ↦ (rowLowWeights zSkip rowLow).2.getD z 0) (fun i ↦ s.getD i 0) 0 =
      ∑ i ∈ range 64, (rowLowWeights zSkip rowLow).2.getD i 0 * s.getD i 0 :=
    Finset.sum_congr rfl fun z hz ↦ by rw [show (z + 64 - 0) % 64 = z by have := mem_range.mp hz; omega]
  simp only [structuredTerminal]
  rw [hpack, hcorr, hsA, structuredCore_eq _ _ _ _ _ _ _ _ _ _ (packing_sum hrl hz), walkedTerminal_eq_bilinear,
    bilinear_eq_WF, WF_congr _ α (fun z _ ↦ rfl) (fun w hw ↦ eqKernel_factor chiIn hci hw)
      (fun w hw ↦ eqKernel_factor chiInPrime hcp hw), eqEval_constantBits _ hcp,
    eqKernel_factor chiInPrime hcp (by decide : 1 < 2048), FlockSound.Uni.tx_dot_eq, rowLowWeights_length hrl hz, hc0]
  ring

/-- **The structured terminal is the matrices' bilinear form**, plus the `C = I` claim and the pin. -/
theorem structuredTerminal_eq_bilinear (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (α : E)
    (hrl : rowLow.length ≤ 6) (hz : zSkip = none → rowLow.length = 6) (hci : chiIn.length = 11)
    (hcp : chiInPrime.length = 11) :
    structuredTerminal zSkip rowLow chiIn chiInPrime s α =
      bilinear zSkip rowLow chiIn chiInPrime s α +
        α * α * eqEval chiIn chiInPrime * dot (rowLowWeights zSkip rowLow).2 s +
        α * α * α * eqEval constantBits chiInPrime * s.getD 0 0 := by
  rw [structuredTerminal_eq_walked zSkip rowLow chiIn chiInPrime s α hrl hz hci hcp, walkedTerminal_eq_bilinear]

end KeccakFlock.Core
