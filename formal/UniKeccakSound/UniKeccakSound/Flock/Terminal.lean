-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The terminal's identity is
-- `formal/KeccakFlock`'s `KeccakFlock.Core.structuredTerminal_eq_bilinear`.
import UniKeccakSound.Flock.Instance

/-!
# The Keccak-f block's structured terminal on the cube

`TerminalSpecK KeccakFlock.keccakFlockSpec`: at the main line's shape, the structured terminal the verifier checks
is the block's matrices' product sum `Σ_cy matPart … s(cy)` plus `Front.known`'s two terms. Three steps:

* **the verifier's terminal is `formal/KeccakFlock`'s** (`StructuredTerminalBridge`): `UniKeccak.structuredTerminal`
  (`formal/UniKeccak/UniKeccak/Terminal.lean`, the Rust's loops) and `KeccakFlock.Terminal.structuredTerminal` (the
  same computation, written as the sums the loops compute) are two transcriptions of `keccak_flock.rs`'s
  `structured_terminal`; their equality is `Bridge.lean`'s `structuredTerminalBridge` (here a hypothesis, so that
  this file does not depend on the loops' proof);
* `KeccakFlock.Core.structuredTerminal_eq_bilinear`: the latter is the matrices' bilinear form plus the `C = I` claim
  and the pin;
* **on the cube** (`bilinear_eq_matPart`, `known_eq`): the bilinear form is `Σ_cy matPart … s(cy)` (block positions
  `z + 64 w` are `posFinM 11`'s), the two known terms are `Front.known`'s.

Hence **`terminalSpecK_of_bridge`**, and the interfaces **`flockSoundK_main`**, **`flockSoundK_rec3`** on
`KeccakFlock.keccakFlockSpec`, from the bridge; `Bridge.lean` closes them (`flockSoundK_main_closed`,
`flockSoundK_rec3_closed`).
-/

namespace UniKeccakSound.KF

open UniSound hiding rd
open UniStatement LeanVM.Parameters Finset FlockSound FlockSound.Uni
open LeanVM.Protocol (Column)
open scoped ENNReal

/-! ## The bridge between the two transcriptions -/

/-- **The verifier's structured terminal is `formal/KeccakFlock`'s**, at the main line's shape (a skip point, a
row point of `3` coordinates, lincheck points of `11`, `64` slices). Both are transcriptions of `keccak_flock.rs`'s
`structured_terminal`; `formal/UniKeccak`'s runner and `formal/KeccakFlock`'s test check each against the Rust's.
Proved in `Bridge.lean` (`structuredTerminalBridge`, for all inputs). -/
def StructuredTerminalBridge : Prop :=
  ∀ (z : E) (rowLow chiIn chiInPrime s : List E) (α : E), rowLow.length = 3 → chiIn.length = 11 →
    chiInPrime.length = 11 → s.length = 64 →
    UniKeccak.structuredTerminal (some z) rowLow chiIn chiInPrime s α =
      KeccakFlock.Terminal.structuredTerminal (some z) rowLow chiIn chiInPrime s α

/-! ## Positions and weights on the cube -/

/-- A block position as a number: packing index `cy`, word `ch`, `cy + 64 ch`. -/
theorem posFinM11_val (cy : Cube (3 + 3)) (ch : Cube 11) :
    ((posFinM (k := 3) (l := 3) 11 rfl (cy, ch) : Fin _) : ℕ) = cubeFin (3 + 3) cy + 64 * cubeFin 11 ch := by
  simp only [posFinM, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, LeanVM.Protocol.cubeSplit_apply,
    LeanVM.Protocol.cubeIndex]
  rfl

/-- **The low weights** at a cube point of the row's `6` packing bits: `lowW`. -/
theorem lowWeights_cubeK (z : E) (rowLow : List E) (hl : rowLow.length = 3) (cy : Cube (3 + 3)) :
    (Flock.rowLowWeights (some z) rowLow).2.getD (cubeFin (3 + 3) cy) 0 =
      lowW (skipNodes 3 (by decide)) z (ptOf rowLow 3) cy := by
  have hpk : Flock.packing - rowLow.length = 3 := by simp only [Flock.packing, hl]
  simp only [Flock.rowLowWeights, hpk]
  have hS : (Flock.lagrangeWeights (2 ^ 3) z).length = 2 ^ 3 := lagrangeWeights_length _ _
  have hM : (eqKernel rowLow).toList.length = 2 ^ 3 := by
    rw [Array.length_toList, eqKernel_size, hl]
  rw [tx_cubeFin_split, tx_flatMap_getD _ hS _ (cubeFin 3 (lowPart cy)).isLt
    (by rw [hM]; exact (cubeFin 3 (highPart cy)).isLt), lagrangeWeights_skip 3 (by decide), ← tx_array_getD,
    eqKernel_cube rowLow hl]
  rfl

theorem length_lowWeightsK (z : E) (rowLow : List E) (hl : rowLow.length = 3) :
    (Flock.rowLowWeights (some z) rowLow).2.length = 64 := by
  simp only [Flock.rowLowWeights, tx_length_flatMap, lagrangeWeights_length, Array.length_toList, eqKernel_size, hl]
  rfl

/-! ## The bilinear form on the cube -/

theorem ite_eq_bit_mul (b : Bool) (w : E) : (if b = true then w else 0) = bit b * w := by
  cases b <;> simp [bit]

/-- **The matrices' bilinear form is the product sum** `Σ_cy matPart … ŝ(cy)` on the cube. -/
theorem bilinear_eq_matPart (z α : E) (rowLow chiIn chiInPrime s : List E) (hl : rowLow.length = 3)
    (h11 : chiIn.length = 11) (h11' : chiInPrime.length = 11) :
    KeccakFlock.Terminal.bilinear (some z) rowLow chiIn chiInPrime s α =
      ∑ cy, matPart (cubeMatM (k := 3) (l := 3) (m := 11) rfl KeccakFlock.matA)
        (cubeMatM (k := 3) (l := 3) (m := 11) rfl KeccakFlock.matB) (skipNodes 3 (by decide)) z (ptOf rowLow 3)
        (ptOf chiIn 11) (ptOf chiInPrime 11) α cy * sliceOf s cy := by
  have hrow : ∀ row : Pos 3 3 11,
      KeccakFlock.Terminal.eRow (some z) rowLow chiIn (posFinM (k := 3) (l := 3) 11 rfl row) =
        lowW (skipNodes 3 (by decide)) z (ptOf rowLow 3) row.1 * eqP (ptOf chiIn 11) row.2 := by
    rintro ⟨cy, ch⟩
    have hv := posFinM11_val cy ch
    have hc := (cubeFin (3 + 3) cy).isLt
    have h1 : ((posFinM (k := 3) (l := 3) 11 rfl (cy, ch) : Fin _) : ℕ) % 64 = cubeFin (3 + 3) cy := by
      rw [hv]; omega
    have h2 : ((posFinM (k := 3) (l := 3) 11 rfl (cy, ch) : Fin _) : ℕ) / 64 = cubeFin 11 ch := by
      rw [hv]; omega
    unfold KeccakFlock.Terminal.eRow
    rw [h1, h2, lowWeights_cubeK z rowLow hl, eqKernel_cube chiIn h11]
  have hcol : ∀ col : Pos 3 3 11,
      KeccakFlock.Terminal.wCol chiInPrime s (posFinM (k := 3) (l := 3) 11 rfl col) =
        sliceOf s col.1 * eqP (ptOf chiInPrime 11) col.2 := by
    rintro ⟨cy, ch⟩
    have hv := posFinM11_val cy ch
    have hc := (cubeFin (3 + 3) cy).isLt
    have h1 : ((posFinM (k := 3) (l := 3) 11 rfl (cy, ch) : Fin _) : ℕ) % 64 = cubeFin (3 + 3) cy := by
      rw [hv]; omega
    have h2 : ((posFinM (k := 3) (l := 3) 11 rfl (cy, ch) : Fin _) : ℕ) / 64 = cubeFin 11 ch := by
      rw [hv]; omega
    unfold KeccakFlock.Terminal.wCol
    rw [h1, h2, eqKernel_cube chiInPrime h11']
    rfl
  have hsum : ∀ G : KeccakFlock.Pos → KeccakFlock.Pos → E, ∑ k : KeccakFlock.Pos, ∑ j : KeccakFlock.Pos, G k j =
      ∑ row : Pos 3 3 11, ∑ col : Pos 3 3 11,
        G (posFinM (k := 3) (l := 3) 11 rfl row) (posFinM (k := 3) (l := 3) 11 rfl col) := by
    intro G
    refine (Fintype.sum_equiv (posFinM (k := 3) (l := 3) 11 rfl) _ _ fun row ↦ ?_).symm
    exact Fintype.sum_equiv (posFinM (k := 3) (l := 3) 11 rfl) _ _ fun _ ↦ rfl
  unfold KeccakFlock.Terminal.bilinear
  rw [hsum]
  simp only [hrow, hcol]
  simp only [matPart, mle, rowW, Finset.sum_mul]
  set G : Pos 3 3 11 → Pos 3 3 11 → E := fun row col ↦
    lowW (skipNodes 3 (by decide)) z (ptOf rowLow 3) row.1 * eqP (ptOf chiIn 11) row.2 *
      (bit (cubeMatM (k := 3) (l := 3) (m := 11) rfl KeccakFlock.matA row col) +
        α * bit (cubeMatM (k := 3) (l := 3) (m := 11) rfl KeccakFlock.matB row col)) *
      (sliceOf s col.1 * eqP (ptOf chiInPrime 11) col.2) with hG
  calc _ = ∑ row : Pos 3 3 11, ∑ col : Pos 3 3 11, G row col := by
        refine Finset.sum_congr rfl fun row _ ↦ Finset.sum_congr rfl fun col _ ↦ ?_
        simp only [hG, cubeMatM, ite_eq_bit_mul]
        ring
    _ = ∑ col : Pos 3 3 11, ∑ row : Pos 3 3 11, G row col := Finset.sum_comm
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun cy _ ↦ Finset.sum_congr rfl fun ch _ ↦
          Finset.sum_congr rfl fun row _ ↦ ?_
        rw [hG]
        simp only [lowW]
        ring

/-! ## The known terms on the cube -/

/-- The constant position (`64`): packing index `0`, word `1`. -/
theorem cposK_eq : (posFinM (k := 3) (l := 3) 11 rfl).symm KeccakFlock.cpos =
    ((cubeFin (3 + 3)).symm ⟨0, by norm_num⟩, (cubeFin 11).symm ⟨1, by norm_num⟩) := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [posFinM11_val, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  decide

theorem eqEval_constantBits (χ' : Fin 11 → E) :
    UniStatement.eqEval KeccakFlock.Terminal.constantBits (List.ofFn χ') =
      eqP χ' ((posFinM (k := 3) (l := 3) 11 rfl).symm KeccakFlock.cpos).2 := by
  have hc : KeccakFlock.Terminal.constantBits.length = 11 := by simp [KeccakFlock.Terminal.constantBits]
  rw [eqEval_eq _ _ hc List.length_ofFn, tx_ptOf_ofFn, cposK_eq, FlockSound.eqEval, eqP]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  have hj := j.isLt
  dsimp only
  rw [cubeFin_symm_apply]
  have hget : ptOf KeccakFlock.Terminal.constantBits 11 j = if (1 : ℕ).testBit j then 1 else 0 := by
    simp [ptOf, List.getD_eq_getElem?_getD, KeccakFlock.Terminal.constantBits, hj, bitE]
  rw [hget]
  cases (1 : ℕ).testBit j <;> simp

/-- **The two known terms** (`α² eq(chi_in, chi_in') Σ e s + α³ eq(word 1, chi_in') s_0`) are `Front.known`'s. -/
theorem known_eq (z α : E) (rl : Fin 3 → E) (rh χ' : Fin 11 → E) (s : Cube (3 + 3) → E) :
    α * α * UniStatement.eqEval (List.ofFn rh) (List.ofFn χ') *
        dot (Flock.rowLowWeights (some z) (List.ofFn rl)).2 (sliceList s) +
      α * α * α * UniStatement.eqEval KeccakFlock.Terminal.constantBits (List.ofFn χ') * (sliceList s).getD 0 0 =
    α ^ 2 * FlockSound.eqEval rh χ' * ∑ cy, lowW (skipNodes 3 (by decide)) z rl cy * s cy +
      α ^ 3 * eqP χ' ((posFinM (k := 3) (l := 3) 11 rfl).symm KeccakFlock.cpos).2 *
        s ((posFinM (k := 3) (l := 3) 11 rfl).symm KeccakFlock.cpos).1 := by
  have hl : (List.ofFn rl).length = 3 := List.length_ofFn
  have hdot : dot (Flock.rowLowWeights (some z) (List.ofFn rl)).2 (sliceList s) =
      ∑ cy, lowW (skipNodes 3 (by decide)) z rl cy * s cy := by
    rw [tx_dot_eq, length_lowWeightsK z _ hl, show (64 : ℕ) = 2 ^ (3 + 3) from rfl, sum_range_eq_sum_cube]
    refine Finset.sum_congr rfl fun cy _ ↦ ?_
    rw [lowWeights_cubeK z _ hl, tx_ptOf_ofFn]
    congr 1
    exact congrFun (tx_sliceOf_ofFn s) cy
  have hs0 : (sliceList s).getD 0 0 = s ((posFinM (k := 3) (l := 3) 11 rfl).symm KeccakFlock.cpos).1 := by
    rw [cposK_eq, sliceList, tx_getD_ofFn _ (by norm_num : 0 < 64)]
  rw [eqEval_eq _ _ List.length_ofFn List.length_ofFn, tx_ptOf_ofFn, tx_ptOf_ofFn, hdot, eqEval_constantBits, hs0]
  ring

/-! ## The terminal, and the interfaces -/

/-- **`TerminalSpecK` for the Keccak-f block**, from the bridge between the two transcriptions. -/
theorem terminalSpecK_of_bridge (hB : StructuredTerminalBridge) : TerminalSpecK KeccakFlock.keccakFlockSpec := by
  intro z α rl rh χ' s
  show _ = ∑ cy, matPart (cubeMatM (k := 3) (l := 3) (m := 11) rfl KeccakFlock.matA)
      (cubeMatM (k := 3) (l := 3) (m := 11) rfl KeccakFlock.matB) (skipNodes 3 (by decide)) z rl rh χ' α cy * s cy +
    (α ^ 2 * FlockSound.eqEval rh χ' * ∑ cy, lowW (skipNodes 3 (by decide)) z rl cy * s cy +
      α ^ 3 * eqP χ' ((posFinM (k := 3) (l := 3) 11 rfl).symm KeccakFlock.cpos).2 *
        s ((posFinM (k := 3) (l := 3) 11 rfl).symm KeccakFlock.cpos).1)
  have hs : (sliceList s).length = 64 := List.length_ofFn
  rw [hB z _ _ _ _ α List.length_ofFn List.length_ofFn List.length_ofFn hs,
    KeccakFlock.Core.structuredTerminal_eq_bilinear _ _ _ _ _ α (by simp) (by simp) List.length_ofFn
      List.length_ofFn,
    bilinear_eq_matPart z α _ _ _ _ List.length_ofFn List.length_ofFn List.length_ofFn, add_assoc, known_eq,
    tx_ptOf_ofFn, tx_ptOf_ofFn, tx_ptOf_ofFn, sliceList, tx_sliceOf_ofFn]

/-- **Flock's interface on the Keccak-f block, main line** (`KECCAK_MAIN`), for every `κ`, from the bridge. -/
noncomputable def flockSoundK_main (hB : StructuredTerminalBridge) (κ : ℕ) :
    KFlockSound KeccakFlock.keccakFlockSpec κ UniKeccak.keccakMain :=
  kFlockSoundMain KeccakFlock.keccakFlockSpec (terminalSpecK_of_bridge hB) κ

/-- **Its rounds' errors**: at most `2^32/|E|` each (for `7 + κ ≤ 2^32`, e.g. `κ ≤ 28`). -/
theorem flockSoundK_main_err_le (hB : StructuredTerminalBridge) (κ : ℕ) (hκ : 7 + κ ≤ 2 ^ 32) (j : ℕ) :
    (flockSoundK_main hB κ).err j ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  kFlockSoundMain_err_le _ _ κ hκ j

/-- **Flock's interface on the Keccak-f block, π1-rec3** (`KECCAK_REC3`), for every `κ`, from the bridge. -/
noncomputable def flockSoundK_rec3 (hB : StructuredTerminalBridge) (κ : ℕ) :
    KFlockSound KeccakFlock.keccakFlockSpec κ UniKeccak.keccakRec3 :=
  kFlockSoundRec3 KeccakFlock.keccakFlockSpec (terminalSpecK_of_bridge hB) κ

/-- **Its rounds' errors**: at most `2^35/|E|` each, for `κ ≤ 28` (Kronecker for the squares' challenge). -/
theorem flockSoundK_rec3_err_le (hB : StructuredTerminalBridge) (κ : ℕ) (hκ : κ ≤ 28) (j : ℕ) :
    (flockSoundK_rec3 hB κ).err j ≤ ((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  kFlockSoundRec3_err_le _ _ κ hκ j

/-- **Flock's result is the main line's** for `flockSoundK_main` (the identity model's `FlockGoodDoneK`,
unfolded). -/
theorem flockSoundK_main_good (hB : StructuredTerminalBridge) (κ : ℕ) :
    ∀ fd, DoneFits (flockSoundK_main hB κ).prog.rounds fd →
      (∃ map target, ((flockSoundK_main hB κ).prog.out fd []).2 = .ring map target) ∧
        ((flockSoundK_main hB κ).prog.out fd []).1.length = KeccakVm.kWords + κ :=
  kFlockSoundMain_good _ _ κ

theorem flockSoundK_rec3_good (hB : StructuredTerminalBridge) (κ : ℕ) :
    ∀ fd, DoneFits (flockSoundK_rec3 hB κ).prog.rounds fd →
      (∃ map target, ((flockSoundK_rec3 hB κ).prog.out fd []).2 = .ring map target) ∧
        ((flockSoundK_rec3 hB κ).prog.out fd []).1.length = KeccakVm.kWords + κ :=
  kFlockSoundRec3_good _ _ κ

/-- **The Fiat–Shamir layer's sizes**, main line: every round's scalars at most `2^30`; at `κ = 15` its `70`
challenges with the batch's `27` within `1014`. -/
theorem flockSoundK_main_nv (hB : StructuredTerminalBridge) (κ : ℕ) :
    ∀ r ∈ (flockSoundK_main hB κ).prog.rounds, r.nv ≤ 2 ^ 30 := kFlockSoundMain_nv _ _ κ

theorem flockSoundK_main_nSteps (hB : StructuredTerminalBridge) :
    Compose.nSteps (flockSoundK_main hB 15).prog.rounds + 27 ≤ 1014 := kFlockSoundMain_nSteps _ _

theorem flockSoundK_rec3_nv (hB : StructuredTerminalBridge) (κ : ℕ) :
    ∀ r ∈ (flockSoundK_rec3 hB κ).prog.rounds, r.nv ≤ 2 ^ 30 := kFlockSoundRec3_nv _ _ κ

theorem flockSoundK_rec3_nSteps (hB : StructuredTerminalBridge) :
    Compose.nSteps (flockSoundK_rec3 hB 15).prog.rounds + 27 ≤ 1014 := kFlockSoundRec3_nSteps _ _

end UniKeccakSound.KF

/-- info: 'UniKeccakSound.KF.terminalSpecK_of_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.terminalSpecK_of_bridge

/-- info: 'UniKeccakSound.KF.flockSoundK_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.flockSoundK_main

/-- info: 'UniKeccakSound.KF.flockSoundK_main_err_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.flockSoundK_main_err_le

/-- info: 'UniKeccakSound.KF.flockSoundK_rec3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.flockSoundK_rec3

/-- info: 'UniKeccakSound.KF.flockSoundK_rec3_err_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.KF.flockSoundK_rec3_err_le
