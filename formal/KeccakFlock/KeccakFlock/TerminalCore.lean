-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import KeccakFlock.TerminalWalk

/-!
# The matrices' bilinear form, row class by row class

The bilinear form of the block's matrices with row weights `Ew z · ρ(w)` (position `z + 64 w`) and column weights
`sv z' · γ(w')`, for any tables `Ew, sv, ρ, γ`, is the walked form `WF` (`wordTerm`: word `w`'s 64 rows). Summed over
the packing positions `z`, every row class is a closed form (`WF_eq`):

* the eleven positions of a bit of `b[i]` give, summed against `Ew`, two correlations
  `corr(off) = Σ_z Ew_z sv_(z − off)` at `off = rot_i` and `rot_i + 1`, times the column weights of the state words
  they read (`sum_bForm`: `bz j i`);
* a product row adds the constant column `c1 = sv_0 γ(1)` once per position (`Σ_z Ew_z`), a lin-id row the `t` term
  `corr(0) γ(t)` and ι's bits (`RCw j`), every `B = [1]` the constant column;
* the port's free inputs and copies are `corr(0)` terms, its constant rows `Ew_0`, `Ew_1` terms.

This is the walked side of the structured terminal's identity; `TerminalStruct.lean` matches the structured side to
it.
-/

namespace KeccakFlock.Core

open LeanVM.Parameters PcsCircuit PcsCircuit.Builder Finset KeccakFlock.Terminal

/-! ## The walked form -/

/-- The column weight of position `p`: `sv(p mod 64) · γ(p / 64)`. -/
def wc (sv γ : ℕ → E) (p : Pos) : E := sv (p.val % 64) * γ (p.val / 64)

/-- The column weights summed over a list of positions. -/
def lsum (sv γ : ℕ → E) (L : List Pos) : E := (L.map (wc sv γ)).sum

/-- Word `w`'s 64 rows: `Σ_z Ew_z ρ(w) (Σ_(row's A list) + α Σ_(row's B list))`. -/
def wordTerm (Ew sv ρ γ : ℕ → E) (α : E) (w : ℕ) : E :=
  ∑ z ∈ range 64, Ew z * ρ w * (lsum sv γ (rowW w z).1 + α * lsum sv γ (rowW w z).2)

/-- **The walked form**: every row, weighed. -/
def WF (Ew sv ρ γ : ℕ → E) (α : E) : E := ∑ w ∈ range 2048, wordTerm Ew sv ρ γ α w

/-- `Corr[off] = Σ_z Ew_z sv_(z − off)`. -/
def corr (Ew sv : ℕ → E) (off : ℕ) : E := ∑ z ∈ range 64, Ew z * sv ((z + 64 - off) % 64)

/-- The column weights of column `x`'s five lanes of the state before round `j`. -/
def colG (γ : ℕ → E) (j x : ℕ) : E :=
  γ (stWord j x) + γ (stWord j (x + 5)) + γ (stWord j (x + 10)) + γ (stWord j (x + 15)) + γ (stWord j (x + 20))

/-- The column weights `b[i]` reads at `z − rot`: its source lane and θ's column `src − 1`. -/
def gamL (γ : ℕ → E) (j i : ℕ) : E := γ (stWord j (piInv i)) + colG γ j ((piInv i % 5 + 4) % 5)

/-- The column weights `b[i]` reads at `z − rot − 1`: θ's column `src + 1`. -/
def gamR (γ : ℕ → E) (j i : ℕ) : E := colG γ j ((piInv i % 5 + 1) % 5)

/-- `Σ_z Ew_z (b[i]'s form at z)`, round `j`. -/
def bz (Ew sv γ : ℕ → E) (j i : ℕ) : E :=
  corr Ew sv (rho (piInv i)) * gamL γ j i + corr Ew sv (rho (piInv i) + 1) * gamR γ j i

/-- ι's weight: `Σ_(z : RC_j has bit z) Ew_z`. -/
def RCw (Ew : ℕ → E) (j : ℕ) : E := ∑ z ∈ range 64, if rcBit j z then Ew z else 0

/-! ## Lists -/

theorem wc_pos (sv γ : ℕ → E) {w z : ℕ} (hw : w < 2048) (hz : z < 64) : wc sv γ (pos w z) = sv z * γ w := by
  simp only [wc, pos_val hw hz, show (z + 64 * w) % 64 = z by omega, show (z + 64 * w) / 64 = w by omega]

theorem lsum_nil (sv γ : ℕ → E) : lsum sv γ [] = 0 := rfl

theorem lsum_cons (sv γ : ℕ → E) (p : Pos) (L : List Pos) : lsum sv γ (p :: L) = wc sv γ p + lsum sv γ L := by
  simp [lsum]

theorem lsum_append (sv γ : ℕ → E) (L₁ L₂ : List Pos) : lsum sv γ (L₁ ++ L₂) = lsum sv γ L₁ + lsum sv γ L₂ := by
  simp [lsum]

theorem wc_cpos (sv γ : ℕ → E) : wc sv γ cpos = sv 0 * γ 1 := by
  rw [cpos, wc_pos sv γ (by decide) (by decide)]
  rfl

theorem lsum_cpos (sv γ : ℕ → E) : lsum sv γ [cpos] = sv 0 * γ 1 := by
  rw [lsum_cons, lsum_nil, add_zero, wc_cpos]

theorem lsum_ite (sv γ : ℕ → E) (P : Prop) [Decidable P] :
    lsum sv γ (if P then [cpos] else []) = if P then sv 0 * γ 1 else 0 := by
  split_ifs <;> simp [lsum_cpos, lsum_nil]

theorem rho_le : ∀ i < 25, rho (piInv i) ≤ 62 := by decide

theorem lsum_bForm (sv γ : ℕ → E) {j i : ℕ} (hj : j ≤ 24) (hi : i < 25) (z : ℕ) :
    lsum sv γ (bForm j i z) = sv ((z + 64 - rho (piInv i)) % 64) * gamL γ j i +
      sv (((z + 64 - rho (piInv i)) % 64 + 63) % 64) * gamR γ j i := by
  have hp : piInv i < 25 := piInv_lt i hi
  obtain ⟨zp, hzp, e⟩ : ∃ zp, zp < 64 ∧ (z + 64 - rho (piInv i)) % 64 = zp := ⟨_, Nat.mod_lt _ (by decide), rfl⟩
  have hzr : (zp + 63) % 64 < 64 := Nat.mod_lt _ (by decide)
  have h := fun l (hl : l < 25) ↦ stWord_lt hj hl
  simp only [bForm, lsum_cons, lsum_nil, e, gamL, gamR, colG]
  rw [wc_pos sv γ (h _ hp) hzp, wc_pos sv γ (h ((piInv i % 5 + 4) % 5) (by omega)) hzp,
    wc_pos sv γ (h ((piInv i % 5 + 4) % 5 + 5) (by omega)) hzp,
    wc_pos sv γ (h ((piInv i % 5 + 4) % 5 + 10) (by omega)) hzp,
    wc_pos sv γ (h ((piInv i % 5 + 4) % 5 + 15) (by omega)) hzp,
    wc_pos sv γ (h ((piInv i % 5 + 4) % 5 + 20) (by omega)) hzp,
    wc_pos sv γ (h ((piInv i % 5 + 1) % 5) (by omega)) hzr,
    wc_pos sv γ (h ((piInv i % 5 + 1) % 5 + 5) (by omega)) hzr,
    wc_pos sv γ (h ((piInv i % 5 + 1) % 5 + 10) (by omega)) hzr,
    wc_pos sv γ (h ((piInv i % 5 + 1) % 5 + 15) (by omega)) hzr,
    wc_pos sv γ (h ((piInv i % 5 + 1) % 5 + 20) (by omega)) hzr]
  ring

/-- **A form of `b`, summed against the packing weights**: two correlations. -/
theorem sum_bForm (Ew sv γ : ℕ → E) {j i : ℕ} (hj : j ≤ 24) (hi : i < 25) :
    ∑ z ∈ range 64, Ew z * lsum sv γ (bForm j i z) = bz Ew sv γ j i := by
  have hr := rho_le i hi
  rw [Finset.sum_congr rfl fun z _ ↦ by rw [lsum_bForm sv γ hj hi z]]
  simp only [bz, corr, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun z _ ↦ by ring) ?_
  · refine Finset.sum_congr rfl fun z hz ↦ ?_
    rw [show ((z + 64 - rho (piInv i)) % 64 + 63) % 64 = (z + 64 - (rho (piInv i) + 1)) % 64 by
      have := mem_range.mp hz; omega]
    ring

/-! ## Word by word -/

variable (Ew sv ρ γ : ℕ → E) (α : E)

theorem wordTerm_eq {w : ℕ} {f : ℕ → E}
    (h : ∀ z < 64, lsum sv γ (rowW w z).1 + α * lsum sv γ (rowW w z).2 = f z) :
    wordTerm Ew sv ρ γ α w = ρ w * ∑ z ∈ range 64, Ew z * f z := by
  unfold wordTerm
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun z hz ↦ by rw [h z (mem_range.mp hz)]; ring

theorem wordTerm_empty {w : ℕ} (h : ∀ z < 64, rowW w z = ([], [])) : wordTerm Ew sv ρ γ α w = 0 := by
  rw [wordTerm_eq Ew sv ρ γ α (f := fun _ ↦ 0) fun z hz ↦ by rw [h z hz]; simp [lsum_nil]]
  simp

/-- A product row: `ρ(t) (Σ Ew · c1 + bz(x+1) + α bz(x+2))`. -/
theorem wordTerm_t {j l : ℕ} (hj : j < 24) (hl : l < 25) :
    wordTerm Ew sv ρ γ α (tWord j l) = ρ (tWord j l) * ((∑ z ∈ range 64, Ew z) * (sv 0 * γ 1) +
      bz Ew sv γ j ((l % 5 + 1) % 5 + 5 * (l / 5)) + α * bz Ew sv γ j ((l % 5 + 2) % 5 + 5 * (l / 5))) := by
  rw [wordTerm_eq Ew sv ρ γ α (f := fun z ↦ sv 0 * γ 1 + lsum sv γ (bForm j ((l % 5 + 1) % 5 + 5 * (l / 5)) z) +
      α * lsum sv γ (bForm j ((l % 5 + 2) % 5 + 5 * (l / 5)) z)) fun z _ ↦ by
    rw [rowW_t hj hl]
    dsimp only
    rw [lsum_cons, wc_cpos]]
  refine congrArg (ρ (tWord j l) * ·) ?_
  rw [← sum_bForm Ew sv γ (j := j) (by omega) (by omega), ← sum_bForm Ew sv γ (j := j) (by omega) (by omega),
    Finset.sum_mul, Finset.mul_sum (a := α), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun z _ ↦ by ring

/-- A lin-id row (a state word, or the output port's `X` word in round 23):
`ρ (bz(l) + corr(0) γ(t) + ι + α Σ Ew · c1)`. -/
theorem wordTerm_A {j l : ℕ} (hj : j < 24) (hl : l < 25) :
    wordTerm Ew sv ρ γ α (stWord (j + 1) l) = ρ (stWord (j + 1) l) * (bz Ew sv γ j l +
      corr Ew sv 0 * γ (tWord j l) + (if l = 0 then RCw Ew j * (sv 0 * γ 1) else 0) +
      α * ((∑ z ∈ range 64, Ew z) * (sv 0 * γ 1))) := by
  rw [wordTerm_eq Ew sv ρ γ α (f := fun z ↦ lsum sv γ (bForm j l z) + sv z * γ (tWord j l) +
      (if l = 0 ∧ rcBit j z = true then sv 0 * γ 1 else 0) + α * (sv 0 * γ 1)) fun z hz ↦ by
    rw [rowW_st hj hl]
    dsimp only
    rw [linForm, lsum_append, lsum_cons, wc_pos sv γ (tWord_lt hj hl) hz, lsum_ite, lsum_cpos]
    ring]
  refine congrArg (ρ (stWord (j + 1) l) * ·) ?_
  have h0 : ∀ z ∈ range 64, Ew z * (sv z * γ (tWord j l)) = Ew z * sv ((z + 64 - 0) % 64) * γ (tWord j l) :=
    fun z hz ↦ by rw [show (z + 64 - 0) % 64 = z by have := mem_range.mp hz; omega]; ring
  have hrc : ∑ z ∈ range 64, Ew z * (if l = 0 ∧ rcBit j z = true then sv 0 * γ 1 else 0) =
      if l = 0 then RCw Ew j * (sv 0 * γ 1) else 0 := by
    by_cases h : l = 0
    · simp only [h, true_and, ite_true, RCw, Finset.sum_mul]
      exact Finset.sum_congr rfl fun z _ ↦ by split_ifs <;> simp
    · simp [h]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_bForm Ew sv γ (by omega) hl, Finset.sum_congr rfl h0, hrc, corr, Finset.sum_mul, Finset.sum_mul,
    Finset.mul_sum (a := α)]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun z _ ↦ by ring)

/-- A free input row (`C` word): `ρ (corr(0) γ(C) + α Σ Ew · c1)`. -/
theorem wordTerm_C {q : ℕ} (hq : q < 25) :
    wordTerm Ew sv ρ γ α (4 * q + 2) = ρ (4 * q + 2) * (corr Ew sv 0 * γ (4 * q + 2) +
      α * ((∑ z ∈ range 64, Ew z) * (sv 0 * γ 1))) := by
  rw [wordTerm_eq Ew sv ρ γ α (f := fun z ↦ sv z * γ (4 * q + 2) + α * (sv 0 * γ 1)) fun z hz ↦ by
    rw [rowW_port (by omega) (by omega)]
    simp only [portRow, show ¬ (2 = 1) by decide, hq, ite_true, show ¬ (2 = 0) by decide, ite_false]
    rw [lsum_cpos, lsum_cons, lsum_nil, add_zero, portWord, wc_pos sv γ (by omega) hz]]
  simp only [corr, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun z hz ↦ ?_) (Finset.sum_congr rfl fun z _ ↦ by ring)
  rw [show (z + 64 - 0) % 64 = z by have := mem_range.mp hz; omega]
  ring

/-- A copy row (`V` word): `ρ (corr(0) γ(X) + α Σ Ew · c1)`. -/
theorem wordTerm_V {q : ℕ} (hq : q < 25) :
    wordTerm Ew sv ρ γ α (4 * q + 3) = ρ (4 * q + 3) * (corr Ew sv 0 * γ (4 * q) +
      α * ((∑ z ∈ range 64, Ew z) * (sv 0 * γ 1))) := by
  rw [wordTerm_eq Ew sv ρ γ α (f := fun z ↦ sv z * γ (4 * q) + α * (sv 0 * γ 1)) fun z hz ↦ by
    rw [rowW_port (by omega) (by omega)]
    simp only [portRow, show ¬ (3 = 1) by decide, hq, ite_true, show ¬ (3 = 0) by decide,
      show ¬ (3 = 2) by decide, ite_false]
    rw [lsum_cpos, lsum_cons, lsum_nil, add_zero, portWord, add_zero, wc_pos sv γ (by omega) hz]]
  simp only [corr, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun z hz ↦ ?_) (Finset.sum_congr rfl fun z _ ↦ by ring)
  rw [show (z + 64 - 0) % 64 = z by have := mem_range.mp hz; omega]
  ring

/-- A `Y` word: its bit 0 is a constant row, the others empty. -/
theorem wordTerm_Y {q : ℕ} (hq : q < 32) :
    wordTerm Ew sv ρ γ α (4 * q + 1) = ρ (4 * q + 1) * (Ew 0 * (sv 0 * γ 1 + α * (sv 0 * γ 1))) := by
  rw [wordTerm_eq Ew sv ρ γ α (f := fun z ↦ if z = 0 then sv 0 * γ 1 + α * (sv 0 * γ 1) else 0) fun z hz ↦ by
    rw [rowW_port hq (by omega)]
    simp only [portRow, ite_true]
    split_ifs <;> simp [lsum_cpos, lsum_nil]]
  refine congrArg (ρ (4 * q + 1) * ·) ?_
  rw [Finset.sum_eq_single 0 (fun z _ hz ↦ by simp [hz]) (by simp)]
  simp

/-- The `x` quad's `X` and `V` words (`r = 0, 3`): bit 1 is a constant row, the others empty. -/
theorem wordTerm_x {r : ℕ} (hr : r = 0 ∨ r = 3) :
    wordTerm Ew sv ρ γ α (4 * 25 + r) = ρ (4 * 25 + r) * (Ew 1 * (sv 0 * γ 1 + α * (sv 0 * γ 1))) := by
  rw [wordTerm_eq Ew sv ρ γ α (f := fun z ↦ if z = 1 then sv 0 * γ 1 + α * (sv 0 * γ 1) else 0) fun z hz ↦ by
    rw [rowW_port (by omega) (by omega)]
    simp only [portRow, show ¬ (r = 1) by omega, show ¬ (25 < 25) by decide, show r ≠ 2 by omega, ite_false,
      true_and, ne_eq, not_false_eq_true]
    split_ifs <;> simp_all [lsum_cpos, lsum_nil]]
  refine congrArg (ρ (4 * 25 + r) * ·) ?_
  rw [Finset.sum_eq_single 1 (fun z _ hz ↦ by simp [hz]) (by simp)]
  simp

/-- The other port words (`X`, `C`, `V` of quads 26..31, `C` of quad 25) are empty. -/
theorem wordTerm_portEmpty {q r : ℕ} (hq : 25 ≤ q) (hq' : q < 32) (hr : r < 4) (hr1 : r ≠ 1)
    (hx : ¬ (q = 25 ∧ r ≠ 2)) : wordTerm Ew sv ρ γ α (4 * q + r) = 0 :=
  wordTerm_empty Ew sv ρ γ α fun z _ ↦ by
    rw [rowW_port hq' hr]
    simp only [portRow, hr1, ite_false, show ¬ q < 25 by omega]
    rw [ite_eq_right (fun h ↦ hx ⟨h.1, h.2.1⟩)]

/-- The empty lanes of a round's run, and round 23's `A` lanes (the output is in the port). -/
theorem wordTerm_roundEmpty {j r : ℕ} (hj : j < 24) (hr : r < 64) (h1 : ¬ r < 25)
    (h2 : ¬ (32 ≤ r ∧ r < 57 ∧ j < 23)) : wordTerm Ew sv ρ γ α (64 * (j + 2) + r) = 0 :=
  wordTerm_empty Ew sv ρ γ α fun z _ ↦ by
    rw [rowW_round hj hr]
    simp only [roundRow, h1, h2, ite_false]

/-- Past the rounds' runs, every row is empty. -/
theorem wordTerm_suffix {w : ℕ} (hw : 1664 ≤ w) : wordTerm Ew sv ρ γ α w = 0 :=
  wordTerm_empty Ew sv ρ γ α fun z _ ↦ by
    unfold rowW
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## The walked form, class by class -/

theorem sum_range_mul (F : ℕ → E) (b : ℕ) : ∀ n : ℕ,
    ∑ h ∈ range n, ∑ l ∈ range b, F (b * h + l) = ∑ k ∈ range (b * n), F k
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_mul F b n, show b * (n + 1) = b * n + b by ring, Finset.sum_range_add]

/-- The walked form: the port region and the rounds' runs (the suffix is empty). -/
theorem WF_split : WF Ew sv ρ γ α = ∑ q ∈ range 32, ∑ r ∈ range 4, wordTerm Ew sv ρ γ α (4 * q + r) +
    ∑ j ∈ range 24, ∑ r ∈ range 64, wordTerm Ew sv ρ γ α (64 * (j + 2) + r) := by
  set T := wordTerm Ew sv ρ γ α
  have h1 : ∑ w ∈ range (4 * 32 + (64 * 24 + 384)), T w =
      ∑ w ∈ range (4 * 32), T w + ∑ w ∈ range (64 * 24 + 384), T (4 * 32 + w) :=
    Finset.sum_range_add _ _ _
  have h2 : ∑ w ∈ range (64 * 24 + 384), T (4 * 32 + w) =
      ∑ w ∈ range (64 * 24), T (4 * 32 + w) + ∑ w ∈ range 384, T (4 * 32 + (64 * 24 + w)) :=
    Finset.sum_range_add _ _ _
  unfold WF
  rw [show (2048 : ℕ) = 4 * 32 + (64 * 24 + 384) from rfl, h1, h2, ← sum_range_mul T 4 32,
    ← sum_range_mul (fun w ↦ T (4 * 32 + w)) 64 24, Finset.sum_eq_zero (s := range 384)
      (f := fun w ↦ T (4 * 32 + (64 * 24 + w))) (fun w _ ↦ wordTerm_suffix Ew sv ρ γ α (by omega)), add_zero]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun r _ ↦ ?_)
  rw [show 4 * 32 + (64 * j + r) = 64 * (j + 2) + r by ring]

/-- The port region: the `Y` words, the `x` quad, the `C` and `V` words, the `X` words (the output port). -/
theorem port_eq : ∑ q ∈ range 32, ∑ r ∈ range 4, wordTerm Ew sv ρ γ α (4 * q + r) =
    ∑ q ∈ range 32, wordTerm Ew sv ρ γ α (4 * q + 1) +
      (wordTerm Ew sv ρ γ α (4 * 25 + 0) + wordTerm Ew sv ρ γ α (4 * 25 + 3)) +
      ∑ q ∈ range 25, wordTerm Ew sv ρ γ α (4 * q + 2) + ∑ q ∈ range 25, wordTerm Ew sv ρ γ α (4 * q + 3) +
      ∑ q ∈ range 25, wordTerm Ew sv ρ γ α (stWord 24 q) := by
  set T := wordTerm Ew sv ρ γ α
  have hr : ∀ q, ∑ r ∈ range 4, T (4 * q + r) = T (4 * q + 0) + T (4 * q + 1) + T (4 * q + 2) + T (4 * q + 3) :=
    fun q ↦ by simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hz : ∀ (r : ℕ), r < 4 → r ≠ 1 → ∑ x ∈ range 6, T (4 * (25 + (x + 1)) + r) = 0 := fun r hr4 hr1 ↦
    Finset.sum_eq_zero fun x hx ↦ by
      have := mem_range.mp hx
      exact wordTerm_portEmpty Ew sv ρ γ α (q := 25 + (x + 1)) (r := r) (by omega) (by omega) hr4 hr1 (by omega)
  have h0 : ∑ q ∈ range 32, T (4 * q + 0) = ∑ q ∈ range 25, T (stWord 24 q) + T (4 * 25 + 0) := by
    have e : ∑ q ∈ range 32, T (4 * q + 0) = ∑ q ∈ range 25, T (4 * q + 0) + ∑ x ∈ range (6 + 1), T (4 * (25 + x) + 0) :=
      Finset.sum_range_add _ 25 (6 + 1)
    rw [e, Finset.sum_range_succ' (fun x ↦ T (4 * (25 + x) + 0)) 6, hz 0 (by decide) (by decide), zero_add]
    rfl
  have h2 : ∑ q ∈ range 32, T (4 * q + 2) = ∑ q ∈ range 25, T (4 * q + 2) := by
    have e : ∑ q ∈ range 32, T (4 * q + 2) = ∑ q ∈ range 25, T (4 * q + 2) + ∑ x ∈ range (6 + 1), T (4 * (25 + x) + 2) :=
      Finset.sum_range_add _ 25 (6 + 1)
    have h25 : T (4 * (25 + 0) + 2) = 0 :=
      wordTerm_portEmpty Ew sv ρ γ α (q := 25 + 0) (r := 2) (by omega) (by omega) (by decide) (by decide) (by omega)
    rw [e, Finset.sum_range_succ' (fun x ↦ T (4 * (25 + x) + 2)) 6, hz 2 (by decide) (by decide), zero_add, h25,
      add_zero]
  have h3 : ∑ q ∈ range 32, T (4 * q + 3) = ∑ q ∈ range 25, T (4 * q + 3) + T (4 * 25 + 3) := by
    have e : ∑ q ∈ range 32, T (4 * q + 3) = ∑ q ∈ range 25, T (4 * q + 3) + ∑ x ∈ range (6 + 1), T (4 * (25 + x) + 3) :=
      Finset.sum_range_add _ 25 (6 + 1)
    rw [e, Finset.sum_range_succ' (fun x ↦ T (4 * (25 + x) + 3)) 6, hz 3 (by decide) (by decide), zero_add]
  rw [Finset.sum_congr rfl fun q _ ↦ hr q, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    h0, h2, h3]
  ring

/-- A round's run: the products, the states (none in round 23, whose output is the port's), the rest empty. -/
theorem run_eq {j : ℕ} (hj : j < 24) : ∑ r ∈ range 64, wordTerm Ew sv ρ γ α (64 * (j + 2) + r) =
    ∑ l ∈ range 25, wordTerm Ew sv ρ γ α (tWord j l) +
      if j < 23 then ∑ l ∈ range 25, wordTerm Ew sv ρ γ α (stWord (j + 1) l) else 0 := by
  set T := wordTerm Ew sv ρ γ α
  have h1 : ∑ r ∈ range 64, T (64 * (j + 2) + r) =
      ∑ r ∈ range 25, T (64 * (j + 2) + r) + ∑ r ∈ range (7 + (25 + 7)), T (64 * (j + 2) + (25 + r)) :=
    Finset.sum_range_add _ 25 (7 + (25 + 7))
  have h2 : ∑ r ∈ range (7 + (25 + 7)), T (64 * (j + 2) + (25 + r)) =
      ∑ r ∈ range 7, T (64 * (j + 2) + (25 + r)) + ∑ r ∈ range (25 + 7), T (64 * (j + 2) + (25 + (7 + r))) :=
    Finset.sum_range_add _ 7 (25 + 7)
  have h3 : ∑ r ∈ range (25 + 7), T (64 * (j + 2) + (25 + (7 + r))) =
      ∑ r ∈ range 25, T (64 * (j + 2) + (25 + (7 + r))) + ∑ r ∈ range 7, T (64 * (j + 2) + (25 + (7 + (25 + r)))) :=
    Finset.sum_range_add _ 25 7
  have z1 : ∑ r ∈ range 7, T (64 * (j + 2) + (25 + r)) = 0 := Finset.sum_eq_zero fun r hr ↦ by
    have := mem_range.mp hr
    exact wordTerm_roundEmpty Ew sv ρ γ α (r := 25 + r) hj (by omega) (by omega) (by omega)
  have z2 : ∑ r ∈ range 7, T (64 * (j + 2) + (25 + (7 + (25 + r)))) = 0 := Finset.sum_eq_zero fun r hr ↦ by
    have := mem_range.mp hr
    exact wordTerm_roundEmpty Ew sv ρ γ α (r := 25 + (7 + (25 + r))) hj (by omega) (by omega) (by omega)
  rw [h1, h2, h3, z1, z2, zero_add, add_zero]
  refine congrArg₂ (· + ·) rfl ?_
  split_ifs with h23
  · refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl := mem_range.mp hl
    have e : stWord (j + 1) l = 64 * (j + 2) + (25 + (7 + l)) := by
      unfold stWord aWord
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      omega
    rw [e]
  · exact Finset.sum_eq_zero fun r hr ↦ by
      have := mem_range.mp hr
      exact wordTerm_roundEmpty Ew sv ρ γ α (r := 25 + (7 + r)) hj (by omega) (by omega) (by omega)

/-- **The walked form, class by class.** -/
theorem WF_eq : WF Ew sv ρ γ α =
    ∑ q ∈ range 32, ρ (4 * q + 1) * (Ew 0 * (sv 0 * γ 1 + α * (sv 0 * γ 1))) +
    (ρ (4 * 25 + 0) + ρ (4 * 25 + 3)) * (Ew 1 * (sv 0 * γ 1 + α * (sv 0 * γ 1))) +
    ∑ q ∈ range 25, ρ (4 * q + 2) * (corr Ew sv 0 * γ (4 * q + 2) + α * ((∑ z ∈ range 64, Ew z) * (sv 0 * γ 1))) +
    ∑ q ∈ range 25, ρ (4 * q + 3) * (corr Ew sv 0 * γ (4 * q) + α * ((∑ z ∈ range 64, Ew z) * (sv 0 * γ 1))) +
    ∑ j ∈ range 24, ∑ l ∈ range 25, ρ (tWord j l) * ((∑ z ∈ range 64, Ew z) * (sv 0 * γ 1) +
      bz Ew sv γ j ((l % 5 + 1) % 5 + 5 * (l / 5)) + α * bz Ew sv γ j ((l % 5 + 2) % 5 + 5 * (l / 5))) +
    ∑ j ∈ range 24, ∑ l ∈ range 25, ρ (stWord (j + 1) l) * (bz Ew sv γ j l +
      corr Ew sv 0 * γ (tWord j l) + (if l = 0 then RCw Ew j * (sv 0 * γ 1) else 0) +
      α * ((∑ z ∈ range 64, Ew z) * (sv 0 * γ 1))) := by
  set T := wordTerm Ew sv ρ γ α
  rw [WF_split, port_eq, Finset.sum_congr rfl fun j hj ↦ run_eq Ew sv ρ γ α (mem_range.mp hj),
    Finset.sum_add_distrib]
  -- The states of rounds 0..22 and the output port (round 23's) together.
  have hst : (∑ j ∈ range 24, if j < 23 then ∑ l ∈ range 25, T (stWord (j + 1) l) else 0) +
      ∑ q ∈ range 25, T (stWord 24 q) = ∑ j ∈ range 24, ∑ l ∈ range 25, T (stWord (j + 1) l) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ (n := 23)]
    simp only [lt_irrefl, ite_false, add_zero]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun j hj ↦ by rw [ite_eq_left (mem_range.mp hj)]) rfl
  have e : ∀ x y z u v w t : E, x + y + z + u + w + (v + t) = x + y + z + u + v + (t + w) :=
    fun _ _ _ _ _ _ _ ↦ by ring
  rw [e, hst]
  simp only [T]
  rw [wordTerm_x Ew sv ρ γ α (Or.inl rfl), wordTerm_x Ew sv ρ γ α (Or.inr rfl),
    Finset.sum_congr rfl fun q hq ↦ wordTerm_Y Ew sv ρ γ α (q := q) (mem_range.mp hq),
    Finset.sum_congr rfl fun q hq ↦ wordTerm_C Ew sv ρ γ α (q := q) (mem_range.mp hq),
    Finset.sum_congr rfl fun q hq ↦ wordTerm_V Ew sv ρ γ α (q := q) (mem_range.mp hq),
    Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun l hl ↦
      wordTerm_t Ew sv ρ γ α (mem_range.mp hj) (mem_range.mp hl),
    Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun l hl ↦
      wordTerm_A Ew sv ρ γ α (mem_range.mp hj) (mem_range.mp hl)]
  ring

end KeccakFlock.Core
