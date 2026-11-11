-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the prover's quotient `q` (`quotientParts`) is F1's honest quotient, `(q /ₘ Z)(0) = 0` by `b₂`.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E`.
import E2ECompleteness.PcsHParts

/-!
# The prover's quotient

With `PcsHParts.lean`'s hypotheses, `Z = w₂₄` dividing the numerator `N₀` (`hdvd`), `N₀` of degree below `3 · 2^24`
and `γ = (E /ₘ Z)(0) ≠ 0` (`E = (X² + X) d d'`):

* `coset_ext`: polynomials of degree below `2^26` that agree on the coset are equal;
* `q0Hat_nov`, `eHat_nov`: the coefficient tables `q0Hat`, `eHat` hold `Q₀ = N₀ /ₘ Z` and `E`;
* **`qHat_spec`**: `q = nov 0 26 qHat` has `Z q = numer … Hp (b₀ + b₁ X + b₂ (X² + X))` (`PcsKc3.lean`'s numerator
  with the whole blinding) and `(q /ₘ Z)(0) = 0`; its entries vanish past `2^25`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

namespace E2ECompleteness.Pcs.H

/-! ## The coset determines a polynomial of degree below `2^26` -/

theorem ofK_injective : Function.Injective (fun a : K => (ofK a : E)) := (algebraMap K E).injective

theorem xc_injective {i j : ℕ} (hi : i < 2 ^ 26) (hj : j < 2 ^ 26) (h : xc i = xc j) : i = j := by
  have h1 : betaAt 26 + point i = betaAt 26 + point j := ofK_injective h
  have h2 : point i = point j := add_left_cancel h1
  have hB := cantorUpTo (m := 26) (by norm_num)
  rw [E2ECompleteness.Pcs.Ntt.point_eq_cantor hB (by unfold basisSize; norm_num) hi,
    E2ECompleteness.Pcs.Ntt.point_eq_cantor hB (by unfold basisSize; norm_num) hj] at h2
  have h3 := (Bridge.Ntt.cantorOf hB).point_injective le_rfl h2
  rw [← Completeness.idx_bitsOf 26 i hi, ← Completeness.idx_bitsOf 26 j hj, h3]

theorem coset_ext_gen (N : ℕ) (hN : N ≤ 2 ^ 26) {p q : E[X]} (hp : p.natDegree < N) (hq : q.natDegree < N)
    (h : ∀ i < N, p.eval (xc i) = q.eval (xc i)) : p = q := by
  rw [← sub_eq_zero]
  have hinj : Function.Injective (fun i : Fin N => xc (i : ℕ)) := fun a b hab =>
    Fin.ext (xc_injective (lt_of_lt_of_le a.2 hN) (lt_of_lt_of_le b.2 hN) hab)
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p - q) hinj (fun i => ?_) ?_
  · rw [Polynomial.eval_sub, h i i.2, sub_self]
  · rw [Fintype.card_fin]
    exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hp hq)

theorem coset_ext {p q : E[X]} (hp : p.natDegree < 2 ^ 26) (hq : q.natDegree < 2 ^ 26)
    (h : ∀ i < 2 ^ 26, p.eval (xc i) = q.eval (xc i)) : p = q :=
  coset_ext_gen (2 ^ 26) le_rfl hp hq h

/-- A polynomial of degree at most `2^k` on `k + 1` digits: its high half is constant. -/
theorem nov_high_const (k : ℕ) (f : ℕ → E) (h : (Novel.nov 0 (k + 1) f).natDegree ≤ 2 ^ k) :
    ∀ j, 0 < j → j < 2 ^ k → f (2 ^ k + j) = 0 := by
  rw [Novel.nov_split] at h
  set H := Novel.nov 0 k fun j => f (2 ^ k + j) with hH
  have hL := Novel.natDegree_nov_lt k f
  have hH0 : H.natDegree = 0 := by
    by_contra hne
    have hHne : H ≠ 0 := fun h0 => hne (by rw [h0, natDegree_zero])
    have hdeg : (digitPoly k * H).natDegree = 2 ^ k + H.natDegree := by
      rw [(Novel.digit_monic k).natDegree_mul' hHne, Novel.digit_natDegree]
    have hsum : (Novel.nov 0 k f + digitPoly k * H).natDegree = 2 ^ k + H.natDegree := by
      rw [natDegree_add_eq_right_of_natDegree_lt (by omega), hdeg]
    omega
  have hC : H = C (f (2 ^ k)) := by
    rw [eq_C_of_natDegree_eq_zero hH0, coeff_zero_eq_eval_zero, hH, Novel.nov_eval_zero, add_zero]
  have hS : H = Novel.nov 0 k (fun j => if j = 0 then f (2 ^ k) else 0) := by
    rw [hC, Novel.nov_single k _ (fun j hj _ => by rw [if_neg (by omega)]), if_pos rfl]
  intro j hj hjk
  have := Novel.nov_inj k hS j hjk
  rw [this, if_neg (by omega)]

theorem nov_smul (k : ℕ) (b : E) (f : ℕ → E) : Novel.nov 0 k (fun j => b * f j) = C b * Novel.nov 0 k f := by
  simp only [Novel.nov, C_mul, Finset.mul_sum, mul_assoc]

theorem numer_add_blind {F : Type*} [Field F] [DecidableEq F] [CharP F 2] (P : _root_.Kc3.Params F)
    (S : _root_.Kc3.Params.Stmt F) (g : Fin 4 → F[X]) (α β μ : F) (h ε : F[X]) (e : F) :
    Kc3.Honest.numer P S g α β μ h ε + P.vCells * (C e * ((X ^ 2 + X) * P.dPoly g α β * P.dNextPoly g α β)) =
      Kc3.Honest.numer P S g α β μ h (ε + C e * (X ^ 2 + X)) := by
  unfold Kc3.Honest.numer
  ring

/-! ## The coefficient tables -/

variable (P : _root_.Kc3.Params E) (cir : Circuit) (cells₀ : Array K) (coins : Coins) (stmt : Statement)
  (α β μ : E) (c : (Fin 24 → Bool) → E)

theorem partsOf_size : (partsOf cir stmt cells₀ coins α β μ).size = 4 * 2 ^ cellVars cir.logRows := by
  unfold partsOf; rw [Array.size_ofFn]

theorem q0Hat_eval (hl : cir.logRows = 22) {i : ℕ} (hi : i < 2 ^ 26) :
    (Novel.nov 0 26 fun j => (q0HatOf cir stmt cells₀ coins α β μ).getD j 0).eval (xc i) =
      ((partsOf cir stmt cells₀ coins α β μ).map (·.1)).getD i 0 := by
  have hm : cellVars cir.logRows = 24 := by rw [hl]; rfl
  have hsz : ((partsOf cir stmt cells₀ coins α β μ).map (·.1)).size = 2 ^ (cellVars cir.logRows + 2) := by
    rw [Array.size_map, partsOf_size, pow_add]; ring
  have h := nov_coefficients (m := cellVars cir.logRows + 2) (by rw [hm]; norm_num) (offsetOf cir) _ hsz
    (by rw [hm]; exact hi)
  have e : coefficients (cellVars cir.logRows + 2) (offsetOf cir)
      ((partsOf cir stmt cells₀ coins α β μ).map (·.1)) = q0HatOf cir stmt cells₀ coins α β μ := by
    unfold q0HatOf; rfl
  rw [e, offsetOf, hm] at h
  rw [xc]
  exact h

theorem eHat_eval (hl : cir.logRows = 22) {i : ℕ} (hi : i < 2 ^ 26) :
    (Novel.nov 0 26 fun j => (eHatOf cir stmt cells₀ coins α β μ).getD j 0).eval (xc i) =
      ((partsOf cir stmt cells₀ coins α β μ).map (·.2)).getD i 0 := by
  have hm : cellVars cir.logRows = 24 := by rw [hl]; rfl
  have hsz : ((partsOf cir stmt cells₀ coins α β μ).map (·.2)).size = 2 ^ (cellVars cir.logRows + 2) := by
    rw [Array.size_map, partsOf_size, pow_add]; ring
  have h := nov_coefficients (m := cellVars cir.logRows + 2) (by rw [hm]; norm_num) (offsetOf cir) _ hsz
    (by rw [hm]; exact hi)
  have e : coefficients (cellVars cir.logRows + 2) (offsetOf cir)
      ((partsOf cir stmt cells₀ coins α β μ).map (·.2)) = eHatOf cir stmt cells₀ coins α β μ := by
    unfold eHatOf; rfl
  rw [e, offsetOf, hm] at h
  rw [xc]
  exact h

section Quot

variable (hθ : P.θ = ofK (betaAt 1)) (hl : cir.logRows = 22) (hw : (witnessParts cir cells₀ coins).2.size = 2 ^ 24)
  (hs : cir.wiringTable.size = 2 ^ 24) (hWc : Wp cir cells₀ coins = tablePoly c)
  (hS : ∀ t, (Sp cir).eval t = P.sigmaPoly.eval t)
  (hZ : P.vCells = digitPoly 24) (hR : ∀ t, P.vRows.eval t = PcsBridge.Kc3.rowsAt t)
  (hpins : ∀ k : Fin 11, P.pinPt k = PcsBridge.Kc3.pinE k)
  (hdvd : P.vCells ∣ N0 P cir cells₀ coins stmt α β μ c)
  (hdegN : (N0 P cir cells₀ coins stmt α β μ c).natDegree < 3 * 2 ^ 24)
  (hdegE : (Epoly P α β c).natDegree ≤ 2 ^ 25)
include hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE

/-- `Q₀ = N₀ / Z`. -/
noncomputable def Q0 : E[X] := N0 P cir cells₀ coins stmt α β μ c /ₘ P.vCells

theorem Z_mul_Q0 : P.vCells * Q0 P cir cells₀ coins stmt α β μ c = N0 P cir cells₀ coins stmt α β μ c := by
  have hmon : P.vCells.Monic := by rw [hZ]; exact Novel.digit_monic 24
  have h0 : N0 P cir cells₀ coins stmt α β μ c %ₘ P.vCells = 0 := (modByMonic_eq_zero_iff_dvd hmon).mpr hdvd
  have := modByMonic_add_div (N0 P cir cells₀ coins stmt α β μ c) P.vCells
  rw [h0, zero_add] at this
  exact this

theorem natDegree_Q0 : (Q0 P cir cells₀ coins stmt α β μ c).natDegree < 2 ^ 25 := by
  have hmon : P.vCells.Monic := by rw [hZ]; exact Novel.digit_monic 24
  rw [Q0, natDegree_divByMonic _ hmon, hZ, Novel.digit_natDegree]
  omega

theorem q0Hat_nov :
    (Novel.nov 0 26 fun j => (q0HatOf cir stmt cells₀ coins α β μ).getD j 0) = Q0 P cir cells₀ coins stmt α β μ c := by
  refine coset_ext (Novel.natDegree_nov_lt 26 _)
    (lt_of_lt_of_le (natDegree_Q0 P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE)
      (by norm_num)) fun i hi => ?_
  rw [q0Hat_eval cir cells₀ coins stmt α β μ hl hi,
    parts_fst P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hi,
    ← Z_mul_Q0 P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE,
    Polynomial.eval_mul, mul_div_cancel_left₀]
  rw [hZ, digitPoly_eval]
  exact zc_ne_zero hi

theorem eHat_nov : (Novel.nov 0 26 fun j => (eHatOf cir stmt cells₀ coins α β μ).getD j 0) = Epoly P α β c := by
  refine coset_ext (Novel.natDegree_nov_lt 26 _) (lt_of_le_of_lt hdegE (by norm_num)) fun i hi => ?_
  rw [eHat_eval cir cells₀ coins stmt α β μ hl hi, parts_snd P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hi]

theorem q0Hat_high {j : ℕ} (h1 : 2 ^ 25 ≤ j) (h2 : j < 2 ^ 26) : (q0HatOf cir stmt cells₀ coins α β μ).getD j 0 = 0 := by
  have hd := natDegree_Q0 P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE
  rw [← q0Hat_nov P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE] at hd
  have := Novel.nov_high_zero 25 _ hd (j - 2 ^ 25) (by omega)
  rwa [show 2 ^ 25 + (j - 2 ^ 25) = j by omega] at this

theorem eHat_high {j : ℕ} (h1 : 2 ^ 25 < j) (h2 : j < 2 ^ 26) : (eHatOf cir stmt cells₀ coins α β μ).getD j 0 = 0 := by
  have hd := hdegE
  rw [← eHat_nov P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE] at hd
  have := nov_high_const 25 _ hd (j - 2 ^ 25) (by omega) (by omega)
  rwa [show 2 ^ 25 + (j - 2 ^ 25) = j by omega] at this

/-- `γ = e[n] + e[2n]` is `(E /ₘ Z)(0)`. -/
theorem gamma_eq : (eHatOf cir stmt cells₀ coins α β μ).getD (2 ^ 24) 0 + (eHatOf cir stmt cells₀ coins α β μ).getD (2 ^ 25) 0 =
    (Epoly P α β c /ₘ P.vCells).eval 0 := by
  rw [← eHat_nov P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE, hZ]
  exact (Novel.nov_divByMonic_eval_zero 24 _ fun j h1 h2 =>
    eHat_high P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE h1 h2).symm

theorem b2_eq : b2Of cir stmt cells₀ coins α β μ =
    (q0HatOf cir stmt cells₀ coins α β μ).getD (2 ^ 24) 0 *
      ((eHatOf cir stmt cells₀ coins α β μ).getD (2 ^ 24) 0 + (eHatOf cir stmt cells₀ coins α β μ).getD (2 ^ 25) 0)⁻¹ := by
  have hm : cellVars cir.logRows = 24 := by rw [hl]; rfl
  unfold b2Of
  rw [hm, show (2 * 2 ^ 24 : ℕ) = 2 ^ 25 from rfl]

theorem qHat_getD {j : ℕ} (hj : j < 2 ^ 26) : (qHatOf cir stmt cells₀ coins α β μ).getD j 0 =
    (q0HatOf cir stmt cells₀ coins α β μ).getD j 0 + b2Of cir stmt cells₀ coins α β μ * (eHatOf cir stmt cells₀ coins α β μ).getD j 0 := by
  have hm : cellVars cir.logRows = 24 := by rw [hl]; rfl
  by_cases hjn : j < 2 * 2 ^ cellVars cir.logRows + 1
  · unfold qHatOf
    rw [getD_ofFn _ hjn]
  · have hsz : (qHatOf cir stmt cells₀ coins α β μ).size = 2 * 2 ^ cellVars cir.logRows + 1 := by
      unfold qHatOf; rw [Array.size_ofFn]
    rw [getD_ge _ _ (by omega)]
    rw [hm] at hjn
    rw [q0Hat_high P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE (by omega) hj,
      eHat_high P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE (by omega) hj,
      mul_zero, add_zero]

/-- The honest quotient `q`. -/
noncomputable def Qp : E[X] := Novel.nov 0 26 fun j => (qHatOf cir stmt cells₀ coins α β μ).getD j 0

theorem Qp_eq : Qp cir cells₀ coins stmt α β μ =
    Q0 P cir cells₀ coins stmt α β μ c + C (b2Of cir stmt cells₀ coins α β μ) * Epoly P α β c := by
  rw [Qp, Novel.nov_congr 0 26 fun j hj =>
      qHat_getD P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE hj,
    Novel.nov_add, nov_smul, q0Hat_nov P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE,
    eHat_nov P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE]

/-- **`Z q` is the numerator with the whole blinding.** -/
theorem Z_mul_Qp : P.vCells * Qp cir cells₀ coins stmt α β μ =
    Kc3.Honest.numer P (Kc3Deployed.stmtOf stmt) (witnessOfTable (k := 22) c) α β μ (Hp cir cells₀ coins α β)
      (blindPoly coins + C (b2Of cir stmt cells₀ coins α β μ) * (X ^ 2 + X)) := by
  rw [Qp_eq P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE, mul_add,
    Z_mul_Q0 P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE, N0, Epoly]
  exact numer_add_blind P _ _ α β μ _ _ _

theorem Qp_entries {j : ℕ} (h1 : 2 ^ 25 < j) (h2 : j < 2 ^ 26) : (qHatOf cir stmt cells₀ coins α β μ).getD j 0 = 0 := by
  rw [qHat_getD P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE h2,
    q0Hat_high P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE (by omega) h2,
    eHat_high P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE h1 h2, mul_zero, add_zero]

/-- **`b₂` makes `(q /ₘ Z)(0)` vanish**, where `γ = (E /ₘ Z)(0)` does not. -/
theorem Qp_div_eval_zero (hγ : (Epoly P α β c /ₘ P.vCells).eval 0 ≠ 0) :
    (Qp cir cells₀ coins stmt α β μ /ₘ P.vCells).eval 0 = 0 := by
  rw [Qp, hZ, Novel.nov_divByMonic_eval_zero 24 _ fun j h1 h2 =>
      Qp_entries P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE h1 h2,
    qHat_getD P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE (by norm_num),
    qHat_getD P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE (by norm_num),
    q0Hat_high P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE le_rfl (by norm_num),
    b2_eq P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE]
  have hg := gamma_eq P cir cells₀ coins stmt α β μ c hθ hl hw hs hWc hS hZ hR hpins hdvd hdegN hdegE
  rw [← hg] at hγ
  generalize (eHatOf cir stmt cells₀ coins α β μ).getD (2 ^ 24) 0 = e1 at hγ ⊢
  generalize (eHatOf cir stmt cells₀ coins α β μ).getD (2 ^ 25) 0 = e2 at hγ ⊢
  generalize (q0HatOf cir stmt cells₀ coins α β μ).getD (2 ^ 24) 0 = q1
  have : q1 * (e1 + e2)⁻¹ * e1 + q1 * (e1 + e2)⁻¹ * e2 = q1 := by
    rw [← mul_add, inv_mul_cancel_right₀ hγ]
  linear_combination (norm := char2_norm) this

end Quot

end E2ECompleteness.Pcs.H
