-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the prover's quotient parts on the coset are F1's numerator over `Z`, and `(X² + X) d d'`.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E`.
import E2ECompleteness.PcsHArrays

/-!
# The quotient's parts on the coset

For a circuit of `2^22` rows whose witness table's polynomial is `tablePoly c` (`hWc`) and whose wiring
polynomial is F1's `σ` polynomial (`hS`), at the coset point `xc i`:

* **`parts_fst`**: the first part is `N(x) / Z(x)`, `N = numer P0 … Hp (b₀ + b₁ X)` (`PcsKc3.lean`'s numerator, the
  sum's polynomial with its free blinding), `Z = w₂₄`;
* **`parts_snd`**: the second is `((X² + X) d d')(x)`.

`cellPoly_eval`: F1's polynomial of role `r` of a witness table's first message is the table's polynomial,
shifted by the role.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

namespace E2ECompleteness.Pcs.H

/-- **F1's polynomial of a role** of a witness table's first message is the table's polynomial, shifted. -/
theorem cellPoly_eval (P : _root_.Kc3.Params E) (c : (Fin 24 → Bool) → E) (r : Fin 4) (x : E) :
    (P.cellPoly (witnessOfTable (k := 22) c) r).eval x = (tablePoly c).eval (x + shift P.θ r) := by
  rw [← Completeness.witnessPoly_witnessOfTable_eval c]
  simp only [_root_.Kc3.Params.cellPoly, QuotientSecurity.Instance.witnessPoly, eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [P.rowPoly_eval_shift]

theorem getD_map_ofFn {β γ : Type} [Inhabited γ] {n : ℕ} (f : β → γ) (g : Fin n → β) {i : ℕ} (h : i < n) (d : γ) :
    ((Array.ofFn g).map f).getD i d = f (g ⟨i, h⟩) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_ofFn]
  simp [h]

theorem xc_xor {i c : ℕ} (hc : c < 4) : xc (i ^^^ c) = xc i + ofK (point c) := by
  rw [xc, xc, point_xor_low, ← Compose.Reduce.ofK_add, add_assoc]

variable (P : _root_.Kc3.Params E) (cir : Circuit) (cells₀ : Array K) (coins : Coins) (stmt : Statement)
  (α β μ : E) (c : (Fin 24 → Bool) → E)

/-- The numerator with the free blinding. -/
noncomputable def N0 : E[X] :=
  Kc3.Honest.numer P (Kc3Deployed.stmtOf stmt) (witnessOfTable (k := 22) c) α β μ (Hp cir cells₀ coins α β)
    (blindPoly coins)

/-- `E = (X² + X) d d'`. -/
noncomputable def Epoly : E[X] :=
  (X ^ 2 + X) * P.dPoly (witnessOfTable (k := 22) c) α β * P.dNextPoly (witnessOfTable (k := 22) c) α β

theorem ofK_point_role (hθ : P.θ = ofK (betaAt 1)) (r : Fin 4) : ofK (point r) = shift P.θ r := by
  fin_cases r
  · show ofK (point 0) = 0
    rw [point_zero, Compose.Reduce.ofK_zero]
  · show ofK (point 1) = 1
    rw [point_one, Compose.Reduce.ofK_one]
  · show ofK (point 2) = P.θ
    rw [point_two, hθ]
  · show ofK (point 3) = P.θ + 1
    rw [point_three, Compose.Reduce.ofK_add, Compose.Reduce.ofK_one, add_comm, hθ]

section Coset

variable (hθ : P.θ = ofK (betaAt 1)) (hl : cir.logRows = 22) (hw : (witnessParts cir cells₀ coins).2.size = 2 ^ 24)
  (hs : cir.wiringTable.size = 2 ^ 24) (hWc : Wp cir cells₀ coins = tablePoly c)
  (hS : ∀ t, (Sp cir).eval t = P.sigmaPoly.eval t)
include hθ hl hw hs hWc hS

theorem cellVars_cir : cellVars cir.logRows = 24 := by rw [hl]; rfl

/-- The witness values at `i ⊕ r` are F1's role `r` polynomial at `xc i`. -/
theorem wValues_role {i : ℕ} (hi : i < 2 ^ 26) (r : Fin 4) :
    ofK ((wValuesOf cir cells₀ coins).getD (i ^^^ (r : ℕ)) 0) =
      (P.cellPoly (witnessOfTable (k := 22) c) r).eval (xc i) := by
  have hr := r.2
  rw [wValues_getD cir cells₀ coins hl hw (Nat.xor_lt_two_pow hi (by omega)), hWc, cellPoly_eval,
    xc_xor (by omega), ofK_point_role P hθ]

theorem parts_snd {i : ℕ} (hi : i < 2 ^ 26) :
    ((partsOf cir stmt cells₀ coins α β μ).map (·.2)).getD i 0 = (Epoly P α β c).eval (xc i) := by
  have hn : i < 4 * 2 ^ cellVars cir.logRows := by
    rw [cellVars_cir P cir cells₀ coins c hθ hl hw hs hWc hS]; omega
  unfold partsOf
  rw [getD_map_ofFn _ _ hn]
  show ofK ((offsetOf cir + point i) * (offsetOf cir + point i) + (offsetOf cir + point i)) *
      (α + ofK ((wValuesOf cir cells₀ coins).getD i 0) + β * ofK (offsetOf cir + point i)) *
      (α + ofK ((wValuesOf cir cells₀ coins).getD i 0) + β * ofK ((sigmaValuesOf cir).getD i 0)) = _
  have h0 := wValues_role P cir cells₀ coins c hθ hl hw hs hWc hS hi 0
  rw [show ((0 : Fin 4) : ℕ) = 0 from rfl, Nat.xor_zero] at h0
  have hσ := sigmaValues_getD cir hl hs hi
  have hx : ofK (offsetOf cir + point i) = xc i := by
    rw [offsetOf, cellVars_cir P cir cells₀ coins c hθ hl hw hs hWc hS, xc, show (24 + 2 : ℕ) = 26 from rfl]
  rw [Compose.Reduce.ofK_add, Compose.Reduce.ofK_mul, hx, h0, hσ, hS, Epoly, Polynomial.eval_mul, Polynomial.eval_mul,
    _root_.Kc3.Params.dPoly, _root_.Kc3.Params.dNextPoly]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul]
  ring

variable (hZ : P.vCells = digitPoly 24) (hR : ∀ t, P.vRows.eval t = PcsBridge.Kc3.rowsAt t)
  (hpins : ∀ k : Fin 11, P.pinPt k = PcsBridge.Kc3.pinE k)
include hZ hR hpins

theorem rowPolyOf_eq (x : K) : rowPolyOf cir x = rowPolyAt 24 x := by
  unfold rowPolyOf rowPolyAt
  rw [cellVars_cir P cir cells₀ coins c hθ hl hw hs hWc hS]

set_option maxHeartbeats 400000 in
theorem parts_fst {i : ℕ} (hi : i < 2 ^ 26) :
    ((partsOf cir stmt cells₀ coins α β μ).map (·.1)).getD i 0 =
      (N0 P cir cells₀ coins stmt α β μ c).eval (xc i) / P.vCells.eval (xc i) := by
  have hm := cellVars_cir P cir cells₀ coins c hθ hl hw hs hWc hS
  have hn : i < 4 * 2 ^ cellVars cir.logRows := by rw [hm]; omega
  unfold partsOf
  rw [getD_map_ofFn _ _ hn]
  show ((hValuesOf cir cells₀ coins α β).getD i 0 *
        (α + ofK ((wValuesOf cir cells₀ coins).getD i 0) + β * ofK (offsetOf cir + point i)) *
        (α + ofK ((wValuesOf cir cells₀ coins).getD i 0) + β * ofK ((sigmaValuesOf cir).getD i 0)) +
        (α + ofK ((wValuesOf cir cells₀ coins).getD i 0) + β * ofK (offsetOf cir + point i)) +
        (α + ofK ((wValuesOf cir cells₀ coins).getD i 0) + β * ofK ((sigmaValuesOf cir).getD i 0))) *
      ofK ((chain (offsetOf cir + point i) (cellVars cir.logRows + 1)).getD (cellVars cir.logRows) 0)⁻¹ +
      μ * ofK (((wValuesOf cir cells₀ coins).getD (i ^^^ 3) 0 + (wValuesOf cir cells₀ coins).getD (i ^^^ 1) 0 +
          (wValuesOf cir cells₀ coins).getD (i ^^^ 2) 0 +
          (wValuesOf cir cells₀ coins).getD i 0 * (wValuesOf cir cells₀ coins).getD (i ^^^ 2) 0) *
        (rowPolyOf cir (offsetOf cir + point i))⁻¹ +
        ((wValuesOf cir cells₀ coins).getD i 0 + pinPolyOf stmt (offsetOf cir + point i)) *
        (zPinsOf (offsetOf cir + point i))⁻¹) = _
  -- the coset point
  have hx : ofK (offsetOf cir + point i) = xc i := by
    rw [offsetOf, hm, xc, show (24 + 2 : ℕ) = 26 from rfl]
  have hZx : P.vCells.eval (xc i) ≠ 0 := by rw [hZ, digitPoly_eval]; exact zc_ne_zero hi
  have hRZ : P.vRows.eval (xc i) * P.cofRows.eval (xc i) = P.vCells.eval (xc i) := by
    rw [← Polynomial.eval_mul, P.vRows_mul_cofRows]
  have hPZ : P.vPins.eval (xc i) * P.cofPins.eval (xc i) = P.vCells.eval (xc i) := by
    rw [← Polynomial.eval_mul, P.vPins_mul_cofPins]
  have hRx : P.vRows.eval (xc i) ≠ 0 := fun h => hZx (by rw [← hRZ, h, zero_mul])
  have hPx : P.vPins.eval (xc i) ≠ 0 := fun h => hZx (by rw [← hPZ, h, zero_mul])
  have hpk : ∀ k < 11, xc i + PcsBridge.Kc3.pinE k ≠ 0 := by
    intro k hk h0
    apply hPx
    unfold _root_.Kc3.Params.vPins
    rw [Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨k, hk⟩) ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hpins, CharTwo.sub_eq_add]
    exact h0
  -- the values
  have h0 := wValues_role P cir cells₀ coins c hθ hl hw hs hWc hS hi 0
  have h1 := wValues_role P cir cells₀ coins c hθ hl hw hs hWc hS hi 1
  have h2 := wValues_role P cir cells₀ coins c hθ hl hw hs hWc hS hi 2
  have h3 := wValues_role P cir cells₀ coins c hθ hl hw hs hWc hS hi 3
  rw [show ((0 : Fin 4) : ℕ) = 0 from rfl, Nat.xor_zero] at h0
  rw [show ((1 : Fin 4) : ℕ) = 1 from rfl] at h1
  rw [show ((2 : Fin 4) : ℕ) = 2 from rfl] at h2
  rw [show ((3 : Fin 4) : ℕ) = 3 from rfl] at h3
  have hσ := sigmaValues_getD cir hl hs hi
  rw [hS] at hσ
  have hh := hValues_getD cir cells₀ coins α β hl hi
  have hz : ofK ((chain (offsetOf cir + point i) (cellVars cir.logRows + 1)).getD (cellVars cir.logRows) 0) =
      P.vCells.eval (xc i) := by
    rw [hm, chain_ofK, hx, hZ, digitPoly_eval]
  have hr : ofK (rowPolyOf cir (offsetOf cir + point i)) = P.vRows.eval (xc i) := by
    rw [rowPolyOf_eq P cir cells₀ coins c hθ hl hw hs hWc hS hZ hR hpins, rowPolyAt_ofK, hx, hR]
  have hp : ofK (((wValuesOf cir cells₀ coins).getD i 0 + pinPolyOf stmt (offsetOf cir + point i)) *
      (zPinsOf (offsetOf cir + point i))⁻¹) =
      ((P.cellPoly (witnessOfTable (k := 22) c) 0).eval (xc i) +
        (P.pinPoly (Kc3Deployed.stmtOf stmt)).eval (xc i)) / P.vPins.eval (xc i) := by
    rw [pinTerm_ofK stmt _ _ (by rw [hx]; exact hpk), hx, h0,
      ← PcsBridge.Kc3.pinned_eq P hpins stmt (xc i) _ hpk]
    rfl
  have hzi : ofK ((chain (offsetOf cir + point i) (cellVars cir.logRows + 1)).getD (cellVars cir.logRows) 0)⁻¹ =
      (P.vCells.eval (xc i))⁻¹ := by
    rw [PcsBridge.Kc3.ofK_inv, hz]
  have hg : ofK (((wValuesOf cir cells₀ coins).getD (i ^^^ 3) 0 + (wValuesOf cir cells₀ coins).getD (i ^^^ 1) 0 +
          (wValuesOf cir cells₀ coins).getD (i ^^^ 2) 0 +
          (wValuesOf cir cells₀ coins).getD i 0 * (wValuesOf cir cells₀ coins).getD (i ^^^ 2) 0) *
        (rowPolyOf cir (offsetOf cir + point i))⁻¹ +
        ((wValuesOf cir cells₀ coins).getD i 0 + pinPolyOf stmt (offsetOf cir + point i)) *
        (zPinsOf (offsetOf cir + point i))⁻¹) =
      ((P.cellPoly (witnessOfTable (k := 22) c) 3).eval (xc i) + (P.cellPoly (witnessOfTable (k := 22) c) 1).eval (xc i) +
        (P.cellPoly (witnessOfTable (k := 22) c) 2).eval (xc i) +
        (P.cellPoly (witnessOfTable (k := 22) c) 0).eval (xc i) * (P.cellPoly (witnessOfTable (k := 22) c) 2).eval (xc i)) /
        P.vRows.eval (xc i) +
      ((P.cellPoly (witnessOfTable (k := 22) c) 0).eval (xc i) +
        (P.pinPoly (Kc3Deployed.stmtOf stmt)).eval (xc i)) / P.vPins.eval (xc i) := by
    rw [Compose.Reduce.ofK_add _ (_ * _), hp, Compose.Reduce.ofK_mul, PcsBridge.Kc3.ofK_inv, hr,
      Compose.Reduce.ofK_add, Compose.Reduce.ofK_add, Compose.Reduce.ofK_add, Compose.Reduce.ofK_mul, h0, h1, h2, h3]
    simp only [div_eq_mul_inv]
  have hd : ofK (offsetOf cir) + ofK (point i) = xc i := by rw [← Compose.Reduce.ofK_add, hx]
  rw [hzi, hg, hh, h0, hσ]
  simp only [Compose.Reduce.ofK_add, hd]
  -- the numerator
  have hcofR : P.cofRows.eval (xc i) = P.vCells.eval (xc i) / P.vRows.eval (xc i) := by
    rw [← hRZ, mul_div_cancel_left₀ _ hRx]
  have hcofP : P.cofPins.eval (xc i) = P.vCells.eval (xc i) / P.vPins.eval (xc i) := by
    rw [← hPZ, mul_div_cancel_left₀ _ hPx]
  rw [N0, Kc3.Honest.numer]
  rw [_root_.Kc3.Params.zgPoly, _root_.Kc3.Params.gatePoly, _root_.Kc3.Params.dPoly, _root_.Kc3.Params.dNextPoly]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, _root_.Kc3.gate_eval, Polynomial.eval_X,
    hcofR, hcofP]
  simp only [_root_.Kc3.gate]
  rw [← hZ]
  generalize Polynomial.eval (xc i) P.vCells = Zx at hZx ⊢
  generalize Polynomial.eval (xc i) P.vRows = Rx at hRx ⊢
  generalize Polynomial.eval (xc i) P.vPins = Px at hPx ⊢
  generalize Polynomial.eval (xc i) (P.cellPoly (witnessOfTable (k := 22) c) 0) = w0
  generalize Polynomial.eval (xc i) (P.cellPoly (witnessOfTable (k := 22) c) 1) = w1
  generalize Polynomial.eval (xc i) (P.cellPoly (witnessOfTable (k := 22) c) 2) = w2
  generalize Polynomial.eval (xc i) (P.cellPoly (witnessOfTable (k := 22) c) 3) = w3
  generalize Polynomial.eval (xc i) P.sigmaPoly = sv
  generalize Polynomial.eval (xc i) (Hp cir cells₀ coins α β) = hv
  generalize Polynomial.eval (xc i) (blindPoly coins) = bv
  generalize Polynomial.eval (xc i) (P.pinPoly (Kc3Deployed.stmtOf stmt)) = pv
  generalize xc i = x
  rw [eq_div_iff hZx]
  field_simp

end Coset

end E2ECompleteness.Pcs.H
