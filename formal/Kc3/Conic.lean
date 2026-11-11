-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The conic of the witness claim, `docs/membership/PROTOCOL.md` ("The witness claim binds three values"), for
-- `crates/membership/quotient/src/protocol.rs`'s `witness_conic` and `witness_weights`.
import Kc3.Protocol

/-!
# The witness claim's conic

The witness claim is the witness table at the row point `(z₀, z₁) = (ρ, a / (a + b))` (`conic`), whose weights on
the four row polynomials' values are `e = (1 + z₀, z₀) ⊗ (1 + z₁, z₁)` (`rowWeights`). The verifier reads the row
through three values, `X`, `C` and `V + Y` (`rowVals`, three linear forms of the row polynomials' values), and
weighs them by `λ` (`conicWeights`):

* `conic_identity`: `e · a = λ · (X, C, V + Y)` for every row (when `a + b ≠ 0`): the claim is the three values';
* `conic_poly`: `(a + b) λ · Δ` is the polynomial `c₀ + c₁ ρ + c₂ ρ²` (`conicCoeffs`), and `conicCoeffs_ne_zero`: not
  all three coefficients vanish when `Δ ≠ 0` (the conic spans its plane: `(a + b) e` runs over the independent
  quadratics `θ (1 + ρ²)`, `s + ρ + (s + 1) ρ²`, `s ρ + (s + 1) ρ²`, `s = t + θ ω`). So a claimed triple other
  than the row's passes for at most two `ρ` (`card_conic_le`).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Kc3

open Params

variable {F : Type*} [Field F] [CharP F 2]

/-- A numeral of a ring of characteristic two is its parity. -/
theorem ofNat_char2 (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : F) = (((OfNat.ofNat n : ℕ) % 2 : ℕ) : F) := by
  rw [← CharP.cast_eq_mod F 2]; exact (Nat.cast_ofNat).symm

/-- A ring identity in characteristic two: normalized, then every numeral read by its parity. -/
macro "char2_norm" : tactic => `(tactic| (ring_nf; simp only [ofNat_char2, Nat.reduceMod, Nat.cast_zero,
  Nat.cast_one, mul_zero, zero_mul, mul_one, neg_zero, add_zero, zero_add, sub_zero, zero_sub, sub_self]))

/-- The three values `X`, `C`, `V + Y` of a row as linear forms of its row polynomials' values `a` at `t`
(`ω = t² + t`; the cells at `t`, `t + 1`, `t + θ`, `t + θ + 1` when `θ² + θ + 1 = 0`). -/
def rowVals (θ t : F) (a : Fin 4 → F) : Fin 3 → F :=
  let ω := t * t + t
  ![a 0 + t * a 1 + ω * a 2 + ω * t * a 3,
    a 0 + (t + θ) * a 1 + (ω + 1) * a 2 + (ω + 1) * (t + θ) * a 3,
    θ * a 1 + a 2 + (t + θ * ω + θ + 1) * a 3]

/-- `a + b`, the witness claim's row point's denominator. -/
def conicDen (θ t ρ : F) : F := (conic θ t ρ).1 + (conic θ t ρ).2

/-- The row point's second coordinate `z₁ = a / (a + b)`. -/
noncomputable def conicZ (θ t ρ : F) : F := (conic θ t ρ).1 / conicDen θ t ρ

theorem conicDen_eq (θ t ρ : F) :
    conicDen θ t ρ = (t + (t * t + t) * θ) * (1 + ρ) + ρ + θ * (1 + ρ) := rfl

theorem conicZ_mul (θ t ρ : F) (hD : conicDen θ t ρ ≠ 0) :
    conicZ θ t ρ * conicDen θ t ρ = (t + (t * t + t) * θ) * (1 + ρ) + ρ := by
  rw [conicZ, div_mul_cancel₀ _ hD]; rfl

set_option maxRecDepth 100000 in
/-- **The claim is the three values'**: `e · a = λ · (X, C, V + Y)`. -/
theorem conic_identity (θ t ρ : F) (a : Fin 4 → F) (hD : conicDen θ t ρ ≠ 0) :
    ∑ j, rowWeights ρ (conicZ θ t ρ) j * a j =
      ∑ k, conicWeights θ t ρ (conicZ θ t ρ) k * rowVals θ t a k := by
  have hz := conicZ_mul θ t ρ hD
  rw [conicDen_eq] at hz
  generalize conicZ θ t ρ = z at hz ⊢
  simp only [Fin.sum_univ_four, Fin.sum_univ_three, rowWeights, conicWeights, rowVals, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val,
    Matrix.tail_cons]
  linear_combination (norm := char2_norm) (a 1) * hz

/-- The coefficients of `(a + b) λ · Δ` as a polynomial in `ρ`. -/
def conicCoeffs (θ t : F) (Δ : Fin 3 → F) : F × F × F :=
  let ω := t * t + t
  let s := t + θ * ω
  let k3 := t + θ * ω + θ + 1
  let W := Δ 0 + Δ 1 + Δ 2
  let V := Δ 2 + k3 * W
  let U := Δ 0 + ω * Δ 2 + (t * ω + k3 * ω) * W
  (θ * U + s * V, V + s * W, θ * U + (s + 1) * V + (s + 1) * W)

set_option maxRecDepth 100000 in
/-- **`(a + b) λ · Δ = c₀ + c₁ ρ + c₂ ρ²`.** -/
theorem conic_poly (θ t ρ : F) (Δ : Fin 3 → F) (hD : conicDen θ t ρ ≠ 0) :
    conicDen θ t ρ * ∑ k, conicWeights θ t ρ (conicZ θ t ρ) k * Δ k =
      (conicCoeffs θ t Δ).1 + (conicCoeffs θ t Δ).2.1 * ρ + (conicCoeffs θ t Δ).2.2 * ρ ^ 2 := by
  have hz := conicZ_mul θ t ρ hD
  rw [conicDen_eq] at hz ⊢
  generalize conicZ θ t ρ = z at hz ⊢
  simp only [Fin.sum_univ_three, conicWeights, conicCoeffs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.cons_val, Matrix.tail_cons]
  linear_combination (norm := char2_norm)
    ((1 + ρ) * Δ 0 + (1 + ρ) * (1 + (t * t + t)) * Δ 2 +
      (ρ + (1 + ρ) * (t * (t * t + t) + (t + θ * (t * t + t) + θ + 1) * (1 + (t * t + t)))) *
        (Δ 0 + Δ 1 + Δ 2)) * hz

theorem theta_ne_zero {θ : F} (hθ : θ * θ + θ + 1 = 0) : θ ≠ 0 := by
  intro h
  rw [h] at hθ
  simp at hθ

/-- **The conic spans its plane**: `(a + b) λ · Δ` is not the zero polynomial when `Δ ≠ 0`. -/
theorem conicCoeffs_ne_zero {θ : F} (hθ : θ * θ + θ + 1 = 0) (t : F) {Δ : Fin 3 → F} (hΔ : Δ ≠ 0) :
    conicCoeffs θ t Δ ≠ (0, 0, 0) := by
  intro h
  simp only [conicCoeffs, Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2⟩ := h
  generalize hW : Δ 0 + Δ 1 + Δ 2 = W at h0 h1 h2
  generalize hV : Δ 2 + (t + θ * (t * t + t) + θ + 1) * W = V at h0 h1 h2
  generalize hU : Δ 0 + (t * t + t) * Δ 2 + (t * (t * t + t) + (t + θ * (t * t + t) + θ + 1) * (t * t + t)) * W = U
    at h0 h1 h2
  have hW0 : W = 0 := by linear_combination (norm := char2_norm) h0 + h1 + h2
  have hV0 : V = 0 := by rw [hW0] at h1; simpa using h1
  have hU0 : U = 0 := by
    rw [hV0, mul_zero, add_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left (theta_ne_zero hθ)
  apply hΔ
  have d2 : Δ 2 = 0 := by rw [hW0, hV0, mul_zero, add_zero] at hV; exact hV
  have d0 : Δ 0 = 0 := by rw [hW0, hU0, d2] at hU; simpa using hU
  have d1 : Δ 1 = 0 := by rw [hW0, d0, d2] at hW; simpa using hW
  funext k
  fin_cases k <;> simp [d0, d1, d2]

variable [DecidableEq F] [Fintype F]

open Classical in
/-- **A claimed triple other than the row's passes the witness claim for at most two `ρ`.** -/
theorem card_conic_le {θ : F} (hθ : θ * θ + θ + 1 = 0) (t : F) (a : Fin 4 → F) (v : Fin 3 → F)
    (hv : v ≠ rowVals θ t a) :
    (univ.filter fun ρ : F => conicDen θ t ρ ≠ 0 ∧
      ∑ j, rowWeights ρ (conicZ θ t ρ) j * a j = ∑ k, conicWeights θ t ρ (conicZ θ t ρ) k * v k).card ≤ 2 := by
  set Δ : Fin 3 → F := fun k => v k + rowVals θ t a k with hΔ
  have hΔ0 : Δ ≠ 0 := by
    intro h
    apply hv
    funext k
    exact CharTwo.add_eq_zero.mp (congrFun h k)
  set c := conicCoeffs θ t Δ
  set Q : F[X] := C c.1 + C c.2.1 * X + C c.2.2 * X ^ 2 with hQ
  have hQ0 : Q ≠ 0 := by
    intro h0
    apply conicCoeffs_ne_zero hθ t hΔ0
    have e0 := congrArg (fun p : F[X] => p.coeff 0) h0
    have e1 := congrArg (fun p : F[X] => p.coeff 1) h0
    have e2 := congrArg (fun p : F[X] => p.coeff 2) h0
    simp only [hQ, coeff_add, coeff_C_mul, coeff_C, coeff_X_pow, coeff_X, coeff_zero] at e0 e1 e2
    norm_num at e0 e1 e2
    show c = (0, 0, 0)
    exact Prod.ext e0 (Prod.ext e1 e2)
  have hdeg : Q.natDegree ≤ 2 := by rw [hQ]; compute_degree
  calc _ ≤ Q.roots.toFinset.card := Finset.card_le_card fun ρ hρ => by
        rw [Finset.mem_filter] at hρ
        obtain ⟨-, hD, heq⟩ := hρ
        rw [Multiset.mem_toFinset, mem_roots hQ0, IsRoot.def]
        have hid := conic_identity θ t ρ a hD
        have hsum : ∑ k, conicWeights θ t ρ (conicZ θ t ρ) k * Δ k = 0 := by
          simp only [hΔ, mul_add, Finset.sum_add_distrib]
          rw [← heq, ← hid]
          exact CharTwo.add_self_eq_zero _
        have hp := conic_poly θ t ρ Δ hD
        rw [hsum, mul_zero] at hp
        simp only [hQ, eval_add, eval_mul, eval_C, eval_X, eval_pow]
        exact hp.symm
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := card_roots' Q
    _ ≤ 2 := hdeg

end Kc3
