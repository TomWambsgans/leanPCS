-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecStatement.Lemmas.Phi

/-!
# The verifier's checks and claims are `RecPiop`'s state after `ρ` (π2v4)

`PI2.md` §2 steps 6–7: the verifier at `t` (`CoreSpec.run`) requires one value nonzero,
`all = R_d Y_1 Y_2 · B · w_m · Y_3 · c_h D_n`, and leaves its claims: `Q`'s identity claim at `(u, z_0, z_1, y_0, y_1)`,
`Q`'s pushes' claim at `(u, ρ, z'_1, 1, 1)`, the setup's `ξ = κ(t) + βσ(t)` and `W`'s fold. Under `SpecOf` (its
constants are `RecPiop`'s circuit's on a Cantor basis), with the ports' polynomials `phiPoly`:

* **the one inversion carries the nonzero conditions** (`all_ne_zero_iff`): `all ≠ 0` exactly when `t ∉ V_m`, `c_h`,
  `Y_1 = c_h + t w_m`, `Y_2 = c_h + t w_m²`, `Y_3 = 1 + ρ + ρ w_m` and `α + P_v(t) + ξ` are nonzero
  (`D_n = B (α + P_v(t) + ξ)`);
* there, the inverses (`run_invs`), `z_0 = t w_m/Y_1`, `z_1 = t w_m²/Y_2`, `z'_1 = ρ w_m/Y_3` (`run_zs`), `num_1/R_d`
  is the identity's right side (`run_rhs`), `num_3/B = s + P_v(t)` (`run_num3`);
* **`checks_claims_iff`**: the verifier's check passes and its claims hold at the true values of `Q`'s sixteen slots
  at `t` (`idEq`, `pushEq`: each claim's value the slots' combination at its point, `t/w_m` the position coordinates'
  weight), `κ(t)`, `σ(t)` and `W`'s true fold, exactly when `t ∉ V_m`, `α + P_v(t) + ξ ≠ 0` and `RecPiop`'s claims
  hold (`QClaim` at `c = Y³`, `q = q_0 + w_m q_1`, `q_P` likewise), the setup's claim and the fold;
  **`checks_claims_iff_post2`** is the same with `RecPiop.Post2` itself;
* the claims' points for the tables' layer: `u_l = w_l/(1 + w_l)` (`run_u`) and `t/w_m = Π_{l < m}
  (1 + w_l)^{-1}` (`digitsScale_eq`).
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Finset RecPiop

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

/-- **`Q`'s identity claim at the slots' values**: its value is `scale (t/w_m)` times the slots' combination at
`(z_0, z_1)` (slot bits `(b_0, b_1)` weigh `(1 + z_0 or z_0)(1 + z_1 or z_1)`): `H`, `q`'s digits, `G` (limbs of `E`),
and by `c = Y³` limb code `3`'s `P`, `q_P`'s digits, `S`. -/
def idEq (o : Out F) (scale c t wm : F) (ht q0t q1t gt pt qp0t qp1t st : F) : Prop :=
  o.quotientValue = scale * (t * wm⁻¹) *
    ((1 + o.z0) * (1 + o.z1) * ht + o.z0 * (1 + o.z1) * q0t + (1 + o.z0) * o.z1 * q1t + o.z0 * o.z1 * gt +
      c * ((1 + o.z0) * (1 + o.z1) * pt + o.z0 * (1 + o.z1) * qp0t + (1 + o.z0) * o.z1 * qp1t + o.z0 * o.z1 * st))

/-- **`Q`'s pushes' claim at the slots' values**: limb code `3` alone (`(y_0, y_1) = (1, 1)`), its value `t/w_m` times
the slots' combination at `(ρ, z'_1)`. -/
def pushEq (o : Out F) (t wm ρ : F) (pt qp0t qp1t st : F) : Prop :=
  o.pushesValue = t * wm⁻¹ *
    ((1 + ρ) * (1 + o.zp1) * pt + ρ * (1 + o.zp1) * qp0t + (1 + ρ) * o.zp1 * qp1t + ρ * o.zp1 * st)

section Main

variable {n : ℕ} {S : CoreSpec F} {G : RecPiop.Circuit F} {B : QuotientSecurity.CantorBasis F n}
  {pairOf : ℕ → Block × ℕ} {portOf : ℕ → ℕ} {pubOf : List F → ℕ → List F}

/-- The run's digit `w_l`, `l ≤ m`. -/
theorem run_digit (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) {l : ℕ} (hl : l ≤ G.logN) :
    (S.run inp).digits.getD l 0 = QuotientSecurity.sq^[l] inp.t := by
  show (digitsList inp.t (S.logN + 1)).getD l 0 = _
  exact digitsList_getD inp.t (by rw [hS.logN]; omega)

theorem run_wm (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) :
    (S.run inp).digits.getD S.logN 0 = QuotientSecurity.sq^[G.logN] inp.t := by
  rw [hS.logN]; exact run_digit hS inp le_rfl

/-- The cells' `v`, the pull's denominator. -/
theorem run_dPull (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F) :
    dPullAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.α inp.β inp.t = (S.run inp).dPull := by
  unfold dPullAt
  rw [← run_cells hS hV inp (Nat.two_pow_pos _)]
  rfl

theorem run_ch (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F) :
    chAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.s inp.α inp.β inp.t =
      (S.run inp).ch := by
  unfold chAt
  rw [run_dPull hS hV inp]
  rfl

theorem run_y1 (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F) :
    chAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.s inp.α inp.β inp.t +
      inp.t * (G.zV (Heap.omega B)).eval inp.t = (S.run inp).y1 := by
  rw [run_ch hS hV inp, Circuit.zV_eval_eq G B hS.hn]
  show _ = (S.run inp).ch + inp.t * (S.run inp).digits.getD S.logN 0
  rw [run_wm hS inp]

theorem run_y2 (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F) :
    chAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.s inp.α inp.β inp.t +
      inp.t * (G.zV (Heap.omega B)).eval inp.t * (G.zV (Heap.omega B)).eval inp.t = (S.run inp).y2 := by
  rw [run_ch hS hV inp, Circuit.zV_eval_eq G B hS.hn]
  show _ = (S.run inp).ch + inp.t * (S.run inp).digits.getD S.logN 0 * (S.run inp).digits.getD S.logN 0
  rw [run_wm hS inp]

theorem run_y3 (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) :
    1 + inp.ρ + inp.ρ * (G.zV (Heap.omega B)).eval inp.t = (S.run inp).y3 := by
  rw [Circuit.zV_eval_eq G B hS.hn]
  show _ = 1 + inp.ρ + inp.ρ * (S.run inp).digits.getD S.logN 0
  rw [run_wm hS inp]

/-- **The one value the verifier requires nonzero**: `all = R_d Y_1 Y_2 · B · w_m · Y_3 · (c_h D_n)`. -/
theorem run_all (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) :
    (S.run inp).all = (S.run inp).rDen * (S.run inp).y1 * (S.run inp).y2 * (S.run inp).den *
      QuotientSecurity.sq^[G.logN] inp.t * (S.run inp).y3 * ((S.run inp).ch * (S.run inp).dN) := by
  rw [← run_wm hS inp]
  rfl

/-- `w_{l+1} ≠ 0` gives `w_l ≠ 0`. -/
theorem wm_ne_zero {t : F} {m : ℕ} (h : QuotientSecurity.sq^[m + 1] t ≠ 0) : QuotientSecurity.sq^[m] t ≠ 0 :=
  digit_ne_zero_of_le (by omega) h

/-- **The pushes at `t`, through `phiPoly`.** -/
theorem push_side' (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F)
    (ht : QuotientSecurity.sq^[G.logN] inp.t ≠ 0) :
    (S.run inp).den ≠ 0 ∧ (S.run inp).rDen ≠ 0 ∧
      G.pvAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t =
        cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t 0 +
          QuotientSecurity.sq^[G.logN] inp.t * (S.run inp).num / (S.run inp).den ∧
      (G.holePoly (Heap.omega B)).eval inp.t * (S.run inp).delta +
          G.tAt (Heap.omega B) (phiPoly G B (pubOf inp.scalars) inp.γ)
            (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t =
        QuotientSecurity.sq^[G.logN] inp.t * (S.run inp).rNum / (S.run inp).rDen :=
  push_side hS hV inp ht (phiPoly G B (pubOf inp.scalars) inp.γ) fun k ↦ (phiAt_eq hS hV inp.scalars inp.γ ht k).symm

/-- **`D_n = B (α + P_v(t) + ξ)`.** -/
theorem run_dN (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F)
    (ht : QuotientSecurity.sq^[G.logN] inp.t ≠ 0) :
    (S.run inp).dN = (S.run inp).den *
      (inp.α + G.pvAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t +
        inp.ξ) := by
  obtain ⟨hden, -, hpv, -⟩ := push_side' hS hV inp ht
  have e : (S.run inp).dN = (inp.α + (S.run inp).cells.getD 0 0 + inp.ξ) * (S.run inp).den +
      (S.run inp).digits.getD S.logN 0 * (S.run inp).num := rfl
  rw [e, hpv, run_wm hS inp, run_cells hS hV inp (Nat.two_pow_pos _)]
  field_simp
  ring

/-- **`num_3 = B (s + P_v(t))`.** -/
theorem run_num3 (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F)
    (ht : QuotientSecurity.sq^[G.logN] inp.t ≠ 0) :
    (S.run inp).num3 = (S.run inp).den *
      (inp.s + G.pvAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t) := by
  have e : (S.run inp).num3 = (S.run inp).dN + (inp.α + inp.s + inp.ξ) * (S.run inp).den := rfl
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [e, run_dN hS hV inp ht]
  linear_combination (inp.α + inp.ξ) * (S.run inp).den * h2

/-- **`num_1/R_d` is the identity's right side** `(1 + 1_S)(d_push + d_pull) + T`. -/
theorem run_rhs (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F)
    (ht : QuotientSecurity.sq^[G.logN] inp.t ≠ 0) :
    (S.run inp).num1 = (S.run inp).rDen * G.rhsAt (Heap.omega B) (phiPoly G B (pubOf inp.scalars) inp.γ)
      (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.s inp.α inp.β inp.γ inp.t := by
  obtain ⟨-, hrden, -, hport⟩ := push_side' hS hV inp ht
  have e : (S.run inp).num1 = (S.run inp).delta * (S.run inp).rDen +
      (S.run inp).digits.getD S.logN 0 * (S.run inp).rNum := rfl
  have ed : (S.run inp).delta = dPushAt inp.s inp.ξ inp.α +
      dPullAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.α inp.β inp.t := by
    rw [run_dPull hS hV inp]
    show (S.run inp).dPull + (S.run inp).dPush = _
    unfold dPushAt
    rw [add_comm]
    rfl
  rw [e, run_wm hS inp]
  unfold Circuit.rhsAt
  have hq : QuotientSecurity.sq^[G.logN] inp.t * (S.run inp).rNum =
      (S.run inp).rDen * ((G.holePoly (Heap.omega B)).eval inp.t * (S.run inp).delta +
        G.tAt (Heap.omega B) (phiPoly G B (pubOf inp.scalars) inp.γ)
          (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t) := by
    rw [hport]
    field_simp
  rw [hq, ← ed]
  ring

/-- **The one inversion carries the nonzero conditions**: `all ≠ 0` iff `t ∉ V_m`, `c_h ≠ 0`, `Y_1 ≠ 0`, `Y_2 ≠ 0`,
`Y_3 ≠ 0` and `α + P_v(t) + ξ ≠ 0`. -/
theorem all_ne_zero_iff (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F) :
    (S.run inp).all ≠ 0 ↔
      QuotientSecurity.sq^[G.logN] inp.t ≠ 0 ∧ (S.run inp).ch ≠ 0 ∧ (S.run inp).y1 ≠ 0 ∧ (S.run inp).y2 ≠ 0 ∧
        (S.run inp).y3 ≠ 0 ∧
        inp.α + G.pvAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t +
          inp.ξ ≠ 0 := by
  rw [run_all hS inp]
  constructor
  · intro h
    have q7 := left_ne_zero_of_mul h
    have qcd := right_ne_zero_of_mul h
    have h3 := right_ne_zero_of_mul q7
    have q6 := left_ne_zero_of_mul q7
    have hm := right_ne_zero_of_mul q6
    have q5 := left_ne_zero_of_mul q6
    have hd' := right_ne_zero_of_mul q5
    have q4 := left_ne_zero_of_mul q5
    have h2 := right_ne_zero_of_mul q4
    have q3 := left_ne_zero_of_mul q4
    have h1 := right_ne_zero_of_mul q3
    have hr := left_ne_zero_of_mul q3
    have hch := left_ne_zero_of_mul qcd
    have hd := right_ne_zero_of_mul qcd
    refine ⟨hm, hch, h1, h2, h3, fun h0 ↦ hd ?_⟩
    rw [run_dN hS hV inp hm, h0, mul_zero]
  · rintro ⟨hm, hch, h1, h2, h3, hd⟩
    obtain ⟨hden, hrden, -, -⟩ := push_side' hS hV inp hm
    rw [run_dN hS hV inp hm]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hrden h1) h2) hden) hm) h3)
      (mul_ne_zero hch (mul_ne_zero hden hd))

/-- **The inverses**, where `all ≠ 0`: `1/(R_d Y_1 Y_2 B w_m)`, `1/(B w_m Y_3)`, `1/w_m`, `1/Y_1`, `1/Y_2`, `1/Y_3`. -/
theorem run_invs (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) :
    (S.run inp).invP4 = ((S.run inp).rDen * (S.run inp).y1 * (S.run inp).y2 * (S.run inp).den *
        QuotientSecurity.sq^[G.logN] inp.t)⁻¹ ∧
      (S.run inp).invP5 * (S.run inp).p2 =
        ((S.run inp).den * QuotientSecurity.sq^[G.logN] inp.t * (S.run inp).y3)⁻¹ ∧
      (S.run inp).invZ = (QuotientSecurity.sq^[G.logN] inp.t)⁻¹ ∧ (S.run inp).invY1 = (S.run inp).y1⁻¹ ∧
      (S.run inp).invY2 = (S.run inp).y2⁻¹ ∧ (S.run inp).invY3 = (S.run inp).y3⁻¹ := by
  have ha := run_all hS inp
  have wm : (S.run inp).digits.getD S.logN 0 = QuotientSecurity.sq^[G.logN] inp.t := run_wm hS inp
  rw [ha] at h
  have q7 := left_ne_zero_of_mul h
  have qcd := right_ne_zero_of_mul h
  have h3 := right_ne_zero_of_mul q7
  have q6 := left_ne_zero_of_mul q7
  have hm := right_ne_zero_of_mul q6
  have q5 := left_ne_zero_of_mul q6
  have hd := right_ne_zero_of_mul q5
  have q4 := left_ne_zero_of_mul q5
  have h2 := right_ne_zero_of_mul q4
  have q3 := left_ne_zero_of_mul q4
  have h1 := right_ne_zero_of_mul q3
  have hr := left_ne_zero_of_mul q3
  have hch := left_ne_zero_of_mul qcd
  have hdn := right_ne_zero_of_mul qcd
  have eAll : (S.run inp).all = (S.run inp).rDen * (S.run inp).y1 * (S.run inp).y2 * (S.run inp).den *
      QuotientSecurity.sq^[G.logN] inp.t * (S.run inp).y3 * ((S.run inp).ch * (S.run inp).dN) := ha
  have ePinv5 : (S.run inp).invP5 = (S.run inp).all⁻¹ * ((S.run inp).ch * (S.run inp).dN) := rfl
  have eP2 : (S.run inp).p2 = (S.run inp).rDen * (S.run inp).y1 * (S.run inp).y2 := rfl
  have eP4 : (S.run inp).p4 = (S.run inp).rDen * (S.run inp).y1 * (S.run inp).y2 * (S.run inp).den *
      QuotientSecurity.sq^[G.logN] inp.t := by
    show (S.run inp).rDen * (S.run inp).y1 * (S.run inp).y2 * (S.run inp).den *
      (S.run inp).digits.getD S.logN 0 = _
    rw [wm]
  have eP3 : (S.run inp).p3 = (S.run inp).rDen * (S.run inp).y1 * (S.run inp).y2 * (S.run inp).den := rfl
  have eP1 : (S.run inp).p1 = (S.run inp).rDen * (S.run inp).y1 := rfl
  have eInvP4 : (S.run inp).invP4 = (S.run inp).invP5 * (S.run inp).y3 := rfl
  have eInvZ : (S.run inp).invZ = (S.run inp).invP4 * (S.run inp).p3 := rfl
  have eInvP3 : (S.run inp).invP3 = (S.run inp).invP4 * QuotientSecurity.sq^[G.logN] inp.t := by
    show (S.run inp).invP4 * (S.run inp).digits.getD S.logN 0 = _
    rw [wm]
  have eInvP2 : (S.run inp).invP2 = (S.run inp).invP3 * (S.run inp).den := rfl
  have eInvY2 : (S.run inp).invY2 = (S.run inp).invP2 * (S.run inp).p1 := rfl
  have eInvP1 : (S.run inp).invP1 = (S.run inp).invP2 * (S.run inp).y2 := rfl
  have eInvY1 : (S.run inp).invY1 = (S.run inp).invP1 * (S.run inp).rDen := rfl
  have eInvY3 : (S.run inp).invY3 = (S.run inp).invP5 * (S.run inp).p4 := rfl
  have hP4 : (S.run inp).invP4 = ((S.run inp).rDen * (S.run inp).y1 * (S.run inp).y2 * (S.run inp).den *
      QuotientSecurity.sq^[G.logN] inp.t)⁻¹ := by
    rw [eInvP4, ePinv5, eAll]
    field_simp
  refine ⟨hP4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ePinv5, eAll, eP2]
    field_simp
  · rw [eInvZ, hP4, eP3]
    field_simp
  · rw [eInvY1, eInvP1, eInvP2, eInvP3, hP4]
    field_simp
  · rw [eInvY2, eInvP2, eInvP3, hP4, eP1]
    field_simp
  · rw [eInvY3, ePinv5, eAll, eP4]
    field_simp

/-- **The slot coordinates**, where `all ≠ 0`: `z_0 = t w_m/Y_1`, `z_1 = t w_m²/Y_2`, `z'_1 = ρ w_m/Y_3`. -/
theorem run_zs (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) :
    (S.run inp).z0 = inp.t * QuotientSecurity.sq^[G.logN] inp.t / (S.run inp).y1 ∧
      (S.run inp).z1 = inp.t * QuotientSecurity.sq^[G.logN] inp.t * QuotientSecurity.sq^[G.logN] inp.t /
        (S.run inp).y2 ∧
      (S.run inp).zp1 = inp.ρ * QuotientSecurity.sq^[G.logN] inp.t / (S.run inp).y3 := by
  obtain ⟨-, -, -, h1, h2, h3⟩ := run_invs hS inp h
  have wm := run_wm hS inp
  refine ⟨?_, ?_, ?_⟩
  · show inp.t * (S.run inp).digits.getD S.logN 0 * (S.run inp).invY1 = _
    rw [wm, h1, div_eq_mul_inv]
  · show inp.t * (S.run inp).digits.getD S.logN 0 * (S.run inp).digits.getD S.logN 0 * (S.run inp).invY2 = _
    rw [wm, h2, div_eq_mul_inv]
  · show inp.ρ * (S.run inp).digits.getD S.logN 0 * (S.run inp).invY3 = _
    rw [wm, h3, div_eq_mul_inv]

/-- **W's fold is `foldAt`.** -/
theorem run_fold (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) :
    (S.run inp).fold = foldAt G.logW (fun k ↦ inp.a.getD k 0) inp.ρ := by
  show foldW ((List.range S.logRow).map fun l ↦ sqIter inp.ρ l) S.logRow inp.a = _
  rw [hS.logRow]
  exact foldW_eq_foldAt inp.ρ _ G.logW inp.a fun l hl ↦ by
    simp [List.getD_eq_getElem?_getD, hl, sqIter_eq]

/-- **The verifier's check passes and its claims hold, at the true values, iff `t ∉ V_m`, `α + P_v(t) + ξ ≠ 0` and
`RecPiop`'s claims hold** (`QClaim` at `c = Y³`, `q = q_0 + w_m q_1`, `q_P = q_{P,0} + w_m q_{P,1}`, the setup's claim,
the fold), for a nonzero scale. -/
theorem checks_claims_iff (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F)
    (hsc : S.scale ≠ 0) (ht q0t q1t gt pt qp0t qp1t st κt σt foldTrue : F) :
    ((S.run inp).all ≠ 0 ∧
        idEq (S.run inp) S.scale S.yCube inp.t (QuotientSecurity.sq^[G.logN] inp.t) ht q0t q1t gt pt qp0t qp1t st ∧
        pushEq (S.run inp) inp.t (QuotientSecurity.sq^[G.logN] inp.t) inp.ρ pt qp0t qp1t st ∧
        inp.ξ = κt + inp.β * σt ∧ (S.run inp).fold = foldTrue) ↔
      (QuotientSecurity.sq^[G.logN] inp.t ≠ 0 ∧
        inp.α + G.pvAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t +
          inp.ξ ≠ 0 ∧
        G.QClaim (Heap.omega B) (phiPoly G B (pubOf inp.scalars) inp.γ) S.yCube
          (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.s inp.α inp.β inp.γ inp.t inp.ρ
          ht (q0t + QuotientSecurity.sq^[G.logN] inp.t * q1t) gt pt
          (qp0t + QuotientSecurity.sq^[G.logN] inp.t * qp1t) st ∧
        inp.ξ = κt + inp.β * σt ∧ foldAt G.logW (fun k ↦ inp.a.getD k 0) inp.ρ = foldTrue) := by
  set v := cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t with hv
  set wm := QuotientSecurity.sq^[G.logN] inp.t with hwm
  set pv := G.pvAt (Heap.omega B) v inp.γ inp.t with hpv
  set rhs := G.rhsAt (Heap.omega B) (phiPoly G B (pubOf inp.scalars) inp.γ) v inp.ξ inp.s inp.α inp.β inp.γ inp.t
    with hrhs
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hzv : (G.zV (Heap.omega B)).eval inp.t = wm := Circuit.zV_eval_eq G B hS.hn _
  have hchv : chAt v inp.ξ inp.s inp.α inp.β inp.t = (S.run inp).ch := run_ch hS hV inp
  have hwmR : (S.run inp).digits.getD S.logN 0 = wm := run_wm hS inp
  -- the claims' equations, where `all ≠ 0`
  have hclaims : (S.run inp).all ≠ 0 →
      ((idEq (S.run inp) S.scale S.yCube inp.t wm ht q0t q1t gt pt qp0t qp1t st ↔
          (S.run inp).ch ^ 2 * ht + inp.t * wm * (S.run inp).ch * (q0t + wm * q1t) + inp.t ^ 2 * wm ^ 3 * gt +
              S.yCube * ((S.run inp).ch ^ 2 * pt + inp.t * wm * (S.run inp).ch * (qp0t + wm * qp1t) +
                inp.t ^ 2 * wm ^ 3 * st) =
            inp.t * (S.run inp).ch * rhs +
              S.yCube * ((S.run inp).ch ^ 2 * inp.s + inp.t * (S.run inp).ch * (inp.s + pv))) ∧
        (pushEq (S.run inp) inp.t wm inp.ρ pt qp0t qp1t st ↔
          RecPiop.pushComb (wm * (pt + inp.s)) (wm * (qp0t + wm * qp1t) + inp.s + pv) (wm ^ 2 * st) inp.ρ = 0)) := by
    intro h0
    obtain ⟨hm, hch, hy1, hy2, hy3, -⟩ := (all_ne_zero_iff hS hV inp).mp h0
    obtain ⟨hden, hrden, -, -⟩ := push_side' hS hV inp hm
    obtain ⟨iP4, iP5, iZ, -, -, -⟩ := run_invs hS inp h0
    obtain ⟨ez0, ez1, ezp1⟩ := run_zs hS inp h0
    have ht0 : inp.t ≠ 0 := digit_ne_zero_of_le (l := 0) (by omega) hm
    rw [← hwm] at hm iP4 iP5 iZ ez0 ez1 ezp1
    have ey1 : (S.run inp).y1 = (S.run inp).ch + inp.t * wm := by
      show (S.run inp).ch + inp.t * (S.run inp).digits.getD S.logN 0 = _
      rw [hwmR]
    have ey2 : (S.run inp).y2 = (S.run inp).ch + inp.t * wm * wm := by
      show (S.run inp).ch + inp.t * (S.run inp).digits.getD S.logN 0 * (S.run inp).digits.getD S.logN 0 = _
      rw [hwmR]
    have ey3 : (S.run inp).y3 = 1 + inp.ρ + inp.ρ * wm := by
      show 1 + inp.ρ + inp.ρ * (S.run inp).digits.getD S.logN 0 = _
      rw [hwmR]
    have h1z0 : 1 + (S.run inp).z0 = (S.run inp).ch / (S.run inp).y1 := by
      rw [ez0, eq_div_iff hy1, add_mul, one_mul, div_mul_cancel₀ _ hy1, ey1]
      linear_combination (inp.t * wm) * h2
    have h1z1 : 1 + (S.run inp).z1 = (S.run inp).ch / (S.run inp).y2 := by
      rw [ez1, eq_div_iff hy2, add_mul, one_mul, div_mul_cancel₀ _ hy2, ey2]
      linear_combination (inp.t * wm * wm) * h2
    have h1zp1 : 1 + (S.run inp).zp1 = (1 + inp.ρ) / (S.run inp).y3 := by
      rw [ezp1, eq_div_iff hy3, add_mul, one_mul, div_mul_cancel₀ _ hy3, ey3]
      linear_combination (inp.ρ * wm) * h2
    have hn1 : (S.run inp).num1 = (S.run inp).rDen * rhs := run_rhs hS hV inp hm
    have hn3 : (S.run inp).num3 = (S.run inp).den * (inp.s + pv) := run_num3 hS hV inp hm
    have eq : (S.run inp).quotientValue = S.scale * inp.t * (S.run inp).ch * (inp.t * ((S.run inp).num1 *
        (S.run inp).den) + S.yCube * ((S.run inp).rDen * ((S.run inp).ch * (inp.s * (S.run inp).den) +
          inp.t * (S.run inp).num3))) * (S.run inp).invP4 := rfl
    have ep : (S.run inp).pushesValue = inp.t * (1 + inp.ρ) * ((1 + inp.ρ) * (wm * (inp.s * (S.run inp).den)) +
        inp.ρ * (S.run inp).num3) * ((S.run inp).invP5 * (S.run inp).p2) * (S.run inp).invZ := by
      show inp.t * (1 + inp.ρ) * ((1 + inp.ρ) * ((S.run inp).digits.getD S.logN 0 * (inp.s * (S.run inp).den)) +
        inp.ρ * (S.run inp).num3) * ((S.run inp).invP5 * (S.run inp).p2) * (S.run inp).invZ = _
      rw [hwmR]
    refine ⟨?_, ?_⟩
    · unfold idEq
      have key : (S.run inp).quotientValue + S.scale * (inp.t * wm⁻¹) *
          ((1 + (S.run inp).z0) * (1 + (S.run inp).z1) * ht + (S.run inp).z0 * (1 + (S.run inp).z1) * q0t +
            (1 + (S.run inp).z0) * (S.run inp).z1 * q1t + (S.run inp).z0 * (S.run inp).z1 * gt +
            S.yCube * ((1 + (S.run inp).z0) * (1 + (S.run inp).z1) * pt +
              (S.run inp).z0 * (1 + (S.run inp).z1) * qp0t + (1 + (S.run inp).z0) * (S.run inp).z1 * qp1t +
              (S.run inp).z0 * (S.run inp).z1 * st)) =
          S.scale * inp.t / (wm * (S.run inp).y1 * (S.run inp).y2) *
            (((S.run inp).ch ^ 2 * ht + inp.t * wm * (S.run inp).ch * (q0t + wm * q1t) + inp.t ^ 2 * wm ^ 3 * gt +
              S.yCube * ((S.run inp).ch ^ 2 * pt + inp.t * wm * (S.run inp).ch * (qp0t + wm * qp1t) +
                inp.t ^ 2 * wm ^ 3 * st)) +
            (inp.t * (S.run inp).ch * rhs +
              S.yCube * ((S.run inp).ch ^ 2 * inp.s + inp.t * (S.run inp).ch * (inp.s + pv)))) := by
        rw [h1z0, h1z1, ez0, ez1, eq, iP4, hn1, hn3]
        field_simp
        ring
      have hK : S.scale * inp.t / (wm * (S.run inp).y1 * (S.run inp).y2) ≠ 0 :=
        div_ne_zero (mul_ne_zero hsc ht0) (mul_ne_zero (mul_ne_zero hm hy1) hy2)
      constructor
      · intro h
        have := key
        rw [h, CharTwo.add_self_eq_zero] at this
        exact CharTwo.add_eq_zero.mp ((mul_eq_zero.mp this.symm).resolve_left hK)
      · intro h
        have := key
        rw [h, CharTwo.add_self_eq_zero, mul_zero] at this
        exact CharTwo.add_eq_zero.mp this
    · unfold pushEq
      have key : (S.run inp).pushesValue + inp.t * wm⁻¹ *
          ((1 + inp.ρ) * (1 + (S.run inp).zp1) * pt + inp.ρ * (1 + (S.run inp).zp1) * qp0t +
            (1 + inp.ρ) * (S.run inp).zp1 * qp1t + inp.ρ * (S.run inp).zp1 * st) =
          inp.t / (wm ^ 2 * (S.run inp).y3) *
            RecPiop.pushComb (wm * (pt + inp.s)) (wm * (qp0t + wm * qp1t) + inp.s + pv) (wm ^ 2 * st) inp.ρ := by
        rw [h1zp1, ezp1, ep, iP5, iZ, hn3]
        unfold RecPiop.pushComb
        field_simp
        ring
      have hK : inp.t / (wm ^ 2 * (S.run inp).y3) ≠ 0 := div_ne_zero ht0 (mul_ne_zero (pow_ne_zero 2 hm) hy3)
      constructor
      · intro h
        have := key
        rw [h, CharTwo.add_self_eq_zero] at this
        exact (mul_eq_zero.mp this.symm).resolve_left hK
      · intro h
        have := key
        rw [h, mul_zero] at this
        exact CharTwo.add_eq_zero.mp this
  constructor
  · rintro ⟨h0, hi, hp, hξ, hf⟩
    obtain ⟨hm, hch, hy1, hy2, hy3, hd⟩ := (all_ne_zero_iff hS hV inp).mp h0
    refine ⟨hm, hd, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hξ, by rw [← hf, run_fold hS inp]⟩
    · rw [hzv]; exact hm
    · rw [hchv]; exact hch
    · rw [run_y1 hS hV inp]; exact hy1
    · rw [run_y2 hS hV inp]; exact hy2
    · rw [run_y3 hS inp]; exact hy3
    · rw [hzv, hchv]; exact ((hclaims h0).1).mp hi
    · rw [hzv]; exact ((hclaims h0).2).mp hp
  · rintro ⟨hm, hd, ⟨-, hch, hy1, hy2, hy3, hi, hp⟩, hξ, hf⟩
    rw [hchv] at hch
    rw [run_y1 hS hV inp] at hy1
    rw [run_y2 hS hV inp] at hy2
    rw [run_y3 hS inp] at hy3
    have h0 : (S.run inp).all ≠ 0 := (all_ne_zero_iff hS hV inp).mpr ⟨hm, hch, hy1, hy2, hy3, hd⟩
    rw [hzv, hchv] at hi
    rw [hzv] at hp
    exact ⟨h0, ((hclaims h0).1).mpr hi, ((hclaims h0).2).mpr hp, hξ, by rw [run_fold hS inp, hf]⟩

/-- **The same with `RecPiop.Post2`**, for any tables' model `Mo` whose `Φ` is `phiPoly` and whose constant is `Y³`:
its `H`, `G`, `P`, `S` at `t` the slots' values, its `q`, `q_P` at `t` the digits' (`q_0 + w_m q_1`), the setup's `σ`,
`κ`, `W`'s true fold values; the statement `s` with the public limbs `pubOf` of the public scalars, the fold values `a`
(`2^r` of them), `ξ` and `s` the round's message. -/
theorem checks_claims_iff_post2 {St M : Type} (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid)
    (inp : Inputs F) (hsc : S.scale ≠ 0) (Mo : Model G (Heap.omega B) M)
    (hphi : ∀ pub γ, Mo.phi pub γ = phiPoly G B pub γ) (hc : Mo.idC = S.yCube) (pubOf' : St → ℕ → List F) (s : St)
    (hpub : pubOf' s = pubOf inp.scalars) (cW cQ : M) (ha : inp.a.length = 2 ^ G.logW) (q0t q1t qp0t qp1t : F)
    (hq : (Mo.qP cQ).eval inp.t = q0t + QuotientSecurity.sq^[G.logN] inp.t * q1t)
    (hqp : (Mo.qPP cQ).eval inp.t = qp0t + QuotientSecurity.sq^[G.logN] inp.t * qp1t) :
    ((S.run inp).all ≠ 0 ∧
        idEq (S.run inp) S.scale S.yCube inp.t (QuotientSecurity.sq^[G.logN] inp.t) ((Mo.hP cQ).eval inp.t) q0t q1t
          ((Mo.gP cQ).eval inp.t) ((Mo.pP cQ).eval inp.t) qp0t qp1t ((Mo.sP cQ).eval inp.t) ∧
        pushEq (S.run inp) inp.t (QuotientSecurity.sq^[G.logN] inp.t) inp.ρ ((Mo.pP cQ).eval inp.t) qp0t qp1t
          ((Mo.sP cQ).eval inp.t) ∧
        inp.ξ = Mo.setup.κP.eval inp.t + inp.β * Mo.setup.σP.eval inp.t ∧
        (S.run inp).fold = foldAt G.logW (Mo.fold cW inp.t) inp.ρ) ↔
      (QuotientSecurity.sq^[G.logN] inp.t ≠ 0 ∧
        inp.α + G.pvAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t +
          inp.ξ ≠ 0 ∧
        Post2 G (Heap.omega B) Mo pubOf' s cW [inp.α, inp.β, inp.γ] cQ [inp.t] (inp.a ++ [inp.ξ, inp.s]) [inp.ρ]) := by
  rw [checks_claims_iff hS hV inp hsc, ← hq, ← hqp]
  have hfv : ∀ k < 2 ^ G.logW, foldVals (inp.a ++ [inp.ξ, inp.s]) k = inp.a.getD k 0 := by
    intro k hk
    unfold foldVals
    rw [List.getD_append _ _ _ _ (by omega)]
  have hxi : xiOf G.logW (inp.a ++ [inp.ξ, inp.s]) = inp.ξ := by
    unfold xiOf
    rw [List.getD_append_right _ _ _ _ (by omega), ha, Nat.sub_self]
    rfl
  have hsv : sOf G.logW (inp.a ++ [inp.ξ, inp.s]) = inp.s := by
    unfold sOf
    rw [List.getD_append_right _ _ _ _ (by omega), ha, show 2 ^ G.logW + 1 - 2 ^ G.logW = 1 by omega]
    rfl
  have hcells : cellsOf G.logW (Heap.omega B) (foldVals (inp.a ++ [inp.ξ, inp.s])) inp.t =
      cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t :=
    funext fun x ↦ cellsOf_congr G.logW (Heap.omega B) hfv inp.t x
  have hfold : foldAt G.logW (foldVals (inp.a ++ [inp.ξ, inp.s])) inp.ρ =
      foldAt G.logW (fun k ↦ inp.a.getD k 0) inp.ρ :=
    Finset.sum_congr rfl fun k hk ↦ by rw [hfv k (Finset.mem_range.mp hk)]
  unfold Post2 abc
  simp only [List.getD_cons_zero, List.getD_cons_succ, hxi, hsv, hcells, hfold, hpub, hphi, hc]
  constructor
  · rintro ⟨hT, hd, hq', hξ, hf⟩
    exact ⟨hT, hd, hξ, hq', hf⟩
  · rintro ⟨hT, hd, hξ, hq', hf⟩
    exact ⟨hT, hd, hq', hξ, hf⟩

/-! ## The claims' points, for the tables' layer -/

/-- **The digits' inverses**, where `all ≠ 0`: `1/w_l` for `l ≤ m`. -/
theorem run_wInvs (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) {l : ℕ}
    (hl : l ≤ G.logN) : (S.run inp).wInvs.getD l 0 = (QuotientSecurity.sq^[l] inp.t)⁻¹ := by
  obtain ⟨-, -, hZ, -, -, -⟩ := run_invs hS inp h
  have hT : QuotientSecurity.sq^[G.logN] inp.t ≠ 0 := by
    intro h0; apply h; rw [run_all hS inp, h0]; ring
  have htop : (S.run inp).invZ = ((S.run inp).digits.getD S.logN 0)⁻¹ := by
    rw [hZ, run_wm hS inp]
  have e : (S.run inp).wInvs = wInvsList (S.run inp).digits S.logN (S.run inp).invZ := rfl
  rw [e, htop, hS.logN,
    wInvsList_getD inp.t (S.run inp).digits (fun l hl ↦ run_digit hS inp hl) hT hl, run_digit hS inp hl]

/-- **`u_l = w_l/(1 + w_l)`** (`Q`'s point in the novel basis), where `all ≠ 0`, `l < m`. -/
theorem run_u (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) {l : ℕ}
    (hl : l < G.logN) :
    (S.run inp).uList.getD l 0 = QuotientSecurity.sq^[l] inp.t / (1 + QuotientSecurity.sq^[l] inp.t) := by
  have hT : QuotientSecurity.sq^[G.logN] inp.t ≠ 0 := by
    intro h0; apply h; rw [run_all hS inp, h0]; ring
  have e : (S.run inp).uList = (List.range S.logN).map fun l ↦
      1 + (S.run inp).wInvs.getD l 0 + (S.run inp).wInvs.getD (l + 1) 0 := rfl
  have hl' : l < S.logN := by rw [hS.logN]; exact hl
  rw [e]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl', Option.map_some,
    Option.getD_some]
  rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, run_wInvs hS inp h hl.le,
    run_wInvs hS inp h (by omega : l + 1 ≤ G.logN), Function.iterate_succ_apply', sq_eq_mul]
  have h0 : QuotientSecurity.sq^[l] inp.t ≠ 0 := digit_ne_zero_of_le (by omega) hT
  have h1 : 1 + QuotientSecurity.sq^[l] inp.t ≠ 0 := by
    have := digit_ne_zero_of_le (l := l + 1) (by omega) hT
    rw [Function.iterate_succ_apply', sq_eq_mul] at this
    exact right_ne_zero_of_mul this
  field_simp
  ring_nf
  rw [CharTwo.two_eq_zero]
  ring

/-- **`t/w_m = Π_{l<m} (1 + w_l)^{-1}`** (the position coordinates' weight), where `w_m(t) ≠ 0`. -/
theorem digitsScale_eq {t : F} {L : ℕ} (hT : QuotientSecurity.sq^[L] t ≠ 0) :
    t * (QuotientSecurity.sq^[L] t)⁻¹ = ∏ l ∈ range L, (1 + QuotientSecurity.sq^[l] t)⁻¹ := by
  have key : ∀ L' ≤ L, t * (QuotientSecurity.sq^[L'] t)⁻¹ = ∏ l ∈ range L', (1 + QuotientSecurity.sq^[l] t)⁻¹ := by
    intro L' hL
    induction L' with
    | zero =>
      have : t ≠ 0 := digit_ne_zero_of_le (l := 0) (by omega) hT
      simp [this]
    | succ L' ih =>
      rw [Finset.prod_range_succ, ← ih (by omega), Function.iterate_succ_apply', sq_eq_mul, mul_inv, ← mul_assoc]
  exact key _ le_rfl

end Main

end RecStatement
