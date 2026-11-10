-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecStatement.Lemmas.Phi

/-!
# The verifier's checks and claims are `RecPiop`'s state after `ρ` (π2v3)

`PI2.md` §2 steps 6–7: the verifier at `t` (`CoreSpec.run`) requires one value nonzero,
`all = R_d Y · w_{m+1} · B · c_h D_n`, and leaves its claims: `Q`'s identity claim, worth
`(D/Y)(num_1/R_d + c_3 (c_h w_m s + num_3/B))` (`run_quotientValue`, `D = s_E t/w_{m+1}`), `Q`'s pushes' claim, worth
`(D/L_0)((1 + ρ) w_m s + ρ num_3/(w_m B))` (`run_pushesValue`), the sum `Σ_V h = 0`, the setup's `ξ = κ(t) + βσ(t)`
and `W`'s fold. Under `SpecOf` (its constants are `RecPiop`'s circuit's on a Cantor basis), with the ports'
polynomials `phiPoly`:

* **the one inversion carries the nonzero conditions** (`all_ne_zero_iff`): `all ≠ 0` exactly when `t ∉ V_{m+1}`
  (`w_{m+1}(t) ≠ 0`, which makes `B ≠ 0`), `c_h ≠ 0`, `Y = c_h + c_q ≠ 0` and `α + P_v(t) + ξ ≠ 0`
  (`D_n = B (α + P_v(t) + ξ)`);
* there, `ρ' = c_q/Y` (`run_rhoQ`), `num_1/R_d` is the identity's right side (`run_rhs`: the ports' fraction is
  `1_S Δ + T`), `num_3/B = s + P_v(t)` (`run_num3`);
* **`checks_claims_iff`**: the verifier's check passes and its claims hold at the true values `h(t), q(t), P(t),
  q_P(t), Σ_V h, κ(t), σ(t)` and `W`'s true fold (`Q`'s two claims normalised: `idEq`, `pushEq`), exactly when
  `t ∉ V_{m+1}`, `α + P_v(t) + ξ ≠ 0`, and `RecPiop`'s claims hold: `QClaim` (at `c = c_3`), the sum, the setup's
  claim and the fold; **`checks_claims_iff_post2`** is the same with `RecPiop.Post2` itself, for any tables' model
  whose `Φ` is `phiPoly` and whose constant is `c_3`;
* the claims' points for the tables' layer: `u_l = w_l/(1 + w_l)` (`run_u`) and `t/w_{m+1} = Π_{l ≤ m}
  (1 + w_l)^{-1}` (`digitsScale_eq`).
-/

set_option linter.unusedSectionVars false

namespace RecStatement

open Finset RecPiop

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

/-- **The identity claim's weight of `P`'s slots** `c_3 = y_0 y_1/((1 + y_0)(1 + y_1))`. -/
def c3Of (S : CoreSpec F) : F := S.y0 * S.y1 * ((1 + S.y0) * (1 + S.y1))⁻¹

/-- **`Q`'s identity claim, normalised**: its value over `D/Y` equals the slots' combination at `(ρ', y_0, y_1)`. -/
def idEq (o : Out F) (c rq ht qt pt qpt : F) (wm sv : F) : Prop :=
  (o.num1 / o.rDen + c * (o.ch * wm * sv + o.num3 / o.den)) / o.y =
    (1 + rq) * ht + rq * qt + c * ((1 + rq) * wm * pt + rq * qpt)

/-- **`Q`'s pushes' claim, normalised**: `(1 + ρ) w_m s + ρ num_3/(w_m B) = (1 + ρ) w_m P(t) + ρ q_P(t)`. -/
def pushEq (o : Out F) (ρ pt qpt : F) (wm sv : F) : Prop :=
  (1 + ρ) * wm * sv + ρ * (o.num3 / (wm * o.den)) = (1 + ρ) * wm * pt + ρ * qpt

section Main

variable {n : ℕ} {S : CoreSpec F} {G : RecPiop.Circuit F} {B : QuotientSecurity.CantorBasis F n}
  {pairOf : ℕ → Block × ℕ} {portOf : ℕ → ℕ} {pubOf : List F → ℕ → List F}

/-- The run's digit `w_l`. -/
theorem run_digit (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) {l : ℕ} (hl : l ≤ G.logN + 1) :
    (S.run inp).digits.getD l 0 = QuotientSecurity.sq^[l] inp.t := by
  show (digitsList inp.t (S.logN + 2)).getD l 0 = _
  exact digitsList_getD inp.t (by rw [hS.logN]; omega)

/-- **The one value the verifier requires nonzero**: `all = R_d · Y · w_{m+1} · B · (c_h D_n)`. -/
theorem run_all (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) :
    (S.run inp).all = (S.run inp).rDen * (S.run inp).y * QuotientSecurity.sq^[G.logN + 1] inp.t * (S.run inp).den *
      ((S.run inp).ch * (S.run inp).dN) := by
  rw [← run_digit hS inp le_rfl, ← hS.logN]
  rfl

theorem run_wm (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) :
    (S.run inp).digits.getD S.logN 0 = QuotientSecurity.sq^[G.logN] inp.t := by
  rw [hS.logN]; exact run_digit hS inp (by omega)

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

theorem run_y (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F) :
    chAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.s inp.α inp.β inp.t +
      (G.zV (Heap.omega B)).eval inp.t = (S.run inp).y := by
  rw [run_ch hS hV inp, Circuit.zV_eval_eq G B hS.hn]
  show _ = (S.run inp).ch + (S.run inp).digits.getD S.logN 0
  rw [run_wm hS inp]

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

/-- **The one inversion carries the nonzero conditions**: `all ≠ 0` iff `t ∉ V_{m+1}`, `c_h ≠ 0`, `Y ≠ 0` and
`α + P_v(t) + ξ ≠ 0`. -/
theorem all_ne_zero_iff (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F) :
    (S.run inp).all ≠ 0 ↔
      QuotientSecurity.sq^[G.logN + 1] inp.t ≠ 0 ∧
        chAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.s inp.α inp.β inp.t ≠ 0 ∧
        chAt (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.s inp.α inp.β inp.t +
          (G.zV (Heap.omega B)).eval inp.t ≠ 0 ∧
        inp.α + G.pvAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t +
          inp.ξ ≠ 0 := by
  rw [run_all hS inp, run_y hS hV inp, run_ch hS hV inp]
  constructor
  · intro h
    have hT : QuotientSecurity.sq^[G.logN + 1] inp.t ≠ 0 := fun h0 ↦ h (by rw [h0]; ring)
    have hm := wm_ne_zero hT
    refine ⟨hT, fun h0 ↦ h (by rw [h0]; ring), fun h0 ↦ h (by rw [h0]; ring), fun h0 ↦ h ?_⟩
    rw [run_dN hS hV inp hm, h0]
    ring
  · rintro ⟨hT, hch, hy, hd⟩
    have hm := wm_ne_zero hT
    obtain ⟨hden, hrden, -, -⟩ := push_side' hS hV inp hm
    rw [run_dN hS hV inp hm]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hrden hy) hT) hden)
      (mul_ne_zero hch (mul_ne_zero hden hd))

/-- Where `all ≠ 0`: `1/(R_d Y w_{m+1})`. -/
theorem run_invP2 (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) :
    (S.run inp).invP2 = ((S.run inp).rDen * (S.run inp).y * QuotientSecurity.sq^[G.logN + 1] inp.t)⁻¹ := by
  have e : (S.run inp).invP2 = (S.run inp).all⁻¹ * ((S.run inp).ch * (S.run inp).dN) * (S.run inp).den := rfl
  have ha := run_all hS inp
  rw [e, ha]
  rw [ha] at h
  have h1 : (S.run inp).ch * (S.run inp).dN ≠ 0 := right_ne_zero_of_mul h
  have h2 : (S.run inp).den ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have h3 : (S.run inp).rDen * (S.run inp).y * QuotientSecurity.sq^[G.logN + 1] inp.t ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul h)
  have h4 : (S.run inp).ch ≠ 0 := left_ne_zero_of_mul h1
  have h5 : (S.run inp).dN ≠ 0 := right_ne_zero_of_mul h1
  field_simp

/-- **`ρ' = c_q/Y`**, where `all ≠ 0`. -/
theorem run_rhoQ (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) :
    (S.run inp).rhoQ = QuotientSecurity.sq^[G.logN] inp.t / (S.run inp).y := by
  have e : (S.run inp).rhoQ = (S.run inp).digits.getD S.logN 0 * ((S.run inp).invP2 *
      ((S.run inp).rDen * (S.run inp).digits.getD (S.logN + 1) 0)) := rfl
  have hi := run_invP2 hS inp h
  have ha := run_all hS inp
  rw [ha] at h
  have h1 : (S.run inp).rDen ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h)))
  have h2 : (S.run inp).y ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h)))
  have h3 : QuotientSecurity.sq^[G.logN + 1] inp.t ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  rw [e, hi, run_wm hS inp, hS.logN, run_digit hS inp le_rfl]
  field_simp

/-- **W's fold is `foldAt`.** -/
theorem run_fold (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) :
    (S.run inp).fold = foldAt G.logW (fun k ↦ inp.a.getD k 0) inp.ρ := by
  show foldW ((List.range S.logRow).map fun l ↦ sqIter inp.ρ l) S.logRow inp.a = _
  rw [hS.logRow]
  exact foldW_eq_foldAt inp.ρ _ G.logW inp.a fun l hl ↦ by
    simp [List.getD_eq_getElem?_getD, hl, sqIter_eq]

/-- **The verifier's check passes and its claims hold, at the true values, iff `t ∉ V_{m+1}`,
`α + P_v(t) + ξ ≠ 0` and `RecPiop`'s claims hold** (`QClaim` at `c_3`, the sum, the setup's claim, the fold). -/
theorem checks_claims_iff (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid) (inp : Inputs F)
    (ht qt pt qpt sumH κt σt foldTrue : F) :
    ((S.run inp).all ≠ 0 ∧
        idEq (S.run inp) (c3Of S) (S.run inp).rhoQ ht qt pt qpt (QuotientSecurity.sq^[G.logN] inp.t) inp.s ∧
        pushEq (S.run inp) inp.ρ pt qpt (QuotientSecurity.sq^[G.logN] inp.t) inp.s ∧
        sumH = 0 ∧ inp.ξ = κt + inp.β * σt ∧ (S.run inp).fold = foldTrue) ↔
      (QuotientSecurity.sq^[G.logN + 1] inp.t ≠ 0 ∧
        inp.α + G.pvAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t +
          inp.ξ ≠ 0 ∧
        G.QClaim (Heap.omega B) (phiPoly G B (pubOf inp.scalars) inp.γ) (c3Of S)
          (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.ξ inp.s inp.α inp.β inp.γ inp.t inp.ρ
          ht qt pt qpt ∧
        sumH = 0 ∧ inp.ξ = κt + inp.β * σt ∧ foldAt G.logW (fun k ↦ inp.a.getD k 0) inp.ρ = foldTrue) := by
  set v := cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t with hv
  set wm := QuotientSecurity.sq^[G.logN] inp.t with hwm
  set pv := G.pvAt (Heap.omega B) v inp.γ inp.t with hpv
  set rhs := G.rhsAt (Heap.omega B) (phiPoly G B (pubOf inp.scalars) inp.γ) v inp.ξ inp.s inp.α inp.β inp.γ inp.t
    with hrhs
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  -- the claims' equations, where `all ≠ 0`
  have hclaims : (S.run inp).all ≠ 0 →
      ((idEq (S.run inp) (c3Of S) (S.run inp).rhoQ ht qt pt qpt wm inp.s ↔
          (1 + wm / (S.run inp).y) * ht + wm / (S.run inp).y * qt + rhs / (S.run inp).y +
            c3Of S * ((1 + wm / (S.run inp).y) * wm * (pt + inp.s) +
              wm / (S.run inp).y * (qpt + (inp.s + pv) / wm)) = 0) ∧
        (pushEq (S.run inp) inp.ρ pt qpt wm inp.s ↔
          pushComb wm (pt + inp.s) (qpt + (inp.s + pv) / wm) inp.ρ = 0)) := by
    intro h0
    obtain ⟨hT, hch, hy, -⟩ := (all_ne_zero_iff hS hV inp).mp h0
    have hm : wm ≠ 0 := wm_ne_zero hT
    obtain ⟨hden, hrden, -, -⟩ := push_side' hS hV inp hm
    rw [run_y hS hV inp] at hy
    have ey : (S.run inp).y = (S.run inp).ch + wm := by
      show (S.run inp).ch + (S.run inp).digits.getD S.logN 0 = _
      rw [run_wm hS inp]
    have h1 : 1 + wm / (S.run inp).y = (S.run inp).ch / (S.run inp).y := by
      rw [eq_div_iff hy, add_mul, one_mul, div_mul_cancel₀ _ hy, ey, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have hn1 : (S.run inp).num1 / (S.run inp).rDen = rhs := by
      rw [run_rhs hS hV inp hm, mul_div_cancel_left₀ _ hrden]
    have hn3 : (S.run inp).num3 / (S.run inp).den = inp.s + pv := by
      rw [run_num3 hS hV inp hm, mul_div_cancel_left₀ _ hden]
    refine ⟨?_, ?_⟩
    · unfold idEq
      rw [run_rhoQ hS inp h0, hn1, hn3, h1]
      have key : (S.run inp).ch / (S.run inp).y * ht + wm / (S.run inp).y * qt + rhs / (S.run inp).y +
          c3Of S * ((S.run inp).ch / (S.run inp).y * wm * (pt + inp.s) +
            wm / (S.run inp).y * (qpt + (inp.s + pv) / wm)) =
          (rhs + c3Of S * ((S.run inp).ch * wm * inp.s + (inp.s + pv))) / (S.run inp).y +
            ((S.run inp).ch / (S.run inp).y * ht + wm / (S.run inp).y * qt +
              c3Of S * ((S.run inp).ch / (S.run inp).y * wm * pt + wm / (S.run inp).y * qpt)) := by
        field_simp
        ring
      rw [key]
      constructor
      · intro h
        rw [h, CharTwo.add_self_eq_zero]
      · intro h
        exact CharTwo.add_eq_zero.mp h
    · unfold pushEq pushComb
      have e3 : (S.run inp).num3 / (wm * (S.run inp).den) = (inp.s + pv) / wm := by
        rw [← hn3]; field_simp
      rw [e3]
      have key : (1 + inp.ρ) * wm * (pt + inp.s) + inp.ρ * (qpt + (inp.s + pv) / wm) =
          ((1 + inp.ρ) * wm * inp.s + inp.ρ * ((inp.s + pv) / wm)) + ((1 + inp.ρ) * wm * pt + inp.ρ * qpt) := by
        ring
      rw [key]
      constructor
      · intro h
        rw [h, CharTwo.add_self_eq_zero]
      · intro h
        exact CharTwo.add_eq_zero.mp h
  have hnd : (S.run inp).all ≠ 0 → (G.zV (Heap.omega B)).eval inp.t ≠ 0 ∧ chAt v inp.ξ inp.s inp.α inp.β inp.t ≠ 0 ∧
      chAt v inp.ξ inp.s inp.α inp.β inp.t + (G.zV (Heap.omega B)).eval inp.t ≠ 0 := by
    intro h0
    obtain ⟨hT, hch, hy, -⟩ := (all_ne_zero_iff hS hV inp).mp h0
    exact ⟨by rw [Circuit.zV_eval_eq G B hS.hn]; exact wm_ne_zero hT, hch, hy⟩
  have hzv : (G.zV (Heap.omega B)).eval inp.t = wm := Circuit.zV_eval_eq G B hS.hn _
  have hyv : chAt v inp.ξ inp.s inp.α inp.β inp.t + (G.zV (Heap.omega B)).eval inp.t = (S.run inp).y :=
    run_y hS hV inp
  constructor
  · rintro ⟨h0, hi, hp, hs, hξ, hf⟩
    obtain ⟨hT, hch, hy, hd⟩ := (all_ne_zero_iff hS hV inp).mp h0
    refine ⟨hT, hd, ⟨(hnd h0).1, (hnd h0).2.1, (hnd h0).2.2, ?_, ?_⟩, hs, hξ, by rw [← hf, run_fold hS inp]⟩
    · rw [hyv, hzv]; exact ((hclaims h0).1).mp hi
    · rw [hzv]; exact ((hclaims h0).2).mp hp
  · rintro ⟨hT, hd, ⟨hcq, hch, hy, hi, hp⟩, hs, hξ, hf⟩
    have h0 : (S.run inp).all ≠ 0 := (all_ne_zero_iff hS hV inp).mpr ⟨hT, hch, hy, hd⟩
    rw [hyv, hzv] at hi
    rw [hzv] at hp
    exact ⟨h0, ((hclaims h0).1).mpr hi, ((hclaims h0).2).mpr hp, hs, hξ, by rw [run_fold hS inp, hf]⟩

/-- **The same with `RecPiop.Post2`**, for any tables' model `Mo` whose `Φ` is `phiPoly` and whose constant is
`c_3` (its `h`, `q`, `P`, `q_P`, `S`, the setup's `σ`, `κ`, `W`'s true fold values; `P`'s share of the claims read as
`P(t) + S(t)/Z_V(t)` and the sum `Σ_V (h + c_3 S)`, `Q`'s empty slot `12` the prover's), the statement `s` with the public


limbs `pubOf` of the public scalars, the fold values `a` (`2^r` of them), `ξ` and `s` the round's message. -/
theorem checks_claims_iff_post2 {St M : Type} (hS : SpecOf S G B pairOf portOf pubOf) (hV : G.Valid)
    (inp : Inputs F) (Mo : Model G (Heap.omega B) M) (hphi : ∀ pub γ, Mo.phi pub γ = phiPoly G B pub γ)
    (hc : Mo.idC = c3Of S) (pubOf' : St → ℕ → List F) (s : St)
    (hpub : pubOf' s = pubOf inp.scalars) (cW cQ : M) (ha : inp.a.length = 2 ^ G.logW) :
    ((S.run inp).all ≠ 0 ∧
        idEq (S.run inp) (c3Of S) (S.run inp).rhoQ ((Mo.hP cQ).eval inp.t) ((Mo.qP cQ).eval inp.t)
          ((Mo.pP cQ).eval inp.t + (Mo.sP cQ).eval inp.t / (G.zV (Heap.omega B)).eval inp.t) ((Mo.qPP cQ).eval inp.t)
          (QuotientSecurity.sq^[G.logN] inp.t) inp.s ∧
        pushEq (S.run inp) inp.ρ ((Mo.pP cQ).eval inp.t + (Mo.sP cQ).eval inp.t / (G.zV (Heap.omega B)).eval inp.t)
          ((Mo.qPP cQ).eval inp.t) (QuotientSecurity.sq^[G.logN] inp.t) inp.s ∧
        ∑ i ∈ range G.N, ((Mo.hP cQ).eval (Heap.omega B i) + Mo.idC * (Mo.sP cQ).eval (Heap.omega B i)) = 0 ∧
        inp.ξ = Mo.setup.κP.eval inp.t + inp.β * Mo.setup.σP.eval inp.t ∧
        (S.run inp).fold = foldAt G.logW (Mo.fold cW inp.t) inp.ρ) ↔
      (QuotientSecurity.sq^[G.logN + 1] inp.t ≠ 0 ∧
        inp.α + G.pvAt (Heap.omega B) (cellsOf G.logW (Heap.omega B) (fun k ↦ inp.a.getD k 0) inp.t) inp.γ inp.t +
          inp.ξ ≠ 0 ∧
        Post2 G (Heap.omega B) Mo pubOf' s cW [inp.α, inp.β, inp.γ] cQ [inp.t] (inp.a ++ [inp.ξ, inp.s]) [inp.ρ]) := by
  rw [checks_claims_iff hS hV inp]
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
  unfold Post2 SumOK abc
  simp only [List.getD_cons_zero, List.getD_cons_succ, hxi, hsv, hcells, hfold, hpub, hphi, hc]
  constructor
  · rintro ⟨hT, hd, hq, hs, hξ, hf⟩
    exact ⟨hT, hd, hs, hξ, hq, hf⟩
  · rintro ⟨hT, hd, hs, hξ, hq, hf⟩
    exact ⟨hT, hd, hq, hs, hξ, hf⟩

/-! ## The claims' points, for the tables' layer -/

/-- **The digits' inverses**, where `all ≠ 0`: `1/w_l` for `l ≤ m + 1`. -/
theorem run_wInvs (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) {l : ℕ}
    (hl : l ≤ G.logN + 1) : (S.run inp).wInvs.getD l 0 = (QuotientSecurity.sq^[l] inp.t)⁻¹ := by
  have ha := run_all hS inp
  have hT : QuotientSecurity.sq^[G.logN + 1] inp.t ≠ 0 := by
    rw [ha] at h; exact right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have htop : (S.run inp).invTop = ((S.run inp).digits.getD (S.logN + 1) 0)⁻¹ := by
    have e : (S.run inp).invTop = (S.run inp).invP2 * (S.run inp).p1 := rfl
    have ep : (S.run inp).p1 = (S.run inp).rDen * (S.run inp).y := rfl
    rw [e, run_invP2 hS inp h, ep, hS.logN, run_digit hS inp le_rfl]
    rw [ha] at h
    have h1 : (S.run inp).rDen * (S.run inp).y ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
    rw [mul_inv, mul_right_comm, inv_mul_cancel₀ h1, one_mul]
  have e : (S.run inp).wInvs = wInvsList (S.run inp).digits (S.logN + 1) (S.run inp).invTop := rfl
  rw [e, htop, hS.logN,
    wInvsList_getD inp.t (S.run inp).digits (fun l hl ↦ run_digit hS inp hl) hT hl, run_digit hS inp hl]

/-- **`u_l = w_l/(1 + w_l)`** (`Q`'s point in the novel basis), where `all ≠ 0`. -/
theorem run_u (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) {l : ℕ}
    (hl : l < G.logN + 1) :
    (S.run inp).uList.getD l 0 = QuotientSecurity.sq^[l] inp.t / (1 + QuotientSecurity.sq^[l] inp.t) := by
  have ha := run_all hS inp
  have hT : QuotientSecurity.sq^[G.logN + 1] inp.t ≠ 0 := by
    rw [ha] at h; exact right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have e : (S.run inp).uList = (List.range (S.logN + 1)).map fun l ↦
      1 + (S.run inp).wInvs.getD l 0 + (S.run inp).wInvs.getD (l + 1) 0 := rfl
  have hl' : l < S.logN + 1 := by rw [hS.logN]; exact hl
  rw [e]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl', Option.map_some,
    Option.getD_some]
  rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, run_wInvs hS inp h hl.le,
    run_wInvs hS inp h (by omega : l + 1 ≤ G.logN + 1), Function.iterate_succ_apply', sq_eq_mul]
  have h0 : QuotientSecurity.sq^[l] inp.t ≠ 0 := digit_ne_zero_of_le (by omega) hT
  have h1 : 1 + QuotientSecurity.sq^[l] inp.t ≠ 0 := by
    have := digit_ne_zero_of_le (l := l + 1) (by omega) hT
    rw [Function.iterate_succ_apply', sq_eq_mul] at this
    exact right_ne_zero_of_mul this
  field_simp
  ring_nf
  rw [CharTwo.two_eq_zero]
  ring

/-- **`t/w_{m+1} = Π_{l<m+1} (1 + w_l)^{-1}`** (the scale of `Q`'s value), where `w_{m+1}(t) ≠ 0`. -/
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

/-- **`Q`'s identity claim's value** is `s_E Π_{l ≤ m} (1 + w_l)^{-1} (num_1/R_d + c_3 (c_h w_m s + num_3/B))/Y`, where
`all ≠ 0`. -/
theorem run_quotientValue (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) :
    (S.run inp).quotientValue = S.scale * (∏ l ∈ range (G.logN + 1), (1 + QuotientSecurity.sq^[l] inp.t)⁻¹) *
      (((S.run inp).num1 / (S.run inp).rDen + c3Of S * ((S.run inp).ch * QuotientSecurity.sq^[G.logN] inp.t * inp.s +
        (S.run inp).num3 / (S.run inp).den)) / (S.run inp).y) := by
  have ha := run_all hS inp
  rw [ha] at h
  have hT : QuotientSecurity.sq^[G.logN + 1] inp.t ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have hrd : (S.run inp).rDen ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h)))
  have hy : (S.run inp).y ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h)))
  have hden : (S.run inp).den ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have hcd : (S.run inp).ch * (S.run inp).dN ≠ 0 := right_ne_zero_of_mul h
  have e : (S.run inp).quotientValue = S.scale * inp.t * ((S.run inp).all⁻¹ * ((S.run inp).ch * (S.run inp).dN)) *
      ((S.run inp).num1 * (S.run inp).den + c3Of S * ((S.run inp).rDen * ((S.run inp).ch *
        ((S.run inp).digits.getD S.logN 0 * (inp.s * (S.run inp).den)) + (S.run inp).num3))) := rfl
  rw [e, run_wm hS inp, ← digitsScale_eq hT, ha]
  have hch : (S.run inp).ch ≠ 0 := left_ne_zero_of_mul hcd
  have hdN : (S.run inp).dN ≠ 0 := right_ne_zero_of_mul hcd
  field_simp

/-- **`Q`'s pushes' claim's value** is `(s_E/L_0) Π_{l ≤ m} (1 + w_l)^{-1} ((1 + ρ) w_m s + ρ num_3/(w_m B))`, where
`all ≠ 0`. -/
theorem run_pushesValue (hS : SpecOf S G B pairOf portOf pubOf) (inp : Inputs F) (h : (S.run inp).all ≠ 0) :
    (S.run inp).pushesValue = S.scale * ((1 + S.y0) * (1 + S.y1))⁻¹ *
      (∏ l ∈ range (G.logN + 1), (1 + QuotientSecurity.sq^[l] inp.t)⁻¹) *
      ((1 + inp.ρ) * QuotientSecurity.sq^[G.logN] inp.t * inp.s +
        inp.ρ * ((S.run inp).num3 / (QuotientSecurity.sq^[G.logN] inp.t * (S.run inp).den))) := by
  have hw := run_wInvs hS inp h (l := G.logN) (by omega)
  have ha := run_all hS inp
  rw [ha] at h
  have hT : QuotientSecurity.sq^[G.logN + 1] inp.t ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have hm : QuotientSecurity.sq^[G.logN] inp.t ≠ 0 := wm_ne_zero hT
  have hp1 : (S.run inp).rDen * (S.run inp).y ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have hden : (S.run inp).den ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have hcd : (S.run inp).ch * (S.run inp).dN ≠ 0 := right_ne_zero_of_mul h
  have e : (S.run inp).pushesValue = S.scale * ((1 + S.y0) * (1 + S.y1))⁻¹ * inp.t *
      ((1 + inp.ρ) * ((S.run inp).digits.getD S.logN 0 * (S.run inp).digits.getD S.logN 0 * (inp.s * (S.run inp).den)) +
        inp.ρ * (S.run inp).num3) * ((S.run inp).all⁻¹ * ((S.run inp).ch * (S.run inp).dN) *
          ((S.run inp).rDen * (S.run inp).y)) * (S.run inp).wInvs.getD S.logN 0 := rfl
  rw [e, run_wm hS inp, ← digitsScale_eq hT, ha, hS.logN] at *
  rw [hw]
  have hch : (S.run inp).ch ≠ 0 := left_ne_zero_of_mul hcd
  have hdN : (S.run inp).dN ≠ 0 := right_ne_zero_of_mul hcd
  have hrd : (S.run inp).rDen ≠ 0 := left_ne_zero_of_mul hp1
  have hy : (S.run inp).y ≠ 0 := right_ne_zero_of_mul hp1
  generalize S.scale * ((1 + S.y0) * (1 + S.y1))⁻¹ = K
  field_simp

end Main

end RecStatement
