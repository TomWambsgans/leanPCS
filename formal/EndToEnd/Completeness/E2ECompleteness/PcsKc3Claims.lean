-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the converse of `PcsBridge/Kc3Accepts.lean`'s `accepts_of_claims`, for completeness.
import PcsBridge.Kc3Accepts

/-!
# The deployed claims hold of tables that F1's verifier accepts

`PcsBridge.Kc3.claimsAt_spec` gives the three claims `claimsAt` returns, and `accepts_of_claims` reads the claims
as F1's `Accepts`. Here, the converse, for completeness:

* **`claimsAt_isSome`**: at challenges where no denominator vanishes (`NonDeg`), `claimsAt` returns claims;
* **`claims_of_accepts`**: if F1's verifier accepts the tables' polynomials (`Accepts` of `witnessOfTable cW` and
  `readTM cT`, for parameters matching the statement's constants), the claims hold of the tables.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace E2ECompleteness.Pcs

open LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity PcsBridge.Kc3

/-- **The denominators `claimsAt` inverts do not vanish.** -/
structure NonDeg (α β t ρ : E) (v : Fin 3 → E) (next : E) : Prop where
  one_add : ∀ k < 24, 1 + sq^[k] t ≠ 0
  zeta : 1 + sq^[24] t * t ≠ 0
  copy : sq^[24] t * t + (α + v 0 + β * t) * (α + v 0 + β * next) ≠ 0
  rows : rowsAt t ≠ 0
  pins : ∀ k < 11, t + pinE k ≠ 0
  conic : (witnessConic t (sq t) ρ).1 + (witnessConic t (sq t) ρ).2 ≠ 0

set_option maxHeartbeats 1000000 in
/-- **`claimsAt` returns claims** where no denominator vanishes. -/
theorem claimsAt_isSome (stmt : Statement) {α β μ t ρ : E} {v : Fin 3 → E} {next : E}
    (hN : NonDeg α β t ρ v next) : ∃ cl, claimsAt 22 stmt α β μ t ρ (Vector.ofFn v) next = some cl := by
  unfold claimsAt
  lift_lets
  extract_lets m w wAt x c vy gate tau rows d dNext product z zeta pubWords
  have hm : m = 24 := rfl
  have hw : w = (List.range 25).map fun k => sq^[k] t := digitsOf_eq t 24
  have hwAt : ∀ k < 25, wAt k = sq^[k] t := fun k hk => by simp only [wAt, hw, getD_map_range _ hk]
  have hx : x = v 0 := by simp [x]
  have hz : z = sq^[24] t := hwAt 24 (by norm_num)
  have hzeta : zeta = sq^[24] t * t := by rw [show zeta = z * t from rfl, hz]
  have hprod : product = (α + v 0 + β * t) * (α + v 0 + β * next) := by
    simp only [product, d, dNext, hx]
  have hrows : rows = rowsAt t := by
    simp only [rows, tau, hm, rowsAt]
    rw [show 24 - 1 = 23 from rfl, foldl_add_range, zero_add]
    exact sum_congr rfl fun k hk => by rw [hwAt k (by simp at hk; omega)]
  generalize hcon : witnessConic t (wAt 1) ρ = cc
  rcases cc with ⟨cA, cB⟩
  have hcon' : witnessConic t (sq t) ρ = (cA, cB) := by
    rw [← hcon, hwAt 1 (by norm_num)]; rfl
  dsimp (config := { zeta := false }) only
  extract_lets denominators
  rw [if_neg]
  · exact ⟨_, rfl⟩
  intro hany
  obtain ⟨a, ha, ha0⟩ := List.any_eq_true.mp hany
  have ha0 : a = 0 := by simpa using ha0
  subst ha0
  simp only [denominators, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at ha
  rcases ha with ((⟨k, hk, hk0⟩ | h | h | h) | ⟨p, hp, hp0⟩) | h
  · rw [hm] at hk
    exact hN.one_add k hk (by rw [← hwAt k (by omega)]; exact hk0)
  · exact hN.zeta (by rw [← hzeta]; exact h.symm)
  · exact hN.copy (by rw [← hzeta, ← hprod]; exact h.symm)
  · exact hN.rows (by rw [← hrows]; exact h.symm)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    have hk' : k < 11 := List.mem_range.mp hk
    exact hN.pins k hk' hp0
  · have := hN.conic
    rw [hcon'] at this
    exact this h.symm

/-- **The claims hold of tables that F1's verifier accepts.** -/
theorem claims_of_accepts (P : _root_.Kc3.Params E) {s₀ : (Fin 24 → Bool) → E} (hM : Matches P s₀)
    {stmt : Statement} {α β μ t ρ : E} {v : Fin 3 → E} {next : E} {cl : Claims}
    (h : claimsAt 22 stmt α β μ t ρ (Vector.ofFn v) next = some cl)
    (cW : (Fin 24 → Bool) → E) (cT : (Fin 28 → Bool) → E)
    (hA : P.Accepts (fun k => ofK (anchorValues stmt.words k)) (witnessOfTable cW) (readTM cT) α β μ t v next ρ) :
    mle cW (fun k => cl.witness.point.getD k 0) = cl.witness.value ∧
      mle s₀ (fun k => cl.wiring.point.getD k 0) = cl.wiring.value ∧
      mle cT (fun k => cl.copy.point.getD k 0) = cl.copy.value := by
  have S := claimsAt_spec h
  have ht2 : ∀ i : Fin 22, 1 + sq^[(i : ℕ) + 2] t ≠ 0 := fun i => S.one_add _ (by omega)
  have ht0 : ∀ i : Fin 24, 1 + sq^[(i : ℕ)] t ≠ 0 := fun i => S.one_add _ i.2
  have hconic : _root_.Kc3.Params.conic P.θ t ρ = witnessConic t (QuotientSecurity.sq t) ρ := by
    rw [hM.theta]
    simp only [witnessConic, _root_.Kc3.Params.conic, QuotientSecurity.sq]
  have hz1 : (_root_.Kc3.Params.conic P.θ t ρ).1 /
      ((_root_.Kc3.Params.conic P.θ t ρ).1 + (_root_.Kc3.Params.conic P.θ t ρ).2) = z1Of t ρ := by
    rw [hconic, z1Of]
  have hpin := pinned_eq P hM.pins stmt t (v 0) S.pins
  unfold _root_.Kc3.Params.Accepts at hA
  dsimp only at hA
  rw [hz1, hconic, hM.vCells, hM.vRows] at hA
  obtain ⟨hAw, hAs, -, -, -, -, hAc⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · rw [S.wPoint, S.wValue, witness_mle' cW t ρ _ ht2, div_left_inj' (claimScale_ne_zero ht2), hAw,
      Fin.sum_univ_three, hM.theta]
    simp only [witnessWeights, _root_.Kc3.Params.conicWeights, QuotientSecurity.sq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  · rw [S.sPoint, S.sValue, wiring_claim s₀ t next (fun i => ht0 i), ← hM.sigma t]
    exact hAs
  · rw [S.cPoint, S.cValue, copy_mle cT t _ _ ey one_add_ey_ne_zero one_add_ey_sq_ne_zero ht0]
    have hq : (P.qPoly (readTM cT)).eval t =
        (limbPoly ey cT false false).eval t + QuotientSecurity.sq^[24] t * t * (limbPoly ey cT true false).eval t := by
      rw [_root_.Kc3.Params.qPoly, _root_.Kc3.Params.zeta, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_mul, Polynomial.eval_X, hM.vCells, readTM_A₀, readTM_A₁]
    have hxh : (P.xhPoly (readTM cT)).eval t =
        (limbPoly ey cT false true).eval t + QuotientSecurity.sq^[24] t * t * (limbPoly ey cT true true).eval t := by
      rw [_root_.Kc3.Params.xhPoly, _root_.Kc3.Params.zeta, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_mul, Polynomial.eval_X, hM.vCells, readTM_B₀, readTM_B₁]
    rw [hq, hxh, hpin] at hAc
    have hZ : 1 + QuotientSecurity.sq^[24] t * t ≠ 0 := S.zeta
    have he : 1 + QuotientSecurity.sq^[24] t * t / (1 + QuotientSecurity.sq^[24] t * t) =
        (1 + QuotientSecurity.sq^[24] t * t)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [add_mul, one_mul, div_mul_cancel₀ _ hZ, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [he]
    simp only [div_eq_mul_inv, mul_inv, _root_.Kc3.gate] at hAc ⊢
    linear_combination ((1 + QuotientSecurity.sq^[24] t * t)⁻¹ * ((1 + ey)⁻¹ * (1 + ey ^ 2)⁻¹) *
      (claimScale 0 24 t)⁻¹) * hAc

end E2ECompleteness.Pcs
