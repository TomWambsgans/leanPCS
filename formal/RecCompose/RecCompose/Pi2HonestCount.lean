-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The counting follows `formal/RecPiop`'s (`Copy.lean`:
-- `card_dPull_eq_zero_le`; `Identity.lean`: `card_eval_eq_zero_le`, the degrees).
import RecCompose.Pi2HonestThm

/-!
# π2's honest prover: how many challenges are bad (π2v3)

* **`card_badCopy_le`**: at most `2N |E|²` triples `(α, β, γ)` are in `BadCopy`: each of the non-holes' `d_pull` and
  `d_push` is `α + f(γ) + β g(γ)`, zero at `|E|²` triples (`α` determined by `β, γ`, `card_den_zero_le`).
* **`card_badT_le`**: for a witness, a triple off `BadCopy` and a circuit with a non-hole position, at most `9N`
  points `t` are in `BadT`: `V_{m+1}` has `2N` points (`w_{m+1}`, monic of degree `2N`), and `d_pull d_push`,
  `d_pull d_push + Z_V` and `α + P_v + κ + β σ` are nonzero polynomials (at a non-hole `ω_i` they are
  `d_pull(i) d_push(i)` and `d_push(i)`, nonzero) of degrees at most `2N`, `2N` and `3N`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Finset Polynomial

/-- **A denominator `α + f(γ) + β g(γ)` is zero at `|E|²` triples.** -/
theorem card_den_zero_le (f g : E → E) :
    (univ.filter fun v : E × E × E ↦ v.1 + f v.2.2 + v.2.1 * g v.2.2 = 0).card ≤ Fintype.card E ^ 2 := by
  classical
  refine (Finset.card_le_card (t := univ.image fun p : E × E ↦ (f p.2 + p.1 * g p.2, p.1, p.2))
    fun v hv ↦ ?_).trans (Finset.card_image_le.trans (by simp [sq]))
  rw [Finset.mem_filter] at hv
  refine Finset.mem_image.mpr ⟨(v.2.1, v.2.2), Finset.mem_univ _, ?_⟩
  have : v.1 = f v.2.2 + v.2.1 * g v.2.2 := CharTwo.add_eq_zero.mp (by rw [← hv.2]; ring)
  rw [← this]

open Classical in
/-- **At most `2N |E|²` triples are bad for the copy argument.** -/
theorem card_badCopy_le (G : RecPiop.Circuit E) (w : ℕ → K) (pub : ℕ → List E) :
    (univ.filter fun v : E × E × E ↦ BadCopy G w pub v.1 v.2.1 v.2.2).card ≤ 2 * G.N * Fintype.card E ^ 2 := by
  classical
  set NH := (range G.N).filter fun i ↦ ¬ G.IsHole i with hNH
  have hsub : (univ.filter fun v : E × E × E ↦ BadCopy G w pub v.1 v.2.1 v.2.2) ⊆
      (NH.biUnion fun i ↦ univ.filter fun v : E × E × E ↦
          RecPiop.dPull pi2Omega (RecCircuit.emb w) v.1 v.2.1 i = 0) ∪
        (NH.biUnion fun i ↦ univ.filter fun v : E × E × E ↦
          G.dPushV pi2Omega (RecCircuit.emb w) v.1 v.2.1 i = 0) := by
    intro v hv
    have hv' := (mem_filter.mp hv).2
    unfold BadCopy at hv'
    simp only [mem_union, mem_biUnion, mem_range, mem_filter, mem_univ, true_and, hNH]
    rcases hv' with ⟨i, hi, hh, h⟩ | ⟨i, hi, hh, h⟩
    · exact Or.inl ⟨i, ⟨hi, hh⟩, h⟩
    · exact Or.inr ⟨i, ⟨hi, hh⟩, h⟩
  have e1 : ∀ i, (univ.filter fun v : E × E × E ↦ RecPiop.dPull pi2Omega (RecCircuit.emb w) v.1 v.2.1 i = 0).card ≤
      Fintype.card E ^ 2 := fun i ↦ card_den_zero_le (fun _ ↦ RecCircuit.emb w i) (fun _ ↦ pi2Omega i)
  have e2 : ∀ i, (univ.filter fun v : E × E × E ↦ G.dPushV pi2Omega (RecCircuit.emb w) v.1 v.2.1 i = 0).card ≤
      Fintype.card E ^ 2 := fun i ↦
    card_den_zero_le (fun _ ↦ G.pushV (RecCircuit.emb w) i) (fun _ ↦ pi2Omega (G.sigma i))
  have hcNH : NH.card ≤ G.N := (card_filter_le _ _).trans (by rw [card_range])
  calc _ ≤ _ := card_le_card hsub
    _ ≤ NH.card * Fintype.card E ^ 2 + NH.card * Fintype.card E ^ 2 := by
        refine (card_union_le _ _).trans (add_le_add ?_ ?_)
        · exact card_biUnion_le.trans ((Finset.sum_le_sum fun i _ ↦ e1 i).trans (by rw [sum_const, smul_eq_mul]))
        · exact card_biUnion_le.trans ((Finset.sum_le_sum fun i _ ↦ e2 i).trans (by rw [sum_const, smul_eq_mul]))
    _ ≤ 2 * G.N * Fintype.card E ^ 2 := by
        have := Nat.mul_le_mul_right (Fintype.card E ^ 2) hcNH
        nlinarith

/-! ## The bad points `t` -/

/-- The honest setup's polynomials (`sigmaPoly`, `kappaPoly`). -/
noncomputable def setupOfG (G : RecPiop.Circuit E) (hm : G.logN ≤ 28) : RecPiop.SetupPolys G pi2Omega where
  σP := sigmaPoly G
  κP := kappaPoly G
  σ_deg := UniKeccakComplete.AlgC.novP_natDegree_lt _ _
  κ_deg := UniKeccakComplete.AlgC.novP_natDegree_lt _ _
  σ_eval _ hi := sigmaPoly_omega G hm hi
  κ_eval _ hi := kappaPoly_omega G hm hi

/-- A polynomial nonzero at a point is nonzero. -/
theorem ne_zero_of_eval_ne {p : E[X]} {x : E} (h : p.eval x ≠ 0) : p ≠ 0 := fun h0 ↦ h (by rw [h0, Polynomial.eval_zero])

open Classical in
/-- **At most `9N` points `t` are bad**, for a witness, a triple off `BadCopy` and a circuit with a non-hole
position. -/
theorem card_badT_le (G : RecPiop.Circuit E) (hV : G.Valid) (hK : KCircuit G) (hm : G.logN ≤ 28) (w : ℕ → K)
    (pub : ℕ → List E) (hw : G.Satisfies pub (RecCircuit.emb w)) (α β γ : E) (hbad : ¬ BadCopy G w pub α β γ)
    (hnh : ∃ i < G.N, ¬ G.IsHole i) :
    (univ.filter fun t ↦ BadT G w α β γ t).card ≤ 9 * G.N := by
  classical
  have hpts := RecPiop.Points.ofCantor UniComplete.Domain.basisE
  have hN2 := RecPiop.Circuit.N_ge_two hV
  have hn : G.logN ≤ 32 := by omega
  set S := setupOfG G hm with hS
  obtain ⟨i, hi, hh⟩ := hnh
  have hpull : RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i ≠ 0 := fun h0 ↦ hbad (Or.inl ⟨i, hi, hh, h0⟩)
  have hpush : G.dPushV pi2Omega (RecCircuit.emb w) α β i ≠ 0 := fun h0 ↦ hbad (Or.inr ⟨i, hi, hh, h0⟩)
  have hwv : ∀ j < G.N, (witnessPoly G w).eval (pi2Omega j) = RecCircuit.emb w j :=
    fun j hj ↦ witnessPoly_omega G w hm hj
  set B := RecPiop.dPullP (witnessPoly G w) α β * dPushH G w α β with hB
  set Y := B + G.zV pi2Omega with hY
  set P := C α + G.pushPolyV pi2Omega (witnessPoly G w) γ + kappaPoly G + C β * sigmaPoly G with hP
  have hpullv : (RecPiop.dPullP (witnessPoly G w) α β).eval (pi2Omega i) = RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i := by
    rw [RecPiop.Circuit.dPullP_eval]
    simp only [RecPiop.dPull, RecPiop.den, hwv i hi]
  have hpushv : (dPushH G w α β).eval (pi2Omega i) = G.dPushV pi2Omega (RecCircuit.emb w) α β i := by
    unfold dPushH RecPiop.Circuit.dPushV RecPiop.den
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [pushPolyH_omega G hK w hw hm hi, kappaPoly_omega G hm hi, sigmaPoly_omega G hm hi]
    unfold pvValue
    rw [add_assoc α, add_assoc (G.pushV _ i), CharTwo.add_self_eq_zero, add_zero]
  have hBi : B.eval (pi2Omega i) ≠ 0 := by
    rw [hB, Polynomial.eval_mul, hpullv, hpushv]
    exact mul_ne_zero hpull hpush
  have hYi : Y.eval (pi2Omega i) ≠ 0 := by
    rw [hY, Polynomial.eval_add, RecPiop.Circuit.zV_eval hi, add_zero]
    exact hBi
  have hPi : P.eval (pi2Omega i) ≠ 0 := by
    have h := RecPiop.Circuit.pushPolyV_eval hV hpts hn (witnessPoly G w) γ hi
    have e : G.pushV (fun j ↦ (witnessPoly G w).eval (pi2Omega j)) i = G.pushV (RecCircuit.emb w) i := by
      unfold RecPiop.Circuit.pushV
      simp only [hh, ↓reduceIte]
      exact G.push_congr_off_holes hV (fun j hj _ ↦ hwv j hj) 0 hi
    rw [hP]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [kappaPoly_omega G hm hi, sigmaPoly_omega G hm hi, add_assoc α, h, e]
    exact hpush
  have hsub : (univ.filter fun t ↦ BadT G w α β γ t) ⊆
      (univ.filter fun t ↦ (UniComplete.Domain.wP (G.logN + 1)).eval t = 0) ∪
        (univ.filter fun t ↦ B.eval t = 0) ∪ (univ.filter fun t ↦ Y.eval t = 0) ∪
          univ.filter fun t ↦ P.eval t = 0 := by
    intro t ht
    have ht' := (mem_filter.mp ht).2
    unfold BadT at ht'
    simp only [mem_union, mem_filter, mem_univ, true_and]
    rcases ht' with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (by rw [wP_eval_sq]; exact h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  -- `V_{m+1}`
  have hA : (univ.filter fun t ↦ (UniComplete.Domain.wP (G.logN + 1)).eval t = 0).card ≤ 2 * G.N := by
    refine (RecPiop.Circuit.card_eval_eq_zero_le _ (UniComplete.Domain.wP_monic _).ne_zero).trans ?_
    rw [UniComplete.Domain.wP_natDegree, pow_succ]
    unfold RecPiop.Circuit.N
    omega
  have hwdeg : (witnessPoly G w).natDegree ≤ G.N - 1 := by
    have := UniKeccakComplete.AlgC.novP_natDegree_lt G.logN fun j ↦
      (UniComplete.novelOfValuesK G.logN (wValues G w)).getD j 0
    unfold witnessPoly
    unfold RecPiop.Circuit.N
    omega
  have hpdeg : (pushPolyH G w).natDegree < G.N := UniKeccakComplete.AlgC.novP_natDegree_lt _ _
  have h1 := RecPiop.Circuit.natDegree_dPullP_le (D := G.N - 1) hwdeg (by omega) α β
  have h2 : (dPushH G w α β).natDegree ≤ G.N - 1 := RecPiop.Circuit.natDegree_dPushP_le S hpdeg α β
  have hBdeg : B.natDegree ≤ 2 * G.N := (natDegree_mul_le_of_le h1 h2).trans (by omega)
  have hYdeg : Y.natDegree ≤ 2 * G.N := (natDegree_add_le _ _).trans (max_le hBdeg
    ((RecPiop.Circuit.natDegree_zV_le (G := G) (ω := pi2Omega)).trans (by omega)))
  have hPdeg : P.natDegree ≤ 3 * G.N := by
    have hv := RecPiop.Circuit.natDegree_pushPolyV_le (ω := pi2Omega) hV (wP := witnessPoly G w) (by omega) γ
    have hk : (kappaPoly G).natDegree < G.N := UniKeccakComplete.AlgC.novP_natDegree_lt _ _
    have hs : (sigmaPoly G).natDegree < G.N := UniKeccakComplete.AlgC.novP_natDegree_lt _ _
    rw [hP]
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le (by rw [natDegree_C]; omega) (hv.trans (by omega))))
      (by omega))) ((natDegree_C_mul_le _ _).trans (by omega)))
  have hBc := (RecPiop.Circuit.card_eval_eq_zero_le _ (ne_zero_of_eval_ne hBi)).trans hBdeg
  have hYc := (RecPiop.Circuit.card_eval_eq_zero_le _ (ne_zero_of_eval_ne hYi)).trans hYdeg
  have hPc := (RecPiop.Circuit.card_eval_eq_zero_le _ (ne_zero_of_eval_ne hPi)).trans hPdeg
  calc _ ≤ _ := card_le_card hsub
    _ ≤ 2 * G.N + 2 * G.N + 2 * G.N + 3 * G.N :=
        (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add
          ((card_union_le _ _).trans (add_le_add hA hBc)) hYc)) hPc)
    _ = 9 * G.N := by ring

end RecCompose

/-- info: 'RecCompose.card_badCopy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.card_badCopy_le

/-- info: 'RecCompose.card_badT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.card_badT_le
