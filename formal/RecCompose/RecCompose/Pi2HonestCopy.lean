-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The polynomials are `formal/RecPiop`'s (`Identity.lean`:
-- `idPoly`, `defPoly`, `idPoly_eval_omega`, `pushPolyV_eval`, `natDegree_idPoly_le`; `Ports.lean`: `push_port`).
import RecCompose.Pi2HonestBase

/-!
# π2's honest prover: the copy argument's sum, `P`'s definition and the identity (π2v3)

For a witness satisfying the circuit (`RecPiop.Circuit.Satisfies`) and the honest `h` on `V_m` (`hValues`: zero at
the holes, `1/d_pull + 1/d_push` elsewhere):

* **`sum_hValues`** (`SumOK`): `Σ_V h = 0`: the pulls and the pushes of the non-holes cancel (`σ` is a bijection of
  the non-holes, `w(σ_i) = P_v(i) + κ_i`, characteristic two). No denominator need be nonzero: a zero one is inverted
  to zero on both sides.
* **`P`'s definition**: for a `P` taking `P_v + κ`'s values on `V_m` (`pvValue`), `P + P_v` vanishes there, so
  **`q_P = (P + P_v) /ₘ Z_V`** makes `defPoly` zero (`defPoly_qpHonest`), of degree below `2N`.
* **The identity**: with every pulled `d_pull` and every `d_push` on `V_m` nonzero, the identity without `q`
  (`numPoly`: `h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T`) vanishes on `V_m` (`numPoly_eval_omega`: at a
  hole `h = 0`, `1 + 1_S = 0` and `T = E_p + F_j = 0`, the port holding), so `Z_V` divides it (`num_eq_zV_mul`) and
  **`q = numPoly /ₘ Z_V`** makes the identity zero (`idPoly_qHonest`), of degree below `2N` (`natDegree_qHonest_lt`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters Finset Polynomial

variable {G : RecPiop.Circuit E}

/-! ## `h` on `V_m` -/

/-- **`h` at position `i`**: zero at a hole, `1/d_pull(i) + 1/d_push(i)` elsewhere. -/
theorem hValues_getD (w : ℕ → K) (α β : E) {i : ℕ} (hi : i < G.N) :
    (hValues G w α β).getD i 0 =
      if G.IsHole i then 0 else (RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i)⁻¹ +
        (G.dPushV pi2Omega (RecCircuit.emb w) α β i)⁻¹ := by
  unfold hValues
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hi, dite_true, Option.getD_some]
  unfold RecPiop.dPull RecPiop.Circuit.dPushV RecPiop.den RecPiop.Circuit.IsHole
  rw [pi2Omega_eq, pi2Omega_eq]
  rfl

theorem size_hValues (w : ℕ → K) (α β : E) : (hValues G w α β).size = 2 ^ G.logN := by
  simp [hValues, RecPiop.Circuit.N]

/-- **A non-hole's push is its target's pull**, for a witness. -/
theorem dPushV_nonhole (w : ℕ → K) {pub : ℕ → List E} (hw : G.Satisfies pub (RecCircuit.emb w)) (α β : E) {i : ℕ}
    (hi : i < G.N) (hh : ¬ G.IsHole i) :
    G.dPushV pi2Omega (RecCircuit.emb w) α β i = RecPiop.dPull pi2Omega (RecCircuit.emb w) α β (G.sigma i) := by
  unfold RecPiop.Circuit.dPushV RecPiop.dPull RecPiop.Circuit.pushV
  rw [ite_eq_right hh, hw.copy i hi hh]

/-- **The copy argument's honest sum** (`SumOK`): `Σ_V h = 0`. -/
theorem sum_hValues (hV : G.Valid) (w : ℕ → K) {pub : ℕ → List E} (hw : G.Satisfies pub (RecCircuit.emb w))
    (α β : E) : ∑ i ∈ range G.N, (hValues G w α β).getD i 0 = 0 := by
  set v := RecCircuit.emb w with hv
  rw [Finset.sum_congr rfl fun i hi ↦ hValues_getD w α β (mem_range.mp hi)]
  rw [← sum_filter_not_add_sum_filter (range G.N) (fun i ↦ G.IsHole i)]
  have hH : ∑ i ∈ (range G.N).filter (fun i ↦ G.IsHole i), (if G.IsHole i then (0 : E) else
      (RecPiop.dPull pi2Omega v α β i)⁻¹ + (G.dPushV pi2Omega v α β i)⁻¹) = 0 :=
    sum_eq_zero fun i hi ↦ ite_eq_left (mem_filter.mp hi).2
  rw [hH, add_zero, sum_congr rfl fun i hi ↦ ite_eq_right (mem_filter.mp hi).2, sum_add_distrib]
  have hNH : ∑ i ∈ (range G.N).filter (fun i ↦ ¬ G.IsHole i), (G.dPushV pi2Omega v α β i)⁻¹ =
      ∑ j ∈ (range G.N).filter (fun i ↦ ¬ G.IsHole i), (RecPiop.dPull pi2Omega v α β j)⁻¹ := by
    refine Finset.sum_nbij G.sigma (fun a ha ↦ ?_) (fun a ha b hb hab ↦ ?_) (fun b hb ↦ ?_) (fun a ha ↦ ?_)
    · obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
      have := hV.sigma_inside a (mem_range.mp ha1) ha2
      exact mem_filter.mpr ⟨mem_range.mpr this.1, this.2⟩
    · exact hV.sigma_inj a (mem_range.mp (mem_filter.mp (Finset.mem_coe.mp ha)).1) b
        (mem_range.mp (mem_filter.mp (Finset.mem_coe.mp hb)).1) hab
    · obtain ⟨hb1, hb2⟩ := mem_filter.mp (Finset.mem_coe.mp hb)
      obtain ⟨i, hi, hσ⟩ := hV.sigma_onto b (mem_range.mp hb1) hb2
      refine ⟨i, Finset.mem_coe.mpr (mem_filter.mpr ⟨mem_range.mpr hi, fun hh ↦ ?_⟩), hσ⟩
      obtain ⟨j, hj, rfl⟩ := RecPiop.Circuit.exists_port_of_hole hV hi hh
      rw [hV.sigma_port j hj] at hσ
      have := mem_range.mp hb1
      omega
    · obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
      rw [dPushV_nonhole w hw α β (mem_range.mp ha1) ha2]
  rw [hNH, CharTwo.add_self_eq_zero]

/-! ## `P`'s definition -/

/-- **`P_v + κ` is in `K`** for a witness, at a circuit over `K`. -/
theorem pvValue_mem (hK : KCircuit G) (w : ℕ → K) {pub : ℕ → List E} (hw : G.Satisfies pub (RecCircuit.emb w))
    {i : ℕ} (hi : i < G.N) : pvValue G w i ∈ subK := by
  unfold pvValue RecPiop.Circuit.pushV
  refine add_mem ?_ (hK.kappa i)
  by_cases hh : G.IsHole i
  · rw [ite_eq_left hh]
    exact ofK_mem_subK _
  · rw [ite_eq_right hh, ← hw.copy i hi hh]
    exact ofK_mem_subK _

/-- **`P + P_v` vanishes on `V_m`** for `P` taking `P_v + κ` there, `w` the witness's polynomial's values. -/
theorem defNum_eval_omega (hV : G.Valid) (hn : G.logN ≤ 32) {wP pP : E[X]} (w : ℕ → K)
    (hwP : ∀ j < G.N, wP.eval (pi2Omega j) = RecCircuit.emb w j) (γ : E)
    (hpP : ∀ i < G.N, pP.eval (pi2Omega i) = pvValue G w i) {i : ℕ} (hi : i < G.N) :
    (pP + G.pushPolyV pi2Omega wP γ).eval (pi2Omega i) = 0 := by
  have hpts := RecPiop.Points.ofCantor UniComplete.Domain.basisE
  have h := RecPiop.Circuit.pushPolyV_eval hV hpts hn wP γ hi
  have e : G.pushV (fun j ↦ wP.eval (pi2Omega j)) i = G.pushV (RecCircuit.emb w) i := by
    unfold RecPiop.Circuit.pushV
    split_ifs
    · exact hwP i hi
    · exact G.push_congr_off_holes hV (fun j hj _ ↦ hwP j hj) 0 hi
  rw [Polynomial.eval_add, hpP i hi]
  unfold pvValue
  rw [← e, ← h]
  generalize (G.pushPolyV pi2Omega wP γ).eval (pi2Omega i) = a
  generalize G.kappa i = k
  calc a + k + k + a = (a + a) + (k + k) := by ring
    _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]

theorem zV_monic : (G.zV pi2Omega).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_add_C _

theorem natDegree_zV : (G.zV pi2Omega).natDegree = G.N := by
  unfold RecPiop.Circuit.zV
  rw [natDegree_prod_of_monic _ _ fun i _ ↦ monic_X_add_C _]
  simp

theorem omega_injOn_N (hn : G.logN ≤ 32) : ∀ a < G.N, ∀ b < G.N, pi2Omega a = pi2Omega b → a = b := by
  have hN : G.N ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hn
  intro a ha b hb h
  exact (RecPiop.Points.ofCantor UniComplete.Domain.basisE).inj a (by omega) b (by omega) h

/-- **`Z_V` divides a polynomial vanishing on `V_m`.** -/
theorem num_eq_zV_mul (hn : G.logN ≤ 32) {p : E[X]} (hp : ∀ i < G.N, p.eval (pi2Omega i) = 0) :
    p = G.zV pi2Omega * (p /ₘ G.zV pi2Omega) := by
  have hmod : p %ₘ G.zV pi2Omega = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero ((range G.N).image pi2Omega) ?_ ?_
    · rw [card_image_of_injOn (fun a ha b hb hab ↦ omega_injOn_N hn a (mem_range.mp ha) b (mem_range.mp hb) hab),
        card_range]
      have := degree_modByMonic_lt p (zV_monic (G := G))
      rwa [degree_eq_natDegree (zV_monic (G := G)).ne_zero, natDegree_zV] at this
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      have e := congrArg (eval (pi2Omega i)) (modByMonic_add_div p (G.zV pi2Omega))
      rw [Polynomial.eval_add, Polynomial.eval_mul, RecPiop.Circuit.zV_eval (mem_range.mp hi), zero_mul, add_zero,
        hp i (mem_range.mp hi)] at e
      exact e
  have e := modByMonic_add_div p (G.zV pi2Omega)
  rw [hmod, zero_add] at e
  exact e.symm

/-- **The honest `q_P`**: `(P + P_v) /ₘ Z_V`. -/
noncomputable def qpHonest (wP pP : E[X]) (γ : E) : E[X] := (pP + G.pushPolyV pi2Omega wP γ) /ₘ G.zV pi2Omega

/-- **The honest `q_P` makes `P`'s definition zero.** -/
theorem defPoly_qpHonest (hV : G.Valid) (hn : G.logN ≤ 32) {wP pP : E[X]} (w : ℕ → K)
    (hwP : ∀ j < G.N, wP.eval (pi2Omega j) = RecCircuit.emb w j) (γ : E)
    (hpP : ∀ i < G.N, pP.eval (pi2Omega i) = pvValue G w i) :
    G.defPoly pi2Omega wP pP (qpHonest wP pP γ (G := G)) γ = 0 := by
  have h := num_eq_zV_mul hn fun i hi ↦ defNum_eval_omega hV hn w hwP γ hpP hi
  unfold RecPiop.Circuit.defPoly qpHonest
  set n := pP + G.pushPolyV pi2Omega wP γ
  nth_rewrite 1 [h]
  rw [mul_comm (n /ₘ G.zV pi2Omega)]
  exact CharTwo.add_self_eq_zero _

/-- **The honest `q_P` has degree below `2N`.** -/
theorem natDegree_qpHonest_lt (hV : G.Valid) {wP pP : E[X]} (hw : wP.natDegree < G.N) (hp : pP.natDegree < G.N)
    (γ : E) : (qpHonest wP pP γ (G := G)).natDegree < 2 * G.N := by
  unfold qpHonest
  rw [natDegree_divByMonic _ (zV_monic (G := G)), natDegree_zV]
  have h2 := RecPiop.Circuit.N_ge_two hV
  have hv := RecPiop.Circuit.natDegree_pushPolyV_le (ω := pi2Omega) hV hw γ
  have := natDegree_add_le pP (G.pushPolyV pi2Omega wP γ)
  have : (pP + G.pushPolyV pi2Omega wP γ).natDegree ≤ 3 * (G.N - 1) := by
    refine this.trans (max_le (by omega) hv)
  omega

/-! ## The identity without `q` -/

/-- **The identity without `q`**: `h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T`. -/
noncomputable def numPoly (S : RecPiop.SetupPolys G pi2Omega) (Φ : ℕ → E[X]) (wP hP pP : E[X]) (α β γ : E) : E[X] :=
  G.idPoly pi2Omega S Φ wP hP 0 pP α β γ

theorem idPoly_eq_num (S : RecPiop.SetupPolys G pi2Omega) (Φ : ℕ → E[X]) (wP hP qP pP : E[X]) (α β γ : E) :
    G.idPoly pi2Omega S Φ wP hP qP pP α β γ = numPoly S Φ wP hP pP α β γ + qP * G.zV pi2Omega := by
  unfold numPoly RecPiop.Circuit.idPoly
  ring

/-- **The identity without `q` vanishes on `V_m`**, for a witness, `P`'s definition true, the non-holes' `d_pull`
and `d_push` nonzero. -/
theorem numPoly_eval_omega (hV : G.Valid) (hn : G.logN ≤ 32) (S : RecPiop.SetupPolys G pi2Omega)
    {pub : ℕ → List E} {Φ : ℕ → E[X]} {wP hP pP qPP : E[X]} (w : ℕ → K)
    (hwP : ∀ j < G.N, wP.eval (pi2Omega j) = RecCircuit.emb w j) (α β γ : E)
    (hΦ : ∀ j < G.nP, (Φ (G.port j % G.W)).eval (pi2Omega (G.port j)) = G.pubFp γ pub j)
    (hdef : G.defPoly pi2Omega wP pP qPP γ = 0) (hw : G.Satisfies pub (RecCircuit.emb w))
    (hhP : ∀ i < G.N, hP.eval (pi2Omega i) = (hValues G w α β).getD i 0)
    (hpull : ∀ i < G.N, ¬ G.IsHole i → RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i ≠ 0)
    (hpush : ∀ i < G.N, ¬ G.IsHole i → G.dPushV pi2Omega (RecCircuit.emb w) α β i ≠ 0) {i : ℕ} (hi : i < G.N) :
    (numPoly S Φ wP hP pP α β γ).eval (pi2Omega i) = 0 := by
  have hpts := RecPiop.Points.ofCantor UniComplete.Domain.basisE
  unfold numPoly
  rw [RecPiop.Circuit.idPoly_eval_omega hV hpts hn S pub Φ wP hP 0 pP qPP α β γ hΦ hdef hi]
  have e1 : RecPiop.dPull pi2Omega (fun j ↦ wP.eval (pi2Omega j)) α β i =
      RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i := by
    simp only [RecPiop.dPull, RecPiop.den, hwP i hi]
  have e2 : G.dPushV pi2Omega (fun j ↦ wP.eval (pi2Omega j)) α β i =
      G.dPushV pi2Omega (RecCircuit.emb w) α β i := by
    unfold RecPiop.Circuit.dPushV RecPiop.Circuit.pushV
    split_ifs
    · simp only [hwP i hi]
    · rw [G.push_congr_off_holes hV (w := fun j ↦ wP.eval (pi2Omega j)) (w' := RecCircuit.emb w)
        (fun j hj _ ↦ hwP j hj) 0 hi]
  have e3 : G.tVal pub (fun j ↦ wP.eval (pi2Omega j)) γ i = G.tVal pub (RecCircuit.emb w) γ i := by
    unfold RecPiop.Circuit.tVal
    refine sum_congr rfl fun j _ ↦ ?_
    split_ifs
    · rw [G.push_congr_off_holes hV (w := fun j ↦ wP.eval (pi2Omega j)) (w' := RecCircuit.emb w)
        (fun j hj _ ↦ hwP j hj) γ hi]
    · rfl
  rw [e1, e2, e3, hhP i hi, hValues_getD w α β hi]
  unfold RecPiop.Circuit.holeInd
  by_cases hh : G.IsHole i
  · obtain ⟨j, hj, rfl⟩ := RecPiop.Circuit.exists_port_of_hole hV hi hh
    simp only [hh, ite_true, zero_mul, zero_add, CharTwo.add_self_eq_zero]
    rw [RecPiop.Circuit.tVal_port hV pub _ γ hj, RecPiop.Circuit.push_port hV hj, hw.ports j hj]
    exact CharTwo.add_self_eq_zero _
  · have ha := hpull i hi hh
    have hb := hpush i hi hh
    simp only [hh, ite_false, add_zero, RecPiop.Circuit.tVal_internal hV pub _ γ hh]
    generalize RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i = a at ha ⊢
    generalize G.dPushV pi2Omega (RecCircuit.emb w) α β i = b at hb ⊢
    have e : (a⁻¹ + b⁻¹) * a * b = b + a := by field_simp
    rw [e, one_mul, CharTwo.add_self_eq_zero]

/-- **The honest `q` makes the identity zero.** -/
theorem idPoly_qHonest (hV : G.Valid) (hn : G.logN ≤ 32) (S : RecPiop.SetupPolys G pi2Omega)
    {pub : ℕ → List E} {Φ : ℕ → E[X]} {wP hP pP qPP : E[X]} (w : ℕ → K)
    (hwP : ∀ j < G.N, wP.eval (pi2Omega j) = RecCircuit.emb w j) (α β γ : E)
    (hΦ : ∀ j < G.nP, (Φ (G.port j % G.W)).eval (pi2Omega (G.port j)) = G.pubFp γ pub j)
    (hdef : G.defPoly pi2Omega wP pP qPP γ = 0) (hw : G.Satisfies pub (RecCircuit.emb w))
    (hhP : ∀ i < G.N, hP.eval (pi2Omega i) = (hValues G w α β).getD i 0)
    (hpull : ∀ i < G.N, ¬ G.IsHole i → RecPiop.dPull pi2Omega (RecCircuit.emb w) α β i ≠ 0)
    (hpush : ∀ i < G.N, ¬ G.IsHole i → G.dPushV pi2Omega (RecCircuit.emb w) α β i ≠ 0) :
    G.idPoly pi2Omega S Φ wP hP (numPoly S Φ wP hP pP α β γ /ₘ G.zV pi2Omega) pP α β γ = 0 := by
  have h := num_eq_zV_mul hn fun i hi ↦
    numPoly_eval_omega hV hn S w hwP α β γ hΦ hdef hw hhP hpull hpush hi
  rw [idPoly_eq_num]
  set n := numPoly S Φ wP hP pP α β γ
  nth_rewrite 1 [h]
  rw [mul_comm (n /ₘ G.zV pi2Omega)]
  exact CharTwo.add_self_eq_zero _

/-- **The numerator's degree is below `3N`** when `h` is below `N` (the honest `h`; RecPiop's bound, `4N − 1`, allows
`h` below `2N`). -/
theorem natDegree_numPoly_le (hV : G.Valid) (S : RecPiop.SetupPolys G pi2Omega) {Φ : ℕ → E[X]}
    (hΦ : ∀ k, (Φ k).natDegree < G.N) {wP hP pP : E[X]}
    (hw : wP.natDegree < G.N) (hh : hP.natDegree < G.N) (hp : pP.natDegree < G.N) (α β γ : E) :
    (numPoly S Φ wP hP pP α β γ).natDegree ≤ 3 * G.N - 1 := by
  have h2 := RecPiop.Circuit.N_ge_two hV
  have hpull := RecPiop.Circuit.natDegree_dPullP_le (D := G.N - 1) (by omega) (by omega) α β (wP := wP)
  have hpush := RecPiop.Circuit.natDegree_dPushP_le S hp α β
  have hhole := RecPiop.Circuit.natDegree_holePoly_le hV (ω := pi2Omega)
  have ht := RecPiop.Circuit.natDegree_tPoly_le (ω := pi2Omega) hV hΦ hw γ
  have h1 : (1 + G.holePoly pi2Omega).natDegree ≤ G.N - 1 :=
    natDegree_add_le_of_degree_le (by rw [natDegree_one]; exact Nat.zero_le _) hhole
  have hA := natDegree_mul_le_of_le (natDegree_mul_le_of_le (Nat.le_sub_one_of_lt hh) hpull) hpush
  have hB := natDegree_mul_le_of_le h1 (natDegree_add_le_of_degree_le hpush hpull)
  unfold numPoly RecPiop.Circuit.idPoly
  rw [zero_mul, add_zero]
  refine natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (hA.trans ?_) (hB.trans ?_)) (ht.trans ?_) <;>
  · generalize G.N = N at *
    omega

/-- **The honest `q` has degree below `2N`.** -/
theorem natDegree_qHonest_lt (hV : G.Valid) (S : RecPiop.SetupPolys G pi2Omega) {Φ : ℕ → E[X]}
    (hΦ : ∀ k, (Φ k).natDegree < G.N) {wP hP pP : E[X]}
    (hw : wP.natDegree < G.N) (hh : hP.natDegree < G.N) (hp : pP.natDegree < G.N) (α β γ : E) :
    (numPoly S Φ wP hP pP α β γ /ₘ G.zV pi2Omega).natDegree < 2 * G.N := by
  rw [natDegree_divByMonic _ (zV_monic (G := G)), natDegree_zV]
  have h2 := RecPiop.Circuit.N_ge_two hV
  have := natDegree_numPoly_le hV S hΦ hw hh hp α β γ
  omega

end RecCompose

/-- info: 'RecCompose.sum_hValues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.sum_hValues

/-- info: 'RecCompose.idPoly_qHonest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.idPoly_qHonest

/-- info: 'RecCompose.defPoly_qpHonest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.defPoly_qpHonest
