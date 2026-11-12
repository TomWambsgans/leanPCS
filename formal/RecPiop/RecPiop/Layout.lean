-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecPiop.Identity
import RecPiop.Copy
import RecPiop.SumDeg

/-!
# π2v4: the copy sum from `Q`'s layout

`PI2.md` §7, "The copy sum from `Q`'s layout". `Q`'s sixteen slots hold, for the limbs of `E`, `H = x h` (one digit,
below `N`), `q`'s two digits on the slot bits' anti-diagonal (`A = A_0 + Z_V A_1`, below `2N`) and `G` (below `N`, the
prover's; zero for the honest one). With the pushes' claim giving `P(t) = s`, `P`'s definition at `t` and `S(t) = 0`,
the identity's claim at `t` is `I(t) = 0` for

`I = D² H + x Z_V D A + x² Z_V³ G + x D R`,  `D = d_pull d_push`,  `R = (1 + 1_S)(d_pull + d_push) + T`

(`iPoly`, of degree below `5N`: `natDegree_iPoly_le`). **The lemma** (`copyOK4_of_iPoly`): if `I = 0` and `P`'s
definition holds as polynomials, then either a denominator vanishes on `V_m` (`DenZero`), or `D(0) ≠ 0`, so
`H(0) = 0`, `h = H/x` has degree below `N − 1`, `Σ_V h = 0` (`sum_eval_eq_zero_of_natDegree_lt`), and
`I/x = D (h D + R) + Z_V D A + x Z_V³ G = 0` gives `h D + R = 0` on `V_m`: `CopyOK` with `h`'s values. No claim reads
the sum. `card_iPoly_eval_eq_zero_le`: unless `I` and the definition are zero, they vanish together at at most
`5N − 1` points `t`.
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset Polynomial

variable {F : Type} [Field F] [CharP F 2] [DecidableEq F]

namespace Circuit

variable (G : Circuit F) (ω : ℕ → F)

/-- **`D = d_pull d_push`**, with the committed `P`. -/
noncomputable def dP (S : SetupPolys G ω) (wP pP : F[X]) (α β : F) : F[X] := dPullP wP α β * G.dPushP ω S pP α β

/-- **`R = (1 + 1_S)(d_pull + d_push) + T`**, with the committed `P`. -/
noncomputable def rP (S : SetupPolys G ω) (Φ : ℕ → F[X]) (wP pP : F[X]) (α β γ : F) : F[X] :=
  (1 + G.holePoly ω) * (G.dPushP ω S pP α β + dPullP wP α β) + G.tPoly ω Φ wP γ

/-- **The identity as the identity's claim reads it** (π2v4): `I = D² H + x Z_V D A + x² Z_V³ G + x D R`. -/
noncomputable def iPoly (S : SetupPolys G ω) (Φ : ℕ → F[X]) (wP HP AP GP pP : F[X]) (α β γ : F) : F[X] :=
  G.dP ω S wP pP α β ^ 2 * HP + X * G.zV ω * G.dP ω S wP pP α β * AP + X ^ 2 * G.zV ω ^ 3 * GP +
    X * G.dP ω S wP pP α β * G.rP ω S Φ wP pP α β γ

variable {G ω} {n : ℕ}

/-- `idPoly` without its quotient: `h D + R`. -/
theorem idPoly_zero (S : SetupPolys G ω) (Φ : ℕ → F[X]) (wP h pP : F[X]) (α β γ : F) :
    G.idPoly ω S Φ wP h 0 pP α β γ = h * G.dP ω S wP pP α β + G.rP ω S Φ wP pP α β γ := by
  unfold idPoly dP rP
  ring

/-- **`I` at `H = x h`**: `x (D (h D + R) + Z_V D A + x Z_V³ G)`. -/
theorem iPoly_X_mul (S : SetupPolys G ω) (Φ : ℕ → F[X]) (wP h AP GP pP : F[X]) (α β γ : F) :
    G.iPoly ω S Φ wP (X * h) AP GP pP α β γ = X * (G.dP ω S wP pP α β * G.idPoly ω S Φ wP h 0 pP α β γ +
      G.zV ω * G.dP ω S wP pP α β * AP + X * G.zV ω ^ 3 * GP) := by
  rw [idPoly_zero]
  unfold iPoly
  ring

/-- **The layout lemma** (`PI2.md` §7, steps 5–6): `I = 0` and `P`'s definition give `CopyOK4`, for `H` below `N`. -/
theorem copyOK4_of_iPoly (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n) (S : SetupPolys G ω)
    (pub : ℕ → List F) (Φ : ℕ → F[X]) (wP HP AP GP pP qPP : F[X]) (α β γ : F)
    (hΦ : ∀ j < G.nP, (Φ (G.port j % G.W)).eval (ω (G.port j)) = G.pubFp γ pub j)
    (hI : G.iPoly ω S Φ wP HP AP GP pP α β γ = 0) (hdef : G.defPoly ω wP pP qPP γ = 0)
    (hH : HP.natDegree < G.N) :
    G.CopyOK4 ω pub (fun j => wP.eval (ω j)) α β γ := by
  by_cases hz : G.DenZero ω (fun j => wP.eval (ω j)) α β
  · exact Or.inr hz
  refine Or.inl ?_
  unfold DenZero at hz
  push Not at hz
  have h2 := N_ge_two hV
  -- `D` on `V_m` is the copy argument's denominators' product, nonzero
  have hD : ∀ i < G.N, (G.dP ω S wP pP α β).eval (ω i) ≠ 0 := by
    intro i hi
    unfold dP
    rw [eval_mul, dPullP_eval, dPushP_eval hV hP hn S wP pP qPP α β γ hdef hi]
    exact mul_ne_zero (hz i hi).1 (hz i hi).2
  -- `H(0) = 0`
  have hH0 : HP.eval 0 = 0 := by
    have h0 := congrArg (fun p => p.eval 0) hI
    simp only [iPoly, eval_add, eval_mul, eval_pow, eval_X, eval_zero] at h0
    have hD0 := hD 0 (by omega)
    rw [hP.zero] at hD0
    simp only [zero_mul, add_zero, ne_eq, zero_pow two_ne_zero, mul_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hD0)
  obtain ⟨h, hh⟩ : X ∣ HP := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero]
    exact hH0
  subst hh
  -- `deg h < N − 1`, so `Σ_V h = 0`
  have hdeg : h.natDegree + 1 < 2 ^ G.logN := by
    by_cases h0 : h = 0
    · rw [h0, natDegree_zero]
      exact h2
    · rw [natDegree_X_mul h0] at hH
      exact hH
  have hsum := sum_eval_eq_zero_of_natDegree_lt hP hn h hdeg
  -- `I/x = 0`, so `h D + R = 0` on `V_m`
  rw [iPoly_X_mul] at hI
  have hQ := (mul_eq_zero.mp hI).resolve_left X_ne_zero
  refine ⟨fun i => h.eval (ω i), fun i hi => ?_, hsum⟩
  have hi' := congrArg (fun p => p.eval (ω i)) hQ
  simp only [eval_add, eval_mul, eval_pow, zV_eval hi, zero_mul, mul_zero, add_zero, zero_pow three_ne_zero,
    eval_zero] at hi'
  have hid := (mul_eq_zero.mp hi').resolve_left (hD i hi)
  unfold PointId
  rw [← idPoly_eval_omega hV hP hn S pub Φ wP h 0 pP qPP α β γ hΦ hdef hi]
  exact hid

/-! ## The degrees -/

theorem natDegree_dP_le (hV : G.Valid) (S : SetupPolys G ω) {wP pP : F[X]} (hw : wP.natDegree < G.N)
    (hp : pP.natDegree < G.N) (α β : F) : (G.dP ω S wP pP α β).natDegree ≤ 2 * G.N - 2 := by
  have h2 := N_ge_two hV
  have hpull := natDegree_dPullP_le (D := G.N - 1) (by omega) (by omega) α β (wP := wP)
  have hpush := natDegree_dPushP_le S hp α β
  unfold dP
  exact (natDegree_mul_le_of_le hpull hpush).trans (by omega)

theorem natDegree_rP_le (hV : G.Valid) (S : SetupPolys G ω) {Φ : ℕ → F[X]} (hΦ : ∀ k, (Φ k).natDegree < G.N)
    {wP pP : F[X]} (hw : wP.natDegree < G.N) (hp : pP.natDegree < G.N) (α β γ : F) :
    (G.rP ω S Φ wP pP α β γ).natDegree ≤ 2 * G.N - 2 := by
  have h2 := N_ge_two hV
  have hpull := natDegree_dPullP_le (D := G.N - 1) (by omega) (by omega) α β (wP := wP)
  have hpush := natDegree_dPushP_le S hp α β
  have hhole := natDegree_holePoly_le hV (ω := ω)
  have ht := natDegree_tPoly_le (ω := ω) hV hΦ hw γ
  have h1 : (1 + G.holePoly ω).natDegree ≤ G.N - 1 :=
    natDegree_add_le_of_degree_le (by rw [natDegree_one]; exact Nat.zero_le _) hhole
  have hB := natDegree_mul_le_of_le h1 (natDegree_add_le_of_degree_le hpush hpull)
  unfold rP
  exact natDegree_add_le_of_degree_le (hB.trans (by omega)) (ht.trans (by omega))

/-- **`I` has degree at most `5N − 1`**, for `w, σ, κ, P, Φ, H, G` below `N` and `A` below `2N`. -/
theorem natDegree_iPoly_le (hV : G.Valid) (S : SetupPolys G ω) {Φ : ℕ → F[X]}
    (hΦ : ∀ k, (Φ k).natDegree < G.N) {wP HP AP GP pP : F[X]} (hw : wP.natDegree < G.N)
    (hh : HP.natDegree < G.N) (ha : AP.natDegree < 2 * G.N) (hg : GP.natDegree < G.N) (hp : pP.natDegree < G.N)
    (α β γ : F) : (G.iPoly ω S Φ wP HP AP GP pP α β γ).natDegree ≤ 5 * G.N - 1 := by
  have h2 := N_ge_two hV
  have hd := natDegree_dP_le hV S hw hp α β
  have hr := natDegree_rP_le hV S hΦ hw hp α β γ
  have hz := natDegree_zV_le (G := G) (ω := ω)
  have hX : (X : F[X]).natDegree ≤ 1 := natDegree_X_le
  have hX2 : (X ^ 2 : F[X]).natDegree ≤ 2 := by rw [natDegree_X_pow]
  have t1 := natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 hd) (Nat.le_sub_one_of_lt hh)
  have t2 := natDegree_mul_le_of_le (natDegree_mul_le_of_le (natDegree_mul_le_of_le hX hz) hd)
    (Nat.le_sub_one_of_lt ha)
  have t3 := natDegree_mul_le_of_le (natDegree_mul_le_of_le hX2 (natDegree_pow_le_of_le 3 hz))
    (Nat.le_sub_one_of_lt hg)
  have t4 := natDegree_mul_le_of_le (natDegree_mul_le_of_le hX hd) hr
  unfold iPoly
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (t1.trans ?_) (t2.trans ?_)) (t3.trans ?_)) (t4.trans ?_) <;>
  · generalize G.N = N at *
    omega

/-- **The identities at a random point** (π2v4): unless `I` and `P`'s definition are zero, they vanish together at at
most `5N − 1` points `t`. -/
theorem card_iPoly_eval_eq_zero_le [Fintype F] (hV : G.Valid) (S : SetupPolys G ω) {Φ : ℕ → F[X]}
    (hΦ : ∀ k, (Φ k).natDegree < G.N) {wP HP AP GP pP qPP : F[X]} (hw : wP.natDegree < G.N)
    (hh : HP.natDegree < G.N) (ha : AP.natDegree < 2 * G.N) (hg : GP.natDegree < G.N) (hp : pP.natDegree < G.N)
    (hqp : qPP.natDegree < 2 * G.N) (α β γ : F)
    (hne : ¬ (G.iPoly ω S Φ wP HP AP GP pP α β γ = 0 ∧ G.defPoly ω wP pP qPP γ = 0)) :
    (univ.filter fun t => (G.iPoly ω S Φ wP HP AP GP pP α β γ).eval t = 0 ∧
      (G.defPoly ω wP pP qPP γ).eval t = 0).card ≤ 5 * G.N - 1 := by
  by_cases h1 : G.iPoly ω S Φ wP HP AP GP pP α β γ = 0
  · have h2 : G.defPoly ω wP pP qPP γ ≠ 0 := fun h => hne ⟨h1, h⟩
    exact (Finset.card_le_card fun t ht => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp ht).2.2⟩).trans ((card_eval_eq_zero_le _ h2).trans
        ((natDegree_defPoly_le hV hw hp hqp γ).trans (by omega)))
  · exact (Finset.card_le_card fun t ht => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp ht).2.1⟩).trans ((card_eval_eq_zero_le _ h1).trans
        (natDegree_iPoly_le hV S hΦ hw hh ha hg hp α β γ))

end Circuit

end RecPiop
