-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The degree bookkeeping follows
-- `formal/QuotientSecurity/Degrees.lean` (crates/membership/quotient's two identities).
import RecPiop.Indicator
import RecPiop.Copy

/-!
# π2's quotient identities and their degrees (π2v2)

`PI2.md` §1: with `w` the witness's polynomial (degree below `N`, its values on `V_m` the witness), the
**internal pushes**

`P_v = w + Σ_{p internal} I_p·(E_p + w)`,

`E_p` pair `p`'s formula on the row's cells `w(X + ω_{k ⊕ c})` (`cellPoly`; `ω_{k ⊕ c}` moves role `k`'s position
to cell `c` of its row, `cellPoly_eval`), the internal pairs those that are not ports; with `κ` they take the push
values `pushV` on `V_m` (`pushPolyV_eval`: a hole's own value at a hole, where `κ` is zero). `1_S = Σ_{port pairs}
I_p` is the holes' indicator there (`holePoly_eval`), and the **ports' term** `T = Σ_{port pairs} I_p (E_p + Φ_k)`
(`tPoly`) is `E_p + F_j` at the hole of port `j` and zero elsewhere (`tPoly_eval`), for any polynomials `Φ_k`
taking the public fingerprints `F_j` at the holes of role `k` (`PI2.md` §1: `Φ_k` by rows,
`RecStatement.Lemmas.Phi`). **`P` is committed** (in `Q`, after `α, β`) with its definition (`defPoly`)

`P + P_v + q_P·Z_V = 0`,

and the **copy identity** (`idPoly`)

`h·d_pull·d_push + (1 + 1_S)·(d_push + d_pull) + T + q·Z_V`, `d_pull = α + w + βX`, `d_push = α + P + κ + βσ`,
`Z_V = Π_{i<N} (X + ω_i)`,

evaluates on `V_m`, where the definition pins `P` to `P_v`, to the pointwise identity of the copy argument
(`idPoly_eval_omega`): if both are the zero polynomial and `Σ_V h = 0`, the state `CopyOK` holds
(`copyOK_of_idPoly`).

**The degrees** (`natDegree_idPoly_le`, `natDegree_defPoly_le`): with `w, σ, κ, h, P, Φ` below `N` and `q`, `q_P`
below `2N`, the indicators are at most `N − 2^s` (`natDegree_ind_le`), the formulas at most `2(N − 1)` (a port's,
linear, `N − 1`), so `P_v` at most `3(N − 1)`, `d_push` below `N`, `T` at most `2(N − 1)`, and both identities at
most `3N − 1`. **Schwartz–Zippel in `t`** (`card_idPoly_eval_eq_zero_le`): unless both are zero, they vanish
together at at most `3N − 1` points `t`.

The setup's polynomials `σ`, `κ` (`SetupPolys`) are any of degree below `N` taking the columns'
values on `V_m` (`SetupPolys.ofInterpolate` builds them by interpolation).
-/

set_option linter.unusedSectionVars false

namespace RecPiop

open Finset Polynomial

variable {F : Type} [Field F] [CharP F 2]

/-! ## Formulas on polynomials -/

theorem Poly2.eval_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (φ : R →ₐ[F] S) (p : Poly2 F) (cell : ℕ → R) : φ (p.eval cell) = p.eval (φ ∘ cell) := by
  unfold Poly2.eval
  simp only [map_add, map_list_sum, List.map_map]
  congr 2
  · refine List.map_congr_left fun t _ => ?_
    simp [map_mul, AlgHom.commutes]
  · refine List.map_congr_left fun t _ => ?_
    simp [map_mul, AlgHom.commutes]

theorem fpEval_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (φ : R →ₐ[F] S) (ls : List (Limb F)) (γ : F) (cell : ℕ → R) :
    φ (fpEval ls γ cell) = fpEval ls γ (φ ∘ cell) := by
  unfold fpEval
  simp only [map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  simp [map_mul, AlgHom.commutes]

theorem Role.value_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (φ : R →ₐ[F] S) (r : Role F) (γ : F) (own : R) (cell : ℕ → R) :
    φ (r.value γ own cell) = r.value γ (φ own) (φ ∘ cell) := by
  cases r with
  | forward => rfl
  | expr p => exact Poly2.eval_map φ p cell
  | port ls => exact fpEval_map φ ls γ cell

/-- **A role's formula on polynomials, evaluated, is the formula on the values.** -/
theorem Role.value_eval (r : Role F) (γ : F) (own : F[X]) (cell : ℕ → F[X]) (x : F) :
    (r.value γ own cell).eval x = r.value γ (own.eval x) (fun c => (cell c).eval x) := by
  have h := Role.value_map (aeval x) r γ own cell
  simp only [coe_aeval_eq_eval] at h
  exact h

theorem natDegree_list_sum_le {l : List F[X]} {D : ℕ} (h : ∀ p ∈ l, p.natDegree ≤ D) :
    l.sum.natDegree ≤ D := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons]
    exact natDegree_add_le_of_degree_le (h a (List.mem_cons_self ..))
      (ih fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem Poly2.natDegree_eval_le (p : Poly2 F) {cell : ℕ → F[X]} {D : ℕ}
    (h : ∀ c, (cell c).natDegree ≤ D) : (p.eval cell).natDegree ≤ 2 * D := by
  unfold Poly2.eval
  refine natDegree_add_le_of_degree_le (natDegree_list_sum_le fun q hq => ?_)
    (natDegree_list_sum_le fun q hq => ?_)
  · obtain ⟨t, _, rfl⟩ := List.mem_map.mp hq
    rw [Polynomial.algebraMap_eq]
    exact (natDegree_C_mul_le _ _).trans ((h _).trans (by omega))
  · obtain ⟨t, _, rfl⟩ := List.mem_map.mp hq
    rw [Polynomial.algebraMap_eq]
    refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
    have := h t.1
    have := h t.2.1
    omega

theorem fpEval_natDegree_le (ls : List (Limb F)) (γ : F) {cell : ℕ → F[X]} {D : ℕ}
    (h : ∀ c, (cell c).natDegree ≤ D) : (fpEval ls γ cell).natDegree ≤ D := by
  unfold fpEval
  refine natDegree_list_sum_le fun q hq => ?_
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hq
  rw [Polynomial.algebraMap_eq]
  exact (natDegree_C_mul_le _ _).trans (h _)

theorem Role.natDegree_value_le (r : Role F) (γ : F) {own : F[X]} {cell : ℕ → F[X]} {D : ℕ}
    (ho : own.natDegree ≤ D) (h : ∀ c, (cell c).natDegree ≤ D) :
    (r.value γ own cell).natDegree ≤ 2 * D := by
  cases r with
  | forward => exact ho.trans (by omega)
  | expr p => exact Poly2.natDegree_eval_le p h
  | port ls => exact (fpEval_natDegree_le ls γ h).trans (by omega)

/-! ## The polynomials of the identity -/

/-- **A cell of a role-`k` position's row**, as a polynomial: `w(X + ω_{k ⊕ c})`. -/
noncomputable def cellPoly (ω : ℕ → F) (wP : F[X]) (k c : ℕ) : F[X] :=
  wP.comp (X + C (ω (k ^^^ c)))

/-- **The pull's denominator** `α + w + βX`. -/
noncomputable def dPullP (wP : F[X]) (α β : F) : F[X] := C α + wP + C β * X

/-- **The setup's polynomials**: `σ` (the tags) and `κ` (the constants), of degree below `N`,
taking the columns' values on `V_m`. -/
structure SetupPolys (G : Circuit F) (ω : ℕ → F) where
  σP : F[X]
  κP : F[X]
  σ_deg : σP.natDegree < G.N
  κ_deg : κP.natDegree < G.N
  σ_eval : ∀ i < G.N, σP.eval (ω i) = ω (G.sigma i)
  κ_eval : ∀ i < G.N, κP.eval (ω i) = G.kappa i

theorem natDegree_lt_of_degree_lt' {p : F[X]} {m : ℕ} (h : p.degree < m) (hm : 0 < m) :
    p.natDegree < m := by
  by_cases hp : p = 0
  · rw [hp, natDegree_zero]; exact hm
  · exact (natDegree_lt_iff_degree_lt hp).mpr h

/-- **The setup's polynomials exist**: `σ` and `κ` by interpolation on `V_m`. -/
noncomputable def SetupPolys.ofInterpolate (G : Circuit F) {ω : ℕ → F} {n : ℕ} (hP : Points ω n)
    (hn : G.logN ≤ n) : SetupPolys G ω :=
  have hinj : Set.InjOn ω (range G.N : Set ℕ) := fun a ha b hb h => by
    have hN : G.N ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [Finset.mem_coe, Finset.mem_range] at ha hb
    exact hP.inj a (by omega) b (by omega) h
  have hN : 0 < G.N := Nat.two_pow_pos _
  { σP := Lagrange.interpolate (range G.N) ω (fun i => ω (G.sigma i))
    κP := Lagrange.interpolate (range G.N) ω G.kappa
    σ_deg := natDegree_lt_of_degree_lt' (by
      simpa using Lagrange.degree_interpolate_lt (fun i => ω (G.sigma i)) hinj) hN
    κ_deg := natDegree_lt_of_degree_lt' (by
      simpa using Lagrange.degree_interpolate_lt G.kappa hinj) hN
    σ_eval := fun i hi => Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_range.mpr hi)
    κ_eval := fun i hi => Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_range.mpr hi) }

namespace Circuit

variable (G : Circuit F) [DecidableEq F] (ω : ℕ → F)

/-- **Pair `p`'s formula** `E_p` on the row's cells, a polynomial. -/
noncomputable def formulaPoly (wP : F[X]) (γ : F) (p : Block × ℕ) : F[X] :=
  (G.regionRole p.1 p.2).value γ wP (cellPoly ω wP p.2)

/-- The internal pairs: those whose role is not a port. -/
def intPairs : Finset (Block × ℕ) := G.pairs.filter fun p => (G.regionRole p.1 p.2).isPort = false

/-- The port pairs. -/
def portPairs : Finset (Block × ℕ) := G.pairs.filter fun p => (G.regionRole p.1 p.2).isPort = true

/-- **The internal pushes** `P_v = w + Σ_{p internal} I_p·(E_p + w)`. -/
noncomputable def pushPolyV (wP : F[X]) (γ : F) : F[X] :=
  wP + ∑ p ∈ G.intPairs, G.ind ω p * (G.formulaPoly ω wP γ p + wP)

/-- **The holes' indicator** `1_S`: the port pairs' indicators. -/
noncomputable def holePoly : F[X] := ∑ p ∈ G.portPairs, G.ind ω p

/-- **The ports' term** `T = Σ_{p port} I_p·(E_p + Φ_{k_p})`. -/
noncomputable def tPoly (Φ : ℕ → F[X]) (wP : F[X]) (γ : F) : F[X] :=
  ∑ p ∈ G.portPairs, G.ind ω p * (G.formulaPoly ω wP γ p + Φ p.2)

/-- **`V_m`'s vanishing polynomial** `Z_V = Π_{i<N} (X + ω_i)`. -/
noncomputable def zV : F[X] := ∏ i ∈ range G.N, (X + C (ω i))

/-- **The push's denominator** `α + P + κ + βσ`, `P` the committed polynomial. -/
noncomputable def dPushP (S : SetupPolys G ω) (pP : F[X]) (α β : F) : F[X] :=
  C α + pP + S.κP + C β * S.σP

/-- **The copy identity**
`h·d_pull·d_push + (1 + 1_S)·(d_push + d_pull) + T + q·Z_V`, zero on `V_m` but for `q·Z_V`. -/
noncomputable def idPoly (S : SetupPolys G ω) (Φ : ℕ → F[X]) (wP hP qP pP : F[X]) (α β γ : F) : F[X] :=
  hP * dPullP wP α β * G.dPushP ω S pP α β + (1 + G.holePoly ω) * (G.dPushP ω S pP α β + dPullP wP α β) +
    G.tPoly ω Φ wP γ + qP * G.zV ω

/-- **`P`'s definition** `P + P_v + q_P·Z_V` (zero exactly when `P = P_v + Z_V q_P`). -/
noncomputable def defPoly (wP pP qPP : F[X]) (γ : F) : F[X] :=
  pP + G.pushPolyV ω wP γ + qPP * G.zV ω

variable {G ω} {n : ℕ}

theorem mem_intPairs {p : Block × ℕ} : p ∈ G.intPairs ↔ p ∈ G.pairs ∧ (G.regionRole p.1 p.2).isPort = false := by
  simp [intPairs]

theorem mem_portPairs {p : Block × ℕ} :
    p ∈ G.portPairs ↔ p ∈ G.pairs ∧ (G.regionRole p.1 p.2).isPort = true := by
  simp [portPairs]

/-! ## On `V_m` -/

/-- **A row's cell from a role-`k` position**: `i ⊕ (k ⊕ c)` is cell `c` of `i`'s row. -/
theorem xor_role (i : ℕ) {c : ℕ} (hc : c < G.W) : i ^^^ ((i % G.W) ^^^ c) = G.base i + c := by
  have hdvd : 2 ^ G.logW ∣ G.base i := Dvd.intro_left _ rfl
  have hk : i % G.W < 2 ^ G.logW := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hi : G.base i ^^^ (i % G.W) = i := by
    rw [← Heap.add_eq_xor_of_dvd hdvd hk]
    exact Nat.div_add_mod' i G.W
  rw [Heap.add_eq_xor_of_dvd hdvd hc]
  calc i ^^^ ((i % G.W) ^^^ c) = (G.base i ^^^ (i % G.W)) ^^^ ((i % G.W) ^^^ c) := by rw [hi]
    _ = G.base i ^^^ c := by
      rw [Nat.xor_assoc, ← Nat.xor_assoc (i % G.W), Nat.xor_self, Nat.zero_xor]

theorem cellPoly_eval (hP : Points ω n) (wP : F[X]) (i : ℕ) {c : ℕ} (hc : c < G.W) :
    (cellPoly ω wP (i % G.W) c).eval (ω i) = wP.eval (ω (G.base i + c)) := by
  unfold cellPoly
  rw [eval_comp, eval_add, eval_X, eval_C, ← hP.xor, xor_role i hc]

theorem formulaPoly_eval (hV : G.Valid) (hP : Points ω n) (wP : F[X]) (γ : F)
    {p : Block × ℕ} (hp : p ∈ G.pairs) {i : ℕ} (hi : G.InPair p i) :
    (G.formulaPoly ω wP γ p).eval (ω i) =
      (G.role i).value γ (wP.eval (ω i)) (fun c => wP.eval (ω (G.base i + c))) := by
  unfold formulaPoly
  rw [Role.value_eval, ← role_of_inPair hV hp hi]
  refine Role.value_congr _ γ (fun _ => rfl) fun c hc => ?_
  rw [← hi.2.2]
  exact cellPoly_eval hP wP i (role_reads_lt hV hc)

/-- `κ` is zero at a hole. -/
theorem kappa_hole (hV : G.Valid) {i : ℕ} (hi : i < G.N) (hh : G.IsHole i) : G.kappa i = 0 := by
  by_contra hk
  have := hV.kappa_expr _ hi hk
  unfold IsHole at hh
  cases hr : G.role i <;> rw [hr] at this hh <;> simp [Role.isExpr, Role.isPort] at this hh

/-- **The internal pushes and `κ` take the push values on `V_m`.** -/
theorem pushPolyV_eval (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n) (wP : F[X]) (γ : F) {i : ℕ}
    (hi : i < G.N) :
    (G.pushPolyV ω wP γ).eval (ω i) + G.kappa i = G.pushV (fun j => wP.eval (ω j)) i := by
  unfold pushPolyV pushV
  rw [eval_add, eval_finsetSum]
  cases hf : (G.role i).isForward with
  | true =>
    have hs : ∑ p ∈ G.intPairs, (G.ind ω p * (G.formulaPoly ω wP γ p + wP)).eval (ω i) = 0 :=
      Finset.sum_eq_zero fun p hp => by
        rw [eval_mul, ind_eval_not_mem hi (not_inPair_of_forward hV (mem_intPairs.mp hp).1 hf), zero_mul]
    have hh : ¬ G.IsHole i := by
      unfold IsHole
      cases hr : G.role i <;> rw [hr] at hf <;> simp [Role.isForward, Role.isPort] at hf ⊢
    rw [hs, add_zero, ite_eq_right hh]
    unfold push
    cases hr : G.role i with
    | forward => rfl
    | expr _ => rw [hr] at hf; simp [Role.isForward] at hf
    | port _ => rw [hr] at hf; simp [Role.isForward] at hf
  | false =>
    obtain ⟨p₀, hp₀, hi₀⟩ := exists_pair hi hf
    by_cases hh : G.IsHole i
    · have hport : (G.regionRole p₀.1 p₀.2).isPort = true := by
        rw [← role_of_inPair hV hp₀ hi₀]; exact hh
      have hs : ∑ p ∈ G.intPairs, (G.ind ω p * (G.formulaPoly ω wP γ p + wP)).eval (ω i) = 0 :=
        Finset.sum_eq_zero fun p hp => by
          have hp' := mem_intPairs.mp hp
          have hne : ¬ G.InPair p i := fun h => by
            rw [pair_unique hV hp'.1 hp₀ h hi₀, hport] at hp'
            exact absurd hp'.2 (by decide)
          rw [eval_mul, ind_eval_not_mem hi hne, zero_mul]
      rw [hs, add_zero, kappa_hole hV hi hh, add_zero, ite_eq_left hh]
    · have hport : (G.regionRole p₀.1 p₀.2).isPort = false := by
        rw [← role_of_inPair hV hp₀ hi₀]; simpa [IsHole] using hh
      have hm : p₀ ∈ G.intPairs := mem_intPairs.mpr ⟨hp₀, hport⟩
      rw [Finset.sum_eq_single p₀ (fun p hp hne => by
          rw [eval_mul, ind_eval_not_mem hi (fun h => hne (pair_unique hV (mem_intPairs.mp hp).1 hp₀ h hi₀)),
            zero_mul])
        (fun h => absurd hm h)]
      rw [eval_mul, ind_eval_mem hV hP hn hp₀ hi₀, one_mul, eval_add, formulaPoly_eval hV hP wP γ hp₀ hi₀,
        ite_eq_right hh]
      have e : ∀ a b : F, a + (b + a) = b := fun a b => by
        rw [add_comm b a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      rw [e, ← G.push_gamma (fun j => wP.eval (ω j)) hh γ 0]
      rfl

/-- **The holes' polynomial is the holes' indicator on `V_m`.** -/
theorem holePoly_eval (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n) {i : ℕ} (hi : i < G.N) :
    (G.holePoly ω).eval (ω i) = G.holeInd i := by
  unfold holePoly holeInd
  rw [eval_finsetSum]
  by_cases hh' : G.IsHole i
  · have hh : (G.role i).isPort = true := hh'
    have hf : (G.role i).isForward = false := by
      cases hr : G.role i <;> rw [hr] at hh <;> simp_all [Role.isForward, Role.isPort]
    obtain ⟨p₀, hp₀, hi₀⟩ := exists_pair hi hf
    have hm : p₀ ∈ G.portPairs :=
      mem_portPairs.mpr ⟨hp₀, by rw [← role_of_inPair hV hp₀ hi₀]; exact hh⟩
    rw [Finset.sum_eq_single p₀ (fun p hp hne => ind_eval_not_mem hi
        (fun h => hne (pair_unique hV (mem_portPairs.mp hp).1 hp₀ h hi₀)))
      (fun h => absurd hm h), ind_eval_mem hV hP hn hp₀ hi₀, ite_eq_left hh']
  · rw [ite_eq_right hh']
    refine Finset.sum_eq_zero fun p hp => ind_eval_not_mem hi fun h => hh' ?_
    show (G.role i).isPort = true
    rw [role_of_inPair hV (mem_portPairs.mp hp).1 h]
    exact (mem_portPairs.mp hp).2

/-- **The ports' term on `V_m`**: `E_p + F_j` at the hole of port `j`, zero elsewhere, for `Φ` taking the public
fingerprints at the holes. -/
theorem tPoly_eval (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n) (pub : ℕ → List F) (Φ : ℕ → F[X])
    (wP : F[X]) (γ : F)
    (hΦ : ∀ j < G.nP, (Φ (G.port j % G.W)).eval (ω (G.port j)) = G.pubFp γ pub j) {i : ℕ} (hi : i < G.N) :
    (G.tPoly ω Φ wP γ).eval (ω i) = G.tVal pub (fun j => wP.eval (ω j)) γ i := by
  unfold tPoly
  rw [eval_finsetSum]
  by_cases hh : G.IsHole i
  · obtain ⟨j, hj, rfl⟩ := exists_port_of_hole hV hi hh
    have hh' : (G.role (G.port j)).isPort = true := hh
    have hf : (G.role (G.port j)).isForward = false := by
      cases hr : G.role (G.port j) <;> rw [hr] at hh' <;> simp_all [Role.isForward, Role.isPort]
    obtain ⟨p₀, hp₀, hi₀⟩ := exists_pair hi hf
    have hm : p₀ ∈ G.portPairs :=
      mem_portPairs.mpr ⟨hp₀, by rw [← role_of_inPair hV hp₀ hi₀]; exact hh'⟩
    rw [Finset.sum_eq_single p₀ (fun p hp hne => by
        rw [eval_mul, ind_eval_not_mem hi (fun h => hne (pair_unique hV (mem_portPairs.mp hp).1 hp₀ h hi₀)),
          zero_mul])
      (fun h => absurd hm h), eval_mul, ind_eval_mem hV hP hn hp₀ hi₀, one_mul, eval_add,
      formulaPoly_eval hV hP wP γ hp₀ hi₀, ← hi₀.2.2, hΦ j hj, tVal_port hV pub _ γ hj]
    unfold push
    rw [kappa_hole hV hi hh, add_zero]
  · rw [tVal_internal hV pub _ γ hh]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [eval_mul, ind_eval_not_mem hi fun h => hh ?_, zero_mul]
    show (G.role i).isPort = true
    rw [role_of_inPair hV (mem_portPairs.mp hp).1 h]
    exact (mem_portPairs.mp hp).2

theorem zV_eval {i : ℕ} (hi : i < G.N) : (G.zV ω).eval (ω i) = 0 := by
  unfold zV
  rw [eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hi) (by simp [CharTwo.add_self_eq_zero])

theorem dPullP_eval (wP : F[X]) (α β : F) (i : ℕ) :
    (dPullP wP α β).eval (ω i) = dPull ω (fun j => wP.eval (ω j)) α β i := by
  simp [dPullP, dPull, den]

/-- **Where `P`'s definition holds, the push's denominator on `V_m` is `d_push`.** -/
theorem dPushP_eval (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n) (S : SetupPolys G ω)
    (wP pP qPP : F[X]) (α β γ : F) (hdef : G.defPoly ω wP pP qPP γ = 0) {i : ℕ} (hi : i < G.N) :
    (G.dPushP ω S pP α β).eval (ω i) = G.dPushV ω (fun j => wP.eval (ω j)) α β i := by
  have hp : pP.eval (ω i) = (G.pushPolyV ω wP γ).eval (ω i) := by
    have h := congrArg (fun p => p.eval (ω i)) hdef
    simp only [defPoly, eval_add, eval_mul, zV_eval hi, mul_zero, add_zero, eval_zero] at h
    exact CharTwo.add_eq_zero.mp h
  unfold dPushP dPushV den
  rw [eval_add, eval_add, eval_add, eval_mul, eval_C, eval_C, hp, add_assoc _ _ (S.κP.eval (ω i)),
    S.κ_eval i hi, pushPolyV_eval hV hP hn wP γ hi, S.σ_eval i hi, add_assoc]

/-- **The identity on `V_m` is the copy argument's pointwise identity**, with `h_i = h(ω_i)`, where `P`'s
definition holds. -/
theorem idPoly_eval_omega (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n)
    (S : SetupPolys G ω) (pub : ℕ → List F) (Φ : ℕ → F[X]) (wP hP' qP pP qPP : F[X]) (α β γ : F)
    (hΦ : ∀ j < G.nP, (Φ (G.port j % G.W)).eval (ω (G.port j)) = G.pubFp γ pub j)
    (hdef : G.defPoly ω wP pP qPP γ = 0) {i : ℕ} (hi : i < G.N) :
    (G.idPoly ω S Φ wP hP' qP pP α β γ).eval (ω i) =
      hP'.eval (ω i) * dPull ω (fun j => wP.eval (ω j)) α β i *
          G.dPushV ω (fun j => wP.eval (ω j)) α β i +
        (1 + G.holeInd i) * (G.dPushV ω (fun j => wP.eval (ω j)) α β i + dPull ω (fun j => wP.eval (ω j)) α β i) +
          G.tVal pub (fun j => wP.eval (ω j)) γ i := by
  unfold idPoly
  rw [eval_add, eval_add, eval_add, eval_mul, eval_mul, eval_mul, eval_mul, eval_add, eval_add, eval_one,
    zV_eval hi, mul_zero, add_zero, dPullP_eval, dPushP_eval hV hP hn S wP pP qPP α β γ hdef hi,
    holePoly_eval hV hP hn hi, tPoly_eval hV hP hn pub Φ wP γ hΦ hi]

/-- **The identities as polynomials give the state after `α, β, γ`**: if both are zero and `Σ_V h = 0`,
`CopyOK` holds of the witness `w(ω_i)`. -/
theorem copyOK_of_idPoly (hV : G.Valid) (hP : Points ω n) (hn : G.logN ≤ n) (S : SetupPolys G ω)
    (pub : ℕ → List F) (Φ : ℕ → F[X]) (wP hP' qP pP qPP : F[X]) (α β γ : F)
    (hΦ : ∀ j < G.nP, (Φ (G.port j % G.W)).eval (ω (G.port j)) = G.pubFp γ pub j)
    (hid : G.idPoly ω S Φ wP hP' qP pP α β γ = 0) (hdef : G.defPoly ω wP pP qPP γ = 0)
    (hsum : ∑ i ∈ range G.N, hP'.eval (ω i) = 0) :
    G.CopyOK ω pub (fun j => wP.eval (ω j)) α β γ :=
  ⟨fun i => hP'.eval (ω i), fun i hi => by
    unfold PointId
    rw [← idPoly_eval_omega hV hP hn S pub Φ wP hP' qP pP qPP α β γ hΦ hdef hi, hid, eval_zero], hsum⟩

/-! ## The degrees -/

theorem natDegree_cellPoly_le (wP : F[X]) (k c : ℕ) : (cellPoly ω wP k c).natDegree ≤ wP.natDegree := by
  unfold cellPoly
  refine natDegree_comp_le.trans ?_
  rw [natDegree_X_add_C, mul_one]

theorem N_ge_two (hV : G.Valid) : 2 ≤ G.N := by
  unfold N
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ G.logN := Nat.pow_le_pow_right (by norm_num) (by have := hV.logW_lt; omega)

/-- **The internal pushes have degree below `3N`**: `3(N − 1)`. -/
theorem natDegree_pushPolyV_le (hV : G.Valid) {wP : F[X]} (hw : wP.natDegree < G.N) (γ : F) :
    (G.pushPolyV ω wP γ).natDegree ≤ 3 * (G.N - 1) := by
  have hw' : wP.natDegree ≤ G.N - 1 := by omega
  unfold pushPolyV
  refine natDegree_add_le_of_degree_le (by omega) ?_
  refine natDegree_sum_le_of_forall_le _ _ fun p hp => ?_
  have hp' := (mem_intPairs.mp hp).1
  refine natDegree_mul_le_of_le (natDegree_ind_le' hV hp')
    (natDegree_add_le_of_degree_le (n := 2 * (G.N - 1)) ?_ (by omega)) |>.trans (by omega)
  exact Role.natDegree_value_le _ γ hw' fun c => (natDegree_cellPoly_le wP _ c).trans hw'

/-- A port pair's formula is linear: below `N`. -/
theorem natDegree_formulaPoly_port_le {wP : F[X]} {p : Block × ℕ} (hp : (G.regionRole p.1 p.2).isPort = true)
    (γ : F) : (G.formulaPoly ω wP γ p).natDegree ≤ wP.natDegree := by
  unfold formulaPoly
  cases hr : G.regionRole p.1 p.2 with
  | forward => rw [hr] at hp; simp [Role.isPort] at hp
  | expr _ => rw [hr] at hp; simp [Role.isPort] at hp
  | port ls => exact fpEval_natDegree_le ls γ fun c => natDegree_cellPoly_le wP _ c

theorem natDegree_holePoly_le (hV : G.Valid) : (G.holePoly ω).natDegree ≤ G.N - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun _ hp => natDegree_ind_le' hV (mem_portPairs.mp hp).1

/-- **The ports' term has degree at most `2(N − 1)`.** -/
theorem natDegree_tPoly_le (hV : G.Valid) {Φ : ℕ → F[X]} (hΦ : ∀ k, (Φ k).natDegree < G.N) {wP : F[X]}
    (hw : wP.natDegree < G.N) (γ : F) : (G.tPoly ω Φ wP γ).natDegree ≤ 2 * (G.N - 1) := by
  unfold tPoly
  refine natDegree_sum_le_of_forall_le _ _ fun p hp => ?_
  have hp' := mem_portPairs.mp hp
  refine natDegree_mul_le_of_le (natDegree_ind_le' hV hp'.1)
    (natDegree_add_le_of_degree_le (n := G.N - 1) ((natDegree_formulaPoly_port_le hp'.2 γ).trans (by omega))
      (by have := hΦ p.2; omega)) |>.trans (by omega)

theorem natDegree_zV_le : (G.zV ω).natDegree ≤ G.N := by
  unfold zV
  refine (natDegree_prod_le _ _).trans (le_of_eq ?_)
  simp

theorem natDegree_dPullP_le {wP : F[X]} {D : ℕ} (hw : wP.natDegree ≤ D) (hD : 1 ≤ D) (α β : F) :
    (dPullP wP α β).natDegree ≤ D := by
  unfold dPullP
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ hw) ?_
  · rw [natDegree_C]; exact Nat.zero_le _
  · exact (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans hD)

theorem natDegree_dPushP_le (S : SetupPolys G ω) {pP : F[X]} (hp : pP.natDegree < G.N)
    (α β : F) : (G.dPushP ω S pP α β).natDegree ≤ G.N - 1 := by
  have := S.σ_deg
  have := S.κ_deg
  unfold dPushP
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_
    (by omega)) (by omega)) ?_
  · rw [natDegree_C]; exact Nat.zero_le _
  · exact (natDegree_C_mul_le _ _).trans (by omega)

/-- **`P`'s definition has degree at most `3N − 1`**, for `w`, `P` below `N` and `q_P` below `2N`. -/
theorem natDegree_defPoly_le (hV : G.Valid) {wP pP qPP : F[X]} (hw : wP.natDegree < G.N)
    (hp : pP.natDegree < G.N) (hq : qPP.natDegree < 2 * G.N) (γ : F) :
    (G.defPoly ω wP pP qPP γ).natDegree ≤ 3 * G.N - 1 := by
  have h2 := N_ge_two hV
  have hv := natDegree_pushPolyV_le (ω := ω) hV hw γ
  have hz := natDegree_zV_le (G := G) (ω := ω)
  have hD := natDegree_mul_le_of_le (Nat.le_sub_one_of_lt hq) hz
  unfold defPoly
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (by omega) (hv.trans (by omega)))
    (hD.trans (by omega))

/-- **The copy identity has degree at most `3N − 1`**, for `w, σ, κ, h, P, Φ` below `N` and `q` below `2N`
(`q·Z_V` dominates; `h·d_pull·d_push` is at most `3(N − 1)`, the rest at most `2(N − 1)`). -/
theorem natDegree_idPoly_le (hV : G.Valid) (S : SetupPolys G ω) {Φ : ℕ → F[X]}
    (hΦ : ∀ k, (Φ k).natDegree < G.N) {wP hP qP pP : F[X]}
    (hw : wP.natDegree < G.N) (hh : hP.natDegree < G.N) (hq : qP.natDegree < 2 * G.N)
    (hp : pP.natDegree < G.N) (α β γ : F) : (G.idPoly ω S Φ wP hP qP pP α β γ).natDegree ≤ 3 * G.N - 1 := by
  have h2 := N_ge_two hV
  have hpull := natDegree_dPullP_le (D := G.N - 1) (by omega) (by omega) α β (wP := wP)
  have hpush := natDegree_dPushP_le S hp α β
  have hhole := natDegree_holePoly_le hV (ω := ω)
  have ht := natDegree_tPoly_le (ω := ω) hV hΦ hw γ
  have hz := natDegree_zV_le (G := G) (ω := ω)
  have h1 : (1 + G.holePoly ω).natDegree ≤ G.N - 1 :=
    natDegree_add_le_of_degree_le (by rw [natDegree_one]; exact Nat.zero_le _) hhole
  have hA := natDegree_mul_le_of_le (natDegree_mul_le_of_le hh.le hpull) hpush
  have hB := natDegree_mul_le_of_le h1 (natDegree_add_le_of_degree_le hpush hpull)
  have hD := natDegree_mul_le_of_le (Nat.le_sub_one_of_lt hq) hz
  unfold idPoly
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (hA.trans ?_) (hB.trans ?_)) (ht.trans ?_)) (hD.trans ?_) <;>
  · generalize G.N = N at *
    omega

/-! ## Schwartz–Zippel in `t` -/

/-- A nonzero polynomial vanishes at at most its degree's number of points. -/
theorem card_eval_eq_zero_le [Fintype F] (p : F[X]) (hp : p ≠ 0) :
    (univ.filter fun t => p.eval t = 0).card ≤ p.natDegree := by
  refine (Finset.card_le_card fun t ht => ?_).trans ((Multiset.toFinset_card_le _).trans
    (card_roots' p))
  rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
  exact (Finset.mem_filter.mp ht).2

/-- **The identities at a random point**: unless both are zero, they vanish together at at most `3N − 1` points
`t`. -/
theorem card_idPoly_eval_eq_zero_le [Fintype F] (hV : G.Valid) (S : SetupPolys G ω) {Φ : ℕ → F[X]}
    (hΦ : ∀ k, (Φ k).natDegree < G.N) {wP hP qP pP qPP : F[X]} (hw : wP.natDegree < G.N)
    (hh : hP.natDegree < G.N) (hq : qP.natDegree < 2 * G.N) (hp : pP.natDegree < G.N)
    (hqp : qPP.natDegree < 2 * G.N) (α β γ : F)
    (hne : ¬ (G.idPoly ω S Φ wP hP qP pP α β γ = 0 ∧ G.defPoly ω wP pP qPP γ = 0)) :
    (univ.filter fun t => (G.idPoly ω S Φ wP hP qP pP α β γ).eval t = 0 ∧
      (G.defPoly ω wP pP qPP γ).eval t = 0).card ≤ 3 * G.N - 1 := by
  by_cases h1 : G.idPoly ω S Φ wP hP qP pP α β γ = 0
  · have h2 : G.defPoly ω wP pP qPP γ ≠ 0 := fun h => hne ⟨h1, h⟩
    exact (Finset.card_le_card fun t ht => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp ht).2.2⟩).trans ((card_eval_eq_zero_le _ h2).trans
        (natDegree_defPoly_le hV hw hp hqp γ))
  · exact (Finset.card_le_card fun t ht => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp ht).2.1⟩).trans ((card_eval_eq_zero_le _ h1).trans
        (natDegree_idPoly_le hV S hΦ hw hh hq hp α β γ))

end Circuit

end RecPiop
