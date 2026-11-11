-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The transforms' lemmas are `formal/EndToEnd/Bridge`'s
-- (`Bridge.Ntt.values_getD_E`, `values_coefficients_E`) at `formal/UniComplete`'s Cantor basis (`AlgC.cantorUpTo`,
-- `novX_ofK`, `Ppoint_eq`).
import RecCompose.Pi2Prover
import RecCompose.Tables

/-!
# π2's honest prover: the transforms, the coset, the stacks

The facts the honest prover's algebra (`Pi2Honest.lean`) reads its computations through:

* **interpolation**: two polynomials of degree below `n` agreeing at `n` distinct points are equal (`poly_eq_of_eval_eq`);
* **the transform** (`PcsQuotient.Domain.values`, `coefficients`): `values k offset c` at `p` is the novel-basis
  polynomial of `c` at `offset + B(p)` (`values_getD_novP`), and the polynomial of `coefficients k offset v` takes `v`
  there (`novP_coefficients_eval`);
* **the coset** `β_{m+1} + V_{m+1}`: its point `p` is `ω_{2^(m+1) ⊕ p}` (`cosetPoint_eq`), a cell moves it by `ω_c`
  (`cosetPoint_xor`), and it is off `V_m` (`cosetPoint_ne`);
* **the stacks**: a padded stack reads back its table (`getD_padStack_lt`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol Finset Polynomial

/-! ## Interpolation -/

theorem degree_lt_of_natDegree_lt {p : E[X]} {n : ℕ} (h : p.natDegree < n) : p.degree < n :=
  lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.mpr h)

/-- **Two polynomials of degree below `n` agreeing at `n` distinct points are equal.** -/
theorem poly_eq_of_eval_eq {p q : E[X]} {n : ℕ} (hp : p.natDegree < n) (hq : q.natDegree < n) (f : ℕ → E)
    (hf : ∀ a < n, ∀ b < n, f a = f b → a = b) (h : ∀ i < n, p.eval (f i) = q.eval (f i)) : p = q := by
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq ((range n).image f) ?_ ?_
  · rw [card_image_of_injOn (fun a ha b hb hab ↦ hf a (mem_range.mp ha) b (mem_range.mp hb) hab), card_range]
    exact lt_of_le_of_lt (degree_sub_le p q) (max_lt (degree_lt_of_natDegree_lt hp) (degree_lt_of_natDegree_lt hq))
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact h i (mem_range.mp hi)

/-! ## The transform -/

/-- **`values` is the novel-basis polynomial on the coset**: entry `p` of `values k offset c` is `Σ_j c_j X_j` at
`offset + B(p)`. -/
theorem values_getD_novP {k : ℕ} (hk : k ≤ 28) (offset : K) (c : Array E) (hc : c.size = 2 ^ k) {p : ℕ}
    (hp : p < 2 ^ k) :
    (PcsQuotient.Domain.values k offset c).getD p 0 =
      (UniKeccakComplete.AlgC.novP k fun j ↦ c.getD j 0).eval (ofK (offset + PcsQuotient.Domain.point p)) := by
  rw [Bridge.Ntt.values_getD_E (UniKeccakComplete.AlgC.cantorUpTo hk) hk offset c hc hp, UniKeccakComplete.AlgC.novP_eval]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [UniKeccakComplete.AlgC.novX_ofK, mul_comm]

/-- **The coefficients' polynomial takes the values**: `Σ_j (coefficients k offset v)_j X_j` is `v_p` at
`offset + B(p)`. -/
theorem novP_coefficients_eval {k : ℕ} (hk : k ≤ 28) (offset : K) (v : Array E) (hv : v.size = 2 ^ k) {p : ℕ}
    (hp : p < 2 ^ k) :
    (UniKeccakComplete.AlgC.novP k fun j ↦ (PcsQuotient.Domain.coefficients k offset v).getD j 0).eval
      (ofK (offset + PcsQuotient.Domain.point p)) = v.getD p 0 := by
  rw [← values_getD_novP hk offset _ (by rw [Bridge.Ntt.coefficients_size, hv]) hp,
    Bridge.Ntt.values_coefficients_E k offset v hv]

/-- The statement's point, embedded, is `pi2Omega` below `2^28`. -/
theorem ofK_point_eq {i : ℕ} (hi : i < 2 ^ 28) : ofK (PcsQuotient.Domain.point i) = pi2Omega i := by
  rw [UniKeccakComplete.AlgC.Ppoint_eq hi, pi2Omega_eq]
  rfl

/-- **The novel-basis polynomial of an interpolation's coefficients** takes the values on `V_k`. -/
theorem novP_values_omega {k : ℕ} (hk : k ≤ 28) (v : Array E) (hv : v.size = 2 ^ k) {i : ℕ} (hi : i < 2 ^ k) :
    (UniKeccakComplete.AlgC.novP k fun j ↦ (UniComplete.novelOfValuesE k v).getD j 0).eval (pi2Omega i) = v.getD i 0 := by
  have h := novP_coefficients_eval hk 0 v hv hi
  rw [zero_add, ofK_point_eq (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hk))] at h
  exact h

/-- The same for a `K`-column. -/
theorem novP_valuesK_omega {k : ℕ} (hk : k ≤ 28) (v : Array K) (hv : v.size = 2 ^ k) {i : ℕ} (hi : i < 2 ^ k) :
    (UniKeccakComplete.AlgC.novP k fun j ↦ (UniComplete.novelOfValuesK k v).getD j 0).eval (pi2Omega i) =
      ofK (v.getD i 0) := by
  have h := UniKeccakComplete.AlgC.pEval_colPolyK_pointE hk v hv hi
  rw [UniKeccakComplete.AlgC.pEval_eq, UniKeccakComplete.colPolyK, UniKeccakComplete.AlgC.ofNovel_toPoly] at h
  rw [pi2Omega_eq]
  exact h

/-! ## The coset -/

theorem xor_lt_pow {a b n : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) : a ^^^ b < 2 ^ n := Nat.xor_lt_two_pow ha hb

/-- **The coset's point `p` is `ω_{2^(m+1) ⊕ p}`.** -/
theorem cosetPoint_eq {m p : ℕ} (hm : m + 1 < 28) (hp : p < 2 ^ (m + 1)) :
    cosetPoint m p = pi2Omega (2 ^ (m + 1) ^^^ p) := by
  have hp28 : p < 2 ^ 28 := lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold cosetPoint cosetOffset
  rw [UniComplete.Domain.embed_add, ← UniComplete.Domain.point_two_pow (by omega), ofK_point_eq hp28, pi2Omega_eq,
    pi2Omega_eq, UniComplete.Domain.pointE_xor]
  rfl

/-- **A cell moves a coset point by `ω_c`.** -/
theorem cosetPoint_xor {m p c : ℕ} (hm : m + 1 < 28) (hp : p < 2 ^ (m + 1)) (hc : c < 2 ^ (m + 1)) :
    cosetPoint m (p ^^^ c) = cosetPoint m p + pi2Omega c := by
  rw [cosetPoint_eq hm (xor_lt_pow hp hc), cosetPoint_eq hm hp, pi2Omega_eq, pi2Omega_eq, pi2Omega_eq,
    ← UniComplete.Domain.pointE_xor, Nat.xor_assoc]

theorem two_pow_xor_testBit {m p : ℕ} (hp : p < 2 ^ (m + 1)) : (2 ^ (m + 1) ^^^ p).testBit (m + 1) = true := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_self, Nat.testBit_eq_false_of_lt hp]
  rfl

/-- The coset's indices are distinct. -/
theorem cosetPoint_inj {m : ℕ} (hm : m + 1 < 28) {a b : ℕ} (ha : a < 2 ^ (m + 1)) (hb : b < 2 ^ (m + 1))
    (h : cosetPoint m a = cosetPoint m b) : a = b := by
  rw [cosetPoint_eq hm ha, cosetPoint_eq hm hb] at h
  have h32 : ∀ x < 2 ^ (m + 1), 2 ^ (m + 1) ^^^ x < 2 ^ 32 := fun x hx ↦
    lt_of_lt_of_le (xor_lt_pow (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)) (lt_trans hx
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)))) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have := (RecPiop.Points.ofCantor UniComplete.Domain.basisE).inj _ (h32 a ha) _ (h32 b hb) h
  have e := congrArg (2 ^ (m + 1) ^^^ ·) this
  simpa [← Nat.xor_assoc] using e

/-- **The coset is off `V_m`.** -/
theorem cosetPoint_ne {m p j : ℕ} (hm : m + 1 < 28) (hp : p < 2 ^ (m + 1)) (hj : j < 2 ^ m) :
    cosetPoint m p ≠ pi2Omega j := by
  rw [cosetPoint_eq hm hp]
  intro h
  have h32a : 2 ^ (m + 1) ^^^ p < 2 ^ 32 :=
    lt_of_lt_of_le (xor_lt_pow (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)) (lt_trans hp
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)))) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h32b : j < 2 ^ 32 := lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega))
  have := (RecPiop.Points.ofCantor UniComplete.Domain.basisE).inj _ h32a _ h32b h
  have hb := two_pow_xor_testBit hp
  rw [this, Nat.testBit_eq_false_of_lt (lt_trans hj (Nat.pow_lt_pow_right (by norm_num) (by omega)))] at hb
  exact absurd hb (by decide)

/-! ## The stacks -/

/-- **A padded stack reads its table below `2^vars`, zero beyond.** -/
theorem padStack_getD (vars : ℕ) (T : ℕ → K) (i : ℕ) :
    (padStack vars T).getD i 0 = if i < 2 ^ vars then T i else 0 := by
  split_ifs with h <;> simp [padStack, Array.getD, h]

/-- **A padded stack reads back its table** below `2^vars`. -/
theorem getD_padStack_lt (vars : ℕ) (T : ℕ → K) {i : ℕ} (hi : i < 2 ^ vars) : (padStack vars T).getD i 0 = T i := by
  simp [padStack, Array.getD, hi]

/-! ## `K` inside `E` -/

theorem ofK_mem_subK (a : K) : ofK a ∈ subK := ⟨a, rfl⟩

theorem limb_zero_of_mem {x : E} (hx : x ∈ subK) : ofK (x.limb 0) = x := by
  obtain ⟨a, rfl⟩ := hx
  rfl

/-- **A stage of the transform commutes with `K → E`.** -/
theorem stageF_map (fwd : Bool) (lam : ℕ → K) (k : ℕ) (a : ℕ → K) (p : ℕ) :
    algebraMap K E (Bridge.Ntt.stageF fwd lam k a p) =
      Bridge.Ntt.stageF fwd lam k (fun i ↦ algebraMap K E (a i)) p := by
  unfold Bridge.Ntt.stageF
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs <;> simp [map_add, map_mul]

theorem coefficientsF_map (lamOf : ℕ → ℕ → K) : ∀ (m : ℕ) (v : ℕ → K) (p : ℕ),
    algebraMap K E (Bridge.Ntt.coefficientsF lamOf m v p) =
      Bridge.Ntt.coefficientsF lamOf m (fun i ↦ algebraMap K E (v i)) p
  | 0, _, _ => rfl
  | m + 1, v, p => by
    rw [Bridge.Ntt.coefficientsF_succ, Bridge.Ntt.coefficientsF_succ, stageF_map]
    congr 1
    funext i
    exact coefficientsF_map lamOf m v i

theorem valuesF_map (lamOf : ℕ → ℕ → K) : ∀ (m : ℕ) (v : ℕ → K) (p : ℕ),
    algebraMap K E (Bridge.Ntt.valuesF lamOf m v p) = Bridge.Ntt.valuesF lamOf m (fun i ↦ algebraMap K E (v i)) p
  | 0, _, _ => rfl
  | m + 1, v, p => by
    rw [Bridge.Ntt.valuesF_succ, Bridge.Ntt.valuesF_succ, valuesF_map lamOf m]
    congr 1
    funext i
    exact stageF_map _ _ _ _ i

/-- **The `K` transform, embedded, is the `E` transform of the embedded values.** -/
theorem coefficients_map_ofK {r : ℕ} (off : K) (v : Array K) (hv : v.size = 2 ^ r) {p : ℕ} (hp : p < 2 ^ r) :
    ofK ((PcsQuotient.Domain.coefficients r off v).getD p 0) =
      (PcsQuotient.Domain.coefficients r off (v.map ofK)).getD p 0 := by
  rw [Bridge.Ntt.coefficients_getD_K' r off v hv p hp,
    Bridge.Ntt.coefficients_getD_E' r off (v.map ofK) (by rw [Array.size_map, hv]) p hp]
  refine (coefficientsF_map _ r _ p).trans ?_
  congr 1
  funext i
  exact (UniKeccakComplete.AlgC.getD_map_ofK v i).symm

/-- **The `E` transform of embedded values is embedded.** -/
theorem values_mem_subK {r : ℕ} (off : K) (c : Array E) (hc : c.size = 2 ^ r) (hK : ∀ i < 2 ^ r, c.getD i 0 ∈ subK)
    {p : ℕ} (hp : p < 2 ^ r) : (PcsQuotient.Domain.values r off c).getD p 0 ∈ subK := by
  choose! a ha using fun i hi ↦ hK i hi
  have e : (PcsQuotient.Domain.values r off c).getD p 0 =
      algebraMap K E (Bridge.Ntt.valuesF (Bridge.Ntt.lamAt (PcsQuotient.Domain.chain off r)) r
        (fun i ↦ if i < 2 ^ r then a i else 0) p) := by
    rw [Bridge.Ntt.values_getD_E' r off c hc p hp, valuesF_map]
    unfold Bridge.Ntt.valuesF
    refine Bridge.Ntt.foldr_congr (m := r) true _ (List.range r) (fun k hk ↦ List.mem_range.mp hk)
      (fun i hi ↦ ?_) p hp
    simp only [hi, ite_true]
    exact (ha i hi).symm
  rw [e]
  exact ofK_mem_subK _

/-! ## A circuit over `K` -/

/-- **A circuit over `K`**: `κ` in `K`, and every internal role's value in `K` on cells in `K` (the compiled
circuits: `kCircuit_toPiop`). -/
structure KCircuit (G : RecPiop.Circuit E) : Prop where
  kappa : ∀ i, G.kappa i ∈ subK
  value : ∀ (b : RecPiop.Block) (k : ℕ) (γ own : E) (cell : ℕ → E), (G.regionRole b k).isPort = false →
    own ∈ subK → (∀ c, cell c ∈ subK) → (G.regionRole b k).value γ own cell ∈ subK

theorem list_sum_mem_subK {l : List E} (h : ∀ x ∈ l, x ∈ subK) : l.sum ∈ subK := list_sum_mem h

/-- **The compiled circuits are over `K`.** -/
theorem kCircuit_toPiop (C : RecCircuit.Circuit) : KCircuit C.toPiop where
  kappa i := ofK_mem_subK _
  value b k γ own cell hp ho hc := by
    have hr : ∃ f, C.toPiop.regionRole b k = RecCircuit.toRole f := by
      unfold RecPiop.Circuit.regionRole
      simp only [RecCircuit.Circuit.toPiop]
      refine ⟨((C.regions.toList.getD b.region default).roles.toList.getD k .forward), ?_⟩
      rw [show ([] : List (RecPiop.Role E)) = (fun r : RecCircuit.Region ↦ r.roles.toList.map RecCircuit.toRole)
          default from rfl, RecCircuit.list_getD_map,
        show (RecPiop.Role.forward : RecPiop.Role E) = RecCircuit.toRole .forward from rfl, RecCircuit.list_getD_map]
    obtain ⟨f, hf⟩ := hr
    rw [hf] at hp ⊢
    cases f with
    | forward => exact ho
    | port ls => simp [RecCircuit.toRole, RecPiop.Role.isPort] at hp
    | expr q =>
      show RecPiop.Poly2.eval (RecCircuit.toPoly2 q) cell ∈ subK
      unfold RecPiop.Poly2.eval RecCircuit.toPoly2
      refine add_mem (list_sum_mem_subK fun x hx ↦ ?_) (list_sum_mem_subK fun x hx ↦ ?_)
      · simp only [List.map_map, List.mem_map, Function.comp] at hx
        obtain ⟨t, -, rfl⟩ := hx
        exact mul_mem (by simp only [Algebra.algebraMap_self, RingHom.id_apply]; exact ofK_mem_subK _) (hc _)
      · simp only [List.map_map, List.mem_map, Function.comp] at hx
        obtain ⟨t, -, rfl⟩ := hx
        exact mul_mem (by simp only [Algebra.algebraMap_self, RingHom.id_apply]; exact ofK_mem_subK _)
          (mul_mem (hc _) (hc _))

end RecCompose

/-- info: 'RecCompose.cosetPoint_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.cosetPoint_ne

/-- info: 'RecCompose.novP_coefficients_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.novP_coefficients_eval
