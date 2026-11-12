-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsGroup1Onto
import ZK.PcsIdeal

/-!
# Group 1 is uniform off `εgroup1` of the challenges

The good event's failure is a union of events each pinning one coordinate of `W`'s point to a value (or to one of
`|K|` values) that the other coordinates and `t` fix (`prEvent_hit`, by resampling that coordinate: `iidE_set`), or
`t` to the roots of a polynomial of degree `4` or `2` over `E` with a coefficient in `K` (`prEvent_inK_poly`):
`w₂(t) ∈ K` (`4 |K|` values), `t² + θ t ∈ K` (`2 |K|`), and on `W`'s point `44` single values and `3 |K|`.

* **`group1Uniform`**: `Group1Uniform εgroup1`, `εgroup1 = (9 · 2^64 + 44) · 2^-192 ≤ 2^-124` (`εgroup1_le`).
* **`zeroKnowledge_of_pcs`**: zero knowledge of the membership proof over every PCS with `PcsZeroKnowledge` as the
  only hypothesis, within `εpcs Q + εgroup1 + εslack + εfs₀`; **`zeroKnowledge_ideal`**: over the model's ideal
  PCS, within `εgroup1 + εslack + εfs₀`, with no hypothesis.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open PcsQuotient.Domain QuotientSecurity Finset
open scoped ENNReal

-- The membership circuit is a closed term of `2^22` rows: never evaluate it.
attribute [local irreducible] PcsQuotient.membership PcsQuotient.membershipBuilder

namespace PcsQuotient.EndToEnd.Group1

/-! ### Resampling one coordinate -/

theorem xc_set_ne (z : List E) {b j : ℕ} (h : j ≠ b) (x : E) : xc (z.set b x) j = xc z j := by
  simp only [xc, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem xc_set_self (z : List E) {b : ℕ} (h : b < z.length) (x : E) : xc (z.set b x) b = x := by
  simp only [xc, List.getD_eq_getElem?_getD, List.getElem?_set_self h, Option.getD_some]

theorem uz_set_ne (z : List E) {b j : ℕ} (h : j ≠ b) (x : E) : uz (z.set b x) j = uz z j := by
  rw [uz, uz, xc_set_ne z h]

/-- **Resampling a coordinate of `n` uniform elements leaves their law.** -/
theorem iidE_set : ∀ (n b : ℕ), b < n →
    (iidE n >>= fun z ↦ eDist >>= fun x ↦ (pure (z.set b x) : ProbComp (List E))) =ᵈ iidE n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, 0, _ => by
    rw [iidE_succ]
    simp only [bind_assoc, pure_bind, List.set_cons_zero]
    exact (evalDistEq_bind_drop _ _).trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  | n + 1, b + 1, h => by
    rw [iidE_succ]
    simp only [bind_assoc, pure_bind, List.set_cons_succ]
    refine EvalDistEq.bind_right _ fun e ↦ ?_
    have := (iidE_set n b (by omega)).bind_left (fun l ↦ (pure (e :: l) : ProbComp (List E)))
    simpa only [bind_assoc, pure_bind] using this

/-- **A coordinate hits one of `|ι|` values fixed by the others** with probability at most `|ι| · 2^-192`. -/
theorem prEvent_hit {ι : Type} [Fintype ι] (n b : ℕ) (hb : b < n) (g : ι → List E → E)
    (hg : ∀ i z x, g i (z.set b x) = g i z) :
    Pr{let z ← iidE n}[∃ i, xc z b = g i z] ≤ Fintype.card ι * κE := by
  have h1 : Pr{let z ← iidE n}[∃ i, xc z b = g i z] =
      Pr{let z ← iidE n}[b < z.length ∧ ∃ i, xc z b = g i z] :=
    prEvent_congr_of_support _ _ _ fun z hz ↦ by
      rw [length_of_mem_iidE n z hz]; simp only [hb, true_and]
  rw [h1, ← (iidE_set n b hb).prEvent_eq]
  refine prEvent_bind_le_of_forall_le _ _ _ fun z ↦ ?_
  rw [prEvent_bind_pure]
  refine (prEvent_mono_of_support _ _ (fun x ↦ ∃ i, x = g i z) fun x _ hx ↦ ?_).trans
    (prEvent_eDist_exists fun i ↦ g i z)
  obtain ⟨hl, i, hi⟩ := hx
  rw [List.length_set] at hl
  rw [xc_set_self z hl, hg] at hi
  exact ⟨i, hi⟩

/-- The same for `u_b = 1 + z_b`. -/
theorem prEvent_hit_u {ι : Type} [Fintype ι] (b : ℕ) (hb : b < 24) (g : ι → List E → E)
    (hg : ∀ i z x, g i (z.set b x) = g i z) :
    Pr{let z ← iidE 24}[∃ i, uz z b = g i z] ≤ Fintype.card ι * κE := by
  refine le_trans (prEvent_mono_of_support _ _ (fun z ↦ ∃ i, xc z b = g i z - 1) fun z _ ⟨i, hi⟩ ↦
    ⟨i, by rw [← hi, uz]; ring⟩) ?_
  exact prEvent_hit 24 b hb (fun i z ↦ g i z - 1) fun i z x ↦ by rw [hg]

/-- One value of `u_b`. -/
theorem prEvent_hit1 (b : ℕ) (hb : b < 24) (g : List E → E) (hg : ∀ z x, g (z.set b x) = g z) :
    Pr{let z ← iidE 24}[uz z b = g z] ≤ κE := by
  have := prEvent_hit_u (ι := Unit) b hb (fun _ ↦ g) fun _ z x ↦ hg z x
  rw [Fintype.card_unit, Nat.cast_one, one_mul] at this
  exact le_trans (prEvent_mono_of_support _ _ _ fun z _ h ↦ ⟨(), h⟩) this

/-- `|K|` values of `u_b`. -/
theorem prEvent_hitK (b : ℕ) (hb : b < 24) (g : K → List E → E) (hg : ∀ l z x, g l (z.set b x) = g l z) :
    Pr{let z ← iidE 24}[∃ l, uz z b = g l z] ≤ 2 ^ 64 * κE := by
  have := prEvent_hit_u b hb g hg
  rwa [show (Fintype.card K : ℝ≥0∞) = 2 ^ 64 by rw [BF64.card_bf64]; norm_num] at this

/-- A union over `Fin n`. -/
theorem prEvent_exists_fin {α : Type} (X : ProbComp α) : ∀ (n : ℕ) (P : Fin n → α → Prop) (ε : ℝ≥0∞),
    (∀ i, Pr{let x ← X}[P i x] ≤ ε) → Pr{let x ← X}[∃ i, P i x] ≤ n * ε
  | 0, P, ε, _ => by
    rw [(prEvent_eq_zero_iff _ _).2 fun x _ ⟨i, _⟩ ↦ i.elim0]; exact zero_le
  | n + 1, P, ε, h => by
    calc Pr{let x ← X}[∃ i, P i x] ≤ Pr{let x ← X}[P 0 x ∨ ∃ i : Fin n, P i.succ x] :=
          prEvent_mono_of_support _ _ _ fun x _ hx ↦ Fin.exists_fin_succ.1 hx
      _ ≤ ε + n * ε := (prEvent_or_le _ _ _).trans
          (add_le_add (h 0) (prEvent_exists_fin X n (fun i ↦ P i.succ) ε fun i ↦ h i.succ))
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * ε := by push_cast; ring

/-! ### `W`'s point -/

theorem HQ_set (t : E) (z : List E) {b : ℕ} (hb : 4 ≤ b) (x : E) (Q : Fin 4) :
    HQ t (z.set b x) Q = HQ t z Q := by
  unfold HQ
  rw [uz_set_ne z (by omega), uz_set_ne z (by omega), uz_set_ne z (by omega), uz_set_ne z (by omega)]

theorem yQ_set (t : E) (z : List E) {b : ℕ} (hb : 5 ≤ b) (x : E) (Q : Fin 4) :
    yQ t (z.set b x) Q = yQ t z Q := by
  unfold yQ
  rw [HQ_set t z (by omega), uz_set_ne z (by omega)]

/-- **A quarter's `H` vanishes** with probability at most `5 · 2^-192`. -/
theorem prEvent_notGoodH (t : E) (Q : Fin 4) :
    Pr{let z ← iidE 24}[¬ GoodH θE (γQ Q) (δQ Q) (eQ Q) (cK t Q) (uz z 0) (uz z 1) (uz z 2) (uz z 3)] ≤
      5 * κE := by
  set κ := cK t Q
  refine (prEvent_mono_of_support _ _ (fun z ↦ uz z 0 = 0 ∨ uz z 2 = A0 κ / A1 θE (γQ Q) κ ∨
    uz z 2 = A2 (δQ Q) κ / A3 θE (γQ Q) (δQ Q) κ ∨
    uz z 3 = (A0 κ + uz z 2 * A1 θE (γQ Q) κ) / (A2 (δQ Q) κ + uz z 2 * A3 θE (γQ Q) (δQ Q) κ) ∨
    uz z 1 = θE * uz z 0 * Pq θE (γQ Q) (δQ Q) κ (uz z 2) (uz z 3) /
      βq θE (γQ Q) (δQ Q) (eQ Q) κ (uz z 0) (uz z 2) (uz z 3)) fun z _ h ↦ ?_).trans ?_
  · unfold GoodH at h
    by_contra hn
    push Not at hn
    exact h hn
  · refine (prEvent_or_le _ _ _).trans ?_
    refine (add_le_add (prEvent_hit1 0 (by norm_num) (fun _ ↦ 0) fun _ _ ↦ rfl)
      ((prEvent_or_le _ _ _).trans (add_le_add
        (prEvent_hit1 2 (by norm_num) (fun _ ↦ _) fun _ _ ↦ rfl)
        ((prEvent_or_le _ _ _).trans (add_le_add
          (prEvent_hit1 2 (by norm_num) (fun _ ↦ _) fun _ _ ↦ rfl)
          ((prEvent_or_le _ _ _).trans (add_le_add
            (prEvent_hit1 3 (by norm_num) (fun z ↦ (A0 κ + uz z 2 * A1 θE (γQ Q) κ) /
              (A2 (δQ Q) κ + uz z 2 * A3 θE (γQ Q) (δQ Q) κ)) fun z x ↦ by
                rw [uz_set_ne z (by norm_num)])
            (prEvent_hit1 1 (by norm_num) (fun z ↦ θE * uz z 0 * Pq θE (γQ Q) (δQ Q) κ (uz z 2) (uz z 3) /
              βq θE (γQ Q) (δQ Q) (eQ Q) κ (uz z 0) (uz z 2) (uz z 3)) fun z x ↦ by
                rw [uz_set_ne z (by norm_num), uz_set_ne z (by norm_num), uz_set_ne z (by norm_num)])))))))).trans
      (le_of_eq ?_)
    ring

/-- `W`'s point's bound: `42` single values and `3 |K|`. -/
noncomputable def εW : ℝ≥0∞ := 42 * κE + 3 * (2 ^ 64 * κE)

/-- **`W`'s point is good** for every `t` but with probability at most `εW`. -/
theorem prEvent_notGoodW (t : E) : Pr{let z ← iidE 24}[¬ GoodW t z] ≤ εW := by
  refine (prEvent_mono_of_support _ _ (fun z ↦ (∃ b : Fin 18, uz z (b.val + 6) = (pt (Hc / 2 ^ b.val))⁻¹) ∨
    (∃ Q : Fin 4, ¬ GoodH θE (γQ Q) (δQ Q) (eQ Q) (cK t Q) (uz z 0) (uz z 1) (uz z 2) (uz z 3)) ∨
    uz z 4 = (c4Q 0)⁻¹ ∨ (∃ l, uz z 4 = g4 (c4Q 0) (c4Q 1) (HQ t z 0) (HQ t z 1) l) ∨
    uz z 4 = (c4Q 2)⁻¹ ∨ (∃ l, uz z 4 = g4 (c4Q 2) (c4Q 3) (HQ t z 2) (HQ t z 3) l) ∨
    uz z 5 = (dQ 0)⁻¹ ∨ uz z 5 = (dQ 2)⁻¹ ∨
    ∃ l, uz z 5 = g5 (dQ 0) (dQ 2) (yQ t z 0) (yQ t z 1) (yQ t z 2) (yQ t z 3) l) fun z _ h ↦ ?_).trans ?_
  · unfold GoodW at h
    by_contra hn
    simp only [not_or, not_exists, not_not] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hn
    exact h ⟨fun b hb ↦ h1 ⟨b, hb⟩, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · have e1 : Pr{let z ← iidE 24}[∃ b : Fin 18, uz z (b.val + 6) = (pt (Hc / 2 ^ b.val))⁻¹] ≤ 18 * κE := by
      have := prEvent_exists_fin (iidE 24) 18 (fun b z ↦ uz z (b.val + 6) = (pt (Hc / 2 ^ b.val))⁻¹) κE
        fun b ↦ prEvent_hit1 (b.val + 6) (by omega) (fun _ ↦ _) fun _ _ ↦ rfl
      exact_mod_cast this
    have e2 : Pr{let z ← iidE 24}[∃ Q : Fin 4,
        ¬ GoodH θE (γQ Q) (δQ Q) (eQ Q) (cK t Q) (uz z 0) (uz z 1) (uz z 2) (uz z 3)] ≤ 4 * (5 * κE) := by
      have := prEvent_exists_fin (iidE 24) 4 (fun Q z ↦
        ¬ GoodH θE (γQ Q) (δQ Q) (eQ Q) (cK t Q) (uz z 0) (uz z 1) (uz z 2) (uz z 3)) (5 * κE)
        fun Q ↦ prEvent_notGoodH t Q
      exact_mod_cast this
    have g4i : ∀ Q0 Q1 : Fin 4, Pr{let z ← iidE 24}[∃ l, uz z 4 = g4 (c4Q Q0) (c4Q Q1) (HQ t z Q0) (HQ t z Q1) l]
        ≤ 2 ^ 64 * κE := fun Q0 Q1 ↦
      prEvent_hitK 4 (by norm_num) (fun l z ↦ g4 (c4Q Q0) (c4Q Q1) (HQ t z Q0) (HQ t z Q1) l) fun l z x ↦ by
        rw [HQ_set t z le_rfl, HQ_set t z le_rfl]
    have g5i : Pr{let z ← iidE 24}[∃ l, uz z 5 = g5 (dQ 0) (dQ 2) (yQ t z 0) (yQ t z 1) (yQ t z 2) (yQ t z 3) l]
        ≤ 2 ^ 64 * κE :=
      prEvent_hitK 5 (by norm_num) (fun l z ↦ g5 (dQ 0) (dQ 2) (yQ t z 0) (yQ t z 1) (yQ t z 2) (yQ t z 3) l)
        fun l z x ↦ by rw [yQ_set t z le_rfl, yQ_set t z le_rfl, yQ_set t z le_rfl, yQ_set t z le_rfl]
    have c1 : ∀ (b : ℕ) (hb : b < 24) (v : E), Pr{let z ← iidE 24}[uz z b = v] ≤ κE := fun b hb v ↦
      prEvent_hit1 b hb (fun _ ↦ v) fun _ _ ↦ rfl
    refine ((prEvent_or_le _ _ _).trans (add_le_add e1 ((prEvent_or_le _ _ _).trans (add_le_add e2
      ((prEvent_or_le _ _ _).trans (add_le_add (c1 4 (by norm_num) _) ((prEvent_or_le _ _ _).trans (add_le_add
      (g4i 0 1) ((prEvent_or_le _ _ _).trans (add_le_add (c1 4 (by norm_num) _) ((prEvent_or_le _ _ _).trans
      (add_le_add (g4i 2 3) ((prEvent_or_le _ _ _).trans (add_le_add (c1 5 (by norm_num) _)
      ((prEvent_or_le _ _ _).trans (add_le_add (c1 5 (by norm_num) _) g5i)))))))))))))))).trans (le_of_eq ?_)
    unfold εW
    ring

/-! ### The challenge `t` -/

/-- A uniform element lies in a finite set `S` with probability at most `|S| · 2^-192`. -/
theorem prEvent_eDist_finset (S : Finset E) : Pr{let x ← eDist}[x ∈ S] ≤ S.card * κE := by
  refine le_trans (prEvent_mono_of_support _ _ (fun x : E ↦ ∃ i : S, x = (i : E))
    fun x _ hx ↦ ⟨⟨x, hx⟩, rfl⟩) ?_
  have := prEvent_eDist_exists (fun i : S ↦ (i : E))
  rwa [Fintype.card_coe] at this

/-- The roots of a family of polynomials indexed by `K` (irreducible: `K`'s `univ` is never unfolded). -/
@[irreducible] noncomputable def rootSet (P : K → Polynomial E) : Finset E :=
  Finset.univ.biUnion fun a : K ↦ (P a).roots.toFinset

theorem mem_rootSet (P : K → Polynomial E) {a : K} {t : E} (hP : P a ≠ 0) (h : (P a).eval t = 0) :
    t ∈ rootSet P := by
  unfold rootSet
  rw [Finset.mem_biUnion]
  refine ⟨a, Finset.mem_univ _, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
  exact h

theorem card_rootSet (P : K → Polynomial E) (d : ℕ) (hd : ∀ a, (P a).natDegree ≤ d) :
    (rootSet P).card ≤ 2 ^ 64 * d := by
  unfold rootSet
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ a, ((P a).roots.toFinset).card ≤ ∑ _a : K, d :=
        Finset.sum_le_sum fun a _ ↦ (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (hd a))
    _ = 2 ^ 64 * d := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, BF64.card_bf64]

/-- **`f(t) ∈ K` at a uniform `t`**, where `f(t) = a ∈ K` makes `t` a root of a nonzero polynomial of degree at most
`d`: probability at most `d |K| 2^-192`. -/
theorem prEvent_inK_poly (f : E → E) (d : ℕ) (P : K → Polynomial E) (hP : ∀ a, P a ≠ 0)
    (hd : ∀ a, (P a).natDegree ≤ d) (hroot : ∀ t a, f t = ofK a → (P a).eval t = 0) :
    Pr{let t ← eDist}[InK (f t)] ≤ d * 2 ^ 64 * κE := by
  refine (prEvent_mono_of_support _ _ (· ∈ rootSet P) fun t _ ht ↦ ?_).trans
    ((prEvent_eDist_finset (rootSet P)).trans ?_)
  · obtain ⟨a, ha⟩ := ht
    exact mem_rootSet P (hP a) (hroot t a ha)
  · have hcard := card_rootSet P d hd
    calc ((rootSet P).card : ℝ≥0∞) * κE ≤ ((2 ^ 64 * d : ℕ) : ℝ≥0∞) * κE := by
          gcongr
      _ = d * 2 ^ 64 * κE := by push_cast; ring

/-- **`w₂(t) ∈ K`** at a uniform `t`: at most `4 |K| 2^-192`. -/
theorem prEvent_T2 : Pr{let t ← eDist}[InK (sq^[2] t)] ≤ 4 * 2 ^ 64 * κE := by
  have h := prEvent_inK_poly (fun t ↦ sq^[2] t) 4
    (fun a ↦ Polynomial.X ^ 4 + Polynomial.X - Polynomial.C (ofK a)) (fun a ↦ ?_) (fun a ↦ ?_) fun t a ha ↦ ?_
  · exact_mod_cast h
  · have hm : (Polynomial.X ^ 4 + Polynomial.X - Polynomial.C (ofK a) : Polynomial E).Monic := by monicity!
    exact hm.ne_zero
  · compute_degree!
  · simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]
    rw [← ha]
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, QuotientSecurity.sq]
    linear_combination (-(t * t * t) - t * t) * two_E

/-- **`t² + θ t ∈ K`** at a uniform `t`: at most `2 |K| 2^-192`. -/
theorem prEvent_Z1 : Pr{let t ← eDist}[InK (t * t + θE * t)] ≤ 2 * 2 ^ 64 * κE := by
  have h := prEvent_inK_poly (fun t ↦ t * t + θE * t) 2
    (fun a ↦ Polynomial.X ^ 2 + Polynomial.C θE * Polynomial.X - Polynomial.C (ofK a)) (fun a ↦ ?_) (fun a ↦ ?_)
    fun t a ha ↦ ?_
  · exact_mod_cast h
  · have hm : (Polynomial.X ^ 2 + Polynomial.C θE * Polynomial.X - Polynomial.C (ofK a) : Polynomial E).Monic := by
      monicity!
    exact hm.ne_zero
  · compute_degree!
  · simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_mul]
    rw [← ha]; ring

/-! ### The challenges -/

theorem zW_length_of_mem {c : Challenges} (hc : c ∈ support sampleChallenges) : c.zW.length = 24 := by
  rw [sampleChallenges_eq] at hc
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hc
  obtain ⟨zW, hzW, α, -, β, -, μ, -, zT, -, t, -, ρ, -, rfl⟩ := hc
  exact length_of_mem_iidE _ _ hzW

/-- **`W`'s point and `t`**: independent, `t` drawn first. -/
theorem zWt_dist : (sampleChallenges >>= fun c ↦ (pure (c.zW, c.t) : ProbComp (List E × E))) =ᵈ
    (eDist >>= fun t ↦ iidE 24 >>= fun z ↦ (pure (z, t) : ProbComp (List E × E))) := by
  rw [sampleChallenges_eq]
  simp only [bind_assoc, pure_bind]
  refine EvalDistEq.trans ?_
    (OracleComp.EvalDistEq.bind_bind_swap (iidE 24) eDist fun z t ↦ (pure (z, t) : ProbComp (List E × E)))
  refine EvalDistEq.bind_right _ fun zW ↦ ?_
  exact (evalDistEq_bind_drop _ _).trans ((evalDistEq_bind_drop _ _).trans ((evalDistEq_bind_drop _ _).trans
    ((evalDistEq_bind_drop _ _).trans (EvalDistEq.bind_right _ fun t ↦ evalDistEq_bind_drop _ _))))

/-- **Group 1's failure bound**: `(9 · 2^64 + 42) · 2^-192` (`εgroup1_le`: at most `2^-124`). -/
noncomputable def εgroup1 : ℝ≥0∞ := (9 * 2 ^ 64 + 42) * κE

/-- **The good event fails** with probability at most `εgroup1`. -/
theorem prEvent_notGood : Pr{let c ← sampleChallenges}[¬ Good c.t c.zW] ≤ εgroup1 := by
  have h1 : Pr{let c ← sampleChallenges}[¬ Good c.t c.zW] =
      Pr{let p ← (eDist >>= fun t ↦ iidE 24 >>= fun z ↦ (pure (z, t) : ProbComp (List E × E)))}[¬ Good p.2 p.1] := by
    rw [← zWt_dist.prEvent_eq (fun p ↦ ¬ Good p.2 p.1), prEvent_bind_pure]
  rw [h1]
  have hT : ∀ Q : E → Prop, Pr{let p ← (eDist >>= fun t ↦ iidE 24 >>= fun z ↦
      (pure (z, t) : ProbComp (List E × E)))}[Q p.2] = Pr{let t ← eDist}[Q t] := fun Q ↦ by
    rw [← prEvent_map (eDist >>= fun t ↦ iidE 24 >>= fun z ↦ (pure (z, t) : ProbComp (List E × E)))
      (fun p : List E × E ↦ p.2) Q]
    refine EvalDistEq.prEvent_eq ?_ Q
    simp only [map_bind, map_pure]
    have h := EvalDistEq.bind_right eDist fun t ↦ evalDistEq_bind_drop (iidE 24) (pure t : ProbComp E)
    rwa [bind_pure] at h
  have hW : Pr{let p ← (eDist >>= fun t ↦ iidE 24 >>= fun z ↦
      (pure (z, t) : ProbComp (List E × E)))}[¬ GoodW p.2 p.1] ≤ εW :=
    prEvent_bind_le_of_forall_le _ _ _ fun t ↦ by rw [prEvent_bind_pure]; exact prEvent_notGoodW t
  refine (prEvent_mono_of_support _ _ (fun p : List E × E ↦
    InK (sq^[2] p.2) ∨ InK (p.2 * p.2 + θE * p.2) ∨ ¬ GoodW p.2 p.1) fun p _ h ↦ ?_).trans ?_
  · unfold Good at h
    by_contra hn
    push Not at hn
    exact h hn
  · refine ((prEvent_or_le _ _ _).trans (add_le_add (le_of_eq (hT fun t ↦ InK (sq^[2] t)))
      ((prEvent_or_le _ _ _).trans (add_le_add (le_of_eq (hT fun t ↦ InK (t * t + θE * t))) hW)))).trans ?_
    refine (add_le_add prEvent_T2 (add_le_add prEvent_Z1 le_rfl)).trans (le_of_eq ?_)
    unfold εgroup1 εW
    ring

/-- **`εgroup1 ≤ 2^-124`.** -/
theorem εgroup1_le : εgroup1 ≤ ((2 : ℝ≥0∞) ^ 124)⁻¹ := by
  have hk : κE = ((2 : ℝ≥0∞) ^ 192)⁻¹ := pmax_eq
  have hc : (2 : ℝ≥0∞) ^ 68 * ((2 : ℝ≥0∞) ^ (68 + 124))⁻¹ = ((2 : ℝ≥0∞) ^ 124)⁻¹ := by
    rw [pow_add, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp),
      one_mul]
  have hn : (9 * 2 ^ 64 + 42 : ℝ≥0∞) ≤ 2 ^ 68 := by
    have : (9 * 2 ^ 64 + 42 : ℕ) ≤ 2 ^ 68 := by norm_num
    exact_mod_cast this
  unfold εgroup1
  rw [hk, ← hc]
  exact mul_le_mul' hn le_rfl

/-- **Group 1 is uniform at all but `εgroup1` of the challenges**: `Group1Uniform` proved. -/
theorem group1Uniform : Group1Uniform εgroup1 := by
  intro stmt w _
  have hc := E2ECompleteness.Pcs.cellsOf_size w
  unfold E2ECompleteness.Pcs.cellsOf at hc
  have hG : ∀ c ∈ support sampleChallenges, Good c.t c.zW →
      Group1At stmt ((membership logRows).cells (membershipInputs w)) c := fun c hc' hg ↦
    group1At_of_surj stmt _ hc c (zW_length_of_mem hc') (onto_of_good hg)
  exact (prEvent_mono_of_support _ _ _ fun c hc' hn hg ↦ hn (hG c hc' hg)).trans prEvent_notGood

end PcsQuotient.EndToEnd.Group1

namespace PcsQuotient.EndToEnd

/-- **Zero knowledge of the membership proof over any zero-knowledge PCS, with `PcsZeroKnowledge` its only
hypothesis**: for every PCS `pcs` and PCS simulator `sim` with `PcsZeroKnowledge pcs sim εpcs`, the simulator
`zkSimulator sim` is within `εpcs Q + εgroup1 + εslack + εfs₀` of the honest prover over `pcs`, `εgroup1 ≤ 2^-124`
(`Group1.εgroup1_le`), `εslack ≤ 2^-126`, `εfs₀ ≤ 2^-163`. -/
theorem zeroKnowledge_of_pcs {Hd : Type} (pcs : PcsOps (OracleComp RandomPermutationOracles) Hd)
    (sim : PcsSimulator) (εpcs : ℕ → ℝ≥0∞) (hpcs : PcsZeroKnowledge pcs sim εpcs) :
    ZeroKnowledgeWith pcs sim.s₀ (zkSimulator sim) sim.oracle
      (fun Q ↦ εpcs Q + Group1.εgroup1 + εslack + εfs₀) :=
  zeroKnowledge_pcs_slack pcs sim εpcs Group1.εgroup1 hpcs Group1.group1Uniform

/-- **Zero knowledge of the protocol over the model's ideal PCS**, with no hypothesis: within
`εgroup1 + εslack + εfs₀`. -/
theorem zeroKnowledge_ideal
    (simO : Commitment → Claim → OracleComp RandomPermutationOracles (Option Compile.Proof)) :
    ZeroKnowledgeWith (PcsOps.idealOf simO) (PcsSimulator.ofOpen simO).s₀ (zkSimulator (PcsSimulator.ofOpen simO))
      (PcsSimulator.ofOpen simO).oracle (fun _ ↦ Group1.εgroup1 + εslack + εfs₀) :=
  PcsParam.zeroKnowledge_idealOf simO Group1.εgroup1 Group1.group1Uniform

end PcsQuotient.EndToEnd
