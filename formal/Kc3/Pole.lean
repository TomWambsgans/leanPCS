-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The pole lemma of `docs/membership/PROTOCOL.md` ("Soundness", "The pole lemma"), in the style of
-- `formal/QuotientSecurity/LogDerivative.lean` (adapted from leanVM, branch PCS-openings-aggregation, commit
-- 651453c6), whose `beta_eq_of_pole_eq` it uses.
import QuotientSecurity.Counting

/-!
# The pole lemma

Cells `ι` carry values `w`, distinct labels `id` and errors `e`, and `σ` permutes the cells. With
`d x = α + w x + β id x` and `d' x = α + w x + β id (σ x)`, the sum on the cells of the copy argument's
`1 / d + 1 / d'` plus `μ e / (d d')` is `L(α, β) + μ B(α, β)`, `B = Σ_x e x / (d x d' x)`. **If an error cell
`x₀` has no error at its predecessor on its cycle** (or is a lone cell), then at most `(4 N + 1) q²` triples
`(α, β, μ)` with no vanishing denominator make the sum zero, whatever `L` is (`card_pole_le`).

For `β` outside `2 |S|` values (`errBetas`, `S` the error cells), the pole of `1 / d x₀` (`α = w x₀ + β id x₀`)
is the pole of no other term with an error: another first term would need the same label (another `β`), a
second term `d' z` the label `id (σ z) = id x₀`, so `z` is `x₀`'s predecessor, whose error is zero. So the
cleared numerator `N(α) = Σ_{x ∈ S} e x Π_{z ∈ S ∖ x} d z d' z` is nonzero at `α = w x₀ + β id x₀`
(`errPoly_ne_zero`), and a nonzero polynomial of degree at most `2 N` in `α`; where it does not vanish, `B ≠ 0`
fixes `μ`.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial

namespace Kc3

open QuotientSecurity

variable {F : Type*} [Field F] [CharP F 2] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The error cells. -/
def errCells (e : ι → F) : Finset ι := univ.filter fun x => e x ≠ 0

/-- **The cleared numerator** of `B` as a polynomial in `α`, at `β`: `Σ_{x ∈ S} e x Π_{z ∈ S ∖ x}
(X + a z)(X + b z)`, `a z = w z + β id z`, `b z = w z + β id (σ z)`. -/
noncomputable def errPoly (id : ι → F) (σ : Equiv.Perm ι) (w e : ι → F) (β : F) : F[X] :=
  ∑ x ∈ errCells e, C (e x) * ∏ z ∈ (errCells e).erase x,
    ((X + C (w z + β * id z)) * (X + C (w z + β * id (σ z))))

theorem natDegree_prod_quad_le (s : Finset ι) (a b : ι → F) :
    (∏ z ∈ s, ((X + C (a z)) * (X + C (b z)))).natDegree ≤ 2 * s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert z s hz ih =>
    rw [Finset.prod_insert hz, Finset.card_insert_of_notMem hz]
    refine natDegree_mul_le.trans ?_
    have h := natDegree_mul_le (p := X + C (a z)) (q := X + C (b z))
    rw [natDegree_X_add_C, natDegree_X_add_C] at h
    omega

theorem natDegree_errPoly_le (id : ι → F) (σ : Equiv.Perm ι) (w e : ι → F) (β : F) :
    (errPoly id σ w e β).natDegree ≤ 2 * Fintype.card ι := by
  unfold errPoly
  refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_C, zero_add]
  have hcard : ((errCells e).erase x).card ≤ Fintype.card ι :=
    le_trans Finset.card_erase_le (Finset.card_le_univ _)
  have := natDegree_prod_quad_le ((errCells e).erase x) (fun z => w z + β * id z)
    (fun z => w z + β * id (σ z))
  omega

/-- Where no denominator vanishes, the cleared numerator is the product of the error cells' denominators times
`B`. -/
theorem eval_errPoly (id : ι → F) (σ : Equiv.Perm ι) (w e : ι → F) (α β : F)
    (hd : ∀ x, α + w x + β * id x ≠ 0) (hd' : ∀ x, α + w x + β * id (σ x) ≠ 0) :
    (errPoly id σ w e β).eval α =
      (∏ z ∈ errCells e, ((α + w z + β * id z) * (α + w z + β * id (σ z)))) *
        ∑ x, e x * ((α + w x + β * id x) * (α + w x + β * id (σ x)))⁻¹ := by
  have hden : ∀ x, (α + w x + β * id x) * (α + w x + β * id (σ x)) ≠ 0 := fun x =>
    mul_ne_zero (hd x) (hd' x)
  have hsum : ∑ x, e x * ((α + w x + β * id x) * (α + w x + β * id (σ x)))⁻¹ =
      ∑ x ∈ errCells e, e x * ((α + w x + β * id x) * (α + w x + β * id (σ x)))⁻¹ := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
    simp only [errCells, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
    rw [hx, zero_mul]
  rw [hsum, Finset.mul_sum]
  unfold errPoly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finset.mul_prod_erase _ _ hx]
  simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X, ← add_assoc]
  set D := (α + w x + β * id x) * (α + w x + β * id (σ x))
  set P' := ∏ z ∈ (errCells e).erase x, ((α + w z + β * id z) * (α + w z + β * id (σ z)))
  calc e x * P' = e x * P' * (D * D⁻¹) := by rw [mul_inv_cancel₀ (hden x), mul_one]
    _ = D * P' * (e x * D⁻¹) := by ring

/-- **The bad `β`** for the error cell `x₀`: where the pole of `1 / d x₀` meets the pole of another error
cell's first term, or of an error cell's second term whose label is not `x₀`'s. -/
noncomputable def errBetas (id : ι → F) (σ : Equiv.Perm ι) (w e : ι → F) (x₀ : ι) : Finset F :=
  ((errCells e).erase x₀).image (fun z => (w x₀ + w z) / (id x₀ + id z)) ∪
    ((errCells e).erase x₀).image (fun z => (w x₀ + w z) / (id x₀ + id (σ z)))

theorem card_errBetas_le (id : ι → F) (σ : Equiv.Perm ι) (w e : ι → F) (x₀ : ι) :
    (errBetas id σ w e x₀).card ≤ 2 * Fintype.card ι := by
  unfold errBetas
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := (errCells e).erase x₀)
    (f := fun z => (w x₀ + w z) / (id x₀ + id z))
  have h2 := Finset.card_image_le (s := (errCells e).erase x₀)
    (f := fun z => (w x₀ + w z) / (id x₀ + id (σ z)))
  have h3 : ((errCells e).erase x₀).card ≤ Fintype.card ι :=
    le_trans Finset.card_erase_le (Finset.card_le_univ _)
  omega

/-- **The pole of an error cell whose predecessor has no error is simple**: away from `errBetas`, the cleared
numerator does not vanish at `α = w x₀ + β id x₀`. -/
theorem errPoly_ne_zero (id : ι → F) (hid : Function.Injective id) (σ : Equiv.Perm ι) (w e : ι → F)
    (x₀ : ι) (he : e x₀ ≠ 0) (hpred : σ.symm x₀ = x₀ ∨ e (σ.symm x₀) = 0) {β : F}
    (hβ : β ∉ errBetas id σ w e x₀) : errPoly id σ w e β ≠ 0 := by
  intro h
  have hx₀ : x₀ ∈ errCells e := by simp [errCells, he]
  set a₀ := w x₀ + β * id x₀ with ha₀
  have hev : (errPoly id σ w e β).eval a₀ = 0 := by rw [h]; simp
  unfold errPoly at hev
  rw [eval_finsetSum, Finset.sum_eq_single x₀] at hev
  · simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X] at hev
    rcases mul_eq_zero.mp hev with h1 | h1
    · exact he h1
    · obtain ⟨z, hz, hz0⟩ := Finset.prod_eq_zero_iff.mp h1
      have hzx : z ≠ x₀ := (Finset.mem_erase.mp hz).1
      simp only [errBetas, Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and] at hβ
      rcases mul_eq_zero.mp hz0 with h2 | h2
      · have hpole : w x₀ + β * id x₀ = w z + β * id z := CharTwo.add_eq_zero.mp h2
        refine hβ.1 z hz ?_
        exact (beta_eq_of_pole_eq hpole fun h' => hzx (hid h').symm).symm
      · have hpole : w x₀ + β * id x₀ = w z + β * id (σ z) := CharTwo.add_eq_zero.mp h2
        by_cases hσz : σ z = x₀
        · have hzp : z = σ.symm x₀ := by rw [← hσz, Equiv.symm_apply_apply]
          rcases hpred with hp | hp
          · exact hzx (hzp.trans hp)
          · have hzS := (Finset.mem_erase.mp hz).2
            simp only [errCells, Finset.mem_filter, Finset.mem_univ, true_and] at hzS
            exact hzS (hzp ▸ hp)
        · refine hβ.2 z hz ?_
          exact (beta_eq_of_pole_eq hpole fun h' => hσz (hid h').symm).symm
  · intro x hx hxx
    have : (∏ z ∈ (errCells e).erase x,
        ((X + C (w z + β * id z)) * (X + C (w z + β * id (σ z))))).eval a₀ = 0 := by
      rw [eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hxx h.symm, hx₀⟩) ?_
      simp only [eval_mul, eval_add, eval_X, eval_C, ha₀, CharTwo.add_self_eq_zero, zero_mul]
    rw [eval_mul, this, mul_zero]
  · intro h; exact absurd hx₀ h

variable [Fintype F]

/-- **The pole lemma.** If the error cell `x₀` has no error at its predecessor (or is a lone cell), then at most
`(4 N + 1) q²` triples `(α, β, μ)` have no vanishing denominator and `L(α, β) + μ B(α, β) = 0`, for any `L`. -/
theorem card_pole_le (id : ι → F) (hid : Function.Injective id) (σ : Equiv.Perm ι) (w e : ι → F)
    (x₀ : ι) (he : e x₀ ≠ 0) (hpred : σ.symm x₀ = x₀ ∨ e (σ.symm x₀) = 0) (L : F → F → F) :
    (univ.filter fun p : F × F × F =>
        (∀ x, p.1 + w x + p.2.1 * id x ≠ 0 ∧ p.1 + w x + p.2.1 * id (σ x) ≠ 0) ∧
          L p.1 p.2.1 + p.2.2 * ∑ x, e x * ((p.1 + w x + p.2.1 * id x) *
            (p.1 + w x + p.2.1 * id (σ x)))⁻¹ = 0).card
      ≤ (4 * Fintype.card ι + 1) * Fintype.card F ^ 2 := by
  classical
  set q := Fintype.card F
  set N := Fintype.card ι
  set A := univ.filter fun p : F × F × F =>
    (∀ x, p.1 + w x + p.2.1 * id x ≠ 0 ∧ p.1 + w x + p.2.1 * id (σ x) ≠ 0) ∧
      L p.1 p.2.1 + p.2.2 * ∑ x, e x * ((p.1 + w x + p.2.1 * id x) *
        (p.1 + w x + p.2.1 * id (σ x)))⁻¹ = 0 with hA
  -- The pairs `(α, β)` at which the cleared numerator vanishes.
  set Pz := univ.filter fun p : F × F => (errPoly id σ w e p.2).eval p.1 = 0 with hPzDef
  have hPz : Pz.card ≤ 4 * N * q := by
    have hsplit : Pz.card = ∑ β : F, (Pz.filter fun p => p.2 = β).card :=
      Finset.card_eq_sum_card_fiberwise (f := fun p : F × F => p.2) (t := univ)
        fun _ _ => Finset.mem_univ _
    have hall : ∀ β : F, (Pz.filter fun p => p.2 = β).card ≤ q := by
      intro β
      have : (Pz.filter fun p => p.2 = β).card ≤ (univ.image fun α : F => (α, β)).card := by
        refine Finset.card_le_card fun p hp => ?_
        rw [Finset.mem_filter] at hp
        exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, by rw [← hp.2]⟩
      exact this.trans (Finset.card_image_le.trans (by simp [q]))
    have hgood : ∀ β : F, β ∉ errBetas id σ w e x₀ → (Pz.filter fun p => p.2 = β).card ≤ 2 * N := by
      intro β hβ
      have h0 := errPoly_ne_zero id hid σ w e x₀ he hpred hβ
      have hsub : (Pz.filter fun p => p.2 = β) ⊆
          (errPoly id σ w e β).roots.toFinset.image fun α : F => (α, β) := by
        intro p hp
        rw [Finset.mem_filter, hPzDef, Finset.mem_filter] at hp
        obtain ⟨⟨-, hev⟩, rfl⟩ := hp
        refine Finset.mem_image.mpr ⟨p.1, ?_, rfl⟩
        rw [Multiset.mem_toFinset, mem_roots h0, IsRoot.def]
        exact hev
      calc (Pz.filter fun p => p.2 = β).card
          ≤ ((errPoly id σ w e β).roots.toFinset.image fun α : F => (α, β)).card :=
            Finset.card_le_card hsub
        _ ≤ (errPoly id σ w e β).roots.toFinset.card := Finset.card_image_le
        _ ≤ Multiset.card (errPoly id σ w e β).roots := Multiset.toFinset_card_le _
        _ ≤ (errPoly id σ w e β).natDegree := card_roots' _
        _ ≤ 2 * N := natDegree_errPoly_le _ _ _ _ _
    rw [hsplit]
    calc ∑ β : F, (Pz.filter fun p => p.2 = β).card
        ≤ ∑ β : F, (if β ∈ errBetas id σ w e x₀ then q else 2 * N) :=
          Finset.sum_le_sum fun β _ => by
            split_ifs with h
            · exact hall β
            · exact hgood β h
      _ = (errBetas id σ w e x₀).card * q +
            (univ.filter fun β => β ∉ errBetas id σ w e x₀).card * (2 * N) := by
          have hmem : (univ.filter fun β => β ∈ errBetas id σ w e x₀) = errBetas id σ w e x₀ := by
            ext β; simp
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, hmem]
      _ ≤ (2 * N) * q + q * (2 * N) := by
          gcongr
          · exact card_errBetas_le id σ w e x₀
          · exact Finset.card_le_univ _
      _ = 4 * N * q := by ring
  -- The triples split: the cleared numerator vanishes, or `μ` is fixed by `(α, β)`.
  set A1 := A.filter fun p => (errPoly id σ w e p.2.1).eval p.1 = 0
  set A2 := A.filter fun p => (errPoly id σ w e p.2.1).eval p.1 ≠ 0
  have hA12 : A.card = A1.card + A2.card := (Finset.card_filter_add_card_filter_not _).symm
  have hA1 : A1.card ≤ 4 * N * q * q := by
    have hsub : A1 ⊆ (Pz ×ˢ (univ : Finset F)).image fun r : (F × F) × F => (r.1.1, r.1.2, r.2) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      refine Finset.mem_image.mpr ⟨((p.1, p.2.1), p.2.2), ?_, rfl⟩
      rw [Finset.mem_product, hPzDef, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, hp.2⟩, Finset.mem_univ _⟩
    calc A1.card ≤ _ := Finset.card_le_card hsub
      _ ≤ (Pz ×ˢ (univ : Finset F)).card := Finset.card_image_le
      _ = Pz.card * q := by rw [Finset.card_product, Finset.card_univ]
      _ ≤ 4 * N * q * q := Nat.mul_le_mul_right _ hPz
  have hA2 : A2.card ≤ q ^ 2 := by
    have hinj : Set.InjOn (fun p : F × F × F => (p.1, p.2.1)) (A2 : Set (F × F × F)) := by
      rintro ⟨α, β, μ⟩ hp ⟨α', β', μ'⟩ hp' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [Finset.mem_coe, Finset.mem_filter, hA, Finset.mem_filter] at hp hp'
      obtain ⟨⟨-, hd, hsum⟩, hN0⟩ := hp
      obtain ⟨⟨-, -, hsum'⟩, -⟩ := hp'
      rw [eval_errPoly id σ w e α β (fun x => (hd x).1) (fun x => (hd x).2)] at hN0
      have hB := right_ne_zero_of_mul hN0
      have h1 := CharTwo.add_eq_zero.mp hsum
      have h2 := CharTwo.add_eq_zero.mp hsum'
      simp only [Prod.mk.injEq, true_and]
      exact mul_right_cancel₀ hB (h1.symm.trans h2)
    calc A2.card = (A2.image fun p : F × F × F => (p.1, p.2.1)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (univ : Finset (F × F)).card := Finset.card_le_univ _
      _ = q ^ 2 := by rw [Finset.card_univ, Fintype.card_prod]; ring
  rw [hA12]
  calc A1.card + A2.card ≤ 4 * N * q * q + q ^ 2 := Nat.add_le_add hA1 hA2
    _ = (4 * N + 1) * q ^ 2 := by ring

/-- **The first challenge's count, generically.** `A` the triples to count: outside those where a cell's
denominator vanishes and a set `Z1` of at most `2 q²`, each has no vanishing denominator and makes the sum
`L + μ B` zero (`L` the copy argument's); if no error sits anywhere a copy fails; an error sits on an error cell
(`E`); and every cycle but a lone cell's holds a cell no error can sit on. Then `A` has at most `8 N q²` triples. -/
theorem card_round1_core (id : ι → F) (hid : Function.Injective id) (σ : Equiv.Perm ι) (w e : ι → F)
    (A Z1 : Finset (F × F × F)) (hZ1 : Z1.card ≤ 2 * Fintype.card F ^ 2)
    (hgood : ∀ p ∈ A,
      p ∉ (univ.filter fun p : F × F × F =>
        ∃ i, p.1 + w i + p.2.1 * id i = 0 ∨ p.1 + w i + p.2.1 * id (σ i) = 0) → p ∉ Z1 →
      (∀ i, p.1 + w i + p.2.1 * id i ≠ 0 ∧ p.1 + w i + p.2.1 * id (σ i) ≠ 0) ∧
        logSum id σ w p.1 p.2.1 + p.2.2 * ∑ i, e i * ((p.1 + w i + p.2.1 * id i) *
          (p.1 + w i + p.2.1 * id (σ i)))⁻¹ = 0)
    (hcopy : (∀ i, e i = 0) → ¬ ∀ x, w (σ x) = w x)
    {E : ι → Prop} (hE : ∀ i, e i ≠ 0 → E i) (hpole : ∀ i, σ i ≠ i → ∃ k : ℕ, ¬ E ((σ ^ k) i))
    (hN2 : 2 ≤ Fintype.card ι) :
    A.card ≤ 8 * Fintype.card ι * Fintype.card F ^ 2 := by
  classical
  set q := Fintype.card F
  set N := Fintype.card ι
  set Z0 := univ.filter fun p : F × F × F =>
    ∃ i, p.1 + w i + p.2.1 * id i = 0 ∨ p.1 + w i + p.2.1 * id (σ i) = 0
  have hZ0c : Z0.card ≤ 2 * N * q ^ 2 := card_zero_le id σ w
  by_cases he : ∀ i, e i = 0
  · have hc := hcopy he
    have hN : 1 ≤ N := by omega
    set S := univ.filter fun p : F × F × F =>
      (∀ x, p.1 + w x + p.2.1 * id x = 0 ↔ p.1 + w x + p.2.1 * id (σ x) = 0) ∧
        ((∀ x, p.1 + w x + p.2.1 * id x ≠ 0) → logSum id σ w p.1 p.2.1 = (fun _ => (0 : F)) p.2.2) with hS
    have hSc : S.card ≤ (4 * N - 2) * q ^ 2 := by
      convert card_copy_triple_le id hid σ w hc (fun _ => (0 : F))
    have hsub : A ⊆ Z0 ∪ Z1 ∪ S := by
      intro p hp
      by_cases h0 : p ∈ Z0
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h0)
      by_cases h1 : p ∈ Z1
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
      refine Finset.mem_union_right _ ?_
      obtain ⟨hd, hs⟩ := hgood p hp h0 h1
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun x => ⟨fun h => absurd h (hd x).1, fun h => absurd h (hd x).2⟩,
        fun _ => ?_⟩
      simpa [he] using hs
    calc A.card ≤ (Z0 ∪ Z1 ∪ S).card := Finset.card_le_card hsub
      _ ≤ Z0.card + Z1.card + S.card := (Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      _ ≤ 2 * N * q ^ 2 + 2 * q ^ 2 + (4 * N - 2) * q ^ 2 := by gcongr
      _ ≤ 8 * N * q ^ 2 := by
          have : 2 * N * q ^ 2 + 2 * q ^ 2 + (4 * N - 2) * q ^ 2 = 6 * N * q ^ 2 := by
            obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hN
            rw [hk, show 4 * (k + 1) - 2 = 4 * k + 2 by omega]
            ring
          rw [this]
          gcongr
          omega
  · push Not at he
    obtain ⟨x₀, hx₀, hpred⟩ : ∃ x₀, e x₀ ≠ 0 ∧ (σ.symm x₀ = x₀ ∨ e (σ.symm x₀) = 0) := by
      by_contra hno
      push Not at hno
      obtain ⟨i, hi⟩ := he
      have hback : ∀ m : ℕ, e ((σ⁻¹ ^ m) i) ≠ 0 := by
        intro m
        induction m with
        | zero => simpa using hi
        | succ m ih =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          exact (hno _ ih).2
      have hfix : σ i ≠ i := by
        intro h
        apply (hno i hi).1
        rw [Equiv.symm_apply_eq]
        exact h.symm
      obtain ⟨k, hk⟩ := hpole i hfix
      apply hk
      have hord : σ ^ orderOf σ = 1 := pow_orderOf_eq_one _
      have hpos : 0 < orderOf σ := orderOf_pos _
      have hpow : σ ^ k = σ⁻¹ ^ ((orderOf σ - 1) * k) := by
        rw [inv_pow, eq_inv_iff_mul_eq_one, ← pow_add]
        obtain ⟨o, ho⟩ := Nat.exists_eq_add_of_le' hpos
        rw [show k + (orderOf σ - 1) * k = orderOf σ * k by rw [ho, show o + 1 - 1 = o by omega]; ring,
          pow_mul, hord, one_pow]
      rw [hpow]
      exact hE _ (hback _)
    have hN : 1 ≤ N := Fintype.card_pos_iff.mpr ⟨x₀⟩
    set S := univ.filter fun p : F × F × F =>
      (∀ x, p.1 + w x + p.2.1 * id x ≠ 0 ∧ p.1 + w x + p.2.1 * id (σ x) ≠ 0) ∧
        logSum id σ w p.1 p.2.1 + p.2.2 * ∑ x, e x * ((p.1 + w x + p.2.1 * id x) *
          (p.1 + w x + p.2.1 * id (σ x)))⁻¹ = 0 with hS
    have hSc : S.card ≤ (4 * N + 1) * q ^ 2 := card_pole_le id hid σ w e x₀ hx₀ hpred (logSum id σ w)
    have hsub : A ⊆ Z0 ∪ Z1 ∪ S := by
      intro p hp
      by_cases h0 : p ∈ Z0
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h0)
      by_cases h1 : p ∈ Z1
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h1)
      refine Finset.mem_union_right _ ?_
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hgood p hp h0 h1⟩
    calc A.card ≤ (Z0 ∪ Z1 ∪ S).card := Finset.card_le_card hsub
      _ ≤ Z0.card + Z1.card + S.card := (Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      _ ≤ 2 * N * q ^ 2 + 2 * q ^ 2 + (4 * N + 1) * q ^ 2 := by gcongr
      _ ≤ 8 * N * q ^ 2 := by
          have : 2 * N * q ^ 2 + 2 * q ^ 2 + (4 * N + 1) * q ^ 2 = (6 * N + 3) * q ^ 2 := by ring
          rw [this]
          gcongr
          omega

end Kc3
