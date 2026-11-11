-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsSlack

/-!
# The slack's span failure, bounded

The slack's weights at `T`'s out-of-domain point `z` (`slackWeight`) are a common factor `C(z)` times the four
monomials `(1+z₀)(1+z₁)(1+z₂)`, `z₀(1+z₁)(1+z₂)`, `(1+z₀)z₁(1+z₂)`, `(1+z₀)(1+z₁)z₂` (`weight_closed`), the slack
sitting at coefficients `0, 1, 2, 4` of limbs `0`, `1`, `3`:
`C(z) = Π_{3 ≤ j < 25}(1+z_j) · (1+z₂₇) · (1 + z₂₆(1+z₂₅))`.
Divided by `(1+z₀)(1+z₁)(1+z₂)` they are `1, u₀, u₁, u₂`, `u_j = z_j/(1+z_j)`, so they span `E` over `K` as soon as
`C(z) ≠ 0`, `u₀ ∉ K` and `u₁` or `u₂` lies outside `K + K·u₀` (`span3`, `E` being `K³`): `slackSpan_of`. Each of these
fails at a uniform point with small probability, the coordinates of `z` being independent and uniform:

**`spanFail_le`**: `spanFail ≤ εslack = 27 · 2^-192 + 2^64 · 2^-192 + (2^128 · 2^-192)²`, and `εslack ≤ 2^-126`
(`εslack_le`; `2^-127 + 27 · 2^-192` exactly).

**`zeroKnowledge_pcs_slack`**: zero knowledge from the PCS hypothesis and `Group1Uniform ε1` alone, within
`εpcs Q + ε1 + εslack + εfs₀`.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open PcsQuotient.Transcript PcsQuotient.Domain
open scoped ENNReal

namespace PcsQuotient.EndToEnd

/-! ### The equality kernel at a cube point, as a product -/

/-- Coordinate `j` of a point. -/
abbrev xc (z : List E) (j : ℕ) : E := z.getD j 0

/-- Factor `j` of the equality kernel at the cube point `w`. -/
def fz (z : List E) (w j : ℕ) : E := if w.testBit j then xc z j else 1 + xc z j

theorem fz_t {z : List E} {w j : ℕ} (h : w.testBit j = true) : fz z w j = xc z j := by simp [fz, h]

theorem fz_f {z : List E} {w j : ℕ} (h : w.testBit j = false) : fz z w j = 1 + xc z j := by simp [fz, h]

theorem eqEval_boolPoint_prod : ∀ (V w : ℕ) (z : List E), z.length = V →
    eqEval (boolPoint V w) z = ∏ j ∈ Finset.range V, fz z w j
  | 0, w, z, hz => by
    rw [List.length_eq_zero_iff.1 hz,
      List.length_eq_zero_iff.1 (LeanVM.Protocol.Whir.Complete.length_boolPoint 0 w)]
    simp
  | V + 1, w, [], hz => by simp at hz
  | V + 1, w, x :: z, hz => by
    rw [LeanVM.Protocol.Whir.Complete.boolPoint_succ, LeanVM.Protocol.Whir.Complete.eqEval_cons,
      eqEval_boolPoint_prod V (w / 2) z (by simpa using hz), Finset.prod_range_succ', mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun j _ ↦ ?_
      simp [fz, xc, Nat.testBit_div_two]
    · have h2 : (1 : E) + 1 = 0 := CharTwo.add_self_eq_zero 1
      by_cases hb : w.testBit 0
      · simp only [fz, xc, hb, ite_true, List.getD_cons_zero]
        rw [h2, zero_add]
      · simp [fz, xc, hb]

/-! ### The slack's weights in closed form -/

/-- **The slack's positions** in a table of `2^28` words: `slackAt k` plus `0`, `2^25` or `3 · 2^25`. -/
theorem slackPos_filter (k : ℕ) :
    (Finset.range (2 ^ 28)).filter (SlackPos (2 ^ 24) k) =
      {slackAt k, slackAt k + 2 ^ 25, slackAt k + 3 * 2 ^ 25} := by
  have hs : slackAt k < 8 := by unfold slackAt; split_ifs <;> omega
  ext w
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, SlackPos]
  norm_num only
  omega

/-- The common factor of the slack's weights below the slack's coefficient bits and limb bits. -/
noncomputable def Rz (z : List E) : E := ∏ j ∈ Finset.Ico 3 25, (1 + xc z j)

/-- **The slack's common factor** `C(z)`. -/
noncomputable def Cz (z : List E) : E := Rz z * (1 + xc z 27) * (1 + xc z 26 * (1 + xc z 25))

/-- **Slack word `k`'s monomial** in `z₀, z₁, z₂`. -/
def mz (z : List E) (k : ℕ) : E := ∏ j ∈ Finset.range 3, fz z (slackAt k) j

theorem prod28 (z : List E) (w : ℕ) : ∏ j ∈ Finset.range 28, fz z w j =
    (∏ j ∈ Finset.range 3, fz z w j) * (∏ j ∈ Finset.Ico 3 25, fz z w j) * (fz z w 25 * fz z w 26 * fz z w 27) := by
  rw [← Finset.prod_range_mul_prod_Ico _ (show 3 ≤ 28 by norm_num),
    ← Finset.prod_Ico_consecutive _ (show 3 ≤ 25 by norm_num) (show 25 ≤ 28 by norm_num),
    show Finset.Ico 25 28 = {25, 26, 27} by decide, Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
  ring

theorem prodLow (z : List E) (w s : ℕ) (h : ∀ j < 3, w.testBit j = s.testBit j) :
    ∏ j ∈ Finset.range 3, fz z w j = ∏ j ∈ Finset.range 3, fz z s j :=
  Finset.prod_congr rfl fun j hj ↦ by simp only [fz, h j (Finset.mem_range.1 hj)]

theorem prodMid (z : List E) (w : ℕ) (h : ∀ j < 25, 3 ≤ j → w.testBit j = false) :
    ∏ j ∈ Finset.Ico 3 25, fz z w j = Rz z :=
  Finset.prod_congr rfl fun j hj ↦ by
    have := Finset.mem_Ico.1 hj
    exact fz_f (h j this.2 this.1)

/-- The bits of the slack's positions. -/
theorem slack_bits : ∀ k < 4,
    (∀ j < 3, (slackAt k + 2 ^ 25).testBit j = (slackAt k).testBit j) ∧
    (∀ j < 3, (slackAt k + 3 * 2 ^ 25).testBit j = (slackAt k).testBit j) ∧
    (∀ j < 25, 3 ≤ j → (slackAt k).testBit j = false) ∧
    (∀ j < 25, 3 ≤ j → (slackAt k + 2 ^ 25).testBit j = false) ∧
    (∀ j < 25, 3 ≤ j → (slackAt k + 3 * 2 ^ 25).testBit j = false) ∧
    (slackAt k).testBit 25 = false ∧ (slackAt k).testBit 26 = false ∧ (slackAt k).testBit 27 = false ∧
    (slackAt k + 2 ^ 25).testBit 25 = true ∧ (slackAt k + 2 ^ 25).testBit 26 = false ∧
    (slackAt k + 2 ^ 25).testBit 27 = false ∧
    (slackAt k + 3 * 2 ^ 25).testBit 25 = true ∧ (slackAt k + 3 * 2 ^ 25).testBit 26 = true ∧
    (slackAt k + 3 * 2 ^ 25).testBit 27 = false := by
  decide

/-- **The slack's weights in closed form**: `slackWeight z k = mz z k · C(z)`. -/
theorem weight_closed (z : List E) (hz : z.length = 28) (k : ℕ) (hk : k < slackWords) :
    slackWeight z k = mz z k * Cz z := by
  have hk4 : k < 4 := hk
  obtain ⟨h1, h2, h3, h4, h5, a25, a26, a27, b25, b26, b27, c25, c26, c27⟩ := slack_bits k hk4
  rw [slackWeight, ← Finset.sum_filter, slackPos_filter k, Finset.sum_insert (by norm_num),
    Finset.sum_pair (by norm_num)]
  simp only [eqEval_boolPoint_prod 28 _ z hz, prod28]
  rw [prodLow z _ _ h1, prodLow z _ _ h2, prodMid z _ h3, prodMid z _ h4, prodMid z _ h5,
    fz_f a25, fz_f a26, fz_f a27, fz_t b25, fz_f b26, fz_f b27, fz_t c25, fz_t c26, fz_f c27,
    show ∏ j ∈ Finset.range 3, fz z (slackAt k) j = mz z k from rfl, Cz]
  have h2E : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination (mz z k * Rz z * (1 + xc z 27) * xc z 25 * (1 + xc z 26)) * h2E

theorem mz0 (z : List E) : mz z 0 = (1 + xc z 0) * (1 + xc z 1) * (1 + xc z 2) := by
  simp only [mz, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rw [fz_f (by decide), fz_f (by decide), fz_f (by decide)]

theorem mz1 (z : List E) : mz z 1 = xc z 0 * (1 + xc z 1) * (1 + xc z 2) := by
  simp only [mz, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rw [fz_t (by decide), fz_f (by decide), fz_f (by decide)]

theorem mz2 (z : List E) : mz z 2 = (1 + xc z 0) * xc z 1 * (1 + xc z 2) := by
  simp only [mz, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rw [fz_f (by decide), fz_t (by decide), fz_f (by decide)]

theorem mz3 (z : List E) : mz z 3 = (1 + xc z 0) * (1 + xc z 1) * xc z 2 := by
  simp only [mz, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rw [fz_f (by decide), fz_f (by decide), fz_t (by decide)]

/-- **The slack map in closed form.** -/
theorem slackMap_eq (z : List E) (hz : z.length = 28) (sw : Fin slackWords → K) :
    slackMap z sw = Cz z * (ofK (svAt sw 0) * ((1 + xc z 0) * (1 + xc z 1) * (1 + xc z 2)) +
      ofK (svAt sw 1) * (xc z 0 * (1 + xc z 1) * (1 + xc z 2)) +
      ofK (svAt sw 2) * ((1 + xc z 0) * xc z 1 * (1 + xc z 2)) +
      ofK (svAt sw 3) * ((1 + xc z 0) * (1 + xc z 1) * xc z 2)) := by
  show ∑ k ∈ Finset.range slackWords, ofK (svAt sw k) * slackWeight z k = _
  rw [show slackWords = 4 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [weight_closed z hz 0 (by decide), weight_closed z hz 1 (by decide), weight_closed z hz 2 (by decide),
    weight_closed z hz 3 (by decide), mz0, mz1, mz2, mz3]
  ring

/-! ### `E` is three-dimensional over `K` -/

/-- **Three elements `1, u, v` span `E` over `K`** when `u ∉ K` and `v ∉ K + K·u`: the map `(a, b, c) ↦ a + b·u + c·v`
is injective, so onto, `|K³| = |E|`. -/
theorem span3 (u v : E) (hu : ∀ a : K, u ≠ ofK a) (hv : ∀ a b : K, v ≠ ofK a + ofK b * u) (y : E) :
    ∃ a b c : K, ofK a + ofK b * u + ofK c * v = y := by
  classical
  have hof : ∀ a : K, ofK a = algebraMap K E a := fun _ ↦ rfl
  let f : K × K × K → E := fun p ↦ ofK p.1 + ofK p.2.1 * u + ofK p.2.2 * v
  have hinj : Function.Injective f := by
    intro p q hpq
    simp only [f, hof] at hpq
    have hd : algebraMap K E (p.1 - q.1) + algebraMap K E (p.2.1 - q.2.1) * u +
        algebraMap K E (p.2.2 - q.2.2) * v = 0 := by
      simp only [map_sub]; linear_combination hpq
    have h3 : p.2.2 - q.2.2 = 0 := by
      by_contra h3
      have hA : algebraMap K E (p.2.2 - q.2.2) ≠ 0 := (map_ne_zero _).2 h3
      refine hv (-(p.1 - q.1) / (p.2.2 - q.2.2)) (-(p.2.1 - q.2.1) / (p.2.2 - q.2.2)) ?_
      have hv' : algebraMap K E (p.2.2 - q.2.2) * v =
          -algebraMap K E (p.1 - q.1) - algebraMap K E (p.2.1 - q.2.1) * u := by linear_combination hd
      rw [hof, hof, map_div₀, map_div₀, map_neg, map_neg]
      calc v = (algebraMap K E (p.2.2 - q.2.2))⁻¹ * (algebraMap K E (p.2.2 - q.2.2) * v) := by
            rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]
        _ = _ := by rw [hv']; field_simp; ring
    have h2 : p.2.1 - q.2.1 = 0 := by
      by_contra h2
      have hA : algebraMap K E (p.2.1 - q.2.1) ≠ 0 := (map_ne_zero _).2 h2
      refine hu (-(p.1 - q.1) / (p.2.1 - q.2.1)) ?_
      have hu' : algebraMap K E (p.2.1 - q.2.1) * u = -algebraMap K E (p.1 - q.1) := by
        rw [h3, map_zero] at hd; linear_combination hd
      rw [hof, map_div₀, map_neg]
      calc u = (algebraMap K E (p.2.1 - q.2.1))⁻¹ * (algebraMap K E (p.2.1 - q.2.1) * u) := by
            rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]
        _ = _ := by rw [hu']; field_simp
    have h1 : p.1 - q.1 = 0 := by
      simp only [h3, h2, map_zero, zero_mul, add_zero] at hd
      exact (map_eq_zero _).1 hd
    exact Prod.ext (sub_eq_zero.1 h1) (Prod.ext (sub_eq_zero.1 h2) (sub_eq_zero.1 h3))
  have hcard : Fintype.card (K × K × K) = Fintype.card E := by
    simp only [Fintype.card_prod, BF64.card_bf64, card_E]
    norm_num
  obtain ⟨⟨a, b, c⟩, h⟩ := ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩).2 y
  exact ⟨a, b, c, h⟩

/-! ### Where the slack's weights span `E` -/

/-- The involution `u ↦ u/(1+u)` (off `1`) taking `z_j` to `u_j`. -/
noncomputable def invE (u : E) : E := u / (1 + u)

theorem one_add_ne_zero {x : E} (hx : x ≠ 1) : 1 + x ≠ 0 := fun h ↦
  hx (by have h2 : (2 : E) = 0 := CharTwo.two_eq_zero; linear_combination h - h2)

theorem invE_invE {x : E} (hx : x ≠ 1) : invE (invE x) = x := by
  have ha := one_add_ne_zero hx
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hb : 1 + invE x = (1 + x)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [invE, add_mul, div_mul_cancel₀ _ ha]
    linear_combination x * h2
  rw [invE, hb, div_inv_eq_mul, invE, div_mul_cancel₀ _ ha]

/-- `z₀` lands `u₀` in `K`. -/
def B0 (x : E) : Prop := ∃ a : K, x = invE (ofK a)

/-- `x` lands its `u` in `K + K·u₀`. -/
def B1 (x0 x : E) : Prop := ∃ p : K × K, x = invE (ofK p.1 + ofK p.2 * invE x0)

/-- An index-dependent family of slack words. -/
def mkSw (g : ℕ → K) : Fin slackWords → K := fun k ↦ g k.val

theorem svAt_mkSw (g : ℕ → K) (j : ℕ) (hj : j < slackWords) : svAt (mkSw g) j = g j := by
  simp [svAt, mkSw, hj]

/-- **The slack's weights span `E`** off the bad events. -/
theorem slackSpan_of (z : List E) (hz : z.length = 28) (hR : ∀ j < 25, xc z j ≠ 1) (h27 : xc z 27 ≠ 1)
    (hL : 1 + xc z 26 * (1 + xc z 25) ≠ 0) (h0 : ¬ B0 (xc z 0))
    (h12 : ¬ (B1 (xc z 0) (xc z 1) ∧ B1 (xc z 0) (xc z 2))) : SlackSpan z := by
  have hC : Cz z ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (one_add_ne_zero h27)) hL
    exact Finset.prod_ne_zero_iff.2 fun j hj ↦ one_add_ne_zero (hR j (Finset.mem_Ico.1 hj).2)
  have a0 := one_add_ne_zero (hR 0 (by norm_num))
  have a1 := one_add_ne_zero (hR 1 (by norm_num))
  have a2 := one_add_ne_zero (hR 2 (by norm_num))
  have hQ : Cz z * ((1 + xc z 0) * (1 + xc z 1) * (1 + xc z 2)) ≠ 0 :=
    mul_ne_zero hC (mul_ne_zero (mul_ne_zero a0 a1) a2)
  have hu : ∀ a : K, invE (xc z 0) ≠ ofK a := fun a h ↦
    h0 ⟨a, by rw [← h, invE_invE (hR 0 (by norm_num))]⟩
  have hv : ∀ j, j < 25 → ¬ B1 (xc z 0) (xc z j) → ∀ a b : K, invE (xc z j) ≠ ofK a + ofK b * invE (xc z 0) :=
    fun j hj hB a b h ↦ hB ⟨(a, b), by rw [← h, invE_invE (hR j hj)]⟩
  intro y
  have hy : y = Cz z * ((1 + xc z 0) * (1 + xc z 1) * (1 + xc z 2)) *
      (y / (Cz z * ((1 + xc z 0) * (1 + xc z 1) * (1 + xc z 2)))) := by
    rw [mul_div_cancel₀ _ hQ]
  rcases not_and_or.1 h12 with h1 | h2
  · obtain ⟨a, b, c, habc⟩ := span3 _ _ hu (hv 1 (by norm_num) h1) (y / (Cz z * ((1 + xc z 0) * (1 + xc z 1) *
      (1 + xc z 2))))
    refine ⟨mkSw fun j ↦ if j = 0 then a else if j = 1 then b else if j = 2 then c else 0, ?_⟩
    have e0 : svAt (mkSw fun j ↦ if j = 0 then a else if j = 1 then b else if j = 2 then c else 0) 0 = a := rfl
    have e1 : svAt (mkSw fun j ↦ if j = 0 then a else if j = 1 then b else if j = 2 then c else 0) 1 = b := rfl
    have e2 : svAt (mkSw fun j ↦ if j = 0 then a else if j = 1 then b else if j = 2 then c else 0) 2 = c := rfl
    have e3 : svAt (mkSw fun j ↦ if j = 0 then a else if j = 1 then b else if j = 2 then c else 0) 3 = 0 := rfl
    rw [slackMap_eq z hz, e0, e1, e2, e3, ofK_zero₂, hy, ← habc]
    simp only [invE]
    field_simp
    ring
  · obtain ⟨a, b, c, habc⟩ := span3 _ _ hu (hv 2 (by norm_num) h2) (y / (Cz z * ((1 + xc z 0) * (1 + xc z 1) *
      (1 + xc z 2))))
    refine ⟨mkSw fun j ↦ if j = 0 then a else if j = 1 then b else if j = 3 then c else 0, ?_⟩
    have e0 : svAt (mkSw fun j ↦ if j = 0 then a else if j = 1 then b else if j = 3 then c else 0) 0 = a := rfl
    have e1 : svAt (mkSw fun j ↦ if j = 0 then a else if j = 1 then b else if j = 3 then c else 0) 1 = b := rfl
    have e2 : svAt (mkSw fun j ↦ if j = 0 then a else if j = 1 then b else if j = 3 then c else 0) 2 = 0 := rfl
    have e3 : svAt (mkSw fun j ↦ if j = 0 then a else if j = 1 then b else if j = 3 then c else 0) 3 = c := rfl
    rw [slackMap_eq z hz, e0, e1, e2, e3, ofK_zero₂, hy, ← habc]
    simp only [invE]
    field_simp
    ring

/-! ### The coordinates of `n` uniform elements -/

theorem prEvent_bind_pure {α β : Type} (X : ProbComp α) (f : α → β) (P : β → Prop) :
    Pr{let y ← X >>= fun x ↦ pure (f x)}[P y] = Pr{let x ← X}[P (f x)] := by
  rw [show (X >>= fun x ↦ pure (f x)) = f <$> X by rw [map_eq_bind_pure_comp]; rfl, prEvent_map]

/-- **A coordinate of `n` uniform elements is uniform.** -/
theorem coord_iidE : ∀ (n i : ℕ), i < n → (iidE n >>= fun z ↦ pure (z.getD i 0)) =ᵈ eDist
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, 0, _ => by
    rw [iidE_succ]
    simp only [bind_assoc, pure_bind, List.getD_cons_zero]
    have h := EvalDistEq.bind_right eDist fun e ↦ evalDistEq_bind_drop (iidE n) (pure e : ProbComp E)
    rwa [bind_pure] at h
  | n + 1, i + 1, hi => by
    rw [iidE_succ]
    simp only [bind_assoc, pure_bind, List.getD_cons_succ]
    exact (evalDistEq_bind_drop _ _).trans (coord_iidE n i (by omega))

/-- **Two coordinates of `n` uniform elements are independent and uniform.** -/
theorem pair_iidE : ∀ (n i j : ℕ), i < j → j < n →
    (iidE n >>= fun z ↦ pure (z.getD i 0, z.getD j 0)) =ᵈ
      (eDist >>= fun a ↦ eDist >>= fun b ↦ (pure (a, b) : ProbComp (E × E)))
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, 0, 0, hij, _ => absurd hij (lt_irrefl 0)
  | n + 1, 0, j + 1, _, hj => by
    rw [iidE_succ]
    simp only [bind_assoc, pure_bind, List.getD_cons_zero, List.getD_cons_succ]
    refine EvalDistEq.bind_right eDist fun e ↦ ?_
    have h := (coord_iidE n j (by omega)).bind_left (fun b ↦ (pure (e, b) : ProbComp (E × E)))
    simpa only [bind_assoc, pure_bind] using h
  | n + 1, i + 1, 0, hij, _ => absurd hij (Nat.not_lt_zero _)
  | n + 1, i + 1, j + 1, hij, hj => by
    rw [iidE_succ]
    simp only [bind_assoc, pure_bind, List.getD_cons_succ]
    exact (evalDistEq_bind_drop _ _).trans (pair_iidE n i j (by omega) (by omega))

/-- Three independent uniform elements. -/
noncomputable def tripleDist : ProbComp (E × E × E) :=
  eDist >>= fun a ↦ eDist >>= fun b ↦ eDist >>= fun c ↦ pure (a, b, c)

/-- **The first three coordinates of `n + 3` uniform elements are independent and uniform.** -/
theorem triple_iidE (n : ℕ) :
    (iidE (n + 3) >>= fun z ↦ pure (z.getD 0 0, z.getD 1 0, z.getD 2 0)) =ᵈ tripleDist := by
  rw [iidE_succ, iidE_succ, iidE_succ, tripleDist]
  simp only [bind_assoc, pure_bind, List.getD_cons_zero, List.getD_cons_succ]
  exact EvalDistEq.bind_right _ fun a ↦ EvalDistEq.bind_right _ fun b ↦ EvalDistEq.bind_right _ fun c ↦
    evalDistEq_bind_drop _ _

theorem prEvent_coord (n i : ℕ) (hi : i < n) (P : E → Prop) :
    Pr{let z ← iidE n}[P (z.getD i 0)] = Pr{let x ← eDist}[P x] := by
  rw [← (coord_iidE n i hi).prEvent_eq P, prEvent_bind_pure]

/-! ### The events' probabilities -/

/-- **A uniform element hits a family of `|ι|` points** with probability at most `|ι| · 2^-192`. -/
theorem prEvent_eDist_exists {ι : Type} [Fintype ι] (g : ι → E) :
    Pr{let x ← eDist}[∃ i, x = g i] ≤ Fintype.card ι * κE := by
  classical
  rw [prEvent_eq_tsum_ite, tsum_fintype]
  simp only [prEvent_eDist]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul' ?_ le_rfl
  have h : (Finset.univ.filter fun x ↦ ∃ i, x = g i) = Finset.univ.image g := by
    ext x; simp [eq_comm]
  rw [h]
  exact_mod_cast Finset.card_image_le.trans (by simp)

theorem card_K_cast : (Fintype.card K : ℝ≥0∞) = 2 ^ 64 := by
  simp only [BF64.card_bf64]; norm_num

theorem card_KK_cast : (Fintype.card (K × K) : ℝ≥0∞) = 2 ^ 128 := by
  simp only [Fintype.card_prod, BF64.card_bf64]; norm_num

theorem prEvent_B0 : Pr{let x ← eDist}[B0 x] ≤ 2 ^ 64 * κE :=
  (prEvent_eDist_exists fun a : K ↦ invE (ofK a)).trans (by rw [card_K_cast])

theorem prEvent_B1 (x0 : E) : Pr{let x ← eDist}[B1 x0 x] ≤ 2 ^ 128 * κE :=
  (prEvent_eDist_exists fun p : K × K ↦ invE (ofK p.1 + ofK p.2 * invE x0)).trans (by rw [card_KK_cast])

/-- **`1 + b(1 + a) = 0`** at two uniform elements: at most one `b` a given `a`. -/
theorem prEvent_L :
    Pr{let p ← (eDist >>= fun a ↦ eDist >>= fun b ↦ (pure (a, b) : ProbComp (E × E)))}[1 + p.2 * (1 + p.1) = 0]
      ≤ κE := by
  refine prEvent_bind_le_of_forall_le _ _ _ fun a ↦ ?_
  rw [prEvent_bind_pure]
  refine (prEvent_mono_of_support _ _ (fun b ↦ b = (1 + a)⁻¹) fun b _ hb ↦ ?_).trans (le_of_eq (prEvent_eDist _))
  dsimp only at hb
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  exact eq_inv_of_mul_eq_one_left (by linear_combination hb - h2)

/-- **Two events of the same probability `ε`, each on `(a, b)` and `(a, c)`**, at three uniform elements. -/
theorem prEvent_triple (Q : E → E → Prop) (ε : ℝ≥0∞) (hQ : ∀ a, Pr{let x ← eDist}[Q a x] ≤ ε) :
    Pr{let t ← tripleDist}[Q t.1 t.2.1 ∧ Q t.1 t.2.2] ≤ ε * ε := by
  rw [tripleDist]
  refine prEvent_bind_le_of_forall_le _ _ _ fun a ↦ ?_
  refine (prEvent_bind_le_prEvent_mul_of_forall_le _ _ (Q a) _ (ε := ε) (fun b _ ↦ ?_) (fun b hb ↦ ?_)).trans
    (mul_le_mul' (hQ a) le_rfl)
  · rw [prEvent_bind_pure]
    exact (prEvent_mono_of_support _ _ (fun c ↦ Q a c) fun c _ h ↦ h.2).trans (hQ a)
  · rw [prEvent_bind_pure]
    exact (prEvent_eq_zero_iff _ _).2 fun c _ h ↦ hb h.1

theorem prEvent_coords_one (n : ℕ) (hn : n ≤ 28) :
    Pr{let z ← iidE 28}[∃ j < n, xc z j = 1] ≤ n * κE := by
  induction n with
  | zero =>
    rw [(prEvent_eq_zero_iff _ _).2 fun z _ ⟨j, hj, _⟩ ↦ absurd hj (Nat.not_lt_zero _)]
    simp
  | succ n ih =>
    calc Pr{let z ← iidE 28}[∃ j < n + 1, xc z j = 1]
        ≤ Pr{let z ← iidE 28}[(∃ j < n, xc z j = 1) ∨ xc z n = 1] :=
          prEvent_mono_of_support _ _ _ fun z _ ⟨j, hj, h⟩ ↦ by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
            · exact Or.inl ⟨j, hj, h⟩
            · exact Or.inr h
      _ ≤ _ := prEvent_or_le _ _ _
      _ ≤ n * κE + κE := add_le_add (ih (by omega))
          (le_of_eq ((prEvent_coord 28 n (by omega) (fun x ↦ x = 1)).trans (prEvent_eDist 1)))
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * κE := by push_cast; ring

/-! ### The bound -/

/-- **The slack's span-failure bound**: `27 · 2^-192 + 2^64 · 2^-192 + (2^128 · 2^-192)²` (`εslack_le`: at most
`2^-126`). -/
noncomputable def εslack : ℝ≥0∞ := 27 * κE + 2 ^ 64 * κE + (2 ^ 128 * κE) ^ 2

theorem εslack_le : εslack ≤ ((2 : ℝ≥0∞) ^ 126)⁻¹ := by
  have hk : κE = ((2 : ℝ≥0∞) ^ 192)⁻¹ := pmax_eq
  have hcancel : ∀ a b : ℕ, (2 : ℝ≥0∞) ^ a * ((2 : ℝ≥0∞) ^ (a + b))⁻¹ = ((2 : ℝ≥0∞) ^ b)⁻¹ := fun a b ↦ by
    rw [pow_add, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp),
      one_mul]
  have h64 : (2 : ℝ≥0∞) ^ 64 * κE = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by rw [hk]; exact hcancel 64 128
  have h128 : (2 : ℝ≥0∞) ^ 128 * κE = ((2 : ℝ≥0∞) ^ 64)⁻¹ := by rw [hk]; exact hcancel 128 64
  have hsq : (((2 : ℝ≥0∞) ^ 64)⁻¹) ^ 2 = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
    rw [show (2 : ℝ≥0∞) ^ 128 = (2 ^ 64) ^ 2 by rw [← pow_mul]]
    exact ENNReal.inv_pow.symm
  have h27 : 27 * κE ≤ ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
    rw [← h64]; gcongr; norm_num
  have h4 : 4 * ((2 : ℝ≥0∞) ^ 128)⁻¹ = ((2 : ℝ≥0∞) ^ 126)⁻¹ := by
    rw [show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num]; exact hcancel 2 126
  unfold εslack
  rw [h64, h128, hsq, ← h4]
  calc 27 * κE + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹
      ≤ ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ := by gcongr
    _ = 3 * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by ring
    _ ≤ 4 * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by gcongr; norm_num

/-- `T`'s point: its law under the simulator's challenges. -/
theorem zT_dist : (sampleChallenges >>= fun c ↦ pure c.zT) =ᵈ iidE 28 := by
  rw [sampleChallenges_eq]
  simp only [bind_assoc, pure_bind]
  refine (evalDistEq_bind_drop _ _).trans ((evalDistEq_bind_drop _ _).trans ((evalDistEq_bind_drop _ _).trans
    ((evalDistEq_bind_drop _ _).trans ?_)))
  have h := EvalDistEq.bind_right (iidE 28) fun zT ↦
    (evalDistEq_bind_drop eDist _).trans (evalDistEq_bind_drop eDist (pure zT : ProbComp (List E)))
  rwa [bind_pure] at h

/-- The bad events of `T`'s point. -/
def SpanBad (z : List E) : Prop :=
  (∃ j < 25, xc z j = 1) ∨ xc z 27 = 1 ∨ 1 + xc z 26 * (1 + xc z 25) = 0 ∨ B0 (xc z 0) ∨
    (B1 (xc z 0) (xc z 1) ∧ B1 (xc z 0) (xc z 2))

theorem spanBad_of (z : List E) (hz : z.length = 28) (h : ¬ SlackSpan z) : SpanBad z := by
  by_contra hb
  simp only [SpanBad, not_or] at hb
  obtain ⟨hR, h27, hL, h0, h12⟩ := hb
  exact h (slackSpan_of z hz (fun j hj h1 ↦ hR ⟨j, hj, h1⟩) h27 hL h0 h12)

/-- **The slack's span failure is at most `εslack`** (`≤ 2^-126`, `εslack_le`). -/
theorem spanFail_le : spanFail ≤ εslack := by
  have h1 : spanFail = Pr{let z ← iidE 28}[¬ SlackSpan z] := by
    rw [spanFail, ← zT_dist.prEvent_eq (fun z ↦ ¬ SlackSpan z), prEvent_bind_pure]
  rw [h1]
  refine (prEvent_mono_of_support _ _ SpanBad fun z hz h ↦ spanBad_of z (length_of_mem_iidE 28 z hz) h).trans ?_
  have hA := prEvent_coords_one 25 (by norm_num)
  have hB : Pr{let z ← iidE 28}[xc z 27 = 1] ≤ κE :=
    le_of_eq ((prEvent_coord 28 27 (by norm_num) (fun x ↦ x = 1)).trans (prEvent_eDist 1))
  have hC : Pr{let z ← iidE 28}[1 + xc z 26 * (1 + xc z 25) = 0] ≤ κE := by
    refine le_trans (le_of_eq ?_) prEvent_L
    rw [← (pair_iidE 28 25 26 (by norm_num) (by norm_num)).prEvent_eq, prEvent_bind_pure]
  have hD : Pr{let z ← iidE 28}[B0 (xc z 0)] ≤ 2 ^ 64 * κE :=
    (le_of_eq (prEvent_coord 28 0 (by norm_num) B0)).trans prEvent_B0
  have hF : Pr{let z ← iidE 28}[B1 (xc z 0) (xc z 1) ∧ B1 (xc z 0) (xc z 2)] ≤
      2 ^ 128 * κE * (2 ^ 128 * κE) := by
    refine le_trans (le_of_eq ?_) (prEvent_triple B1 _ prEvent_B1)
    rw [← (triple_iidE 25).prEvent_eq, prEvent_bind_pure]
  delta SpanBad
  refine ((prEvent_or_le _ _ _).trans (add_le_add hA ((prEvent_or_le _ _ _).trans (add_le_add hB
    ((prEvent_or_le _ _ _).trans (add_le_add hC ((prEvent_or_le _ _ _).trans (add_le_add hD hF)))))))).trans
    (le_of_eq ?_)
  unfold εslack
  push_cast
  ring

/-! ### Zero knowledge with the slack proved -/

/-- **`RevealedUniform` at `δr = 0` from group 1's uniformity alone**, the span failure bounded. -/
theorem revealedUniform_slack (ε1 : ℝ≥0∞) (h : Group1Uniform ε1) : RevealedUniform (ε1 + εslack) 0 :=
  fun stmt w hrel ↦ (revealedUniform_of_group1 ε1 h stmt w hrel).trans (add_le_add le_rfl spanFail_le)

/-- **Zero knowledge of the membership proof from a zero-knowledge PCS and group 1's uniformity**: the simulator
`zkSimulator sim` is within `εpcs Q + ε1 + εslack + εfs₀` of the honest prover, `εslack ≤ 2^-126` (`εslack_le`),
`εfs₀ ≤ 2^-163` (`εfs₀_le`). -/
theorem zeroKnowledge_pcs_slack (sim : PcsSimulator) (εpcs : ℕ → ℝ≥0∞) (ε1 : ℝ≥0∞)
    (hpcs : PcsZeroKnowledge sim εpcs) (h1 : Group1Uniform ε1) :
    ZeroKnowledgeWith sim.s₀ (zkSimulator sim) sim.oracle (fun Q ↦ εpcs Q + ε1 + εslack + εfs₀) := by
  have h := zeroKnowledge_pcs_closed sim εpcs (ε1 + εslack) 0 hpcs (revealedUniform_slack ε1 h1)
  have he : (fun Q ↦ εpcs Q + (ε1 + εslack) + 0 + εfs₀) = fun Q ↦ εpcs Q + ε1 + εslack + εfs₀ :=
    funext fun Q ↦ by rw [add_zero, ← add_assoc]
  rwa [he] at h

end PcsQuotient.EndToEnd
