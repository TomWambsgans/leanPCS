-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniSound.Ids.Bridges

/-!
# The batch's start (`UniIdsRest.batch_start`)

`Σ_u g(u) + target` is the combination by `λ` of each commitment's combination by `ρ` of its relations'
differences, and of the pending matrices' difference (`batch_start_of`): `weightAt` is linear in its
terms (`WeightAtLinear`), `combine` is the `ρ`-combination at the merged points (`CombineEq`), so the
combined claim's weight against the zero-extended stack, plus its value, is `Σ_i ρ^i` of the relations'
differences (`relDiff`, at the same merged points); the pending term's product is its difference's sum.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset

/-! ## Powers -/

theorem powComb_nil (ρ : E) : powComb [] ρ = 0 := by simp [powComb]

theorem powComb_eq_range (a : List E) (ρ : E) :
    powComb a ρ = ∑ i ∈ range a.length, a.getD i 0 * ρ ^ i := by
  unfold powComb
  rw [← Fin.sum_univ_eq_sum_range (fun i ↦ a.getD i 0 * ρ ^ i)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [List.getD_eq_getElem _ _ i.isLt]
  rfl

theorem powComb_cons (x : E) (l : List E) (ρ : E) : powComb (x :: l) ρ = x + ρ * powComb l ρ := by
  rw [powComb_eq_range, powComb_eq_range, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
  have h1 : ∀ i ∈ range l.length, (x :: l).getD (i + 1) 0 * ρ ^ (i + 1) = ρ * (l.getD i 0 * ρ ^ i) := by
    intro i _
    rw [List.getD_cons_succ, pow_succ]
    ring
  rw [Finset.sum_congr rfl h1, List.getD_cons_zero, pow_zero, mul_one, add_comm]

theorem zipIdx_sum (ρ : E) (f : Relation → E) : ∀ (l : List Relation) (n : ℕ),
    ((l.zipIdx n).map fun ri ↦ ρ ^ ri.2 * f ri.1).sum = ρ ^ n * powComb (l.map f) ρ
  | [], n => by simp [powComb_nil]
  | x :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, zipIdx_sum ρ f l (n + 1), List.map_cons,
      powComb_cons, pow_succ]
    ring

/-- `Σ_i ρ^i f(l_i)` is `powComb (l.map f) ρ`. -/
theorem zipIdx_sum_zero (ρ : E) (f : Relation → E) (l : List Relation) :
    ((l.zipIdx).map fun ri ↦ ρ ^ ri.2 * f ri.1).sum = powComb (l.map f) ρ := by
  have := zipIdx_sum ρ f l 0
  rwa [pow_zero, one_mul] at this

/-! ## One commitment -/

theorem sum_list_mul {α : Type} (l : List α) (f : α → E) (c : E) :
    (l.map fun a ↦ f a * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, add_mul]

theorem sum_range_list {α : Type} (l : List α) (f : α → ℕ → E) (n : ℕ) :
    ∑ u ∈ range n, (l.map fun a ↦ f a u).sum = (l.map fun a ↦ ∑ u ∈ range n, f a u).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- **One commitment's product and value**: its combined claim's weight against the zero-extended
stack, plus its value, is `Σ_i ρ^i` of its relations' differences. -/
theorem comm_start (hW : WeightAtLinear) (hC : CombineEq) (rels : List Relation) (c : Commitment)
    (ρ : E) (L : StackLayout) (rm : Option (List E)) (V : ℕ) (C : Stk) :
    ∑ u ∈ range (2 ^ V), weightAt ((combine rels c ρ).getD zeroClaim) L (bitsE u V) rm * stE C L.vars u +
        ((combine rels c ρ).getD zeroClaim).value =
      powComb ((mine rels c).map (relDiff L rm V C (mergedPoint (mine rels c)))) ρ := by
  by_cases hm : mine rels c = []
  · have hnone : combine rels c ρ = none := by
      unfold combine
      simp only [mine] at hm
      simp [hm]
    rw [hnone, hm]
    simp [weightAt, powComb_nil, zeroClaim]
  · obtain ⟨cb, hcb, hv, hF⟩ := hC rels c ρ hm
    rw [hcb, Option.getD_some]
    have hw : ∀ u, weightAt cb L (bitsE u V) rm =
        (cb.terms.map fun tm ↦ tm.2.2.2 * termW L rm V tm.1 (cb.points.getD tm.2.1 []) tm.2.2.1 u).sum :=
      fun u ↦ hW cb L (bitsE u V) rm
    simp_rw [hw, ← sum_list_mul]
    rw [sum_range_list]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [hF (fun col pt tw ↦ ∑ u ∈ range (2 ^ V), termW L rm V col pt tw u * stE C L.vars u), hv,
      ← List.sum_map_add, ← zipIdx_sum_zero]
    congr 1
    refine List.map_congr_left fun ri _ ↦ ?_
    simp only [relDiff]
    ring

end UniSound.Ids
