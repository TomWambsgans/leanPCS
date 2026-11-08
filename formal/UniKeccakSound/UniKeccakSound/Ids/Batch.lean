-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The proofs are `UniSound/Ids/Weights.lean`'s
-- (`weightAtLinear`) and `UniSound/Ids/Batch.lean`'s (`batch_start_of`), for `weightAtK` and the Keccak batch.
import UniSound.Ids.Batch
import UniSound.Ids.Weights
import UniKeccakSound.Ids.Model

/-!
# The Keccak batch's start (`UniIdsK.batch_start`)

* **`weightAtK_linear`**: `weightAtK` is linear in its claim's terms (`UniSound.Ids.weightAtLinear`'s proof: the
  fold term by term, each term's weight its one-term claim's; a `q_flock` slot term reads `q_flock`'s variables
  minus its point's slot bits, the same in both).
* **`batch_start_K`**: `Σ_u g(u) + target` is the combination by `λ` of the three commitments' combinations by `ρ`
  of their relations' differences (`relDiffK`), from `weightAtK_linear` and `combine`'s `ρ`-combination
  (`UniSound.Ids.combineEq`, generic). No pending term.
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.Weights UniKeccak Finset

/-! ## `weightAtK` term by term -/

/-- `q_flock`'s variables in a layout (`weightAtK`'s `qflockVars`). -/
def qvOf (L : StackLayout) : ℕ := ((L.limbs .qflock).head?.map (·.2.1)).getD 0

/-- `weightAtK`'s view of a term's column: `q_flock`'s slot `j` at the point `pt` (twisted `point`) reads
`q_flock` at `(bits(j), point)`, `qv − |pt|` slot bits; another column itself. -/
def slotViewK (qv : ℕ) (column : Column) (pt point : List E) : Column × List E × ℕ :=
  match column with
  | .qflockSlot j =>
    let row := (List.range (qv - pt.length)).map (bitE j) ++ point
    (.qflock, row, row.length)
  | _ => (column, point, 0)

/-- `weightAtK`'s step on one term. -/
def wStepK (L : StackLayout) (r : List E) (rm : Option (List E)) (pt point : List E) (total : E)
    (column : Column) (twist : ℕ) (coefficient : E) : E :=
  if twist = ringTwist then
    (L.limbs column).foldl (fun total b ↦ total +
      (if b.1 = 0 then coefficient else coefficient * limbBasis.getD b.1 0) *
        (ringRow rm pt r b.2.1 * selector r b.2.1 b.2.2)) total
  else
    (L.limbs (slotViewK (qvOf L) column pt point).1).foldl (fun total b ↦ total +
      (if b.1 = 0 then coefficient else coefficient * limbBasis.getD b.1 0) *
        (rowEq (slotViewK (qvOf L) column pt point).2.1
          (if (slotViewK (qvOf L) column pt point).2.2 > 0 then (slotViewK (qvOf L) column pt point).2.2
            else b.2.1) r *
          selector r b.2.1 b.2.2)) total

/-- **One term's weight** under `weightAtK`, coefficient `1`. -/
def wSumK (L : StackLayout) (r : List E) (rm : Option (List E)) (pt point : List E) (column : Column)
    (twist : ℕ) : E :=
  if twist = ringTwist then
    ((L.limbs column).map fun b ↦ limbScale b.1 * (ringRow rm pt r b.2.1 * selector r b.2.1 b.2.2)).sum
  else
    ((L.limbs (slotViewK (qvOf L) column pt point).1).map fun b ↦ limbScale b.1 *
      (rowEq (slotViewK (qvOf L) column pt point).2.1
        (if (slotViewK (qvOf L) column pt point).2.2 > 0 then (slotViewK (qvOf L) column pt point).2.2
          else b.2.1) r *
        selector r b.2.1 b.2.2)).sum

theorem weightAtK_foldl (claim : Combined) (L : StackLayout) (r : List E) (rm : Option (List E)) :
    weightAtK claim L r rm = claim.terms.foldl (fun total x ↦
      wStepK L r rm (claim.points.toArray.getD x.2.1 [])
        (((twistedOf claim).getD x.2.1 #[]).getD x.2.2.1 []) total x.1 x.2.2.1 x.2.2.2) 0 := rfl

theorem wStepK_eq (L : StackLayout) (r : List E) (rm : Option (List E)) (pt point : List E) (total : E)
    (column : Column) (twist : ℕ) (c : E) :
    wStepK L r rm pt point total column twist c = total + c * wSumK L r rm pt point column twist := by
  unfold wStepK wSumK
  split_ifs <;>
  · rw [foldl_add_map, ← List.sum_map_mul_left]
    refine congrArg (total + ·) (congrArg List.sum (List.map_congr_left fun b _ ↦ ?_))
    rw [scale_eq, mul_assoc]

theorem wSumK_ring (L : StackLayout) (r : List E) (rm : Option (List E)) (pt point point' : List E)
    (column : Column) : wSumK L r rm pt point column ringTwist = wSumK L r rm pt point' column ringTwist := by
  simp only [wSumK, ite_true]

/-- **A one-term claim's weight** under `weightAtK`. -/
theorem weightAtK_single (L : StackLayout) (r : List E) (rm : Option (List E)) (pt : List E)
    (column : Column) (twist : ℕ) :
    weightAtK ⟨[pt], [(column, 0, twist, 1)], 0, 1⟩ L r rm =
      wSumK L r rm pt (twistPt pt twist) column twist := by
  rw [weightAtK_foldl, List.foldl_cons, List.foldl_nil, wStepK_eq, zero_add, one_mul, toArray_getD]
  by_cases htw : twist = ringTwist
  · subst htw
    exact wSumK_ring _ _ _ _ _ _ _
  · rw [twistedOf_getD _ (column, 0, twist, 1) (by simp) htw]
    rfl

/-- `termWK` is one term's weight at the cube point. -/
theorem termWK_eq (L : StackLayout) (rm : Option (List E)) (V : ℕ) (column : Column) (pt : List E)
    (twist u : ℕ) :
    termWK L rm V column pt twist u = wSumK L (bitsE u V) rm pt (twistPt pt twist) column twist :=
  weightAtK_single _ _ _ _ _ _

/-- **`weightAtK` is linear in its claim's terms**: the sum of each term's coefficient times the weight of the term
alone at its point. -/
theorem weightAtK_linear (claim : Combined) (L : StackLayout) (r : List E) (rm : Option (List E)) :
    weightAtK claim L r rm = (claim.terms.map fun tm ↦
      tm.2.2.2 * weightAtK ⟨[claim.points.getD tm.2.1 []], [(tm.1, 0, tm.2.2.1, 1)], 0, 1⟩ L r rm).sum := by
  rw [weightAtK_foldl, foldl_eq_sum_of _ (fun tm ↦ tm.2.2.2 * weightAtK ⟨[claim.points.getD tm.2.1 []],
    [(tm.1, 0, tm.2.2.1, 1)], 0, 1⟩ L r rm) _ _ ?_, zero_add]
  intro t x hx
  rw [wStepK_eq, weightAtK_single, toArray_getD]
  by_cases htw : x.2.2.1 = ringTwist
  · rw [htw, wSumK_ring _ _ _ _ _ (twistPt (claim.points.getD x.2.1 []) ringTwist)]
  · rw [twistedOf_getD claim x hx htw]

/-! ## One commitment, the batch -/

/-- **One commitment's product and value** on the Keccak VM: its combined claim's `weightAtK` against the
zero-extended stack, plus its value, is `Σ_i ρ^i` of its relations' differences. -/
theorem comm_startK (rels : List Relation) (c : Commitment) (ρ : E) (L : StackLayout)
    (rm : Option (List E)) (V : ℕ) (C : Stk) :
    ∑ u ∈ range (2 ^ V), weightAtK ((combine rels c ρ).getD zeroClaim) L (bitsE u V) rm * stE C L.vars u +
        ((combine rels c ρ).getD zeroClaim).value =
      powComb ((mine rels c).map (relDiffK L rm V C (mergedPoint (mine rels c)))) ρ := by
  by_cases hm : mine rels c = []
  · have hnone : combine rels c ρ = none := by
      unfold combine
      simp only [mine] at hm
      simp [hm]
    rw [hnone, hm]
    simp [weightAtK, powComb_nil, zeroClaim]
  · obtain ⟨cb, hcb, hv, hF⟩ := combineEq rels c ρ hm
    rw [hcb, Option.getD_some]
    have hw : ∀ u, weightAtK cb L (bitsE u V) rm =
        (cb.terms.map fun tm ↦ tm.2.2.2 * termWK L rm V tm.1 (cb.points.getD tm.2.1 []) tm.2.2.1 u).sum :=
      fun u ↦ weightAtK_linear cb L (bitsE u V) rm
    simp_rw [hw, ← sum_list_mul]
    rw [sum_range_list]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [hF (fun col pt tw ↦ ∑ u ∈ range (2 ^ V), termWK L rm V col pt tw u * stE C L.vars u), hv,
      ← List.sum_map_add, ← zipIdx_sum_zero]
    congr 1
    refine List.map_congr_left fun ri _ ↦ ?_
    simp only [relDiffK]
    ring

/-- **The Keccak batch's start** (`UniIdsK.batch_start`): `Σ_u g(u) + target` is the combination by `λ` of the
commitments' combinations by `ρ` of their relations' differences. -/
theorem batch_start_K (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E)
    (vals : List E) (ρ l : E) :
    (prodK D Fl s c1 ch fd c2 t vals ρ l).T [] + targetK D Fl s c1 ch fd c2 t vals ρ l =
      powComb ((diffsK D Fl s c1 ch fd c2 t vals).map fun d ↦ powComb d ρ) l := by
  unfold prodK targetK diffsK
  split_ifs with hg
  · have h0 := comm_startK (relsAtK D Fl s ch fd t vals) .c1 ρ (layoutOfK D.shape .c1)
      (ringMapAtK Fl fd) (batchVarsK D.shape) (stackForK D c1 c2 .c1)
    have h1 := comm_startK (relsAtK D Fl s ch fd t vals) .c2 ρ (layoutOfK D.shape .c2)
      (ringMapAtK Fl fd) (batchVarsK D.shape) (stackForK D c1 c2 .c2)
    have h2 := comm_startK (relsAtK D Fl s ch fd t vals) .setup ρ (layoutOfK D.shape .setup)
      (ringMapAtK Fl fd) (batchVarsK D.shape) (stackForK D c1 c2 .setup)
    simp only [ProdSum.T, List.length_nil, Nat.sub_zero, foldAll, List.foldl_nil,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add, commitments, List.map_cons,
      List.map_nil, powComb_cons, powComb_nil, mul_zero, add_zero]
    simp only [cm, combAtK, commitments, List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 ⊢
    rw [← h0, ← h1, ← h2]
    ring
  · simp [ProdSum.T, powComb_cons, powComb_nil]

end UniKeccakSound.Ids
