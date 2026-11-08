-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Ported from `formal/UniSound`'s `Ids/Weights.lean`
-- (`slotView`, `wStep`, `wSum`, `weightAt_foldl`, `wStep_eq`, `weightAt_single`, `weightAtLinear`) to
-- `UniKeccak.weightAtK`, whose slot terms read `q_flock`'s variables minus their point's as slot bits.
import UniSound.Ids.Weights
import UniKeccak.Verifier

/-!
# `UniKeccak.weightAtK` term by term

`weightAtK` is `UniStatement.weightAt` but for a `q_flock` slot term's slot bits: `q_flock`'s variables (`qvOf L`)
minus its point's, not `8`. As `UniSound.Ids.Weights` does for `weightAt`: its fold (`weightAtK_foldl`, by `rfl`), one
term's step (`wStepK_eq`), a one-term claim's weight (`weightAtK_single`), and **`weightAtK_linear`**: the weight is
linear in the claim's terms, each read at its own point.
-/

namespace RecGraphKeccak.Sim

open LeanVM.Parameters UniStatement
open UniSound.Ids (limbScale)
open UniSound.Ids.Weights (twistPt ringRow maxTwistOf twistedOf scale_eq toArray_getD twistedOf_getD foldl_add_map
  foldl_eq_sum_of twistedPoints_getD)

/-- `q_flock`'s variables at a layout, as `weightAtK` reads them. -/
def qvOf (L : StackLayout) : ℕ := ((L.limbs .qflock).head?.map (·.2.1)).getD 0

/-- `weightAtK`'s view of a term's column (`pt` its point, `point` its twisted point): `q_flock`'s slot `j` reads
`q_flock` at `(bits(j), point)`, its `qv − |pt|` slot bits then the point; another column itself at the point. -/
def slotViewK (qv : ℕ) (pt : List E) (column : Column) (point : List E) : Column × List E × ℕ :=
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
    (L.limbs (slotViewK (qvOf L) pt column point).1).foldl (fun total b ↦ total +
      (if b.1 = 0 then coefficient else coefficient * limbBasis.getD b.1 0) *
        (rowEq (slotViewK (qvOf L) pt column point).2.1
          (if (slotViewK (qvOf L) pt column point).2.2 > 0 then (slotViewK (qvOf L) pt column point).2.2
            else b.2.1) r *
          selector r b.2.1 b.2.2)) total

/-- **One term's weight**, coefficient `1`. -/
def wSumK (L : StackLayout) (r : List E) (rm : Option (List E)) (pt point : List E) (column : Column)
    (twist : ℕ) : E :=
  if twist = ringTwist then
    ((L.limbs column).map fun b ↦ limbScale b.1 * (ringRow rm pt r b.2.1 * selector r b.2.1 b.2.2)).sum
  else
    ((L.limbs (slotViewK (qvOf L) pt column point).1).map fun b ↦ limbScale b.1 *
      (rowEq (slotViewK (qvOf L) pt column point).2.1
        (if (slotViewK (qvOf L) pt column point).2.2 > 0 then (slotViewK (qvOf L) pt column point).2.2
          else b.2.1) r *
        selector r b.2.1 b.2.2)).sum

theorem weightAtK_foldl (claim : Combined) (L : StackLayout) (r : List E) (rm : Option (List E)) :
    UniKeccak.weightAtK claim L r rm = claim.terms.foldl (fun total x ↦
      wStepK L r rm (claim.points.toArray.getD x.2.1 [])
        (((twistedOf claim).getD x.2.1 #[]).getD x.2.2.1 []) total x.1 x.2.2.1 x.2.2.2) 0 := by
  unfold UniKeccak.weightAtK
  rfl

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

/-- **A one-term claim's weight.** -/
theorem weightAtK_single (L : StackLayout) (r : List E) (rm : Option (List E)) (pt : List E)
    (column : Column) (twist : ℕ) :
    UniKeccak.weightAtK ⟨[pt], [(column, 0, twist, 1)], 0, 1⟩ L r rm =
      wSumK L r rm pt (twistPt pt twist) column twist := by
  rw [weightAtK_foldl, List.foldl_cons, List.foldl_nil, wStepK_eq, zero_add, one_mul, toArray_getD]
  by_cases htw : twist = ringTwist
  · subst htw
    exact wSumK_ring _ _ _ _ _ _ _
  · rw [twistedOf_getD _ (column, 0, twist, 1) (by simp) htw]
    rfl

/-- **`weightAtK` is linear in its claim's terms.** -/
theorem weightAtK_linear (claim : Combined) (L : StackLayout) (r : List E) (rm : Option (List E)) :
    UniKeccak.weightAtK claim L r rm = (claim.terms.map fun tm ↦
      tm.2.2.2 * UniKeccak.weightAtK ⟨[claim.points.getD tm.2.1 []], [(tm.1, 0, tm.2.2.1, 1)], 0, 1⟩ L r rm).sum := by
  rw [weightAtK_foldl, foldl_eq_sum_of _ (fun tm ↦ tm.2.2.2 * UniKeccak.weightAtK ⟨[claim.points.getD tm.2.1 []],
    [(tm.1, 0, tm.2.2.1, 1)], 0, 1⟩ L r rm) _ _ ?_, zero_add]
  intro t x hx
  rw [wStepK_eq, weightAtK_single, toArray_getD]
  by_cases htw : x.2.2.1 = ringTwist
  · rw [htw, wSumK_ring _ _ _ _ _ (twistPt (claim.points.getD x.2.1 []) ringTwist)]
  · rw [twistedOf_getD claim x hx htw]

end RecGraphKeccak.Sim
