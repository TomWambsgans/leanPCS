-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The weight is `formal/UniKeccak`'s `weightAtK`; the
-- proofs are `UniSound/Ids/Weights.lean`'s (`slotInner`) and `UniSound/Ids/Eval.lean`'s (`inner_colPoly`,
-- `inner_slot`), for `weightAtK`'s `11` slot bits.
import UniKeccakSound.Ids.Batch
import UniSound.Ids.Eval

/-!
# A Keccak term's inner product on the cube is its column's polynomial at `t`

`weightAtK` is `weightAt` but for a `q_flock` slot term, which reads `q_flock`'s variables minus its point's as slot
bits (`11` on the Keccak VM, `8` for `weightAt`):

* **`termWK_eq_termW`**: on every column but a slot, `termWK` is `termW`, so `UniSound`'s lemmas apply
  (`inner_colPolyK` from `UniSound.Ids.Eval.inner_colPoly`);
* **`slotInnerK`**, **`inner_slotK`**: a slot `j` at a point `y` of `q_flock`'s variables minus `11` reads `q_flock` at
  `(bits(j), y)`, its claim the column's polynomial at `(bits(j), Y(t))`.
-/

namespace UniKeccakSound.IdsEval

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.Weights UniKeccak UniKeccakSound.Ids Finset
  Polynomial

theorem slotViewK_of_ne {column : Column} (h : ∀ j, column ≠ .qflockSlot j) (qv : ℕ) (pt point : List E) :
    slotViewK qv column pt point = (column, point, 0) := by
  unfold slotViewK
  split
  · rename_i j
    exact absurd rfl (h j)
  · rfl

/-- **On every column but a slot, `termWK` is `termW`.** -/
theorem termWK_eq_termW (L : StackLayout) (rm : Option (List E)) (V : ℕ) (col : Column) (pt : List E)
    (tw u : ℕ) (hcol : ∀ j, col ≠ .qflockSlot j) : termWK L rm V col pt tw u = termW L rm V col pt tw u := by
  rw [termWK_eq, termW_eq]
  unfold wSumK wSum
  simp only [slotViewK_of_ne hcol, slotView_of_ne hcol]

/-- **A column's term at a merged point** (not a slot): `inner_colPoly` for `termWK`. -/
theorem inner_colPolyK (L : StackLayout) (rm : Option (List E)) (V : ℕ) (St : Stk) (col : Column)
    (p q : List E) (t : E) (P : ℕ → Polynomial E)
    (hcol : ∀ j, col ≠ .qflockSlot j) (hq : q.take p.length = p)
    (hb : ∀ b ∈ L.limbs col, b.2.1 ≤ p.length ∧ b.2.1 ≤ V)
    (hP : ∀ b ∈ L.limbs col, ∀ l < b.2.1, (P l).eval t = p.getD l 0) :
    ∑ u ∈ range (2 ^ V), termWK L rm V col q 0 u * stE St L.vars u = (colPoly L V St col P).eval t := by
  simp only [termWK_eq_termW L rm V col q 0 _ hcol]
  exact Eval.inner_colPoly L rm V St col p q t P hcol hq hb hP

/-- **`q_flock`'s slot `j` on the cube** under `weightAtK`: its claim on `q_flock`'s blocks at `(bits(j), pt)`, `11`
slot bits. -/
theorem slotInnerK (L : StackLayout) (rm : Option (List E)) (V : ℕ) (C : Stk) (j : ℕ) (pt : List E)
    (hL : ∀ b ∈ L.limbs .qflock, b.2.1 = qflockRowBits + pt.length ∧ b.2.1 ≤ V)
    (hq : qvOf L = qflockRowBits + pt.length) :
    ∑ u ∈ range (2 ^ V), termWK L rm V (.qflockSlot j) pt 0 u * stE C L.vars u =
      ((L.limbs .qflock).map fun b ↦ limbScale b.1 *
        ∑ x ∈ range (2 ^ b.2.1), cubeEq ((List.range qflockRowBits).map (bitE j) ++ pt) b.2.1 x *
          stE C L.vars (blockBase b.2.2 b.2.1 V + x)).sum := by
  have h : ∀ u, termWK L rm V (.qflockSlot j) pt 0 u = ((L.limbs .qflock).map fun b ↦
      limbScale b.1 * (rowEq ((List.range qflockRowBits).map (bitE j) ++ pt) b.2.1 (bitsE u V) *
        selector (bitsE u V) b.2.1 b.2.2)).sum := by
    intro u
    have h0 : twistPt pt 0 = pt := rfl
    rw [termWK_eq, wSumK, ite_eq_right zero_ne_ringTwist, h0]
    refine congrArg List.sum (List.map_congr_left fun b hb ↦ ?_)
    have hlen : ((List.range qflockRowBits).map (bitE j) ++ pt).length = b.2.1 := by
      rw [(hL b hb).1]
      simp
    simp only [slotViewK, hq, Nat.add_sub_cancel, hlen, gt_iff_lt, ite_self]
  have hw : ∀ b ∈ L.limbs .qflock, ∀ x < 2 ^ b.2.1,
      rowEq ((List.range qflockRowBits).map (bitE j) ++ pt) b.2.1 (bitsE (blockBase b.2.2 b.2.1 V + x) V) =
        cubeEq ((List.range qflockRowBits).map (bitE j) ++ pt) b.2.1 x := by
    intro b hb x hx
    rw [rowEq_bits _ _ _ _ (hL b hb).2, cubeEq_block _ _ _ _ _ hx]
  simp only [h]
  exact cube_sum V L.vars C (L.limbs .qflock) (fun b hb ↦ (hL b hb).2)
    (fun b u ↦ rowEq ((List.range qflockRowBits).map (bitE j) ++ pt) b.2.1 (bitsE u V))
    (fun b x ↦ cubeEq ((List.range qflockRowBits).map (bitE j) ++ pt) b.2.1 x) hw

/-- **`q_flock`'s slot `j` at its own point `y`** under `weightAtK`: the slot's claim at `(bits(j), y)`, the
column's polynomial at `(bits(j), Y(t))`. -/
theorem inner_slotK (L : StackLayout) (rm : Option (List E)) (V : ℕ) (St : Stk) (j : ℕ) (y : List E)
    (t : E) (Y : ℕ → Polynomial E)
    (hb : ∀ b ∈ L.limbs .qflock, b.2.1 = qflockRowBits + y.length ∧ b.2.1 ≤ V)
    (hq : qvOf L = qflockRowBits + y.length)
    (hY : ∀ m < y.length, (Y m).eval t = y.getD m 0) :
    ∑ u ∈ range (2 ^ V), termWK L rm V (.qflockSlot j) y 0 u * stE St L.vars u =
      (colPoly L V St .qflock fun l ↦
        if l < qflockRowBits then Polynomial.C (bitE j l) else Y (l - qflockRowBits)).eval t := by
  rw [slotInnerK L rm V St j y hb hq]
  unfold colPoly
  rw [eval_listSum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun b hbm ↦ ?_)
  simp only [Function.comp_apply, Polynomial.eval_mul, eval_C]
  rw [eval_mlP _ _ _ t ((List.range qflockRowBits).map (bitE j) ++ y)]
  intro l hl
  rw [(hb b hbm).1] at hl
  by_cases h8 : l < qflockRowBits
  · rw [ite_eq_left h8, eval_C, List.getD_append _ _ _ _ (by simpa using h8), getD_map_range _ h8]
  · rw [ite_eq_right h8, List.getD_append_right _ _ _ _ (by simp; omega), List.length_map, List.length_range,
      hY _ (by omega)]

end UniKeccakSound.IdsEval
