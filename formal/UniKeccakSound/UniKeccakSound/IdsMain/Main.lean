-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proofs are `UniSound/Ids/Main.lean`'s,
-- `Leaves.lean`'s, `MainOk.lean`'s and `BcTuple.lean`'s (`mainOfPolys`), for the Keccak VM's identities
-- (`polysK`) and heap (`hdK`).
import UniSound.Ids.MainOk
import UniSound.Ids.BcTuple
import UniKeccakSound.IdsMain.Cvec

/-!
# `MainOfPolysK`: the identities as polynomials give the heap and the constraint vectors

**`mainOfPolysK`**: where every polynomial of `polysK` is zero (so the counts are in range), the heap read off
`C1` (`hdK`) holds at `(α, β)` with `T` the committed heap at the points (`heapTK`: the tree from `treePK`, every
block's leaves from `blockPK` laid end to end at the heap's positions, the root from `rootPK`), and the constraint
vectors (`cvecK`) vanish on `V_{r_W}` (from `wPK`, `Z_bad ≠ 0`). The proofs are `UniSound`'s on the Keccak
layouts and tables: the tables' flushes by `tablesFactsK`, `C1`'s columns by `c1LimbsK`/`c1AbsentK`, the setup's
bytecode tuple by `UniSound.Ids.bcTuple_core`.

**Deployment hypotheses** (`MainDeployK`): the heap's layout (`HeapGood`), the coordinate functionals at `h_SHA3`
(`FunctionalsCorrect`), `2 ≤ h_SHA3`, `r_W ≤ 24`, every table's height `< 24`. All are decidable facts of a shape.
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak Finset Polynomial

/-- **The deployment's facts the reading of the heap rests on** (all decidable at a given shape). -/
structure MainDeployK (D : KDeployment) : Prop where
  heap : HeapGood D.shape
  functionals : FunctionalsCorrect (D.shape.heights.getD opSha3 0)
  height2 : 2 ≤ D.shape.heights.getD opSha3 0
  rW : D.shape.constraintVars ≤ 24
  heightsLt : ∀ o < 6, D.shape.heights.getD o 0 < 24

/-! ## The constraint vectors -/

/-- **The constraint vectors from the constraint identity.** -/
theorem cvec_of_wPK (D : KDeployment) (hf : FunctionalsCorrect (D.shape.heights.getD opSha3 0))
    (h2 : 2 ≤ D.shape.heights.getD opSha3 0) (hrW : D.shape.constraintVars ≤ 24)
    (c1 c2 : Stk) (s : USt) (γ p0 : E) (hfit : CountsFit D.shape s.2)
    (hW : wPK D.shape c1 c2 (publicWordsOf s.1.toList) γ p0 = 0) :
    ∀ x < 2 ^ D.shape.constraintVars, powComb (cvecK D c1 s x) γ = 0 := by
  intro x hx
  unfold wPK at hW
  have hin := (mul_eq_zero.mp hW).resolve_left (zBad_ne_zero D.shape betaCantor hf h2 p0)
  have hx24 : x < 2 ^ 24 := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hrW)
  have he := congrArg (Polynomial.eval (pointE x)) hin
  rw [Polynomial.eval_add, Polynomial.eval_mul, eval_digitP_pointE betaCantor _ hx24,
    show x >>> D.shape.constraintVars = 0 by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hx,
    pointE_zero, mul_zero, add_zero, eval_zero, eval_batched] at he
  unfold cvecK
  rw [ite_eq_left hfit]
  exact he

/-! ## The tree and the root -/

theorem c2PK_eval_congr (S : Shape) (c2 : Stk) (col : Column) (P P' : ℕ → Polynomial E) (x y : E)
    (h : ∀ l, (P l).eval x = (P' l).eval y) : (c2PK S c2 col P).eval x = (c2PK S c2 col P').eval y := by
  unfold c2PK
  exact colPoly_eval_congr (layoutOfK S .c2) (batchVarsK S) c2 col P P' x y h

/-- The heap's values at the points (`C2`'s `T`). -/
noncomputable def heapTK (S : Shape) (c2 : Stk) (i : ℕ) : E := (c2PK S c2 .heap digitP).eval (pointE i)

/-- **The tree from its identity.** -/
theorem tree_of_treePK (S : Shape) (c2 : Stk) (hh1 : 1 ≤ S.heap.h) (hh : S.heap.h ≤ 24)
    (ht : treePK S c2 = 0) : Heap.TreeHolds S.heap.h (heapTK S c2) := by
  have hq : ∀ x : E, QuotientSecurity.sq x * ((c2PK S c2 .heap digitP).eval (QuotientSecurity.sq x) +
      (c2PK S c2 .heap digitP).eval x * (c2PK S c2 .heap digitP).eval (x + 1)) +
      QuotientSecurity.sq^[S.heap.h] x * (c2PK S c2 (.treeQuotient 0) digitP +
        digitP S.heap.h * c2PK S c2 (.treeQuotient 1) digitP).eval x = 0 := by
    intro x
    have := congrArg (Polynomial.eval x) ht
    unfold treePK at this
    simp only [Polynomial.eval_add, Polynomial.eval_mul, eval_zero] at this
    rw [eval_digitP 1, eval_digitP S.heap.h,
      c2PK_eval_congr _ _ _ (fun l ↦ digitP (l + 1)) digitP x (QuotientSecurity.sq x)
        (fun l ↦ (digitP_eval_sq l x).symm),
      c2PK_eval_congr _ _ _ (fun l ↦ if l = 0 then digitP 0 + 1 else digitP l) digitP x (x + 1)
        (fun l ↦ (digitP_eval_add_one l x).symm)] at this
    rw [Function.iterate_one] at this
    rw [Polynomial.eval_add, Polynomial.eval_mul, eval_digitP]
    exact this
  have h1 := Heap.treeHolds_omega (cantorN betaCantor S.heap.h hh) hh1
    (T := fun x ↦ (c2PK S c2 .heap digitP).eval x)
    (Heap.tree_of_quotient (cantorN betaCantor S.heap.h hh) (T := fun x ↦ (c2PK S c2 .heap digitP).eval x)
      (Q := fun x ↦ (c2PK S c2 (.treeQuotient 0) digitP +
        digitP S.heap.h * c2PK S c2 (.treeQuotient 1) digitP).eval x)
      (fun x _ ↦ hq x))
  intro i hi2 hi
  have hj1 : i >>> 1 < 2 ^ S.heap.h :=
    lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) hi
  have hj2 : i ^^^ 1 < 2 ^ S.heap.h := Nat.xor_lt_two_pow hi (Nat.one_lt_two_pow (by omega))
  have := h1 i hi2 hi
  simp only at this
  unfold heapTK
  rwa [omega_cantorN betaCantor _ hh hj1, omega_cantorN betaCantor _ hh hi,
    omega_cantorN betaCantor _ hh hj2] at this

/-- **The root from its identity**: `T(1) fp(init) = fp(fin)`. -/
theorem root_of_rootPK (S : Shape) (c2 : Stk) (weights : Array E) (β : E)
    (hr : rootPK S c2 weights β = 0) : heapTK S c2 1 * rootInit weights β = rootFin S weights β := by
  have he := congrArg (Polynomial.eval 0) hr
  unfold rootPK at he
  rw [Polynomial.eval_add, Polynomial.eval_mul, eval_C, eval_C, eval_zero,
    c2PK_eval_congr _ _ _ (fun l ↦ if l = 0 then (1 : Polynomial E) else 0) digitP 0 1
      (fun l ↦ (digitP_eval_one l).symm)] at he
  have hp1 : pointE 1 = 1 := by
    rw [pointE_eq_omega betaCantor (by norm_num), Heap.omega_one (cantorE betaCantor) (by norm_num)]
  unfold heapTK
  rw [hp1, mul_comm]
  exact CharTwo.add_eq_zero.mp he

theorem fp_finKK (D : KDeployment) (ch : List E) :
    Heap.fp (fun i ↦ ch.getD i.val 0) (ch.getD 4 0) (finKK D) =
      rootFin D.shape (eqKernel (alphasOf ch)) (betaOf ch) := by
  rw [fp_eq eqKernelLagrange]
  unfold finKK rootFin betaOf sepState
  simp only [Vector.get_ofFn]
  rw [sum_fin16 (fun s ↦ (eqKernel (alphasOf ch)).getD s 0 *
    ofK (if s = 1 then toK (UniStatement.gpow (2 ^ D.shape.logBytecode - 1)) else if s < 3 then 1 else 0))]
  simp (config := {decide := true}) only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    ite_true, ite_false, UniSound.Ids.ofK_one, UniSound.Ids.ofK_zero, mul_one, mul_zero, add_zero]
  rw [gpowInK]
  ring

/-! ## `C1`'s and the setup's columns -/

/-- An absent column's polynomial is `0`, and its value. -/
theorem c1PK_eval_absent (D : KDeployment) (c : Stk) (col : Column) (v x : ℕ)
    (hl : (layoutOfK D.shape .c1).limbs col = []) :
    (c1PK D.shape c col).eval (pointE x) = ofK (c1ValK D c col v x) := by
  unfold c1PK colPoly c1ValK c1Block basisValue
  rw [hl, ← layoutOfK_c1, hl]
  simp [mleK_empty]

/-- A table column of `C1` at `ω_x`, present or absent. -/
theorem c1Col_evalK (D : KDeployment) (hrW : D.shape.constraintVars ≤ 24) (c : Stk) (o : ℕ) (ho : o < 6)
    (i x : ℕ) (hx : x < 2 ^ D.shape.heights.getD o 0) :
    (c1PK D.shape c (.table o i)).eval (pointE x) = ofK (c1RowK D c o x i) := by
  unfold c1RowK
  by_cases hi : i < (tablesKeccak.getD o default).width
  · obtain ⟨off, hl⟩ := (c1LimbsK D.shape).table o ho i hi
    exact c1PK_eval_pointE D c _ _ off x hl ((height_le_rW D.shape o).trans hrW) hx
  · exact c1PK_eval_absent D c _ _ x (c1AbsentK D.shape o ho i (by omega))

theorem tupleOffK_eq (D : KDeployment) (off : ℕ)
    (hl : (layoutOfK D.shape .setup).limbs .bytecodeTuple = [(0, D.shape.logBytecode + 4, off)]) :
    tupleOffK D = off := by
  unfold tupleOffK
  rw [setupLayout_eqK, hl]
  rfl

/-- **The setup's bytecode tuple at `(α, ω_x)`** (`BcTupleEval` on the Keccak setup): `Σ_s eq(α, s)` times slot
`s`'s value at instruction `x`. -/
theorem bcTupleEvalK (D : KDeployment) (hH : HeapGood D.shape) (ch : List E) (x : ℕ)
    (hx : x < 2 ^ D.shape.logBytecode) :
    (suPK D.shape (setupStkK D) .bytecodeTuple
        (fun l ↦ if l < 4 then C ((alphasOf ch).getD l 0) else digitP (l - 4))).eval (pointE x) =
      ∑ s : Fin 16, (eqKernel (alphasOf ch)).getD s.val 0 * ofK (slotValK D s.val x) := by
  obtain ⟨off, hl⟩ := (setupLimbsK D.shape).2
  have hb := setupAlignedK D.shape _ (limbs_mem_blocks (b := (0, D.shape.logBytecode + 4, off))
    (by rw [hl]; exact List.mem_singleton_self _))
  have hlb : D.shape.logBytecode ≤ 24 := (Eval.lbFits D.shape).trans hH.2.1
  have hV : (layoutOfK D.shape .setup).vars ≤ batchVarsK D.shape :=
    UniSound.layoutOf_vars_le (layoutsOfK D.shape) .setup
  unfold slotValK suPK
  rw [tupleOffK_eq D off hl]
  generalize setupStkK D = C
  exact bcTuple_core betaCantor _ _ C _ off x _ (Facts.alphasOf_length ch) hl hb.1 hb.2 hV hlb hx

/-! ## The blocks -/

theorem blockKK_r' (D : KDeployment) (c : Stk) (rows : List ℕ) (b : Block) : (blockKK D c rows b).r = b.r :=
  blockKK_r D c rows b

theorem fp_memTupleKK (D : KDeployment) (c : Stk) (ch : List E) (cnt : K) (x : ℕ) :
    Heap.fp (fun i ↦ ch.getD i.val 0) (ch.getD 4 0) (memTupleKK D c cnt x) =
      ch.getD 4 0 + wt ch 0 * ofK (toK sepMem) + wt ch 1 * ofK (suValK D .address D.shape.logMemory x) +
        wt ch 2 * ofK cnt + wt ch 3 * ofK (c1ValK D c (.memory 0) D.shape.logMemory x) +
        wt ch 4 * ofK (c1ValK D c (.memory 1) D.shape.logMemory x) +
        wt ch 5 * ofK (c1ValK D c (.memory 2) D.shape.logMemory x) := by
  rw [fp_eq eqKernelLagrange]
  unfold memTupleKK
  simp only [Vector.get_ofFn]
  rw [sum_fin16 (fun s ↦ wt ch s * ofK (if s = 0 then toK sepMem
    else if s = 1 then suValK D .address D.shape.logMemory x
    else if s = 2 then cnt
    else if s < 6 then c1ValK D c (.memory (s - 3)) D.shape.logMemory x else 0))]
  simp (config := {decide := true}) only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    ite_true, ite_false, UniSound.Ids.ofK_zero, mul_zero, add_zero, Nat.reduceSub]
  ring

theorem fp_bcTupleKK (D : KDeployment) (ch : List E) (cnt : K) (x : ℕ) :
    Heap.fp (fun i ↦ ch.getD i.val 0) (ch.getD 4 0) (bcTupleKK D cnt x) =
      ch.getD 4 0 + ∑ s : Fin 16, wt ch s.val * ofK (slotValK D s.val x) + wt ch 2 * ofK cnt := by
  rw [fp_eq eqKernelLagrange]
  unfold bcTupleKK
  simp only [Vector.get_ofFn, UniSound.Ids.ofK_add, mul_add, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 2
  rw [sum_fin16 (fun s ↦ wt ch s * ofK (if s = 2 then cnt else 0))]
  simp (config := {decide := true}) only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    ite_true, ite_false, UniSound.Ids.ofK_zero, mul_zero, add_zero]

section Blocks

variable (D : KDeployment) (hd : MainDeployK D) (c1 c2 : Stk) (s : USt) (ch : List E) (b : Block) (i : ℕ)

/-- The restriction at `ω_k`. -/
theorem restr_evalK (hal : 2 ^ b.r ∣ b.position) {k : ℕ} (hk : k < 2 ^ b.r)
    (hpk : b.position + k < 2 ^ 24) :
    (c2PK D.shape c2 .heap (mixP b)).eval (pointE k) = heapTK D.shape c2 (b.position + k) :=
  c2PK_eval_congr _ _ _ _ _ _ _ fun l ↦ mixP_eval_pointE betaCantor b hal hk hpk l

theorem hk_ofK (k : ℕ) (hk : k < (blockKK D c1 s.2 b).size) : k < 2 ^ b.r := by
  have := blockKK_r D c1 s.2 b
  simp only [Heap.LeafBlock.size, this] at hk
  exact hk

include hd in
/-- **A table's block from its leaf identity.** -/
theorem tableHoldsK (hfit : CountsFit D.shape s.2) (t : ℕ) (hb : b.leaves = .table t) (ht : t < 6)
    (hrb : b.r = D.shape.heights.getD t 0) (hal : 2 ^ b.r ∣ b.position) (hpos : b.position + 2 ^ b.r ≤ 2 ^ 24)
    (hP : blockPK D.shape c1 c2 (setupStkK D) s.2 (alphasOf ch) (betaOf ch) b i = 0) :
    (blockKK D c1 s.2 b).Holds (Heap.fp (fun j ↦ ch.getD j.val 0) (ch.getD 4 0)) (heapTK D.shape c2)
      b.position := by
  intro k hk
  have hbk : blockKK D c1 s.2 b = tableBlockKK D c1 s.2 b t := by unfold blockKK; rw [hb]
  rw [hbk]
  unfold blockPK at hP
  rw [hb] at hP
  simp only at hP
  rw [leaf_form] at hP
  have hk' : k < 2 ^ b.r := by
    have := blockKK_r D c1 s.2 b
    simp only [Heap.LeafBlock.size, this] at hk
    exact hk
  have hk24 : k < 2 ^ 24 := by omega
  have hw : (digitP b.r).eval (pointE k) = 0 := by
    rw [eval_digitP_pointE betaCantor _ hk24, pointE_shift_zero hk']
  have hw' : (derivative (digitP b.r)).eval (pointE k) = 1 := by rw [derivative_digitP, eval_one]
  have hR := restr_evalK D c2 b hal hk' (by omega)
  have hcols : ∀ j, (c1PK D.shape c1 (.table (tablesKeccak.getD t default).opcode j)).eval (pointE k) =
      ofK (c1RowK D c1 t k j) := by
    intro j
    rw [tablesKeccak_opcode t ht]
    exact c1Col_evalK D hd.rW c1 t ht j k (hrb ▸ hk')
  have hfacts := tablesFactsK _ (tablesKeccak_mem t ht)
  have hcount : s.2.getD t 0 ≤ 2 ^ b.r := hrb ▸ hfit.2 t ht
  have hZ := zActZero betaCantor (s.2.getD t 0) b.r k (hrb ▸ hd.heightsLt t ht) hcount hk'
  unfold tableBlockKK
  simp only
  by_cases ha : isActive k (s.2.getD t 0) b.r = true
  · simp only [ha, ite_true]
    have hA := active_of_leaf _ _ _ _ (pointE k) hP hw hw' (hZ.mpr ha)
    rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hZ.mpr ha,
      mul_zero, add_zero, hR, pullP_eval eqKernelLagrange _ hfacts.1 hfacts.2 _ _ _ hcols ch,
      pushP_eval eqKernelLagrange _ hfacts.1 hfacts.2 _ _ _ hcols ch] at hA
    exact CharTwo.add_eq_zero.mp hA
  · simp only [ha, Bool.false_eq_true, ite_false]
    have h1 := padding_of_leaf _ _ _ _ (pointE k) hP hw (fun h0 ↦ ha (hZ.mp h0))
    rw [hR] at h1
    simp [Heap.fpProd, h1]

include hd in
/-- **The memory's block from its leaf identity.** -/
theorem memHoldsK (hb : b.leaves = .memory) (hrb : b.r = D.shape.logMemory) (hal : 2 ^ b.r ∣ b.position)
    (hpos : b.position + 2 ^ b.r ≤ 2 ^ 24)
    (hP : blockPK D.shape c1 c2 (setupStkK D) s.2 (alphasOf ch) (betaOf ch) b i = 0) :
    (blockKK D c1 s.2 b).Holds (Heap.fp (fun j ↦ ch.getD j.val 0) (ch.getD 4 0)) (heapTK D.shape c2)
      b.position := by
  intro k hk
  have hk' := hk_ofK D c1 s b k hk
  have hk24 : k < 2 ^ 24 := by omega
  have hbk : blockKK D c1 s.2 b = Heap.LeafBlock.pair b.r (memTupleKK D c1 1)
      (fun x ↦ memTupleKK D c1 (c1ValK D c1 (.memory 3) D.shape.logMemory x) x) := by
    unfold blockKK; rw [hb]
  rw [hbk]
  show heapTK D.shape c2 (b.position + k) * Heap.fpProd _ [_] = Heap.fpProd _ [_]
  rw [fpProd_single, fpProd_single, fp_memTupleKK, fp_memTupleKK]
  unfold blockPK at hP
  rw [hb] at hP
  simp only at hP
  have he := congrArg (Polynomial.eval (pointE k)) hP
  have hlm : D.shape.logMemory ≤ 24 := (logMemory_le_rW D.shape).trans hd.rW
  have hkm : k < 2 ^ D.shape.logMemory := hrb ▸ hk'
  have hmem : ∀ j < 4, (c1PK D.shape c1 (.memory j)).eval (pointE k) =
      ofK (c1ValK D c1 (.memory j) D.shape.logMemory k) := fun j hj ↦ by
    obtain ⟨off, hl⟩ := (c1LimbsK D.shape).memory j hj
    exact c1PK_eval_pointE D c1 _ _ off k hl hlm hkm
  have haddr : (suPK D.shape (setupStkK D) .address digitP).eval (pointE k) =
      ofK (suValK D .address D.shape.logMemory k) := by
    obtain ⟨off, hl⟩ := (setupLimbsK D.shape).1
    have hbl := setupAlignedK D.shape _ (limbs_mem_blocks (b := (0, D.shape.logMemory, off))
      (by rw [hl]; exact List.mem_singleton_self _))
    have hV : (layoutOfK D.shape .setup).vars ≤ batchVarsK D.shape :=
      UniSound.layoutOf_vars_le (layoutsOfK D.shape) .setup
    unfold suPK
    rw [colPoly_eval_pointE betaCantor _ _ _ _ _ off k hl hbl.1 hbl.2 hV hlm hkm]
    unfold suValK c1Block
    rw [setupLayout_eqK, hl]
  simp only [memPullPK, Polynomial.eval_add, Polynomial.eval_mul, eval_C, eval_one, eval_zero,
    List.map_cons, List.map_nil, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.sum_cons, List.sum_nil, add_zero, Nat.reduceAdd] at he
  rw [eval_digitP_pointE betaCantor _ hk24, pointE_shift_zero hk', mul_zero, add_zero,
    restr_evalK D c2 b hal hk' (by omega), hmem 0 (by norm_num), hmem 1 (by norm_num),
    hmem 2 (by norm_num), hmem 3 (by norm_num), haddr] at he
  have hsep : ofK (toK sepMem) = sepMem := by
    unfold sepMem gen
    rw [eK_eq, toK_ofK]
  rw [hsep, UniSound.Ids.ofK_one]
  have h2 := UniSound.Ids.two_eq_zero_E
  unfold betaOf at he
  refine CharTwo.add_eq_zero.mp ?_
  linear_combination he + (-(wt ch 2 * ofK (c1ValK D c1 (.memory 3) D.shape.logMemory k))) * h2

include hd in
/-- **The bytecode's block from its leaf identity.** -/
theorem bcHoldsK (hb : b.leaves = .bytecode) (hrb : b.r = D.shape.logBytecode) (hal : 2 ^ b.r ∣ b.position)
    (hpos : b.position + 2 ^ b.r ≤ 2 ^ 24) (hlb : D.shape.logBytecode ≤ 24)
    (hP : blockPK D.shape c1 c2 (setupStkK D) s.2 (alphasOf ch) (betaOf ch) b i = 0) :
    (blockKK D c1 s.2 b).Holds (Heap.fp (fun j ↦ ch.getD j.val 0) (ch.getD 4 0)) (heapTK D.shape c2)
      b.position := by
  intro k hk
  have hk' := hk_ofK D c1 s b k hk
  have hk24 : k < 2 ^ 24 := by omega
  have hbk : blockKK D c1 s.2 b = Heap.LeafBlock.pair b.r (bcTupleKK D 1)
      (fun x ↦ bcTupleKK D (c1ValK D c1 .bytecodeFinal D.shape.logBytecode x) x) := by
    unfold blockKK; rw [hb]
  rw [hbk]
  show heapTK D.shape c2 (b.position + k) * Heap.fpProd _ [_] = Heap.fpProd _ [_]
  rw [fpProd_single, fpProd_single, fp_bcTupleKK, fp_bcTupleKK]
  unfold blockPK at hP
  rw [hb] at hP
  simp only at hP
  have he := congrArg (Polynomial.eval (pointE k)) hP
  have hkb : k < 2 ^ D.shape.logBytecode := hrb ▸ hk'
  have hbf : (c1PK D.shape c1 .bytecodeFinal).eval (pointE k) =
      ofK (c1ValK D c1 .bytecodeFinal D.shape.logBytecode k) := by
    obtain ⟨off, hl⟩ := (c1LimbsK D.shape).bytecodeFinal
    exact c1PK_eval_pointE D c1 _ _ off k hl hlb hkb
  simp only [bcPullPK, Polynomial.eval_add, Polynomial.eval_mul, eval_C, eval_one, eval_zero] at he
  rw [eval_digitP_pointE betaCantor _ hk24, pointE_shift_zero hk', mul_zero, add_zero,
    restr_evalK D c2 b hal hk' (by omega), hbf, bcTupleEvalK D hd.heap ch k hkb] at he
  rw [UniSound.Ids.ofK_one]
  have h2 := UniSound.Ids.two_eq_zero_E
  unfold betaOf at he
  refine CharTwo.add_eq_zero.mp ?_
  linear_combination he + (-(wt ch 2 * ofK (c1ValK D c1 .bytecodeFinal D.shape.logBytecode k))) * h2

/-- **An unused block from its identity.** -/
theorem unusedHoldsK (hb : b.leaves = .unused) (hal : 2 ^ b.r ∣ b.position)
    (hpos : b.position + 2 ^ b.r ≤ 2 ^ 24)
    (hP : blockPK D.shape c1 c2 (setupStkK D) s.2 (alphasOf ch) (betaOf ch) b i = 0) :
    (blockKK D c1 s.2 b).Holds (Heap.fp (fun j ↦ ch.getD j.val 0) (ch.getD 4 0)) (heapTK D.shape c2)
      b.position := by
  intro k hk
  have hk' := hk_ofK D c1 s b k hk
  have hbk : blockKK D c1 s.2 b = Heap.LeafBlock.unused b.r := by unfold blockKK; rw [hb]
  rw [hbk]
  unfold blockPK at hP
  rw [hb] at hP
  simp only at hP
  have he := congrArg (Polynomial.eval (pointE k)) hP
  rw [Polynomial.eval_add, eval_one, eval_zero, restr_evalK D c2 b hal hk' (by omega)] at he
  simp [Heap.LeafBlock.unused, Heap.fpProd, CharTwo.add_eq_zero.mp he]

end Blocks

/-! ## The identities as polynomials -/

/-- **The identities as polynomials give the heap and the constraint vectors** (`MainOfPolysK`). -/
theorem mainOfPolysK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (hd : MainDeployK D) : MainOfPolysK D Fl := by
  intro s c1 ch fd c2 hP
  by_cases hfit : CountsFit D.shape s.2
  swap
  · exfalso
    exact one_ne_zero (hP 1 (by unfold polysK; rw [ite_eq_right hfit]; exact List.mem_singleton_self _))
  have hpol : polysK D Fl s c1 ch fd c2 =
      [treePK D.shape c2, rootPK D.shape c2 (eqKernel (alphasOf ch)) (betaOf ch),
        wPK D.shape c1 c2 (publicWordsOf s.1.toList) (gammaOf ch) ((Fl.prog.out fd []).1.getD 0 0)] ++
      (D.shape.heap.blocks.zip (List.range D.shape.heap.blocks.length)).map fun bi ↦
        blockPK D.shape c1 c2 (setupStkK D) s.2 (alphasOf ch) (betaOf ch) bi.1 bi.2 := by
    unfold polysK; rw [ite_eq_left hfit]
  have htree : treePK D.shape c2 = 0 := hP _ (by rw [hpol]; simp)
  have hroot : rootPK D.shape c2 (eqKernel (alphasOf ch)) (betaOf ch) = 0 := hP _ (by rw [hpol]; simp)
  have hW : wPK D.shape c1 c2 (publicWordsOf s.1.toList) (gammaOf ch) ((Fl.prog.out fd []).1.getD 0 0) = 0 :=
    hP _ (by rw [hpol]; simp)
  have hblk : ∀ i (hi : i < D.shape.heap.blocks.length),
      blockPK D.shape c1 c2 (setupStkK D) s.2 (alphasOf ch) (betaOf ch) D.shape.heap.blocks[i] i = 0 :=
    fun i hi ↦ hP _ (by
      rw [hpol]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨_, mem_zip_range _ i hi, rfl⟩))
  have hg := hd.heap
  refine ⟨⟨heapTK D.shape c2, ⟨tree_of_treePK D.shape c2 hg.1 hg.2.1 htree, ?_, ?_⟩⟩,
    cvec_of_wPK D hd.functionals hd.height2 hd.rW c1 c2 s (gammaOf ch) _ hfit hW⟩
  · -- the leaves
    show Heap.LeavesHold _ _ (2 ^ (D.shape.heap.h - 1)) (D.shape.heap.blocks.map (blockKK D c1 s.2))
    refine leavesHold_of _ _ _ _ (fun i ↦ (D.shape.heap.blocks.getD i default).position) (fun i hi ↦ ?_)
      (fun i hi ↦ ?_)
    · rw [List.length_map] at hi
      rw [hg.2.2.2.1 i hi, ← List.map_take, List.map_map]
      congr 2
      refine List.map_congr_left fun b _ ↦ ?_
      simp [Heap.LeafBlock.size, blockKK_r]
    · rw [List.length_map] at hi
      rw [List.getElem_map, List.getD_eq_getElem _ _ hi]
      have hb : D.shape.heap.blocks[i] ∈ D.shape.heap.blocks := List.getElem_mem hi
      have h1 := hg.2.2.2.1 i hi
      rw [List.getD_eq_getElem _ _ hi] at h1
      have h2 := sum_take_succ_le (D.shape.heap.blocks.map fun b ↦ 2 ^ b.r) i (by simpa using hi)
      rw [← List.map_take, List.getElem_map, hg.2.2.1] at h2
      have h3 : 2 ^ (D.shape.heap.h - 1) + 2 ^ (D.shape.heap.h - 1) ≤ 2 ^ 24 := by
        rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hg.1]
        exact Nat.pow_le_pow_right (by norm_num) hg.2.1
      have hP := hblk i hi
      generalize D.shape.heap.blocks[i] = b at hb h1 h2 hP ⊢
      have hal := hg.2.2.2.2.1 b hb
      have hpos : b.position + 2 ^ b.r ≤ 2 ^ 24 := by rw [h1]; omega
      have hkind := hg.2.2.2.2.2 b hb
      rcases hlv : b.leaves with _ | _ | t | _
      · rw [hlv] at hkind
        exact memHoldsK D hd c1 c2 s ch b i hlv hkind hal hpos hP
      · rw [hlv] at hkind
        have hlb : D.shape.logBytecode ≤ 24 := by
          have : 2 ^ b.r ≤ 2 ^ 24 := by omega
          rw [← hkind]
          exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
        exact bcHoldsK D hd c1 c2 s ch b i hlv hkind hal hpos hlb hP
      · rw [hlv] at hkind
        exact tableHoldsK D hd c1 c2 s ch b i hfit t hlv hkind.1 hkind.2 hal hpos hP
      · exact unusedHoldsK D c1 c2 s ch b i hlv hal hpos hP
  · -- the root
    show heapTK D.shape c2 1 * Heap.fp _ _ initK = Heap.fp _ _ (finKK D)
    rw [fp_initK eqKernelLagrange, fp_finKK D]
    exact root_of_rootPK D.shape c2 _ _ hroot

end UniKeccakSound.Ids

/-- info: 'UniKeccakSound.Ids.mainOfPolysK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.Ids.mainOfPolysK
