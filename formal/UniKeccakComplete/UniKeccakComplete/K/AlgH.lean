-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/AlgH.lean`.
import UniKeccakComplete.K.AlgHRelD

/-!
# The honest prover's heap on `C2` (milestone 4, layer AlgH)

The headline facts of the heap's layer, for a placed trace `tr`, bus challenges `α` (`eqKernel α` the weights),
`β` and a heap of height `h ≤ 28` (the statement's transform, `PcsQuotient.Domain.coefficients`, has `28` basis
vectors; at a deployable shape `C2`'s `2^28` words bound `h` lower):

1. **The polynomial identities** (`Polynomial E`, through CompPoly's `toPoly`, `AlgHPoly`):
   * `treeQuotient_exact_fits` (any trace): the heap's values are a product tree (`heapValues_tree`), so
     `w_h ∣ w_1 (T(s(X)) + T(X) T(X + 1))` and the tree quotient has degree `≤ 2^h`, its chunks `[h, 0]`;
     `X_k(s(x)) = X_{2k}(x)`, `X_k(x + 1) = X_k(x) + X_{k−1}(x)` for odd `k` (`tp_ofNovel_compSNovel`,
     `tp_ofNovel_shiftOneNovel`);
   * **the root** `heap_root` (`TraceHonest`, `¬ BadFp`): `T_1 · fp(SEP_STATE, 1, 1) = fp(SEP_STATE, g^(2^lb − 1), 1)`
     from the bus's permutation;
   * **every used block's leaf quotient** (`TraceHonest`, `¬ BadFp`): exact (`leafQuotient_exact`) and fitting
     `chunks (d + 1)`, `d` its `Shape.leafDegreeK` (`leafQuotient_fits`, under `RowsFit`, every height: **every honest
     run fits**).
2. **The heap's relations hold** (`heapRelations_hold`, `atTOf_heap_holds`): at any `t`, every relation
   `heapRelations` states, at the layouts the verifier states, which are `layoutsOfK` (`atTOf_c2Columns_eq`: the
   verifier's `C2` columns are `Shape.c2ColumnsK`).

The layout facts (`layoutOK_new`, `used_perm`) and the restriction to a coset (`mle_mixed`) hold at every shape.
-/

namespace UniKeccakComplete.AlgH

open UniComplete

open Polynomial UniStatement UniKeccak LeanVM.Parameters
open UniComplete.Domain (wP)

/-- **The tree quotient is exact and fits its chunks `[h, 0]`** (any trace, any weights; `h ≤ 28`). -/
theorem treeQuotient_exact_fits (tr : Trace) (weights : Array E) (beta : E) (hH : tr.shape.heap.h ≤ 28) :
    tp (treeNumerator tr.shape.heap.h (novelOfValuesE tr.shape.heap.h (heapValues tr weights beta))) =
        wP tr.shape.heap.h *
          tp (treeQuotient tr.shape.heap.h (novelOfValuesE tr.shape.heap.h (heapValues tr weights beta))) ∧
      (tp (treeQuotient tr.shape.heap.h (novelOfValuesE tr.shape.heap.h (heapValues tr weights beta)))).natDegree <
        ([tr.shape.heap.h, 0].map (2 ^ ·)).sum := by
  have hL := layoutOK_new tr.shape.logMemory tr.shape.logBytecode tr.shape.heights
  exact ⟨treeNumerator_eq_mul hL.one_le hH (heapValues_size' tr weights beta) (heapValues_tree tr weights beta hL),
    natDegree_treeQuotient_lt hL.one_le _⟩

/-- **`h ≤ 28` when `C2` fits WHIR's `2^28` words** (the heap's three limbs are blocks of `C2`'s stack; in fact then
`h ≤ 26`): the hypothesis `h ≤ 28` of the layer is the openings'. -/
theorem heap_h_le_of_c2 (shape : UniStatement.Shape) (hvars : (((layoutsOfK shape).lookup .c2).getD default).vars ≤ 28) :
    shape.heap.h ≤ 28 := by
  rw [c2Layout_eq] at hvars
  have hnd := c2Names_nodup shape
  have hmem := mem_c2_heap shape
  have hperm := AlgC.limbs_map_new (List.count_eq_one_of_mem hnd (List.mem_map_of_mem hmem))
    (fun p hp hp1 ↦ by rw [List.inj_on_of_nodup_map hnd hp hmem hp1])
  have h0 : (0, shape.heap.h) ∈ ((StackLayout.new (Shape.c2ColumnsK shape)).limbs .heap).map
      (fun b ↦ (b.1, b.2.1)) := hperm.mem_iff.mpr (by simp)
  obtain ⟨b, hb, hbe⟩ := List.mem_map.mp h0
  have hin := AlgC.blocks_inRange _ _ (AlgC.mem_limbs.mp hb)
  simp only [Prod.mk.injEq] at hbe
  have h2 : 2 ^ shape.heap.h ≤ 2 ^ (StackLayout.new (Shape.c2ColumnsK shape)).vars := by
    rw [← hbe.2]; simp only at hin; omega
  have := (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  omega

end UniKeccakComplete.AlgH

/-! ### Axioms -/

/-- info: 'UniKeccakComplete.AlgH.heap_h_le_of_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.heap_h_le_of_c2

/-- info: 'UniKeccakComplete.AlgH.treeQuotient_exact_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.treeQuotient_exact_fits

/-- info: 'UniKeccakComplete.AlgH.heapValues_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.heapValues_tree

/-- info: 'UniKeccakComplete.AlgH.tp_ofNovel_compSNovel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.tp_ofNovel_compSNovel

/-- info: 'UniKeccakComplete.AlgH.tp_ofNovel_shiftOneNovel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.tp_ofNovel_shiftOneNovel

/-- info: 'UniKeccakComplete.AlgH.heap_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.heap_root

/-- info: 'UniKeccakComplete.AlgH.leafNumerator_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.leafNumerator_eval

/-- info: 'UniKeccakComplete.AlgH.leafQuotient_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.leafQuotient_exact

/-- info: 'UniKeccakComplete.AlgH.leafQuotient_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.leafQuotient_fits

/-- info: 'UniKeccakComplete.AlgH.table_degree_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.table_degree_arith

/-- info: 'UniKeccakComplete.AlgH.layoutOK_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.layoutOK_new

/-- info: 'UniKeccakComplete.AlgH.used_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.used_perm

/-- info: 'UniKeccakComplete.AlgH.mle_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.mle_mixed

/-- info: 'UniKeccakComplete.AlgH.atTOf_c2Columns_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.atTOf_c2Columns_eq

/-- info: 'UniKeccakComplete.AlgH.heapRelations_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.heapRelations_hold

/-- info: 'UniKeccakComplete.AlgH.atTOf_heap_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.AlgH.atTOf_heap_holds
