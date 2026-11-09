-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/CoreBatch.lean`.
import UniKeccakComplete.K.SyncVerifier
import UniKeccakComplete.K.BatchProof
import UniKeccakComplete.K.Combine
import UniKeccakComplete.K.AlgCSome
import UniKeccakComplete.K.AlgH
import UniKeccakComplete.K.FlockProverMain
import UniKeccakComplete.K.ProbHyp

/-!
# The honest batch's hypotheses at the prover's front state (milestone 4, completeness), Keccak VM

At the reference shape (`keccakRefShape`), for an honest trace, the prover's state when the batching sumcheck
starts (`frontOf`, with Flock's honest prover `FlockP.flockProve` on the Keccak-f block) satisfies `BatchHolds`
(`batchHolds_front`), unless a bad event on the challenges happened: `BadFp` (a divided fingerprint vanishes at
`α, β`) or `BadT` (`y(t)` a proper prefix of another point on `C1`). So the batching sumcheck synchronises with the
verifier and its terminal is zero (`batchSyncsAt_front`).

* **The stacks' sizes** (`c1Stack_size`, `c2Stack_size`, `setupStackOf_size`): `2^27`, `2^26`, `2^23` words.
* **Flock's output** (`FlockProverMain`): its point has `h_SHA3 + 11` coordinates (`flock_point_length_trace`), it
  ends with a ring switch of six stages whose target is the ring identity (`flockRingSum`). The Keccak verifier has
  no pending matrices, so `BatchHolds` has only the combined claims.
* **The slot condition** (`slotCondition_of_badT`): `¬ BadT` is `AtTSlotCondition` (at the reference shape
  `|y| = 15 < 20 = log_m ≤ |w|` and `|y| < h_SHA3 + 11`).
* **`C2`'s terms cover their columns** (`atTOf_coversC2`): the relations off the heap have no `C2` term
  (`offHeap_offC2`), every heap term's column is listed in `c2Columns` at a size its point covers once that
  size is at most `|w|` (`heap_terms_cover`), the names are distinct (`AlgH.c2Names_nodup`) and `C2`'s blocks have
  at most `26 ≤ |w|` variables at the reference shape.
* **Every relation holds** (`relations_hold_front`): off `C2` by `AlgC.relations_hold_some_reference`, the heap's by
  `AlgH.heapRelations_hold`, the ring switch's by Flock's ring identity (`FlockP.flockRingSum`, `ringRel_holds`).

Decision (recorded): no term whose type is `FlockP.FlockRingHolds` of the prover's concrete output is ever
elaborated (its `match` on the output's end makes the elaborator evaluate Flock's prover symbolically);
`FlockP.flockRingSum` states the same fact unfolded.
-/

namespace UniKeccakComplete.Core

open UniComplete

open UniStatement UniKeccak LeanVM.Parameters LeanVM.Protocol Finset
open UniKeccakSound (keccakRefShape)

/-! ## The stacks' sizes -/

theorem foldl_size_K {α : Type} (F : Array K → α → Array K) (hF : ∀ s a, (F s a).size = s.size) :
    ∀ (l : List α) (s : Array K), (l.foldl F s).size = s.size
  | [], _ => rfl
  | a :: l, s => by rw [List.foldl_cons, foldl_size_K F hF l, hF]

/-- **A placed stack has `2^vars` words**, whatever its layout. -/
theorem placeStack_size' (layout : StackLayout) (data : Column → ℕ → Array K) :
    (placeStack layout data).size = 2 ^ layout.vars := by
  unfold placeStack
  refine (foldl_size_K _ ?_ _ _).trans (Array.size_replicate ..)
  intro s b
  obtain ⟨c, l, v, o⟩ := b
  exact foldl_size_K _ (fun s i ↦ by simp) _ _

/-- **`C1`'s stack has `2^27` words** at the reference shape. -/
theorem c1Stack_size (tr : Trace) (href : tr.shape = keccakRefShape) : (c1Stack tr).size = 2 ^ 27 := by
  unfold c1Stack
  rw [placeStack_size', href, show (c1LayoutK keccakRefShape).vars = 27 from reference_c1Vars]

/-- **`C2`'s stack has `2^26` words** at the reference shape. -/
theorem c2Stack_size (tr : Trace) (href : tr.shape = keccakRefShape) (weights : Array E) (beta gamma : E) :
    (c2DataOf tr weights beta gamma).stack.size = 2 ^ 26 := by
  rw [AlgH.c2Stack_eq, placeStack_size', href, reference_c2Vars]

/-- **The setup's stack has `2^23` words** at the reference shape. -/
theorem setupStackOf_size (tr : Trace) (href : tr.shape = keccakRefShape) : (setupStackOf tr).size = 2 ^ 23 := by
  obtain ⟨⟨o₁, h₁, -⟩, ⟨o₂, h₂, -⟩⟩ := AlgC.setup_limbs tr.shape
  have h : (setupStackOf tr).size = 2 ^ (setupLayout tr.shape).vars := by
    unfold setupStackOf
    simp only [h₁, h₂, List.headD_cons]
    exact Array.size_ofFn
  rw [h, href, show (setupLayout keccakRefShape).vars = 23 from reference_setupVars]

/-! ## The slot condition from `¬ BadT` -/

theorem reference_logMemory : keccakRefShape.logMemory = 20 := by decide +kernel

theorem reference_sha3Height : keccakRefShape.heights.getD opSha3 0 = 15 := by
  rw [reference_heights]
  rfl

/-- **`¬ BadT` gives the slot condition** at the reference shape: `y(t)` (`15` coordinates) is a prefix neither of
`w(t)` (else a proper prefix of `w(t).take 20`) nor of Flock's point (of at least `26` coordinates). -/
theorem slotCondition_of_badT (tr : Trace) (href : tr.shape = keccakRefShape) (t : E) (out : FlockOut)
    (hpt : tr.shape.heights.getD opSha3 0 + 11 ≤ out.point.length)
    (hbad : ¬ Prob.BadT keccakRefShape out.point t) :
    AtTSlotCondition (digits t (max tr.shape.heap.h (tr.shape.constraintVars + 4) + 2))
      (coordinatesAt t (coordinateFunctionals (tr.shape.heights.getD opSha3 0))) (some out) := by
  rw [href] at hpt ⊢
  have hy : (coordinatesAt t (coordinateFunctionals (keccakRefShape.heights.getD opSha3 0))).length = 15 := by
    rw [length_coordinatesAt, reference_sha3Height]
  have hw := length_w keccakRefShape t
  have hlm := logMemory_le_constraintVars keccakRefShape
  rw [reference_logMemory] at hlm
  rw [reference_sha3Height] at hpt
  refine ⟨fun hpre ↦ hbad ?_, fun out' hout hpre ↦ hbad ?_⟩
  · refine ⟨(digits t (max keccakRefShape.heap.h (keccakRefShape.constraintVars + 4) + 2)).take
      keccakRefShape.logMemory, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_, ?_⟩
    · rw [List.length_take, hw, hy, reference_logMemory]
      omega
    · rw [List.take_take, hy, reference_logMemory, show min 15 20 = 15 from rfl, ← hy]
      exact (List.prefix_iff_eq_take.mp hpre).symm
  · obtain rfl := Option.some.inj hout
    refine ⟨out.point, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ?_, ?_⟩
    · rw [hy]; omega
    · exact (List.prefix_iff_eq_take.mp hpre).symm

/-! ## `C2`'s terms cover their columns -/

theorem ne_c2_of {x : Term} (h : x.column.commitment = .c1 ∨ x.column.commitment = .setup) :
    x.column.commitment ≠ .c2 := by
  rcases h with h | h <;> rw [h] <;> decide

/-- **The relations off the heap have no term on `C2`**: the tables' (their columns at `w.take r`), the memory's,
the bytecode's and the constraint relation (on `C1`). -/
theorem offHeap_offC2 (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) :
    ∀ r ∈ AlgC.atTableRels tr (eqKernel alphas) beta (AlgC.atW tr t) ++
        AlgC.atMemoryRels tr (eqKernel alphas) beta (AlgC.atW tr t) ++
        AlgC.atBytecodeRels tr alphas beta (AlgC.atW tr t) ++ [(AlgC.atConstraint tr c2 alphas beta gamma t).1],
      ∀ x ∈ r.terms, x.column.commitment ≠ .c2 := by
  intro r hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with ((hr | hr) | hr) | rfl
  · unfold AlgC.atTableRels at hr
    obtain ⟨table, -, hr⟩ := List.mem_flatMap.mp hr
    unfold AlgC.atPart at hr
    rw [← AlgC.tablePart_run] at hr
    exact runReader_of
      (Q := fun res : TablePart × List Relation ↦ ∀ r ∈ res.2, ∀ x ∈ r.terms, x.column.commitment ≠ .c2)
      (tablePart_terms table _ _ _ _ (fun x ↦ x.column.commitment ≠ .c2) (fun _ _ ↦ ne_c2_of (Or.inl rfl)))
      (fun r hr ↦ absurd hr List.not_mem_nil) _ r hr
  · simp only [AlgC.atMemoryRels, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · intro x hx
      simp only [Relation.equal, List.mem_singleton] at hx
      subst hx
      exact ne_c2_of (Or.inl rfl)
    · intro x hx
      simp only [Relation.equal, List.mem_singleton] at hx
      subst hx
      exact ne_c2_of (Or.inr rfl)
    · intro x hx
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
      exact ne_c2_of (Or.inl rfl)
  · simp only [AlgC.atBytecodeRels, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro x hx
      simp only [Relation.equal, List.mem_singleton] at hx
      subst hx
      exact ne_c2_of (Or.inl rfl)
    · intro x hx
      simp only [Relation.equal, List.mem_singleton] at hx
      subst hx
      exact ne_c2_of (Or.inr rfl)
  · exact constraintRelation_terms _ _ _ _ _ _ _ (fun x ↦ x.column.commitment ≠ .c2)
      (fun _ _ _ ↦ ne_c2_of (Or.inl rfl)) (fun _ _ ↦ ne_c2_of (Or.inl rfl))
      (fun _ _ _ _ _ ↦ ne_c2_of (Or.inl rfl)) (fun _ _ ↦ ne_c2_of (Or.inl rfl))

/-- A relation on `C2` has a term on `C2`. -/
theorem exists_c2_term {r : Relation} (h : r.commitment = .c2) : ∃ x ∈ r.terms, x.column.commitment = .c2 := by
  unfold Relation.commitment at h
  cases hr : r.terms with
  | nil => rw [hr] at h; cases h
  | cons x rest => rw [hr] at h; exact ⟨x, List.mem_cons_self .., h⟩

/-- **Every heap term's column is in `c2Columns`** at a size its point covers (once that size is at most `|w|`). -/
theorem heap_terms_cover (tr : Trace) (c2 : C2Data) (alphas : List E) (beta gamma t : E) :
    ∀ r ∈ (AlgC.atHeap tr c2 alphas beta gamma t).1, ∀ x ∈ r.terms,
      ∃ v, (x.column, v, true) ∈ (atTOf tr c2 alphas beta gamma t none).c2Columns ∧
        (v ≤ (AlgC.atW tr t).length → v ≤ x.point.length) := by
  have hwl : (AlgC.atW tr t).length = max tr.shape.heap.h (tr.shape.constraintVars + 4) + 2 := AlgC.atW_length tr t
  have hh : ((AlgC.atW tr t).take tr.shape.heap.h).length = tr.shape.heap.h := by
    rw [List.length_take, hwl]; omega
  have hC := AlgC.atTOf_c2Columns tr c2 alphas beta gamma t
  have hheap : (Column.heap, tr.shape.heap.h, true) ∈ (atTOf tr c2 alphas beta gamma t none).c2Columns := by
    rw [hC]; simp
  have htq0 : (Column.treeQuotient 0, tr.shape.heap.h, true) ∈ (atTOf tr c2 alphas beta gamma t none).c2Columns := by
    rw [hC]; simp
  have htq1 : (Column.treeQuotient 1, 0, true) ∈ (atTOf tr c2 alphas beta gamma t none).c2Columns := by
    rw [hC]; simp
  have hcq : ∀ e c, (e, c) ∈ (chunks ((AlgC.atConstraint tr c2 alphas beta gamma t).2 + 1)).zip
      (List.range (chunks ((AlgC.atConstraint tr c2 alphas beta gamma t).2 + 1)).length) →
      (Column.constraintQuotient c, e, true) ∈ (atTOf tr c2 alphas beta gamma t none).c2Columns := by
    intro e c h
    rw [hC]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨(e, c), h, rfl⟩))
  have hleaf : ∀ y ∈ tr.shape.heap.blocks.zip (List.range tr.shape.heap.blocks.length),
      ∀ p ∈ AlgH.blockCols (AlgC.atActive tr (AlgC.atW tr t))
        (AlgC.atParts tr (eqKernel alphas) beta (AlgC.atW tr t))
        (AlgC.atMemoryPull tr (eqKernel alphas) beta (AlgC.atW tr t))
        (AlgC.atMemoryPush tr (eqKernel alphas) beta (AlgC.atW tr t))
        (AlgC.atBytecodePull tr (eqKernel alphas) beta (AlgC.atW tr t))
        (AlgC.atBytecodePush tr (eqKernel alphas) beta (AlgC.atW tr t)) (AlgC.atW tr t) y,
      p ∈ (atTOf tr c2 alphas beta gamma t none).c2Columns := by
    intro y hy p hp
    rw [hC]
    refine List.mem_append_right _ ?_
    unfold AlgC.atHeap
    rw [AlgH.heapRelations_eq]
    exact List.mem_flatMap.mpr ⟨y, hy, hp⟩
  have htake : ∀ e, e ≤ (AlgC.atW tr t).length → e ≤ ((AlgC.atW tr t).take e).length := by
    intro e he
    rw [List.length_take]
    omega
  unfold AlgC.atHeap
  rw [AlgH.heapRelations_eq]
  intro r hr x hx
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl) | ⟨y, hy, rfl⟩) | rfl
  · -- `T(t)`
    simp only [Relation.equal, List.mem_singleton] at hx
    subst hx
    exact ⟨_, hheap, fun _ ↦ hh.ge⟩
  · -- the tree
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · refine ⟨_, hheap, fun _ ↦ ?_⟩
      show tr.shape.heap.h ≤ ((List.drop 1 (AlgC.atW tr t)).take tr.shape.heap.h).length
      rw [List.length_take, List.length_drop, hwl]; omega
    · refine ⟨_, hheap, fun _ ↦ ?_⟩
      show tr.shape.heap.h ≤ (((AlgC.atW tr t).take tr.shape.heap.h).modify 0 (· + 1)).length
      rw [List.length_modify, hh]
    · exact ⟨_, htq0, fun _ ↦ hh.ge⟩
    · exact ⟨0, htq1, fun _ ↦ Nat.zero_le _⟩
  · -- the root
    simp only [List.mem_singleton] at hx
    subst hx
    refine ⟨_, hheap, fun _ ↦ ?_⟩
    show tr.shape.heap.h ≤ ((List.range tr.shape.heap.h).map _).length
    rw [List.length_map, List.length_range]
  · -- a block
    have hl := hleaf y hy
    unfold AlgH.blockRel at hx
    unfold AlgH.blockCols at hl
    split at hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨_, hheap, fun _ ↦ (AlgH.mixedPoint_length _ _ _ _).ge⟩
    · rename_i pull push d scale hbl
      rw [hbl] at hl
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact ⟨_, hheap, fun _ ↦ (AlgH.mixedPoint_length _ _ _ _).ge⟩
      · exact quotientTerms_terms _ _ _ _
          (fun x ↦ ∃ v, (x.column, v, true) ∈ (atTOf tr c2 alphas beta gamma t none).c2Columns ∧
            (v ≤ (AlgC.atW tr t).length → v ≤ x.point.length))
          (fun e c hec _ ↦ ⟨e, hl _ (List.mem_map.mpr ⟨(e, c), hec, rfl⟩), htake e⟩) x hx
  · -- the constraint quotient
    exact quotientTerms_terms _ _ _ _
      (fun x ↦ ∃ v, (x.column, v, true) ∈ (atTOf tr c2 alphas beta gamma t none).c2Columns ∧
        (v ≤ (AlgC.atW tr t).length → v ≤ x.point.length))
      (fun e c hec _ ↦ ⟨e, hcq e c hec, htake e⟩) x hx




theorem reference_constraintVars : keccakRefShape.constraintVars = 20 := by decide +kernel

/-- **`C2`'s terms cover their columns** (`AtTCoversC2`) at the reference shape, for an honest trace: every `C2`
term is a heap term (`offHeap_offC2`; the ring switch's is on `C1`), its column is listed once in `c2Columns`
(`AlgH.c2Names_nodup`) at a size of at most `26 ≤ |w|` (`C2`'s `26` variables), which its point covers
(`heap_terms_cover`). -/
theorem atTOf_coversC2 (tr : Trace) (hon : TraceHonest tr) (href : tr.shape = keccakRefShape) (c2 : C2Data)
    (alphas : List E) (beta gamma t : E) (out : FlockOut) {map : List E} {target : E}
    (hend : out.end_ = .ring map target) :
    AtTCoversC2 tr.shape (atTOf tr c2 alphas beta gamma t (some out)) := by
  intro r hr x hx hxc b hb
  rw [AlgC.atTOf_some_c2Columns tr c2 alphas beta gamma t out hend, layoutIn_c2] at hb
  rw [AlgC.atTOf_some_relations tr c2 alphas beta gamma t out hend] at hr
  have hcols : (atTOf tr c2 alphas beta gamma t none).c2Columns = Shape.c2ColumnsK tr.shape :=
    AlgH.atTOf_c2Columns_eq hon c2 alphas beta gamma t
  have hheap : r ∈ (AlgC.atHeap tr c2 alphas beta gamma t).1 := by
    rcases List.mem_append.mp hr with hr | hr
    · rw [AlgC.atTOf_relations] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact absurd hxc (offHeap_offC2 tr c2 alphas beta gamma t r hr x hx)
      · exact hr
    · rw [List.mem_singleton] at hr
      subst hr
      simp only [AlgC.ringRel, List.mem_singleton] at hx
      subst hx
      exact absurd hxc (ne_c2_of (Or.inl rfl))
  obtain ⟨v, hv, hcov⟩ := heap_terms_cover tr c2 alphas beta gamma t r hheap x hx
  obtain ⟨eV, hb'⟩ := mem_limbs_new hb
  have hnd := AlgH.c2Names_nodup tr.shape
  rw [← hcols] at hnd
  have heq := List.inj_on_of_nodup_map hnd hb' hv rfl
  have hbv : b.2.1 = v := by
    simp only [Prod.mk.injEq] at heq
    exact heq.2.1
  have hin := AlgC.blocks_inRange _ _ (AlgC.mem_limbs.mp hb)
  simp only at hin
  rw [hcols, href, reference_c2Vars] at hin
  have h26 : b.2.1 ≤ 26 := by
    have : 2 ^ b.2.1 ≤ 2 ^ 26 := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hwl : (AlgC.atW tr t).length = max tr.shape.heap.h (tr.shape.constraintVars + 4) + 2 :=
    AlgC.atW_length tr t
  rw [href, reference_constraintVars] at hwl
  rw [hbv] at h26 ⊢
  exact hcov (by omega)

/-! ## Every relation at `t` holds -/

/-- **The ring switch's relation holds**: `Φ(eq(p, ·))` paired with `q_flock`'s block of `C1` is Flock's target
(`FlockP.flockRingSum`), `q_flock` one block `(0, h_SHA3 + 11, o)` of `C1` (`AlgC.limbs_K`) placed at its offset. -/
theorem ringRel_holds (tr : Trace) (out : FlockOut) {map : List E} {target : E}
    (hring : ∑ u ∈ range (2 ^ out.point.length),
      Flock.towerRingMap ((eqKernel out.point).getD u 0) map * ofK (tr.qflock.getD u 0) = target)
    (hlen : out.point.length = tr.shape.heights.getD opSha3 0 + 11) (cols : List (Column × ℕ × Bool))
    (SO : Commitment → Array K) (hSO : SO .c1 = c1Stack tr) :
    Relation.Holds (layoutIn (layoutsK tr.shape cols)) SO (some map) (AlgC.ringRel out target) := by
  unfold Relation.Holds AlgC.ringRel
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  show termEval (c1LayoutK tr.shape) (SO .c1) (some map) ⟨.qflock, out.point, ringTwist, 1⟩ = target
  rw [hSO]
  obtain ⟨o, hlimbs, hin⟩ := AlgC.limbs_K (cols := AlgC.c1ColsOf tr.shape) (column := .qflock)
    (AlgC.termCount_c1 tr.shape AlgC.c1Names_count_qflock) (AlgC.c1ColsOf_vars tr.shape)
  rw [show AlgC.c1VarsOf tr.shape .qflock = tr.shape.heights.getD opSha3 0 + 11 from rfl] at hlimbs hin
  have hb : (Column.qflock, 0, tr.shape.heights.getD opSha3 0 + 11, o) ∈
      (StackLayout.new (AlgC.c1ColsOf tr.shape)).blocks :=
    AlgC.mem_limbs.mp (by rw [hlimbs]; exact List.mem_singleton_self _)
  unfold termEval denseWeight termClaim c1Stack
  rw [AlgC.c1Layout_eq]
  simp only [List.foldl_cons, List.foldl_nil, AlgC.termGetD_single, hlimbs, ↓reduceIte]
  obtain ⟨-, h2⟩ := AlgC.dotK_foldl_addAt (placeStack (StackLayout.new (AlgC.c1ColsOf tr.shape)) (c1Words tr))
    (fun u ↦ o + u)
    (fun u ↦ limbScale 1 0 * Flock.towerRingMap ((eqKernel ((out.point ++ List.replicate
      (tr.shape.heights.getD opSha3 0 + 11) 0).take (tr.shape.heights.getD opSha3 0 + 11))).getD u 0) map)
    (List.range (2 ^ (tr.shape.heights.getD opSha3 0 + 11)))
    (Array.replicate (2 ^ (StackLayout.new (AlgC.c1ColsOf tr.shape)).vars) 0)
  rw [h2, AlgC.dotK_replicate, zero_add, AlgC.termSum_map_range, AlgC.termTake_pad _ hlen, ← hring, hlen,
    Array.size_replicate]
  refine Finset.sum_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.mp hu
  have hst := AlgC.placeStack_block (AlgC.c1ColsOf tr.shape) (c1Words tr) _ hb u hu'
  simp only at hst
  rw [AlgC.termIte_pos (by omega), hst, AlgC.limbScale_zero, one_mul]
  rfl

/-- **Every relation the prover states at `t` holds** of its three stacks, at the layouts the verifier states,
with the ring map, for an honest trace at the reference shape, `α, β` off `BadFp` and Flock's output with its
ring switch true. -/
theorem relations_hold_front (tr : Trace) (hon : TraceHonest tr) (href : tr.shape = keccakRefShape)
    {alphas : List E} (hα : alphas.length = 4) (beta gamma t : E) (out : FlockOut) {map : List E} {target : E}
    (hend : out.end_ = .ring map target) (hbad : ¬ BadFp tr alphas beta)
    (hring : ∑ u ∈ range (2 ^ out.point.length),
      Flock.towerRingMap ((eqKernel out.point).getD u 0) map * ofK (tr.qflock.getD u 0) = target)
    (hlen : out.point.length = tr.shape.heights.getD opSha3 0 + 11) :
    ∀ r ∈ (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).relations,
      Relation.Holds (layoutIn (layoutsK tr.shape
          (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).c2Columns))
        (stacksOf (c1Stack tr) (c2DataOf tr (eqKernel alphas) beta gamma).stack (setupStackOf tr))
        (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).ringMap r := by
  intro r hr
  have hS : stacksOf (c1Stack tr) (c2DataOf tr (eqKernel alphas) beta gamma).stack (setupStackOf tr) =
      AlgC.stackOfTr tr (c2DataOf tr (eqKernel alphas) beta gamma) := funext fun c ↦ by cases c <;> rfl
  have hS' : stacksOf (c1Stack tr) (c2DataOf tr (eqKernel alphas) beta gamma).stack (setupStackOf tr) =
      AlgH.stacksOf tr (c2DataOf tr (eqKernel alphas) beta gamma) := funext fun c ↦ by cases c <;> rfl
  have hH : tr.shape.heap.h ≤ 28 :=
    AlgH.heap_h_le_of_c2 tr.shape (by rw [href, AlgH.c2Layout_eq, reference_c2Vars]; norm_num)
  obtain ⟨-, hrest⟩ := AlgC.relations_hold_some_reference hon href hα beta gamma t out hend
  have hrel := AlgC.atTOf_some_relations tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t out hend
  rw [hrel] at hr
  rcases List.mem_append.mp hr with hr' | hr'
  · by_cases hc : r.commitment = .c2
    · have hheap : r ∈ (AlgC.atHeap tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t).1 := by
        rw [AlgC.atTOf_relations] at hr'
        rcases List.mem_append.mp hr' with h | h
        · obtain ⟨x, hx, hxc⟩ := exists_c2_term hc
          exact absurd hxc (offHeap_offC2 tr _ alphas beta gamma t r h x hx)
        · exact h
      have := AlgH.heapRelations_hold hon hbad hH t
        (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).ringMap r hheap
      rw [AlgC.atTOf_some_c2Columns _ _ _ _ _ _ out hend, hS']
      exact this
    · have hmem : r ∈
          (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).relations.dropLast := by
        rw [hrel, List.dropLast_concat]
        exact hr'
      rw [hS]
      exact hrest r hmem hc
  · rw [List.mem_singleton] at hr'
    subst hr'
    rw [AlgC.atTOf_some_ringMap _ _ _ _ _ _ out hend]
    exact ringRel_holds tr out hring hlen _ _ rfl

/-! ## The honest batch's hypotheses -/

/-- **The three stacks have their layouts' `2^vars` words** at the reference shape. -/
theorem stack_sizes (tr : Trace) (href : tr.shape = keccakRefShape) (weights : Array E) (beta gamma : E)
    (c : Commitment) :
    (stacksOf (c1Stack tr) (c2DataOf tr weights beta gamma).stack (setupStackOf tr) c).size =
      2 ^ (layoutIn (layoutsK tr.shape (Shape.c2ColumnsK tr.shape)) c).vars := by
  cases c
  · rw [AlgC.layoutIn_c1, href, show (c1LayoutK keccakRefShape).vars = 27 from reference_c1Vars]
    exact c1Stack_size tr href
  · rw [layoutIn_c2, href, reference_c2Vars]
    exact c2Stack_size tr href weights beta gamma
  · rw [AlgC.layoutIn_setup, href, show (setupLayout keccakRefShape).vars = 23 from reference_setupVars]
    exact setupStackOf_size tr href

/-- **`BatchHolds` at `t`, `ρ`** (any challenges), for an honest trace at the reference shape, Flock's honest
output at any writer, `α, β` off `BadFp` and `t` off `BadT`. -/
theorem batchHolds_of (H : List UInt8 → Digest) (tr : Trace) (hon : TraceHonest tr)
    (href : tr.shape = keccakRefShape) {alphas : List E} (hα : alphas.length = 4) (beta gamma t rho : E) (w : Wr)
    (out : FlockOut)
    (hout : out = ((FlockP.flockProve (m := Id) (Pure.pure ∘ H)
      (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) keccakMain tr.qflock).run w).1)
    (hbad : ¬ BadFp tr alphas beta) (hbadT : ¬ Prob.BadT keccakRefShape out.point t) :
    BatchHolds
      (commitments.filterMap fun c ↦
        (combine (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).relations c
          rho).map (c, ·))
      (layoutsK tr.shape (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).c2Columns)
      (stacksOf (c1Stack tr) (c2DataOf tr (eqKernel alphas) beta gamma).stack (setupStackOf tr))
      (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).ringMap := by
  obtain ⟨map, target, hend, hmap6, hring⟩ :=
    FlockP.flockRingSum (Pure.pure ∘ H) (keccakR1csLogSize + tr.shape.heights.getD opSha3 0) keccakMain
      tr.qflock w
  rw [← hout] at hend hring
  have hlen : out.point.length = tr.shape.heights.getD opSha3 0 + 11 := by
    rw [hout]
    exact FlockP.flock_point_length_trace H tr keccakMain (by decide) w
  have hslot := slotCondition_of_badT tr href t out (by omega) hbadT
  have hcov := atTOf_coversC2 tr hon href (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t out hend
  have hringMap :=
    AlgC.atTOf_some_ringMap tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t out hend
  obtain ⟨-, hcomb⟩ := atTOf_combined tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t rho
    (some out) (stacksOf (c1Stack tr) (c2DataOf tr (eqKernel alphas) beta gamma).stack (setupStackOf tr)) hα
    (fun o ho ↦ by obtain rfl := Option.some.inj ho; omega)
    (fun m hm ↦ by rw [hringMap] at hm; obtain rfl := Option.some.inj hm; omega) hcov hslot
  have hall := relations_hold_front tr hon href hα beta gamma t out hend hbad hring hlen
  have hcols : (atTOf tr (c2DataOf tr (eqKernel alphas) beta gamma) alphas beta gamma t (some out)).c2Columns =
      Shape.c2ColumnsK tr.shape := by
    rw [AlgC.atTOf_some_c2Columns _ _ _ _ _ _ out hend]
    exact AlgH.atTOf_c2Columns_eq hon _ alphas beta gamma t
  refine ⟨fun x hx ↦ ⟨(hcomb x hx).2 hall, (hcomb x hx).1, aligned_layoutIn _ (aligned_layouts _ _) _, ?_⟩⟩
  rw [hcols]
  exact stack_sizes tr href _ beta gamma x.1

/-- **The honest batch's hypotheses at the prover's front state** (`frontOf` with Flock's honest prover): an honest
trace at the reference shape, `α, β` off `BadFp`, `t` off `BadT`. -/
theorem batchHolds_front (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (tr : Trace) (hon : TraceHonest tr) (href : tr.shape = keccakRefShape) (seed : Digest)
    (hbad : ¬ BadFp tr (frontOf H commit (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr (Wr.start seed)).1.alphas
      (frontOf H commit (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr (Wr.start seed)).1.beta)
    (hbadT : ∀ out, (frontOf H commit (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr
        (Wr.start seed)).1.flockOut = some out →
      ¬ Prob.BadT keccakRefShape out.point
        (frontOf H commit (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr (Wr.start seed)).1.t) :
    let F := (frontOf H commit (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr (Wr.start seed)).1
    BatchHolds F.combined F.stackLayouts F.stackOf F.atT.ringMap := by
  simp only [frontOf, FrontOut.stackOf] at hbad hbadT ⊢
  exact batchHolds_of H tr hon href (FlockP.samplesW_length _ 4 _) _ _ _ _ _ _ rfl hbad (hbadT _ rfl)

/-- **The batching sumcheck synchronises at the prover's front state, its terminal zero.** -/
theorem batchSyncsAt_front (H : List UInt8 → Digest) (commit : Commitment → ℕ → Array K → Id Committed)
    (tr : Trace) (hon : TraceHonest tr) (href : tr.shape = keccakRefShape) (seed : Digest)
    (hbad : ¬ BadFp tr (frontOf H commit (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr (Wr.start seed)).1.alphas
      (frontOf H commit (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr (Wr.start seed)).1.beta)
    (hbadT : ∀ out, (frontOf H commit (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr
        (Wr.start seed)).1.flockOut = some out →
      ¬ Prob.BadT keccakRefShape out.point
        (frontOf H commit (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr (Wr.start seed)).1.t) :
    BatchSyncsAt H commit (FlockP.flockProve (m := Id) (Pure.pure ∘ H)) tr seed (fun _ ↦ 0) :=
  batchSyncs_honest H _ _ _ _ (batchHolds_front H commit tr hon href seed hbad hbadT)

end UniKeccakComplete.Core

/-- info: 'UniKeccakComplete.Core.batchHolds_front' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.Core.batchHolds_front

/-- info: 'UniKeccakComplete.Core.batchSyncsAt_front' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.Core.batchSyncsAt_front

/-- info: 'UniKeccakComplete.Core.c1Stack_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.Core.c1Stack_size

/-- info: 'UniKeccakComplete.Core.c2Stack_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.Core.c2Stack_size

/-- info: 'UniKeccakComplete.Core.setupStackOf_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.Core.setupStackOf_size
