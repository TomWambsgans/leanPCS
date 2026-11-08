-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The construction is `UniSound/Ids/Build.lean`'s
-- (`busModelOf`, `idsRestOf`) and `UniSound/Bus.lean`'s `UniIds.ofBus`, for the Keccak VM.
import UniSound.Ids.Build
import UniSound.Ids.Main
import UniSound.Ids.Deployed
import UniKeccakSound.Ids.Bus
import UniKeccakSound.Ids.Batch

/-!
# The Keccak identity model, constructed from named bridges

**`uniIdsK D Fl N h d n g : UniIdsK F D Fl`**: the identity model of the Keccak verifier's main line, for a
deployment `D` and Flock's phase `Fl` on the Keccak-f block, built from the data of `Model.lean`, the proved
reductions (round `0`, `BusModelK.mainSound`; the batch's start, `batch_start_K`; `Z_bad`'s degree and
nonvanishing; the differences' count and lengths), and two structures of named hypotheses:

* `IdsHypsK F D κ N` — the bridges to the Keccak VM's relation (`KvRealizesK`, `KvConstraintsK`, `KvBusCountK`,
  `AuxOfFlockK`), the heap's layout (`HeapGood`), the constraint vectors' reading (`CvecOkK`), the coordinate
  functionals at `h_SHA3` (`FunctionalsCorrect`);
* `IdsGapsK D Fl d n` — the reductions between the verifier's checks and the identities: the relations at `t`
  give the identities at `t` (`DiffsEvalK`), the identities as polynomials give the heap and the constraint
  vectors (`MainOfPolysK`), the ring-switch relation gives Flock's claim (`DiffsFlockK`), the degrees
  (`DegBoundK`), the relations' number (`RelCountK`).

Each bridge is a `Prop` about the verifier's (`formal/UniKeccak`), the Keccak VM's (`formal/KeccakVm`) or the
deployment's definitions; the rest of `UniIdsK` is proved here.
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak Finset
open scoped ENNReal

/-! ## The constraints on `C1`'s rows -/

/-- **The constraints on `C1`'s rows, pointwise**, on the Keccak VM (what the constraint quotient's identity gives
on the domain): `JUMP`'s two, the counters' inverse, the lanes' copies, the public lines. -/
structure RowConstraintsK (D : KDeployment) (c : Stk) (s : USt) : Prop where
  jump : ∀ x < 2 ^ D.shape.heights.getD opJump 0,
    c1ValK D c (.table opJump (colIdx jumpColumns "b")) (D.shape.heights.getD opJump 0) x +
        c1ValK D c (.table opJump (colIdx jumpColumns "v_cond")) (D.shape.heights.getD opJump 0) x *
          c1ValK D c (.table opJump (colIdx jumpColumns "w")) (D.shape.heights.getD opJump 0) x = 0 ∧
      c1ValK D c (.table opJump (colIdx jumpColumns "v_cond")) (D.shape.heights.getD opJump 0) x *
          (c1ValK D c (.table opJump (colIdx jumpColumns "b")) (D.shape.heights.getD opJump 0) x + 1) = 0
  counters : ∀ o < 6, ∀ x < 2 ^ D.shape.heights.getD o 0,
    c1ValK D c (.inverse o) (D.shape.heights.getD o 0) x *
      ((tablesKeccak.getD o default).countColumns.map fun j ↦
        c1ValK D c (.table o j) (D.shape.heights.getD o 0) x).prod = 1
  copies : ∀ x < 2 ^ D.shape.heights.getD opBlake2s 0, ∀ col slot,
    keccakSlot (sha3Columns.getD col "") = some slot →
      c1ValK D c (.table opBlake2s col) (D.shape.heights.getD opBlake2s 0) x =
        c (qfOffK D + slot + 2 ^ qflockRowBits * x) + toK (eK (keccakSlotOffset (sha3Columns.getD col "")))
  lines : ∀ k < 3,
    c1ValK D c (.memory k) D.shape.logMemory 0 = toK ((linesOf (publicWordsOf s.1.toList)).getD k (0, 0)).1 ∧
      c1ValK D c (.memory k) D.shape.logMemory 1 = toK ((linesOf (publicWordsOf s.1.toList)).getD k (0, 0)).2

/-! ## The bridges, stated -/

/-- **The constraint vectors' vanishing gives the counts in range and the rows' constraints.** -/
def CvecOkK (D : KDeployment) : Prop :=
  ∀ s c, (∀ x < 2 ^ D.shape.constraintVars, ∀ v ∈ cvecK D c s x, v = 0) →
    CountsFit D.shape s.2 ∧ RowConstraintsK D c s

/-- **The constraints on `C1`'s rows are the Keccak VM's** `ConstraintsVanish`, `CountsNonzero`,
`PublicLinesHold` of `C1`'s Keccak VM stack (`kvStack`). -/
def KvConstraintsK (D : KDeployment) : Prop :=
  ∀ (s : USt) (c : Stk), CountsFit D.shape s.2 → RowConstraintsK D c s →
    (D.inst s.2).ConstraintsVanish (kvStack D.prog (D.sizes s.2) D.shape c) ∧
      (D.inst s.2).CountsNonzero (kvStack D.prog (D.sizes s.2) D.shape c) ∧
      (D.inst s.2).PublicLinesHold (publicInputOf s.1.toList) (kvStack D.prog (D.sizes s.2) D.shape c)

/-- **The heap read off `C1` realizes the Keccak VM's bus** of `C1`'s Keccak VM stack where the copies hold. -/
def KvRealizesK (D : KDeployment) : Prop :=
  ∀ (s : USt) (c : Stk), CopiesK D c s →
    Heap.Realizes (I := D.inst s.2) (kvStack D.prog (D.sizes s.2) D.shape c) (hdK D c s)

/-- **The bus counts** at counts in range: at most `N` tuples a side. -/
def KvBusCountK (D : KDeployment) (N : ℕ) : Prop :=
  ∀ rows : List ℕ, CountsFit D.shape rows →
    Heap.busCount (D.inst rows) .push ≤ N ∧ Heap.busCount (D.inst rows) .pull ≤ N

/-- **Flock's predicate on `C1`'s `q_flock` and the copies give the Keccak-f region with the lanes' copies**
(`KeccakAux`) of `C1`'s Keccak VM stack. -/
def AuxOfFlockK (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (κ : ℕ) : Prop :=
  ∀ (s : USt) (c : Stk), CopiesK D c s → KFlockHolds F κ (qfK D c κ) →
    KeccakVm.KeccakAux F D.prog (D.sizes s.2) (kvStack D.prog (D.sizes s.2) D.shape c)

section Gaps

variable (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant} (Fl : KFlockSound F κ v)

/-- **The relations at `t` give the identities at `t`.** -/
def DiffsEvalK : Prop :=
  ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffsK D Fl s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    ∀ P ∈ polysK D Fl s c1 ch fd c2, P.eval t = 0

/-- **The identities as polynomials give the heap and the constraint vectors** (`BusModelK.MainOK`). -/
def MainOfPolysK : Prop :=
  ∀ s c1 ch fd c2, (∀ P ∈ polysK D Fl s c1 ch fd c2, P = 0) →
    (hdK D c1 s).Sat (fun i ↦ ch.getD i.val 0) (ch.getD 4 0) ∧
      ∀ x < 2 ^ D.shape.constraintVars, powComb (cvecK D c1 s x) (ch.getD 5 0) = 0

/-- **The ring-switch relation gives Flock's claim on `q_flock`.** -/
def DiffsFlockK : Prop :=
  ∀ s c1 ch fd c2 t vals, (∀ d ∈ diffsK D Fl s c1 ch fd c2 t vals, ∀ x ∈ d, x = 0) →
    FlockEndHoldsK (qfK D c1 κ) (Fl.prog.out fd [])

/-- **The identities' degrees** sum to at most `d`. -/
def DegBoundK (d : ℕ) : Prop :=
  ∀ s c1 ch fd c2, ((polysK D Fl s c1 ch fd c2).map Polynomial.natDegree).sum ≤ d

/-- **At most `n` relations.** -/
def RelCountK (n : ℕ) : Prop :=
  ∀ s ch fd t vals, (relsAtK D Fl s ch fd t vals).length ≤ n

end Gaps

/-- **The bridges** at the bus bound `N`. -/
structure IdsHypsK (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (κ : ℕ) (N : ℕ) : Prop where
  heapGood : HeapGood D.shape
  kvRealizes : KvRealizesK D
  kvBusCount : KvBusCountK D N
  kvConstraints : KvConstraintsK D
  cvecOk : CvecOkK D
  auxOfFlock : AuxOfFlockK F D κ
  /-- The coordinate functionals at `SHA3`'s height invert the Moore matrix (`Z_bad ≠ 0`). -/
  functionals : FunctionalsCorrect (D.shape.heights.getD opBlake2s 0)
  height2 : 2 ≤ D.shape.heights.getD opBlake2s 0

/-- **The reductions** at the degrees' bound `d` and the relations' `n`. -/
structure IdsGapsK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (d n : ℕ) : Prop where
  diffsEval : DiffsEvalK D Fl
  mainOfPolys : MainOfPolysK D Fl
  diffsFlock : DiffsFlockK D Fl
  degBound : DegBoundK D Fl d
  relCount : RelCountK D Fl n

/-! ## Proved fields -/

/-- The number of constraints, any `C1`. -/
noncomputable def ncvK (S : Shape) : ℕ := (constraintsPK S (fun _ ↦ 0) []).length + 1

theorem length_tableConstraintsPK (S : Shape) (c : Stk) (tab : Table) :
    (tableConstraintsPK S c tab).length = (tableConstraintsPK S (fun _ ↦ 0) tab).length := by
  unfold tableConstraintsPK
  simp only [List.length_append]
  split_ifs <;> simp [length_filterMap_map]

theorem length_constraintsPK (S : Shape) (c : Stk) (pw : List E) :
    (constraintsPK S c pw).length = (constraintsPK S (fun _ ↦ 0) []).length := by
  unfold constraintsPK linesPK
  simp only [List.length_append, List.length_flatMap, List.length_map, List.length_zip, linesOf,
    List.length_cons, List.length_nil, List.length_range]
  exact congrArg (· + _) (congrArg List.sum (List.map_congr_left fun tab _ ↦ length_tableConstraintsPK S c tab))

theorem cvecK_len (D : KDeployment) (s : USt) (c : Stk) (x : ℕ) :
    (cvecK D c s x).length ≤ ncvK D.shape := by
  unfold cvecK ncvK
  split_ifs
  · rw [List.length_map, length_constraintsPK]; omega
  · simp

theorem blockKK_r (D : KDeployment) (c : Stk) (rows : List ℕ) (b : Block) :
    (blockKK D c rows b).r = b.r := by
  unfold blockKK
  cases b.leaves <;> rfl

/-- **The heap read off `C1` is well formed** (`HeapGood`). -/
theorem hdK_wf (D : KDeployment) (hH : HeapGood D.shape) (c : Stk) (s : USt) : (hdK D c s).WellFormed := by
  refine ⟨hH.1, ?_⟩
  show Heap.total (D.shape.heap.blocks.map (blockKK D c s.2)) = 2 ^ (D.shape.heap.h - 1)
  unfold Heap.total
  rw [List.map_map, ← hH.2.2.1]
  congr 1
  refine List.map_congr_left fun b _ ↦ ?_
  simp [blockKK_r]

theorem diffsK_count (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E)
    (vals : List E) : (diffsK D Fl s c1 ch fd c2 t vals).length ≤ 3 := by
  unfold diffsK
  split_ifs <;> simp [commitments]

theorem diffsK_len (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (n : ℕ) (hn : RelCountK D Fl n)
    (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E) (vals : List E) :
    ∀ d ∈ diffsK D Fl s c1 ch fd c2 t vals, d.length ≤ max n 1 := by
  intro d hd
  unfold diffsK at hd
  split_ifs at hd
  · simp only [List.mem_map] at hd
    obtain ⟨c, _, rfl⟩ := hd
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans ((hn s ch fd t vals).trans (le_max_left _ _))
  · simp only [List.mem_singleton] at hd
    subst hd
    simp

theorem prodK_vars (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (s : USt) (c1 : Stk) (ch : List E) (fd : Done) (c2 : Stk) (t : E)
    (vals : List E) (ρ l : E) : (prodK D Fl s c1 ch fd c2 t vals ρ l).vars = batchVarsK D.shape := by
  unfold prodK
  split_ifs <;> rfl

/-! ## The models -/

/-- **The bus model** of the deployment `D` on the Keccak VM. -/
noncomputable def busModelK (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (κ N : ℕ)
    (h : IdsHypsK F D κ N) : BusModelK D where
  hd s c := hdK D c s
  wf s c := hdK_wf D h.heapGood c s
  Copies s c := CopiesK D c s
  realizes s c hcp := h.kvRealizes s c hcp
  N := N
  hpush s c hcp := (h.kvBusCount s.2 hcp.1).1
  hpull s c hcp := (h.kvBusCount s.2 hcp.1).2
  nrows := 2 ^ D.shape.constraintVars
  cvec s c x := cvecK D c s x
  ncv := ncvK D.shape
  cvec_len s c x := cvecK_len D s c x
  cvec_ok s c hall := by
    obtain ⟨hfit, hrow⟩ := h.cvecOk s c hall
    obtain ⟨hcv, hcn, hpl⟩ := h.kvConstraints s c hfit hrow
    exact ⟨hcv, hcn, hpl, hfit, hrow.copies⟩

/-- **The identity model of the Keccak verifier's main line** for the deployment `D` and Flock's phase `Fl` on the
Keccak-f block, from the bridges `h` and the reductions `g`. -/
noncomputable def uniIdsK (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (N : ℕ) (h : IdsHypsK F D κ N) (d n : ℕ) (g : IdsGapsK D Fl d n) :
    UniIdsK F D Fl where
  nV := valsCountK
  V := batchVarsK D.shape
  qf c := qfK D c κ
  MainHolds := (busModelK F D κ N h).MainHolds
  rel_of s c hm hf := (busModelK F D κ N h).rel_of F s c hm (h.auxOfFlock s c hm.2.2.2.2 hf)
  MainOK := (busModelK F D κ N h).MainOK
  errMain := (busModelK F D κ N h).errMain
  mainSound := (busModelK F D κ N h).mainSound
  polys := polysK D Fl
  degSum := d
  deg_le := g.degBound
  main_of_polys s c1 ch fd c2 hP := g.mainOfPolys s c1 ch fd c2 hP
  zb := zbK D Fl
  zb_ne _ := zBad_ne_zero D.shape betaCantor h.functionals h.height2 _
  degBad := zBadDeg D.shape
  zb_deg _ := natDegree_zBad_le D.shape _
  diffs := diffsK D Fl
  nRel := max n 1
  diffs_len := diffsK_len D Fl n g.relCount
  diffs_count := diffsK_count D Fl
  diffs_eval := g.diffsEval
  diffs_flock := g.diffsFlock
  prod := prodK D Fl
  prod_vars := prodK_vars D Fl
  target := targetK D Fl
  batch_start := batch_start_K D Fl

/-- **Round `0`'s error** is at most `2^32 / |E|` when `4 N + ncv ≤ 2^32`. -/
theorem uniIdsK_errMain_le (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (N : ℕ) (h : IdsHypsK F D κ N) (d n : ℕ) (g : IdsGapsK D Fl d n)
    (hB : 4 * N + ncvK D.shape ≤ 2 ^ 32) :
    (uniIdsK D Fl N h d n g).errMain ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) / (Fintype.card E : ℝ≥0∞) :=
  (busModelK F D κ N h).errMain_le hB

end UniKeccakSound.Ids
