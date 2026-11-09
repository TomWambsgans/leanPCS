-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The tables are `formal/UniStatement`'s `tablesKeccak`
-- (`KeccakTables.lean`); the proofs are `UniSound/Ids/Eval.lean`'s (`tablePartOf_spec`, `tablesLin`, `chunksFit`) on
-- the Keccak tables, whose `SHA3` table has `28` flushes and `27` counters.
import UniKeccakSound.IdsEval.Layout

/-!
# The Keccak tables' facts, and the quotients' chunks within the digits

* **`tablesLinK`**: the Keccak tables' flushes are as `linearise` reads them (the kernel checks their monomials);
  **`tablePartOf_specOf`**: a table's part at `t` (`UniSound.Ids.Eval.tablePartOf_spec` for any table whose flushes
  are so);
* **`chunksFitK`**: at a valid shape whose heap's blocks are `HeapGood`'s, every chunk of the constraint quotient
  (`constraintDegreeK < 2^(r_W + 5)`) and of each heap block's leaf quotient (`leafDegreeK`: a table's below
  `2^(r + 6)` from its at most `57` fingerprint degrees) is below the number of digits `t` is read through.
-/

namespace UniKeccakSound.IdsEval

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniSound.Ids.Eval UniKeccak UniKeccakSound.Ids

/-! ## The tables -/

/-- **The Keccak tables' flushes, as `linearise` reads them** (`UniSound.Ids.Eval.TablesLin` on `tablesKeccak`). -/
def TablesLinK : Prop :=
  ∀ tab ∈ tablesKeccak, (∀ c ∈ sentColumns tab, c < tab.width) ∧
    ∀ fl ∈ tab.flushes.pull.zip tab.flushes.push, fl.2.length = fl.1.length ∧
      ∀ f ∈ fl.1 ++ fl.2, ∀ mc ∈ f, mc.1.length = 2 →
        mc.1.getD 0 0 ∈ sentColumns tab ∨ mc.1.getD 1 0 ∈ sentColumns tab

set_option maxRecDepth 100000 in
/-- **The Keccak tables' flushes are as `linearise` reads them** (the kernel checks the six tables' monomials, not
their coefficients). -/
theorem tablesLinK : TablesLinK := by
  unfold TablesLinK
  decide +kernel

theorem tablesKeccak_opcode (o : ℕ) (ho : o < 6) : (tablesKeccak.getD o default).opcode = o := by
  interval_cases o <;> rfl

theorem tablesKeccak_mem (o : ℕ) (ho : o < 6) : tablesKeccak.getD o default ∈ tablesKeccak := by
  rw [List.getD_eq_getElem _ _ (by rw [tablesKeccak_length]; omega)]
  exact List.getElem_mem _

/-- **A table's part at `t`** (`tablePartOf_spec` for one table whose flushes are as `linearise` reads them). -/
theorem tablePartOf_specOf (tab : Table)
    (hT : (∀ c ∈ sentColumns tab, c < tab.width) ∧
      ∀ fl ∈ tab.flushes.pull.zip tab.flushes.push, fl.2.length = fl.1.length ∧
        ∀ f ∈ fl.1 ++ fl.2, ∀ mc ∈ f, mc.1.length = 2 →
          mc.1.getD 0 0 ∈ sentColumns tab ∨ mc.1.getD 1 0 ∈ sentColumns tab)
    (lh : ℕ) (weights : Array E) (beta : E) (w vals : List E) (ev : Column → List E → E) (colv : ℕ → E)
    (hev : ∀ c, ev (.table tab.opcode c) (w.take lh) = colv c)
    (hh : ∀ r ∈ (tablePartOf tab lh weights beta w vals).2.1, RelHolds ev r) :
    (∀ c ∈ sentColumns tab, (tablePartOf tab lh weights beta w vals).1.sent.getD c none = some (colv c)) ∧
      (tablePartOf tab lh weights beta w vals).1.pull =
        ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ beta + tupleE fl.1 weights colv).prod ∧
      (tablePartOf tab lh weights beta w vals).1.push =
        ((tab.flushes.pull.zip tab.flushes.push).map fun fl ↦ beta + tupleE fl.2 weights colv).prod ∧
      (tablePartOf tab lh weights beta w vals).1.pullDegree = (tableDegrees tab).1 ∧
      (tablePartOf tab lh weights beta w vals).1.pushDegree = (tableDegrees tab).2 := by
  obtain ⟨hw, hfl⟩ := hT
  have h0 : ∀ p < (sentColumns tab).length, vals.getD p 0 = colv ((sentColumns tab).getD p 0) := by
    intro p hp
    rw [← holds_equal (hh _ (tablePartOf_equal_mem tab lh weights beta w vals p hp)), hev]
  have hs := sentOf_spec tab vals colv h0
  have hsome : ∀ c ∈ sentColumns tab, ((sentOf tab vals).getD c none).isSome :=
    fun c hc ↦ sentOf_isSome tab vals c hc (hw c hc)
  have hSF : ∀ fl ∈ tab.flushes.pull.zip tab.flushes.push, fl.2.length = fl.1.length ∧
      (∀ f ∈ fl.1, ∀ mc ∈ f, SentFactor (sentOf tab vals) mc.1) ∧
      ∀ f ∈ fl.2, ∀ mc ∈ f, SentFactor (sentOf tab vals) mc.1 := by
    intro fl hf
    obtain ⟨hlen, hm⟩ := hfl fl hf
    have key : ∀ f ∈ fl.1 ++ fl.2, ∀ mc ∈ f, SentFactor (sentOf tab vals) mc.1 := by
      intro f hf' mc hmc i j hij
      have := hm f hf' mc hmc (by rw [hij]; rfl)
      rw [hij] at this
      rcases this with h | h
      · exact Or.inl (hsome i h)
      · exact Or.inr (hsome j h)
    exact ⟨hlen, fun f hf' ↦ key f (List.mem_append_left _ hf'),
      fun f hf' ↦ key f (List.mem_append_right _ hf')⟩
  unfold tablePartOf at hh ⊢
  dsimp only at hh ⊢
  obtain ⟨hpull, hpush⟩ := flushFold_spec tab.opcode (w.take lh) weights beta (sentOf tab vals) ev colv hev hs
    _ _ hSF hh
  obtain ⟨hd1, hd2⟩ := degree_flushFold (fun c ↦ .table tab.opcode c) (w.take lh) weights beta
    (sentOf tab vals) (tab.flushes.pull.zip tab.flushes.push)
    ⟨1, 1, 1, 0, ((sentColumns tab).zip (List.range (sentColumns tab).length)).map fun p ↦
      Relation.equal (.table tab.opcode p.1) (w.take lh) (vals.getD p.2 0), vals.drop (sentColumns tab).length⟩
  refine ⟨fun c hc ↦ ?_, by rw [hpull, one_mul], by rw [hpush, one_mul], ?_, ?_⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hsome c hc)
    rw [hv, hs c v hv]
  · rw [hd1, tableDegrees_eq]
  · rw [hd2, tableDegrees_eq]

/-! ## The deployment's shape -/

/-- A valid shape's heights are at most `31`. -/
theorem heights_leK (D : KDeployment) (o : ℕ) : D.shape.heights.getD o 0 ≤ 31 := by
  have h := D.valid.2
  unfold Shape.validate at h
  simp at h
  by_cases ho : o < D.shape.heights.length
  · rw [List.getD_eq_getElem _ _ ho]
    exact h.1.2 _ (List.getElem_mem ho)
  · rw [List.getD_eq_default _ _ (by omega)]
    omega

/-- `SHA3` has at least one row variable (a valid shape with Flock: at least `7`). -/
theorem hB_posK (D : KDeployment) : 1 ≤ D.shape.heights.getD opSha3 0 := by
  have h := D.valid.2
  unfold Shape.validate at h
  simp at h
  rw [List.getD_eq_getElem?_getD]
  omega

/-! ## The quotients' chunks fit the digits -/

/-- **The Keccak quotients' chunks fit the digits** (`ChunksFit` with `constraintDegreeK`, `leafDegreeK`). -/
def ChunksFitK (S : Shape) : Prop :=
  (∀ e ∈ chunks (UniKeccak.Shape.constraintDegreeK S + 1), e < nDigits S) ∧
    ∀ b ∈ S.heap.blocks, ∀ d, UniKeccak.Shape.leafDegreeK b = some d → ∀ e ∈ chunks (d + 1), e < nDigits S

/-- **The Keccak tables' shapes, as the degrees read them**: at most `28` flushes, monomials of degree at most two,
at most `27` counters. -/
def TablesDegK : Prop :=
  ∀ tab ∈ tablesKeccak, (tab.flushes.pull.zip tab.flushes.push).length ≤ 28 ∧
    (∀ fl ∈ tab.flushes.pull.zip tab.flushes.push, ∀ f ∈ fl.1 ++ fl.2, ∀ mc ∈ f, mc.1.length ≤ 2) ∧
    tab.countColumns.length ≤ 27

set_option maxRecDepth 100000 in
theorem tablesDegK : TablesDegK := by
  unfold TablesDegK
  decide +kernel

/-- A Keccak table's leaf degrees are at most `57`. -/
theorem tableDegreesK_le (tab : Table) (htab : tab ∈ tablesKeccak) :
    (tableDegrees tab).1 ≤ 57 ∧ (tableDegrees tab).2 ≤ 57 := by
  obtain ⟨hn, hm, -⟩ := tablesDegK tab htab
  rw [tableDegrees_eq]
  have h1 : ∀ x ∈ (tab.flushes.pull.zip tab.flushes.push).map (fun fl ↦ tupleDegree fl.1), x ≤ 2 := by
    intro x hx
    obtain ⟨fl, hfl, rfl⟩ := List.mem_map.mp hx
    exact tupleDegree_le _ 2 (by norm_num) fun f hf mc hmc ↦ hm fl hfl f (List.mem_append_left _ hf) mc hmc
  have h2 : ∀ x ∈ (tab.flushes.pull.zip tab.flushes.push).map (fun fl ↦ tupleDegree fl.2), x ≤ 2 := by
    intro x hx
    obtain ⟨fl, hfl, rfl⟩ := List.mem_map.mp hx
    exact tupleDegree_le _ 2 (by norm_num) fun f hf mc hmc ↦ hm fl hfl f (List.mem_append_right _ hf) mc hmc
  have s1 := sum_le_of h1
  have s2 := sum_le_of h2
  rw [List.length_map] at s1 s2
  dsimp only
  constructor <;> omega

/-- **The Keccak constraint quotient's degree is below `2^(r_W + 5)`.** -/
theorem constraintDegreeK_lt (D : KDeployment) :
    UniKeccak.Shape.constraintDegreeK D.shape < 2 ^ (D.shape.constraintVars + 5) := by
  set rW := D.shape.constraintVars
  have hB : 2 ^ (rW + 5) = 32 * 2 ^ rW := by rw [pow_add]; ring
  have key : ∀ (L : List Table) (d : ℕ), d < 32 * 2 ^ rW → (∀ tab ∈ L, tab ∈ tablesKeccak) →
      L.foldl (UniSound.cdStep D.shape) d < 32 * 2 ^ rW := by
    intro L
    induction L with
    | nil => intro d hd _; exact hd
    | cons tab L ih =>
      intro d hd hL
      rw [List.foldl_cons]
      refine ih _ ?_ fun t ht ↦ hL t (List.mem_cons_of_mem _ ht)
      have htab := hL tab (List.mem_cons_self ..)
      have hcnt := (tablesDegK tab htab).2.2
      have hr := height_le_rW D.shape tab.opcode
      have hr31 := heights_leK D tab.opcode
      have hn : 2 ^ D.shape.heights.getD tab.opcode 0 ≤ 2 ^ rW := Nat.pow_le_pow_right (by norm_num) hr
      have hpos := Nat.two_pow_pos (D.shape.heights.getD tab.opcode 0)
      unfold UniSound.cdStep UniStatement.degree
      dsimp only
      generalize 2 ^ D.shape.heights.getD tab.opcode 0 = n at hn hpos ⊢
      generalize D.shape.heights.getD tab.opcode 0 = r at hr hr31 ⊢
      have h1 : (n - 1) * (1 + tab.countColumns.length) ≤ (n - 1) * 28 := Nat.mul_le_mul_left _ (by omega)
      have h2 : r * (n / 2) ≤ 31 * (n / 2) := Nat.mul_le_mul_right _ hr31
      split_ifs <;> simp only [max_lt_iff] <;> omega
  rw [constraintDegreeK_eq]
  unfold UniStatement.degree
  rw [hB]
  have hlm : 2 ^ D.shape.logMemory ≤ 2 ^ rW := Nat.pow_le_pow_right (by norm_num) (logMemory_le_rW D.shape)
  have := Nat.two_pow_pos rW
  refine max_lt (key tablesKeccak 0 (by positivity) fun _ h ↦ h) ?_
  omega

theorem rW_lt_nDigitsK (S : Shape) : S.constraintVars + 5 < nDigits S := by unfold nDigits; omega

theorem h_lt_nDigitsK (S : Shape) : S.heap.h + 1 < nDigits S := by unfold nDigits; omega

/-- **The Keccak quotients' chunks fit the digits**, at a valid shape whose heap's blocks are `HeapGood`'s. -/
theorem chunksFitK (D : KDeployment) (hH : HeapGood D.shape) : ChunksFitK D.shape := by
  have hN := rW_lt_nDigitsK D.shape
  refine ⟨fun e he ↦ ?_, fun b hb d hd e he ↦ ?_⟩
  · have := chunk_lt _ (D.shape.constraintVars + 6) (by
      have := constraintDegreeK_lt D
      rw [pow_succ]; omega) e he
    omega
  · have hbr := block_r_lt D.shape hH b hb
    have hhN := h_lt_nDigitsK D.shape
    have hblk := hH.2.2.2.2.2 b hb
    have hpos := Nat.two_pow_pos b.r
    unfold UniKeccak.Shape.leafDegreeK at hd
    rcases hlv : b.leaves with _ | _ | tt | _ <;> rw [hlv] at hd hblk
    · simp only [Option.some.injEq] at hd
      subst hd
      have := chunk_lt _ (b.r + 1) (by unfold UniStatement.degree; rw [pow_succ]; omega) e he
      omega
    · simp only [Option.some.injEq] at hd
      subst hd
      have := chunk_lt _ (b.r + 1) (by unfold UniStatement.degree; rw [pow_succ]; omega) e he
      omega
    · obtain ⟨ht6, hrt⟩ := hblk
      dsimp only at hd
      simp only [Option.some.injEq] at hd
      subst hd
      obtain ⟨hp1, hp2⟩ := tableDegreesK_le _ (tablesKeccak_mem tt ht6)
      have hr := height_le_rW D.shape tt
      have hmax : max (tableDegrees (tablesKeccak.getD tt default)).1
          (tableDegrees (tablesKeccak.getD tt default)).2 ≤ 57 := max_le hp1 hp2
      have hm : max (tableDegrees (tablesKeccak.getD tt default)).1 (tableDegrees (tablesKeccak.getD tt default)).2 *
          (2 ^ b.r - 1) ≤ 57 * (2 ^ b.r - 1) := Nat.mul_le_mul_right _ hmax
      have h64 : 2 ^ (b.r + 6) = 64 * 2 ^ b.r := by rw [pow_add]; ring
      have := chunk_lt _ (b.r + 6) (by unfold UniStatement.degree; omega) e he
      omega
    · simp at hd

end UniKeccakSound.IdsEval
