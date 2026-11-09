-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proof is `UniSound/Ids/Degrees.lean`'s
-- (`degBound_of`, `degBound_reference`) on the Keccak identity model (`Ids/Model.lean`'s `polysK`).
import UniSound.Ids.Degrees
import UniKeccakSound.IdsNum.Deployed
import UniKeccakSound.Code.Shape

/-!
# The Keccak identities' degrees (`DegBoundK`)

Every polynomial of `polysK` is bounded from its construction, symbolically in the shape's numbers; no polynomial
is evaluated. As `UniSound/Ids/Degrees.lean`, whose generic lemmas (sums, products, columns at polynomial points,
lifts, `Z_act`, `Z_bad`, the tuples' products, the quotients' chunks `Σ_c 2^(e_c) ≤ 5n/4`) are reused; what changes
is the Keccak VM's:

* **the columns** at their Keccak layouts' variables (`Layouts.lean`'s `c1_limbsK`, `c2_limbsK`, `setup_limbsK`);
  `q_flock`'s slot at `y(X)` reads `11` slot bits, still at most `h_SHA3 2^(h_SHA3 − 1)` (`ndeg_slotPK`);
* **the tables** `tablesKeccak` (the kernel reads their monomials, not their coefficients: `tablesK_pullDeg`,
  `tablesK_pushDeg`, `tablesK_oc`; `SHA3`'s products `54` and `54`, its `27` counters);
* **the constraints** with the `SHA3` lanes' copies `copy + slot(y) + offset` (`ndeg_constraintsK`), the constraint
  quotient's degree `Shape.constraintDegreeK` (`constraintDegreeK_le`).

**`degBoundK_of`**: `DegBoundK D Fl (treeB + wBK + Σ_b blockBK b)` at every Keccak deployment whose heap is
`HeapGood`; **`degBoundK_ref`**: `DegBoundK D Fl 19339139` (`< 2^25`) at the reference Keccak shape (the tree
`2^23 + 2`, `Z_bad P_W` `2,392,065`, the leaves `8,558,464`), by `norm_num`.
-/

namespace UniKeccakSound.IdsNum

open LeanVM.Parameters UniStatement Finset Polynomial UniSound UniSound.Ids UniSound.Ids.Eval UniKeccak UniKeccakSound
  UniKeccakSound.Ids

/-! ## Columns at polynomial points -/

/-- **A Keccak `C1` column** at the digits: below `2^v`, `v` its variables. -/
theorem ndeg_c1PK (S : Shape) (c : Stk) (col : Column) : (c1PK S c col).natDegree ≤ 2 ^ c1VarsK S col := by
  unfold c1PK
  refine ndeg_colPoly _ _ _ _ _ _ fun b hb ↦ ?_
  rw [c1_limbsK S col b hb, ← add_zero (c1VarsK S col)]
  exact sum_deg_pow digitP _ 0 fun l _ ↦ digit_le l

/-- **A Keccak `C2` column** at a point of coordinates of degree at most `2^(l+s)`. -/
theorem ndeg_c2PK (S : Shape) (c2 : Stk) (col : Column) (pt : ℕ → Polynomial E) (s : ℕ)
    (h : ∀ l, (pt l).natDegree ≤ 2 ^ (l + s)) :
    (c2PK S c2 col pt).natDegree ≤ 2 ^ (c2VarsK S col + s) := by
  unfold c2PK
  refine ndeg_colPoly _ _ _ _ _ _ fun b hb ↦ ?_
  rw [c2_limbsK S col b hb]
  exact sum_deg_pow pt _ s fun l _ ↦ h l

theorem ndeg_c2PK_digits (S : Shape) (c2 : Stk) (col : Column) :
    (c2PK S c2 col digitP).natDegree ≤ 2 ^ c2VarsK S col := by
  simpa using ndeg_c2PK S c2 col digitP 0 digit_le

/-- **The restriction `R_b`**: `T` at the block's mixed point, below `2^r`. -/
theorem ndeg_restrK (S : Shape) (c2 : Stk) (b : Block) : (c2PK S c2 .heap (mixP b)).natDegree ≤ 2 ^ b.r := by
  unfold c2PK
  refine ndeg_colPoly _ _ _ _ _ _ fun bl _ ↦ sum_deg_below _ _ _ fun l _ ↦ ?_
  unfold mixP
  split_ifs
  · exact ndeg_add (natDegree_digitP l) (ndeg_C _ _)
  · simp

/-- The setup's addresses at the digits. -/
theorem ndeg_suPK_address (S : Shape) (st : Stk) : (suPK S st .address digitP).natDegree ≤ 2 ^ S.logMemory := by
  unfold suPK
  refine ndeg_colPoly _ _ _ _ _ _ fun b hb ↦ ?_
  rw [(setup_limbsK S .address b hb).2 rfl, ← add_zero S.logMemory]
  exact sum_deg_pow digitP _ 0 fun l _ ↦ digit_le l

/-- The setup's bytecode tuples at `(α, w)`: below `2^lb`. -/
theorem ndeg_suPK_tuple (S : Shape) (st : Stk) (alphas : List E) :
    (suPK S st .bytecodeTuple (fun l ↦ if l < 4 then C (alphas.getD l 0) else digitP (l - 4))).natDegree ≤
      2 ^ S.logBytecode := by
  unfold suPK
  refine ndeg_colPoly _ _ _ _ _ _ fun b hb ↦ ?_
  rw [(setup_limbsK S .bytecodeTuple b hb).1 rfl,
    show S.logBytecode + 4 = 4 + S.logBytecode from add_comm _ _, Finset.sum_range_add]
  have h1 : ∑ x ∈ range 4, (if x < 4 then C (alphas.getD x 0) else digitP (x - 4)).natDegree = 0 :=
    Finset.sum_eq_zero fun x hx ↦ by rw [ite_eq_left (mem_range.mp hx), natDegree_C]
  rw [h1, zero_add]
  refine (Finset.sum_le_sum fun l _ ↦ ?_).trans (sum_two_pow_lt _).le
  rw [ite_eq_right (show ¬ 4 + l < 4 by omega), show 4 + l - 4 = l by omega]
  exact natDegree_digitP l

/-- **`q_flock`'s slot at `y(X)`** on the Keccak VM (`11` slot bits): at most `h_SHA3 2^(h_SHA3 − 1)`. -/
theorem ndeg_slotPK (S : Shape) (c : Stk) (slot : ℕ) :
    (slotPK S c slot).natDegree ≤ S.heights.getD opSha3 0 * 2 ^ (S.heights.getD opSha3 0 - 1) := by
  unfold slotPK
  refine ndeg_colPoly _ _ _ _ _ _ fun b hb ↦ ?_
  rw [c1_limbsK S .qflock b hb]
  show ∑ l ∈ range (S.heights.getD opSha3 0 + qflockRowBits), _ ≤ _
  rw [show S.heights.getD opSha3 0 + qflockRowBits = qflockRowBits + S.heights.getD opSha3 0 from
    add_comm _ _, Finset.sum_range_add]
  have h1 : ∑ x ∈ range qflockRowBits, (if x < qflockRowBits then C (bitE slot x)
      else yP (coordinateFunctionals (S.heights.getD opSha3 0)) (x - qflockRowBits)).natDegree = 0 :=
    Finset.sum_eq_zero fun x hx ↦ by rw [ite_eq_left (mem_range.mp hx), natDegree_C]
  rw [h1, zero_add]
  refine (Finset.sum_le_sum (g := fun _ ↦ 2 ^ (S.heights.getD opSha3 0 - 1)) fun l _ ↦ ?_).trans
    (by simp)
  rw [ite_eq_right (show ¬ qflockRowBits + l < qflockRowBits by omega)]
  have := ndeg_yP (coordinateFunctionals (S.heights.getD opSha3 0)) (qflockRowBits + l - qflockRowBits)
  rwa [coordinateFunctionals_size] at this

/-! ## The Keccak tables, as the degrees read them (the kernel reads monomials, not coefficients) -/

/-- The Keccak tables' pull degrees. -/
def pullLK : List ℕ := [8, 8, 4, 8, 8, 54]

/-- The Keccak tables' push degrees. -/
def pushLK : List ℕ := [8, 8, 4, 8, 9, 54]

/-- The Keccak tables' opcodes and counters' numbers. -/
def ocLK : List (ℕ × ℕ) := [(0, 4), (1, 4), (2, 2), (3, 4), (4, 4), (5, 27)]

set_option maxRecDepth 100000 in
theorem tablesK_pullDeg : tablesKeccak.map pullDeg = pullLK := by decide +kernel

set_option maxRecDepth 100000 in
theorem tablesK_pushDeg : tablesKeccak.map pushDeg = pushLK := by decide +kernel

set_option maxRecDepth 100000 in
theorem tablesK_oc : tablesKeccak.map (fun tab ↦ (tab.opcode, tab.countColumns.length)) = ocLK := by
  decide +kernel

theorem pullDegK_getD (t : ℕ) : pullDeg (tablesKeccak.getD t default) = pullLK.getD t 0 := by
  rw [← tablesK_pullDeg, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases tablesKeccak[t]? <;> rfl

theorem pushDegK_getD (t : ℕ) : pushDeg (tablesKeccak.getD t default) = pushLK.getD t 0 := by
  rw [← tablesK_pushDeg, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases tablesKeccak[t]? <;> rfl

theorem mem_ocLK {tab : Table} (h : tab ∈ tablesKeccak) : (tab.opcode, tab.countColumns.length) ∈ ocLK := by
  rw [← tablesK_oc]
  exact List.mem_map.mpr ⟨tab, h, rfl⟩

/-! ## Quotients -/

theorem quotPK_cons (S : Shape) (c2 : Stk) (column : ℕ → Column) (e : ℕ) (rest : List ℕ) :
    quotPK S c2 column (e :: rest) =
      c2PK S c2 (column 0) digitP + digitP e * quotPK S c2 (fun c ↦ column (c + 1)) rest := by
  unfold quotPK
  rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
    List.range_zero, List.map_nil, List.prod_nil, mul_one, ← List.sum_map_mul_left]
  refine congrArg (fun z ↦ c2PK S c2 (column 0) digitP + z) ?_
  refine congrArg List.sum (List.map_congr_left fun c _ ↦ ?_)
  show c2PK S c2 (column (c + 1)) digitP *
      ((List.range (c + 1)).map fun c' ↦ digitP ((e :: rest).getD c' 0)).prod =
    digitP e * (c2PK S c2 (column (c + 1)) digitP * ((List.range c).map fun c' ↦ digitP (rest.getD c' 0)).prod)
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  have h : ((fun c' ↦ digitP ((e :: rest).getD c' 0)) ∘ Nat.succ) = fun c' ↦ digitP (rest.getD c' 0) :=
    funext fun c' ↦ by simp
  rw [h, List.getD_cons_zero]
  ring

/-- **A quotient from its chunks**: at most `Σ_c 2^(e_c)`. -/
theorem ndeg_quotPK (S : Shape) (c2 : Stk) : ∀ (column : ℕ → Column) (sizes : List ℕ),
    (∀ c < sizes.length, (c2PK S c2 (column c) digitP).natDegree ≤ 2 ^ sizes.getD c 0) →
    (quotPK S c2 column sizes).natDegree ≤ (sizes.map (2 ^ ·)).sum
  | _, [], _ => by simp [quotPK]
  | column, e :: rest, h => by
    rw [quotPK_cons]
    have h0 := h 0 (by simp)
    have ih := ndeg_quotPK S c2 (fun c ↦ column (c + 1)) rest
      (fun c hc ↦ by simpa using h (c + 1) (by simp; omega))
    simp only [List.getD_cons_zero] at h0
    rw [List.map_cons, List.sum_cons]
    exact ndeg_add (h0.trans (Nat.le_add_right _ _)) (ndeg_mul (natDegree_digitP e) ih le_rfl)

/-! ## The constraint quotient's degree -/

/-- **The constraint quotient's degree bound** on the Keccak VM. -/
def cdBK (S : Shape) : ℕ := max ((ocLK.map (cdOf S)).foldr max 0) (2 ^ S.logMemory)

theorem constraintDegreeK_le (S : Shape) : Shape.constraintDegreeK S ≤ cdBK S := by
  have key : ∀ (L : List Table), (∀ tab ∈ L, tab ∈ tablesKeccak) → ∀ d ≤ (ocLK.map (cdOf S)).foldr max 0,
      L.foldl (UniSound.cdStep S) d ≤ (ocLK.map (cdOf S)).foldr max 0 := by
    intro L
    induction L with
    | nil => intro _ d hd; exact hd
    | cons tab L ih =>
      intro hL d hd
      rw [List.foldl_cons]
      have htab : tab ∈ tablesKeccak := hL tab (List.mem_cons_self ..)
      have hc : cdOf S (tab.opcode, tab.countColumns.length) ≤ (ocLK.map (cdOf S)).foldr max 0 :=
        le_foldr_max (List.mem_map.mpr ⟨_, mem_ocLK htab, rfl⟩)
      exact ih (fun t ht ↦ hL t (List.mem_cons_of_mem _ ht)) _ (cdStep_le S _ d tab hd hc)
  rw [constraintDegreeK_eq]
  unfold cdBK
  exact max_le_max (key tablesKeccak (fun _ h ↦ h) 0 (Nat.zero_le _)) (Nat.sub_le _ _)

/-! ## The constraints' degrees -/

/-- **The Keccak constraints' `W_i` bound**: the tables', `q_flock`'s slots', the public lines'. -/
def wMaxK (S : Shape) : ℕ :=
  max (2 ^ S.logMemory) (max (S.heights.getD opSha3 0 * 2 ^ (S.heights.getD opSha3 0 - 1))
    ((ocLK.map (wOf S)).foldr max 0))

theorem wOf_leK (S : Shape) {tab : Table} (h : tab ∈ tablesKeccak) :
    wOf S (tab.opcode, tab.countColumns.length) ≤ wMaxK S :=
  (le_foldr_max (List.mem_map.mpr ⟨_, mem_ocLK h, rfl⟩)).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- **Each Keccak constraint `(M_i, W_i)`**: `deg M_i + deg W_i ≤ 2^(r_W) + wMaxK`. -/
theorem ndeg_constraintsK (S : Shape) (c1 : Stk) (pw : List E) :
    ∀ mw ∈ constraintsPK S c1 pw, mw.1.natDegree + mw.2.natDegree ≤ 2 ^ S.constraintVars + wMaxK S := by
  intro mw hmw
  unfold constraintsPK at hmw
  rcases List.mem_append.mp hmw with hmw | hmw
  · obtain ⟨tab, htab, hmw⟩ := List.mem_flatMap.mp hmw
    have hw := wOf_leK S htab
    unfold wOf at hw
    dsimp only at hw
    have hcol : ∀ i, (c1PK S c1 (.table tab.opcode i)).natDegree ≤ 2 ^ S.heights.getD tab.opcode 0 :=
      fun i ↦ ndeg_c1PK S c1 _
    have hinv : (c1PK S c1 (.inverse tab.opcode)).natDegree ≤ 2 ^ S.heights.getD tab.opcode 0 :=
      ndeg_c1PK S c1 _
    have hlift := ndeg_liftP (S.heights.getD tab.opcode 0) S.constraintVars
    generalize hH : 2 ^ S.heights.getD tab.opcode 0 = H at hcol hinv hw
    have hm1 : H ≤ H * max 1 tab.countColumns.length :=
      Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.one_pos (le_max_left _ _))
    have hm2 : H * (1 + max 1 tab.countColumns.length) = H + H * max 1 tab.countColumns.length := by ring
    have hm3 : tab.countColumns.length * H ≤ H * max 1 tab.countColumns.length := by
      rw [mul_comm]; exact Nat.mul_le_mul_left _ (le_max_right _ _)
    unfold tableConstraintsPK at hmw
    dsimp only at hmw
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmw
    rcases hmw with ((hmw | rfl) | hmw)
    · split_ifs at hmw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmw
        rcases hmw with rfl | rfl
        · refine Nat.add_le_add hlift ?_
          exact ndeg_add ((hcol _).trans (by omega)) (ndeg_mul (hcol _) (hcol _) (by omega))
        · refine Nat.add_le_add hlift ?_
          exact ndeg_mul (hcol _) (ndeg_add (hcol _) ((natDegree_one).le.trans (Nat.zero_le _)))
            (by omega)
      · simp at hmw
    · refine Nat.add_le_add hlift ?_
      have hprod : ((tab.countColumns.map fun c ↦ c1PK S c1 (.table tab.opcode c)).prod).natDegree ≤
          tab.countColumns.length * H := by
        refine (ndeg_listProd _).trans ?_
        rw [List.map_map]
        refine (sum_le_of (k := H) fun x hx ↦ ?_).trans (le_of_eq (by rw [List.length_map]))
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        exact hcol c
      exact ndeg_add (ndeg_mul hinv hprod (by omega)) (by simp)
    · split_ifs at hmw
      · obtain ⟨c, _, hc⟩ := List.mem_filterMap.mp hmw
        obtain ⟨slot, _, rfl⟩ := Option.map_eq_some_iff.mp hc
        refine Nat.add_le_add hlift (ndeg_add (ndeg_add ((hcol c).trans ?_)
          ((ndeg_slotPK S c1 slot).trans ?_)) (ndeg_C _ _))
        · omega
        · unfold wMaxK
          exact (le_max_left _ _).trans (le_max_right _ _)
      · simp at hmw
  · unfold linesPK at hmw
    obtain ⟨lk, _, rfl⟩ := List.mem_map.mp hmw
    refine Nat.add_le_add (ndeg_liftP 1 _) ?_
    have hm : (c1PK S c1 (.memory lk.2)).natDegree ≤ 2 ^ S.logMemory := ndeg_c1PK S c1 _
    have h1 : (1 : ℕ) ≤ 2 ^ S.logMemory := Nat.one_le_two_pow
    refine (ndeg_add (ndeg_add hm (ndeg_C _ _)) (ndeg_mul natDegree_X_le (natDegree_C _).le
      (by omega))).trans (le_max_left _ _)

/-- **The Keccak constraint quotient's identity `Z_bad (Σ γ^i M_i W_i + Q_W w_{r_W})`.** -/
def wBK (S : Shape) : ℕ :=
  2 * 2 ^ (S.heights.getD opSha3 0 - 1) +
    max (2 ^ S.constraintVars + wMaxK S) (chB (cdBK S + 1) + 2 ^ S.constraintVars)

theorem ndeg_wPK (S : Shape) (c1 c2 : Stk) (pw : List E) (gamma p0 : E) :
    (wPK S c1 c2 pw gamma p0).natDegree ≤ wBK S := by
  unfold wPK wBK
  refine ndeg_mul (ndeg_zBad S p0) (ndeg_add ?_ ?_) le_rfl
  · refine ndeg_listSum _ _ fun p hp ↦ ?_
    obtain ⟨⟨mw, i⟩, hmw, rfl⟩ := List.mem_map.mp hp
    have := ndeg_constraintsK S c1 pw mw (List.of_mem_zip hmw).1
    exact (ndeg_mul (ndeg_Cmul le_rfl) le_rfl this).trans (le_max_left _ _)
  · refine (ndeg_mul ((ndeg_quotPK S c2 _ _ fun c _ ↦ ndeg_c2PK_digits S c2 _).trans
      ((chunks_le_chB _).trans (chB_mono (Nat.add_le_add_right (constraintDegreeK_le S) 1))))
      (natDegree_digitP _) le_rfl).trans (le_max_right _ _)

/-! ## The tree and the root -/

theorem ndeg_treePK (S : Shape) (c2 : Stk) : (treePK S c2).natDegree ≤ treeB S := by
  unfold treePK treeB
  have hA : (c2PK S c2 .heap (fun l ↦ digitP (l + 1))).natDegree ≤ 2 ^ (S.heap.h + 1) :=
    ndeg_c2PK S c2 .heap _ 1 fun l ↦ natDegree_digitP (l + 1)
  have hB : (c2PK S c2 .heap digitP).natDegree ≤ 2 ^ S.heap.h := ndeg_c2PK_digits S c2 .heap
  have hB2 : (c2PK S c2 .heap (fun l ↦ if l = 0 then digitP 0 + 1 else digitP l)).natDegree ≤
      2 ^ S.heap.h := by
    exact ndeg_c2PK S c2 .heap (fun l ↦ if l = 0 then digitP 0 + 1 else digitP l) 0 fun l ↦ by
      split_ifs with h
      · subst h; exact digit_one_le 0
      · exact digit_le l
  have hQ0 : (c2PK S c2 (.treeQuotient 0) digitP).natDegree ≤ 2 ^ S.heap.h :=
    ndeg_c2PK_digits S c2 (.treeQuotient 0)
  have hQ1 : (c2PK S c2 (.treeQuotient 1) digitP).natDegree ≤ 2 ^ 0 :=
    ndeg_c2PK_digits S c2 (.treeQuotient 1)
  rw [pow_zero] at hQ1
  have h1 : (digitP 1).natDegree ≤ 2 := natDegree_digitP 1
  have hh := natDegree_digitP S.heap.h
  rw [pow_succ] at hA ⊢
  exact ndeg_add (ndeg_mul h1 (ndeg_add hA (ndeg_mul hB hB2 (by omega))) (by omega))
    (ndeg_mul hh (ndeg_add (hQ0.trans (Nat.le_succ _)) (ndeg_mul hh hQ1 le_rfl)) (by omega))

theorem ndeg_rootPK (S : Shape) (c2 : Stk) (weights : Array E) (beta : E) :
    (rootPK S c2 weights beta).natDegree ≤ 0 := by
  unfold rootPK
  refine ndeg_add (ndeg_Cmul ?_) (ndeg_C _ _)
  unfold c2PK
  refine ndeg_colPoly _ _ _ _ _ _ fun _ _ ↦ (Finset.sum_eq_zero fun l _ ↦ ?_).le
  split_ifs <;> simp

/-! ## The heap blocks' leaves -/

/-- **A Keccak heap block's leaf identity's degree bound.** -/
def blockBK (S : Shape) (b : Block) : ℕ :=
  match b.leaves with
  | .unused => 2 ^ b.r
  | .memory => memB b.r S.logMemory
  | .bytecode => memB b.r S.logBytecode
  | .table t => tabB b.r (pullLK.getD t 0) (pushLK.getD t 0)

theorem ndeg_memPullPK (S : Shape) (c1 setup : Stk) (weights : Array E) (beta : E) :
    (memPullPK S c1 setup weights beta).natDegree ≤ 2 ^ S.logMemory := by
  unfold memPullPK
  have hm : ∀ k, (c1PK S c1 (.memory k)).natDegree ≤ 2 ^ S.logMemory := fun k ↦ ndeg_c1PK S c1 (.memory k)
  refine ndeg_add (ndeg_add (ndeg_add (ndeg_add (ndeg_C _ _) (ndeg_C _ _))
    (ndeg_Cmul (ndeg_suPK_address S setup))) (ndeg_Cmul (hm 3))) (ndeg_listSum _ _ fun p hp ↦ ?_)
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
  exact ndeg_Cmul (hm k)

theorem ndeg_bcPullPK (S : Shape) (c1 setup : Stk) (alphas : List E) (weights : Array E) (beta : E) :
    (bcPullPK S c1 setup alphas weights beta).natDegree ≤ 2 ^ S.logBytecode := by
  unfold bcPullPK
  exact ndeg_add (ndeg_add (ndeg_C _ _) (ndeg_suPK_tuple S setup alphas))
    (ndeg_Cmul (ndeg_c1PK S c1 .bytecodeFinal))

/-- A leaf quotient's chunks, at the block's leaf degree. -/
theorem ndeg_leafQK (S : Shape) (c2 : Stk) (b : Block) (i d : ℕ) (hbi : S.heap.blocks.getD i default = b)
    (hd : Shape.leafDegreeK b = some d) :
    (quotPK S c2 (Column.leafQuotient i) (chunks (d + 1))).natDegree ≤ chB (d + 1) := by
  refine (ndeg_quotPK S c2 _ _ fun c _ ↦ ?_).trans (chunks_le_chB _)
  have hv : c2VarsK S (.leafQuotient i c) = (chunks (d + 1)).getD c 0 := by
    simp only [c2VarsK, hbi, hd]
  rw [← hv]
  exact ndeg_c2PK_digits S c2 _

/-- **A Keccak heap block's leaf identity**: at most `blockBK`. -/
theorem ndeg_blockPK (S : Shape) (hH : HeapGood S) (c1 c2 setup : Stk) (rows : List ℕ) (alphas : List E)
    (beta : E) (b : Block) (i : ℕ) (hb : b ∈ S.heap.blocks) (hbi : S.heap.blocks.getD i default = b) :
    (blockPK S c1 c2 setup rows alphas beta b i).natDegree ≤ blockBK S b := by
  have hblk := hH.2.2.2.2.2 b hb
  have hR := ndeg_restrK S c2 b
  have hw := natDegree_digitP b.r
  unfold blockPK blockBK
  rcases hlv : b.leaves with _ | _ | t | _ <;> rw [hlv] at hblk <;> dsimp only
  · -- The memory's block.
    have hd : Shape.leafDegreeK b = some (UniStatement.degree (2 * (2 ^ b.r - 1)) (2 ^ b.r)) := by
      unfold Shape.leafDegreeK; rw [hlv]
    have hq := ndeg_leafQK S c2 b i _ hbi hd
    have hp := ndeg_memPullPK S c1 setup (eqKernel alphas) beta
    unfold memB
    refine ndeg_add (ndeg_add (ndeg_mul hR hp (le_max_left _ _)) (ndeg_mul hq hw (le_max_right _ _)))
      (ndeg_add (hp.trans ?_) (ndeg_Cmul (ndeg_add (by simp) ((ndeg_c1PK S c1 (.memory 3)).trans ?_))))
    · exact (Nat.le_add_left _ _).trans (le_max_left _ _)
    · exact (Nat.le_add_left _ _).trans (le_max_left _ _)
  · -- The bytecode's block.
    have hd : Shape.leafDegreeK b = some (UniStatement.degree (2 * (2 ^ b.r - 1)) (2 ^ b.r)) := by
      unfold Shape.leafDegreeK; rw [hlv]
    have hq := ndeg_leafQK S c2 b i _ hbi hd
    have hp := ndeg_bcPullPK S c1 setup alphas (eqKernel alphas) beta
    unfold memB
    refine ndeg_add (ndeg_add (ndeg_mul hR hp (le_max_left _ _)) (ndeg_mul hq hw (le_max_right _ _)))
      (ndeg_add (hp.trans ?_) (ndeg_Cmul (ndeg_add (by simp) ((ndeg_c1PK S c1 .bytecodeFinal).trans ?_))))
    · exact (Nat.le_add_left _ _).trans (le_max_left _ _)
    · exact (Nat.le_add_left _ _).trans (le_max_left _ _)
  · -- A table's block.
    obtain ⟨ht, hr⟩ := hblk
    have hop := tablesKeccak_opcode t ht
    have hd : Shape.leafDegreeK b = some (UniStatement.degree (max (tableDegrees (tablesKeccak.getD t default)).1
        (tableDegrees (tablesKeccak.getD t default)).2 * (2 ^ b.r - 1) + (2 ^ b.r - Shape.leastRows b.r))
        (2 ^ b.r)) := by
      unfold Shape.leafDegreeK; rw [hlv]
    have hq := ndeg_leafQK S c2 b i _ hbi hd
    obtain ⟨hpd, hppd⟩ := tableDegrees_le' (tablesKeccak.getD t default)
    rw [pullDegK_getD] at hpd
    rw [pushDegK_getD] at hppd
    have hq' : (quotPK S c2 (Column.leafQuotient i) (chunks (UniStatement.degree (max
        (tableDegrees (tablesKeccak.getD t default)).1 (tableDegrees (tablesKeccak.getD t default)).2 *
          (2 ^ b.r - 1) + (2 ^ b.r - Shape.leastRows b.r)) (2 ^ b.r) + 1))).natDegree ≤
        chB (UniStatement.degree (max (1 + pullLK.getD t 0) (pushLK.getD t 0) * (2 ^ b.r - 1) +
          (2 ^ b.r - Shape.leastRows b.r)) (2 ^ b.r) + 1) := by
      refine hq.trans (chB_mono (Nat.add_le_add_right (Nat.sub_le_sub_right (Nat.add_le_add_right
        (Nat.mul_le_mul_right _ (max_le_max hpd hppd)) _) _) _))
    have hcol : ∀ c, (c1PK S c1 (.table (tablesKeccak.getD t default).opcode c)).natDegree ≤ 2 ^ b.r :=
      fun c ↦ by
        rw [hop, hr]
        exact ndeg_c1PK S c1 _
    have hpull := ndeg_pullP (tablesKeccak.getD t default) (eqKernel alphas) beta _ _ hcol
    have hpush := ndeg_pushP (tablesKeccak.getD t default) (eqKernel alphas) beta _ _ hcol
    rw [pullDegK_getD] at hpull
    rw [pushDegK_getD] at hpush
    have hZ := ndeg_zActP ((List.range (b.r + 1)).map fun j ↦ intBits (rows.getD t 0) j 1) b.r
    have hZ2 : (zActP ((List.range (b.r + 1)).map fun j ↦ intBits (rows.getD t 0) j 1) b.r ^ 2).natDegree ≤
        2 ^ (b.r + 2) := by
      refine natDegree_pow_le.trans ?_
      have e : 2 ^ (b.r + 2) = 2 ^ (b.r + 1) * 2 := by ring
      rw [e]
      omega
    unfold tabB
    refine ndeg_add (ndeg_add (ndeg_add ?_ ?_) ?_) ?_
    · exact ndeg_mul hR (ndeg_add (ndeg_mul hpull hw le_rfl |>.trans (le_max_left _ _))
        (hZ2.trans (le_max_right _ _))) (le_max_left _ _)
    · exact ndeg_mul hq' (ndeg_mul hw hZ le_rfl) ((le_max_left _ _).trans (le_max_right _ _))
    · exact (ndeg_mul hpush hw le_rfl).trans
        ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    · exact hZ2.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  · -- An unused block.
    exact ndeg_add hR ((natDegree_one).le.trans (Nat.zero_le _))

/-! ## The identities' degrees -/

/-- **The Keccak identities' degrees, summed**, at a deployment whose heap is `HeapGood`. -/
theorem degBoundK_of (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (hH : HeapGood D.shape) :
    DegBoundK D Fl (treeB D.shape + wBK D.shape + (D.shape.heap.blocks.map (blockBK D.shape)).sum) := by
  intro s c1 ch fd c2
  unfold polysK
  split_ifs
  · simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, List.map_map]
    have h1 := ndeg_treePK D.shape c2
    have h2 := ndeg_rootPK D.shape c2 (eqKernel (alphasOf ch)) (betaOf ch)
    have h3 := ndeg_wPK D.shape c1 c2 (publicWordsOf s.1.toList) (gammaOf ch) ((Fl.prog.out fd []).1.getD 0 0)
    have h4 : ((D.shape.heap.blocks.zip (List.range D.shape.heap.blocks.length)).map
        (Polynomial.natDegree ∘ fun bi ↦ blockPK D.shape c1 c2 (setupStkK D) s.2 (alphasOf ch)
          (betaOf ch) bi.1 bi.2)).sum ≤ (D.shape.heap.blocks.map (blockBK D.shape)).sum := by
      rw [← map_zip_fst D.shape.heap.blocks (List.range D.shape.heap.blocks.length) (by simp)
        (blockBK D.shape)]
      refine list_sum_map_le _ _ _ fun bi hbi ↦ ?_
      obtain ⟨b, i⟩ := bi
      exact ndeg_blockPK D.shape hH c1 c2 _ s.2 (alphasOf ch) (betaOf ch) b i (List.of_mem_zip hbi).1
        (mem_zip_range_iff _ default _ hbi).2
    omega
  · simp

theorem treeBK_ref : treeB keccakRefShape = 2 ^ 23 + 2 := by
  rw [treeB, heapK_ref.1]

/-- **The bound at the reference Keccak shape**, by `norm_num` on the closed sum (the shape rewritten to its
numbers first, so nothing reduces its heap). -/
theorem refBoundK :
    treeB keccakRefShape + wBK keccakRefShape + ((heapBlocksK.map Block.ofTuple).map (blockBK keccakRefShape)).sum ≤
      19339139 := by
  rw [treeBK_ref, keccakRef_eq]
  simp only [heapBlocksK, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Block.ofTuple,
    blockBK, wBK, wMaxK, cdBK, cdOf, wOf, ocLK, tabB, memB, chB, pullLK, pushLK, List.foldr_cons,
    List.foldr_nil, List.getD_cons_succ, List.getD_cons_zero, Shape.leastRows, UniStatement.degree,
    Shape.constraintVars, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, opSha3]
  norm_num [max_def]

/-- **The Keccak identities' degrees at the reference shape**: at most `19,339,139`. -/
theorem degBoundK_ref (D : KDeployment) {F : KeccakVm.KeccakFlockSpec} {κ : ℕ} {v : KeccakVariant}
    (Fl : KFlockSound F κ v) (hD : D.shape = keccakRefShape) : DegBoundK D Fl 19339139 := by
  intro s c1 ch fd c2
  refine (degBoundK_of D Fl (hD ▸ heapGoodK_ref) s c1 ch fd c2).trans ?_
  rw [hD, heapK_blocks_ref]
  exact refBoundK

end UniKeccakSound.IdsNum

/-- info: 'UniKeccakSound.IdsNum.degBoundK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.degBoundK_of

/-- info: 'UniKeccakSound.IdsNum.degBoundK_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsNum.degBoundK_ref
