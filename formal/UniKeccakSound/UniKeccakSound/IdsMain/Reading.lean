-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The proofs are `UniSound/Ids/Deployed.lean`'s
-- (`c1Limbs`, `setupLimbs`), `UniSound/Ids/Counts.lean`'s (`c1Absent`) and `UniSound/Ids/Facts.lean`'s
-- (`tablesFacts`), for the Keccak VM's layouts (`layoutsK`) and tables (`tablesKeccak`).
import UniSound.Ids.Counts
import UniSound.Ids.Facts
import UniKeccakSound.Ids.FlockEnd

/-!
# How the Keccak verifier's stacks and tables are read

* **`c1LimbsK`**: every column of `C1` on the Keccak VM is one limb, at every shape: the tables' columns
  (`tablesKeccak`, the `SHA3` table's 86 included) and their `z_T`, the memory's four, the bytecode's final
  counts, `q_flock` (`h_SHA3 + 11` variables). By `limbs_new_single`: each is named once (`c1NamesK`, kernel).
* **`c1AbsentK`**: a table's column past its width has no limbs.
* **`setupLimbsK`**, **`setupAlignedK`**: the setup's two columns, as BLAKE2s's (the same columns).
* **`tablesFactsK`**: the Keccak tables' flushes have as many pulls as pushes, tuples of at most `16` forms, every
  coefficient in `K` (`good_sha3`: the `SHA3` table's state step, bytecode read and `26` cell reads).
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters UniStatement UniSound UniSound.Ids UniKeccak

/-! ## `C1`'s columns -/

/-- `C1`'s column names on the Keccak VM (no shape). -/
def c1NamesK : List Column :=
  [.qflock] ++ tablesKeccak.flatMap (fun t ↦
      (List.range t.width).map (fun c ↦ Column.table t.opcode c) ++ [.inverse t.opcode]) ++
    (List.range 4).map Column.memory ++ [.bytecodeFinal]

/-- A `C1` column's variables at a shape on the Keccak VM. -/
def c1VarsK (S : Shape) : Column → ℕ
  | .qflock => S.heights.getD opSha3 0 + qflockRowBits
  | .table o _ => S.heights.getD o 0
  | .inverse o => S.heights.getD o 0
  | .memory _ => S.logMemory
  | .bytecodeFinal => S.logBytecode
  | _ => 0

theorem c1ColsK_eq (S : Shape) : c1ColsK S = c1NamesK.map fun c ↦ (c, c1VarsK S c, false) := by
  simp only [c1ColsK, c1NamesK, List.map_append, List.map_flatMap, List.map_cons, List.map_nil,
    List.map_map]
  rfl

theorem c1ColsK_filter (S : Shape) (col : Column) (h : c1NamesK.filter (· == col) = [col]) :
    (c1ColsK S).filter (fun x ↦ x.1 == col) = [(col, c1VarsK S col, false)] := by
  rw [c1ColsK_eq, List.filter_map]
  have e : ((fun x : Column × ℕ × Bool ↦ x.1 == col) ∘ fun c ↦ (c, c1VarsK S c, false)) = (· == col) := rfl
  rw [e, h]
  rfl

section Kernel

set_option maxRecDepth 100000

theorem c1NamesK_table : ∀ o < 6, ∀ i < (tablesKeccak.getD o default).width,
    c1NamesK.filter (· == Column.table o i) = [.table o i] := by decide +kernel

theorem c1NamesK_inverse : ∀ o < 6, c1NamesK.filter (· == Column.inverse o) = [.inverse o] := by
  decide +kernel

theorem c1NamesK_memory : ∀ k < 4, c1NamesK.filter (· == Column.memory k) = [.memory k] := by
  decide +kernel

theorem c1NamesK_bytecodeFinal : c1NamesK.filter (· == Column.bytecodeFinal) = [.bytecodeFinal] := by
  decide +kernel

end Kernel

/-- **`C1`'s columns are one limb each** on the Keccak VM (`C1Limbs`'s form; `q_flock` in `c1LayoutK_qflock`). -/
structure C1LimbsK (S : Shape) : Prop where
  table : ∀ o < 6, ∀ i < (tablesKeccak.getD o default).width, ∃ off,
    (layoutOfK S .c1).limbs (.table o i) = [(0, S.heights.getD o 0, off)]
  inverse : ∀ o < 6, ∃ off, (layoutOfK S .c1).limbs (.inverse o) = [(0, S.heights.getD o 0, off)]
  memory : ∀ k < 4, ∃ off, (layoutOfK S .c1).limbs (.memory k) = [(0, S.logMemory, off)]
  bytecodeFinal : ∃ off, (layoutOfK S .c1).limbs .bytecodeFinal = [(0, S.logBytecode, off)]

theorem c1LimbsK (S : Shape) : C1LimbsK S where
  table o ho i hi := by
    rw [layoutOfK_c1, c1LayoutK_eq]
    exact limbs_new_single _ _ _ (c1ColsK_filter S _ (c1NamesK_table o ho i hi))
  inverse o ho := by
    rw [layoutOfK_c1, c1LayoutK_eq]
    exact limbs_new_single _ _ _ (c1ColsK_filter S _ (c1NamesK_inverse o ho))
  memory k hk := by
    rw [layoutOfK_c1, c1LayoutK_eq]
    exact limbs_new_single _ _ _ (c1ColsK_filter S _ (c1NamesK_memory k hk))
  bytecodeFinal := by
    rw [layoutOfK_c1, c1LayoutK_eq]
    exact limbs_new_single _ _ _ (c1ColsK_filter S _ c1NamesK_bytecodeFinal)

theorem tablesKeccak_eq : tablesKeccak = [tables.getD 0 default, tables.getD 1 default, tables.getD 2 default,
    tables.getD 3 default, tables.getD 4 default, ⟨opSha3, sha3Columns, flushesSha3⟩] := rfl

/-- Every Keccak table is the one at its opcode. -/
theorem tablesKeccak_getD_opcode : ∀ tab ∈ tablesKeccak, tablesKeccak.getD tab.opcode default = tab := by
  rw [tablesKeccak_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro tab (rfl | rfl | rfl | rfl | rfl | rfl) <;> rfl

theorem tablesKeccak_opcode (o : ℕ) (ho : o < 6) : (tablesKeccak.getD o default).opcode = o := by
  interval_cases o <;> rfl

theorem tablesKeccak_mem (o : ℕ) (ho : o < 6) : tablesKeccak.getD o default ∈ tablesKeccak := by
  rw [List.getD_eq_getElem _ _ (by rw [tablesKeccak_eq]; simp; omega)]
  exact List.getElem_mem _

/-- **A Keccak table's column past its width has no limbs in `C1`**, at every shape. -/
theorem c1AbsentK (S : Shape) : ∀ o < 6, ∀ i, (tablesKeccak.getD o default).width ≤ i →
    (layoutOfK S .c1).limbs (.table o i) = [] := by
  intro o _ i hi
  rw [layoutOfK_c1, c1LayoutK_eq]
  refine limbs_new_absent _ _ fun x hx he ↦ ?_
  rw [c1ColsK_eq] at hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  dsimp only at he
  subst he
  unfold c1NamesK at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap,
    List.mem_map, List.mem_range] at hc
  rcases hc with ((h | ⟨tab, htab, ⟨c, hc, he⟩ | h⟩) | ⟨k, _, h⟩) | h
  · exact Column.noConfusion h
  · simp only [Column.table.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [tablesKeccak_getD_opcode tab htab] at hi
    omega
  · exact Column.noConfusion h
  · exact Column.noConfusion h
  · exact Column.noConfusion h

/-! ## The setup -/

theorem layoutOfK_setup (S : Shape) : layoutOfK S .setup = StackLayout.new (setupCols S) := rfl

theorem setupLimbsK (S : Shape) :
    (∃ off, (layoutOfK S .setup).limbs .address = [(0, S.logMemory, off)]) ∧
      ∃ off, (layoutOfK S .setup).limbs .bytecodeTuple = [(0, S.logBytecode + 4, off)] := by
  have h := setupLimbs S
  unfold SetupLimbs at h
  rw [layoutOf_setup] at h
  rw [layoutOfK_setup]
  exact h

theorem setupAlignedK (S : Shape) : LayoutAligned (layoutOfK S .setup) := by
  rw [layoutOfK_setup]; exact layoutAligned_new _

theorem c1AlignedK (S : Shape) : LayoutAligned (layoutOfK S .c1) := by
  rw [layoutOfK_c1, c1LayoutK_eq]; exact layoutAligned_new _

theorem setupLayout_eqK (S : Shape) : setupLayout S = layoutOfK S .setup := rfl

/-! ## The Keccak tables' flushes -/

open Facts in
theorem good_sha3 : Good flushesSha3 := by
  unfold flushesSha3
  dsimp only
  refine good_foldl _ (fun f x hf ↦ good_foldl _ (fun f' cell hf' ↦ ?_) _ hf) _ ?_
  · split <;> exact hf'.memoryCols (by split_ifs <;> exact formK_prod _ _ _) _ _
  · exact (good_empty.stateStep _ _).bytecode _ _ _ (by simp) (allK_map _ fun _ ↦ formK_col _ 0)

/-- **The Keccak tables' flushes** (`TablesFacts` on `tablesKeccak`). -/
theorem tablesFactsK : ∀ tab ∈ tablesKeccak, tab.flushes.pull.length = tab.flushes.push.length ∧
    ∀ tup ∈ tab.flushes.pull ++ tab.flushes.push, tup.length ≤ 16 ∧
      ∀ f ∈ tup, ∀ mc ∈ f, ofK (toK mc.2) = mc.2 := by
  have key : ∀ tab ∈ tablesKeccak, Facts.Good tab.flushes := by
    intro tab htab
    rw [tablesKeccak_eq] at htab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htab
    rcases htab with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Facts.good_arith _ _
    · exact Facts.good_arith _ _
    · exact Facts.good_set
    · exact Facts.good_deref
    · exact Facts.good_jump
    · exact good_sha3
  intro tab htab
  obtain ⟨hlen, htup⟩ := key tab htab
  exact ⟨hlen, fun tup h ↦ ⟨(htup tup h).1, fun f hf mc hmc ↦ ((htup tup h).2 f hf mc hmc).ofK_toK⟩⟩

end UniKeccakSound.Ids
