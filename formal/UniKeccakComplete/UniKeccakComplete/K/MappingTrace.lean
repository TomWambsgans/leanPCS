-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/MappingTrace.lean`.
import UniKeccakComplete.K.MappingRows

/-!
# The placed trace's cells (milestone 4)

What `honestTrace D input rows q` holds, cell by cell, under `RowsFit`:

* **The heights** (`tau_eq`): the Keccak VM's `τ_t = ⌈log₂ rows_t⌉` is the shape's `h_t` (`leastRows h ≤ rows ≤
  2^h`: `2^(h−1) < rows ≤ 2^h`, or `h = 0` and `rows ≤ 1`).
* **Scattering** (`foldl_set_getD`, `scatter_getD`): writing value `x` at `f x` for every `x` of a duplicate-free
  list, `f` injective on it, leaves `value x` at `f x`; so `scatter r (rowPosition count r) value` holds
  the Keccak VM's row `x` at `rowPosition count r x`.
* **The cells** (`column_eq`, `cell_active`, `cell_counter`, `cell_plain`, `placedCol_lane`, `memory_getD`,
  `bytecodeFinal_getD`, `slots_getD`, `qflock_getD`): a table's column `c` at the PIOP's row `rowPosition x` is the
  Keccak VM's cell `x` of column `⟨t + 3, c⟩` (`kvTableCell`) at an executed row (`x < count`); at a padding row
  it is `1` on a counter column, its block's port word (plus `END_BIT` for `in_16`) on a `SHA3` lane, the Keccak
  VM's (padding) cell otherwise; the memory's, the bytecode's final counts', the setup slots' are the Keccak VM's
  and the program's, and `q_flock`'s word `j + 2048 · rowPosition x` is the Keccak VM's `QFLOCK` word
  `j + 2048 x`.
-/

namespace UniKeccakComplete.Mapping

open UniComplete

open UniStatement UniKeccak LeanVM.Parameters LeanVM.Protocol
open Lv42.Protocol Lv42.Arithmetization
open Lv42.Protocol.LeanIsa (opIdx Sizes)
open KeccakVm.KeccakIsa (Col kappa memCol bfcntCol flockCol)

/-- `dif_pos`, which this Mathlib deprecates. -/
theorem mdif_pos {α : Sort*} {c : Prop} [Decidable c] {t : c → α} {e : ¬ c → α} (h : c) :
    dite c t e = t h := by
  simp [h]

/-- `if_pos`, which this Mathlib deprecates. -/
theorem mif_pos {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

/-- `if_neg`, which this Mathlib deprecates. -/
theorem mif_neg {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

/-- `dif_neg`, which this Mathlib deprecates. -/
theorem mdif_neg {α : Sort*} {c : Prop} [Decidable c] {t : c → α} {e : ¬ c → α} (h : ¬ c) :
    dite c t e = e h := by
  simp [h]

/-! ### The heights -/

/-- **The Keccak VM's height is the shape's**, under `RowsFit`. -/
theorem tau_eq (D : KDeployment) (rows : List ℕ) (hfit : D.shape.RowsFit rows) (t : Fin 6) :
    (D.sizes rows).τ t = D.shape.heights.getD t 0 := by
  obtain ⟨-, hfit⟩ := hfit
  obtain ⟨hlo, hhi⟩ := hfit t t.isLt
  have hcap : D.shape.capacityRows.getD t 0 = Shape.leastRows (D.shape.heights.getD t 0) :=
    List.getD_map D.shape.heights 0 Shape.leastRows
  rw [hcap] at hlo
  show Nat.clog 2 (rows.getD t 0) = _
  set h := D.shape.heights.getD t 0
  apply le_antisymm (Nat.clog_le_of_le_pow hhi)
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · have hl : Shape.leastRows h = 2 ^ (h - 1) + 1 := by simp [Shape.leastRows, hpos.ne']
    rw [hl] at hlo
    have := (Nat.lt_clog_iff_pow_lt (b := 2) (by norm_num) (x := rows.getD t 0) (y := h - 1)).mpr
      (by omega)
    omega

/-- A table's rows fit its height. -/
theorem count_le (D : KDeployment) (rows : List ℕ) (hfit : D.shape.RowsFit rows) (t : ℕ) (ht : t < 6) :
    rows.getD t 0 ≤ 2 ^ D.shape.heights.getD t 0 :=
  (hfit.2 t ht).2

/-! ### Scattering -/

theorem foldl_set_size {α : Type} (f : ℕ → ℕ) (val : ℕ → α) :
    ∀ (L : List ℕ) (a : Array α), (L.foldl (fun a y ↦ a.set! (f y) (val y)) a).size = a.size
  | [], _ => rfl
  | y :: L, a => by
    rw [List.foldl_cons, foldl_set_size f val L, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem foldl_set_getD_of_ne {α : Type} (f : ℕ → ℕ) (val : ℕ → α) (p : ℕ) (d : α) :
    ∀ (L : List ℕ) (a : Array α), (∀ y ∈ L, f y ≠ p) →
      (L.foldl (fun a y ↦ a.set! (f y) (val y)) a).getD p d = a.getD p d
  | [], _, _ => rfl
  | y :: L, a, h => by
    rw [List.foldl_cons, foldl_set_getD_of_ne f val p d L _ fun z hz ↦ h z (List.mem_cons_of_mem _ hz),
      Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds, ite_eq_right_of_eq_false _ _ (eq_false (h y List.mem_cons_self))]

/-- **Writing `val x` at `f x` for every `x` of a list** leaves `val x` at `f x`, `f` injective on the list. -/
theorem foldl_set_getD {α : Type} (f : ℕ → ℕ) (val : ℕ → α) (d : α) :
    ∀ (L : List ℕ) (a : Array α), L.Nodup → ∀ x ∈ L, (∀ y ∈ L, f y = f x → y = x) → f x < a.size →
      (L.foldl (fun a y ↦ a.set! (f y) (val y)) a).getD (f x) d = val x
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | y :: L, a, hnd, x, hx, hinj, hs => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hxL
    · rw [foldl_set_getD_of_ne f val _ d L _ fun z hz hzx ↦ (List.nodup_cons.mp hnd).1
          (hinj z (List.mem_cons_of_mem _ hz) hzx ▸ hz),
        Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
        ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true hs)]
      rfl
    · exact foldl_set_getD f val d L _ (List.nodup_cons.mp hnd).2 x hxL
        (fun z hz ↦ hinj z (List.mem_cons_of_mem _ hz))
        (by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hs)

theorem scatter_size (r : ℕ) (pos : ℕ → ℕ) (value : ℕ → K) : (scatter r pos value).size = 2 ^ r := by
  rw [scatter, foldl_set_size, Array.size_replicate]

/-- **A scattered column holds value `x` at `pos x`**, `pos` a bijection of `[0, 2^r)`. -/
theorem scatter_getD (r : ℕ) (pos : ℕ → ℕ) (value : ℕ → K) (hinj : Set.InjOn pos (Set.Iio (2 ^ r)))
    (hlt : ∀ x < 2 ^ r, pos x < 2 ^ r) {x : ℕ} (hx : x < 2 ^ r) :
    (scatter r pos value).getD (pos x) 0 = value x :=
  foldl_set_getD pos value 0 _ _ List.nodup_range x (List.mem_range.mpr hx)
    (fun y hy h ↦ hinj (Set.mem_Iio.mpr (List.mem_range.mp hy)) (Set.mem_Iio.mpr hx) h)
    (by rw [Array.size_replicate]; exact hlt x hx)

/-! ### The cells of the placed trace -/

variable (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)

/-- `q_flock` of the placed trace (`honestTrace`'s `qflock`). -/
def qflockOf : Array K :=
  (List.range (2 ^ (D.shape.heights.getD 5 0 + 11))).foldl (fun a word ↦
      a.set! (word % 2048 + 2048 * rowPosition (rows.getD 5 0) (D.shape.heights.getD 5 0) (word / 2048))
        (kvCell D rows q flockCol word)) (Array.replicate (2 ^ (D.shape.heights.getD 5 0 + 11)) 0)

/-- The `q_flock` slot of column `i` of table `t`: a `SHA3` lane's (`keccakSlot`), none otherwise. -/
def laneSlot (t : Fin 6) (i : ℕ) : Option ℕ :=
  if t.val = 5 then keccakSlot ((tablesKeccak.getD t.val default).columns.getD i "") else none

/-- Column `i` of table `t` in the placed trace (`honestTrace`'s `table`). -/
def placedCol (t : Fin 6) (i : ℕ) : Array K :=
  let r := D.shape.heights.getD t.val 0
  let count := rows.getD t.val 0
  let counters := (tablesKeccak.getD t.val default).countColumns
  let placed := scatter r (rowPosition count r) (kvTableCell D rows q t i)
  let name := (tablesKeccak.getD t.val default).columns.getD i ""
  if i ∈ counters then
    Array.ofFn (n := 2 ^ r) fun p ↦ if isActive p.val count r then placed.getD p.val 0 else 1
  else match (if t.val = 5 then keccakSlot name else none) with
    | some slot => Array.ofFn (n := 2 ^ r) fun p ↦ if isActive p.val count r then placed.getD p.val 0
        else (qflockOf D rows q).getD (slot + 2048 * p.val) 0 + K.ofLane (keccakSlotOffset name)
    | none => placed

/-- Table `t`'s columns in the placed trace. -/
def tableCols (t : Fin 6) : List (Array K) :=
  (List.range (tablesKeccak.getD t.val default).width).map (placedCol D rows q t)

theorem honestTrace_tables : (honestTrace D input rows q).tables = (List.finRange 6).map (tableCols D rows q) :=
  rfl

theorem honestTrace_qflock : (honestTrace D input rows q).qflock = qflockOf D rows q := rfl

theorem honestTrace_shape : (honestTrace D input rows q).shape = D.shape := rfl

theorem honestTrace_rows : (honestTrace D input rows q).rows = rows := rfl

theorem honestTrace_publicInput : (honestTrace D input rows q).publicInput = input.toList := rfl

theorem honestTrace_height (t : ℕ) : (honestTrace D input rows q).height t = D.shape.heights.getD t 0 := rfl

theorem tables_getD (t : Fin 6) :
    (honestTrace D input rows q).tables.getD t [] = tableCols D rows q t := by
  rw [honestTrace_tables, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
  rfl

/-- Column `c` of table `t` (`c` below the width). -/
theorem column_eq (t : Fin 6) {c : ℕ} (hc : c < (tablesKeccak.getD t default).width) :
    (honestTrace D input rows q).column t c = placedCol D rows q t c := by
  rw [Trace.column, tables_getD, tableCols, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map,
    List.getElem_range]

/-- A counter column. -/
theorem placedCol_counter (t : Fin 6) {c : ℕ} (hc : c ∈ (tablesKeccak.getD t default).countColumns) :
    placedCol D rows q t c = Array.ofFn (n := 2 ^ D.shape.heights.getD t 0) fun p ↦
      if isActive p.val (rows.getD t 0) (D.shape.heights.getD t 0) then
        (scatter (D.shape.heights.getD t 0) (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0))
          (kvTableCell D rows q t c)).getD p.val 0
      else 1 := by
  simp only [placedCol, mif_pos hc]

/-- A `SHA3` lane: its block's port word (plus its offset) on a padding row. -/
theorem placedCol_lane (t : Fin 6) {c slot : ℕ} (hc : c ∉ (tablesKeccak.getD t default).countColumns)
    (hs : laneSlot t c = some slot) :
    placedCol D rows q t c = Array.ofFn (n := 2 ^ D.shape.heights.getD t 0) fun p ↦
      if isActive p.val (rows.getD t 0) (D.shape.heights.getD t 0) then
        (scatter (D.shape.heights.getD t 0) (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0))
          (kvTableCell D rows q t c)).getD p.val 0
      else (qflockOf D rows q).getD (slot + 2048 * p.val) 0 +
        K.ofLane (keccakSlotOffset ((tablesKeccak.getD t default).columns.getD c "")) := by
  unfold laneSlot at hs
  simp only [placedCol, mif_neg hc]
  split
  · next slot' heq =>
    rw [hs] at heq
    cases heq
    rfl
  · next heq =>
    rw [hs] at heq
    cases heq

/-- Any other column: the scattered cells. -/
theorem placedCol_plain (t : Fin 6) {c : ℕ} (hc : c ∉ (tablesKeccak.getD t default).countColumns)
    (hs : laneSlot t c = none) :
    placedCol D rows q t c = scatter (D.shape.heights.getD t 0)
      (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0)) (kvTableCell D rows q t c) := by
  unfold laneSlot at hs
  simp only [placedCol, mif_neg hc]
  split
  · next slot' heq =>
    rw [hs] at heq
    cases heq
  · rfl

theorem placedCol_size (t : Fin 6) (c : ℕ) :
    (placedCol D rows q t c).size = 2 ^ D.shape.heights.getD t 0 := by
  by_cases hc : c ∈ (tablesKeccak.getD t default).countColumns
  · rw [placedCol_counter D rows q t hc, Array.size_ofFn]
  · cases hs : laneSlot t c with
    | some slot => rw [placedCol_lane D rows q t hc hs, Array.size_ofFn]
    | none => rw [placedCol_plain D rows q t hc hs, scatter_size]

theorem column_size (t : Fin 6) {c : ℕ} (hc : c < (tablesKeccak.getD t default).width) :
    ((honestTrace D input rows q).column t c).size = 2 ^ D.shape.heights.getD t 0 := by
  rw [column_eq D input rows q t hc, placedCol_size]

/-- A column past its table's width is empty. -/
theorem column_of_ge (t : Fin 6) {c : ℕ} (hc : (tablesKeccak.getD t default).width ≤ c) :
    (honestTrace D input rows q).column t c = #[] := by
  rw [Trace.column, tables_getD, tableCols, List.getD_eq_default _ _ (by simpa using hc)]

section Cells

variable {rows} (hfit : D.shape.RowsFit rows) (t : Fin 6) {c : ℕ} {x : ℕ}
  (hx : x < 2 ^ D.shape.heights.getD t 0)
include hfit hx

/-- The scattered cells at `rowPosition x`. -/
theorem scatter_rowPosition :
    (scatter (D.shape.heights.getD t 0) (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0))
      (kvTableCell D rows q t c)).getD (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0) x) 0 =
      kvTableCell D rows q t c x := by
  have hcnt := count_le D rows hfit t t.isLt
  exact scatter_getD (D.shape.heights.getD t 0) (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0))
    (kvTableCell D rows q t c) (Domain.rowPosition_injOn hcnt) (fun y hy ↦ Domain.rowPosition_lt hcnt hy) hx

/-- **An executed row's placed cell** is the Keccak VM's. -/
theorem cell_active (hxc : x < rows.getD t 0) :
    (placedCol D rows q t c).getD (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0) x) 0 =
      kvTableCell D rows q t c x := by
  have hcnt := count_le D rows hfit t t.isLt
  have hlt := Domain.rowPosition_lt hcnt hx
  by_cases hc : c ∈ (tablesKeccak.getD t default).countColumns
  · rw [placedCol_counter D rows q t hc, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, mdif_pos hlt,
      Option.getD_some, Domain.isActive_rowPosition hcnt hx]
    simp only [decide_eq_true_eq, hxc, ite_true]
    exact scatter_rowPosition D q hfit t hx
  · cases hs : laneSlot t c with
    | some slot =>
      rw [placedCol_lane D rows q t hc hs, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, mdif_pos hlt,
        Option.getD_some, Domain.isActive_rowPosition hcnt hx]
      simp only [decide_eq_true_eq, hxc, ite_true]
      exact scatter_rowPosition D q hfit t hx
    | none => rw [placedCol_plain D rows q t hc hs, scatter_rowPosition D q hfit t hx]

/-- A counter at a padding row is `1`. -/
theorem cell_counter (hc : c ∈ (tablesKeccak.getD t default).countColumns) (hxc : ¬ x < rows.getD t 0) :
    (placedCol D rows q t c).getD (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0) x) 0 = 1 := by
  have hcnt := count_le D rows hfit t t.isLt
  rw [placedCol_counter D rows q t hc, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    mdif_pos (Domain.rowPosition_lt hcnt hx), Option.getD_some, Domain.isActive_rowPosition hcnt hx]
  simp only [decide_eq_true_eq, hxc, ite_false]

/-- A column neither a counter nor a lane: the Keccak VM's cell on every row. -/
theorem cell_plain (hc : c ∉ (tablesKeccak.getD t default).countColumns) (hs : laneSlot t c = none) :
    (placedCol D rows q t c).getD (rowPosition (rows.getD t 0) (D.shape.heights.getD t 0) x) 0 =
      kvTableCell D rows q t c x := by
  rw [placedCol_plain D rows q t hc hs, scatter_rowPosition D q hfit t hx]

end Cells

/-- `kvCell` is the Keccak VM's column. -/
theorem kvCell_eq (c : Col) {x : ℕ} (hx : x < 2 ^ kappa D.prog (D.sizes rows) c) :
    kvCell D rows q c x = ((D.inst rows).column q c).values.get ⟨x, hx⟩ := by
  rw [kvCell, mdif_pos hx]

/-- `kvTableCell` is the Keccak VM's row. -/
theorem kvTableCell_eq (t : Fin 6) {c : ℕ} (hc : c < KeccakVm.KeccakIsa.width (opIdx t)) {x : ℕ}
    (hx : x < 2 ^ (D.inst rows).τ (opIdx t)) :
    kvTableCell D rows q t c x = (D.inst rows).row q (opIdx t) ⟨x, hx⟩ ⟨c, hc⟩ := by
  show (if h : c < KeccakVm.KeccakIsa.width (opIdx t) then _ else _) = _
  rw [mdif_pos hc]
  exact kvCell_eq D rows q ⟨opIdx t, ⟨c, hc⟩⟩ hx

/-! ### The memory, the bytecode, the slots, `q_flock` -/

theorem memory_length : (honestTrace D input rows q).memory.length = 4 := by
  simp [honestTrace]

theorem memory_getD_arr {k : ℕ} (hk : k < 4) :
    (honestTrace D input rows q).memory.getD k #[] =
      Array.ofFn (n := 2 ^ D.shape.logMemory) fun x ↦ kvCell D rows q (memCol ⟨k, hk⟩) x.val := by
  simp only [honestTrace]
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]
  congr 1
  funext x
  rw [mdif_pos hk]

theorem memory_getD {k : ℕ} (hk : k < 4) {x : ℕ} (hx : x < 2 ^ D.shape.logMemory) :
    ((honestTrace D input rows q).memory.getD k #[]).getD x 0 = kvCell D rows q (memCol ⟨k, hk⟩) x := by
  rw [memory_getD_arr D input rows q hk, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, mdif_pos hx,
    Option.getD_some]

theorem bytecodeFinal_eq : (honestTrace D input rows q).bytecodeFinal =
    Array.ofFn (n := 2 ^ D.shape.logBytecode) fun x ↦ kvCell D rows q bfcntCol x.val := rfl

theorem bytecodeFinal_getD {x : ℕ} (hx : x < 2 ^ D.shape.logBytecode) :
    (honestTrace D input rows q).bytecodeFinal.getD x 0 = kvCell D rows q bfcntCol x := by
  rw [bytecodeFinal_eq, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, mdif_pos hx, Option.getD_some]

theorem slots_length : (honestTrace D input rows q).slots.length = 16 := by
  simp [honestTrace]

theorem slots_getD_arr {s : ℕ} (hs : s < 16) :
    (honestTrace D input rows q).slots.getD s #[] =
      Array.ofFn (n := 2 ^ D.shape.logBytecode) fun i ↦
        if h : i.val < 2 ^ D.prog.logSize then tupleSlotK D.prog ⟨i.val, h⟩ s else 0 := by
  simp only [honestTrace]
  rw [List.getD_eq_getElem _ _ (by simpa using hs), List.getElem_map, List.getElem_range]

theorem slots_getD {s : ℕ} (hs : s < 16) {i : ℕ} (hi : i < 2 ^ D.shape.logBytecode) :
    ((honestTrace D input rows q).slots.getD s #[]).getD i 0 =
      tupleSlotK D.prog ⟨i, by rw [← D.logBytecode_eq]; exact hi⟩ s := by
  rw [slots_getD_arr D input rows q hs, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, mdif_pos hi,
    Option.getD_some, mdif_pos (by rw [← D.logBytecode_eq]; exact hi)]

theorem qflock_size : (honestTrace D input rows q).qflock.size = 2 ^ (D.shape.heights.getD 5 0 + 11) := by
  rw [honestTrace_qflock, qflockOf, foldl_set_size, Array.size_replicate]

/-- **`q_flock`'s blocks are the Keccak VM's, moved by `rowPosition`**: word `j + 2048 · rowPosition x` is the
Keccak VM's `QFLOCK` word `j + 2048 x`. -/
theorem qflock_getD (hfit : D.shape.RowsFit rows) {j : ℕ} (hj : j < 2048) {x : ℕ}
    (hx : x < 2 ^ D.shape.heights.getD 5 0) :
    (qflockOf D rows q).getD (j + 2048 * rowPosition (rows.getD 5 0) (D.shape.heights.getD 5 0) x) 0 =
      kvCell D rows q flockCol (j + 2048 * x) := by
  have hcnt := count_le D rows hfit 5 (by norm_num)
  set hB := D.shape.heights.getD 5 0
  set f : ℕ → ℕ := fun word ↦ word % 2048 + 2048 * rowPosition (rows.getD 5 0) hB (word / 2048)
  have hpow : 2 ^ (hB + 11) = 2048 * 2 ^ hB := by rw [pow_add]; norm_num; ring
  have hw : j + 2048 * x < 2 ^ (hB + 11) := by rw [hpow]; omega
  have hfw : f (j + 2048 * x) = j + 2048 * rowPosition (rows.getD 5 0) hB x := by
    simp only [f]
    congr 2
    · omega
    · congr 1
      omega
  rw [← hfw, qflockOf]
  refine foldl_set_getD f _ 0 _ _ List.nodup_range _ (List.mem_range.mpr hw) (fun y hy hfy ↦ ?_) ?_
  · have hy' := List.mem_range.mp hy
    have hyq : y / 2048 < 2 ^ hB := by rw [hpow] at hy'; omega
    have hwq : (j + 2048 * x) / 2048 < 2 ^ hB := by omega
    simp only [f] at hfy
    have hmod : y % 2048 = (j + 2048 * x) % 2048 := by omega
    have hpos : rowPosition (rows.getD 5 0) hB (y / 2048) =
        rowPosition (rows.getD 5 0) hB ((j + 2048 * x) / 2048) := by omega
    have hdiv := Domain.rowPosition_injOn hcnt (Set.mem_Iio.mpr hyq) (Set.mem_Iio.mpr hwq) hpos
    omega
  · rw [Array.size_replicate, hfw, hpow]
    have := Domain.rowPosition_lt hcnt hx
    omega

end UniKeccakComplete.Mapping
