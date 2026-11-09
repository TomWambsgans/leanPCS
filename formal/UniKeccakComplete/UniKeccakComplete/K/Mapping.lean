-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Uses `formal/KeccakVm`'s relation (`KvHonest`:
-- `M3Honest` of `keccakIsaInstance` and `KeccakAux`) and `formal/UniSound`'s `LvLink.batchBlock_congr`.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/Mapping.lean`.
import UniKeccakComplete.K.MappingBus

/-!
# The honest prover's placed trace is honest (milestone 4, the mapping)

**`honestTrace_honest`**: for a Keccak deployment `D`, row counts that fit its shape (`RowsFit`) and a stack `q` of
the Keccak VM's layout with `KvHonest` at the Keccak-f block `KeccakFlock.keccakFlockSpec` (`D.HonestRelation`), the
placed trace `honestTrace D input rows q` has every property the algebra needs (`TraceHonest`), each read off one
clause of the Keccak VM's relation:

| `TraceHonest` | from |
|---|---|
| sizes, the setup's fixed slots | `honestTrace`'s construction (`MappingTrace`), `tupleSlotK` |
| `jump` | `ConstraintsVanish` at the executed rows (`jump_constraints`), `PaddingHonest` (`padRow` zero) |
| `counters` | `CountsNonzero` at the executed rows (`countColumns_eq`), `1` at the padding rows |
| `copies` | `KeccakAux`'s copies at the executed rows (`lane_cases`, `q_flock`'s placement `qflock_getD`); the padding rows' lanes are their blocks' port words by construction |
| `publicLines` | `PublicLinesHold` (`publicK` is `publicInputOf`'s word) |
| `bus` | `Balanced` (`bus_perm`: the tuples are the Keccak VM's in `E`, `phi` injective) |
| `flock` | `KeccakAux`'s region (the Keccak-f block's R1CS on `QFLOCK`), block by block: `q_flock`'s block `rowPosition x` is `QFLOCK`'s `x` |

Under `RowsFit` the Keccak VM's height `⌈log₂ rows⌉` is the shape's (`tau_eq`), so the placed rows are its rows.
Two readings are worth keeping: the placed counters differ from the Keccak VM's on the padding rows (`1` against
`padRow`'s `0`), and so do the placed `SHA3` lanes (their blocks' port words against `0`): no clause of the bus
sees either (the PIOP's bus reads the active rows only), and the copies `Q_W` checks need the lanes on every row (a
padding block of `QFLOCK` is a Keccak-f block, whose output port is not zero where its input port is `END_BIT`).

**`badFp_card`**: for every `α` (of any length), at most `(dividedTuples tr).length` challenges `β` are bad
(`BadFp`: each divided fingerprint is `β` plus a constant, so one root each), for any `Fintype E` instance.
**`dividedTuples_length`**: that length is `Σ_t pulls_t · |activeRows t| + 2^lm + 2^lb`; under `RowsFit` it is
`dividedBound` of the shape and the row counts (`Σ_t pulls_t · rows_t + 2^lm + 2^lb`,
`pulls = [5, 5, 3, 5, 5, 28]`, `pulls_eq`), at most `capBound` of the shape (`rows_t ≤ 2^h_t`); the reference
shape's (`keccakRefShape`: `h = 15, 16, 15, 16, 14, 15`, `lm = 20`, `lb = 18`) is `3,227,648 < 2^22`.
-/

namespace UniKeccakComplete.Mapping

open UniComplete

open UniStatement UniKeccak LeanVM.Parameters LeanVM.Protocol
open Lv42.Protocol Lv42.Arithmetization
open Lv42.Protocol.LeanIsa (opIdx Sizes)
open KeccakVm.KeccakIsa (Col kappa memCol bfcntCol flockCol)

variable (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)

/-! ### Rows -/

/-- Every PIOP row of table `t` is `rowPosition x` of a Keccak VM row `x` in the height. -/
theorem exists_rowPosition (hfit : D.shape.RowsFit rows) {t : ℕ} (ht : t < 6) {i : ℕ}
    (hi : i < 2 ^ D.shape.heights.getD t 0) :
    ∃ x < 2 ^ D.shape.heights.getD t 0, rowPosition (rows.getD t 0) (D.shape.heights.getD t 0) x = i := by
  obtain ⟨x, hx, hxi⟩ := (Domain.rowPosition_bijOn (count_le D rows hfit t ht)).surjOn (Set.mem_Iio.mpr hi)
  exact ⟨x, Set.mem_Iio.mp hx, hxi⟩

/-- The Keccak VM's height of table `t` is the shape's. -/
theorem tau_opIdx (hfit : D.shape.RowsFit rows) (t : Fin 6) :
    (D.inst rows).τ (opIdx t) = D.shape.heights.getD t 0 :=
  tau_eq D rows hfit t

/-- **A padding row of the Keccak VM is zero** (`PaddingHonest`, `padRow = 0`). -/
theorem kvTableCell_pad (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) (t : Fin 6) (c : ℕ) {x : ℕ}
    (hx : x < 2 ^ D.shape.heights.getD t 0) (hge : rows.getD t 0 ≤ x) : kvTableCell D rows q t c x = 0 := by
  have hxt : x < 2 ^ (D.inst rows).τ (opIdx t) := by rw [tau_opIdx D rows hfit t]; exact hx
  by_cases hc : c < KeccakVm.KeccakIsa.width (opIdx t)
  · rw [kvTableCell_eq D rows q t hc hxt]
    exact congrFun (hrel.1.2 (opIdx t) ⟨x, hxt⟩ hge) ⟨c, hc⟩
  · show (if h : c < KeccakVm.KeccakIsa.width (opIdx t) then _ else _) = _
    rw [mdif_neg hc]

/-! ### The fields of `TraceHonest` -/

theorem honest_tablesSize : (honestTrace D input rows q).tables.length = 6 ∧
    ∀ t < 6, ((honestTrace D input rows q).tables.getD t []).length = (tablesKeccak.getD t default).width ∧
      ∀ c < (tablesKeccak.getD t default).width,
        ((honestTrace D input rows q).column t c).size = 2 ^ (honestTrace D input rows q).height t := by
  refine ⟨by simp [honestTrace_tables], fun t ht ↦ ⟨?_, fun c hc ↦ ?_⟩⟩
  · rw [tables_getD D input rows q ⟨t, ht⟩, tableCols]
    simp
  · exact column_size D input rows q ⟨t, ht⟩ hc

theorem honest_memorySize : (honestTrace D input rows q).memory.length = 4 ∧
    ∀ k < 4, ((honestTrace D input rows q).memory.getD k #[]).size =
      2 ^ (honestTrace D input rows q).shape.logMemory :=
  ⟨memory_length D input rows q, fun k hk ↦ by rw [memory_getD_arr D input rows q hk]; exact Array.size_ofFn⟩

theorem honest_slotsSize : (honestTrace D input rows q).slots.length = 16 ∧
    ∀ s < 16, ((honestTrace D input rows q).slots.getD s #[]).size =
      2 ^ (honestTrace D input rows q).shape.logBytecode :=
  ⟨slots_length D input rows q, fun s hs ↦ by rw [slots_getD_arr D input rows q hs]; exact Array.size_ofFn⟩

theorem honest_slotsFixed : ∀ i < 2 ^ (honestTrace D input rows q).shape.logBytecode,
    ((honestTrace D input rows q).slots.getD 0 #[]).getD i 0 = K.ofBits 4 ∧
      ((honestTrace D input rows q).slots.getD 1 #[]).getD i 0 = LeanVM.Parameters.gpow i ∧
      ((honestTrace D input rows q).slots.getD 2 #[]).getD i 0 = 0 := by
  intro i hi
  rw [slots_getD D input rows q (by norm_num) hi, slots_getD D input rows q (by norm_num) hi,
    slots_getD D input rows q (by norm_num) hi]
  simp [tupleSlotK]

/-- **`JUMP`'s constraints on every row**: the executed rows' are the Keccak VM's residuals, the padding rows are
zero. -/
theorem honest_jump (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    ∀ i < 2 ^ (honestTrace D input rows q).height opJump,
      let col (n : String) : K := ((honestTrace D input rows q).column opJump (colIdx jumpColumns n)).getD i 0
      col "b" + col "v_cond" * col "w" = 0 ∧ col "v_cond" * (col "b" + 1) = 0 := by
  intro i hi
  show ((honestTrace D input rows q).column 4 13).getD i 0 +
      ((honestTrace D input rows q).column 4 5).getD i 0 * ((honestTrace D input rows q).column 4 12).getD i 0 = 0 ∧
    ((honestTrace D input rows q).column 4 5).getD i 0 * (((honestTrace D input rows q).column 4 13).getD i 0 + 1)
      = 0
  obtain ⟨x, hx, rfl⟩ := exists_rowPosition D rows hfit (by norm_num : 4 < 6) hi
  have hcell : ∀ c, c = 5 ∨ c = 12 ∨ c = 13 →
      ((honestTrace D input rows q).column 4 c).getD
          (rowPosition (rows.getD 4 0) (D.shape.heights.getD 4 0) x) 0 =
        kvTableCell D rows q ⟨4, by norm_num⟩ c x := by
    rintro c (rfl | rfl | rfl) <;>
      exact (congrArg (fun a : Array K ↦ a.getD _ 0)
        (column_eq D input rows q ⟨4, by norm_num⟩ (by decide +kernel))).trans
        (cell_plain D q hfit ⟨4, by norm_num⟩ hx (by decide +kernel) rfl)
  rw [hcell 5 (by simp), hcell 12 (by simp), hcell 13 (by simp)]
  by_cases hxc : x < rows.getD 4 0
  · have hxt : x < 2 ^ (D.inst rows).τ (opIdx ⟨4, by norm_num⟩) := by
      rw [tau_opIdx D rows hfit ⟨4, by norm_num⟩]
      exact hx
    exact jump_constraints ((D.inst rows).row q (opIdx ⟨4, by norm_num⟩) ⟨x, hxt⟩)
      (fun c ↦ kvTableCell D rows q ⟨4, by norm_num⟩ c x)
      (fun i ↦ (kvTableCell_eq D rows q ⟨4, by norm_num⟩ i.isLt hxt).symm)
      (fun C hC ↦ hrel.1.1.1 (opIdx ⟨4, by norm_num⟩) C hC ⟨x, hxt⟩)
  · rw [kvTableCell_pad D input rows q hfit hrel ⟨4, by norm_num⟩ 5 hx (not_lt.mp hxc),
      kvTableCell_pad D input rows q hfit hrel ⟨4, by norm_num⟩ 12 hx (not_lt.mp hxc),
      kvTableCell_pad D input rows q hfit hrel ⟨4, by norm_num⟩ 13 hx (not_lt.mp hxc)]
    simp

/-- A product of nonzero factors is nonzero. -/
theorem foldl_mul_ne_zero (f : ℕ → K) :
    ∀ (l : List ℕ) (acc : K), acc ≠ 0 → (∀ c ∈ l, f c ≠ 0) → l.foldl (fun acc c ↦ acc * f c) acc ≠ 0
  | [], _, h, _ => h
  | c :: l, acc, h, hf => by
    rw [List.foldl_cons]
    exact foldl_mul_ne_zero f l _ (mul_ne_zero h (hf c List.mem_cons_self))
      fun d hd ↦ hf d (List.mem_cons_of_mem _ hd)

/-- **Every counter is nonzero on every row**: the Keccak VM's `CountsNonzero` on the executed rows, `1` on the
padding rows. -/
theorem honest_counters (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    ∀ t < 6, ∀ i < 2 ^ (honestTrace D input rows q).height t,
      (tablesKeccak.getD t default).countColumns.foldl
        (fun acc c ↦ acc * ((honestTrace D input rows q).column t c).getD i 0) 1 ≠ 0 := by
  intro t ht i hi
  obtain ⟨x, hx, rfl⟩ := exists_rowPosition D rows hfit ht hi
  refine foldl_mul_ne_zero _ _ _ one_ne_zero fun c hcm ↦ ?_
  have hcw : c < (tablesKeccak.getD t default).width := by
    have := hcm
    simp only [Table.countColumns, List.mem_filter, List.mem_range] at this
    exact this.1
  rw [column_eq D input rows q ⟨t, ht⟩ hcw]
  by_cases hxc : x < rows.getD t 0
  · rw [cell_active D q hfit ⟨t, ht⟩ hx hxc]
    have hc' : c < KeccakVm.KeccakIsa.width (opIdx ⟨t, ht⟩) := by
      have h := tables_width ⟨t, ht⟩
      have h' : (tablesKeccak.getD t default).width = KeccakVm.KeccakIsa.width (opIdx ⟨t, ht⟩) := h
      omega
    have hxt : x < 2 ^ (D.inst rows).τ (opIdx ⟨t, ht⟩) := by
      rw [tau_opIdx D rows hfit ⟨t, ht⟩]
      exact hx
    rw [kvTableCell_eq D rows q ⟨t, ht⟩ hc' hxt]
    have hcnt : (tablesKeccak.getD t default).countColumns =
        (KeccakVm.KeccakIsa.counts (opIdx ⟨t, ht⟩)).map Fin.val := countColumns_eq ⟨t, ht⟩
    rw [hcnt] at hcm
    obtain ⟨k, hk, hkc⟩ := List.mem_map.mp hcm
    have hkk : k = ⟨c, hc'⟩ := Fin.ext hkc
    subst hkk
    exact hrel.1.1.2.2.1 (opIdx ⟨t, ht⟩) _ hk ⟨x, hxt⟩ hxc
  · rw [cell_counter D q hfit ⟨t, ht⟩ hx hcm hxc]
    exact one_ne_zero

/-- An executed `SHA3` cell is the Keccak VM's `sha3Cell`. -/
theorem kvTableCell_sha3 {c : ℕ} (hc : c < KeccakVm.Sha3Table.width) {x : ℕ} (hx : x < 2 ^ (D.sizes rows).τ 5) :
    kvTableCell D rows q ⟨5, by norm_num⟩ c x = KeccakVm.sha3Cell D.prog (D.sizes rows) q c hc ⟨x, hx⟩ := by
  show (if h : c < KeccakVm.KeccakIsa.width ⟨8, by norm_num⟩ then _ else _) = _
  rw [mdif_pos (show c < KeccakVm.KeccakIsa.width ⟨8, by norm_num⟩ from hc)]
  exact kvCell_eq D rows q _ hx

/-- A `QFLOCK` word is its block's cell. -/
theorem kvCell_flock {w : ℕ} (hw : w < 2 ^ KeccakVm.kWords) {x : ℕ} (hx : x < 2 ^ (D.sizes rows).τ 5) :
    kvCell D rows q flockCol (w + 2048 * x) =
      KeccakVm.kBlockCell (KeccakVm.flockColumn D.prog (D.sizes rows) q) ⟨x, hx⟩ ⟨w, hw⟩ := by
  have hb : w + 2048 * x < 2 ^ kappa D.prog (D.sizes rows) flockCol := by
    show _ < 2 ^ (11 + (D.sizes rows).τ 5)
    have hw' : w < 2048 := hw
    rw [pow_add]
    norm_num
    omega
  rw [kvCell_eq D rows q _ hb]
  rfl

/-- **`SHA3`'s lanes are `q_flock`'s port words**, row by row: the executed rows by `KeccakAux`'s copies, the
padding rows by construction. -/
theorem honest_copies (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    ∀ i < 2 ^ (honestTrace D input rows q).height opSha3, ∀ c < sha3Columns.length, ∀ slot,
      keccakSlot (sha3Columns.getD c "") = some slot →
        ((honestTrace D input rows q).column opSha3 c).getD i 0 =
          (honestTrace D input rows q).qflock.getD (slot + 2048 * i) 0 +
            K.ofLane (keccakSlotOffset (sha3Columns.getD c "")) := by
  intro i hi c hc slot hslot
  have hi' : i < 2 ^ D.shape.heights.getD 5 0 := hi
  obtain ⟨l, hcase⟩ := lane_cases hslot
  have h959 : 9 ≤ c ∧ c < 59 := by rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
  have hc86 : c < 86 := by omega
  have hcw : c < (tablesKeccak.getD 5 default).width := hc
  have hnc : c ∉ (tablesKeccak.getD 5 default).countColumns := lane_not_counter ⟨c, hc86⟩ h959.1 h959.2
  have hls : laneSlot ⟨5, by norm_num⟩ c = some slot := by
    unfold laneSlot
    rw [mif_pos rfl]
    exact hslot
  have hslot_lt : slot < 2048 := by
    rcases hcase with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · exact (KeccakFlock.keccakFlockSpec.inSlot l).isLt
    · exact (KeccakFlock.keccakFlockSpec.outSlot l).isLt
  show ((honestTrace D input rows q).column (⟨5, by norm_num⟩ : Fin 6) c).getD i 0 = _
  rw [column_eq D input rows q ⟨5, by norm_num⟩ hcw, placedCol_lane D rows q ⟨5, by norm_num⟩ hnc hls,
    Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, mdif_pos hi', Option.getD_some, honestTrace_qflock]
  split_ifs with ha
  · obtain ⟨x, hx, rfl⟩ := exists_rowPosition D rows hfit (by norm_num : 5 < 6) hi'
    have hcnt := count_le D rows hfit 5 (by norm_num)
    have hxc : x < rows.getD 5 0 := by
      have := ha
      simp only [Domain.isActive_rowPosition hcnt hx, decide_eq_true_eq] at this
      exact this
    have hxτ : x < 2 ^ (D.sizes rows).τ 5 := by rw [tau_eq D rows hfit 5]; exact hx
    rw [scatter_rowPosition D q hfit ⟨5, by norm_num⟩ hx, qflock_getD D rows q hfit hslot_lt hx,
      kvTableCell_sha3 D rows q (by unfold KeccakVm.Sha3Table.width; omega) hxτ]
    obtain ⟨hin, hout⟩ := hrel.2.2 ⟨x, hxτ⟩ hxc l
    rcases hcase with ⟨rfl, rfl, hoff⟩ | ⟨rfl, rfl, hoff⟩
    · rw [hoff, kvCell_flock D rows q (KeccakFlock.keccakFlockSpec.inSlot l).isLt hxτ]
      refine hin.trans (congrArg _ ?_)
      unfold KeccakVm.laneOffset sha3EndBit
      split_ifs <;> rfl
    · rw [hoff, kvCell_flock D rows q (KeccakFlock.keccakFlockSpec.outSlot l).isLt hxτ, ofLane_zero,
        add_zero]
      exact hout
  · rfl

/-- **The public lines**: the Keccak VM's `PublicLinesHold`, the words `publicInputOf`'s, the verifier's. -/
theorem honest_publicLines (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    let tr := honestTrace D input rows q
    (tr.memory.getD 0 #[]).getD 0 0 = publicK tr 0 ∧ (tr.memory.getD 0 #[]).getD 1 0 = publicK tr 2 ∧
      (tr.memory.getD 1 #[]).getD 0 0 = publicK tr 1 ∧ (tr.memory.getD 1 #[]).getD 1 0 = publicK tr 3 ∧
      (tr.memory.getD 2 #[]).getD 0 0 = 0 ∧ (tr.memory.getD 2 #[]).getD 1 0 = 0 := by
  intro tr
  have h0 : 0 < 2 ^ D.shape.logMemory := Nat.two_pow_pos _
  have h1 : 1 < 2 ^ D.shape.logMemory := Nat.one_lt_two_pow D.logMemory_pos.ne'
  have hl := hrel.1.1.2.2.2.1
  have l0 := hl _ (List.mem_cons_self)
  have l1 := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have l2 := hl _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (memory_cell D input rows q (by norm_num) h0).trans l0.1
  · exact (memory_cell D input rows q (by norm_num) h1).trans l0.2
  · exact (memory_cell D input rows q (by norm_num) h0).trans l1.1
  · exact (memory_cell D input rows q (by norm_num) h1).trans l1.2
  · exact (memory_cell D input rows q (by norm_num) h0).trans l2.1
  · exact (memory_cell D input rows q (by norm_num) h1).trans l2.2

/-- **The Keccak-f block's R1CS holds of `q_flock`**, block by block: block `rowPosition x` is the Keccak VM's
`QFLOCK` block `x`. -/
theorem honest_flock (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    BlockR1CS.BatchHolds KeccakFlock.keccakFlockSpec.r1cs KeccakFlock.keccakFlockSpec.constPos
      (Lv42.Protocol.bitTable (qflockColumn (honestTrace D input rows q))) := by
  intro t
  have hB := tau_eq D rows hfit 5
  obtain ⟨x, hx, hxt⟩ := exists_rowPosition D rows hfit (by norm_num : 5 < 6) t.isLt
  have hxτ : x < 2 ^ (D.sizes rows).τ 5 := by rw [hB]; exact hx
  have hblock : BlockR1CS.batchBlock (Lv42.Protocol.bitTable (qflockColumn (honestTrace D input rows q))) t =
      BlockR1CS.batchBlock (Lv42.Protocol.bitTable (KeccakVm.flockColumn D.prog (D.sizes rows) q)) ⟨x, hxτ⟩ := by
    refine UniSound.Ids.LvLink.batchBlock_congr _ _ _ _ fun jsk jin ↦ ?_
    rw [UniSound.Ids.LvLink.bitTable_get, UniSound.Ids.LvLink.bitTable_get]
    congr 1
    have hq := qflock_getD D rows q hfit jin.isLt hx
    rw [hxt] at hq
    have e1 : (qflockColumn (honestTrace D input rows q)).values.get (cubeIndex jin t) =
        (qflockOf D rows q).getD (jin.val + 2048 * t.val) 0 := by
      simp only [qflockColumn, Vector.get_ofFn, cubeIndex_val, honestTrace_qflock]
      rfl
    have e2 : KeccakVm.kBlockCell (KeccakVm.flockColumn D.prog (D.sizes rows) q) ⟨x, hxτ⟩ jin =
        (KeccakVm.flockColumn D.prog (D.sizes rows) q).values.get (cubeIndex jin ⟨x, hxτ⟩) := rfl
    exact e1.trans (hq.trans ((kvCell_flock D rows q jin.isLt hxτ).trans e2))
  rw [hblock]
  exact hrel.2.1 ⟨x, hxτ⟩

/-! ### The mapping's theorem -/

/-- **The honest prover's placed trace is honest**: from the Keccak VM's `KvHonest` stack (at the Keccak-f block
`keccakFlockSpec`) at row counts that fit the shape, `honestTrace` has every property of `TraceHonest`. -/
theorem honestTrace_honest (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (hfit : D.shape.RowsFit rows) (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) :
    TraceHonest (honestTrace D input rows q) where
  valid := D.valid
  rowsFit := hfit
  tablesSize := honest_tablesSize D input rows q
  memorySize := honest_memorySize D input rows q
  bytecodeSize := by rw [bytecodeFinal_eq]; exact Array.size_ofFn
  qflockSize := qflock_size D input rows q
  slotsSize := honest_slotsSize D input rows q
  slotsFixed := honest_slotsFixed D input rows q
  publicSize := by rw [honestTrace_publicInput]; simp
  jump := honest_jump D input rows q hfit hrel
  counters := honest_counters D input rows q hfit hrel
  copies := honest_copies D input rows q hfit hrel
  publicLines := honest_publicLines D input rows q hrel
  bus := bus_perm D input rows q hfit hrel.1.1.2.1
  flock := honest_flock D input rows q hfit hrel

/-! ### The bad bus challenges -/

/-- A fingerprint is its challenge plus its weighted sum. -/
theorem fpOf_eq (weights : Array E) (beta : E) (tau : List E) : fpOf weights beta tau = beta + fpOf weights 0 tau := by
  simp only [fpOf]
  rw [foldl_add_shift (fun s ↦ weights.getD s 0 * tau.getD s 0), foldl_add_shift (fun s ↦ weights.getD s 0 *
    tau.getD s 0), zero_add]

/-- **At most one bad challenge per divided tuple**: for every `α`, the `β` that make some divided fingerprint
vanish are at most `(dividedTuples tr).length`. -/
theorem badFp_card (tr : Trace) (alphas : List E) [Fintype E] [DecidablePred (BadFp tr alphas)] :
    (Finset.univ.filter (BadFp tr alphas)).card ≤ (dividedTuples tr).length := by
  classical
  refine (Finset.card_le_card (t := ((dividedTuples tr).map fun tau ↦
    -fpOf (eqKernel alphas) 0 tau).toFinset) fun beta hb ↦ ?_).trans ((List.toFinset_card_le _).trans_eq (List.length_map _))
  obtain ⟨tau, htau, h0⟩ := (Finset.mem_filter.mp hb).2
  rw [fpOf_eq] at h0
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨tau, htau, (neg_eq_of_add_eq_zero_left h0)⟩

/-- The pulls of each table: `[5, 5, 3, 5, 5, 28]`. -/
def pulls (t : ℕ) : ℕ := (tablesKeccak.getD t default).flushes.pull.length

theorem pulls_eq : (List.range 6).map pulls = [5, 5, 3, 5, 5, 28] := by decide +kernel

/-- **The number of divided tuples**: each table's pulls over its active rows, the memory's cells, the
bytecode's instructions. -/
theorem dividedTuples_length (tr : Trace) :
    (dividedTuples tr).length =
      ((List.range 6).map fun t ↦ pulls t * (activeRows tr t).length).sum +
        2 ^ tr.shape.logMemory + 2 ^ tr.shape.logBytecode := by
  simp only [dividedTuples, List.length_append, List.length_flatMap, List.length_map, List.length_range,
    List.map_const', List.sum_replicate, smul_eq_mul, pulls]

/-- A table's active rows are its row count, when it fits its height. -/
theorem activeRows_length (tr : Trace) (t : ℕ) (h : tr.rows.getD t 0 ≤ 2 ^ tr.height t) :
    (activeRows tr t).length = tr.rows.getD t 0 := by
  have hnd : ((List.range (tr.rows.getD t 0)).map (rowPosition (tr.rows.getD t 0) (tr.height t))).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy ↦ ?_) List.nodup_range
    exact Domain.rowPosition_injOn h (Set.mem_Iio.mpr (lt_of_lt_of_le (List.mem_range.mp hx) h))
      (Set.mem_Iio.mpr (lt_of_lt_of_le (List.mem_range.mp hy) h)) hxy
  have hp : (activeRows tr t).Perm
      ((List.range (tr.rows.getD t 0)).map (rowPosition (tr.rows.getD t 0) (tr.height t))) := by
    refine (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hnd).mpr fun i ↦ ?_
    show i ∈ (List.range _).filter _ ↔ _
    simp only [List.mem_filter, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨hi, ha⟩
      obtain ⟨x, hx, rfl⟩ := (Domain.rowPosition_bijOn h).surjOn (Set.mem_Iio.mpr hi)
      rw [Domain.isActive_rowPosition h (Set.mem_Iio.mp hx), decide_eq_true_eq] at ha
      exact ⟨x, ha, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Domain.rowPosition_lt h (lt_of_lt_of_le hx h), ?_⟩
      rw [Domain.isActive_rowPosition h (lt_of_lt_of_le hx h), decide_eq_true_eq]
      exact hx
  rw [hp.length_eq, List.length_map, List.length_range]

/-- **The divided tuples' bound from the row counts**: `Σ_t pulls_t · rows_t + 2^lm + 2^lb`. -/
def dividedBound (shape : UniStatement.Shape) (rows : List ℕ) : ℕ :=
  ((List.range 6).map fun t ↦ pulls t * rows.getD t 0).sum + 2 ^ shape.logMemory + 2 ^ shape.logBytecode

/-- The divided tuples' bound of a shape: every table full. -/
def capBound (shape : UniStatement.Shape) : ℕ := dividedBound shape ((List.range 6).map fun t ↦ 2 ^ shape.heights.getD t 0)

/-- **Under `RowsFit`, the divided tuples are `dividedBound`.** -/
theorem dividedTuples_length_eq (tr : Trace) (h : tr.shape.RowsFit tr.rows) :
    (dividedTuples tr).length = dividedBound tr.shape tr.rows := by
  rw [dividedTuples_length, dividedBound]
  congr 3
  refine List.map_congr_left fun t ht ↦ ?_
  rw [activeRows_length tr t (h.2 t (List.mem_range.mp ht)).2]

/-- **`dividedBound` is at most `capBound`**, under `RowsFit`. -/
theorem dividedBound_le (shape : UniStatement.Shape) (rows : List ℕ) (h : shape.RowsFit rows) :
    dividedBound shape rows ≤ capBound shape := by
  unfold capBound dividedBound
  have hs : ((List.range 6).map fun t ↦ pulls t * rows.getD t 0).sum ≤
      ((List.range 6).map fun t ↦
        pulls t * ((List.range 6).map fun t ↦ 2 ^ shape.heights.getD t 0).getD t 0).sum := by
    refine List.sum_le_sum fun t ht ↦ Nat.mul_le_mul_left _ ?_
    have hi := List.mem_range.mp ht
    rw [List.getD_eq_getElem ((List.range 6).map fun t ↦ 2 ^ shape.heights.getD t 0) 0 (by simpa using hi), List.getElem_map, List.getElem_range]
    exact (h.2 t hi).2
  omega

/-- The reference shape's bound: `3,227,648`. -/
theorem capBound_reference : capBound UniKeccakSound.keccakRefShape = 3227648 := by decide +kernel

/-- The reference shape's bound is below `2^22`. -/
theorem capBound_reference_lt : capBound UniKeccakSound.keccakRefShape < 2 ^ 22 := by
  rw [capBound_reference]
  norm_num

/-- **Under `RowsFit`, at most `dividedBound` divided tuples.** -/
theorem dividedTuples_length_le (tr : Trace) (h : tr.shape.RowsFit tr.rows) :
    (dividedTuples tr).length ≤ dividedBound tr.shape tr.rows :=
  (dividedTuples_length_eq tr h).le

/-- **The bad challenges of an honest trace**, at most `capBound` of its shape. -/
theorem badFp_card_honest (tr : Trace) (h : TraceHonest tr) (alphas : List E) [Fintype E]
    [DecidablePred (BadFp tr alphas)] :
    (Finset.univ.filter (BadFp tr alphas)).card ≤ capBound tr.shape :=
  (badFp_card tr alphas).trans
    ((dividedTuples_length_eq tr h.rowsFit).le.trans (dividedBound_le tr.shape tr.rows h.rowsFit))

end UniKeccakComplete.Mapping

/-- info: 'UniKeccakComplete.Mapping.honestTrace_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Mapping.honestTrace_honest

/-- info: 'UniKeccakComplete.Mapping.badFp_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Mapping.badFp_card

/-- info: 'UniKeccakComplete.Mapping.dividedTuples_length_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Mapping.dividedTuples_length_eq

/-- info: 'UniKeccakComplete.Mapping.dividedBound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Mapping.dividedBound_le

/-- info: 'UniKeccakComplete.Mapping.capBound_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Mapping.capBound_reference

/-- info: 'UniKeccakComplete.Mapping.badFp_card_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Mapping.badFp_card_honest

/-- info: 'UniKeccakComplete.Mapping.rowBridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Mapping.rowBridge

/-- info: 'UniKeccakComplete.Mapping.bus_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Mapping.bus_perm

/-- info: 'UniKeccakComplete.Mapping.tau_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Mapping.tau_eq

/-- info: 'UniKeccakComplete.Mapping.capBound_reference_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Mapping.capBound_reference_lt
