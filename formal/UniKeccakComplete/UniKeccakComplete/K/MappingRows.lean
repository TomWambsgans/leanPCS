-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Uses `formal/Lv42` (leanerVM `mumbai` f0393df4,
-- MIT OR Apache-2.0): `JUMP`'s constraints in closed form (`jump_constraints_iff`,
-- `Arithmetization/Completeness/Satisfied.lean`); and `formal/UniKeccakSound`'s reading of the Keccak VM's flushes
-- (`rowTuplesK_eq`), its tables' facts (`tablesFactsK`) and lanes' slots (`laneSlotsK`, `lane_offsets`).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/MappingRows.lean`.
import UniKeccakComplete.K.MappingBasic
import Lv42.Protocol.LeanIsaBase
import Lv42.Arithmetization.Completeness.BasicsBase

/-!
# The six tables' flushes are the Keccak VM's (milestone 4)

`layout.rs`'s tables (`UniStatement.tablesKeccak`: each a list of push and pull tuples of `Form`s) and the Keccak
VM's (`KeccakVm.KeccakIsa.flushes`: Lv42's five opcode tables' Clean polynomials and the `SHA3` table's) flush the
same tuples on every row.

* **`rowBridge`**: at a row of the Keccak VM's opcode table `j` (its cells `R`), the PIOP's tuples of either side
  (`sideForms j side`, the forms at the cells in `E`) are, in order, the Keccak VM's tuples of that side
  (`Heap.rowTuples`), each in `E` (`phi`). `UniKeccakSound`'s `rowTuplesK_eq` reads the Keccak VM's tuples as the
  forms' `K`-tuples (`tupleK`); the forms' coefficients are in `K` (`tablesFactsK`) and their monomials of degree at
  most two (`tables_degree`), so `tupleAt` is `phi ∘ tupleK` (`tupleAt_ofK`).
* **The rest of the correspondence**: `tables_width` (the widths), `countColumns_eq` (the `cnt…` columns are the
  Keccak VM's count columns), `jump_constraints` (the Keccak VM's `JUMP` constraints, Lv42's, at a row are
  `b + v_cond·w`, `v_cond·(b + 1)`, cells `13, 5, 12`), `lane_cases` (a `SHA3` column with a `q_flock` slot is a
  lane, input lane `l` at the Keccak-f block's input port word `inSlot l`, output lane `l` at `outSlot l`), by
  `decide +kernel` on the tables' data where the kernel evaluates it.
-/

namespace UniKeccakComplete.Mapping

open UniComplete

open UniStatement LeanVM.Parameters LeanVM.Protocol
open Lv42.Protocol Lv42.Protocol.LeanIsa Lv42.Arithmetization

/-- **The PIOP's tuples of a side** of table `j`. -/
def sideForms (j : ℕ) : Lv42.Protocol.Side → List (List Form)
  | .push => (tablesKeccak.getD j default).flushes.push
  | .pull => (tablesKeccak.getD j default).flushes.pull

/-! ### The forms are `K`-forms of degree at most two -/

/-- Every monomial of every flush form has degree at most two. -/
theorem tables_degree : ∀ t < 6, ∀ tup ∈ (tablesKeccak.getD t default).flushes.pull ++
    (tablesKeccak.getD t default).flushes.push, ∀ f ∈ tup, ∀ mc ∈ f, mc.1.length ≤ 2 := by
  decide +kernel

theorem sideForms_mem {t : ℕ} {side : Lv42.Protocol.Side} {tup : List Form} (h : tup ∈ sideForms t side) :
    tup ∈ (tablesKeccak.getD t default).flushes.pull ++ (tablesKeccak.getD t default).flushes.push := by
  cases side
  · exact List.mem_append_right _ h
  · exact List.mem_append_left _ h

/-- **The flush forms are `FormOk`**: coefficients in `K`, monomials of degree at most two. -/
theorem sideForms_ok {t : ℕ} (ht : t < 6) (side : Lv42.Protocol.Side) : ∀ tup ∈ sideForms t side, ∀ f ∈ tup, FormOk f := by
  intro tup htup f hf mc hmc
  have hm := sideForms_mem htup
  exact ⟨tables_degree t ht tup hm f hf mc hmc,
    ((UniKeccakSound.Ids.tablesFactsK _ (UniKeccakSound.Ids.tablesKeccak_mem t ht)).2 tup hm).2 f hf mc hmc⟩

/-! ### Every table, every row -/

/-- **The PIOP's tuples of a table at a row are the Keccak VM's**, side by side and in order: on a row `x` of
opcode table `j` whose cells are `R`, the forms of either side at the cells in `E` are the Keccak VM's tuples of
that side, each in `E`. -/
theorem rowBridge (prog : KeccakVm.Program) (s : Sizes)
    (q : LeanVM.Protocol.Column (KeccakVm.keccakIsaInstance prog s).μ) (j : Fin 6) (side : Lv42.Protocol.Side) (x : ℕ)
    (hx : x < 2 ^ (KeccakVm.keccakIsaInstance prog s).τ (opIdx j)) (R : ℕ → K)
    (hrow : (KeccakVm.keccakIsaInstance prog s).row q (opIdx j) ⟨x, hx⟩ = fun i ↦ R i.val) :
    (sideForms j side).map (tupleAt · fun c ↦ ofK (R c)) =
      (Heap.rowTuples (KeccakVm.keccakIsaInstance prog s) q (opIdx j) side x).map phi := by
  have hok := sideForms_ok j.isLt side
  have he : (if side = .push then (tablesKeccak.getD j default).flushes.push
      else (tablesKeccak.getD j default).flushes.pull) = sideForms j side := by
    cases side <;> simp only [sideForms, ↓reduceIte, reduceCtorEq]
  rw [UniKeccakSound.IdsReal.rowTuplesK_eq prog s q j side x hx R hrow, List.map_map, he]
  refine List.map_congr_left fun tup htup ↦ ?_
  rw [Function.comp_apply]
  exact tupleAt_ofK tup R (hok tup htup)

/-! ### Widths, counters, `JUMP`'s constraints, `SHA3`'s lanes -/

/-- The PIOP's widths are the Keccak VM's. -/
theorem tables_width : ∀ t : Fin 6, (tablesKeccak.getD t default).width = KeccakVm.KeccakIsa.width (opIdx t) := by
  decide +kernel

/-- **The PIOP's counter columns are the Keccak VM's count columns** (`Table::count_columns`, the names `cnt…`;
the Keccak VM's the coordinate-`1` variables of the memory and bytecode pulls, and `SHA3`'s `cnt_0 … cnt_bc`). -/
theorem countColumns_eq :
    ∀ t : Fin 6, (tablesKeccak.getD t default).countColumns = (KeccakVm.KeccakIsa.counts (opIdx t)).map Fin.val := by
  decide +kernel

/-- **`JUMP`'s constraints** at a row are its two residuals `b + v_cond · w` (`b` cell `13`, `v_cond` cell `5`,
`w` cell `12`) and `v_cond · (b + 1)`. -/
theorem jump_constraints (r : Fin (KeccakVm.KeccakIsa.width (opIdx 4)) → K) (v : ℕ → K) (hv : ∀ i, r i = v i)
    (h : ∀ C ∈ KeccakVm.KeccakIsa.constraints (opIdx 4), C.eval r = 0) :
    v 13 + v 5 * v 12 = 0 ∧ v 5 * (v 13 + 1) = 0 := by
  obtain rfl : r = fun i : Fin (KeccakVm.KeccakIsa.width (opIdx 4)) ↦ v i.val := funext hv
  have hl := List.isEmpty_iff.mp (base_lookups 4)
  have hc : (⟨jumpTable⟩ : Air.Flat.Component K).operations.ConstraintsHold
      (Environment.fromArray (Array.ofFn fun i : Fin 14 ↦ v i) fun _ _ ↦ #[]) :=
    (toM3_constraints_iff (baseComponent 4) channelSep channelDir counted hl _ (fun _ _ ↦ #[])).mp h
  have hx : Eval.eval (Environment.fromArray (Array.ofFn fun i : Fin 14 ↦ v i) fun _ _ ↦ #[])
      (varFromOffset JumpRow 0 : Var JumpRow K) =
      (⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11⟩ : JumpRow K) := by
    rw [eval_varFromOffset_valueFromOffset]
    simp [valueFromOffset, explicit_provable_type, circuit_norm, Array.getElem?_ofFn]
  have hw : (Environment.fromArray (Array.ofFn fun i : Fin 14 ↦ v i) fun _ _ ↦ #[]).get
      (size JumpRow) = v 12 := by
    show ((Array.ofFn fun i : Fin 14 ↦ v i)[size JumpRow]?).getD 0 = v 12
    rw [show size JumpRow = 12 from rfl]
    simp
  have hb : (Environment.fromArray (Array.ofFn fun i : Fin 14 ↦ v i) fun _ _ ↦ #[]).get
      (size JumpRow + 1) = v 13 := by
    show ((Array.ofFn fun i : Fin 14 ↦ v i)[size JumpRow + 1]?).getD 0 = v 13
    rw [show size JumpRow + 1 = 13 from rfl]
    simp
  rw [Air.Flat.Component.constraintsHold_iff, Air.Flat.Component.rowOperations_mk] at hc
  exact (jump_constraints_iff _ _ (size JumpRow) _ hx _ _ hw hb).mp hc

/-- `SHA3`'s lane columns (`9 ≤ c < 59`) are not counters. -/
theorem lane_not_counter : ∀ c : Fin 86, 9 ≤ c.val → c.val < 59 →
    c.val ∉ (tablesKeccak.getD 5 default).countColumns := by
  decide +kernel

/-- **A `SHA3` column with a `q_flock` slot is a lane**: input lane `l` (column `9 + l`) at the Keccak-f block's
input port word `inSlot l`, its offset `END_BIT` for `l = 16`; output lane `l` (column `34 + l`) at its output port
word `outSlot l`, its offset `0`. -/
theorem lane_cases {c slot : ℕ} (hs : keccakSlot (sha3Columns.getD c "") = some slot) :
    ∃ l : Fin 25,
      (c = 9 + l.val ∧ slot = (KeccakFlock.keccakFlockSpec.inSlot l).val ∧
        keccakSlotOffset (sha3Columns.getD c "") = (if l.val = KeccakVm.endLane then sha3EndBit else 0)) ∨
      (c = 34 + l.val ∧ slot = (KeccakFlock.keccakFlockSpec.outSlot l).val ∧
        keccakSlotOffset (sha3Columns.getD c "") = 0) := by
  have hL := UniKeccakSound.IdsReal.laneSlotsK
  have hF := UniKeccak.keccakFlockFits_keccakFlockSpec
  obtain ⟨hc, -⟩ := UniKeccakSound.Ids.keccakSlot_lt hL hs
  have h9 : 9 ≤ c := by
    by_contra h
    rw [UniKeccakSound.Ids.keccakSlot_other ⟨c, hc⟩ (Or.inl (by simp only; omega))] at hs
    cases hs
  have h59 : c < 59 := by
    by_contra h
    rw [UniKeccakSound.Ids.keccakSlot_other ⟨c, hc⟩ (Or.inr (by simp only; omega))] at hs
    cases hs
  by_cases h34 : c < 34
  · let l : Fin 25 := ⟨c - 9, by omega⟩
    have hcl : c = 9 + l.val := by simp only [l]; omega
    refine ⟨l, Or.inl ⟨hcl, ?_, ?_⟩⟩
    · have := (hL l).1
      rw [← hcl, hs, Option.some.injEq] at this
      rw [this, hF.1 l]
    · rw [hcl]
      exact (UniKeccakSound.Ids.lane_offsets l).1
  · let l : Fin 25 := ⟨c - 34, by omega⟩
    have hcl : c = 34 + l.val := by simp only [l]; omega
    refine ⟨l, Or.inr ⟨hcl, ?_, ?_⟩⟩
    · have := (hL l).2
      rw [← hcl, hs, Option.some.injEq] at this
      rw [this, hF.2.1 l]
    · rw [hcl]
      exact (UniKeccakSound.Ids.lane_offsets l).2

/-- `SHA3_COLUMNS` has 86 columns. -/
theorem sha3Columns_length : sha3Columns.length = 86 := by decide

/-- `K.ofLane 0` is `0`. -/
theorem ofLane_zero : K.ofLane 0 = 0 := by decide +kernel

end UniKeccakComplete.Mapping
