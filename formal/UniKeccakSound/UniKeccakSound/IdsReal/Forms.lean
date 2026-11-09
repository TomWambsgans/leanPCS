-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The reflection is `UniSound/Ids/LvRealize.lean`'s
-- (`SP`, `spNorm`, `exprSP`, `formSP`, `sides_eq`), for the Keccak VM's `SHA3` table (`formal/KeccakVm`'s
-- `Sha3Table.flushExprs`, `formal/UniStatement`'s `flushesSha3`).
import UniSound.Ids.LvRealize
import UniKeccakSound.Ids.Model

/-!
# The verifier's table forms are the Keccak VM's flushes

**`rowTuplesK_eq`**: on every row `R : ℕ → K`, table `j`'s tuples of the verifier's Keccak tables (`tablesKeccak`,
`tupleK` of its push or pull forms) are, **in order**, the Keccak VM's flushes of opcode table `j` of that side
(`KeccakVm.keccakIsaInstance`'s `flushes (opIdx j)`) evaluated at the row.

* The five tables other than `SHA3` are Lv42's on both sides (`tablesKeccak` is `sharedTables` there; the instance's
  flushes are Lv42's `baseTable`'s): `UniSound.Ids.LvR.uni_tuples_eq_base`.
* **The `SHA3` table** (`sha3_flushes_eq`): the verifier's `flushesSha3` against `KeccakVm.Sha3Table.flushes`, by
  reflection as `LvR.sides_eq`: both sides read as polynomials in `LvR`'s normal form (the forms by `formSP`, the
  instance's Clean expressions `Sha3Table.flushExprs` by `exprSP`), the two lists of normal forms equal by
  `decide +kernel` (`sha3_sides_eq`), the normal form keeping the value.
-/

namespace UniKeccakSound.IdsReal

open LeanVM.Parameters UniStatement UniSound.Ids UniSound.Ids.LvR Lv42.Protocol
open Lv42.Protocol.LeanIsa (opIdx)

/-! ## The `SHA3` table -/

/-- A side named by a Boolean (`true` the push side). -/
def sideOfBool (push : Bool) : Side := if push then .push else .pull

theorem sideOfBool_decide (side : Side) : sideOfBool (decide (side = .push)) = side := by
  cases side <;> rfl

/-- The verifier's `SHA3` forms of one side, as normal forms. -/
def uniSha3Side (push : Bool) : List (List SP) :=
  ((if push then flushesSha3.push else flushesSha3.pull).map tupSP).map (·.map spNorm)

/-- A Keccak VM `SHA3` flush's sixteen coordinates as polynomials (zeros past its end). -/
def exprsSP (l : List (Expression K)) : List SP :=
  (List.range 16).map fun j ↦ exprSP KeccakVm.Sha3Table.width (l.getD j (KeccakVm.Sha3Table.k 0))

/-- The Keccak VM's `SHA3` flushes of one side, as normal forms. -/
def kvSha3Side (push : Bool) : List (List SP) :=
  ((KeccakVm.Sha3Table.flushExprs.filter fun f ↦ decide (f.1 = sideOfBool push)).map
    fun f ↦ exprsSP f.2).map (·.map spNorm)

set_option maxRecDepth 100000 in
/-- **The normal forms are equal**, side by side, in order. -/
theorem sha3_sides_eq : ∀ push : Bool, uniSha3Side push = kvSha3Side push := by
  decide +kernel

/-- A `SHA3` flush's polynomials evaluate to its polynomials' values. -/
theorem tuple_eval (l : List (Expression K)) (R : ℕ → K) :
    (KeccakVm.Sha3Table.tuple l).map (·.eval fun i : Fin KeccakVm.Sha3Table.width ↦ R i.val) =
      tupleOfSP R ((exprsSP l).map spNorm) := by
  apply Vector.ext
  intro n hn
  simp only [KeccakVm.Sha3Table.tuple, Vector.getElem_map, Vector.getElem_ofFn, tupleOfSP, exprsSP]
  rw [getD_map_range _ n hn, spEval_spNorm, Expression.eval_toCMvPolynomial _ noData, eval_exprSP]

/-- The `SHA3` flushes of a side, on a row, as normal forms' values. -/
theorem sha3_flushes_sp (side : Side) (R : ℕ → K) :
    ((KeccakVm.Sha3Table.flushes.filter fun f ↦ decide (f.1 = side)).map fun f ↦
        f.2.map (·.eval fun i : Fin KeccakVm.Sha3Table.width ↦ R i.val)) =
      (kvSha3Side (decide (side = .push))).map (tupleOfSP R) := by
  unfold KeccakVm.Sha3Table.flushes kvSha3Side
  rw [List.filter_map, List.map_map, List.map_map, List.map_map, sideOfBool_decide]
  exact List.map_congr_left fun f _ ↦ tuple_eval f.2 R

/-- **The Keccak VM's `SHA3` flushes are the verifier's forms**: on every row, side by side, in order. -/
theorem sha3_flushes_eq (side : Side) (R : ℕ → K) :
    ((KeccakVm.Sha3Table.flushes.filter fun f ↦ decide (f.1 = side)).map fun f ↦
        f.2.map (·.eval fun i : Fin KeccakVm.Sha3Table.width ↦ R i.val)) =
      (if side = .push then flushesSha3.push else flushesSha3.pull).map fun tup ↦ tupleK tup R := by
  rw [sha3_flushes_sp, ← sha3_sides_eq]
  simp only [uniSha3Side, List.map_map, tupleK_eq]
  cases side <;> rfl

/-! ## The six tables -/

/-- `tablesKeccak` is `sharedTables` but for `SHA3`. -/
theorem tablesKeccak_getD_of_ne {j : ℕ} (hj : j ≠ opSha3) :
    tablesKeccak.getD j default = sharedTables.getD j default := by
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => rfl
  | 5, h => exact absurd rfl h
  | n + 6, _ => simp [tablesKeccak, sharedTables, List.getD_eq_getElem?_getD]

theorem tablesKeccak_getD_sha3 : (tablesKeccak.getD opSha3 default).flushes = flushesSha3 := rfl

/-- The Keccak VM's flushes of the five tables other than `SHA3` (the shared tables `baseTable j`), of a side, on a
row, are their interactions'. -/
theorem kv_flushes_lv (j : Fin 5) (side : Side) (R : ℕ → K) :
    ((KeccakVm.KeccakIsa.flushes (opIdx j.castSucc)).filter fun f ↦ decide (f.1 = side)).map
        (fun f ↦ f.2.map (·.eval fun i ↦ R i.val)) =
      (lvInteractionsBase j (decide (side = .push))).map fun ai ↦
        (LeanVM.Protocol.flushPolys Lv42.Arithmetization.channelSep (LeanIsa.baseComponent j).width ai).map
          (·.eval fun i : Fin (LeanIsa.baseComponent j).width ↦ R i.val) := by
  fin_cases j
  · exact base_flushes_eq 0 side _
  · exact base_flushes_eq 1 side _
  · exact base_flushes_eq 2 side _
  · exact base_flushes_eq 3 side _
  · exact base_flushes_eq 4 side _

/-- **A row's flushes are its forms' tuples**: where the Keccak VM's row `x` of opcode table `j` is the row `R`,
its tuples of a side are the verifier's forms' (`tablesKeccak`) of that side at `R`, in order. -/
theorem rowTuplesK_eq (prog : KeccakVm.Program) (s : LeanIsa.Sizes)
    (q : LeanVM.Protocol.Column (KeccakVm.keccakIsaInstance prog s).μ) (j : Fin 6) (side : Side) (x : ℕ)
    (hx : x < 2 ^ (KeccakVm.keccakIsaInstance prog s).τ (opIdx j)) (R : ℕ → K)
    (hrow : (KeccakVm.keccakIsaInstance prog s).row q (opIdx j) ⟨x, hx⟩ = fun i ↦ R i.val) :
    Heap.rowTuples (KeccakVm.keccakIsaInstance prog s) q (opIdx j) side x =
      (if side = .push then (tablesKeccak.getD j default).flushes.push
        else (tablesKeccak.getD j default).flushes.pull).map fun tup ↦ tupleK tup R := by
  simp only [Heap.rowTuples, dite_pos_of hx, Heap.flushTuple, hrow]
  by_cases hj : j.val < 5
  · obtain ⟨j', rfl⟩ : ∃ j' : Fin 5, j = j'.castSucc := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
    rw [tablesKeccak_getD_of_ne (by unfold opSha3; omega)]
    refine (kv_flushes_lv j' side R).trans ?_
    cases side
    · exact (uni_tuples_eq_base j' true R).symm
    · exact (uni_tuples_eq_base j' false R).symm
  · have h5 : j = 5 := Fin.ext (by have := j.isLt; omega)
    subst h5
    exact sha3_flushes_eq side R

end UniKeccakSound.IdsReal

/-- info: 'UniKeccakSound.IdsReal.rowTuplesK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsReal.rowTuplesK_eq

/-- info: 'UniKeccakSound.IdsReal.sha3_flushes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsReal.sha3_flushes_eq
