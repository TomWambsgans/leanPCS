-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The reflection is `formal/UniSound`'s
-- `UniSound/Ids/LvRealize.lean` (`uni_tuples_eq`), at the Keccak VM's `SHA3` table.
import UniStatement.FormPoly
import UniStatement.KeccakTables
import KeccakVm.Instance

/-!
# The verifier's `SHA3` flushes are the instance's

`flushesSha3_eq`: on every row `R : ℕ → K`, the tuples of the verifier's `SHA3` forms of one side
(`UniStatement.flushesSha3`, read at the row by `UniSound.Ids.tupleK`) are, **in order**, the instance's `SHA3`
flushes of that side (`KeccakVm.Sha3Table.flushes`, whose polynomials are evaluated at the row's first 86 cells).
The two are written from the same Rust function (`layout.rs::flushes_sha3`); this is the statement `UniSound`'s
`uni_tuples_eq` gives the five other tables (`rowTuples_eq` reads its right side off a stack's row), here for the
`SHA3` table, so that a port of `UniSound/Ids/LvRealize.lean` to the Keccak VM reads the `SHA3` table's tuples of
`UniStatement.tablesKeccak` as `KeccakVm.keccakIsaInstance`'s flushes.

The proof is `uni_tuples_eq`'s reflection: both sides are read as polynomials in a normal form (`LvR.SP`,
`LvR.spNorm`; the forms by `LvR.formSP`, the instance's Clean expressions by `LvR.exprSP` before they become
`CMvPolynomial`s), the two lists of normal forms of each side are equal by `decide +kernel` (`sha3Sides_eq`), and
the normal form keeps the value (`LvR.spEval_spNorm`).
-/

namespace KeccakFlushes

open LeanVM.Parameters Lv42.Protocol UniStatement UniSound.Ids UniSound.Ids.LvR KeccakVm

/-- The verifier's `SHA3` forms of one side: `push` or `pull`. -/
def uniSha3 (side : Side) : List (List Form) :=
  if side = .push then flushesSha3.push else flushesSha3.pull

/-- A flush's sixteen coordinates as polynomials in normal form: its expressions on the row's 86 cells, zeros past
its end. -/
def exprTupSP (l : List (Expression K)) : List SP :=
  (List.range 16).map fun j ↦ exprSP Sha3Table.width (l.getD j (Sha3Table.k 0))

/-- The instance's `SHA3` flushes of one side, as normal forms, in order. -/
def instSide (side : Side) : List (List SP) :=
  ((Sha3Table.flushExprs.filter fun f ↦ decide (f.1 = side)).map fun f ↦ exprTupSP f.2).map
    (·.map spNorm)

/-- The verifier's `SHA3` forms of one side, as normal forms, in order. -/
def uniSide (side : Side) : List (List SP) := ((uniSha3 side).map tupSP).map (·.map spNorm)

set_option maxRecDepth 100000 in
/-- The push sides' normal forms are equal, in order. -/
theorem sha3Sides_eq_push : uniSide .push = instSide .push := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pull sides' normal forms are equal, in order. -/
theorem sha3Sides_eq_pull : uniSide .pull = instSide .pull := by
  decide +kernel

/-- **The normal forms are equal**, side by side, in order. -/
theorem sha3Sides_eq : ∀ side : Side, uniSide side = instSide side
  | .push => sha3Sides_eq_push
  | .pull => sha3Sides_eq_pull

/-- An instance flush's tuple at a row is its normal forms' values. -/
theorem tuple_eval_eq (l : List (Expression K)) (R : ℕ → K) :
    (Sha3Table.tuple l).map (·.eval fun i : Fin Sha3Table.width ↦ R i.val) =
      tupleOfSP R ((exprTupSP l).map spNorm) := by
  apply Vector.ext
  intro j hj
  simp only [Sha3Table.tuple, Vector.getElem_map, Vector.getElem_ofFn, tupleOfSP, exprTupSP]
  rw [getD_map_range _ j hj, spEval_spNorm, Expression.eval_toCMvPolynomial _ noData, eval_exprSP]

/-- The instance's `SHA3` flushes of one side, as `(side, tuple)` pairs filtered, are its expressions' tuples. -/
theorem flushes_filter (side : Side) :
    (Sha3Table.flushes.filter fun f ↦ decide (f.1 = side)) =
      (Sha3Table.flushExprs.filter fun f ↦ decide (f.1 = side)).map fun f ↦ (f.1, Sha3Table.tuple f.2) := by
  unfold Sha3Table.flushes
  induction Sha3Table.flushExprs with
  | nil => rfl
  | cons f l ih =>
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    split_ifs <;> simp_all

/-- **The verifier's `SHA3` flushes are the instance's**: on every row `R`, the tuples of the verifier's forms of
one side (`tupleK`) are, in order, the instance's `SHA3` flushes of that side evaluated at the row's 86 cells. -/
theorem flushesSha3_eq (side : Side) (R : ℕ → K) :
    ((if side = .push then flushesSha3.push else flushesSha3.pull).map fun tup ↦ tupleK tup R) =
      (Sha3Table.flushes.filter fun f ↦ decide (f.1 = side)).map
        fun f ↦ f.2.map (·.eval fun i : Fin Sha3Table.width ↦ R i.val) := by
  have h := congrArg (List.map (tupleOfSP R)) (sha3Sides_eq side)
  simp only [uniSide, instSide, List.map_map] at h
  rw [flushes_filter, List.map_map]
  simp only [Function.comp_def, tuple_eval_eq]
  simp only [tupleK_eq]
  exact h

/-- The `SHA3` table of `UniStatement.tablesKeccak` is `flushesSha3`'s. -/
theorem tablesKeccak_sha3 : tablesKeccak.getD opSha3 default = ⟨opSha3, sha3Columns, flushesSha3⟩ :=
  rfl

/-- `SHA3_COLUMNS` has the instance's width. -/
theorem sha3Columns_length : sha3Columns.length = Sha3Table.width := by decide

end KeccakFlushes

/-- info: 'KeccakFlushes.flushesSha3_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms KeccakFlushes.flushesSha3_eq
