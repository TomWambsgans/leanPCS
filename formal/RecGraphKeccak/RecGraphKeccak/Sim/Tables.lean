-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import RecGraph.Sim.TablePart
import RecGraphKeccak.Sim.ComposeSpec

/-!
# The Keccak VM's tables' parts, simulated

`RecGraph.Sim.tablePart_sim` is the program's `tablePart` against `UniStatement.tablePart` for any table whose flush
tuples have at most as many slots as there are weights; the Keccak VM's six tables (`tablesKeccak`: leanVM's five and
the `SHA3` table) have at most 16 (`tuples_le`, by evaluation). So `tableSpecK : TableSpecK partRK tableShapeK
tableBytesK`: a part represented (`RpPart`) with a Keccak table's degrees (`PartDegK`), its relations' terms in the
table's columns at `w[..h_t]` (`TabShape`), `24 · tableReads t` bytes.
-/

set_option linter.dupNamespace false

namespace RecGraphKeccak.Sim

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol UniStatement RecGraph RecGraph.Pi1 RecGraph.Sim RecGraphKeccak.Pi1

/-- The Keccak VM's flush tuples have at most 16 slots. -/
theorem tuples_le : ∀ t ∈ tablesKeccak, ∀ tup ∈ t.flushes.pull ++ t.flushes.push, tup.length ≤ 16 := by
  decide

/-- **A part's degrees are a Keccak table's** (`tableDegrees`). -/
def PartDegK (u : TablePart) : Prop :=
  ∃ t ∈ tablesKeccak, u.pullDegree = (tableDegrees t).1 ∧ u.pushDegree = (tableDegrees t).2

/-- **The parts' representation** for the Keccak composition (`RpPart`), the degrees a Keccak table's. -/
def partRK : PartRep := fun π iv publicInput stream st p u ↦ RpPart π iv publicInput stream st p u ∧ PartDegK u

theorem partRK_grows : PartRepGrows partRK :=
  fun π iv publicInput stream _ _ _ _ hk hgr h ↦ ⟨RpPart.grow π iv publicInput stream hk hgr h.1, h.2⟩

/-- **A table's bytes**: `24` a value it reads (`UniSound.tableReads`). -/
def tableBytesK (t : Table) : Nat := 24 * UniSound.tableReads t

/-- **A table's part, its shape**: its relations' terms in its columns, at `w[..h_t]` (`h_t` its height at
`keccak128`). -/
def tableShapeK (t : Table) (wE : List E) (b : TablePart × List Relation) : Prop :=
  TabShape t (keccak128.heights.getD t.opcode 0) wE b.2

/-- **`TableSpecK`**, the Keccak composition's interface for a table's part. -/
theorem tableSpecK : TableSpecK partRK tableShapeK tableBytesK := by
  intro π iv publicInput stream st t ht weights weightsE beta betaE w wE _ hwt hsize hbeta hw _
  refine Sim.mono (tablePart_sim π iv publicInput stream st t _ hwt
    (fun tup htup ↦ by rw [hsize]; exact tuples_le t ht tup htup) hbeta hw)
    fun _ _ _ _ _ h ↦ ⟨⟨h.1, t, ht, congrArg Prod.fst h.2.2.2, congrArg Prod.snd h.2.2.2⟩, h.2.1, h.2.2.1⟩

end RecGraphKeccak.Sim
