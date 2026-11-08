-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `formal/Lv42`'s `Arithmetization/Statement.lean` and
-- the verifier and bytecode block of `Arithmetization/Boundary.lean` (leanerVM `mumbai` f0393df4, MIT OR Apache-2.0),
-- for the Keccak VM: the `SHA3` table in `BLAKE2S`'s place, the Keccak VM's programs.
module

public import KeccakArith.Rows
public import KeccakVm.Lemmas
public import Clean.Air.FlatEnsemble

/-!
# The Keccak VM's constraint statement

Lv42's constraint statement (`Lv42.Arithmetization.SatisfiedBy`), for the Keccak VM. The ensemble `kEnsemble prog` has
Lv42's five opcode tables, the `SHA3` table (`sha3Table`) in `BLAKE2S`'s place, Lv42's memory and bytecode blocks, the
six channels, and the verifier `kVerifier prog` (Lv42's `leanIsaVerifier`, at the Keccak VM's `finalPc`). A witness
`w : EnsembleWitness (kEnsemble prog)` satisfies `SatisfiedBy prog input w` when every conjunct of Lv42's holds, with
`Sha3RowsValid w` (every `SHA3` row satisfies `Sha3Relation`, the table's `Assumptions`, which the Keccak-f region
gives) in place of `Blake2sRowsValid`, and the bytecode block's rows the Keccak VM program's (`kBytecodeRowOf`).
`AssignmentRepresents w t` is Lv42's, at the Keccak VM's traces.
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Arithmetization KeccakVm
open Lv42.Semantics (Regs MemImage PublicInput)
open Lv42.Parameters (minLogMem maxLogMem maxLogRows)
open Air.Flat (Ensemble EnsembleWitness Component)

/-! ## The verifier and the bytecode block's rows -/

/-- The verifier's state boundary for the Keccak VM program `prog`: push `(1, 1)`, pull `(finalPc, 1)` (Lv42's
`leanIsaVerifier`). -/
def kVerifier (prog : KeccakVm.Program) : GeneralFormalCircuit K PublicIO unit where
  main _ := do
    StatePush.push ⟨1, 1⟩
    StatePull.pull ⟨Expression.const prog.finalPc, 1⟩
  channelsWithRequirements := [StatePush.toRaw]
  requirementsChannelsLawful input offset := by
    simp only [circuit_norm, -BitVec.reduceNeg]
    tauto
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start [StatePull, StatePush]
  completeness := by
    circuit_proof_start [StatePull, StatePush]

/-- The seed row of slot `i` of the Keccak VM program `prog`, with finalize count `cntFin` (Lv42's
`bytecodeRowOf`). -/
def kBytecodeRowOf (prog : KeccakVm.Program) (i : Fin (2 ^ prog.logSize)) (cntFin : K) : BytecodeRow K :=
  let e := KeccakVm.entry (prog.code i)
  ⟨gpow i, cntFin, e[0], #v[e[1], e[2], e[3], e[4], e[5], e[6], e[7]]⟩

/-! ## The ensemble -/

/-- The Keccak VM ensemble of the public program `prog`. -/
def kEnsemble (prog : KeccakVm.Program) : Ensemble K PublicIO where
  tables := [⟨xorTable⟩, ⟨mulTable⟩, ⟨setTable⟩, ⟨derefTable⟩, ⟨jumpTable⟩, ⟨sha3Table⟩,
    ⟨memTable⟩, ⟨bytecodeTable⟩]
  channels := [StatePull.toRaw, StatePush.toRaw, MemPull.toRaw, MemPush.toRaw,
    BytecodePull.toRaw, BytecodePush.toRaw]
  verifier := kVerifier prog
  verifier_length_zero _ := by simp only [circuit_norm, kVerifier]

/-! ## Reading a witness -/

variable {prog : KeccakVm.Program}

/-- The witness's table of component `j`. -/
def tableAt (w : EnsembleWitness (kEnsemble prog)) (j : Fin 8) : Air.Flat.Table K :=
  w.tables[(j : ℕ)]'(by rw [← w.same_length]; exact j.isLt)

/-- The rows of the `SHA3` table. -/
abbrev sha3Rows (w : EnsembleWitness (kEnsemble prog)) : List (Array K) := (tableAt w 5).table

/-- The rows of the memory block. -/
abbrev memBlockRows (w : EnsembleWitness (kEnsemble prog)) : List (Array K) := (tableAt w 6).table

/-- The rows of the bytecode block. -/
abbrev bytecodeBlockRows (w : EnsembleWitness (kEnsemble prog)) : List (Array K) := (tableAt w 7).table

/-- The messages the witness sends on the channel `c`. -/
def messagesOn (w : EnsembleWitness (kEnsemble prog)) (c : RawChannel K) : List (Array K) :=
  (w.interactions.filter (·.channel.name = c.name)).map (·.msg)

/-- A raw row of the memory block, read as its typed row. -/
def memRowAt (w : EnsembleWitness (kEnsemble prog)) (row : Array K) : MemRow K :=
  valueFromOffset MemRow 0 (Environment.fromArray row w.data)

/-- A raw row of the `SHA3` table, read as its typed row. -/
def sha3RowAt (w : EnsembleWitness (kEnsemble prog)) (row : Array K) : Sha3Row K :=
  valueFromOffset Sha3Row 0 (Environment.fromArray row w.data)

/-- Pushed and pulled messages of a channel pair form the same multiset. -/
def BalancedPair (w : EnsembleWitness (kEnsemble prog)) (pull push : RawChannel K) : Prop :=
  (messagesOn w push).Perm (messagesOn w pull)

/-- Every read pull of the six tables carries a nonzero count. -/
def CountsNonzero (w : EnsembleWitness (kEnsemble prog)) : Prop :=
  ∀ t ∈ w.tables.take 6, ∀ i ∈ t.interactions,
    (i.channel.name = MemPull.name ∨ i.channel.name = BytecodePull.name) →
      ∀ h : 1 < i.msg.size, i.msg[1] ≠ 0

/-- The M3 checks of the announced instance. -/
structure Caps (w : EnsembleWitness (kEnsemble prog)) : Prop where
  minLogMem_le : minLogMem ≤ (imageOf w.data).1
  le_maxLogMem : (imageOf w.data).1 ≤ maxLogMem
  heights : ∀ t ∈ w.tables, t.table.length ≤ 2 ^ maxLogRows
  well_shaped : WellShapedData w.data

/-- The `idx` column of row `i` of the memory block is `g^i`. -/
def IndexColumnsAreRowIndices (w : EnsembleWitness (kEnsemble prog)) : Prop :=
  ∀ i (hi : i < (memBlockRows w).length), (memRowAt w (memBlockRows w)[i]).idx = gpow i

/-- The memory block's rows are the words of the image the prover data names, in order. -/
def SeedRowsAreTheImage (w : EnsembleWitness (kEnsemble prog)) : Prop :=
  ∃ idx cntFin : Fin (2 ^ (imageOf w.data).1) → K,
    memBlockRows w = List.ofFn fun i ↦
      (toElements (⟨idx i, cntFin i, #v[((imageOf w.data).2 i).limb 0,
        ((imageOf w.data).2 i).limb 1, ((imageOf w.data).2 i).limb 2]⟩ : MemRow K)).toArray

/-- The bytecode block's rows are the program's. -/
def BytecodeRowsAreTheProgram (prog : KeccakVm.Program) (w : EnsembleWitness (kEnsemble prog)) : Prop :=
  ∃ cntFin : Fin (2 ^ prog.logSize) → K,
    bytecodeBlockRows w = List.ofFn fun i ↦ (toElements (kBytecodeRowOf prog i (cntFin i))).toArray

/-- Every row of the `SHA3` table satisfies the Keccak relation on its lanes (`Sha3Relation`, the table's
`Assumptions`): what the Keccak-f region proves of the lanes' copies. -/
def Sha3RowsValid (w : EnsembleWitness (kEnsemble prog)) : Prop :=
  ∀ row ∈ sha3Rows w, Sha3Relation (sha3RowAt w row)

/-- **The Keccak VM's constraint statement**: Lv42's conjuncts, with `Sha3RowsValid`. -/
structure SatisfiedBy (prog : KeccakVm.Program) (input : PublicInput) (w : EnsembleWitness (kEnsemble prog)) :
    Prop where
  public_input_eq : w.publicInput = PublicIO.ofInput input
  constraints : w.Constraints
  state_balanced : BalancedPair w StatePull.toRaw StatePush.toRaw
  mem_balanced : BalancedPair w MemPull.toRaw MemPush.toRaw
  bytecode_balanced : BalancedPair w BytecodePull.toRaw BytecodePush.toRaw
  counts_nonzero : CountsNonzero w
  caps : Caps w
  index_columns : IndexColumnsAreRowIndices w
  seed_rows : SeedRowsAreTheImage w
  bytecode_rows : BytecodeRowsAreTheProgram prog w
  sha3_valid : Sha3RowsValid w
  word0_eq : (imageOf w.data).2.read (gpow 0) = some input.word0
  word1_eq : (imageOf w.data).2.read (gpow 1) = some input.word1

/-! ## The trace a witness represents -/

/-- The messages one row of a table sends on the channel `c`. -/
def rowMessagesOn (t : Air.Flat.Table K) (row : Array K) (c : RawChannel K) : List (Array K) :=
  ((t.component.operations.interactionValues (t.environment row)).filter
    (·.channel.name = c.name)).map (·.msg)

/-- Some row of some table steps from `r` to `r'`. -/
def RowSteps (w : EnsembleWitness (kEnsemble prog)) (r r' : Regs K) : Prop :=
  ∃ t ∈ w.tables, ∃ row ∈ t.table,
    rowMessagesOn t row StatePull.toRaw = [#[r.pc, r.fp]] ∧
      rowMessagesOn t row StatePush.toRaw = [#[r'.pc, r'.fp]]

/-- The witness `w` represents the Keccak VM trace `t`. -/
structure AssignmentRepresents (w : EnsembleWitness (kEnsemble prog)) (t : KeccakVm.Trace prog) : Prop where
  κ_eq : (imageOf w.data).1 = t.κ
  image_eq : ∀ i (hi : i < 2 ^ t.κ), (imageOf w.data).2 ⟨i, κ_eq ▸ hi⟩ = t.image ⟨i, hi⟩
  regs_embed : ∀ k (hk : k + 1 < t.regs.length), RowSteps w t.regs[k] t.regs[k + 1]

/-! ## Lemmas -/

/-- `memRowAt` inverts `toElements`. -/
theorem memRowAt_toElements (w : EnsembleWitness (kEnsemble prog)) (r : MemRow K) :
    memRowAt w (toElements r).toArray = r :=
  rowAt_toElements w.data r

/-- A table of the witness is `tableAt w j` for some `j`. -/
theorem mem_tables_iff {w : EnsembleWitness (kEnsemble prog)} {t : Air.Flat.Table K} :
    t ∈ w.tables ↔ ∃ j : Fin 8, tableAt w j = t := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by rwa [← w.same_length] at hi⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, _, rfl⟩

/-- The component of `tableAt w j` is the ensemble's `j`-th. -/
theorem tableAt_component (w : EnsembleWitness (kEnsemble prog)) (j : Fin 8) :
    (tableAt w j).component = (kEnsemble prog).tables[(j : ℕ)] :=
  (w.same_circuits j j.isLt).symm

/-- The Keccak relation on the `SHA3` rows is the whole of Clean's `w.Assumptions`. -/
theorem assumptions_of_sha3RowsValid {w : EnsembleWitness (kEnsemble prog)}
    (h : Sha3RowsValid w) : w.Assumptions := by
  intro t ht
  simp only [EnsembleWitness.allTables, List.mem_cons] at ht
  rcases ht with rfl | ht
  · exact fun _ _ ↦ trivial
  · have hd : t.data = w.data := w.same_data t ht
    obtain ⟨j, rfl⟩ := mem_tables_iff.mp ht
    intro row hrow
    rw [tableAt_component, Air.Flat.Table.environment, hd]
    fin_cases j
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact trivial
    · exact h row hrow
    · exact trivial
    · exact trivial

end KeccakArith

end
