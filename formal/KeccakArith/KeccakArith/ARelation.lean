-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `formal/Lv42`'s `Protocol/LeanIsa/Relation.lean`
-- (leanerVM `mumbai` f0393df4, MIT OR Apache-2.0), for the Keccak VM's ensemble and instance.
module

public import KeccakArith.ABus

/-!
# The relations, clause by clause, for the Keccak VM

On a stack `q` of `keccakIsaInstance prog s` and a witness `w` of `kEnsemble prog` that agree: an opcode table's Clean
constraints hold exactly when the instance's vanish on its executed rows (`opcode_constraints_iff`); the bus balances
exactly when the three channel pairs do (`balanced_iff_pairs`); the read counts are nonzero exactly when the count
columns are (`countsNonzero_iff`).
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Arithmetization KeccakVm KeccakVm.KeccakIsa
open LeanVM.Protocol (Column M3Table flushTuple tupleMsg powersTable CountsAreVariables countVar toM3_constraints_iff mem_toM3_count_iff)
open Lv42.Protocol (M3Instance Side BoundaryBlock Coord idxColumn)
open Lv42.Protocol.LeanIsa (Sizes sideOf counted)
open Lv42.Semantics (Regs MemImage PublicInput)
open Lv42.Parameters (minLogMem maxLogMem maxLogRows)
open Air.Flat (Component EnsembleWitness Ensemble)

@[expose] public section

variable {prog : KeccakVm.Program} {s : Sizes} {q : Column (keccakIsaμ prog s)}
  {w : EnsembleWitness (kEnsemble prog)}

/-! ## Facts of the opcode components -/

/-- No opcode table has a lookup. -/
theorem opcode_lookups : ∀ j : Fin 6, (kOpComponent j).rowOperations.lookups.isEmpty := by
  decide +kernel

/-- Every assert expression of an opcode table reads within its width. -/
theorem opcode_constraints_withinWidth : ∀ j : Fin 6,
    ∀ e ∈ (kOpComponent j).rowOperations.constraints,
        e.WithinWidth (kOpComponent j).width := by
  decide +kernel

/-- Every read count of an opcode table is a column. -/
theorem opcode_countsAreVariables : ∀ j : Fin 6,
    CountsAreVariables (kOpComponent j) counted := by
  decide +kernel

/-- Coordinate `1` of a counted interaction, evaluated on any row, is the row's cell at its count
column, `0` when missing. -/
private theorem msg_one_of_countVar' {n : ℕ} {i : AbstractInteraction K} {k : Fin n}
    (h : countVar n i = some k) (row : Array K) (data : ProverData K) :
    (i.eval (Environment.fromArray row data)).msg[1]? = some (row[(k : ℕ)]?.getD 0) := by
  unfold countVar at h
  simp only [AbstractInteraction.eval, Vector.toArray_map, Array.getElem?_map]
  split at h
  · next v hv =>
    split_ifs at h with hn
    obtain rfl := Option.some.inj h
    rw [hv]
    simp [Expression.eval, Environment.fromArray]
  · exact absurd h (by simp)

/-- A row of a table of known length, by its index. -/
private theorem forall_mem_table {t : Air.Flat.Table K} {n : ℕ} (hn : t.table.length = n)
    {P : Array K → Prop} :
    (∀ row ∈ t.table, P row) ↔ ∀ x : Fin n, P (t.table[x.val]'(by rw [hn]; exact x.isLt)) := by
  constructor
  · exact fun h x ↦ h _ (List.getElem_mem _)
  · intro h row hrow
    obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hrow
    exact h ⟨x, hn ▸ hx⟩

/-! ## The constraints -/

/-- On a row agreeing with `r` within the width, an opcode table's Clean constraints hold exactly
when its constraint polynomials vanish at `r`. -/
private theorem opcode_constraintsHold_iff (j : Fin 6) (row : Array K)
    (r : Fin (kOpComponent j).width → K) (hr : ∀ i : Fin (kOpComponent j).width,
      row[(i : ℕ)]?.getD 0 = r i) (data : ProverData K) :
    (kOpComponent j).operations.ConstraintsHold (Environment.fromArray row data) ↔
      ∀ C ∈ (kOpTable j).constraints, C.eval r = 0 := by
  have hl := List.isEmpty_iff.mp (opcode_lookups j)
  refine Iff.trans ?_ (toM3_constraints_iff (kOpComponent j) channelSep channelDir counted hl
    r data).symm
  rw [Air.Flat.Component.constraintsHold_iff, Air.Flat.Component.constraintsHold_iff,
    Operations.ConstraintsHold, Operations.ConstraintsHold, hl]
  have hrow : (Array.ofFn fun i : Fin (kOpComponent j).width ↦ row[(i : ℕ)]?.getD 0) =
      Array.ofFn r := congrArg Array.ofFn (funext hr)
  simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  refine forall₂_congr fun e he ↦ ?_
  rw [Expression.eval_fromArray_truncate row data (opcode_constraints_withinWidth j e he), hrow]

/-- Opcode table `j`'s Clean constraints hold on every row exactly when the instance's constraint
polynomials of that table vanish on every executed row of the stack. -/
theorem opcode_constraints_iff (h : Agrees s q w) (j : Fin 6) :
    (opTable w j).Constraints ↔
      ∀ x : Fin ((keccakIsaInstance prog s).rows (opIdx j)), ∀ C ∈ (kOpTable j).constraints,
        C.eval (kRow ((keccakIsaInstance prog s).row q (opIdx j)
          (Fin.castLE ((keccakIsaInstance prog s).rows_le _) x))) = 0 := by
  rw [Air.Flat.Table.Constraints, forall_mem_table (h.length j)]
  refine forall_congr' fun x ↦ ?_
  rw [Air.Flat.Table.environment, opTable_component]
  refine opcode_constraintsHold_iff j _ _ (fun i ↦ ?_) _
  rw [kRow, ← h.cells j x (Fin.cast (kw prog s j).symm i), cellOf, List.getElem?_eq_getElem]
  rfl

/-! ## The bus -/

/-- The instance's bus balances exactly when leanISA's three channel pairs do. -/
theorem balanced_iff_pairs (h : Agrees s q w) :
    (keccakIsaInstance prog s).Balanced q ↔ ∀ k : Fin 3, BalancedPair w (pullOf k) (pushOf k) := by
  rw [← balanced_iff]
  exact ⟨fun hb ↦ (tuples_perm h .push).symm.trans (hb.trans (tuples_perm h .pull)),
    fun hb ↦ (tuples_perm h .push).trans (hb.trans (tuples_perm h .pull).symm)⟩

/-! ## The read counts -/

/-- A counted interaction of an opcode table has at least two coordinates. -/
private theorem opcode_counted_arity :
    ∀ j : Fin 6, ∀ ai ∈ (kOpComponent j).rowOperations.interactions,
    counted ai.channel → 1 < ai.channel.arity := by
  decide +kernel

/-- The first six tables of a witness are its opcode tables. -/
private theorem take_six_tables (w : EnsembleWitness (kEnsemble prog)) :
    w.tables.take 6 = (List.finRange 6).map (opTable w) := by
  rw [tables_eq_map, show List.finRange 8 = (List.finRange 6).map (fun j : Fin 6 ↦
      (⟨j, by omega⟩ : Fin 8)) ++ [6, 7] by decide, List.map_append, List.map_map,
    List.take_left' (by simp)]
  rfl

/-- The instance's count cells are nonzero exactly when, on every opcode table, every count column
is nonzero on the stack's rows. -/
private theorem m3_countsNonzero_iff :
    (keccakIsaInstance prog s).CountsNonzero q ↔
      ∀ j : Fin 6, ∀ k ∈ (kOpTable j).count, ∀ x : Fin ((keccakIsaInstance prog s).rows (opIdx j)),
        kRow ((keccakIsaInstance prog s).row q (opIdx j)
          (Fin.castLE ((keccakIsaInstance prog s).rows_le _) x)) k ≠ 0 := by
  constructor
  · intro hc j k hk x
    have hi : Fin.cast (kw prog s j).symm k ∈ (keccakIsaInstance prog s).counts (opIdx j) :=
      (mem_inst_counts prog s j _).mpr hk
    exact hc (opIdx j) _ hi _ x.isLt
  · intro hc j'
    rcases j' with ⟨_ | _ | _ | j, hj⟩
    · exact fun i hi ↦ absurd hi List.not_mem_nil
    · exact fun i hi ↦ absurd hi List.not_mem_nil
    · exact fun i hi ↦ absurd hi List.not_mem_nil
    · have h9 : (keccakIsaInstance prog s).ntab = 9 := rfl
      intro k hk x hx
      exact hc ⟨j, by omega⟩ _ ((mem_inst_counts prog s ⟨j, by omega⟩ k).mp hk) ⟨x.val, hx⟩

/-- An interaction of a table of known length: one of its component's, on one of its rows. -/
private theorem forall_mem_interactions {t : Air.Flat.Table K} {n : ℕ} (hn : t.table.length = n)
    {P : Interaction K → Prop} :
    (∀ i ∈ t.interactions, P i) ↔
      ∀ x : Fin n, ∀ ai ∈ t.component.rowOperations.interactions,
        P (ai.eval (t.environment (t.table[x.val]'(by rw [hn]; exact x.isLt)))) := by
  constructor
  · intro hP x ai hai
    refine hP _ ?_
    simp only [Air.Flat.Table.interactions, List.mem_flatMap, Operations.interactionValues,
      List.mem_map, Air.Flat.Component.interactions_eq]
    exact ⟨_, List.getElem_mem _, ai, hai, rfl⟩
  · intro hP i hi
    simp only [Air.Flat.Table.interactions, List.mem_flatMap, Operations.interactionValues,
      List.mem_map, Air.Flat.Component.interactions_eq] at hi
    obtain ⟨row, hrow, ai, hai, rfl⟩ := hi
    obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hrow
    exact hP ⟨x, hn ▸ hx⟩ ai hai

/-- A counted interaction's channel is the memory or bytecode pull. -/
private theorem name_of_counted {ch : RawChannel K} (h : counted ch = true) :
    ch.name = MemPull.name ∨ ch.name = BytecodePull.name := by
  simpa [counted] using h

/-- **The read counts.** Every read count of the six opcode tables is nonzero exactly when every
cell of the instance's count columns is. -/
theorem countsNonzero_iff (h : Agrees s q w) :
    CountsNonzero w ↔ (keccakIsaInstance prog s).CountsNonzero q := by
  rw [m3_countsNonzero_iff, CountsNonzero, take_six_tables, List.forall_mem_map]
  refine forall_congr' fun j ↦ ?_
  simp only [List.mem_finRange, true_implies]
  rw [forall_mem_interactions (h.length j), opTable_component]
  have hcell : ∀ (x : Fin ((keccakIsaInstance prog s).rows (opIdx j))) (k : Fin (kOpComponent j).width),
      ((opTable w j).table[x.val]'(by rw [h.length j]; exact x.isLt))[k.val]?.getD 0 =
        kRow ((keccakIsaInstance prog s).row q (opIdx j)
          (Fin.castLE ((keccakIsaInstance prog s).rows_le _) x)) k := fun x k ↦ by
    rw [kRow, ← h.cells j x (Fin.cast (kw prog s j).symm k), cellOf, List.getElem?_eq_getElem]
    rfl
  constructor
  · intro hc k hk x
    obtain ⟨ai, hai, hcnt, hk'⟩ := (mem_toM3_count_iff _ _ _ _ k).mp hk
    have hm := msg_one_of_countVar' hk' ((opTable w j).table[x.val]'(by
      rw [h.length j]; exact x.isLt)) (opTable w j).data
    have hsize : 1 < (ai.eval (Environment.fromArray ((opTable w j).table[x.val]'(by
        rw [h.length j]; exact x.isLt)) (opTable w j).data)).msg.size := by
      rw [Interaction.same_size]
      exact opcode_counted_arity j ai hai hcnt
    have hne := hc x ai hai (name_of_counted hcnt) hsize
    rw [Array.getElem?_eq_getElem hsize] at hm
    rw [← (Option.some.inj hm).trans (hcell x k)]
    exact hne
  · intro hc x ai hai hname hsize
    change 1 < (ai.eval (Environment.fromArray _ (opTable w j).data)).msg.size at hsize
    change (ai.eval (Environment.fromArray _ (opTable w j).data)).msg[1] ≠ 0
    have hcnt : counted ai.channel = true := by
      simp only [counted, Bool.or_eq_true, decide_eq_true_eq]
      exact hname
    obtain ⟨k, hk'⟩ := Option.isSome_iff_exists.mp (opcode_countsAreVariables j ai hai hcnt)
    have hm := msg_one_of_countVar' hk' ((opTable w j).table[x.val]'(by
      rw [h.length j]; exact x.isLt)) (opTable w j).data
    rw [Array.getElem?_eq_getElem hsize] at hm
    rw [(Option.some.inj hm).trans (hcell x k)]
    exact hc k ((mem_toM3_count_iff _ _ _ _ k).mpr ⟨ai, hai, hcnt, hk'⟩) x

end

end KeccakArith

end
