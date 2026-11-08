-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `formal/Lv42`'s `Arithmetization/Soundness/StateWalk.lean`
-- and `Soundness/Theorem.lean` (leanerVM `mumbai` f0393df4, MIT OR Apache-2.0), for the Keccak VM.
module

public import KeccakArith.SBcChannel
public import KeccakArith.Walk

/-!
# The state walk and constraint soundness, for the Keccak VM

Lv42's `exists_walk` and `constraintSoundness` at `kEnsemble`: under `SentinelSafe`, a witness of `SatisfiedBy`
carries records for its rows and a run of the Keccak VM from `(1, 1)` to `(finalPc, 1)` over the image its data
names, each of whose steps is a row (`exists_walk`); so it represents a valid execution (`constraintSoundness`).
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Arithmetization KeccakVm
open Lv42.Semantics (Regs MemImage PublicInput)
open Lv42.Parameters (minLogMem maxLogMem maxLogRows)
open Air.Flat (Component EnsembleWitness)

variable {prog : KeccakVm.Program} {input : PublicInput} {w : EnsembleWitness (kEnsemble prog)}

/-! ## The rows are steps -/

/-- An interaction of a table is sent by one of its rows. -/
theorem mem_rowSends_of_mem_interactions {t : Air.Flat.Table K} {i : Interaction K}
    (hi : i ∈ t.interactions) :
    ∃ row ∈ t.table, i.msg ∈ chanOf i.channel.name (rowSends t.component (t.environment row)) := by
  unfold Air.Flat.Table.interactions at hi
  obtain ⟨row, hrow, hi⟩ := List.mem_flatMap.mp hi
  refine ⟨row, hrow, ?_⟩
  rw [Component.interactionsValues_eq] at hi
  unfold chanOf rowSends
  refine List.mem_map.mpr ⟨(i.channel.name, i.msg), List.mem_filter.mpr ⟨?_, by simp⟩, rfl⟩
  exact List.mem_map_of_mem hi

/-- The interactions of a row of a witness's table are interactions of the witness. -/
theorem eval_mem_interactions {t : Air.Flat.Table K} (ht : t ∈ w.tables) {row : Array K}
    (hrow : row ∈ t.table) {a : AbstractInteraction K}
    (ha : a ∈ t.component.operations.interactions) :
    a.eval (t.environment row) ∈ w.interactions := by
  unfold EnsembleWitness.interactions
  refine List.mem_flatMap.mpr ⟨t, w.mem_allTables_of_mem_tables ht, ?_⟩
  unfold Air.Flat.Table.interactions
  exact List.mem_flatMap.mpr ⟨row, hrow, List.mem_map_of_mem ha⟩

/-- The pulls of a row of the six tables have their guarantees: the memory reads are the image's
words (`mem_channel_sound`) and the bytecode entry decodes (`bytecode_guarantee`). -/
theorem opRecs_guarantees (h : SatisfiedByB prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) {p : Air.Flat.Table K × Array K} (hp : p ∈ opPairs w) :
    p.1.component.operations.FullGuarantees (p.1.environment p.2) := by
  obtain ⟨ht, hrow⟩ := mem_opPairs hp
  have ht' := List.mem_of_mem_take ht
  have hdata := environment_data ht' p.2
  intro a ha
  have hmem := eval_mem_interactions ht' hrow ha
  rcases (hf p hp).2.2.1 a ha with hc | hc | hc
  · obtain ⟨ch, mult, msg, ag⟩ := a
    dsimp only at hc
    subst hc
    intro _ _
    rw [hdata]
    exact mem_channel_sound h _ hmem rfl _
      (by rw [ProvableType.toElements_fromElements]; rfl)
  · obtain ⟨ch, mult, msg, ag⟩ := a
    dsimp only at hc
    subst hc
    intro _ _
    rw [hdata]
    exact bytecode_guarantee h _ hmem rfl _
      (by rw [ProvableType.toElements_fromElements]; rfl)
  · exact fun _ ↦ hc _ _ _

/-- **Every row of the six tables is a step of the program** over the image the data names, from
its pulled state to its pushed state; its counter is a slot `g^k` of the program, and unless the
program holds a `JUMP` there the successor is the fall-through. -/
theorem opRecs_step (h : SatisfiedBy prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) {p : Air.Flat.Table K × Array K} (hp : p ∈ opPairs w) :
    KeccakVm.step prog (imageOf w.data).2 (f p).src = some (f p).next ∧
      ∃ k : Fin (2 ^ prog.logSize), (f p).pc = gpow k ∧
        ((prog.code k).opcode ≠ .jump → (f p).next = ⟨g * (f p).pc, (f p).fp⟩) := by
  obtain ⟨ht, hrow⟩ := mem_opPairs hp
  have ht' := List.mem_of_mem_take ht
  have ha := assumptions_of_sha3RowsValid h.sha3_valid p.1
    (w.mem_allTables_of_mem_tables ht') p.2 hrow
  have hc := h.constraints p.1 (w.mem_allTables_of_mem_tables ht') p.2 hrow
  obtain ⟨ins, he, hexec, hnj⟩ := (hf p hp).2.2.2 ha hc (opRecs_guarantees h.toB hf hp)
  obtain ⟨k, hpc, hek⟩ := opRecs_bc_sound h.toB hf hp
  have hins : prog.code k = ins := KeccakVm.entry_injective (hek.symm.trans he)
  refine ⟨?_, k, hpc, fun hj ↦ hnj (hins ▸ hj)⟩
  have hfetch : prog.fetch (f p).src.pc = some ins := by
    rw [show (f p).src.pc = (f p).pc from rfl, hpc, KeccakVm.Program.fetch_gpow, hins]
  rw [KeccakVm.step_of_fetch_eq_some hfetch]
  exact hexec

/-! ## The state pair -/

/-- A state message as an array. -/
def regsArr (r : Regs K) : Array K := #[r.pc, r.fp]

/-- The state of a state message, `0` for a missing coordinate. -/
def arrRegs (a : Array K) : Regs K := ⟨a.getD 0 0, a.getD 1 0⟩

/-- Reading a state message back gives the state. -/
theorem arrRegs_regsArr (r : Regs K) : arrRegs (regsArr r) = r := rfl

/-- **The states a satisfying witness pushes**: the verifier's `(1, 1)` and the rows'
successors. -/
theorem statePush_eq (h : SatisfiedByB prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) :
    messagesOn w StatePush.toRaw =
      regsArr Regs.initial :: (opPairs w).map fun p ↦ regsArr (f p).next := by
  obtain ⟨mfin, bfin, hall⟩ := allSends_eq h hf
  rw [messagesOn_eq_chanOf, chanOf_allSends _ hall]
  simp only [Channel.toRaw_name]
  rw [chanOf_verifier_statePush,
    chanOf_memSeed_eq_nil _ _ (by simp [StatePush, MemPull]) (by simp [StatePush, MemPush]),
    chanOf_bcSeed_eq_nil _ (by simp [StatePush, BytecodePull]) (by simp [StatePush, BytecodePush])]
  simp only [RowRec.sends, chanOf, sendsOf_statePush, List.append_nil, flatMap_singleton_eq_map']
  rfl

/-- **The states a satisfying witness pulls**: the verifier's final registers and the rows'
states. -/
theorem statePull_eq (h : SatisfiedByB prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) :
    messagesOn w StatePull.toRaw =
      regsArr (finalRegs prog) :: (opPairs w).map fun p ↦ regsArr (f p).src := by
  obtain ⟨mfin, bfin, hall⟩ := allSends_eq h hf
  rw [messagesOn_eq_chanOf, chanOf_allSends _ hall]
  simp only [Channel.toRaw_name]
  rw [chanOf_verifier_statePull,
    chanOf_memSeed_eq_nil _ _ (by simp [StatePull, MemPull]) (by simp [StatePull, MemPush]),
    chanOf_bcSeed_eq_nil _ (by simp [StatePull, BytecodePull]) (by simp [StatePull, BytecodePush])]
  simp only [RowRec.sends, chanOf, sendsOf_statePull, List.append_nil, flatMap_singleton_eq_map']
  rfl

/-! ## No row at the sentinel -/

/-- The bytecode has at most `2^32` slots, fewer than the order of `g`. -/
theorem two_pow_logSize_lt (prog : KeccakVm.Program) : 2 ^ prog.logSize < 2 ^ 64 - 1 :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) prog.logSize_le) (by decide)

/-- **No row of the six tables sits at the sentinel counter**: its instruction is not a `JUMP`, so it would push
`(g^N_prog, fp)`, which no pull balances. -/
theorem opRecs_pc_ne_finalPc (hsafe : SentinelSafe prog) (h : SatisfiedBy prog input w)
    {f : Air.Flat.Table K × Array K → RowRec} (hf : OpRecs w f) {p : Air.Flat.Table K × Array K}
    (hp : p ∈ opPairs w) : (f p).pc ≠ prog.finalPc := by
  intro hfin
  have hN := two_pow_logSize_lt prog
  have hpos := Nat.two_pow_pos prog.logSize
  obtain ⟨-, k, hk, hnj⟩ := opRecs_step h hf hp
  have hkN : (k : ℕ) = 2 ^ prog.logSize - 1 := by
    have : gpow k = gpow (2 ^ prog.logSize - 1) := hk.symm.trans hfin
    exact gpow_injOn (by simp only [Set.mem_Iio]; have := k.isLt; omega)
      (by simp only [Set.mem_Iio]; omega) this
  have hsafe : (prog.code k).opcode ≠ .jump := by
    have hk' : k = ⟨2 ^ prog.logSize - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩ :=
      Fin.ext hkN
    rw [hk']
    exact hsafe
  have hnext := hnj hsafe
  have hpush : regsArr ⟨gpow (2 ^ prog.logSize), (f p).fp⟩ ∈ messagesOn w StatePush.toRaw := by
    rw [statePush_eq h.toB hf]
    refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, ?_⟩)
    rw [hnext, hfin, Program.finalPc, ← gpow_succ, Nat.sub_add_cancel hpos]
  have hpull := h.state_balanced.subset hpush
  rw [statePull_eq h.toB hf] at hpull
  rcases List.mem_cons.mp hpull with heq | heq
  · have h1 : gpow (2 ^ prog.logSize) = gpow (2 ^ prog.logSize - 1) :=
      (by simpa [regsArr, finalRegs, Program.finalPc] using heq : _ ∧ _).1
    have := gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega) h1
    omega
  · obtain ⟨q, hq, hqe⟩ := List.mem_map.mp heq
    obtain ⟨-, k', hk', -⟩ := opRecs_step h hf hq
    have h1 : gpow (2 ^ prog.logSize) = gpow k' := by
      rw [← hk']
      exact (by simpa [regsArr, RowRec.src] using hqe.symm : _ ∧ _).1
    have := gpow_injOn (by simp only [Set.mem_Iio]; omega)
      (by simp only [Set.mem_Iio]; have := k'.isLt; omega) h1
    have := k'.isLt
    omega

/-! ## The run -/

/-- **The walk of a satisfying witness**: records for its rows and a run of the Keccak VM from the initial to the
final registers over the image the data names, each of whose steps is a row. -/
theorem exists_walk (hsafe : SentinelSafe prog) (h : SatisfiedBy prog input w) :
    ∃ f, OpRecs w f ∧ ∃ n, KeccakVm.run prog (imageOf w.data).2 n Regs.initial = some (finalRegs prog) ∧
      ∀ k < n, ∃ p ∈ opPairs w, KeccakVm.run prog (imageOf w.data).2 k Regs.initial = some (f p).src ∧
        KeccakVm.run prog (imageOf w.data).2 (k + 1) Regs.initial = some (f p).next := by
  obtain ⟨f, hf⟩ := exists_opRecs w
  refine ⟨f, hf, ?_⟩
  have hb := h.state_balanced
  unfold BalancedPair at hb
  rw [statePush_eq h.toB hf, statePull_eq h.toB hf] at hb
  have hperm := hb.map arrRegs
  simp only [List.map_cons, List.map_map, Function.comp_def, arrRegs_regsArr] at hperm
  exact exists_run_of_perm (fun p ↦ (f p).src) (fun p ↦ (f p).next) (opPairs w)
    (fun p hp ↦ ⟨opRecs_pc_ne_finalPc hsafe h hf hp, (opRecs_step h hf hp).1⟩) Regs.initial
    hperm

/-! ## Constraint soundness -/

/-- The state after `k` steps of the run of `t`, the initial state if the run fails. -/
noncomputable def stateAt (t : KeccakVm.Trace prog) (k : ℕ) : Regs K :=
  (KeccakVm.run prog t.image k Regs.initial).getD Regs.initial

/-- A list all of whose entries map to `some` is the `filterMap` of the entries' values. -/
theorem filterMap_eq_map_of {α β : Type} (p : α → Option β) (f : α → β) (l : List α)
    (h : ∀ x ∈ l, p x = some (f x)) : l.filterMap p = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.filterMap_cons, h x List.mem_cons_self, List.map_cons, ih fun y hy ↦
      h y (List.mem_cons_of_mem _ hy)]

/-- The run to step `k ≤ steps` reaches `stateAt t k`. -/
theorem run_stateAt {t : KeccakVm.Trace prog}
    (hv : KeccakVm.run prog t.image t.steps Regs.initial = some (finalRegs prog)) {k : ℕ}
    (hk : k ≤ t.steps) : KeccakVm.run prog t.image k Regs.initial = some (stateAt t k) := by
  obtain ⟨r, hr, -⟩ := KeccakVm.run_prefix (m := k) (n := t.steps - k)
    (by rwa [Nat.add_sub_cancel' hk])
  simp [stateAt, hr]

/-- The register sequence of a valid run is the states `stateAt t 0, …, stateAt t steps`. -/
theorem regs_eq_map {t : KeccakVm.Trace prog}
    (hv : KeccakVm.run prog t.image t.steps Regs.initial = some (finalRegs prog)) :
    t.regs = (List.range (t.steps + 1)).map (stateAt t) := by
  unfold KeccakVm.Trace.regs
  exact filterMap_eq_map_of _ _ _ fun k hk ↦ by
    simp only [run_stateAt hv (Nat.lt_succ_iff.mp (List.mem_range.mp hk))]

/-- A row's messages on a channel are the sends with that channel's name. -/
theorem rowMessagesOn_eq_rowSends (t : Air.Flat.Table K) (row : Array K) (c : RawChannel K) :
    rowMessagesOn t row c =
      ((rowSends t.component (t.environment row)).filter (·.1 = c.name)).map (·.2) := by
  rw [rowMessagesOn, Operations.interactionValues, Component.interactions_eq]
  unfold rowSends
  generalize t.component.rowOperations.interactions.map
    (AbstractInteraction.eval (t.environment row)) = l
  induction l with
  | nil => rfl
  | cons i l ih => by_cases h : i.channel.name = c.name <;> simp [h, ih]

/-- **Constraint soundness, for the Keccak VM.** A witness satisfying the Keccak VM's constraint statement of a
program whose last instruction is not a `JUMP` represents a valid execution of the program on `input`. -/
theorem constraintSoundness {input : PublicInput} (hsafe : SentinelSafe prog)
    (h : SatisfiedBy prog input w) :
    ∃ t, AssignmentRepresents w t ∧ KeccakVm.ValidExecution prog input t := by
  obtain ⟨f, hf, n, hn, hsteps⟩ := exists_walk hsafe h
  let t : KeccakVm.Trace prog := ⟨(imageOf w.data).1, (imageOf w.data).2, n⟩
  have hv : KeccakVm.run prog t.image t.steps Regs.initial = some (finalRegs prog) := hn
  refine ⟨t, ⟨rfl, fun _ _ ↦ rfl, ?_⟩,
    ⟨h.caps.minLogMem_le, h.caps.le_maxLogMem, h.word0_eq, h.word1_eq⟩, hn⟩
  intro k hk
  have hlen : t.regs.length = n + 1 := KeccakVm.Trace.regs_length hv
  have e : ∀ j (hj : j < t.regs.length), t.regs[j] = stateAt t j := fun j hj ↦ by
    rw [List.getElem_of_eq (regs_eq_map hv) hj]
    simp
  obtain ⟨p, hp, h1, h2⟩ := hsteps k (by omega)
  have s1 : stateAt t k = (f p).src := by simp only [stateAt, t, h1, Option.getD_some]
  have s2 : stateAt t (k + 1) = (f p).next := by simp only [stateAt, t, h2, Option.getD_some]
  rw [e k (by omega), e (k + 1) hk, s1, s2]
  obtain ⟨ht, hrow⟩ := mem_opPairs hp
  refine ⟨p.1, List.mem_of_mem_take ht, p.2, hrow, ?_, ?_⟩
  · rw [rowMessagesOn_eq_rowSends, (hf p hp).1, RowRec.sends, Channel.toRaw_name,
      sendsOf_statePull]
    rfl
  · rw [rowMessagesOn_eq_rowSends, (hf p hp).1, RowRec.sends, Channel.toRaw_name,
      sendsOf_statePush]

end KeccakArith

end
