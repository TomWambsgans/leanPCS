-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The machine lemmas are `formal/Lv42`'s
-- `Semantics/Lemmas.lean` and `Arithmetization/Bytecode.lean` (leanerVM `mumbai` f0393df4, MIT OR Apache-2.0), at
-- the Keccak VM's `Program`, `step` and `run`.
module

public import KeccakVm.Isa
public import Lv42.Semantics.Lemmas

/-!
# The Keccak VM's machine: lemmas

The lemmas of Lv42's `Semantics/Lemmas.lean` about programs, steps and runs, for the Keccak VM's (`Program.fetch_gpow`,
`step_of_fetch_eq_some`, `run_add`, `Trace.regs`, …), and the bytecode entry's decoder (`decode`, the inverse of
`entry`: `decode_entry`, `entry_injective`), as Lv42's `Arithmetization/Bytecode.lean` has them for its instruction
set. Nothing here is about the hash: the proofs are Lv42's, at `KeccakVm`'s definitions.
-/

@[expose] public section

namespace KeccakVm

open LeanVM.Parameters
open Lv42.Semantics (Regs MemImage gLog? gLog?_spec gLog?_eq_none_iff DerefMode)
open Lv42.Arithmetization (derefFlags)

/-! ## Programs -/

theorem Program.logSize_lt (prog : Program) : prog.logSize < 64 :=
  lt_of_le_of_lt prog.logSize_le (by decide)

/-- Fetching at the address of index `i` gives instruction `i`. -/
theorem Program.fetch_gpow (prog : Program) (i : Fin (2 ^ prog.logSize)) :
    prog.fetch (gpow i) = some (prog.code i) := by
  rw [Program.fetch, (gLog?_spec prog.logSize_lt).mpr rfl, Option.map_some]

/-- A successful fetch is the instruction of the counter's index. -/
theorem Program.fetch_eq_some_iff (prog : Program) {pc : K} {ins : Instr} :
    prog.fetch pc = some ins ↔ ∃ i : Fin (2 ^ prog.logSize), pc = gpow i ∧ prog.code i = ins := by
  simp only [Program.fetch, Option.map_eq_some_iff, gLog?_spec prog.logSize_lt]

/-- A fetch fails exactly at the counters that are no power below `2 ^ logSize`. -/
theorem Program.fetch_eq_none_iff (prog : Program) {pc : K} :
    prog.fetch pc = none ↔ ∀ i : Fin (2 ^ prog.logSize), pc ≠ gpow i := by
  rw [Program.fetch, Option.map_eq_none_iff, gLog?_eq_none_iff]

/-! ## Steps -/

/-- A step from a counter that fetches `ins` executes `ins`. -/
theorem step_of_fetch_eq_some {κ : ℕ} {prog : Program} {L : MemImage κ} {r : Regs K}
    {ins : Instr} (h : prog.fetch r.pc = some ins) : step prog L r = execute L r ins := by
  rw [step, h]; rfl

/-- A step that fetches `ins` and reaches `next` executes `ins` to `next`. -/
theorem execute_of_step {κ : ℕ} {prog : Program} {L : MemImage κ} {r : Regs K} {ins : Instr}
    {next : Regs K} (hfetch : prog.fetch r.pc = some ins) (hstep : step prog L r = some next) :
    execute L r ins = some next := by
  rwa [step_of_fetch_eq_some hfetch] at hstep

/-! ## Runs -/

/-- The register sequence `r_0 = (1, 1), r_1, …, r_steps` of a trace; a prefix that fails to run is dropped. -/
noncomputable def Trace.regs {prog : Program} (t : Trace prog) : List (Regs K) :=
  (List.range (t.steps + 1)).filterMap fun n ↦ run prog t.image n Regs.initial

section

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

@[simp] theorem run_zero (r : Regs K) : run prog L 0 r = some r := rfl

theorem run_succ (n : ℕ) (r : Regs K) :
    run prog L (n + 1) r = if r.pc = prog.finalPc then none else step prog L r >>= run prog L n :=
  rfl

theorem run_succ_of_ne {r : Regs K} (h : r.pc ≠ prog.finalPc) (n : ℕ) :
    run prog L (n + 1) r = step prog L r >>= run prog L n := by
  rw [run_succ, ite_eq_right h]

theorem run_succ_of_eq {r : Regs K} (h : r.pc = prog.finalPc) (n : ℕ) :
    run prog L (n + 1) r = none := by
  rw [run_succ, ite_eq_left h]

theorem run_add (m n : ℕ) (r : Regs K) :
    run prog L (m + n) r = run prog L m r >>= run prog L n := by
  induction m generalizing r with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + n = m + n + 1 by omega, run_succ, run_succ]
    split_ifs
    · rfl
    · rw [bind_assoc]
      exact bind_congr fun r' ↦ ih r'

theorem run_prefix {m n : ℕ} {r r'' : Regs K} (h : run prog L (m + n) r = some r'') :
    ∃ r', run prog L m r = some r' ∧ run prog L n r' = some r'' := by
  rw [run_add] at h
  exact Option.bind_eq_some_iff.mp h

theorem pc_ne_finalPc_of_run_succ {n : ℕ} {r r' : Regs K} (h : run prog L (n + 1) r = some r') :
    r.pc ≠ prog.finalPc :=
  fun hpc ↦ by rw [run_succ_of_eq hpc] at h; exact Option.some_ne_none r' h.symm

theorem run_intermediate {n : ℕ} {r r' : Regs K} (h : run prog L n r = some r') {m : ℕ}
    (hm : m < n) : ∃ r₁, run prog L m r = some r₁ ∧ r₁.pc ≠ prog.finalPc := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + (k + 1) := ⟨n - m - 1, by omega⟩
  obtain ⟨r₁, h₁, h₂⟩ := run_prefix h
  exact ⟨r₁, h₁, pc_ne_finalPc_of_run_succ h₂⟩

end

/-- A trace that runs has `steps + 1` register states. -/
theorem Trace.regs_length {prog : Program} {t : Trace prog} {r : Regs K}
    (h : run prog t.image t.steps Regs.initial = some r) : t.regs.length = t.steps + 1 := by
  rw [Trace.regs]
  refine (List.filterMap_length_eq_length.mpr ?_).trans List.length_range
  intro n hn
  rcases Nat.lt_succ_iff_lt_or_eq.mp (List.mem_range.mp hn) with hlt | rfl
  · obtain ⟨r₁, h₁, -⟩ := run_intermediate h hlt
    simp [h₁]
  · simp [h]

/-! ## The bytecode entry's decoder -/

/-- The six codes are distinct. -/
theorem Opcode.code_injective : Function.Injective Opcode.code := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide +kernel)

/-- The store mode of a flag pair, if it is one of the three. -/
def derefMode? (fpc ffp : K) : Option DerefMode :=
  if fpc = 0 ∧ ffp = 0 then some .cell
  else if fpc = 1 ∧ ffp = 0 then some .pc
  else if fpc = 0 ∧ ffp = 1 then some .fp
  else none

/-- The opcode of a code, if it is one of the six. -/
def opcode? (a : K) : Option Opcode :=
  if a = Opcode.xor.code then some .xor
  else if a = Opcode.mulNative.code then some .mulNative
  else if a = Opcode.setConstant.code then some .setConstant
  else if a = Opcode.deref.code then some .deref
  else if a = Opcode.jump.code then some .jump
  else if a = Opcode.sha3.code then some .sha3
  else none

/-- Read an entry back as an instruction: the inverse of `entry` (`decode_entry`). -/
def decode (v : Vector K 8) : Option Instr :=
  match opcode? v[0] with
  | some .xor =>
      if v[4] = 0 ∧ v[5] = 0 ∧ v[6] = 0 ∧ v[7] = 0 then some (.xor v[1] v[2] v[3]) else none
  | some .mulNative =>
      if v[4] = 0 ∧ v[5] = 0 ∧ v[6] = 0 ∧ v[7] = 0 then some (.mulNative v[1] v[2] v[3])
      else none
  | some .setConstant =>
      if v[5] = 0 ∧ v[6] = 0 ∧ v[7] = 0 then some (.setConstant v[1] (E.ofLimbs v[2] v[3] v[4]))
      else none
  | some .deref =>
      match derefMode? v[4] v[5] with
      | some mode => if v[6] = 0 ∧ v[7] = 0 then some (.deref v[1] v[2] v[3] mode) else none
      | none => none
  | some .jump =>
      if v[4] = 0 ∧ v[5] = 0 ∧ v[6] = 0 ∧ v[7] = 0 then some (.jump v[1] v[2] v[3]) else none
  | some .sha3 => some (.sha3 ![v[1], v[2], v[3], v[4]] v[5] v[6] v[7])
  | none => none

private theorem vecCons_apply (om : Fin 4 → K) : ![om 0, om 1, om 2, om 3] = om := by
  funext i
  fin_cases i <;> rfl

theorem derefMode?_flags (m : DerefMode) :
    derefMode? (derefFlags m).1 (derefFlags m).2 = some m := by
  cases m <;> simp [derefMode?, derefFlags]

theorem opcode?_code (o : Opcode) : opcode? o.code = some o := by
  cases o <;> simp [opcode?, Opcode.code_injective.eq_iff]

/-- Lv42's five codes are the Keccak VM's. -/
theorem code_xor : Lv42.Parameters.Opcode.xor.code = Opcode.xor.code := rfl
theorem code_mul : Lv42.Parameters.Opcode.mulNative.code = Opcode.mulNative.code := rfl
theorem code_set : Lv42.Parameters.Opcode.setConstant.code = Opcode.setConstant.code := rfl
theorem code_deref : Lv42.Parameters.Opcode.deref.code = Opcode.deref.code := rfl
theorem code_jump : Lv42.Parameters.Opcode.jump.code = Opcode.jump.code := rfl

/-- Every instruction's entry decodes to it. -/
theorem decode_entry (i : Instr) : decode (entry i) = some i := by
  cases i with
  | sha3 om otail ocap oout =>
    have h := vecCons_apply om
    simp [decode, entry, opcode?_code, h]
  | _ =>
    simp only [entry, Lv42.Arithmetization.entry, code_xor, code_mul, code_set, code_deref, code_jump]
    simp [decode, opcode?_code, derefMode?_flags, ofLimbs_limb]

/-- Distinct instructions have distinct entries. -/
theorem entry_injective : Function.Injective entry := by
  intro i j h
  have hi := decode_entry i
  rw [h, decode_entry] at hi
  exact (Option.some.inj hi).symm

end KeccakVm

end
