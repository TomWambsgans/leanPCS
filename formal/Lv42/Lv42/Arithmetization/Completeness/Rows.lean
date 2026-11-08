/-
  Lv42.Arithmetization.Completeness.Rows

  Adapted from leanerVM (https://github.com/Verified-zkEVM/leanerVM), branch mumbai, commit
  f0393df4, file lean_vm/LeanVM/Arithmetization/Completeness/Rows.lean. MIT OR Apache-2.0; see
  NOTICE.md. `LeanVM` renamed `Lv42`.

  The row of an instruction executed at a state: the table it belongs to, the raw row, and what
  it sends on the bus as a function of the state, the successor and the read counts.
-/

module

public import Lv42.Arithmetization.Completeness.RowsBase
public import Lv42.Arithmetization.Completeness.Messages

@[expose] public section

/-!
# The row of an executed instruction

The witness of `constraintCompleteness` writes one row per executed state, in the table of the
opcode the program holds there. `rowOf mem pc fp cnt rbc ins` is that row for the instruction `ins`
executed from `(pc, fp)` over the image `mem`: the typed row of `Arithmetization.Tables`
(`xorRowOf` and its siblings, with the `JUMP` table's honest local witnesses appended), as a raw
row. Its memory reads carry the counts `cnt 0, cnt 1, …` in the order the circuit reads them, and
its bytecode read the count `rbc`.

`sendsOf` is what any such row sends, in the shape every table shares (`Completeness.Messages`):
the state pull and push, the bytecode pull and push of `entry ins` at `pc`, and per read a
memory pull of `(addr, count, v)` and a push of `(addr, g·count, v)`. `readAddrs` lists the
cells an instruction reads, and the memory reads of the row are those cells with the limbs the
image holds there. The master lemma `rowOf_sends` says that if the instruction executes
from `(pc, fp)` to `next` then the row sends exactly `sendsOf` with `next`, and
`readAddrs_valid` that every cell it reads is an address of the image. Both are per table,
from the table's relation (`*_refines_iff`) and the closed forms of `Completeness.Messages`.

## Wrong readings excluded

* The messages carry the limbs the image holds, not the row's own formulas: the third read of an
  `XOR` row carries `v_A + v_B`, and that this is the word at `fp·o_C` is the execution's
  (`xor_refines_iff`), never the row's. A row for an instruction that does not execute sends
  something else, and the bus rejects it.
* The `DEREF` target cell is `p·o_2` for the pointer `p` the image holds at `fp·o_1`, not
  `fp·o_2`: its address is the one read that depends on another.
-/

namespace Lv42.Arithmetization

open Lv42.Parameters Lv42.Semantics LeanVM.Parameters
open Air.Flat (Component)

/-! ## Reading a word back as limbs -/

/-- The cells an instruction reads, in the order its row's reads carry them (the circuits'
order): the operand cells, and for `DEREF` the pointer cell `fp·o₁`, the pointer's target `p·o₂`
(`p` the low limb of the word at `fp·o₁`) and the local cell `fp·o₃`. -/
noncomputable def readAddrs {κ : ℕ} (mem : MemImage κ) (fp : K) : Instr → List K
  | .xor oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .mulNative oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .setConstant o _ => [fp * o]
  | .deref o1 o2 o3 _ => [fp * o1, (mem.limbsAt (fp * o1))[0] * o2, fp * o3]
  | .jump oc od of => [fp * oc, fp * od, fp * of]
  | .blake2s om ocv oout omd =>
      [fp * om 0, fp * om 1, fp * om 2, fp * om 3, fp * ocv, fp * (g * ocv), fp * oout,
        fp * (g * oout), fp * omd]

/-- The reads of an instruction's row: each cell it reads, with its count (`cnt` at its position)
and the limbs the image holds there. -/
noncomputable def readsOf {κ : ℕ} (mem : MemImage κ) (fp : K) (cnt : ℕ → K) (ins : Instr) :
    List (K × K × Vector K 3) :=
  (readAddrs mem fp ins).mapIdx fun j a ↦ (a, cnt j, mem.limbsAt a)

/-! ## The six instructions -/

/-- The `BLAKE2S` row of an execution sends the `BLAKE2S` messages: each of the nine cells
carries its two limbs and a zero third limb, the canonical form the execution checks. -/
theorem blake2s_exec_sends {κ : ℕ} {mem : MemImage κ}
    {pc fp om0 om1 om2 om3 ocv oout omd : K} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ (.blake2s ![om0, om1, om2, om3] ocv oout omd) = some next)
    (rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc : K) (data : ProverData K) :
    rowSends ⟨blake2sTable⟩
        (Environment.fromArray (rawRow (blake2sRowOf mem pc fp om0 om1 om2 om3 ocv oout omd
          rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc)) data) =
      sendsOf pc fp next rbc (entry (.blake2s ![om0, om1, om2, om3] ocv oout omd))
        [(fp * om0, rm0, mem.limbsAt (fp * om0)), (fp * om1, rm1, mem.limbsAt (fp * om1)),
          (fp * om2, rm2, mem.limbsAt (fp * om2)), (fp * om3, rm3, mem.limbsAt (fp * om3)),
          (fp * ocv, rcv0, mem.limbsAt (fp * ocv)),
          (fp * (g * ocv), rcv1, mem.limbsAt (fp * (g * ocv))),
          (fp * oout, rout0, mem.limbsAt (fp * oout)),
          (fp * (g * oout), rout1, mem.limbsAt (fp * (g * oout))),
          (fp * omd, rmd, mem.limbsAt (fp * omd))] := by
  obtain ⟨⟨hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩, -, rfl⟩ :=
    (blake2s_refines_iff _ _ _).mp
      (blake2sRowOf_refines hexec rm0 rm1 rm2 rm3 rcv0 rcv1 rout0 rout1 rmd rbc)
  rw [rowSends_mk, blake2s_sends_gen _ _ _ _ (eval_rowVar _ data)]
  simp only [blake2sRowOf] at hm0 hm1 hm2 hm3 hcv0 hcv1 hout0 hout1 hmd ⊢
  simp [sendsOf, bcMsgOf, entry, Regs.next, memMsgOf_cell hm0, memMsgOf_cell hm1,
    memMsgOf_cell hm2, memMsgOf_cell hm3, memMsgOf_cell hcv0, memMsgOf_cell hcv1,
    memMsgOf_cell hout0, memMsgOf_cell hout1, memMsgOf_cell hmd]

/-! ## Every cell an instruction reads is an address -/

/-- Every cell an executing instruction reads is an address of the image: the execution reads it
(`*_refines_iff`, the bindings and the result cell). -/
theorem readAddrs_valid {κ : ℕ} {mem : MemImage κ} {pc fp : K} {ins : Instr} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ ins = some next) :
    ∀ a ∈ readAddrs mem fp ins, ∃ w, mem.read a = some w := by
  cases ins with
  | xor oA oB oC =>
    obtain ⟨⟨hA, hB⟩, hC, -⟩ := (xor_refines_iff _ _ _).mp (xorRowOf_refines hexec 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl)
    exacts [⟨_, hA⟩, ⟨_, hB⟩, ⟨_, hC⟩]
  | mulNative oA oB oC =>
    obtain ⟨⟨hA, hB⟩, hC, -⟩ := (mul_refines_iff _ _ _).mp (mulRowOf_refines hexec 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl)
    exacts [⟨_, hA⟩, ⟨_, hB⟩, ⟨_, hC⟩]
  | setConstant o k =>
    obtain ⟨hk, -⟩ := (set_refines_iff _ _ _).mp (setRowOf_refines hexec 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a rfl
    exact ⟨_, hk⟩
  | deref o1 o2 o3 mode =>
    obtain ⟨mode', ⟨-, h1, h3⟩, h2, -⟩ :=
      (deref_refines_iff _ _ _).mp (derefRowOf_refines hexec 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl)
    exacts [⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩]
  | jump oc od of =>
    obtain ⟨⟨hc, hd, hf⟩, -⟩ := (jump_refines_iff _ _ _).mp (jumpRowOf_refines hexec 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl)
    exacts [⟨_, hc⟩, ⟨_, hd⟩, ⟨_, hf⟩]
  | blake2s om ocv oout omd =>
    have hom : om = ![om 0, om 1, om 2, om 3] := by funext i; fin_cases i <;> rfl
    rw [hom] at hexec
    obtain ⟨⟨hm0, hm1, hm2, hm3, hcv0, hcv1, hout0, hout1, hmd⟩, -, -⟩ :=
      (blake2s_refines_iff _ _ _).mp (blake2sRowOf_refines hexec 1 1 1 1 1 1 1 1 1 1)
    simp only [readAddrs, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨_, hm0⟩, ⟨_, hm1⟩, ⟨_, hm2⟩, ⟨_, hm3⟩, ⟨_, hcv0⟩, ⟨_, hcv1⟩, ⟨_, hout0⟩,
      ⟨_, hout1⟩, ⟨_, hmd⟩]

/-! ## The row of an instruction -/

/-- The table of each opcode, in the ensemble's order (`leanIsaEnsemble`). -/
def opComponent : Opcode → Component K
  | .xor => ⟨xorTable⟩
  | .mulNative => ⟨mulTable⟩
  | .setConstant => ⟨setTable⟩
  | .deref => ⟨derefTable⟩
  | .jump => ⟨jumpTable⟩
  | .blake2s => ⟨blake2sTable⟩

/-- The width of a raw row of each opcode's table: the row's columns, and for `JUMP` its two
local witnesses. -/
def opWidth : Opcode → ℕ
  | .xor => size XorRow
  | .mulNative => size MulRow
  | .setConstant => size SetRow
  | .deref => size DerefRow
  | .jump => size JumpRow + 2
  | .blake2s => size Blake2sRow

/-- The raw row of an instruction executed from `(pc, fp)` over the image `mem`: the typed row of
its table with the read counts `cnt` (positionally, in the order the circuit reads) and the
bytecode count `rbc`, and for `JUMP` the honest inverse and indicator of the condition. -/
noncomputable def rowOf {κ : ℕ} (mem : MemImage κ) (pc fp : K) (cnt : ℕ → K) (rbc : K) :
    Instr → Array K
  | .xor oA oB oC => rawRow (xorRowOf mem pc fp oA oB oC (cnt 0) (cnt 1) (cnt 2) rbc)
  | .mulNative oA oB oC => rawRow (mulRowOf mem pc fp oA oB oC (cnt 0) (cnt 1) (cnt 2) rbc)
  | .setConstant o k => rawRow (setRowOf pc fp o k (cnt 0) rbc)
  | .deref o1 o2 o3 mode =>
      rawRow (derefRowOf mem pc fp o1 o2 o3 mode (cnt 0) (cnt 1) (cnt 2) rbc)
  | .jump oc od of =>
      jumpRaw (jumpRowOf mem pc fp oc od of (cnt 0) (cnt 1) (cnt 2) rbc)
        (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else ((mem.limbsAt (fp * oc))[0])⁻¹)
        (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else 1)
  | .blake2s om ocv oout omd =>
      rawRow (blake2sRowOf mem pc fp (om 0) (om 1) (om 2) (om 3) ocv oout omd
        (cnt 0) (cnt 1) (cnt 2) (cnt 3) (cnt 4) (cnt 5) (cnt 6) (cnt 7) (cnt 8) rbc)

/-- The raw row of an instruction has the width of its table. -/
theorem rowOf_size {κ : ℕ} (mem : MemImage κ) (pc fp : K) (cnt : ℕ → K) (rbc : K) (ins : Instr) :
    (rowOf mem pc fp cnt rbc ins).size = opWidth ins.opcode := by
  cases ins <;> simp [rowOf, opWidth, Instr.opcode, rawRow_size, jumpRaw]

/-- **The row of an executing instruction sends `sendsOf`.** If the instruction executes from
`(pc, fp)` to `next`, its row, in its table, sends the state step from `(pc, fp)` to `next`, the
bytecode read of its entry at `pc`, and the reads of the cells it reads with the counts `cnt`. -/
theorem rowOf_sends {κ : ℕ} {mem : MemImage κ} {pc fp : K} {ins : Instr} {next : Regs K}
    (hexec : execute mem ⟨pc, fp⟩ ins = some next) (cnt : ℕ → K) (rbc : K)
    (data : ProverData K) :
    rowSends (opComponent ins.opcode)
        (Environment.fromArray (rowOf mem pc fp cnt rbc ins) data) =
      sendsOf pc fp next rbc (entry ins) (readsOf mem fp cnt ins) := by
  cases ins with
  | xor oA oB oC =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, xor_exec_sends hexec]
    simp [readsOf, readAddrs]
  | mulNative oA oB oC =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, mul_exec_sends hexec]
    simp [readsOf, readAddrs]
  | setConstant o k =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, set_exec_sends hexec]
    simp [readsOf, readAddrs]
  | deref o1 o2 o3 mode =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, deref_exec_sends hexec]
    simp [readsOf, readAddrs]
  | jump oc od of =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, jump_exec_sends hexec]
    simp [readsOf, readAddrs]
  | blake2s om ocv oout omd =>
    have hom : om = ![om 0, om 1, om 2, om 3] := by funext i; fin_cases i <;> rfl
    have h := blake2s_exec_sends (hom ▸ hexec) (cnt 0) (cnt 1) (cnt 2) (cnt 3) (cnt 4) (cnt 5)
      (cnt 6) (cnt 7) (cnt 8) rbc data
    rw [← hom] at h
    simp only [Instr.opcode, opComponent]
    rw [rowOf, h]
    simp [readsOf, readAddrs]

end Lv42.Arithmetization
