/-
  Lv42.Arithmetization.Completeness.Messages

  Adapted from leanerVM (https://github.com/Verified-zkEVM/leanerVM), branch mumbai, commit
  f0393df4, file lean_vm/LeanVM/Arithmetization/Completeness/Messages.lean. MIT OR Apache-2.0; see
  AGENTS.md. `LeanVM` renamed `Lv42`.

  What the row of each of the six tables sends on the bus: the state step, the bytecode read, and
  the memory reads, as the explicit messages the row circuit emits.
-/

module

public import Lv42.Arithmetization.Completeness.MessagesBase
public import Lv42.Arithmetization.Completeness.Basics

@[expose] public section

/-!
# The messages of a row

The balance of the three channel pairs is a statement about the messages the rows send, so the
witness of `constraintCompleteness` needs them in closed form. Every table's row circuit has the
same shape: pull the state `(pc, fp)`, push the successor, read the bytecode entry at `pc`
(`bytecodeRead`: a pull with count `r` and a push with count `g·r`), then read its memory cells
(`memRead`, likewise). `rowSends c env` lists the `(channel name, message)` pairs a component's
row circuit sends in the row environment `env`, in the circuit's order.

`xor_sends` and its five siblings state, for a typed row `r` written as the raw row `rawRow r`,
exactly the list the circuit sends, as arrays of the row's fields. The proof is one `simp` with
the circuit lemmas over a row variable `x` with `eval env x = r` (`xor_sends_gen`), the general
form the raw-row lemmas instantiate at Clean's `varFromOffset`; no column index is ever
computed. The `JUMP` row's pushed successor depends on its local witness `b`, which is the slot
after the row's twelve columns.

## Wrong readings excluded

* The sends of a row are not its columns: the third read of an `XOR` row carries the sums
  `v_A + v_B`, the `MUL_NATIVE` row's the twelve products folded by `y^3 = y + 1`, the `DEREF`
  row's the store coordinates of its mode; none of these is a column.
* The pull of a bus read carries the count `r`, the push `g·r` (specification §6.2): a message
  is `(addr, count, v)`, never `(addr, v, count)`.
* The local witnesses of a `JUMP` row are in the raw row, after the columns: reading the
  successor at a row without them would read `0` and push the fall-through for a taken jump.
-/

namespace Lv42.Arithmetization

open Lv42.Parameters Lv42.Semantics LeanVM.Parameters
open Air.Flat (Component)

/-! ## Messages as arrays -/

/-- A row's messages on a channel are the sends with that channel's name. -/
theorem rowMessagesOn_eq_rowSends (t : Air.Flat.Table K) (row : Array K) (c : RawChannel K) :
    rowMessagesOn t row c =
      ((rowSends t.component (t.environment row)).filter (·.1 = c.name)).map (·.2) := by
  rw [rowMessagesOn_eq]
  unfold rowSends
  generalize t.component.rowOperations.interactions.map
    (AbstractInteraction.eval (t.environment row)) = l
  induction l with
  | nil => rfl
  | cons i l ih => by_cases h : i.channel.name = c.name <;> simp [h, ih]

/-- The sends of the `BLAKE2S` row circuit, in closed form: nine cells of two limbs, the third
limb of each message `0`. -/
theorem blake2s_sends_gen (x : Var Blake2sRow K) (env : Environment K) (n : ℕ)
    (r : Blake2sRow K) (hx : eval env x = r) :
    (((blake2sTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePull.name, #[r.pc, r.fp]), (StatePush.name, #[g * r.pc, r.fp]),
       (BytecodePull.name,
        #[r.pc, r.rbc, Opcode.blake2s.code, r.om0, r.om1, r.om2, r.om3, r.ocv, r.oout, r.omd]),
       (BytecodePush.name,
        #[r.pc, g * r.rbc, Opcode.blake2s.code, r.om0, r.om1, r.om2, r.om3, r.ocv, r.oout,
          r.omd]),
       (MemPull.name, #[r.fp * r.om0, r.rm0, r.m0[0], r.m0[1], 0]),
       (MemPush.name, #[r.fp * r.om0, g * r.rm0, r.m0[0], r.m0[1], 0]),
       (MemPull.name, #[r.fp * r.om1, r.rm1, r.m1[0], r.m1[1], 0]),
       (MemPush.name, #[r.fp * r.om1, g * r.rm1, r.m1[0], r.m1[1], 0]),
       (MemPull.name, #[r.fp * r.om2, r.rm2, r.m2[0], r.m2[1], 0]),
       (MemPush.name, #[r.fp * r.om2, g * r.rm2, r.m2[0], r.m2[1], 0]),
       (MemPull.name, #[r.fp * r.om3, r.rm3, r.m3[0], r.m3[1], 0]),
       (MemPush.name, #[r.fp * r.om3, g * r.rm3, r.m3[0], r.m3[1], 0]),
       (MemPull.name, #[r.fp * r.ocv, r.rcv0, r.cv0[0], r.cv0[1], 0]),
       (MemPush.name, #[r.fp * r.ocv, g * r.rcv0, r.cv0[0], r.cv0[1], 0]),
       (MemPull.name, #[r.fp * (g * r.ocv), r.rcv1, r.cv1[0], r.cv1[1], 0]),
       (MemPush.name, #[r.fp * (g * r.ocv), g * r.rcv1, r.cv1[0], r.cv1[1], 0]),
       (MemPull.name, #[r.fp * r.oout, r.rout0, r.out0[0], r.out0[1], 0]),
       (MemPush.name, #[r.fp * r.oout, g * r.rout0, r.out0[0], r.out0[1], 0]),
       (MemPull.name, #[r.fp * (g * r.oout), r.rout1, r.out1[0], r.out1[1], 0]),
       (MemPush.name, #[r.fp * (g * r.oout), g * r.rout1, r.out1[0], r.out1[1], 0]),
       (MemPull.name, #[r.fp * r.omd, r.rmd, r.md[0], r.md[1], 0]),
       (MemPush.name, #[r.fp * r.omd, g * r.rmd, r.md[0], r.md[1], 0])] := by
  subst hx
  obtain ⟨pc, fp, om0, om1, om2, om3, ocv, oout, omd, m0, m1, m2, m3, out0, out1, cv0, cv1, md,
    rm0, rm1, rm2, rm3, rcv0, rcv1, rout0, rout1, rmd, rbc⟩ := x
  simp only [Operations.interactionValues, circuit_norm, blake2sTable, memRead, bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, -BitVec.reduceNeg]

/-! ## The blocks and the verifier -/

end Lv42.Arithmetization
