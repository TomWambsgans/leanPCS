/-
  Lv42.Arithmetization.Completeness.MessagesBase

  Adapted from leanerVM (https://github.com/Verified-zkEVM/leanerVM), branch mumbai, commit
  f0393df4, file lean_vm/LeanVM/Arithmetization/Completeness/Messages.lean. MIT OR Apache-2.0; see
  AGENTS.md. `LeanVM` renamed `Lv42`.

  What the row of each of the six tables sends on the bus: the state step, the bytecode read, and
  the memory reads, as the explicit messages the row circuit emits.

  This module is its instruction-set-independent part (shared by the Keccak VM), with
  every name kept; the BLAKE2s-specific rest (the module without `Base`) is removed with `BLAKE2S`.
-/

module

public import Lv42.Arithmetization.Completeness.BasicsBase

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

/-- A vector of three is the list of its entries. -/
theorem vec3_toList {F : Type} (v : Vector F 3) : v.toList = [v[0], v[1], v[2]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have : i < 3 := by simpa using h1
  interval_cases i <;> simp

/-- A vector of seven is the list of its entries. -/
theorem vec7_toList {F : Type} (v : Vector F 7) :
    v.toList = [v[0], v[1], v[2], v[3], v[4], v[5], v[6]] := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have : i < 7 := by simpa using h1
  interval_cases i <;> simp

/-- A state message flattens to the array `[pc, fp]`, over any type of coordinates. -/
theorem regs_toArray {F : Type} (s : Regs F) : (toElements s).toArray = #[s.pc, s.fp] := by
  obtain ⟨pc, fp⟩ := s
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]

/-- A memory message flattens to the array `[addr, count, v₀, v₁, v₂]`. -/
theorem memMsg_toArray {F : Type} (m : MemMsg F) :
    (toElements m).toArray = #[m.addr, m.count, m.v[0], m.v[1], m.v[2]] := by
  obtain ⟨addr, count, v⟩ := m
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray, Vector.toList_append, Vector.toList_append, vec3_toList]
  rfl

/-- A bytecode message flattens to the array `[pc, count, opcode, op₀, …, op₆]`. -/
theorem bytecodeMsg_toArray {F : Type} (b : BytecodeMsg F) :
    (toElements b).toArray =
      #[b.pc, b.count, b.opcode, b.op[0], b.op[1], b.op[2], b.op[3], b.op[4], b.op[5], b.op[6]] := by
  obtain ⟨pc, count, opcode, op⟩ := b
  simp [circuit_norm, explicit_provable_type, ProvableStruct.toComponents]
  apply Array.toList_inj.mp
  rw [Vector.toList_toArray, Vector.toList_append, Vector.toList_append, Vector.toList_append,
    vec7_toList]
  rfl

/-! ## A row's sends -/

/-- The `(channel name, message)` pairs a component's row circuit sends in the row environment
`env`, in the circuit's order. -/
def rowSends (c : Component K) (env : Environment K) : List (String × Array K) :=
  (c.rowOperations.interactions.map (AbstractInteraction.eval env)).map
    fun i ↦ (i.channel.name, i.msg)

/-- The raw row of a `JUMP` row: its twelve columns, then the local witnesses `w` (the inverse of
the condition) and `b` (its indicator). -/
def jumpRaw (r : JumpRow K) (w b : K) : Array K := rawRow r ++ #[w, b]

/-- Reading the row's variable at any environment whose first cells are the row, and whatever
follows, gives back the row. -/
theorem eval_rowVar_append {Row : TypeMap} [ProvableType Row] (r : Row K) (extra : Array K)
    (data : ProverData K) :
    eval (Environment.fromArray (rawRow r ++ extra) data) (varFromOffset Row 0 : Var Row K) =
      r := by
  rw [eval_varFromOffset_valueFromOffset]
  unfold valueFromOffset
  convert ProvableType.fromElements_toElements r
  refine Vector.ext fun i hi ↦ ?_
  rw [Vector.getElem_mapRange]
  show (((rawRow r ++ extra)[0 + i]?).getD 0) = _
  rw [Nat.zero_add, Array.getElem?_append_left (by rw [rawRow_size]; simpa using hi)]
  show ((toElements r).toArray[i]?).getD 0 = _
  rw [Array.getElem?_eq_getElem (by simpa using hi), Option.getD_some, Vector.getElem_toArray]

/-- The row variable of a raw row evaluates to the row. -/
theorem eval_rowVar {Row : TypeMap} [ProvableType Row] (r : Row K) (data : ProverData K) :
    eval (Environment.fromArray (rawRow r) data) (varFromOffset Row 0 : Var Row K) = r := by
  simpa only [Array.append_empty] using eval_rowVar_append r #[] data

/-! ## The six tables -/

/-- The sends of a row circuit at a row variable that evaluates to `r`: the circuit's interactions
as the arrays of `r`'s fields. -/
theorem xor_sends_gen (x : Var XorRow K) (env : Environment K) (n : ℕ) (r : XorRow K)
    (hx : eval env x = r) :
    (((xorTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePull.name, #[r.pc, r.fp]), (StatePush.name, #[g * r.pc, r.fp]),
       (BytecodePull.name, #[r.pc, r.rbc, Opcode.xor.code, r.oA, r.oB, r.oC, 0, 0, 0, 0]),
       (BytecodePush.name, #[r.pc, g * r.rbc, Opcode.xor.code, r.oA, r.oB, r.oC, 0, 0, 0, 0]),
       (MemPull.name, #[r.fp * r.oA, r.rA, r.vA[0], r.vA[1], r.vA[2]]),
       (MemPush.name, #[r.fp * r.oA, g * r.rA, r.vA[0], r.vA[1], r.vA[2]]),
       (MemPull.name, #[r.fp * r.oB, r.rB, r.vB[0], r.vB[1], r.vB[2]]),
       (MemPush.name, #[r.fp * r.oB, g * r.rB, r.vB[0], r.vB[1], r.vB[2]]),
       (MemPull.name,
        #[r.fp * r.oC, r.rC, r.vA[0] + r.vB[0], r.vA[1] + r.vB[1], r.vA[2] + r.vB[2]]),
       (MemPush.name,
        #[r.fp * r.oC, g * r.rC, r.vA[0] + r.vB[0], r.vA[1] + r.vB[1], r.vA[2] + r.vB[2]])] := by
  subst hx
  obtain ⟨pc, fp, oA, oB, oC, vA, vB, rA, rB, rC, rbc⟩ := x
  simp only [Operations.interactionValues, circuit_norm, xorTable, memRead, bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, -BitVec.reduceNeg]

/-- The sends of the `MUL_NATIVE` row circuit, in closed form. -/
theorem mul_sends_gen (x : Var MulRow K) (env : Environment K) (n : ℕ) (r : MulRow K)
    (hx : eval env x = r) :
    (((mulTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePull.name, #[r.pc, r.fp]), (StatePush.name, #[g * r.pc, r.fp]),
       (BytecodePull.name,
        #[r.pc, r.rbc, Opcode.mulNative.code, r.oA, r.oB, r.oC, 0, 0, 0, 0]),
       (BytecodePush.name,
        #[r.pc, g * r.rbc, Opcode.mulNative.code, r.oA, r.oB, r.oC, 0, 0, 0, 0]),
       (MemPull.name, #[r.fp * r.oA, r.rA, r.vA[0], r.vA[1], r.vA[2]]),
       (MemPush.name, #[r.fp * r.oA, g * r.rA, r.vA[0], r.vA[1], r.vA[2]]),
       (MemPull.name, #[r.fp * r.oB, r.rB, r.vB[0], r.vB[1], r.vB[2]]),
       (MemPush.name, #[r.fp * r.oB, g * r.rB, r.vB[0], r.vB[1], r.vB[2]]),
       (MemPull.name, #[r.fp * r.oC, r.rC,
          r.vA[0] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1],
          r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1] +
            r.vA[2] * r.vB[2],
          r.vA[0] * r.vB[2] + r.vA[1] * r.vB[1] + r.vA[2] * r.vB[0] + r.vA[2] * r.vB[2]]),
       (MemPush.name, #[r.fp * r.oC, g * r.rC,
          r.vA[0] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1],
          r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1] +
            r.vA[2] * r.vB[2],
          r.vA[0] * r.vB[2] + r.vA[1] * r.vB[1] + r.vA[2] * r.vB[0] + r.vA[2] * r.vB[2]])] := by
  subst hx
  obtain ⟨pc, fp, oA, oB, oC, vA, vB, rA, rB, rC, rbc⟩ := x
  simp only [Operations.interactionValues, circuit_norm, mulTable, memRead, bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, -BitVec.reduceNeg]

/-- The sends of the `SET_CONSTANT` row circuit, in closed form. -/
theorem set_sends_gen (x : Var SetRow K) (env : Environment K) (n : ℕ) (r : SetRow K)
    (hx : eval env x = r) :
    (((setTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePull.name, #[r.pc, r.fp]), (StatePush.name, #[g * r.pc, r.fp]),
       (BytecodePull.name,
        #[r.pc, r.rbc, Opcode.setConstant.code, r.o, r.k[0], r.k[1], r.k[2], 0, 0, 0]),
       (BytecodePush.name,
        #[r.pc, g * r.rbc, Opcode.setConstant.code, r.o, r.k[0], r.k[1], r.k[2], 0, 0, 0]),
       (MemPull.name, #[r.fp * r.o, r.r, r.k[0], r.k[1], r.k[2]]),
       (MemPush.name, #[r.fp * r.o, g * r.r, r.k[0], r.k[1], r.k[2]])] := by
  subst hx
  obtain ⟨pc, fp, o, k, r, rbc⟩ := x
  simp only [Operations.interactionValues, circuit_norm, setTable, memRead, bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, -BitVec.reduceNeg]

/-- The sends of the `DEREF` row circuit, in closed form. -/
theorem deref_sends_gen (x : Var DerefRow K) (env : Environment K) (n : ℕ) (r : DerefRow K)
    (hx : eval env x = r) :
    (((derefTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePull.name, #[r.pc, r.fp]), (StatePush.name, #[g * r.pc, r.fp]),
       (BytecodePull.name,
        #[r.pc, r.rbc, Opcode.deref.code, r.o1, r.o2, r.o3, r.fpc, r.ffp, 0, 0]),
       (BytecodePush.name,
        #[r.pc, g * r.rbc, Opcode.deref.code, r.o1, r.o2, r.o3, r.fpc, r.ffp, 0, 0]),
       (MemPull.name, #[r.fp * r.o1, r.r1, r.p, 0, 0]),
       (MemPush.name, #[r.fp * r.o1, g * r.r1, r.p, 0, 0]),
       (MemPull.name, #[r.p * r.o2, r.r2,
          (1 + r.fpc + r.ffp) * r.v3[0] + r.fpc * (g ^ 2 * r.pc) + r.ffp * r.fp,
          (1 + r.fpc + r.ffp) * r.v3[1], (1 + r.fpc + r.ffp) * r.v3[2]]),
       (MemPush.name, #[r.p * r.o2, g * r.r2,
          (1 + r.fpc + r.ffp) * r.v3[0] + r.fpc * (g ^ 2 * r.pc) + r.ffp * r.fp,
          (1 + r.fpc + r.ffp) * r.v3[1], (1 + r.fpc + r.ffp) * r.v3[2]]),
       (MemPull.name, #[r.fp * r.o3, r.r3, r.v3[0], r.v3[1], r.v3[2]]),
       (MemPush.name, #[r.fp * r.o3, g * r.r3, r.v3[0], r.v3[1], r.v3[2]])] := by
  subst hx
  obtain ⟨pc, fp, o1, o2, o3, fpc, ffp, p, v3, r1, r2, r3, rbc⟩ := x
  simp only [Operations.interactionValues, circuit_norm, derefTable, memRead, bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, -BitVec.reduceNeg]

/-- The sends of the `JUMP` row circuit, in closed form: the pushed successor reads the indicator
`b`, the local witness at slot `n + 1`. -/
theorem jump_sends_gen (x : Var JumpRow K) (env : Environment K) (n : ℕ) (r : JumpRow K)
    (hx : eval env x = r) (b : K) (hb : env.get (n + 1) = b) :
    (((jumpTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(StatePull.name, #[r.pc, r.fp]),
       (StatePush.name, #[b * r.vpc + b * (g * r.pc) + g * r.pc, b * r.vfp + b * r.fp + r.fp]),
       (BytecodePull.name, #[r.pc, r.rbc, Opcode.jump.code, r.oc, r.od, r.of, 0, 0, 0, 0]),
       (BytecodePush.name, #[r.pc, g * r.rbc, Opcode.jump.code, r.oc, r.od, r.of, 0, 0, 0, 0]),
       (MemPull.name, #[r.fp * r.oc, r.rc, r.vcond, 0, 0]),
       (MemPush.name, #[r.fp * r.oc, g * r.rc, r.vcond, 0, 0]),
       (MemPull.name, #[r.fp * r.od, r.rd, r.vpc, 0, 0]),
       (MemPush.name, #[r.fp * r.od, g * r.rd, r.vpc, 0, 0]),
       (MemPull.name, #[r.fp * r.of, r.rf, r.vfp, 0, 0]),
       (MemPush.name, #[r.fp * r.of, g * r.rf, r.vfp, 0, 0])] := by
  subst hx
  obtain ⟨pc, fp, oc, od, of, vcond, vpc, vfp, rc, rd, rf, rbc⟩ := x
  dsimp only [jumpTable]
  simp only [Operations.interactionValues, circuit_norm, memRead, bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, hb, -BitVec.reduceNeg]

/-- The sends of the memory block's row circuit: the seed push `(idx, 1, m)` and the finalize pull
`(idx, cntFin, m)`. -/
theorem mem_sends_gen (x : Var MemRow K) (env : Environment K) (n : ℕ) (r : MemRow K)
    (hx : eval env x = r) :
    (((memTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(MemPush.name, #[r.idx, 1, r.m[0], r.m[1], r.m[2]]),
       (MemPull.name, #[r.idx, r.cntFin, r.m[0], r.m[1], r.m[2]])] := by
  subst hx
  obtain ⟨idx, cntFin, m⟩ := x
  simp only [Operations.interactionValues, circuit_norm, memTable, AbstractInteraction.eval,
    Vector.toArray_map, memMsg_toArray, -BitVec.reduceNeg]

/-- The sends of the bytecode block's row circuit: the seed push `(idx, 1, entry)` and the
finalize pull `(idx, cntFin, entry)`. -/
theorem bytecode_sends_gen (x : Var BytecodeRow K) (env : Environment K) (n : ℕ)
    (r : BytecodeRow K) (hx : eval env x = r) :
    (((bytecodeTable.main x).operations n).interactionValues env).map
      (fun i ↦ (i.channel.name, i.msg)) =
      [(BytecodePush.name,
        #[r.idx, 1, r.opcode, r.op[0], r.op[1], r.op[2], r.op[3], r.op[4], r.op[5], r.op[6]]),
       (BytecodePull.name,
        #[r.idx, r.cntFin, r.opcode, r.op[0], r.op[1], r.op[2], r.op[3], r.op[4], r.op[5],
          r.op[6]])] := by
  subst hx
  obtain ⟨idx, cntFin, opcode, op⟩ := x
  simp only [Operations.interactionValues, circuit_norm, bytecodeTable, AbstractInteraction.eval,
    Vector.toArray_map, bytecodeMsg_toArray, -BitVec.reduceNeg]

/-- The sends of the verifier: the push of the initial state and the pull of the final one, in
every environment. -/
theorem verifier_sends (prog : Program) (env : Environment K) :
    rowSends ⟨leanIsaVerifier prog⟩ env =
      [(StatePush.name, #[1, 1]), (StatePull.name, #[prog.finalPc, 1])] := by
  unfold rowSends
  simp only [Component.rowOperations_mk, circuit_norm, leanIsaVerifier, AbstractInteraction.eval,
    Vector.toArray_map, regs_toArray, -BitVec.reduceNeg]

end Lv42.Arithmetization
