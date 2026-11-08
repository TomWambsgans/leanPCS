-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The shape of `formal/Lv42`'s
-- `Arithmetization/Soundness/Rows.lean` (leanerVM `mumbai` f0393df4, MIT OR Apache-2.0), for the Keccak VM.
module

public import KeccakArith.RowSound
public import Lv42.Arithmetization.Soundness.Rows

/-!
# The rows of the Keccak VM's six opcode tables

What Lv42's soundness needs of each opcode table's rows (`Lv42.Arithmetization.OpRow`), for the Keccak VM:
`KOpRow c env` says the row sends the messages of a record (`RowRec`, Lv42's: the state pull and push, the bytecode
pull and push of the entry `e`, and per memory read a pull and a push), with at most 26 reads, and under the table's
assumptions, constraints and pull guarantees it is a step of the Keccak VM: an instruction `ins` with
`KeccakVm.entry ins = e` executes (`KeccakVm.execute`) from the pulled state to the pushed one, to the fall-through
unless it is a `JUMP`.

* `sha3_sends_gen`: the `SHA3` row circuit's sends in closed form, `sendsOf` with the 26 reads `sha3Reads`.
* `sha3_opRow`: a `SHA3` row is a `KOpRow`, its step `sha3_row_sound`.
* `xor_kOpRow`, `mul_kOpRow`, `set_kOpRow`, `deref_kOpRow`, `jump_kOpRow`: the five shared tables, from Lv42's
  closed forms and `*_refines_iff`; their instructions execute identically in the Keccak VM (`executeWith_base`).
* `sha3_channelOk`: every interaction of the `SHA3` table is on one of the six channels.
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Parameters Lv42.Semantics Lv42.Arithmetization KeccakVm
open Air.Flat (Component)

/-- A Keccak-VM opcode-table row: it sends a record's messages, reads at most 26 cells, and under its table's
assumptions, constraints and pull guarantees it is a step of the Keccak VM. -/
def KOpRow (c : Component K) (env : Environment K) : Prop :=
  ∃ x : RowRec, rowSends c env = x.sends ∧ x.reads.length ≤ 26 ∧
    (c.Assumptions env → c.operations.ConstraintsHold env → c.operations.FullGuarantees env →
      ∃ ins : KeccakVm.Instr, x.e = KeccakVm.entry ins ∧
        KeccakVm.execute (imageOf env.data).2 x.src ins = some x.next ∧
        (ins.opcode ≠ .jump → x.next = ⟨g * x.pc, x.fp⟩))

/-! ## The `SHA3` row -/

/-- The address of input cell `c` over a row's values, as `inAddrE` writes it. -/
def kInAddr (r : Sha3Row K) (c : ℕ) : K :=
  if h : c < 4 then r.fp * r.om[c]
  else if c < 8 then g ^ (c - 4) * (r.fp * r.otail)
  else g ^ (c - 8) * (r.fp * r.ocap)

/-- `kInAddr` is the executor's address. -/
theorem kInAddr_eq (r : Sha3Row K) (c : Fin 13) :
    kInAddr r c = r.fp * sha3InOffset r.omF r.otail r.ocap c := by
  unfold kInAddr sha3InOffset Sha3Row.omF
  split_ifs <;> (try simp only [Vector.get, Fin.val_cast, Vector.getElem_toArray]) <;> ring_nf

/-- The 26 reads of a `SHA3` row: the 13 input cells, then the 13 output cells, each `(address, count, limbs)`. -/
def sha3Reads (r : Sha3Row K) : List (K × K × Vector K 3) :=
  [(kInAddr r 0, r.cnt[0], cellLimbs r.inLane 0),
    (kInAddr r 1, r.cnt[1], cellLimbs r.inLane 1),
    (kInAddr r 2, r.cnt[2], cellLimbs r.inLane 2),
    (kInAddr r 3, r.cnt[3], cellLimbs r.inLane 3),
    (kInAddr r 4, r.cnt[4], cellLimbs r.inLane 4),
    (kInAddr r 5, r.cnt[5], cellLimbs r.inLane 5),
    (kInAddr r 6, r.cnt[6], cellLimbs r.inLane 6),
    (kInAddr r 7, r.cnt[7], cellLimbs r.inLane 7),
    (kInAddr r 8, r.cnt[8], cellLimbs r.inLane 8),
    (kInAddr r 9, r.cnt[9], cellLimbs r.inLane 9),
    (kInAddr r 10, r.cnt[10], cellLimbs r.inLane 10),
    (kInAddr r 11, r.cnt[11], cellLimbs r.inLane 11),
    (kInAddr r 12, r.cnt[12], cellLimbs r.inLane 12),
    (g ^ 0 * (r.fp * r.oout), r.cnt[13], cellLimbs r.outLane 0),
    (g ^ 1 * (r.fp * r.oout), r.cnt[14], cellLimbs r.outLane 1),
    (g ^ 2 * (r.fp * r.oout), r.cnt[15], cellLimbs r.outLane 2),
    (g ^ 3 * (r.fp * r.oout), r.cnt[16], cellLimbs r.outLane 3),
    (g ^ 4 * (r.fp * r.oout), r.cnt[17], cellLimbs r.outLane 4),
    (g ^ 5 * (r.fp * r.oout), r.cnt[18], cellLimbs r.outLane 5),
    (g ^ 6 * (r.fp * r.oout), r.cnt[19], cellLimbs r.outLane 6),
    (g ^ 7 * (r.fp * r.oout), r.cnt[20], cellLimbs r.outLane 7),
    (g ^ 8 * (r.fp * r.oout), r.cnt[21], cellLimbs r.outLane 8),
    (g ^ 9 * (r.fp * r.oout), r.cnt[22], cellLimbs r.outLane 9),
    (g ^ 10 * (r.fp * r.oout), r.cnt[23], cellLimbs r.outLane 10),
    (g ^ 11 * (r.fp * r.oout), r.cnt[24], cellLimbs r.outLane 11),
    (g ^ 12 * (r.fp * r.oout), r.cnt[25], cellLimbs r.outLane 12)]

/-- The address expression of input cell `c`, evaluated. -/
theorem eval_inAddrE_k (env : Environment K) (r : Var Sha3Row K) (c : ℕ) :
    Expression.eval env (inAddrE r c) = kInAddr (eval env r) c := by
  obtain ⟨pc, fp, om, otail, ocap, oout, inL, outL, cnt, cntBc⟩ := r
  unfold inAddrE kInAddr
  split_ifs <;> simp [circuit_norm, Expression.eval]

/-- Limb `0` of a cell, evaluated. -/
theorem eval_cellLimbs0 (env : Environment K) (v : Vector (Expression K) 25) (c : ℕ) :
    Expression.eval env (cellLimbs v c)[0] = (cellLimbs (v.map (Expression.eval env)) c)[0] :=
  eval_cellLimbs env v c 0 (by decide)

/-- Limb `1` of a cell, evaluated. -/
theorem eval_cellLimbs1 (env : Environment K) (v : Vector (Expression K) 25) (c : ℕ) :
    Expression.eval env (cellLimbs v c)[1] = (cellLimbs (v.map (Expression.eval env)) c)[1] :=
  eval_cellLimbs env v c 1 (by decide)

/-- Limb `2` of a cell, evaluated. -/
theorem eval_cellLimbs2 (env : Environment K) (v : Vector (Expression K) 25) (c : ℕ) :
    Expression.eval env (cellLimbs v c)[2] = (cellLimbs (v.map (Expression.eval env)) c)[2] :=
  eval_cellLimbs env v c 2 (by decide)

/-- **The sends of the `SHA3` row circuit**, in closed form: the state step, the bytecode read of the row's entry and
the 26 reads `sha3Reads`. -/
theorem sha3_sends_gen (x : Var Sha3Row K) (env : Environment K) (n : ℕ) (r : Sha3Row K)
    (hx : eval env x = r) :
    (((sha3Table.main x).operations n).interactionValues env).map (fun i ↦ (i.channel.name, i.msg)) =
      sendsOf r.pc r.fp ⟨g * r.pc, r.fp⟩ r.cntBc (KeccakVm.entry r.instr) (sha3Reads r) := by
  subst hx
  obtain ⟨pc, fp, om, otail, ocap, oout, inL, outL, cnt, cntBc⟩ := x
  simp only [Operations.interactionValues, circuit_norm, sha3Table, memRead, bytecodeRead,
    AbstractInteraction.eval, Vector.toArray_map, regs_toArray, memMsg_toArray,
    bytecodeMsg_toArray, -BitVec.reduceNeg]
  simp only [eval_inAddrE_k, eval_cellLimbs0, eval_cellLimbs1, eval_cellLimbs2]
  simp [sendsOf, sha3Reads, memMsgOf, bcMsgOf, KeccakVm.entry, Sha3Row.instr, Sha3Row.omF, outAddrE,
    circuit_norm, Expression.eval, Vector.get]

/-- **A `SHA3` row is a step of the Keccak VM**: it sends `sha3Reads`' record, and under `Sha3Relation` (its
`Assumptions`) and its pulls' guarantees the `SHA3` it names executes to the fall-through (`sha3_row_sound`). -/
theorem sha3_opRow (env : Environment K) : KOpRow ⟨sha3Table⟩ env := by
  set r := (⟨sha3Table⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset Sha3Row 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.cntBc, KeccakVm.entry r.instr, sha3Reads r⟩, ?_, by simp [sha3Reads],
    fun ha _ hg ↦ ⟨r.instr, rfl, (sha3_row_sound env ha hg).2, fun _ ↦ rfl⟩⟩
  rw [rowSends_mk, sha3_sends_gen _ _ _ _ hx]
  rfl

/-! ## The five shared tables -/

/-- An `XOR` row is a step of the Keccak VM. -/
theorem xor_kOpRow (env : Environment K) : KOpRow ⟨xorTable⟩ env := by
  set r := (⟨xorTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset XorRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc, Lv42.Arithmetization.entry (.xor r.oA r.oB r.oC),
    [(r.fp * r.oA, r.rA, r.vA), (r.fp * r.oB, r.rB, r.vB),
     (r.fp * r.oC, r.rC, #v[r.vA[0] + r.vB[0], r.vA[1] + r.vB[1], r.vA[2] + r.vB[2]])]⟩,
    ?_, by simp, ?_⟩
  · rw [rowSends_mk, xor_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf, Lv42.Arithmetization.entry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : XorRefines (imageOf env.data).2 r ((⟨xorTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨-, -, hnext⟩ := (xor_refines_iff _ _ _).mp hs'
    refine ⟨.xor r.oA r.oB r.oC, rfl, ?_, fun _ ↦ rfl⟩
    rw [← show ((⟨xorTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- A `SET_CONSTANT` row is a step of the Keccak VM. -/
theorem set_kOpRow (env : Environment K) : KOpRow ⟨setTable⟩ env := by
  set r := (⟨setTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset SetRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc,
    #v[Lv42.Parameters.Opcode.setConstant.code, r.o, r.k[0], r.k[1], r.k[2], 0, 0, 0],
    [(r.fp * r.o, r.r, r.k)]⟩, ?_, by simp, ?_⟩
  · rw [rowSends_mk, set_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : SetRefines (imageOf env.data).2 r ((⟨setTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨-, hnext⟩ := (set_refines_iff _ _ _).mp hs'
    refine ⟨.setConstant r.o (E.ofLimbs r.k[0] r.k[1] r.k[2]),
      by simp [KeccakVm.entry, Lv42.Arithmetization.entry, limb_ofLimbs], ?_, fun _ ↦ rfl⟩
    rw [← show ((⟨setTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- A `MUL_NATIVE` row is a step of the Keccak VM. -/
theorem mul_kOpRow (env : Environment K) : KOpRow ⟨mulTable⟩ env := by
  set r := (⟨mulTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset MulRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc, Lv42.Arithmetization.entry (.mulNative r.oA r.oB r.oC),
    [(r.fp * r.oA, r.rA, r.vA), (r.fp * r.oB, r.rB, r.vB),
     (r.fp * r.oC, r.rC, #v[r.vA[0] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1],
          r.vA[0] * r.vB[1] + r.vA[1] * r.vB[0] + r.vA[1] * r.vB[2] + r.vA[2] * r.vB[1] +
            r.vA[2] * r.vB[2],
          r.vA[0] * r.vB[2] + r.vA[1] * r.vB[1] + r.vA[2] * r.vB[0] + r.vA[2] * r.vB[2]])]⟩,
    ?_, by simp, ?_⟩
  · rw [rowSends_mk, mul_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf, Lv42.Arithmetization.entry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : MulRefines (imageOf env.data).2 r ((⟨mulTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨-, -, hnext⟩ := (mul_refines_iff _ _ _).mp hs'
    refine ⟨.mulNative r.oA r.oB r.oC, rfl, ?_, fun _ ↦ rfl⟩
    rw [← show ((⟨mulTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
    exact hs'.exec_eq

/-- A `DEREF` row is a step of the Keccak VM: the mode is the one its flags name. -/
theorem deref_kOpRow (env : Environment K) : KOpRow ⟨derefTable⟩ env := by
  set r := (⟨derefTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset DerefRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, ⟨g * r.pc, r.fp⟩, r.rbc,
    #v[Lv42.Parameters.Opcode.deref.code, r.o1, r.o2, r.o3, r.fpc, r.ffp, 0, 0],
    [(r.fp * r.o1, r.r1, #v[r.p, 0, 0]),
     (r.p * r.o2, r.r2, #v[(1 + r.fpc + r.ffp) * r.v3[0] + r.fpc * (g ^ 2 * r.pc) + r.ffp * r.fp,
          (1 + r.fpc + r.ffp) * r.v3[1], (1 + r.fpc + r.ffp) * r.v3[2]]),
     (r.fp * r.o3, r.r3, r.v3)]⟩,
    ?_, by simp, ?_⟩
  · rw [rowSends_mk, deref_sends_gen _ _ _ _ hx]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : DerefRefines (imageOf env.data).2 r
      ((⟨derefTable⟩ : Component K).rowOutput env) := hs
    obtain ⟨mode, hb, -, hnext⟩ := (deref_refines_iff _ _ _).mp hs'
    obtain ⟨mode', hb', hexec⟩ := hs'
    have hflags := hb.flags_eq
    have hm : mode' = mode := by
      have h1 := derefMode?_flags mode
      have h2 := derefMode?_flags mode'
      rw [hflags] at h1
      rw [hb'.flags_eq] at h2
      exact Option.some.inj (h2.symm.trans h1)
    subst hm
    refine ⟨.deref r.o1 r.o2 r.o3 mode', ?_, ?_, fun _ ↦ rfl⟩
    · simp [KeccakVm.entry, Lv42.Arithmetization.entry, hflags]
    · rw [← show ((⟨derefTable⟩ : Component K).rowOutput env) = ⟨g * r.pc, r.fp⟩ from hnext]
      exact hexec

/-- A `JUMP` row is a step of the Keccak VM, its pushed successor the table's output. -/
theorem jump_kOpRow (env : Environment K) : KOpRow ⟨jumpTable⟩ env := by
  set r := (⟨jumpTable⟩ : Component K).rowInput env with hr
  have hx : eval env (varFromOffset JumpRow 0) = r := eval_varFromOffset_valueFromOffset ..
  refine ⟨⟨r.pc, r.fp, (⟨jumpTable⟩ : Component K).rowOutput env, r.rbc,
    Lv42.Arithmetization.entry (.jump r.oc r.od r.of),
    [(r.fp * r.oc, r.rc, #v[r.vcond, 0, 0]), (r.fp * r.od, r.rd, #v[r.vpc, 0, 0]),
     (r.fp * r.of, r.rf, #v[r.vfp, 0, 0])]⟩, ?_, by simp, ?_⟩
  · have ho : (⟨jumpTable⟩ : Component K).rowOutput env = _ :=
      jump_output_gen _ env (size JumpRow) r hx _ rfl
    rw [rowSends_mk, jump_sends_gen _ _ _ _ hx _ rfl, ho]
    simp [RowRec.sends, sendsOf, memMsgOf, bcMsgOf, Lv42.Arithmetization.entry]
  · intro ha hc hg
    obtain ⟨hs, -⟩ := Component.weakSoundness ha hc hg
    have hs' : JumpRefines (imageOf env.data).2 r
      ((⟨jumpTable⟩ : Component K).rowOutput env) := hs
    exact ⟨.jump r.oc r.od r.of, rfl, hs'.exec_eq, fun h ↦ absurd rfl h⟩

/-! ## The channels -/

/-- Every interaction of the `SHA3` table is on one of the six channels (Lv42's `ChannelOk`): the two lookup pulls,
or a channel guaranteeing nothing. -/
theorem sha3_channelOk : ∀ a ∈ (⟨sha3Table⟩ : Component K).operations.interactions, ChannelOk a.channel := by
  have h1 : ChannelOk MemPull.toRaw := Or.inl rfl
  have h2 : ChannelOk BytecodePull.toRaw := Or.inr (Or.inl rfl)
  have h3 : ChannelOk StatePull.toRaw := Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
  have h4 : ChannelOk StatePush.toRaw := Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
  have h5 : ChannelOk MemPush.toRaw := Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
  have h6 : ChannelOk BytecodePush.toRaw := Or.inr (Or.inr fun _ _ _ _ ↦ trivial)
  rw [Component.interactions_eq]
  simp only [Component.rowOperations_mk, circuit_norm, sha3Table, memRead, bytecodeRead, -BitVec.reduceNeg]
  simp only [forall_eq_or_imp, forall_eq, ChannelInteraction.toRaw_channel, h1, h2, h3, h4, h5, h6, and_self]

end KeccakArith

end
