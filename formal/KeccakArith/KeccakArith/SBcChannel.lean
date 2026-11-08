-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `formal/Lv42`'s
-- `Arithmetization/Soundness/BytecodeChannel.lean` (leanerVM `mumbai` f0393df4, MIT OR Apache-2.0), for the Keccak VM.
module

public import KeccakArith.SMemChannel

/-!
# Soundness of the bytecode channel, for the Keccak VM

Lv42's `bytecode_channel_sound` at `kEnsemble`: every pulled bytecode entry is the Keccak VM program's entry at the
pulled counter, so it decodes (Lv42's `decode`, the bytecode pull's guarantee).
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Arithmetization KeccakVm
open Lv42.Semantics (Regs MemImage PublicInput)
open Lv42.Parameters (minLogMem maxLogMem maxLogRows)
open Air.Flat (Component EnsembleWitness)

variable {prog : KeccakVm.Program} {input : PublicInput} {w : EnsembleWitness (kEnsemble prog)}

/-! ## Bytecode messages as triples -/

/-- A bytecode message as its triple. -/
def bcMsgOfTriple (x : K × K × Vector K 8) : Array K := bcMsgOf x.1 x.2.1 x.2.2

/-- The triple of a bytecode message, `0` for a missing coordinate. -/
def tripleOfBcMsg (a : Array K) : K × K × Vector K 8 :=
  (a.getD 0 0, a.getD 1 0, #v[a.getD 2 0, a.getD 3 0, a.getD 4 0, a.getD 5 0, a.getD 6 0,
    a.getD 7 0, a.getD 8 0, a.getD 9 0])

/-- A vector of eight is its entries. -/
theorem vec8_eta (v : Vector K 8) : #v[v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]] = v := by
  refine Vector.ext fun i hi ↦ ?_
  interval_cases i <;> rfl

/-- Reading a bytecode message back gives its triple. -/
theorem tripleOfBcMsg_bcMsgOfTriple (x : K × K × Vector K 8) :
    tripleOfBcMsg (bcMsgOfTriple x) = x := by
  obtain ⟨a, c, v⟩ := x
  simp only [tripleOfBcMsg, bcMsgOfTriple, bcMsgOf]
  simp [vec8_eta]

/-- Reading a bytecode message back gives its coordinates. -/
theorem tripleOfBcMsg_bcMsgOf (pc c : K) (e : Vector K 8) :
    tripleOfBcMsg (bcMsgOf pc c e) = (pc, c, e) :=
  tripleOfBcMsg_bcMsgOfTriple (pc, c, e)

/-- Bytecode messages are injective in their triple. -/
theorem bcMsgOfTriple_injective : Function.Injective bcMsgOfTriple := fun x y h ↦ by
  rw [← tripleOfBcMsg_bcMsgOfTriple x, h, tripleOfBcMsg_bcMsgOfTriple]

/-- A vector of seven is its entries. -/
theorem vec7_eta (v : Vector K 7) : #v[v[0], v[1], v[2], v[3], v[4], v[5], v[6]] = v := by
  refine Vector.ext fun i hi ↦ ?_
  interval_cases i <;> rfl

/-- An opcode followed by seven operands is the eight-coordinate vector of them. -/
theorem cons_append_eta (a : K) (v : Vector K 7) :
    #v[a] ++ v = #v[a, v[0], v[1], v[2], v[3], v[4], v[5], v[6]] := by
  conv_lhs => rw [← vec7_eta v]
  rfl

/-- A typed bytecode message flattens to the message of its triple, the entry its opcode followed
by its operands. -/
theorem toElements_bcMsg (m : BytecodeMsg K) :
    (toElements m).toArray = bcMsgOfTriple (m.pc, m.count, #v[m.opcode] ++ m.op) := by
  rw [bytecodeMsg_toArray, bcMsgOfTriple, cons_append_eta]
  rfl

/-! ## The bytecode pair -/

/-- A list of singletons is a map, over any universe. -/
theorem flatMap_singleton_eq_map' {α : Type*} {β : Type} (f : α → β) (l : List α) :
    (l.flatMap fun a ↦ [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The bytecode read of a row of the six tables, as a triple. -/
def bcReadOf (x : RowRec) : K × K × Vector K 8 := (x.pc, x.rbc, x.e)

/-- A bytecode read pushed back: its count multiplied by `g`. -/
def bumpBc (x : K × K × Vector K 8) : K × K × Vector K 8 := (x.1, g * x.2.1, x.2.2)

/-- The bytecode messages a row of the six tables pulls. -/
theorem chanOf_rowRec_bcPull (x : RowRec) :
    chanOf BytecodePull.name x.sends = [bcMsgOfTriple (bcReadOf x)] :=
  sendsOf_bcPull _ _ _ _ _ _

/-- The bytecode messages a row of the six tables pushes. -/
theorem chanOf_rowRec_bcPush (x : RowRec) :
    chanOf BytecodePush.name x.sends = [bcMsgOfTriple (bumpBc (bcReadOf x))] :=
  sendsOf_bcPush _ _ _ _ _ _

/-- **The bytecode pair of a satisfying witness, as triples**: the bumped reads and the seeds are a
permutation of the reads and the finalizes. -/
theorem bc_triples_perm (h : SatisfiedByB prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    {mfin : Fin (2 ^ (imageOf w.data).1) → K} {bfin : Fin (2 ^ prog.logSize) → K}
    (hall : allSends w = verifierSends prog ++ (opPairs w).flatMap (fun p ↦ (f p).sends) ++
      memSeedSends (imageOf w.data).2 mfin ++ bcSeedSends prog bfin) :
    (((opPairs w).map fun p ↦ bcReadOf (f p)).map bumpBc ++
        (List.finRange (2 ^ prog.logSize)).map fun i : Fin _ ↦
          (gpow i, 1, KeccakVm.entry (prog.code i))).Perm
      (((opPairs w).map fun p ↦ bcReadOf (f p)) ++
        (List.finRange (2 ^ prog.logSize)).map fun i : Fin _ ↦
          (gpow i, bfin i, KeccakVm.entry (prog.code i))) := by
  have hb := h.bytecode_balanced
  unfold BalancedPair at hb
  rw [messagesOn_eq_chanOf, messagesOn_eq_chanOf, chanOf_allSends _ hall,
    chanOf_allSends _ hall] at hb
  simp only [Channel.toRaw_name] at hb
  rw [chanOf_verifier_eq_nil (by simp [BytecodePush, StatePull])
      (by simp [BytecodePush, StatePush]),
    chanOf_verifier_eq_nil (by simp [BytecodePull, StatePull]) (by simp [BytecodePull, StatePush]),
    chanOf_memSeed_eq_nil _ _ (by simp [BytecodePush, MemPull]) (by simp [BytecodePush, MemPush]),
    chanOf_memSeed_eq_nil _ _ (by simp [BytecodePull, MemPull]) (by simp [BytecodePull, MemPush]),
    chanOf_bcSeed_push, chanOf_bcSeed_pull] at hb
  simp only [chanOf_rowRec_bcPull, chanOf_rowRec_bcPush, List.nil_append, List.append_nil,
    flatMap_singleton_eq_map'] at hb
  have := hb.map tripleOfBcMsg
  simp only [List.map_append, List.map_map] at this
  convert this using 2 <;>
    simp [Function.comp_def, tripleOfBcMsg_bcMsgOfTriple, tripleOfBcMsg_bcMsgOf]

/-- Every bytecode message a satisfying witness pulls has a counter `g^k` of the program and
the program's entry there. -/
theorem bc_pulls_seeded (h : SatisfiedByB prog input w) :
    ∀ msg ∈ messagesOn w BytecodePull.toRaw, ∃ x : K × K × Vector K 8, msg = bcMsgOfTriple x ∧
      ∃ k : Fin (2 ^ prog.logSize), x.1 = gpow k ∧ x.2.2 = KeccakVm.entry (prog.code k) := by
  obtain ⟨f, hf⟩ := exists_opRecs w
  obtain ⟨mfin, bfin, hall⟩ := allSends_eq h hf
  have hperm := bc_triples_perm h hall
  let key : K × K × Vector K 8 → K × Vector K 8 := fun x ↦ (x.1, x.2.2)
  have hseeded := lookup_sound key (·.2.1) bumpBc _ _ _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hperm
    (fun x hx ↦ by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact (opRecs_counts_nonzero h hf hp).2)
    (by
      rw [List.length_map]
      have := opPairs_length_le h
      omega)
    (fun x hx ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map.mpr ⟨_, List.mem_map_of_mem (List.mem_finRange i), rfl⟩)
  have hkey : ∀ x ∈ ((opPairs w).map fun p ↦ bcReadOf (f p)) ++
      (List.finRange (2 ^ prog.logSize)).map fun i : Fin _ ↦
        (gpow i, bfin i, KeccakVm.entry (prog.code i)),
      ∃ k : Fin (2 ^ prog.logSize), x.1 = gpow k ∧ x.2.2 = KeccakVm.entry (prog.code k) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, hyx⟩ := List.mem_map.mp (hseeded x hx)
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
      exact ⟨i, (congrArg Prod.fst hyx).symm, (congrArg Prod.snd hyx).symm⟩
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨i, rfl, rfl⟩
  intro msg hmsg
  have hpull : messagesOn w BytecodePull.toRaw =
      (((opPairs w).map fun p ↦ bcReadOf (f p)) ++
        (List.finRange (2 ^ prog.logSize)).map fun i : Fin _ ↦
          (gpow i, bfin i, KeccakVm.entry (prog.code i))).map bcMsgOfTriple := by
    rw [messagesOn_eq_chanOf, chanOf_allSends _ hall]
    simp only [Channel.toRaw_name]
    rw [chanOf_verifier_eq_nil (by simp [BytecodePull, StatePull])
        (by simp [BytecodePull, StatePush]),
      chanOf_memSeed_eq_nil _ _ (by simp [BytecodePull, MemPull])
        (by simp [BytecodePull, MemPush]),
      chanOf_bcSeed_pull]
    simp only [chanOf_rowRec_bcPull, List.nil_append, List.append_nil, List.map_append,
      flatMap_singleton_eq_map', List.map_map]
    rfl
  rw [hpull] at hmsg
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmsg
  exact ⟨x, rfl, hkey x hx⟩

/-- **Soundness of the bytecode channel** (specification Theorem 6.4 and Corollary 6.5 for the
bytecode pair), in the strong form: every pulled entry is the public program's at the pulled
counter (from `BytecodeRowsAreTheProgram prog`). It implies the pull's guarantee, that the entry
decodes, and is what `constraintSoundness` joins to `execute` by `execute_of_step`. -/
theorem bytecode_channel_sound (h : SatisfiedByB prog input w) :
    ∀ i ∈ w.interactions, i.channel.name = BytecodePull.name →
      ∀ m : BytecodeMsg K, i.msg = (toElements m).toArray →
        ∃ k : Fin (2 ^ prog.logSize), m.pc = gpow k ∧
          #v[m.opcode] ++ m.op = KeccakVm.entry (prog.code k) := by
  intro i hi hname m hm
  obtain ⟨x, hx, k, h1, h2⟩ := bc_pulls_seeded h i.msg (mem_messagesOn hi hname)
  rw [hm, toElements_bcMsg] at hx
  obtain rfl := bcMsgOfTriple_injective hx
  exact ⟨k, h1, h2⟩

/-- Every Keccak VM entry decodes under the bytecode pull's decoder (Lv42's `decode`, whose opcode-`5` branch reads
seven operand slots, the `SHA3` entry's shape). -/
theorem decode_kentry (i : KeccakVm.Instr) : ∃ ins, Lv42.Arithmetization.decode (KeccakVm.entry i) = some ins := by
  cases i with
  | sha3 om otail ocap oout => exact ⟨_, Lv42.Arithmetization.decode_entry (.blake2s om otail ocap oout)⟩
  | xor oA oB oC => exact ⟨_, Lv42.Arithmetization.decode_entry (.xor oA oB oC)⟩
  | mulNative oA oB oC => exact ⟨_, Lv42.Arithmetization.decode_entry (.mulNative oA oB oC)⟩
  | setConstant o k => exact ⟨_, Lv42.Arithmetization.decode_entry (.setConstant o k)⟩
  | deref o1 o2 o3 mode => exact ⟨_, Lv42.Arithmetization.decode_entry (.deref o1 o2 o3 mode)⟩
  | jump oc od of => exact ⟨_, Lv42.Arithmetization.decode_entry (.jump oc od of)⟩

/-- The bytecode pull's guarantee, that the entry decodes, for every bytecode pull of a satisfying
witness. -/
theorem bytecode_guarantee (h : SatisfiedByB prog input w) :
    ∀ i ∈ w.interactions, i.channel.name = BytecodePull.name →
      ∀ m : BytecodeMsg K, i.msg = (toElements m).toArray → BytecodePull.Guarantees m w.data := by
  intro i hi hname m hm
  obtain ⟨k, -, he⟩ := bytecode_channel_sound h i hi hname m hm
  obtain ⟨ins, hins⟩ := decode_kentry (prog.code k)
  exact ⟨ins, by rw [he]; exact hins⟩

/-- The bytecode read of every row of the six tables is the program's: its counter is `g^k` for a
slot `k` and its coordinates are the entry there. -/
theorem opRecs_bc_sound (h : SatisfiedByB prog input w) {f : Air.Flat.Table K × Array K → RowRec}
    (hf : OpRecs w f) {p : Air.Flat.Table K × Array K} (hp : p ∈ opPairs w) :
    ∃ k : Fin (2 ^ prog.logSize), (f p).pc = gpow k ∧ (f p).e = KeccakVm.entry (prog.code k) := by
  obtain ⟨mfin, bfin, hall⟩ := allSends_eq h hf
  have hm : bcMsgOfTriple (bcReadOf (f p)) ∈ messagesOn w BytecodePull.toRaw := by
    rw [messagesOn_eq_chanOf, chanOf_allSends _ hall]
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
    rw [Channel.toRaw_name, chanOf_rowRec_bcPull]
    exact List.mem_singleton_self _
  obtain ⟨x, hx, k, h1, h2⟩ := bc_pulls_seeded h _ hm
  obtain rfl := bcMsgOfTriple_injective hx
  exact ⟨k, h1, h2⟩

end KeccakArith

end
