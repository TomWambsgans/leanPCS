-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
module

public import KeccakArith.Sha3Table

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Parameters Lv42.Semantics Lv42.Arithmetization KeccakVm

/-- The typed row of 86 cells, in `SHA3_COLUMNS`' order. -/
def rowOfCells (f : Fin 86 → K) : Sha3Row K :=
  ⟨f 0, f 1, Vector.ofFn fun i ↦ f ⟨2 + i, by omega⟩, f 6, f 7, f 8, Vector.ofFn fun l ↦ f ⟨9 + l, by omega⟩,
    Vector.ofFn fun l ↦ f ⟨34 + l, by omega⟩, Vector.ofFn fun c ↦ f ⟨59 + c, by omega⟩, f 85⟩

/-- A raw row of 86 cells reads, as the component reads it, as `rowOfCells`. -/
theorem valueFromOffset_ofFn (f : Fin 86 → K) (data : ProverData K) :
    valueFromOffset Sha3Row 0 (Environment.fromArray (Array.ofFn f) data) = rowOfCells f := by
  simp [valueFromOffset, explicit_provable_type, circuit_norm, Array.getElem?_ofFn, rowOfCells]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    exact Array.ext (by simp) fun i h1 _ ↦ by
      simp only [List.size_toArray, List.length_cons, List.length_nil] at h1
      simp only [Array.getElem_ofFn]
      interval_cases i <;> rfl

/-! ## A row of the component -/

/-- The component has neither a constraint nor a lookup: its Clean constraints hold on every row. -/
theorem sha3_constraintsHold (env : Environment K) :
    (⟨sha3Table⟩ : Air.Flat.Component K).operations.ConstraintsHold env := by
  have h₁ : (⟨sha3Table⟩ : Air.Flat.Component K).rowOperations.constraints = [] :=
    List.eq_nil_of_length_eq_zero (by decide +kernel)
  have h₂ : (⟨sha3Table⟩ : Air.Flat.Component K).rowOperations.lookups = [] :=
    List.eq_nil_of_length_eq_zero (by decide +kernel)
  rw [Air.Flat.Component.constraintsHold_iff, Operations.ConstraintsHold, h₁, h₂]
  simp

/-- **A `SHA3` row is a step** (Clean's soundness of the component, `Component.weakSoundness`): under the Keccak
relation on its lanes and the guarantees of its pulls (the 26 memory pulls are reads of the image the data names,
the bytecode tuple decodes), its cells are bound to the image and the Keccak VM executes the `SHA3` it names, from its
pulled state to the fall-through `(g·pc, fp)`; the read cells are canonical and the written cells are `sha3Step` of
the read state, `END_BIT` included (`Sha3Cells`). -/
theorem sha3_row_sound (env : Environment K)
    (hA : Sha3Relation ((⟨sha3Table⟩ : Air.Flat.Component K).rowInput env))
    (hg : (⟨sha3Table⟩ : Air.Flat.Component K).operations.FullGuarantees env) :
    Sha3Bindings (imageOf env.data).2 ((⟨sha3Table⟩ : Air.Flat.Component K).rowInput env) ∧
      KeccakVm.executeWith (imageOf env.data).2.read
          ⟨((⟨sha3Table⟩ : Air.Flat.Component K).rowInput env).pc,
            ((⟨sha3Table⟩ : Air.Flat.Component K).rowInput env).fp⟩
          ((⟨sha3Table⟩ : Air.Flat.Component K).rowInput env).instr =
        some ⟨g * ((⟨sha3Table⟩ : Air.Flat.Component K).rowInput env).pc,
          ((⟨sha3Table⟩ : Air.Flat.Component K).rowInput env).fp⟩ := by
  obtain ⟨hs, -⟩ := Air.Flat.Component.weakSoundness hA (sha3_constraintsHold env) hg
  have hs' : Sha3Refines (imageOf env.data).2 ((⟨sha3Table⟩ : Air.Flat.Component K).rowInput env)
      ((⟨sha3Table⟩ : Air.Flat.Component K).rowOutput env) := hs
  obtain ⟨hb, -, hnext⟩ := (sha3_refines_iff _ _ _).mp hs'
  refine ⟨hb, ?_⟩
  have he := hs'.exec_eq
  rw [hnext] at he
  exact he

/-! ## The stack's rows -/

/-- A lane of a sum is the `XOR` of the lanes. -/
theorem lane_add (a b : K) : (a + b).lane = a.lane ^^^ b.lane := rfl

/-- The zero element's lane is zero. -/
theorem lane_zero : (0 : K).lane = 0 := rfl

section Stack

variable (F : KeccakFlockSpec) (prog : KeccakVm.Program) (s : Lv42.Protocol.LeanIsa.Sizes)
  (q : LeanVM.Protocol.Column (KeccakIsa.keccakIsaμ prog s))

/-- Row `t` of the `SHA3` table, read off the stack. -/
abbrev stackCells (t : Fin (2 ^ s.τ 5)) : Fin 86 → K := (keccakIsaInstance prog s).row q (⟨8, Nat.lt_succ_self 8⟩ : Fin 9) t

/-- Row `t` of the `SHA3` table as a typed row. -/
def stackRow (t : Fin (2 ^ s.τ 5)) : Sha3Row K := rowOfCells (stackCells prog s q t)

/-- An input lane of the stack's row is its `SHA3` cell. -/
theorem stackRow_inLane (t : Fin (2 ^ s.τ 5)) (l : ℕ) (hl : l < 25) :
    (stackRow prog s q t).inLane[l] =
      sha3Cell prog s q (Sha3Table.inLane l) (by unfold Sha3Table.inLane Sha3Table.width; omega) t := by
  simp only [stackRow, rowOfCells, Vector.getElem_ofFn]
  rfl

/-- An output lane of the stack's row is its `SHA3` cell. -/
theorem stackRow_outLane (t : Fin (2 ^ s.τ 5)) (l : ℕ) (hl : l < 25) :
    (stackRow prog s q t).outLane[l] =
      sha3Cell prog s q (Sha3Table.outLane l) (by unfold Sha3Table.outLane Sha3Table.width; omega) t := by
  simp only [stackRow, rowOfCells, Vector.getElem_ofFn]
  rfl

/-- Lane 16's offset is `END_BIT`. -/
theorem laneOffset_endLane (h : 16 < 25) : laneOffset ⟨16, h⟩ = K.ofLane endBit := by
  simp [laneOffset, endLane]

/-- The other lanes have no offset. -/
theorem laneOffset_ne (l : Fin 25) (h : l.val ≠ 16) : laneOffset l = 0 := by
  simp [laneOffset, endLane, h]

/-- Lane `l` of the lanes' state. -/
theorem laneState_getElem (v : Vector K 25) (l : ℕ) (hl : l < 25) : (laneState v)[l] = (v[l]).lane := by
  simp [laneState]

/-- **The Keccak relation on the stack's executed `SHA3` rows**: `KeccakAux`'s copies tie row `t`'s lanes to block
`t` of `QFLOCK` (the input lanes up to `END_BIT` on lane 16), whose R1CS makes the output port Keccak-f[1600] of the
input port (`KeccakFlockSpec.step_of_holds`); so the output lanes are `sha3Step` of the input lanes. -/
theorem sha3Relation_stackRow (h : KeccakAux F prog s q) (t : Fin (2 ^ s.τ 5)) (ht : t.val < s.rows 5) :
    Sha3Relation (stackRow prog s q t) := by
  obtain ⟨hR, hcopy⟩ := h
  have hstep := F.step_of_holds _ hR t
  have hout : laneState (stackRow prog s q t).outLane =
      kBlockState (flockColumn prog s q) t F.outSlot := by
    apply Vector.ext
    intro l hl
    rw [laneState_getElem _ _ hl, stackRow_outLane _ _ _ _ _ hl, (hcopy t ht ⟨l, hl⟩).2]
    simp [kBlockState]
  have hin : (laneState (stackRow prog s q t).inLane).setIfInBounds endLane
      (LeanVM.Semantics.Keccak.lane (laneState (stackRow prog s q t).inLane) endLane ^^^ endBit) =
        kBlockState (flockColumn prog s q) t F.inSlot := by
    apply Vector.ext
    intro l hl
    have hl' := (hcopy t ht ⟨l, hl⟩).1
    rw [Vector.getElem_setIfInBounds]
    simp only [kBlockState, Vector.getElem_ofFn]
    unfold endLane
    split_ifs with h16
    · subst h16
      rw [lane_eq_getElem _ _ (by decide), laneState_getElem _ _ (by decide), stackRow_inLane _ _ _ _ _ (by decide),
        hl', laneOffset_endLane, lane_add, UInt64.xor_assoc]
      simp [K.lane, K.ofLane]
    · rw [laneState_getElem _ _ hl, stackRow_inLane _ _ _ _ _ hl, hl', laneOffset_ne _ (fun h ↦ h16 h.symm), add_zero]
  unfold Sha3Relation sha3Step
  rw [hout, hin]
  exact hstep

/-- **Per-row soundness on the stack**: on a stack with `KeccakAux`, an executed `SHA3` row whose pulls carry their
guarantees (its 26 memory pulls are reads of the image the data names, as Lv42's bus soundness makes them) is a step:
its cells are bound to the image and the Keccak VM executes its `SHA3` to `(g·pc, fp)`. -/
theorem sha3_stackRow_sound (h : KeccakAux F prog s q) (t : Fin (2 ^ s.τ 5)) (ht : t.val < s.rows 5)
    (data : ProverData K)
    (hg : (⟨sha3Table⟩ : Air.Flat.Component K).operations.FullGuarantees
      (Environment.fromArray (Array.ofFn (stackCells prog s q t)) data)) :
    Sha3Bindings (imageOf data).2 (stackRow prog s q t) ∧
      KeccakVm.executeWith (imageOf data).2.read ⟨(stackRow prog s q t).pc, (stackRow prog s q t).fp⟩
          (stackRow prog s q t).instr =
        some ⟨g * (stackRow prog s q t).pc, (stackRow prog s q t).fp⟩ := by
  have hr : (⟨sha3Table⟩ : Air.Flat.Component K).rowInput
      (Environment.fromArray (Array.ofFn (stackCells prog s q t)) data) = stackRow prog s q t :=
    valueFromOffset_ofFn _ _
  have := sha3_row_sound _ (hr ▸ sha3Relation_stackRow F prog s q h t ht) hg
  rw [hr] at this
  exact this

end Stack

end KeccakArith
end
