-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `formal/Lv42`'s `Protocol/LeanIsa/Sound.lean` and
-- `Arithmetization/Soundness/Theorem.lean` (leanerVM `mumbai` f0393df4, MIT OR Apache-2.0), for the Keccak VM.
module

public import KeccakArith.ARelation

/-!
# Soundness of the Keccak VM's relation

`satisfiedBy_witnessOf`: if the announced sizes are admissible and the stack `q` satisfies `KvHolds F prog s input q`,
the witness read off `q` (`witnessOf`) satisfies the Keccak VM's constraint statement. Every conjunct comes from a
clause of `M3Holds` (through `Agrees`, `ARelation`), from admissibility, or from how the witness is read, as in Lv42;
the Keccak relation on the `SHA3` rows (`Sha3RowsValid`) comes from `KeccakAux` (`sha3Relation_stackRow`: the lanes'
copies and the Keccak-f block's soundness `KeccakFlockSpec.step_of_holds`).

`kvSoundness`: with the program's last instruction not a `JUMP` (`SentinelSafe`), a stack satisfying `KvHolds`
represents a valid execution (`constraintSoundness`); `kvSoundness_exists` states the execution alone.
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Arithmetization KeccakVm KeccakVm.KeccakIsa
open LeanVM.Protocol (Column M3Table flushTuple tupleMsg powersTable CountsAreVariables countVar toM3_constraints_iff mem_toM3_count_iff)
open Lv42.Protocol (M3Instance Side BoundaryBlock Coord idxColumn)
open Lv42.Protocol.LeanIsa (Sizes sideOf counted)
open Lv42.Semantics (Regs MemImage PublicInput)
open Lv42.Parameters (minLogMem maxLogMem maxLogRows)
open Air.Flat (Component EnsembleWitness)

@[expose] public section

variable (prog : KeccakVm.Program) (s : Sizes) (q : Column (keccakIsaμ prog s))

/-- **The Keccak relation on the `SHA3` rows.** On a stack with `KeccakAux`, every `SHA3` row of the witness read off
it satisfies `Sha3Relation` (`sha3Relation_stackRow`). -/
theorem sha3RowsValid_witnessOf (F : KeccakFlockSpec) (h : KeccakAux F prog s q) :
    Sha3RowsValid (witnessOf prog s q) := by
  intro row hrow
  rw [show sha3Rows (witnessOf prog s q) = opcodeRows prog s q 5 from rfl, opcodeRows, List.mem_ofFn] at hrow
  obtain ⟨x, rfl⟩ := hrow
  have := sha3Relation_stackRow F prog s q h (Fin.castLE (s.rows_le 5) x) x.isLt
  show Sha3Relation (valueFromOffset Sha3Row 0 (Environment.fromArray
    (Array.ofFn (stackCells prog s q (Fin.castLE (s.rows_le 5) x))) (witnessOf prog s q).data))
  rw [valueFromOffset_ofFn]
  exact this

/-! ## The witness agrees with its stack -/

/-- The opcode tables of the witness read off a stack are the stack's rows. -/
private theorem opTable_witnessOf (j : Fin 6) :
    (opTable (witnessOf prog s q) j).table = opcodeRows prog s q j := by
  fin_cases j <;> rfl

/-- The witness read off a stack agrees with it. -/
theorem agrees_witnessOf : Agrees s q (witnessOf prog s q) where
  length j := by rw [opTable_witnessOf, opcodeRows, List.length_ofFn]
  cells j x i := by
    rw [cellOf, opTable_witnessOf, opcodeRows]
    have hlt : (i : ℕ) < (shape prog s).width (opIdx j) := i.isLt
    simp only [List.getElem?_ofFn, Array.getElem?_ofFn, Option.bind_some, Fin.is_lt, dite_true,
      hlt, Option.getD_some]
  memRows := rfl
  bytecodeRows := rfl

/-! ## The image and the public input -/

/-- The prover data's `"mem"` table is the image read off the memory columns. -/
private theorem memRows_witnessOf : memRows (witnessOf prog s q).data = imageRows prog s q := by
  simp [memRows, witnessOf, dataOf]

/-- Two images are equal when their sizes are and their words agree. -/
theorem image_sigma_eq {κ κ' : ℕ} (h : κ = κ') (f : MemImage κ) (g : MemImage κ')
    (hfg : ∀ i : Fin (2 ^ κ), f i = g (Fin.cast (by rw [h]) i)) :
    (⟨κ, f⟩ : (κ : ℕ) × MemImage κ) = ⟨κ', g⟩ := by
  subst h
  congr
  funext i
  exact hfg i

/-- The word of the image at index `x`: the three memory columns' cells. -/
abbrev imageWord (x : Fin (2 ^ s.logMem)) : E :=
  E.ofLimbs (cell prog s q (memCol 0) x) (cell prog s q (memCol 1) x)
    (cell prog s q (memCol 2) x)

/-- Within the memory cap, the image the witness's data names is the memory columns, word by
word, at the announced memory size. -/
theorem imageOf_witnessOf (h : s.logMem ≤ maxLogMem) :
    imageOf (witnessOf prog s q).data = ⟨s.logMem, imageWord prog s q⟩ := by
  unfold imageOf
  rw [memRows_witnessOf]
  have hsz : (imageRows prog s q).size = 2 ^ s.logMem := Array.size_ofFn
  refine image_sigma_eq (by rw [hsz, Nat.log_pow (by norm_num), Nat.min_eq_left h]) _ _
    fun i ↦ ?_
  have hi : (i : ℕ) < 2 ^ s.logMem := hsz ▸ (i.isLt.trans_le (by
    rw [hsz, Nat.log_pow (by norm_num), Nat.min_eq_left h]))
  simp [imageRows, hi]
  rfl

/-- The three public lines fix the first two cells of the three memory columns. -/
theorem publicLines_cells {input : PublicInput}
    (hp : (keccakIsaInstance prog s).PublicLinesHold input q) :
    cell0 prog s q 0 = input.lanes 0 ∧ cell1 prog s q 0 = input.lanes 2 ∧
      cell0 prog s q 1 = input.lanes 1 ∧ cell1 prog s q 1 = input.lanes 3 ∧
      cell0 prog s q 2 = 0 ∧ cell1 prog s q 2 = 0 := by
  have h0 := hp _ (List.mem_cons_self (l := [_, _]))
  have h1 := hp _ (List.mem_cons_of_mem _ (List.mem_cons_self (l := [_])))
  have h2 := hp _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self (l := []))))
  exact ⟨h0.1, h0.2, h1.1, h1.2, h2.1, h2.2⟩

/-! ## The constraints and the caps -/

/-- A component with neither constraints nor lookups holds on every row. -/
private theorem constraintsHold_of_nil (c : Component K) (h₁ : c.rowOperations.constraints = [])
    (h₂ : c.rowOperations.lookups = []) (env : Environment K) :
    c.operations.ConstraintsHold env := by
  rw [Air.Flat.Component.constraintsHold_iff, Operations.ConstraintsHold, h₁, h₂]
  simp

/-- On a stack whose constraint polynomials vanish, every table of the witness read off it
satisfies its Clean constraints. -/
theorem constraints_witnessOf (hcv : (keccakIsaInstance prog s).ConstraintsVanish q) :
    (witnessOf prog s q).Constraints := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact fun _ _ ↦ constraintsHold_of_nil _ rfl rfl _
  · obtain ⟨⟨j, hj⟩, rfl⟩ := mem_tables_iff.mp ht
    by_cases h6 : j < 6
    · exact (opcode_constraints_iff (agrees_witnessOf prog s q) ⟨j, h6⟩).mpr
        fun x C hC ↦ (inst_constraints_iff prog s ⟨j, h6⟩ _).mp (fun C' hC' ↦ hcv (opIdx ⟨j, h6⟩) C' hC' _) C hC
    · have : j = 6 ∨ j = 7 := by omega
      rcases this with rfl | rfl
      · intro row _
        rw [tableAt_component]
        exact constraintsHold_of_nil _ rfl rfl _
      · intro row _
        rw [tableAt_component]
        exact constraintsHold_of_nil _ rfl rfl _

/-- The tables of the witness read off a stack have the announced row counts. -/
private theorem table_length_witnessOf (j : Fin 8) :
    (tableAt (witnessOf prog s q) j).table.length =
      ![s.rows 0, s.rows 1, s.rows 2, s.rows 3, s.rows 4, s.rows 5, 2 ^ s.logMem,
        2 ^ prog.logSize] j := by
  fin_cases j <;> exact List.length_ofFn

/-- On admissible sizes, the witness read off a stack is within the caps. -/
theorem caps_witnessOf (hs : Admissible prog s) : Caps (witnessOf prog s q) := by
  obtain ⟨hmin, hmax, hrows, -⟩ := hs
  have himg := imageOf_witnessOf prog s q hmax
  refine ⟨?_, ?_, ?_, ⟨?_⟩⟩
  · rw [himg]
    exact hmin
  · rw [himg]
    exact hmax
  · intro t ht
    obtain ⟨j, rfl⟩ := mem_tables_iff.mp ht
    rw [table_length_witnessOf prog s q j]
    fin_cases j
    exacts [hrows 0, hrows 1, hrows 2, hrows 3, hrows 4, hrows 5,
      Nat.pow_le_pow_right (by norm_num) hmax,
      Nat.pow_le_pow_right (by norm_num) prog.logSize_le]
  · rw [memRows_witnessOf, himg]
    exact Array.size_ofFn

/-- The seed rows are the image, for an image given as a dependent pair. -/
private def SeedRowsAre {prog : KeccakVm.Program} (w : EnsembleWitness (kEnsemble prog))
    (d : (κ : ℕ) × MemImage κ) : Prop :=
  ∃ idx cntFin : Fin (2 ^ d.1) → K, memBlockRows w = List.ofFn fun i ↦
    (toElements (⟨idx i, cntFin i, #v[(d.2 i).limb 0, (d.2 i).limb 1, (d.2 i).limb 2]⟩ :
      MemRow K)).toArray

/-- `SeedRowsAreTheImage` is `SeedRowsAre` of the image the data names. -/
private theorem seedRows_iff {prog : KeccakVm.Program} (w : EnsembleWitness (kEnsemble prog)) :
    SeedRowsAreTheImage w ↔ SeedRowsAre w (imageOf w.data) := Iff.rfl

/-! ## The adaptor -/

/-- **The adaptor, soundness, without the Flock clause.** If the announced sizes are admissible
and the stack `q` satisfies the leanISA instance's constraints, bus, counts and public lines on
the input, then the witness read off `q` satisfies leanISA's constraint system on it but for the
`SHA3` rows' validity (`SatisfiedByB`). -/
theorem satisfiedByB_witnessOf {input : PublicInput} (hs : Admissible prog s)
    (hcv : (keccakIsaInstance prog s).ConstraintsVanish q)
    (hbal : (keccakIsaInstance prog s).Balanced q)
    (hcnt : (keccakIsaInstance prog s).CountsNonzero q)
    (hpl : (keccakIsaInstance prog s).PublicLinesHold input q) :
    SatisfiedByB prog input (witnessOf prog s q) := by
  have hmax : s.logMem ≤ maxLogMem := hs.2.1
  have hA := agrees_witnessOf prog s q
  have hpairs := (balanced_iff_pairs hA).mp hbal
  have himg := imageOf_witnessOf prog s q hmax
  obtain ⟨c00, c01, c10, c11, c20, c21⟩ := publicLines_cells prog s q hpl
  have hκ : s.logMem < 64 := lt_of_le_of_lt hmax (by decide)
  refine ⟨?_, constraints_witnessOf prog s q hcv, hpairs 0, hpairs 1, hpairs 2,
    (countsNonzero_iff hA).mpr hcnt, caps_witnessOf prog s q hs, ?_, ?_, ⟨_, rfl⟩, ?_, ?_⟩
  · show publicInputOf prog s q = PublicIO.ofInput input
    rw [publicInputOf, PublicIO.ofInput, c00, c01, c10, c11]
  · intro i hi
    show (memRowAt _ ((memBlockRowsOf prog s q)[i]'hi)).idx = gpow i
    simp only [memBlockRowsOf, List.getElem_ofFn, memRowAt_toElements]
  · rw [seedRows_iff, himg]
    refine ⟨fun x ↦ gpow x, fun x ↦ cell prog s q (memCol 3) x, ?_⟩
    show memBlockRowsOf prog s q = _
    simp only [memBlockRowsOf, imageWord, limb_ofLimbs]
    rfl
  · rw [himg]
    have := MemImage.read_gpow hκ (imageWord prog s q) ⟨0, Nat.two_pow_pos _⟩
    refine this.trans ?_
    show some (E.ofLimbs (cell0 prog s q 0) (cell0 prog s q 1) (cell0 prog s q 2)) = _
    rw [c00, c10, c20]
    rfl
  · rw [himg]
    have := MemImage.read_gpow hκ (imageWord prog s q)
      ⟨1, Nat.one_lt_two_pow s.logMem_pos.ne'⟩
    refine this.trans ?_
    show some (E.ofLimbs (cell1 prog s q 0) (cell1 prog s q 1) (cell1 prog s q 2)) = _
    rw [c01, c11, c21]
    rfl

/-- **The adaptor, soundness.** If the announced sizes are admissible and the stack `q` satisfies the Keccak VM's
relation on the input, then the witness read off `q` satisfies the Keccak VM's constraint statement on it. -/
theorem satisfiedBy_witnessOf (F : KeccakFlockSpec) {input : PublicInput} (hs : Admissible prog s)
    (h : KvHolds F prog s input q) :
    SatisfiedBy prog input (witnessOf prog s q) :=
  (satisfiedByB_witnessOf prog s q hs h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1).toSatisfiedBy
    (sha3RowsValid_witnessOf prog s q F h.2)

/-- **Soundness of the Keccak VM's relation, with the representation.** If the announced sizes are admissible
(`Admissible`), the program's last instruction is not a `JUMP` (`SentinelSafe`), and the stack `q` satisfies
`KvHolds F prog s input q`, then the witness read off `q` represents a valid execution of `prog` on `input`: its
image is the execution's memory and every step of the execution is a row of one of the six opcode tables. -/
theorem kvSoundness (F : KeccakFlockSpec) {input : PublicInput} (hs : Admissible prog s)
    (hsafe : SentinelSafe prog) (h : KvHolds F prog s input q) :
    ∃ t, AssignmentRepresents (witnessOf prog s q) t ∧ KeccakVm.ValidExecution prog input t :=
  constraintSoundness hsafe (satisfiedBy_witnessOf prog s q F hs h)

/-- **Soundness of the Keccak VM's relation.** Under admissible sizes and `SentinelSafe`, a stack satisfying
`KvHolds F prog s input q` has a valid execution of `prog` on `input`. -/
theorem kvSoundness_exists (F : KeccakFlockSpec) {input : PublicInput} (hs : Admissible prog s)
    (hsafe : SentinelSafe prog) (h : KvHolds F prog s input q) :
    ∃ t, KeccakVm.ValidExecution prog input t :=
  (kvSoundness prog s q F hs hsafe h).imp fun _ h ↦ h.2

end

end KeccakArith

end
