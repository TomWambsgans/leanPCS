-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `formal/Lv42`'s `Arithmetization/Completeness/Witness.lean`
-- (leanerVM `mumbai` f0393df4, MIT OR Apache-2.0), for the Keccak VM.
module

public import KeccakArith.CBus

/-!
# The witness of an execution, for the Keccak VM

Lv42's `skelWitness` at `kEnsemble`: the image as prover data (`imageData`), the six opcode tables holding the rows of
the skeletons of their opcode, the memory block of the image and the bytecode block of the program (`kBytecodeRowOf`),
with the finalize counts the reads make.
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Arithmetization KeccakVm
open Lv42.Semantics (Regs MemImage PublicInput)
open Lv42.Parameters (minLogMem maxLogMem maxLogRows)
open Air.Flat (Component EnsembleWitness)

/-! ## The prover data of an image -/

/-- The prover data holding an image: its words as the `"mem"` table, one row of three limbs
each. -/
def imageData {κ : ℕ} (img : MemImage κ) : ProverData K := fun _ n ↦
  match n with
  | 3 => Array.ofFn fun i : Fin (2 ^ κ) ↦ #v[(img i).limb 0, (img i).limb 1, (img i).limb 2]
  | _ => #[]

/-- The `"mem"` table of the data, read back. By `unfold` and not by `rfl`: the match on the arity
`3` is stuck for definitional unfolding, which then unrolls `Array.ofFn` over the `2^κ` rows. -/
theorem memRows_imageData {κ : ℕ} (img : MemImage κ) :
    memRows (imageData img) =
      Array.ofFn fun i : Fin (2 ^ κ) ↦ #v[(img i).limb 0, (img i).limb 1, (img i).limb 2] := by
  unfold memRows imageData
  rfl

/-- The memory log-size the data names is the image's. -/
theorem imageData_logSize {κ : ℕ} (img : MemImage κ) (hκ : κ ≤ maxLogMem) :
    (imageOf (imageData img)).1 = κ := by
  show min (Nat.log 2 (memRows (imageData img)).size) maxLogMem = κ
  rw [memRows_imageData, Array.size_ofFn, Nat.log_pow (by norm_num)]
  exact Nat.min_eq_left hκ

/-- The data is well shaped. -/
theorem imageData_wellShaped {κ : ℕ} (img : MemImage κ) (hκ : κ ≤ maxLogMem) :
    WellShapedData (imageData img) :=
  ⟨by rw [imageData_logSize img hκ, memRows_imageData, Array.size_ofFn]⟩

/-- Row `k` of the table, through `getElem?`: a `getElem` with a bound on the `2^κ`-row table
makes both the elaborator and the kernel unroll it. -/
theorem imageData_row {κ : ℕ} (img : MemImage κ) (k : ℕ) (hk : k < 2 ^ κ) :
    (memRows (imageData img))[k]? =
      some #v[(img ⟨k, hk⟩).limb 0, (img ⟨k, hk⟩).limb 1, (img ⟨k, hk⟩).limb 2] := by
  rw [memRows_imageData, Array.getElem?_ofFn, dite_eq_left hk]

/-- Every word the data names is the image's. -/
theorem imageData_apply' {κ : ℕ} (img : MemImage κ) (hκ : κ ≤ maxLogMem) (k : ℕ)
    (hk : k < 2 ^ (imageOf (imageData img)).1) :
    (imageOf (imageData img)).2 ⟨k, hk⟩ =
      img ⟨k, by rw [imageData_logSize img hκ] at hk; exact hk⟩ := by
  have hk' : k < 2 ^ κ := by rw [imageData_logSize img hκ] at hk; exact hk
  conv_rhs => rw [← ofLimbs_limb (img ⟨k, hk'⟩)]
  refine imageOf_apply (imageData_wellShaped img hκ) ⟨k, hk⟩
    (v := #v[(img ⟨k, hk'⟩).limb 0, (img ⟨k, hk'⟩).limb 1, (img ⟨k, hk'⟩).limb 2]) ?_
  rw [Array.getElem_eq_iff]
  exact imageData_row img k hk'

/-- The image the data names, as one equality of dependent pairs: what every conjunct over
`imageOf w.data` is rewritten with, so that nothing compares the data's log-size against `κ`
definitionally (which would unroll the `2^κ` rows). -/
theorem imageOf_imageData {κ : ℕ} (img : MemImage κ) (hκ : κ ≤ maxLogMem) :
    imageOf (imageData img) = ⟨κ, img⟩ := by
  have hκ' : (imageOf (imageData img)).1 = κ := imageData_logSize img hκ
  have hpow : 2 ^ (imageOf (imageData img)).1 = 2 ^ κ := by rw [hκ']
  have hf : ∀ i, (imageOf (imageData img)).2 i = img (Fin.cast hpow i) := fun i ↦
    imageData_apply' img hκ i i.isLt
  revert hκ' hpow hf
  generalize imageOf (imageData img) = s
  obtain ⟨κ', img'⟩ := s
  intro hκ' hpow hf
  dsimp only at hκ' hpow hf
  subst hκ'
  exact congrArg _ (funext fun i ↦ (hf i).trans (congrArg img (Fin.ext rfl)))

/-! ## The rows of a list of skeletons -/

/-- The rows of a list of skeletons over the image `img`, numbered from zero. -/
noncomputable def skelRows {κ : ℕ} (img : MemImage κ) (S : List Skel) : List PRow :=
  mkRows img (fun _ ↦ 0) (fun _ ↦ 0) S

/-- How many times each memory cell is read by the rows of `S`: the exponent of its finalize
count. -/
noncomputable def skelMemFin {κ : ℕ} (img : MemImage κ) (S : List Skel) : K → ℕ :=
  readBump (fun _ ↦ 0) (S.flatMap fun sk ↦ readAddrs img sk.fp sk.ins)

/-- How many times each bytecode slot is read by the rows of `S`. -/
noncomputable def skelBcFin (S : List Skel) : K → ℕ :=
  readBump (fun _ ↦ 0) (S.map (·.pc))

/-- A row of the rows of `S` is a row of a skeleton of `S`. -/
theorem mem_mkRows_sk {κ : ℕ} {img : MemImage κ} {sm sb : K → ℕ} {S : List Skel} {r : PRow}
    (h : r ∈ mkRows img sm sb S) : r.sk ∈ S := by
  rw [← mkRows_sk img sm sb S]
  exact List.mem_map_of_mem h

/-! ## The tables -/

/-- The table of an opcode: the raw rows of the rows of `R` whose instruction has the opcode. -/
noncomputable def skOpTable {κ : ℕ} (img : MemImage κ) (data : ProverData K) (R : List PRow)
    (op : Opcode) : Air.Flat.Table K where
  component := opComponent op
  width := opWidth op
  table := (R.filter fun r ↦ r.sk.ins.opcode = op).map (PRow.raw img)
  data := data
  uniform_width := by
    intro row hrow
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
    have h := (List.mem_filter.mp hr).2
    simp only [decide_eq_true_eq] at h
    simp only [PRow.raw, rowOf_size, h]

/-- The memory block: one row per cell, `(g^i, g^(fin (g^i)), the word at i)`. -/
noncomputable def memBlock {κ : ℕ} (img : MemImage κ) (data : ProverData K) (fin : K → ℕ) :
    Air.Flat.Table K where
  component := ⟨memTable⟩
  width := size MemRow
  table := List.ofFn fun i : Fin (2 ^ κ) ↦ rawRow (memRowOf img i (g ^ fin (gpow i)))
  data := data
  uniform_width := by
    intro r hr
    rw [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    exact rawRow_size _

/-- The bytecode block: one row per slot of the program. -/
noncomputable def bcBlock (prog : KeccakVm.Program) (data : ProverData K) (fin : K → ℕ) :
    Air.Flat.Table K where
  component := ⟨bytecodeTable⟩
  width := size BytecodeRow
  table := List.ofFn fun i : Fin (2 ^ prog.logSize) ↦
    rawRow (kBytecodeRowOf prog i (g ^ fin (gpow i)))
  data := data
  uniform_width := by
    intro r hr
    rw [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    exact rawRow_size _

/-- **The witness of a list of skeletons.** -/
noncomputable def skelWitness (prog : KeccakVm.Program) (input : PublicInput) {κ : ℕ} (img : MemImage κ)
    (S : List Skel) : EnsembleWitness (kEnsemble prog) where
  tables := [skOpTable img (imageData img) (skelRows img S) .xor,
    skOpTable img (imageData img) (skelRows img S) .mulNative,
    skOpTable img (imageData img) (skelRows img S) .setConstant,
    skOpTable img (imageData img) (skelRows img S) .deref,
    skOpTable img (imageData img) (skelRows img S) .jump,
    skOpTable img (imageData img) (skelRows img S) .sha3,
    memBlock img (imageData img) (skelMemFin img S),
    bcBlock prog (imageData img) (skelBcFin S)]
  data := imageData img
  publicInput := PublicIO.ofInput input
  same_length := rfl
  same_circuits := by
    intro i hi
    have hi' : i < 8 := hi
    interval_cases i <;> rfl
  same_data := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end KeccakArith

end
