-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `formal/Lv42`'s `Arithmetization/Completeness/
-- Skeletons.lean` and the instruction rows of `Completeness/Rows.lean` (leanerVM `mumbai` f0393df4, MIT OR
-- Apache-2.0), for the Keccak VM.
module

public import KeccakArith.ASound
public import Lv42.Arithmetization.Completeness.Balance

/-!
# The rows of an execution, for the Keccak VM

Lv42's skeletons (`Skel`: the state stepped from and the instruction fetched there; `Trace.runSkels`,
`Trace.runRows`) at the Keccak VM's machine, and the raw row of an executing instruction (`rowOf`), in the table of its
opcode (`opComponent`), with the reads it makes (`readAddrs`, `readsOf`): `rowOf_sends`, the row sends `sendsOf`. The
five shared instructions use Lv42's rows (`xorRowOf`, …) and their `*_exec_sends`; `SHA3` uses `sha3RowOf` and
`sha3_exec_sends`, its 26 reads the cells `KeccakVm.executeWith` reads.
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Arithmetization KeccakVm
open Lv42.Semantics (Regs MemImage PublicInput DerefMode)
open Air.Flat (Component)

/-! ## Skeletons -/

/-- The skeleton of a table row: the state it is stepped from and the instruction fetched there. -/
structure Skel where
  pc : K
  fp : K
  ins : KeccakVm.Instr

/-- The state a skeleton is stepped from. -/
def Skel.regs (s : Skel) : Regs K := ⟨s.pc, s.fp⟩

/-- The skeletons of the run: the states stepped from, the final state dropped. -/
noncomputable def runSkels {prog : KeccakVm.Program} (t : KeccakVm.Trace prog) : List Skel :=
  t.regs.dropLast.filterMap fun r ↦ (prog.fetch r.pc).map fun ins ↦ ⟨r.pc, r.fp, ins⟩

/-- The rows of table `op` among the skeletons. -/
def Skel.onTable (op : Opcode) (l : List Skel) : List Skel :=
  l.filter fun s ↦ s.ins.opcode = op

/-- The number of rows of table `op` among the skeletons. -/
def Skel.count (op : Opcode) (l : List Skel) : ℕ := (Skel.onTable op l).length

/-- The rows of opcode `op` in the run of `t`. -/
noncomputable def runRows {prog : KeccakVm.Program} (t : KeccakVm.Trace prog) (op : Opcode) : ℕ :=
  (t.regs.dropLast.filter fun r ↦ (prog.fetch r.pc).map Instr.opcode = some op).length

theorem count_runSkels {prog : KeccakVm.Program} (t : KeccakVm.Trace prog) (op : Opcode) :
    Skel.count op (runSkels t) = runRows t op := by
  unfold Skel.count Skel.onTable runSkels runRows
  generalize t.regs.dropLast = l
  induction l with
  | nil => rfl
  | cons r l ih =>
    cases hf : prog.fetch r.pc with
    | none => simpa [List.filterMap_cons, List.filter_cons, hf] using ih
    | some ins =>
      by_cases ho : ins.opcode = op <;> simp [hf, ho, ih]

theorem runRows_le_steps {prog : KeccakVm.Program} {t : KeccakVm.Trace prog} {rf : Regs K}
    (h : KeccakVm.run prog t.image t.steps Regs.initial = some rf) (op : Opcode) :
    runRows t op ≤ t.steps := by
  unfold runRows
  refine (List.length_filter_le _ _).trans ?_
  rw [List.length_dropLast, KeccakVm.Trace.regs_length h]
  simp

theorem step_eq_none_of_fetch_eq_none {κ : ℕ} {prog : KeccakVm.Program} {L : MemImage κ} {r : Regs K}
    (h : prog.fetch r.pc = none) : KeccakVm.step prog L r = none := by
  rw [KeccakVm.step, h]; rfl

theorem runCount_eq_length {κ : ℕ} {prog : KeccakVm.Program} {L : MemImage κ} (op : Opcode) {n : ℕ}
    {r rf : Regs K} (h : KeccakVm.run prog L n r = some rf) :
    runCount prog L op n r = (((List.range n).filterMap fun m ↦ KeccakVm.run prog L m r).filter
      fun r₁ ↦ (prog.fetch r₁.pc).map Instr.opcode = some op).length := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have hpc := KeccakVm.pc_ne_finalPc_of_run_succ h
    rw [KeccakVm.run_succ_of_ne hpc] at h
    obtain ⟨r', hs, hr'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ins, hf⟩ : ∃ ins, prog.fetch r.pc = some ins := by
      cases hf : prog.fetch r.pc with
      | none => rw [step_eq_none_of_fetch_eq_none hf] at hs; exact absurd hs (by simp)
      | some ins => exact ⟨ins, rfl⟩
    have htail : ((List.range n).map Nat.succ).filterMap (fun m ↦ KeccakVm.run prog L m r) =
        (List.range n).filterMap fun m ↦ KeccakVm.run prog L m r' := by
      rw [List.filterMap_map]
      congr 1
      funext m
      simp only [Function.comp, KeccakVm.run_succ_of_ne hpc, hs, Option.bind_eq_bind, Option.bind_some]
    rw [List.range_succ_eq_map, List.filterMap_cons, KeccakVm.run_zero, htail]
    simp only [runCount, hf, hs, ih hr']
    by_cases ho : ins.opcode = op <;> simp [hf, ho, Nat.add_comm]

/-- The instructions of an opcode an execution executes are the rows of its table. -/
theorem count_eq_runRows {prog : KeccakVm.Program} {t : KeccakVm.Trace prog} {rf : Regs K}
    (h : KeccakVm.run prog t.image t.steps Regs.initial = some rf) (op : Opcode) :
    t.count op = runRows t op := by
  unfold KeccakVm.Trace.count runRows KeccakVm.Trace.regs
  rw [List.range_succ, List.filterMap_append]
  simp only [List.filterMap_cons, List.filterMap_nil, h, List.dropLast_concat]
  exact runCount_eq_length op h

/-- The six opcode tables in the ensemble's order. -/
def tableOpcodes : List Opcode := [.xor, .mulNative, .setConstant, .deref, .jump, .sha3]

theorem mem_tableOpcodes (o : Opcode) : o ∈ tableOpcodes := by
  cases o <;> decide

/-- The opcode of table `j`. -/
def tableOpcode (j : Fin 6) : Opcode := tableOpcodes.getD j .xor

/-! ## The cells an instruction reads -/

/-- The address of `SHA3` input cell `c`, as the row reads it (`kInAddr`). -/
def inAddrK (fp : K) (om : Fin 4 → K) (otail ocap : K) (c : ℕ) : K :=
  if h : c < 4 then fp * om ⟨c, h⟩
  else if c < 8 then g ^ (c - 4) * (fp * otail)
  else g ^ (c - 8) * (fp * ocap)

/-- The 26 cells a `SHA3` reads, in the row's order: the thirteen input cells, then the thirteen output cells. -/
def sha3Addrs (fp : K) (om : Fin 4 → K) (otail ocap oout : K) : List K :=
  (List.range 13).map (inAddrK fp om otail ocap) ++ (List.range 13).map fun c ↦ g ^ c * (fp * oout)

/-- The cells an instruction reads, in its row's order. -/
noncomputable def readAddrs {κ : ℕ} (mem : MemImage κ) (fp : K) : KeccakVm.Instr → List K
  | .xor oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .mulNative oA oB oC => [fp * oA, fp * oB, fp * oC]
  | .setConstant o _ => [fp * o]
  | .deref o1 o2 o3 _ => [fp * o1, (mem.limbsAt (fp * o1))[0] * o2, fp * o3]
  | .jump oc od of => [fp * oc, fp * od, fp * of]
  | .sha3 om otail ocap oout => sha3Addrs fp om otail ocap oout

/-- The reads of an instruction's row: each cell it reads, with its count and the limbs the image holds there. -/
noncomputable def readsOf {κ : ℕ} (mem : MemImage κ) (fp : K) (cnt : ℕ → K) (ins : KeccakVm.Instr) :
    List (K × K × Vector K 3) :=
  (readAddrs mem fp ins).mapIdx fun j a ↦ (a, cnt j, mem.limbsAt a)

/-! ## `SHA3` -/

/-- The counts of a `SHA3` row, from the count function. -/
def sha3Cnt (cnt : ℕ → K) : Vector K 26 := Vector.ofFn fun c ↦ cnt c

/-- A bound row's input cell `c` holds its cell's limbs. -/
theorem limbsAt_in {κ : ℕ} {mem : MemImage κ} {r : Sha3Row K} (hb : Sha3Bindings mem r) (c : Fin 13) :
    mem.limbsAt (kInAddr r c) = cellLimbs r.inLane c := by
  rw [kInAddr_eq, MemImage.limbsAt_eq_of_read (hb.in_eq c)]
  simp only [cellWord, limb_ofLimbs]
  exact Vector.ext fun i hi ↦ by interval_cases i <;> rfl

/-- A bound row's output cell `c` holds its cell's limbs. -/
theorem limbsAt_out {κ : ℕ} {mem : MemImage κ} {r : Sha3Row K} (hb : Sha3Bindings mem r) (c : Fin 13) :
    mem.limbsAt (g ^ c.val * (r.fp * r.oout)) = cellLimbs r.outLane c := by
  have h := hb.out_eq c
  rw [sha3OutOffset, show r.fp * (g ^ c.val * r.oout) = g ^ c.val * (r.fp * r.oout) by ring] at h
  rw [MemImage.limbsAt_eq_of_read h]
  simp only [cellWord, limb_ofLimbs]
  exact Vector.ext fun i hi ↦ by interval_cases i <;> rfl

/-- `kInAddr` of a row of `sha3RowOf` is `inAddrK` of its operands. -/
theorem kInAddr_sha3RowOf {κ : ℕ} (mem : MemImage κ) (pc fp : K) (om : Fin 4 → K) (otail ocap oout : K)
    (cnt : Vector K 26) (cntBc : K) (c : ℕ) :
    kInAddr (sha3RowOf mem pc fp om otail ocap oout cnt cntBc) c = inAddrK fp om otail ocap c := by
  unfold kInAddr inAddrK
  split_ifs <;> simp [sha3RowOf]

/-- The `SHA3` row of an execution sends the `SHA3` messages. -/
theorem sha3_exec_sends {κ : ℕ} {mem : MemImage κ} {pc fp : K} {om : Fin 4 → K} {otail ocap oout : K}
    {next : Regs K} (hexec : KeccakVm.execute mem ⟨pc, fp⟩ (.sha3 om otail ocap oout) = some next)
    (cnt : ℕ → K) (rbc : K) (data : ProverData K) :
    rowSends ⟨sha3Table⟩
        (Environment.fromArray (rawRow (sha3RowOf mem pc fp om otail ocap oout (sha3Cnt cnt) rbc)) data) =
      sendsOf pc fp next rbc (KeccakVm.entry (.sha3 om otail ocap oout))
        (readsOf mem fp cnt (.sha3 om otail ocap oout)) := by
  have hr := sha3RowOf_refines hexec (sha3Cnt cnt) rbc
  obtain ⟨hb, -, hnext⟩ := (sha3_refines_iff _ _ _).mp hr
  rw [rowSends_mk, sha3_sends_gen _ _ _ _ (eval_rowVar _ data), hnext]
  have hom : (Vector.ofFn om).get = om := funext fun i ↦ by simp [Vector.get]; rfl
  have hinstr : (sha3RowOf mem pc fp om otail ocap oout (sha3Cnt cnt) rbc).instr = .sha3 om otail ocap oout := by
    simp only [sha3RowOf, Sha3Row.instr, Sha3Row.omF, hom]
  rw [hinstr]
  suffices hl : sha3Reads (sha3RowOf mem pc fp om otail ocap oout (sha3Cnt cnt) rbc) =
      readsOf mem fp cnt (.sha3 om otail ocap oout) by
    rw [hl]
    rfl
  have hinN : ∀ c < 13, cellLimbs (sha3RowOf mem pc fp om otail ocap oout (sha3Cnt cnt) rbc).inLane c =
      mem.limbsAt (inAddrK fp om otail ocap c) := fun c hc ↦ by
    rw [← kInAddr_sha3RowOf mem pc fp om otail ocap oout (sha3Cnt cnt) rbc c]
    exact (limbsAt_in hb ⟨c, hc⟩).symm
  have houtN : ∀ c < 13, cellLimbs (sha3RowOf mem pc fp om otail ocap oout (sha3Cnt cnt) rbc).outLane c =
      mem.limbsAt (g ^ c * ((sha3RowOf mem pc fp om otail ocap oout (sha3Cnt cnt) rbc).fp *
        (sha3RowOf mem pc fp om otail ocap oout (sha3Cnt cnt) rbc).oout)) := fun c hc ↦
    (limbsAt_out hb ⟨c, hc⟩).symm
  simp only [sha3Reads, kInAddr_sha3RowOf, hinN _ (by decide : 0 < 13), hinN _ (by decide : 1 < 13),
    hinN _ (by decide : 2 < 13), hinN _ (by decide : 3 < 13), hinN _ (by decide : 4 < 13),
    hinN _ (by decide : 5 < 13), hinN _ (by decide : 6 < 13), hinN _ (by decide : 7 < 13),
    hinN _ (by decide : 8 < 13), hinN _ (by decide : 9 < 13), hinN _ (by decide : 10 < 13),
    hinN _ (by decide : 11 < 13), hinN _ (by decide : 12 < 13),
    houtN _ (by decide : 0 < 13), houtN _ (by decide : 1 < 13),
    houtN _ (by decide : 2 < 13), houtN _ (by decide : 3 < 13), houtN _ (by decide : 4 < 13),
    houtN _ (by decide : 5 < 13), houtN _ (by decide : 6 < 13), houtN _ (by decide : 7 < 13),
    houtN _ (by decide : 8 < 13), houtN _ (by decide : 9 < 13), houtN _ (by decide : 10 < 13),
    houtN _ (by decide : 11 < 13), houtN _ (by decide : 12 < 13)]
  simp only [sha3RowOf, sha3Cnt, Vector.getElem_ofFn]
  simp only [readsOf, readAddrs, sha3Addrs, List.range_succ, List.range_zero, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, List.mapIdx_cons, List.mapIdx_nil,
    Nat.reduceAdd, zero_add]

/-! ## Every cell an instruction reads is an address -/

theorem readAddrs_valid {κ : ℕ} {mem : MemImage κ} {pc fp : K} {ins : KeccakVm.Instr} {next : Regs K}
    (hexec : KeccakVm.execute mem ⟨pc, fp⟩ ins = some next) :
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
  | sha3 om otail ocap oout =>
    obtain ⟨hb, -, -⟩ := (sha3_refines_iff _ _ _).mp (sha3RowOf_refines hexec (sha3Cnt fun _ ↦ 1) 1)
    intro a ha
    simp only [readAddrs, sha3Addrs, List.mem_append, List.mem_map, List.mem_range] at ha
    rcases ha with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · have h := hb.in_eq ⟨c, hc⟩
      rw [← kInAddr_eq, kInAddr_sha3RowOf] at h
      exact ⟨_, h⟩
    · have h := hb.out_eq ⟨c, hc⟩
      rw [sha3OutOffset, show (sha3RowOf mem pc fp om otail ocap oout (sha3Cnt fun _ ↦ 1) 1).fp *
        (g ^ c * (sha3RowOf mem pc fp om otail ocap oout (sha3Cnt fun _ ↦ 1) 1).oout) =
          g ^ c * (fp * oout) by simp only [sha3RowOf]; ring] at h
      exact ⟨_, h⟩

/-! ## The row of an instruction -/

/-- The table of each opcode, in the ensemble's order (`kEnsemble`). -/
def opComponent : Opcode → Component K
  | .xor => ⟨xorTable⟩
  | .mulNative => ⟨mulTable⟩
  | .setConstant => ⟨setTable⟩
  | .deref => ⟨derefTable⟩
  | .jump => ⟨jumpTable⟩
  | .sha3 => ⟨sha3Table⟩

/-- The width of a raw row of each opcode's table. -/
def opWidth : Opcode → ℕ
  | .xor => size XorRow
  | .mulNative => size MulRow
  | .setConstant => size SetRow
  | .deref => size DerefRow
  | .jump => size JumpRow + 2
  | .sha3 => size Sha3Row

/-- The raw row of an instruction executed from `(pc, fp)` over the image `mem`. -/
noncomputable def rowOf {κ : ℕ} (mem : MemImage κ) (pc fp : K) (cnt : ℕ → K) (rbc : K) :
    KeccakVm.Instr → Array K
  | .xor oA oB oC => rawRow (xorRowOf mem pc fp oA oB oC (cnt 0) (cnt 1) (cnt 2) rbc)
  | .mulNative oA oB oC => rawRow (mulRowOf mem pc fp oA oB oC (cnt 0) (cnt 1) (cnt 2) rbc)
  | .setConstant o k => rawRow (setRowOf pc fp o k (cnt 0) rbc)
  | .deref o1 o2 o3 mode =>
      rawRow (derefRowOf mem pc fp o1 o2 o3 mode (cnt 0) (cnt 1) (cnt 2) rbc)
  | .jump oc od of =>
      jumpRaw (jumpRowOf mem pc fp oc od of (cnt 0) (cnt 1) (cnt 2) rbc)
        (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else ((mem.limbsAt (fp * oc))[0])⁻¹)
        (if (mem.limbsAt (fp * oc))[0] = 0 then 0 else 1)
  | .sha3 om otail ocap oout => rawRow (sha3RowOf mem pc fp om otail ocap oout (sha3Cnt cnt) rbc)

theorem rowOf_size {κ : ℕ} (mem : MemImage κ) (pc fp : K) (cnt : ℕ → K) (rbc : K) (ins : KeccakVm.Instr) :
    (rowOf mem pc fp cnt rbc ins).size = opWidth ins.opcode := by
  cases ins <;> simp [rowOf, opWidth, Instr.opcode, rawRow_size, jumpRaw]

/-- **The row of an executing instruction sends `sendsOf`.** -/
theorem rowOf_sends {κ : ℕ} {mem : MemImage κ} {pc fp : K} {ins : KeccakVm.Instr} {next : Regs K}
    (hexec : KeccakVm.execute mem ⟨pc, fp⟩ ins = some next) (cnt : ℕ → K) (rbc : K)
    (data : ProverData K) :
    rowSends (opComponent ins.opcode)
        (Environment.fromArray (rowOf mem pc fp cnt rbc ins) data) =
      sendsOf pc fp next rbc (KeccakVm.entry ins) (readsOf mem fp cnt ins) := by
  cases ins with
  | xor oA oB oC =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, xor_exec_sends hexec]
    simp [readsOf, readAddrs, KeccakVm.entry]
  | mulNative oA oB oC =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, mul_exec_sends hexec]
    simp [readsOf, readAddrs, KeccakVm.entry]
  | setConstant o k =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, set_exec_sends hexec]
    simp [readsOf, readAddrs, KeccakVm.entry]
  | deref o1 o2 o3 mode =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, deref_exec_sends hexec]
    simp [readsOf, readAddrs, KeccakVm.entry]
  | jump oc od of =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, jump_exec_sends hexec]
    simp [readsOf, readAddrs, KeccakVm.entry]
  | sha3 om otail ocap oout =>
    simp only [Instr.opcode, opComponent]
    rw [rowOf, sha3_exec_sends hexec]

end KeccakArith

end
