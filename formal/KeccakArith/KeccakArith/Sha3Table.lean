-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. Written after `formal/Lv42`'s
-- `Arithmetization/Tables/Blake2s.lean` (leanerVM `mumbai` f0393df4, MIT OR Apache-2.0); the `SHA3` table is
-- leanVM `9d50c92a3`'s (`crates/leanvm/statement/src/layout.rs::{SHA3_COLUMNS, flushes_sha3}`).
module

public import KeccakVm.Instance
public import Lv42.Arithmetization.Tables.Basic
public import Clean.Circuit.Formal
public import Clean.Circuit.Loops
public import Clean.Utils.Tactics.CircuitProofStart

/-!
# The `SHA3` table as a Clean component

The Keccak VM's `SHA3` table (`KeccakVm.Sha3Table`), written as a Clean component in the form of Lv42's
`BLAKE2S` table (`Lv42.Arithmetization.blake2sTable`).

**The row** `Sha3Row` is the 86 columns of `SHA3_COLUMNS`, in order: `pc, fp`, the operands `o_m₀ … o_m₃`
(`om`), `o_tail, o_cap, o_out`, the 25 input lanes, the 25 output lanes, the 26 cell read counts, the bytecode
count. Its flat layout is `KeccakVm.Sha3Table`'s column numbering (`sha3Row_offsets`).

**The component** `sha3Table` pulls `(pc, fp)`, pushes and returns `(g·pc, fp)`, reads the bytecode entry
`(g^5, o_m₀, …, o_m₃, o_tail, o_cap, o_out)` at `pc`, and reads the 13 input cells and the 13 output cells with
Lv42's `memRead`: cell `c` at `fp · sha3InOffset c` (resp. `fp · sha3OutOffset c`), holding `(lane lo, lane hi, 0)`
for its lanes `sha3CellLanes c` (`0` for the lone cell's missing high lane).

**The relation.** `Sha3Bindings mem r`: every read cell is the row's cell word (`inWord`, `outWord`).
`Sha3Relation r`: the output lanes are `sha3Step` of the input lanes (`laneState`), the table's `Assumptions`, which
`KeccakAux` and `KeccakFlockSpec.step_of_holds` supply (`KeccakArith.RowSound`). `Sha3Refines mem r next`: the
bindings, and `KeccakVm.executeWith mem.read` executes `SHA3` with the row's operands from `(pc, fp)` to `next`.
`sha3_refines_iff`: `Sha3Refines` is the bindings, the relation and `next = (g·pc, fp)`: the canonicality of the read
cells (top limb zero, the lone cell's middle limb zero) is the literal zeros of the bus tuples, and `END_BIT` is inside
`sha3Step`.

**Rows from executions.** `sha3RowOf mem …` reads the lanes back from the image (`laneOfImage`), and
`sha3RowOf_refines`: a valid execution of `SHA3` is represented by it, with any counts.
-/

@[expose] public section

namespace KeccakArith

open LeanVM.Parameters Lv42.Parameters Lv42.Semantics Lv42.Arithmetization KeccakVm
abbrev KState := LeanVM.Semantics.KeccakState

/-! ## The row -/

/-- The `SHA3` columns, in `SHA3_COLUMNS`' order. -/
structure Sha3Row (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  /-- The operands `o_m₀ … o_m₃`. -/
  om : Vector F 4
  /-- The operand `o_tail`. -/
  otail : F
  /-- The operand `o_cap`. -/
  ocap : F
  /-- The operand `o_out`. -/
  oout : F
  /-- The 25 input lanes. -/
  inLane : Vector F 25
  /-- The 25 output lanes. -/
  outLane : Vector F 25
  /-- The read counts of the 13 input cells, then of the 13 output cells. -/
  cnt : Vector F 26
  /-- The read count of the bytecode entry. -/
  cntBc : F
  deriving ProvableStruct

/-- A lane of a lane vector by its number, `0` past the end. -/
def laneAt {α : Type} [Zero α] (v : Vector α 25) (l : ℕ) : α := if h : l < 25 then v[l] else 0

/-- The three limbs of state cell `c` over the lanes `lane` (`sha3CellLanes`): its low lane, its high lane (`0` for
the lone cell), `0`. -/
def cellLimbs {α : Type} [Zero α] (lane : Vector α 25) (c : ℕ) : Vector α 3 :=
  #v[laneAt lane (sha3CellLanes c).1,
    match (sha3CellLanes c).2 with
    | some h => laneAt lane h
    | none => 0,
    0]

/-- The word of state cell `c` over the lanes `lane`. -/
def cellWord (lane : Vector K 25) (c : ℕ) : E :=
  E.ofLimbs (cellLimbs lane c)[0] (cellLimbs lane c)[1] (cellLimbs lane c)[2]

/-- The state the lanes hold. -/
def laneState (lane : Vector K 25) : KState := Vector.ofFn fun l ↦ (lane[l]).lane

/-! ## The addresses, as expressions -/

/-- The address of input cell `c`: `fp · o_m_c`, `g^(c−4) · (fp · o_tail)`, `g^(c−8) · (fp · o_cap)`
(`KeccakVm.Sha3Table.inAddr`). -/
def inAddrE (r : Var Sha3Row K) (c : ℕ) : Expression K :=
  if h : c < 4 then r.fp * r.om[c]
  else if c < 8 then Expression.const (g ^ (c - 4)) * (r.fp * r.otail)
  else Expression.const (g ^ (c - 8)) * (r.fp * r.ocap)

/-- The address of output cell `c`: `g^c · (fp · o_out)`. -/
def outAddrE (r : Var Sha3Row K) (c : ℕ) : Expression K := Expression.const (g ^ c) * (r.fp * r.oout)

/-! ## The relation -/

/-- The row's operands `o_m₀ … o_m₃` as the instruction's. -/
def Sha3Row.omF (r : Sha3Row K) : Fin 4 → K := r.om.get

/-- The instruction a row names. -/
def Sha3Row.instr (r : Sha3Row K) : KeccakVm.Instr := .sha3 r.omF r.otail r.ocap r.oout

/-- The output lanes are `sha3Step` of the input lanes: what `KeccakAux` and the Keccak-f block give a row
(`KeccakArith.RowSound`). The table's named assumption. -/
def Sha3Relation (r : Sha3Row K) : Prop := laneState r.outLane = sha3Step (laneState r.inLane)

/-- The row's bindings to an image: the 26 cells it reads hold its cell words. -/
structure Sha3Bindings {κ : ℕ} (mem : MemImage κ) (r : Sha3Row K) : Prop where
  /-- Input cell `c` holds the input lanes' cell `c`. -/
  in_eq : ∀ c : Fin 13, mem.read (r.fp * sha3InOffset r.omF r.otail r.ocap c) = some (cellWord r.inLane c)
  /-- Output cell `c` holds the output lanes' cell `c`. -/
  out_eq : ∀ c : Fin 13, mem.read (r.fp * sha3OutOffset r.oout c) = some (cellWord r.outLane c)

/-- The relation a `SHA3` row refines: it is bound to the image, and from its registers the Keccak VM executes the
`SHA3` it names to `next`. -/
structure Sha3Refines {κ : ℕ} (mem : MemImage κ) (r : Sha3Row K) (next : Regs K) : Prop where
  /-- The row is bound to the image. -/
  bindings : Sha3Bindings mem r
  /-- The instruction executes. -/
  exec_eq : KeccakVm.executeWith mem.read ⟨r.pc, r.fp⟩ r.instr = some next

/-! ## Reading thirteen cells -/

/-- The fold of `readCells` over a list of cells. -/
private theorem foldr_readCells_eq_some (read : K → Option E) (fp : K) (offset : Fin 13 → K)
    (L : List (Fin 13)) (f : Fin 13 → E) :
    L.foldr (fun (c : Fin 13) (acc : Option (Fin 13 → E)) ↦ do
        let v ← read (fp * offset c)
        let rest ← acc
        pure fun c' ↦ if c' = c then v else rest c') (some fun _ ↦ 0) = some f ↔
      (∀ c ∈ L, read (fp * offset c) = some (f c)) ∧ ∀ c ∉ L, f c = 0 := by
  induction L generalizing f with
  | nil =>
    simp only [List.foldr_nil, Option.some.injEq, List.not_mem_nil, false_imp_iff, implies_true,
      not_false_eq_true, forall_const, true_and]
    exact ⟨fun h c ↦ by rw [← h], fun h ↦ funext fun c ↦ (h c).symm⟩
  | cons a L ih =>
    rw [List.foldr_cons]
    constructor
    · intro h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨v, hv, rest, hrest, rfl⟩ := h
      obtain ⟨hL, hn⟩ := (ih rest).mp hrest
      refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
      · by_cases h : c = a
        · subst h; simpa using hv
        · rcases List.mem_cons.mp hc with rfl | hc
          · exact absurd rfl h
          · simpa [h] using hL c hc
      · have hca : c ≠ a := fun h ↦ hc (by simp [h])
        have hcL : c ∉ L := fun h ↦ hc (List.mem_cons_of_mem _ h)
        simp [hca, hn c hcL]
    · rintro ⟨hL, hn⟩
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq]
      refine ⟨f a, hL a (by simp), fun c ↦ if c ∈ L then f c else 0,
        (ih _).mpr ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩, funext fun c ↦ ?_⟩
      · simpa [hc] using hL c (List.mem_cons_of_mem _ hc)
      · simp [hc]
      · by_cases h : c = a
        · subst h; simp
        · by_cases hc : c ∈ L
          · simp [h, hc]
          · simp [h, hc, hn c (by simp [h, hc])]

/-- `readCells` succeeds exactly when each of the thirteen cells reads, and returns them. -/
theorem readCells_eq_some (read : K → Option E) (fp : K) (offset : Fin 13 → K) (cells : Fin 13 → E) :
    readCells read fp offset = some cells ↔ ∀ c, read (fp * offset c) = some (cells c) := by
  unfold readCells
  rw [foldr_readCells_eq_some]
  simp only [List.mem_finRange, forall_const, not_true_eq_false, false_imp_iff, and_true]

/-! ## The cells and the state -/

/-- A lane word read back as a field element. -/
@[simp] theorem ofLane_lane (a : K) : K.ofLane a.lane = a := rfl

/-- Lane `i < 25` of a state is its entry `i`. -/
theorem lane_eq_getElem (s : KState) (i : ℕ) (h : i < 25) : LeanVM.Semantics.Keccak.lane s i = s[i] := by
  simp [LeanVM.Semantics.Keccak.lane, Array.getD, h]

/-- A state is read back off its cells. -/
theorem stateOfCells_cellsOfState (s : KState) : stateOfCells (cellsOfState s) = s := by
  apply Vector.ext
  intro l hl
  simp only [stateOfCells, Vector.getElem_ofFn]
  interval_cases l <;>
    simp [laneCell, cellsOfState, sha3CellLanes, lane_eq_getElem, K.lane, K.ofLane]

/-- The state of the cell words is the lanes' state. -/
theorem stateOfCells_cellWord (lane : Vector K 25) :
    stateOfCells (fun c ↦ cellWord lane c) = laneState lane := by
  unfold stateOfCells laneState
  congr 1
  funext l
  fin_cases l <;> rfl

/-- The cell words of a state's lanes are the state's cells. -/
theorem cellsOfState_laneState (lane : Vector K 25) (c : Fin 13) :
    cellsOfState (laneState lane) c = cellWord lane c := by
  fin_cases c <;>
    simp [cellsOfState, cellWord, cellLimbs, laneState, laneAt, sha3CellLanes, lane_eq_getElem, ofLane_lane]

/-- The cell words are canonical: their top limb is zero, and the lone cell's middle limb. -/
theorem sha3Canonical_cellWord (lane : Vector K 25) (c : Fin 13) : Sha3Canonical c (cellWord lane c) := by
  fin_cases c <;> exact ⟨rfl, by simp [sha3CellLanes, cellWord, cellLimbs]⟩

/-- **`Sha3Refines`, expanded**: the bindings, the relation, and the successor `(g·pc, fp)`. -/
theorem sha3_refines_iff {κ : ℕ} (mem : MemImage κ) (r : Sha3Row K) (next : Regs K) :
    Sha3Refines mem r next ↔ Sha3Bindings mem r ∧ Sha3Relation r ∧ next = Regs.next ⟨r.pc, r.fp⟩ := by
  constructor
  · rintro ⟨hb, hexec⟩
    refine ⟨hb, ?_⟩
    have hin := (readCells_eq_some mem.read r.fp _ _).mpr hb.in_eq
    have hout := (readCells_eq_some mem.read r.fp _ _).mpr hb.out_eq
    simp only [Sha3Row.instr, KeccakVm.executeWith, hin, hout, Option.bind_eq_bind, Option.bind_some,
      guard_bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hexec
    obtain ⟨⟨-, hcells⟩, hnext⟩ := hexec
    refine ⟨?_, hnext.symm⟩
    have h : cellsOfState (laneState r.outLane) = cellsOfState (sha3Step (laneState r.inLane)) := by
      funext c
      rw [cellsOfState_laneState, ← stateOfCells_cellWord r.inLane, ← hcells c]
    have := congrArg stateOfCells h
    rwa [stateOfCells_cellsOfState, stateOfCells_cellsOfState] at this
  · rintro ⟨hb, hrel, rfl⟩
    refine ⟨hb, ?_⟩
    have hin := (readCells_eq_some mem.read r.fp _ _).mpr hb.in_eq
    have hout := (readCells_eq_some mem.read r.fp _ _).mpr hb.out_eq
    simp only [Sha3Row.instr, KeccakVm.executeWith, hin, hout, Option.bind_eq_bind, Option.bind_some,
      guard_bind_eq_some_iff, Option.pure_def, and_true]
    refine ⟨sha3Canonical_cellWord r.inLane, fun c ↦ ?_⟩
    rw [stateOfCells_cellWord, ← hrel, cellsOfState_laneState]

/-! ## Rows from executions -/

/-- The lanes thirteen cells hold, as field elements (`stateOfCells`). -/
def lanesOf (cells : Fin 13 → E) : Vector K 25 := Vector.ofFn fun l ↦ K.ofLane (stateOfCells cells)[l]

/-- The cells of a state are canonical. -/
theorem sha3Canonical_cellsOfState (S : KState) (c : Fin 13) : Sha3Canonical c (cellsOfState S c) := by
  fin_cases c <;> exact ⟨rfl, by simp [sha3CellLanes, cellsOfState]⟩

/-- Canonical cells are the cell words of the lanes they hold. -/
theorem cellWord_lanesOf {cells : Fin 13 → E} (h : ∀ c, Sha3Canonical c (cells c)) (c : Fin 13) :
    cellWord (lanesOf cells) c = cells c := by
  have h2 : ∀ c, (cells c).limb 2 = 0 := fun c ↦ (h c).1
  have h81 : (cells 8).limb 1 = 0 := (h 8).2 rfl
  refine E.ext fun i ↦ ?_
  fin_cases c <;> fin_cases i <;>
    simp [cellWord, cellLimbs, laneAt, lanesOf, stateOfCells, laneCell, sha3CellLanes, ofLane_lane, h2, h81]

/-- The state of the lanes thirteen cells hold. -/
theorem laneState_lanesOf (cells : Fin 13 → E) : laneState (lanesOf cells) = stateOfCells cells := by
  apply Vector.ext
  intro l hl
  simp [laneState, lanesOf]
  rfl

/-- The thirteen words of the image at the frame-relative offsets `offset`, `0` where a read fails. -/
noncomputable def cellsAt {κ : ℕ} (mem : MemImage κ) (fp : K) (offset : Fin 13 → K) : Fin 13 → E :=
  fun c ↦ (mem.read (fp * offset c)).getD 0

/-- The row of an execution of `SHA3 om otail ocap oout` from `(pc, fp)` over the image `mem`: the registers, the
operands, the lanes read back from the image, and the counts as parameters. -/
noncomputable def sha3RowOf {κ : ℕ} (mem : MemImage κ) (pc fp : K) (om : Fin 4 → K) (otail ocap oout : K)
    (cnt : Vector K 26) (cntBc : K) : Sha3Row K :=
  ⟨pc, fp, Vector.ofFn om, otail, ocap, oout, lanesOf (cellsAt mem fp (sha3InOffset om otail ocap)),
    lanesOf (cellsAt mem fp (sha3OutOffset oout)), cnt, cntBc⟩

/-- **A valid execution of `SHA3` is represented by `sha3RowOf`**, with any counts: `Sha3Cells` makes every read
cell canonical, so its lanes read it back. -/
theorem sha3RowOf_refines {κ : ℕ} {mem : MemImage κ} {pc fp : K} {om : Fin 4 → K} {otail ocap oout : K}
    {next : Regs K} (hexec : KeccakVm.executeWith mem.read ⟨pc, fp⟩ (.sha3 om otail ocap oout) = some next)
    (cnt : Vector K 26) (cntBc : K) :
    Sha3Refines mem (sha3RowOf mem pc fp om otail ocap oout cnt cntBc) next := by
  have h := hexec
  simp only [KeccakVm.executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨input, hin, output, hout, u, hu, -⟩ := h
  obtain ⟨hcan, hcells⟩ := guard_eq_some hu
  have hin' := (readCells_eq_some _ _ _ _).mp hin
  have hout' := (readCells_eq_some _ _ _ _).mp hout
  have hci : cellsAt mem fp (sha3InOffset om otail ocap) = input := funext fun c ↦ by simp [cellsAt, hin' c]
  have hco : cellsAt mem fp (sha3OutOffset oout) = output := funext fun c ↦ by simp [cellsAt, hout' c]
  have hcan' : ∀ c, Sha3Canonical c (output c) := fun c ↦ by
    rw [hcells c]; exact sha3Canonical_cellsOfState _ c
  have hom : (Vector.ofFn om).get = om := funext fun i ↦ by simp [Vector.get]; rfl
  refine ⟨⟨fun c ↦ ?_, fun c ↦ ?_⟩, ?_⟩
  · simp only [sha3RowOf, Sha3Row.omF, hom, hci, cellWord_lanesOf hcan c]
    exact hin' c
  · simp only [sha3RowOf, hco, cellWord_lanesOf hcan' c]
    exact hout' c
  · simp only [sha3RowOf, Sha3Row.instr, Sha3Row.omF, hom]
    exact hexec

/-! ## Evaluating the reads -/

/-- A lane read off evaluated lanes. -/
theorem eval_laneAt (env : Environment K) (v : Vector (Expression K) 25) (l : ℕ) :
    Expression.eval env (laneAt v l) = laneAt (v.map (Expression.eval env)) l := by
  unfold laneAt
  split_ifs <;> simp [circuit_norm]

/-- A cell's limbs read off evaluated lanes. -/
theorem eval_cellLimbs (env : Environment K) (v : Vector (Expression K) 25) (c : ℕ) (i : ℕ) (hi : i < 3) :
    Expression.eval env (cellLimbs v c)[i] = (cellLimbs (v.map (Expression.eval env)) c)[i] := by
  unfold cellLimbs
  interval_cases i
  · simp [eval_laneAt]
  · cases (sha3CellLanes c).2 <;> simp [eval_laneAt, circuit_norm]
  · simp [circuit_norm]

/-- The address of input cell `c`, evaluated. -/
theorem eval_inAddrE (env : Environment K) (r : Var Sha3Row K) (c : Fin 13) :
    Expression.eval env (inAddrE r c) = Expression.eval env r.fp *
      sha3InOffset (r.om.map (Expression.eval env)).get (Expression.eval env r.otail)
        (Expression.eval env r.ocap) c := by
  unfold inAddrE sha3InOffset
  split_ifs <;> simp only [circuit_norm, Expression.eval, Vector.get, Vector.getElem_map] <;> ring

/-- The address of output cell `c`, evaluated. -/
theorem eval_outAddrE (env : Environment K) (r : Var Sha3Row K) (c : Fin 13) :
    Expression.eval env (outAddrE r c) = Expression.eval env r.fp * sha3OutOffset (Expression.eval env r.oout) c := by
  unfold outAddrE sha3OutOffset
  simp only [circuit_norm, Expression.eval]
  ring

/-- The word a cell read pulls, evaluated. -/
theorem ofLimbs_eval_cellLimbs (env : Environment K) (v : Vector (Expression K) 25) (c : ℕ) :
    E.ofLimbs (Expression.eval env (cellLimbs v c)[0]) (Expression.eval env (cellLimbs v c)[1])
        (Expression.eval env (cellLimbs v c)[2]) = cellWord (v.map (Expression.eval env)) c := by
  rw [eval_cellLimbs _ _ _ 0 (by decide), eval_cellLimbs _ _ _ 1 (by decide), eval_cellLimbs _ _ _ 2 (by decide)]
  rfl

/-- An input cell's read guarantee, evaluated: the binding of the cell. -/
theorem in_eq_of {env : Environment K} {r : Var Sha3Row K} {κ : ℕ} {mem : MemImage κ} {c : ℕ}
    (hc : c < 13) (h : mem.read (Expression.eval env (inAddrE r c)) = some (E.ofLimbs
      (Expression.eval env (cellLimbs r.inLane c)[0]) (Expression.eval env (cellLimbs r.inLane c)[1])
      (Expression.eval env (cellLimbs r.inLane c)[2]))) :
    mem.read (Expression.eval env r.fp * sha3InOffset (r.om.map (Expression.eval env)).get
      (Expression.eval env r.otail) (Expression.eval env r.ocap) ⟨c, hc⟩) =
        some (cellWord (r.inLane.map (Expression.eval env)) c) := by
  rwa [← eval_inAddrE env r ⟨c, hc⟩, ← ofLimbs_eval_cellLimbs]

/-- An output cell's read guarantee, evaluated. -/
theorem out_eq_of {env : Environment K} {r : Var Sha3Row K} {κ : ℕ} {mem : MemImage κ} {c : ℕ}
    (hc : c < 13) (h : mem.read (Expression.eval env (outAddrE r c)) = some (E.ofLimbs
      (Expression.eval env (cellLimbs r.outLane c)[0]) (Expression.eval env (cellLimbs r.outLane c)[1])
      (Expression.eval env (cellLimbs r.outLane c)[2]))) :
    mem.read (Expression.eval env r.fp * sha3OutOffset (Expression.eval env r.oout) ⟨c, hc⟩) =
        some (cellWord (r.outLane.map (Expression.eval env)) c) := by
  rwa [← eval_outAddrE env r ⟨c, hc⟩, ← ofLimbs_eval_cellLimbs]

/-- An input cell's binding, as the read guarantee of its pull. -/
theorem in_eq_to {env : Environment K} {r : Var Sha3Row K} {κ : ℕ} {mem : MemImage κ} {c : ℕ} (hc : c < 13)
    (h : mem.read (Expression.eval env r.fp * sha3InOffset (r.om.map (Expression.eval env)).get
      (Expression.eval env r.otail) (Expression.eval env r.ocap) ⟨c, hc⟩) =
        some (cellWord (r.inLane.map (Expression.eval env)) c)) :
    mem.read (Expression.eval env (inAddrE r c)) = some (E.ofLimbs
      (Expression.eval env (cellLimbs r.inLane c)[0]) (Expression.eval env (cellLimbs r.inLane c)[1])
      (Expression.eval env (cellLimbs r.inLane c)[2])) := by
  rwa [eval_inAddrE env r ⟨c, hc⟩, ofLimbs_eval_cellLimbs]

/-- An output cell's binding, as the read guarantee of its pull. -/
theorem out_eq_to {env : Environment K} {r : Var Sha3Row K} {κ : ℕ} {mem : MemImage κ} {c : ℕ} (hc : c < 13)
    (h : mem.read (Expression.eval env r.fp * sha3OutOffset (Expression.eval env r.oout) ⟨c, hc⟩) =
        some (cellWord (r.outLane.map (Expression.eval env)) c)) :
    mem.read (Expression.eval env (outAddrE r c)) = some (E.ofLimbs
      (Expression.eval env (cellLimbs r.outLane c)[0]) (Expression.eval env (cellLimbs r.outLane c)[1])
      (Expression.eval env (cellLimbs r.outLane c)[2])) := by
  rwa [eval_outAddrE env r ⟨c, hc⟩, ofLimbs_eval_cellLimbs]

/-- The bytecode tuple of a `SHA3` row is Lv42's entry of a `BLAKE2S` with the same operands (both opcodes are
`g^5`), so it decodes: the bytecode pull's guarantee. -/
theorem sha3_entry (om0 om1 om2 om3 otail ocap oout : K) :
    #v[Opcode.sha3.code] ++ #v[om0, om1, om2, om3, otail, ocap, oout] =
      Lv42.Arithmetization.entry (.blake2s ![om0, om1, om2, om3] otail ocap oout) := rfl

/-! ## The adapter to the prover data -/

/-- The table's `Spec`: the row refines `Sha3Refines` over the image the prover data names. -/
def Sha3Spec (r : Sha3Row K) (next : Regs K) (data : ProverData K) : Prop :=
  Sha3Refines (imageOf data).2 r next

/-! ## The table -/

/-- **The `SHA3` table** (`layout.rs::flushes_sha3`): the state step, the bytecode read of
`(g^5, o_m₀, …, o_m₃, o_tail, o_cap, o_out)`, the 13 input cells' reads and the 13 output cells' reads. Returns
the pushed successor `(g·pc, fp)`; sound under `Sha3Relation`. -/
def sha3Table : GeneralFormalCircuit K Sha3Row Regs where
  main r := do
    let next : Var Regs K := ⟨Expression.const g * r.pc, r.fp⟩
    StatePull.pull ⟨r.pc, r.fp⟩
    StatePush.push next
    bytecodeRead r.pc r.cntBc (Expression.const Opcode.sha3.code)
      #v[r.om[0], r.om[1], r.om[2], r.om[3], r.otail, r.ocap, r.oout]
    memRead (inAddrE r 0) r.cnt[0] (cellLimbs r.inLane 0)
    memRead (inAddrE r 1) r.cnt[1] (cellLimbs r.inLane 1)
    memRead (inAddrE r 2) r.cnt[2] (cellLimbs r.inLane 2)
    memRead (inAddrE r 3) r.cnt[3] (cellLimbs r.inLane 3)
    memRead (inAddrE r 4) r.cnt[4] (cellLimbs r.inLane 4)
    memRead (inAddrE r 5) r.cnt[5] (cellLimbs r.inLane 5)
    memRead (inAddrE r 6) r.cnt[6] (cellLimbs r.inLane 6)
    memRead (inAddrE r 7) r.cnt[7] (cellLimbs r.inLane 7)
    memRead (inAddrE r 8) r.cnt[8] (cellLimbs r.inLane 8)
    memRead (inAddrE r 9) r.cnt[9] (cellLimbs r.inLane 9)
    memRead (inAddrE r 10) r.cnt[10] (cellLimbs r.inLane 10)
    memRead (inAddrE r 11) r.cnt[11] (cellLimbs r.inLane 11)
    memRead (inAddrE r 12) r.cnt[12] (cellLimbs r.inLane 12)
    memRead (outAddrE r 0) r.cnt[13] (cellLimbs r.outLane 0)
    memRead (outAddrE r 1) r.cnt[14] (cellLimbs r.outLane 1)
    memRead (outAddrE r 2) r.cnt[15] (cellLimbs r.outLane 2)
    memRead (outAddrE r 3) r.cnt[16] (cellLimbs r.outLane 3)
    memRead (outAddrE r 4) r.cnt[17] (cellLimbs r.outLane 4)
    memRead (outAddrE r 5) r.cnt[18] (cellLimbs r.outLane 5)
    memRead (outAddrE r 6) r.cnt[19] (cellLimbs r.outLane 6)
    memRead (outAddrE r 7) r.cnt[20] (cellLimbs r.outLane 7)
    memRead (outAddrE r 8) r.cnt[21] (cellLimbs r.outLane 8)
    memRead (outAddrE r 9) r.cnt[22] (cellLimbs r.outLane 9)
    memRead (outAddrE r 10) r.cnt[23] (cellLimbs r.outLane 10)
    memRead (outAddrE r 11) r.cnt[24] (cellLimbs r.outLane 11)
    memRead (outAddrE r 12) r.cnt[25] (cellLimbs r.outLane 12)
    pure next
  channelsWithRequirements := [StatePush.toRaw, MemPush.toRaw, BytecodePush.toRaw]
  requirementsChannelsLawful input offset := by
    -- Without core's `BitVec.reduceNeg` simproc, which misreads `-1 : K` (the field's `-1` is `1`).
    simp only [circuit_norm, memRead, bytecodeRead, -BitVec.reduceNeg]
    tauto
  Assumptions r _ := Sha3Relation r
  Spec := Sha3Spec
  ProverAssumptions r data _ := Sha3Bindings (imageOf data).2 r
  soundness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12⟩ := h_holds
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h_input
    refine (sha3_refines_iff _ _ _).mpr ⟨⟨fun c ↦ ?_, fun c ↦ ?_⟩, h_assumptions, ?_⟩
    · fin_cases c
      exacts [(in_eq_of (c := 0) (by decide) h0 :), (in_eq_of (c := 1) (by decide) h1 :), (in_eq_of (c := 2) (by decide) h2 :), (in_eq_of (c := 3) (by decide) h3 :), (in_eq_of (c := 4) (by decide) h4 :), (in_eq_of (c := 5) (by decide) h5 :), (in_eq_of (c := 6) (by decide) h6 :), (in_eq_of (c := 7) (by decide) h7 :), (in_eq_of (c := 8) (by decide) h8 :), (in_eq_of (c := 9) (by decide) h9 :), (in_eq_of (c := 10) (by decide) h10 :), (in_eq_of (c := 11) (by decide) h11 :), (in_eq_of (c := 12) (by decide) h12 :)]
    · fin_cases c
      exacts [(out_eq_of (c := 0) (by decide) o0 :), (out_eq_of (c := 1) (by decide) o1 :), (out_eq_of (c := 2) (by decide) o2 :), (out_eq_of (c := 3) (by decide) o3 :), (out_eq_of (c := 4) (by decide) o4 :), (out_eq_of (c := 5) (by decide) o5 :), (out_eq_of (c := 6) (by decide) o6 :), (out_eq_of (c := 7) (by decide) o7 :), (out_eq_of (c := 8) (by decide) o8 :), (out_eq_of (c := 9) (by decide) o9 :), (out_eq_of (c := 10) (by decide) o10 :), (out_eq_of (c := 11) (by decide) o11 :), (out_eq_of (c := 12) (by decide) o12 :)]
    · rfl
  completeness := by
    circuit_proof_start [StatePull, StatePush, MemPull, MemPush, BytecodePull, BytecodePush,
      memRead, bytecodeRead]
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h_input
    have hb := h_assumptions
    let R : Var Sha3Row K := ⟨input_var_pc, input_var_fp, input_var_om, input_var_otail, input_var_ocap,
      input_var_oout, input_var_inLane, input_var_outLane, input_var_cnt, input_var_cntBc⟩
    refine ⟨⟨_, by rw [sha3_entry, decode_entry]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    exacts [(in_eq_to (env := env.toEnvironment) (r := R) (c := 0) (by decide) (hb.in_eq ⟨0, by decide⟩) :), (in_eq_to (env := env.toEnvironment) (r := R) (c := 1) (by decide) (hb.in_eq ⟨1, by decide⟩) :), (in_eq_to (env := env.toEnvironment) (r := R) (c := 2) (by decide) (hb.in_eq ⟨2, by decide⟩) :), (in_eq_to (env := env.toEnvironment) (r := R) (c := 3) (by decide) (hb.in_eq ⟨3, by decide⟩) :), (in_eq_to (env := env.toEnvironment) (r := R) (c := 4) (by decide) (hb.in_eq ⟨4, by decide⟩) :), (in_eq_to (env := env.toEnvironment) (r := R) (c := 5) (by decide) (hb.in_eq ⟨5, by decide⟩) :), (in_eq_to (env := env.toEnvironment) (r := R) (c := 6) (by decide) (hb.in_eq ⟨6, by decide⟩) :), (in_eq_to (env := env.toEnvironment) (r := R) (c := 7) (by decide) (hb.in_eq ⟨7, by decide⟩) :), (in_eq_to (env := env.toEnvironment) (r := R) (c := 8) (by decide) (hb.in_eq ⟨8, by decide⟩) :), (in_eq_to (env := env.toEnvironment) (r := R) (c := 9) (by decide) (hb.in_eq ⟨9, by decide⟩) :), (in_eq_to (env := env.toEnvironment) (r := R) (c := 10) (by decide) (hb.in_eq ⟨10, by decide⟩) :), (in_eq_to (env := env.toEnvironment) (r := R) (c := 11) (by decide) (hb.in_eq ⟨11, by decide⟩) :), (in_eq_to (env := env.toEnvironment) (r := R) (c := 12) (by decide) (hb.in_eq ⟨12, by decide⟩) :),
      (out_eq_to (env := env.toEnvironment) (r := R) (c := 0) (by decide) (hb.out_eq ⟨0, by decide⟩) :), (out_eq_to (env := env.toEnvironment) (r := R) (c := 1) (by decide) (hb.out_eq ⟨1, by decide⟩) :), (out_eq_to (env := env.toEnvironment) (r := R) (c := 2) (by decide) (hb.out_eq ⟨2, by decide⟩) :), (out_eq_to (env := env.toEnvironment) (r := R) (c := 3) (by decide) (hb.out_eq ⟨3, by decide⟩) :), (out_eq_to (env := env.toEnvironment) (r := R) (c := 4) (by decide) (hb.out_eq ⟨4, by decide⟩) :), (out_eq_to (env := env.toEnvironment) (r := R) (c := 5) (by decide) (hb.out_eq ⟨5, by decide⟩) :), (out_eq_to (env := env.toEnvironment) (r := R) (c := 6) (by decide) (hb.out_eq ⟨6, by decide⟩) :), (out_eq_to (env := env.toEnvironment) (r := R) (c := 7) (by decide) (hb.out_eq ⟨7, by decide⟩) :), (out_eq_to (env := env.toEnvironment) (r := R) (c := 8) (by decide) (hb.out_eq ⟨8, by decide⟩) :), (out_eq_to (env := env.toEnvironment) (r := R) (c := 9) (by decide) (hb.out_eq ⟨9, by decide⟩) :), (out_eq_to (env := env.toEnvironment) (r := R) (c := 10) (by decide) (hb.out_eq ⟨10, by decide⟩) :), (out_eq_to (env := env.toEnvironment) (r := R) (c := 11) (by decide) (hb.out_eq ⟨11, by decide⟩) :), (out_eq_to (env := env.toEnvironment) (r := R) (c := 12) (by decide) (hb.out_eq ⟨12, by decide⟩) :)]

/-- A bound row satisfies the constraints of `main` in the row environment over its data: local completeness, which
does not check the permutation (the boundary with Flock, as Lv42's `blake2sRow_complete`). -/
theorem sha3Row_complete {r : Sha3Row K} {data : ProverData K} (h : Sha3Bindings (imageOf data).2 r) :
    ConstraintsHold.Completeness (rowEnv data) ((sha3Table.main (const r)).operations 0) :=
  (sha3Table.completeness 0 (rowEnv data) (const r)
    (by simp only [circuit_norm, sha3Table, memRead, bytecodeRead, -BitVec.reduceNeg]) r
    ProvableType.eval_const_prover h).1

/-- Every valid `SHA3` execution has a satisfying row, from the execution alone (`sha3RowOf_refines`). -/
theorem sha3_exec_complete {data : ProverData K} {pc fp : K} {om : Fin 4 → K} {otail ocap oout : K}
    {next : Regs K}
    (hexec : KeccakVm.executeWith (imageOf data).2.read ⟨pc, fp⟩ (.sha3 om otail ocap oout) = some next)
    (cnt : Vector K 26) (cntBc : K) :
    ConstraintsHold.Completeness (rowEnv data)
      ((sha3Table.main (const (sha3RowOf (imageOf data).2 pc fp om otail ocap oout cnt cntBc))).operations 0) :=
  sha3Row_complete (sha3RowOf_refines hexec cnt cntBc).bindings

/-- The flushes of a component, as `KeccakVm.Sha3Table.flushExprs` writes them: the side of the channel, then the
separator and the message. -/
def flushForms (c : Air.Flat.Component K) : List (Lv42.Protocol.Side × List (Expression K)) :=
  c.rowOperations.interactions.map fun i ↦
    (Lv42.Protocol.LeanIsa.sideOf (channelDir i.channel), Expression.const (channelSep i.channel) :: i.msg.toList)

/-- An expression as a tree with decidable equality. -/
inductive ETree
  | var (i : ℕ)
  | const (c : K)
  | add (a b : ETree)
  | mul (a b : ETree)
  deriving DecidableEq

/-- The tree of an expression. -/
def toTree : Expression K → ETree
  | .var v => .var v.index
  | .const c => .const c
  | .add a b => .add (toTree a) (toTree b)
  | .mul a b => .mul (toTree a) (toTree b)

theorem toTree_injective : Function.Injective toTree := by
  intro a
  induction a with
  | var v =>
    intro b h
    cases b with
    | var w => simp only [toTree, ETree.var.injEq] at h; cases v; cases w; simp_all
    | _ => simp [toTree] at h
  | const c =>
    intro b h
    cases b with
    | const d => simp only [toTree, ETree.const.injEq] at h; rw [h]
    | _ => simp [toTree] at h
  | add x y hx hy =>
    intro b h
    cases b with
    | add x' y' => simp only [toTree, ETree.add.injEq] at h; rw [hx h.1, hy h.2]
    | _ => simp [toTree] at h
  | mul x y hx hy =>
    intro b h
    cases b with
    | mul x' y' => simp only [toTree, ETree.mul.injEq] at h; rw [hx h.1, hy h.2]
    | _ => simp [toTree] at h

/-- The flushes as trees. -/
def treeForms (l : List (Lv42.Protocol.Side × List (Expression K))) : List (Lv42.Protocol.Side × List ETree) :=
  l.map fun f ↦ (f.1, f.2.map toTree)

/-- The table's flushes as trees are `KeccakVm.Sha3Table.flushExprs`', by the kernel. -/
theorem flushForms_trees : treeForms (flushForms ⟨sha3Table⟩) = treeForms Sha3Table.flushExprs := by
  decide +kernel

/-- **The table's flushes are `KeccakVm.Sha3Table.flushExprs`**, expression for expression: each interaction of the
component is the flush `flushExprs` lists at its place, on its channel's side, its separator first. -/
theorem flushForms_eq : flushForms ⟨sha3Table⟩ = Sha3Table.flushExprs := by
  have hinj : Function.Injective fun f : Lv42.Protocol.Side × List (Expression K) ↦ (f.1, f.2.map toTree) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 ((List.map_injective_iff.mpr toTree_injective) h.2)
  exact (List.map_injective_iff.mpr hinj) flushForms_trees

/-! ## The M3 table -/

open LeanVM.Protocol in
/-- The `SHA3` table as one table of the M3 model, as Lv42 reads its opcode tables (`Component.toM3` with leanISA's
separators, directions and counted channels). -/
def sha3M3 : M3Table K Lv42.Arithmetization.Direction :=
  (⟨sha3Table⟩ : Air.Flat.Component K).toM3 channelSep channelDir Lv42.Protocol.LeanIsa.counted

/-- The component has `86` columns. -/
theorem sha3M3_width : sha3M3.width = Sha3Table.width := rfl

/-- `C 0` is the zero polynomial. -/
theorem cmv_C_zero (n : ℕ) : (CPoly.CMvPolynomial.C (0 : K) : CPoly.CMvPolynomial n K) = 0 := rfl

open LeanVM.Protocol in
/-- The sixteen coordinate polynomials of an interaction are `KeccakVm.Sha3Table.tuple` of its separator and
message. -/
theorem flushPolys_eq_tuple (i : AbstractInteraction K) :
    flushPolys channelSep Sha3Table.width i =
      Sha3Table.tuple (Expression.const (channelSep i.channel) :: i.msg.toList) := by
  apply Vector.ext
  intro j hj
  simp only [flushPolys, Sha3Table.tuple, Vector.getElem_ofFn]
  rcases j with _ | j
  · rfl
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, List.getD_eq_getElem?_getD]
    cases h : i.msg.toArray[j]? with
    | none =>
      have h' : i.msg[j]? = none := by simpa [Vector.getElem?_toArray] using h
      simp [h', Sha3Table.k, Expression.toCMvPolynomial]
      rfl
    | some e =>
      have h' : i.msg[j]? = some e := by simpa [Vector.getElem?_toArray] using h
      simp [h']

/-- **The M3 table's flushes are `KeccakVm.Sha3Table.flushes`**, the instance's `SHA3` flushes, as lists of (side,
sixteen polynomials). -/
theorem sha3M3_flushes :
    sha3M3.flushes.map (fun f ↦ (Lv42.Protocol.LeanIsa.sideOf f.1, f.2)) = Sha3Table.flushes := by
  rw [Sha3Table.flushes, ← flushForms_eq, flushForms]
  simp only [sha3M3, Air.Flat.Component.toM3, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  exact Prod.ext rfl (flushPolys_eq_tuple i)

/-- **The M3 table's count columns are `KeccakVm.Sha3Table.counts`**: the coordinate-`1` variables of its memory and
bytecode pulls, `cnt_0 … cnt_25, cnt_bc`. -/
theorem sha3M3_count : sha3M3.count = Sha3Table.counts := by
  have h : sha3M3.count.map Fin.val = Sha3Table.counts.map Fin.val := by decide +kernel
  exact List.map_injective_iff.mpr Fin.val_injective h

/-- The M3 table has no constraint, as the instance's `SHA3` table. -/
theorem sha3M3_constraints : sha3M3.constraints = [] := by decide +kernel

end KeccakArith

end
