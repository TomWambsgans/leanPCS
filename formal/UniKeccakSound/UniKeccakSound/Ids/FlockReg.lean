-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The proofs follow `UniSound/Ids/LvLink.lean`'s
-- (`column_lv42Stack`, `flock_lv42Stack_qf`, `lvAux`) for `formal/KeccakVm`'s instance and `formal/UniKeccak`'s
-- `kvStack`.
import UniSound.Ids.LvLink
import UniSound.Ids.Deployed
import UniKeccakSound.Ids.Build

/-!
# Reading `C1`'s Keccak VM stack, and the Keccak-f region (`AuxOfFlockK`)

* **`column_kvStack`**: every column of `C1`'s Keccak VM stack (`kvStack`), read back through the instance's
  layout (`keccakIsaInstance`'s, every column committed), is `kvColumn`'s.
* **`c1LayoutK_qflock`**: `q_flock` is one block of `h_SHA3 + 11` variables in `C1`'s layout (`layoutsK`).
* **`auxOfFlockK`**: `AuxOfFlockK F D κ` at `κ = h_SHA3` for a Keccak-f block the verifier was written for
  (`KeccakFlockFits F`: input lane `l` at port word `4l + 2`, output lane `l` at `4l`): the instance's `QFLOCK` block
  `t` is `q_flock`'s block `rowPosition t` (`< 2^h_SHA3`), so Flock's predicate on `q_flock` gives the block R1CS on
  every block; and the copies on `C1`'s row `rowPosition t` (`CopiesK`) are `KeccakAux`'s lane clause on row `t`.
-/

namespace UniKeccakSound.Ids

open LeanVM.Parameters LeanVM.Protocol UniStatement UniSound UniSound.Ids UniKeccak
open KeccakVm.KeccakIsa (Col blocks stackOrder kappa keccakIsaμ blockOf size_blockOf blocks_fits flockCol)
open Lv42.Protocol.LeanIsa (Sizes)

/-! ## Reading the stack -/

section Read

variable (prog : KeccakVm.Program) (s : Sizes) (shape : UniStatement.Shape) (stack : ℕ → K)

theorem kvColumn_congr {c c' : Col} (h : c' = c) (i : ℕ) (h1 : i < 2 ^ kappa prog s c')
    (h2 : i < 2 ^ kappa prog s c) :
    (kvColumn prog s shape stack c')[i]'h1 = (kvColumn prog s shape stack c)[i]'h2 := by
  subst h
  rfl

/-- **A column of `C1`'s Keccak VM stack is `kvColumn`'s.** -/
theorem column_kvStack (c : Col) (x : Fin (2 ^ kappa prog s c)) :
    ((KeccakVm.keccakIsaInstance prog s).column (kvStack prog s shape stack) c).values.get x =
      (kvColumn prog s shape stack c).get x := by
  have hb := size_blockOf prog s c
  have hx : x.val < 2 ^ (blocks prog s).size (blockOf c) := by rw [hb]; exact x.isLt
  have h1 : ((KeccakVm.keccakIsaInstance prog s).column (kvStack prog s shape stack) c).values.get x =
      (kvStack prog s shape stack).values.get (boolIndex ((blocks prog s).extendPoint (blocks_fits prog s)
        (blockOf c) (boolVec (⟨x.val, hx⟩ : Fin (2 ^ (blocks prog s).size (blockOf c))) :
          Vector E ((blocks prog s).size (blockOf c))))) := by
    show (Layout.readWith (KeccakVm.KeccakIsa.layout prog s).extend (kvStack prog s shape stack) c).values.get x = _
    unfold Layout.readWith
    rw [Vector.get_ofFn]
    show (kvStack prog s shape stack).values.get (boolIndex ((blocks prog s).extendPoint (blocks_fits prog s)
      (blockOf c) (Vector.cast (size_blockOf prog s c).symm (boolVec x : Vector E (kappa prog s c))))) = _
    rw [boolVec_cast]
    rfl
  rw [h1, (blocks prog s).get_extendPoint (blocks_fits prog s) _ (blockOf c) ⟨x.val, hx⟩]
  have h2 := (blocks prog s).unstack_getElem (blocks_fits prog s) (kvStack prog s shape stack).values
    (blockOf c) hx
  rw [← h2]
  have h3 : (kvStack prog s shape stack).values = (blocks prog s).stackAt
      (fun b ↦ kvColumn prog s shape stack (stackOrder prog s)[b]) (keccakIsaμ prog s) 0 := rfl
  rw [h3]
  have h4 := (blocks prog s).unstack_stackAt (fun b ↦ kvColumn prog s shape stack (stackOrder prog s)[b])
    (blocks_fits prog s) (0 : K) (blockOf c)
  refine ((congrArg (fun v => v[x.val]'hx) h4).trans
    (kvColumn_congr prog s shape stack (List.getElem_idxOf _) x.val _ x.isLt)).trans ?_
  exact (Vector.get_eq_getElem _ _).symm

end Read

/-! ## `q_flock` in `C1`'s layout -/

/-- `C1`'s columns on the Keccak VM (`layoutsK`'s `c1`). -/
def c1ColsK (S : UniStatement.Shape) : List (Column × ℕ × Bool) :=
  [(.qflock, S.heights.getD opBlake2s 0 + qflockRowBits, false)] ++
    tablesKeccak.flatMap (fun t ↦
      (List.range t.width).map (fun c ↦ (Column.table t.opcode c, S.heights.getD t.opcode 0, false)) ++
        [(.inverse t.opcode, S.heights.getD t.opcode 0, false)]) ++
    (List.range 4).map (fun k ↦ (Column.memory k, S.logMemory, false)) ++
    [(.bytecodeFinal, S.logBytecode, false)]

theorem c1LayoutK_eq (S : UniStatement.Shape) : c1LayoutK S = StackLayout.new (c1ColsK S) := rfl

/-- **`q_flock` is one block of `h_SHA3 + 11` variables in `C1`'s layout.** -/
theorem c1LayoutK_qflock (S : UniStatement.Shape) :
    ∃ off, (c1LayoutK S).limbs .qflock = [(0, S.heights.getD opBlake2s 0 + qflockRowBits, off)] := by
  rw [c1LayoutK_eq]
  refine limbs_new_single _ _ _ ?_
  simp [c1ColsK, List.filter_append, List.filter_flatMap, List.filter_map, Function.comp_def]

section Cells

variable (D : KDeployment) (rows : List ℕ) (c : Stk)

/-- **`QFLOCK`'s cell `u` of `C1`'s Keccak VM stack is `q_flock`'s word** `qfOffK + u mod 2^11 +
2^11 · rowPosition (u / 2^11)`. -/
theorem flock_kvStack_qf (u : Fin (2 ^ (KeccakVm.kWords + (D.sizes rows).τ 5))) :
    ((D.inst rows).column (kvStack D.prog (D.sizes rows) D.shape c) flockCol).values.get u =
      c (qfOffK D + (u.val % 2 ^ 11 +
        2 ^ 11 * rowPosition (rows.getD 5 0) (D.shape.heights.getD opBlake2s 0) (u.val / 2 ^ 11))) := by
  obtain ⟨off, hoff⟩ := c1LayoutK_qflock D.shape
  refine (column_kvStack D.prog (D.sizes rows) D.shape c flockCol u).trans ((Vector.get_ofFn _ _).trans ?_)
  have hqf : qfOffK D = off := by simp [qfOffK, hoff]
  have hblock : c1Block (c1LayoutK D.shape) c .qflock =
      Array.ofFn (n := 2 ^ (D.shape.heights.getD opBlake2s 0 + qflockRowBits)) fun i ↦ c (off + i.val) := by
    unfold c1Block
    rw [hoff]
  have hu : u.val / 2 ^ 11 < 2 ^ Nat.clog 2 (rows.getD 5 0) := by
    have hp : 2 ^ (KeccakVm.kWords + (D.sizes rows).τ 5) = 2 ^ (D.sizes rows).τ 5 * 2 ^ 11 := by
      rw [pow_add, mul_comm]
    have h : u.val < 2 ^ (D.sizes rows).τ 5 * 2 ^ 11 := lt_of_lt_of_eq u.isLt hp
    exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr h
  have ht := LvLink.rowPosition_lt (count := rows.getD 5 0) (r := D.shape.heights.getD opBlake2s 0) hu
  have hm : u.val % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  have hpow : 2 ^ (D.shape.heights.getD opBlake2s 0 + qflockRowBits) =
      2 ^ D.shape.heights.getD opBlake2s 0 * 2 ^ 11 := by
    rw [pow_add]; rfl
  have hb : u.val % 2 ^ 11 + 2 ^ 11 * rowPosition (rows.getD 5 0) (D.shape.heights.getD opBlake2s 0)
      (u.val / 2 ^ 11) < 2 ^ (D.shape.heights.getD opBlake2s 0 + qflockRowBits) := by
    rw [hpow]
    have : 2 ^ 11 * rowPosition (rows.getD 5 0) (D.shape.heights.getD opBlake2s 0) (u.val / 2 ^ 11) + 2 ^ 11 ≤
        2 ^ 11 * 2 ^ D.shape.heights.getD opBlake2s 0 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ht
    rw [mul_comm (2 ^ D.shape.heights.getD opBlake2s 0)]
    omega
  show (c1Block (c1LayoutK D.shape) c .qflock).getD
      (u.val % 2 ^ KeccakVm.kWords + 2 ^ KeccakVm.kWords * rowPosition (rows.getD 5 0)
        (D.shape.heights.getD 5 0) (u.val / 2 ^ KeccakVm.kWords)) 0 = _
  rw [hblock, hqf]
  show (Array.ofFn (n := 2 ^ (D.shape.heights.getD opBlake2s 0 + qflockRowBits)) fun i ↦ c (off + i.val)).getD
      (u.val % 2 ^ 11 + 2 ^ 11 * rowPosition (rows.getD 5 0) (D.shape.heights.getD opBlake2s 0) (u.val / 2 ^ 11))
      0 = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; exact hb),
    Option.getD_some, Array.getElem_ofFn]

/-- **A `SHA3` cell of `C1`'s Keccak VM stack** at row `x`: `C1`'s value at row `rowPosition x`. -/
theorem sha3_kvStack (i : ℕ) (hi : i < KeccakVm.Sha3Table.width) (x : Fin (2 ^ (D.sizes rows).τ 5)) :
    KeccakVm.sha3Cell D.prog (D.sizes rows) (kvStack D.prog (D.sizes rows) D.shape c) i hi x =
      c1ValK D c (.table opBlake2s i) (D.shape.heights.getD opBlake2s 0)
        (rowPosition (rows.getD 5 0) (D.shape.heights.getD opBlake2s 0) x.val) := by
  refine (column_kvStack D.prog (D.sizes rows) D.shape c (KeccakVm.KeccakIsa.sha3Col i hi) x).trans ?_
  exact Vector.get_ofFn _ _

end Cells

/-! ## The lanes' names -/

/-- **The lanes' slots** (`keccakSlot`, by its definition's string parsing, which the kernel does not evaluate:
`String.toNat?`): column `in_l` (`9 + l`) at `q_flock`'s input port word `4l + 2`, column `out_l` (`34 + l`) at its
output port word `4l`. `UniStatementTest/KeccakTables.lean` checks every slot against the Rust. -/
def LaneSlotsK : Prop :=
  ∀ l : Fin 25, keccakSlot (sha3Columns.getD (9 + l.val) "") = some (keccakStateWord (-1) l.val) ∧
    keccakSlot (sha3Columns.getD (34 + l.val) "") = some (keccakStateWord 23 l.val)

/-- Input lane `l`'s offset is `END_BIT` for `l = 16`, else `0`; an output lane's is `0`. -/
theorem lane_offsets : ∀ l : Fin 25,
    keccakSlotOffset (sha3Columns.getD (9 + l.val) "") = (if l.val = KeccakVm.endLane then sha3EndBit else 0) ∧
      keccakSlotOffset (sha3Columns.getD (34 + l.val) "") = 0 := by
  decide +kernel

/-! ## The Keccak-f region -/

/-- **Flock's predicate on `q_flock` and the copies give `KeccakAux`** (`AuxOfFlockK`), for `κ = h_SHA3` and a
Keccak-f block whose ports are the verifier's (`KeccakFlockFits`). -/
theorem auxOfFlockK (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (κ : ℕ)
    (hκ : D.shape.heights.getD opBlake2s 0 = κ) (hF : KeccakFlockFits F) (hL : LaneSlotsK) :
    AuxOfFlockK F D κ := by
  intro s c hcp hflock
  have hpos : ∀ t : Fin (2 ^ (D.sizes s.2).τ 5),
      rowPosition (s.2.getD 5 0) (D.shape.heights.getD opBlake2s 0) t.val < 2 ^ D.shape.heights.getD opBlake2s 0 :=
    fun t ↦ LvLink.rowPosition_lt (count := s.2.getD 5 0) t.isLt
  -- Cell `w` of the instance's block `t` is `q_flock`'s word `w + 2^11 · rowPosition t`.
  have hcell : ∀ (t : Fin (2 ^ (D.sizes s.2).τ 5)) (w : Fin (2 ^ KeccakVm.kWords)),
      KeccakVm.kBlockCell (KeccakVm.flockColumn D.prog (D.sizes s.2) (kvStack D.prog (D.sizes s.2) D.shape c))
        t w = c (qfOffK D + (w.val + 2 ^ 11 * rowPosition (s.2.getD 5 0) (D.shape.heights.getD opBlake2s 0) t.val)) := by
    intro t w
    have h1 := flock_kvStack_qf D s.2 c (cubeIndex w t)
    have hw : w.val < 2 ^ 11 := w.isLt
    have e1 : (w.val + 2 ^ 11 * t.val) % 2 ^ 11 = w.val := by omega
    have e2 : (w.val + 2 ^ 11 * t.val) / 2 ^ 11 = t.val := by omega
    simp only [cubeIndex_val, e1, e2] at h1
    exact h1
  refine ⟨fun t ↦ ?_, fun t ht l ↦ ?_⟩
  · have ht' : rowPosition (s.2.getD 5 0) (D.shape.heights.getD opBlake2s 0) t.val < 2 ^ κ := hκ ▸ hpos t
    have key : Lv42.Protocol.BlockR1CS.batchBlock
        (Lv42.Protocol.bitTable (KeccakVm.flockColumn D.prog (D.sizes s.2) (kvStack D.prog (D.sizes s.2) D.shape c)))
          t = Lv42.Protocol.BlockR1CS.batchBlock (Lv42.Protocol.bitTable (qfK D c κ)) ⟨_, ht'⟩ := by
      refine LvLink.batchBlock_congr _ _ _ _ fun jsk jin ↦ ?_
      rw [LvLink.bitTable_get, LvLink.bitTable_get]
      congr 1
      refine (hcell t jin).trans ?_
      simp only [qfK, Vector.get_ofFn, cubeIndex_val]
    rw [key]
    exact hflock ⟨_, ht'⟩
  · have hx := hpos t
    have hq : (2 : ℕ) ^ qflockRowBits = 2 ^ 11 := rfl
    obtain ⟨hin, hout⟩ := hL l
    obtain ⟨hino, houto⟩ := lane_offsets l
    have hci := hcp.2 _ hx (9 + l.val) _ hin
    have hco := hcp.2 _ hx (34 + l.val) _ hout
    refine ⟨?_, ?_⟩
    · rw [sha3_kvStack D s.2 c, show KeccakVm.Sha3Table.inLane l.val = 9 + l.val from rfl, hci, hcell,
        hF.1 l, hino]
      congr 1
      · congr 1
        rw [hq]
        omega
      · unfold KeccakVm.laneOffset
        split_ifs <;> rfl
    · rw [sha3_kvStack D s.2 c, show KeccakVm.Sha3Table.outLane l.val = 34 + l.val from rfl, hco, hcell,
        hF.2.1 l, houto]
      have h0 : toK (eK 0) = 0 := rfl
      rw [h0, add_zero]
      congr 1
      rw [hq]
      omega

end UniKeccakSound.Ids
