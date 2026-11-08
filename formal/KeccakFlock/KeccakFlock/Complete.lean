-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The honest block is `crates/vendor/leanvm-42422001/flock/src/keccak.rs`'s
-- `build_block_witness`.
import KeccakFlock.Sound

/-!
# Completeness of the Keccak-f block, and the inhabitant of `KeccakVm.KeccakFlockSpec`

**The honest block** of an input state `s` (`honestBlock`, `build_block_witness`): its words hold
* the port quads: `X = V = keccakF1600 s` lane `q`, `Y = 1`, `C = s` lane `q` (`q < 25`), quad 25 `(2, 1, 0, 2)`,
  quads 26..31 `(0, 1, 0, 0)`;
* `t_j[l] = ¬b[x+1] ∧ b[x+2]` (`tBit`, `b = πρθ` of the state after `j` rounds) and `A_j` = the state after `j + 1`
  rounds (`stateAfter`, leanerVM's `Keccak.round` folded over the first round constants);
* zero elsewhere.
The states are computed once a block (`honestBlock`'s `sts`), the words bit by bit from them (`honestBit`).

`genColumn`: block `t` of the column is the honest block of state `t`. `holds_gen`: it satisfies the predicate (every
row's AND of parities is the honest bit, round by round through `round_parity`); `in_gen`: its input port holds
state `t`. `keccakFlockSpec` assembles `r1cs`, `cpos`, `inSlot`, `outSlot`, `Sound.lean`'s `step_of_holds` and these.
-/

namespace KeccakFlock

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol Lv42.Protocol PcsCircuit PcsCircuit.Builder CompPoly
open ProductCircuit (ofBool ofBool_and ofBool_injective)

/-! ## The honest states -/

/-- The state after the first `j` rounds of leanerVM's Keccak-f. -/
def stateAfter (s : KeccakState) (j : ℕ) : KeccakState := (keccakRC.take j).foldl Keccak.round s

theorem stateAfter_zero (s : KeccakState) : stateAfter s 0 = s := rfl

theorem stateAfter_succ (s : KeccakState) (j : ℕ) (hj : j < 24) :
    stateAfter s (j + 1) = Keccak.round (stateAfter s j) (keccakRC.getD j 0) := by
  have h1 : keccakRC[j]? = some (keccakRC.getD j 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [RecCircuit.keccakRC_length]; exact hj)]
    rfl
  unfold stateAfter
  rw [List.take_add_one, List.foldl_append, h1]
  rfl

theorem stateAfter_24 (s : KeccakState) : stateAfter s 24 = keccakF1600 s := by
  unfold stateAfter keccakF1600
  rw [List.take_of_length_le (by rw [RecCircuit.keccakRC_length])]

/-! ## The honest block -/

/-- Bit `z` of `t_j[l]` from the state `a` before round `j`: `¬b[x+1] ∧ b[x+2]`, `b = πρθ(a)`. -/
def tBit (a : KeccakState) (l z : ℕ) : Bool :=
  !KeccakBits.rhoPi (KeccakBits.theta (laneBits a)) ((l % 5 + 1) % 5 + 5 * (l / 5)) z &&
    KeccakBits.rhoPi (KeccakBits.theta (laneBits a)) ((l % 5 + 2) % 5 + 5 * (l / 5)) z

/-- The honest bits of the port region, `st j` the state after `j` rounds. -/
def portBit (st : ℕ → KeccakState) (q r z : ℕ) : Bool :=
  if r = 1 then decide (z = 0)
  else if q < 25 then (if r = 2 then laneBits (st 0) q z else laneBits (st 24) q z)
  else if q = 25 ∧ r ≠ 2 then decide (z = 1)
  else false

/-- The honest bits of round `j`'s run. -/
def roundBit (st : ℕ → KeccakState) (j r z : ℕ) : Bool :=
  if r < 25 then tBit (st j) r z
  else if 32 ≤ r ∧ r < 57 ∧ j < 23 then laneBits (st (j + 1)) (r - 32) z
  else false

/-- **The honest bit `z` of word `w`.** -/
def honestBit (st : ℕ → KeccakState) (w z : ℕ) : Bool :=
  if w < 128 then portBit st (w / 4) (w % 4) z
  else if w < 1664 then roundBit st (w / 64 - 2) (w % 64) z
  else false

/-- The honest word `w`, its bits as a cell of `K`. -/
def honestCell (st : ℕ → KeccakState) (w : ℕ) : K := BF64.ofBitVec (BitVec.ofFnLE fun z : Fin 64 ↦ honestBit st w z)

/-- The states of a block, from the vector of the 25 computed once: `stateAfter s j` for `j ≤ 24`. -/
def stOf (sts : Vector KeccakState 25) (s : KeccakState) (j : ℕ) : KeccakState :=
  if h : j < 25 then sts[j] else s

/-- **The honest block** of an input state (`build_block_witness`). -/
def honestBlock (s : KeccakState) : Vector K (2 ^ KeccakVm.kWords) :=
  let sts : Vector KeccakState 25 := Vector.ofFn fun j ↦ stateAfter s j
  Vector.ofFn fun w ↦ honestCell (stOf sts s) w

/-- **The honest column** of a batch of input states: block `t` is the honest block of state `t`, each computed
once. -/
def genColumn {κ : ℕ} (states : Vector KeccakState (2 ^ κ)) : Column (KeccakVm.kWords + κ) :=
  let blocks := states.map honestBlock
  ⟨Vector.ofFn fun u ↦ blocks[((cubeSplit KeccakVm.kWords κ).symm u).2][((cubeSplit KeccakVm.kWords κ).symm u).1]⟩

theorem stOf_ofFn (s : KeccakState) {j : ℕ} (hj : j < 25) :
    stOf (Vector.ofFn fun j ↦ stateAfter s j) s j = stateAfter s j := by
  simp [stOf, hj]

theorem honestCell_bit (st : ℕ → KeccakState) (w : ℕ) {z : ℕ} (hz : z < 64) :
    (honestCell st w).toBitVec.getLsbD z = honestBit st w z := by
  simp [honestCell, BF64.toBitVec_ofBitVec, hz]

theorem kBlockCell_genColumn {κ : ℕ} (states : Vector KeccakState (2 ^ κ)) (t : Fin (2 ^ κ))
    (w : Fin (2 ^ KeccakVm.kWords)) :
    KeccakVm.kBlockCell (genColumn states) t w =
      honestCell (stOf (Vector.ofFn fun j ↦ stateAfter states[t] j) states[t]) w := by
  have h : (cubeSplit KeccakVm.kWords κ).symm (cubeIndex w t) = (w, t) := by
    rw [← cubeSplit_apply, Equiv.symm_apply_apply]
  simp only [KeccakVm.kBlockCell, genColumn, Fin.getElem_fin, Vector.getElem_ofFn, h, Vector.getElem_map,
    honestBlock]

/-! ## The rows hold on the honest bits -/

theorem rowW_port {q r z : ℕ} (hq : q < 32) (hr : r < 4) : rowW (4 * q + r) z = portRow q r z := by
  unfold rowW
  rw [ite_eq_left (by omega), show (4 * q + r) / 4 = q by omega, show (4 * q + r) % 4 = r by omega]

theorem rowW_round {j r z : ℕ} (hj : j < 24) (hr : r < 64) : rowW (64 * (j + 2) + r) z = roundRow j r z := by
  unfold rowW
  rw [ite_eq_right (by omega), ite_eq_left (by omega), show (64 * (j + 2) + r) / 64 - 2 = j by omega,
    show (64 * (j + 2) + r) % 64 = r by omega]

theorem honestBit_port (st : ℕ → KeccakState) {q r z : ℕ} (hq : q < 32) (hr : r < 4) :
    honestBit st (4 * q + r) z = portBit st q r z := by
  unfold honestBit
  rw [ite_eq_left (by omega), show (4 * q + r) / 4 = q by omega, show (4 * q + r) % 4 = r by omega]

theorem honestBit_round (st : ℕ → KeccakState) {j r z : ℕ} (hj : j < 24) (hr : r < 64) :
    honestBit st (64 * (j + 2) + r) z = roundBit st j r z := by
  unfold honestBit
  rw [ite_eq_right (by omega), ite_eq_left (by omega), show (64 * (j + 2) + r) / 64 - 2 = j by omega,
    show (64 * (j + 2) + r) % 64 = r by omega]

theorem honestBit_stWord (st : ℕ → KeccakState) {j l z : ℕ} (hj : j ≤ 24) (hl : l < 25) :
    honestBit st (stWord j l) z = laneBits (st j) l z := by
  unfold stWord portWord aWord
  by_cases h0 : j = 0
  · subst h0
    rw [ite_eq_left rfl, honestBit_port st (by omega) (by omega)]
    unfold portBit
    rw [ite_eq_right (by decide), ite_eq_left hl, ite_eq_left rfl]
  · rw [ite_eq_right h0]
    by_cases h24 : j = 24
    · subst h24
      rw [ite_eq_left rfl, honestBit_port st (by omega) (by omega)]
      unfold portBit
      rw [ite_eq_right (by decide), ite_eq_left hl, ite_eq_right (by decide)]
    · rw [ite_eq_right h24, show 64 * (j - 1 + 2) + 32 + l = 64 * (j - 1 + 2) + (32 + l) by omega,
        honestBit_round st (by omega) (by omega)]
      unfold roundBit
      rw [ite_eq_right (by omega), ite_eq_left (by omega), show 32 + l - 32 = l by omega,
        show j - 1 + 1 = j by omega]

theorem honestBit_tWord (st : ℕ → KeccakState) {j l z : ℕ} (hj : j < 24) (hl : l < 25) :
    honestBit st (tWord j l) z = tBit (st j) l z := by
  unfold tWord
  rw [honestBit_round st hj (by omega)]
  unfold roundBit
  rw [ite_eq_left hl]

/-- **A lin-id row on the honest bits**: the parity of `linForm j l z` is bit `z` of lane `l` of the state after
round `j`. -/
theorem round_parity {β : Pos → Bool} {st : ℕ → KeccakState} (hc : β cpos = true)
    (hβ : ∀ w < 2048, ∀ z < 64, β (pos w z) = honestBit st w z)
    (hround : ∀ j < 24, st (j + 1) = Keccak.round (st j) (keccakRC.getD j 0))
    {j l z : ℕ} (hj : j < 24) (hl : l < 25) (hz : z < 64) :
    parity β (linForm j l z) = laneBits (st (j + 1)) l z := by
  have hS : ∀ l < 25, ∀ z < 64, β (pos (stWord j l) z) = laneBits (st j) l z := fun l hl z hz ↦ by
    rw [hβ _ (stWord_lt (by omega) hl) z hz, honestBit_stWord st (by omega) hl]
  obtain ⟨x, y, hx, hy, rfl⟩ : ∃ x y, x < 5 ∧ y < 5 ∧ l = x + 5 * y :=
    ⟨l % 5, l / 5, Nat.mod_lt _ (by decide), by omega, by omega⟩
  have e1 : (x + 5 * y) % 5 = x := by omega
  have e2 : (x + 5 * y) / 5 = y := by omega
  rw [hround j hj, round_bits _ _ _ hl z hz, RecCircuit.round_apply _ _ x y z hx]
  simp only [linForm, parity_append, parity_cons]
  rw [parity_bForm hS z hl, hβ _ (tWord_lt hj hl) z hz, honestBit_tWord st hj hl, tBit, e1, e2, rcBit]
  generalize (keccakRC.getD j 0).toBitVec.getLsbD z = r
  have hrc : ∀ (P : Prop) [Decidable P] (r : Bool),
      parity β (if P ∧ r = true then [cpos] else []) = (decide P && r) := by
    intro P _ r
    by_cases hP : P <;> cases r <;> simp [hP, parity_cons, parity_nil, hc]
  rw [hrc, Bool.xor_assoc]

/-- **Every row holds on the honest bits.** -/
theorem rows_honest {β : Pos → Bool} {st : ℕ → KeccakState}
    (hβ : ∀ w < 2048, ∀ z < 64, β (pos w z) = honestBit st w z)
    (hround : ∀ j < 24, st (j + 1) = Keccak.round (st j) (keccakRC.getD j 0))
    {w z : ℕ} (hw : w < 2048) (hz : z < 64) :
    honestBit st w z = (parity β (rowW w z).1 && parity β (rowW w z).2) := by
  have hc : β cpos = true := by
    rw [cpos, hβ _ (by decide) _ (by decide), show portWord 0 1 = 4 * 0 + 1 from rfl,
      honestBit_port st (by decide) (by decide)]
    rfl
  have hS : ∀ j ≤ 24, ∀ l < 25, ∀ z < 64, β (pos (stWord j l) z) = laneBits (st j) l z := fun j hj l hl z hz ↦ by
    rw [hβ _ (stWord_lt hj hl) z hz, honestBit_stWord st hj hl]
  have hone : ∀ L, (parity β L && parity β [cpos]) = parity β L := fun L ↦ by
    rw [parity_cons, parity_nil, hc, Bool.xor_false, Bool.and_true]
  by_cases hp : w < 128
  · obtain ⟨q, r, hq, hr, rfl⟩ : ∃ q r, q < 32 ∧ r < 4 ∧ w = 4 * q + r :=
      ⟨w / 4, w % 4, by omega, Nat.mod_lt _ (by decide), by omega⟩
    rw [rowW_port hq hr, honestBit_port st hq hr]
    unfold portRow portBit
    by_cases h1 : r = 1
    · simp only [h1, ite_true]
      by_cases h0 : z = 0 <;> simp [h0, parity_cons, parity_nil, hc]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases hq25 : q < 25
      · rw [ite_eq_left hq25, ite_eq_left hq25]
        by_cases h0 : r = 0
        · subst h0
          rw [ite_eq_left rfl, ite_eq_right (by decide), hone,
            round_parity hc hβ hround (by decide) hq25 hz]
        · rw [ite_eq_right h0]
          by_cases h2 : r = 2
          · subst h2
            rw [ite_eq_left rfl, ite_eq_left rfl, hone, parity_cons, parity_nil, Bool.xor_false,
              ← hS 0 (by decide) q hq25 z hz]
            rfl
          · have h3 : r = 3 := by omega
            subst h3
            rw [ite_eq_right h2, ite_eq_right h2, hone, parity_cons, parity_nil, Bool.xor_false,
              ← hS 24 le_rfl q hq25 z hz]
            rfl
      · rw [ite_eq_right hq25, ite_eq_right hq25]
        by_cases hx : q = 25 ∧ r ≠ 2
        · rw [ite_eq_left hx]
          by_cases hz1 : z = 1
          · rw [ite_eq_left ⟨hx.1, hx.2, hz1⟩]
            simp [hz1, parity_cons, parity_nil, hc]
          · rw [ite_eq_right (fun h ↦ hz1 h.2.2)]
            simp [hz1, parity_nil]
        · rw [ite_eq_right hx, ite_eq_right (fun h ↦ hx ⟨h.1, h.2.1⟩)]
          rfl
  · by_cases hr26 : w < 1664
    · obtain ⟨j, r, hj, hr, rfl⟩ : ∃ j r, j < 24 ∧ r < 64 ∧ w = 64 * (j + 2) + r :=
        ⟨w / 64 - 2, w % 64, by omega, Nat.mod_lt _ (by decide), by omega⟩
      rw [rowW_round hj hr, honestBit_round st hj hr]
      unfold roundRow roundBit
      by_cases h25 : r < 25
      · rw [ite_eq_left h25, ite_eq_left h25, parity_cons, hc, Bool.true_xor,
          parity_bForm (hS j (by omega)) z (by omega), parity_bForm (hS j (by omega)) z (by omega)]
        rfl
      · rw [ite_eq_right h25, ite_eq_right h25]
        by_cases ha : 32 ≤ r ∧ r < 57 ∧ j < 23
        · rw [ite_eq_left ha, ite_eq_left ha, hone, round_parity hc hβ hround hj (by omega) hz]
        · rw [ite_eq_right ha, ite_eq_right ha]
          rfl
    · unfold rowW honestBit
      rw [ite_eq_right hp, ite_eq_right hp, ite_eq_right hr26, ite_eq_right hr26]
      rfl

/-- **Completeness**: the honest column satisfies the predicate. -/
theorem holds_gen {κ : ℕ} (states : Vector KeccakState (2 ^ κ)) :
    BlockR1CS.BatchHolds r1cs cpos (bitTable (genColumn states)) := by
  intro t
  set st := stOf (Vector.ofFn fun j ↦ stateAfter states[t] j) states[t]
  have hround : ∀ j < 24, st (j + 1) = Keccak.round (st j) (keccakRC.getD j 0) := fun j hj ↦ by
    simp only [st]
    rw [stOf_ofFn _ (by omega), stOf_ofFn _ (by omega), stateAfter_succ _ _ hj]
  have hβ : ∀ w < 2048, ∀ z < 64, blockBit (genColumn states) t (pos w z) = honestBit st w z :=
    fun w hw z hz ↦ by rw [blockBit_pos _ t hw hz, kBlockCell_genColumn, honestCell_bit _ _ hz]
  have hzb := batchBlock_bitTable (genColumn states) t
  have hk : ∀ k : Pos, blockBit (genColumn states) t k =
      (parity (blockBit (genColumn states) t) (row k).1 && parity (blockBit (genColumn states) t) (row k).2) := by
    intro k
    have hw : k.val / 64 < 2048 := by have h : k.val < 131072 := k.isLt; omega
    have hz : k.val % 64 < 64 := Nat.mod_lt _ (by decide)
    have hk : k = pos (k.val / 64) (k.val % 64) := Fin.ext (by rw [pos_val hw hz]; omega)
    rw [hk, row_pos hw hz, hβ _ hw _ hz]
    exact rows_honest hβ hround hw hz
  refine ⟨fun k ↦ ?_, ?_⟩
  · have e : ∀ L : List Pos, (L.map fun p ↦ (BlockR1CS.batchBlock (bitTable (genColumn states)) t)[p]).sum =
        ofBool E (parity (blockBit (genColumn states) t) L) := fun L ↦ by
      rw [← sum_ofBool]
      exact congrArg List.sum (List.map_congr_left fun p _ ↦ hzb p)
    rw [BlockR1CS.rows_fst, BlockR1CS.rows_snd]
    change (∑ j, if xorMem (row k).1 j then _ else 0) * (∑ j, if xorMem (row k).2 j then _ else 0) = _
    rw [sum_ite_xorMem, sum_ite_xorMem, e, e, hzb, ← ofBool_and, ← hk]
  · rw [hzb, cpos, hβ (portWord 0 1) (by decide) 0 (by decide)]
    rfl

/-- **The honest column's block `t` holds state `t` at its input port.** -/
theorem in_gen {κ : ℕ} (states : Vector KeccakState (2 ^ κ)) (t : Fin (2 ^ κ)) :
    KeccakVm.kBlockState (genColumn states) t inSlot = states[t] := by
  apply Vector.ext
  intro l hl
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [KeccakVm.kBlockState, Vector.getElem_ofFn, kBlockCell_genColumn]
  change (honestCell _ (stWord 0 l)).toBitVec.getLsbD z = _
  rw [honestCell_bit _ _ hz, honestBit_stWord _ (by decide) hl, stOf_ofFn _ (by decide), stateAfter_zero, laneBits,
    lane_eq_getElem _ hl]

end KeccakFlock

/-! ## The inhabitant -/

namespace KeccakFlock

/-- **The Keccak-f block of `crates/vendor/leanvm-42422001/flock/src/keccak.rs`** as `KeccakVm.KeccakFlockSpec`: its R1CS, the
constant wire at position 64, the port words `4l + 2` (input) and `4l` (output), soundness and completeness. -/
def keccakFlockSpec : KeccakVm.KeccakFlockSpec where
  r1cs := r1cs
  constPos := cpos
  inSlot := inSlot
  outSlot := outSlot
  step_of_holds := step_of_holds
  gen := genColumn
  holds_gen := holds_gen
  in_gen := in_gen

end KeccakFlock
