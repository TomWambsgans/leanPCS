-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The block is `crates/lv42_flock/src/keccak.rs`'s
-- (its module documentation, `port_row`, `b_forms`, `row_values_walk`); its port layout is read as
-- `crates/leanvm_flock_gas/src/keccak_flock.rs` reads it (`state_word`, `port_word`, `CONSTANT_COLUMN`,
-- `row_values`). Keccak-f[1600] is leanerVM's (`Statement/Keccak.lean`), read bit by bit through `formal/Circuit`'s
-- `KeccakBits` and `formal/RecCircuit`'s `stAfter`.
import KeccakVm.Instance
import Lv42.Protocol.ToArkLib.Flock.Builder
import Batteries.Data.BitVec.Lemmas
import RecCircuit.KeccakMath

/-!
# The Keccak-f block's R1CS

One Keccak-f[1600] permutation in a block of `2^17` positions, every round's state materialised, `C = I`
(`crates/lv42_flock/src/keccak.rs`). Position `z + 64 w` is bit `z` of the block's 64-bit word `w` (`pos w z`): the
low six coordinates are the packing position (`Flock.kSkip = 6`), the high eleven the word, as `bitTable` and
`BlockR1CS.batchBlock` read a column of `K`.

**The layout** (words; `keccak.rs`'s table):
* `4q + r`, `q < 32` (the port quads): `r = 0` the output lane `A_23[q]` (`q < 25`), `r = 1` the word `1`
  (quad 0's bit 0 is the constant wire `cpos`, position 64), `r = 2` the input lane `A_{-1}[q]`, `r = 3` the output
  lane again; quad 25 is `(x, 1, 0, x)` with `x = 2`, quads 26..31 are `(0, 1, 0, 0)`;
* `tWord j l = 64 (j + 2) + l`: `t_j[l]`, χ's products of round `j < 24`;
* `aWord j l = 64 (j + 2) + 32 + l`: the state `A_j[l]`, `j < 23`.

`stWord j l` is the word of the state *before* round `j` (`0 ≤ j ≤ 24`): the input port (`j = 0`), `A_(j-1)`
(`0 < j < 24`), the output port (`j = 24`); it is the Rust's `state_word(j - 1, l)`.

**The rows** (`row k`: the lists of positions whose sums are row `k` of `A` and of `B`; `rowW`, `portRow`,
`roundRow`), one per position, `keccak.rs`'s five kinds:
* constant `([1], [1])`: bit 0 of every `Y` word, bit 1 of quad 25's `X` and `V` words;
* free input `([self], [1])`: the `C` words;
* copy `([X word, same bit], [1])`: the `V` words;
* product `(1 + b[x+1], b[x+2])`: `t_j[x + 5y]`, where `b = πρθ(A_(j-1))` and each bit of `b` is the sum of eleven
  positions of the state before the round (`bForm`: the lane's own bit and θ's two column parities, at the
  ρ-rotated position);
* lin-id `(b[l] + t_j[l] + RC_j, [1])`: the state words `A_j` and the output port's `X` words (`linForm`, ι's bit on
  lane 0 only);
* empty `([], [])`: everything else.

**The matrices** `matA`, `matB`: entry `(k, j)` is the parity of the number of times `j` occurs in row `k`'s list
(`xorMem`); no position occurs twice in a list, so it is the indicator the Rust's matrices have, and in
characteristic two a row of the matrix applied to a vector is the sum of the list's entries
(`sum_ite_xorMem`) in every case. **`r1cs`** carries those matrices, the forward walk summing the lists (as
`row_values_walk` does, about `13 · 2^17` additions) and the naive backward walk.
-/

namespace KeccakFlock

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol Lv42.Protocol PcsCircuit PcsCircuit.Builder CompPoly

/-! ## Positions -/

/-- Log-size of a block: `kSkip + kWords = 17`. -/
abbrev m : ℕ := Lv42.Parameters.Flock.kSkip + KeccakVm.kWords

/-- A position of a block. -/
abbrev Pos : Type := Fin (2 ^ m)

theorem two_pow_m : (2 : ℕ) ^ m = 131072 := rfl

theorem two_pow_kWords : (2 : ℕ) ^ KeccakVm.kWords = 2048 := rfl

/-- Bit `z` of word `w`: position `z + 64 w` (both reduced to their ranges). -/
def pos (w z : ℕ) : Pos := ⟨z % 64 + 64 * (w % 2048), by rw [two_pow_m]; omega⟩

theorem pos_val {w z : ℕ} (hw : w < 2048) (hz : z < 64) : (pos w z).val = z + 64 * w := by
  simp only [pos, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hz]

/-! ## The layout -/

/-- The word of quad `q`'s role `r` (`port_word`). -/
def portWord (q r : ℕ) : ℕ := 4 * q + r

/-- The word of `t_j`'s lane `l` (`t_word`). -/
def tWord (j l : ℕ) : ℕ := 64 * (j + 2) + l

/-- The word of `A_j`'s lane `l`, `j < 23` (`a_word`). -/
def aWord (j l : ℕ) : ℕ := 64 * (j + 2) + 32 + l

/-- The word of lane `l` of the state before round `j`, `0 ≤ j ≤ 24`: the input port's `C` word, a materialised
state, the output port's `X` word (`state_word(j - 1, l)`). -/
def stWord (j l : ℕ) : ℕ := if j = 0 then portWord l 2 else if j = 24 then portWord l 0 else aWord (j - 1) l

/-- The constant wire: bit 0 of quad 0's `Y` word, position 64 (`CONST_POS`, `CONSTANT_COLUMN`). -/
def cpos : Pos := pos (portWord 0 1) 0

theorem cpos_val : cpos.val = 64 := rfl

/-- Bit `z` of ι's round constant `RC_j` (`RC[j] >> z & 1 == 1`). -/
def rcBit (j z : ℕ) : Bool := (keccakRC.getD j 0).toBitVec.getLsbD z

/-- **The eleven positions bit `z` of `b[i]` sums** in round `j` (`b_forms`): with `(src, rot) = SOURCE[i] =
(piInv i, rho (piInv i))` and `z' = z − rot`, the bit `z'` of the state's lane `src`, of the five lanes of column
`src − 1`, and the bit `z' − 1` of the five lanes of column `src + 1` (θ's `C[x − 1][z'] + C[x + 1][z' − 1]`). -/
def bForm (j i z : ℕ) : List Pos :=
  let src := piInv i
  let zp := (z + 64 - rho src) % 64
  let zr := (zp + 63) % 64
  let xl := (src % 5 + 4) % 5
  let xr := (src % 5 + 1) % 5
  [pos (stWord j src) zp,
    pos (stWord j xl) zp, pos (stWord j (xl + 5)) zp, pos (stWord j (xl + 10)) zp, pos (stWord j (xl + 15)) zp,
    pos (stWord j (xl + 20)) zp,
    pos (stWord j xr) zr, pos (stWord j (xr + 5)) zr, pos (stWord j (xr + 10)) zr, pos (stWord j (xr + 15)) zr,
    pos (stWord j (xr + 20)) zr]

/-- **The lin-id form of `A_j[l]` at bit `z`**: `b[l] + t_j[l]`, plus the constant where `RC_j` has bit `z` on lane
0 (`left[s] = bw[l][z] + w[t] + rc`). -/
def linForm (j l z : ℕ) : List Pos :=
  bForm j l z ++ pos (tWord j l) z :: (if l = 0 ∧ rcBit j z = true then [cpos] else [])

/-- The rows of the port region (`port_row`, and the outputs' rows of round 23): quad `q`, role `r`, bit `z`. -/
def portRow (q r z : ℕ) : List Pos × List Pos :=
  if r = 1 then (if z = 0 then ([cpos], [cpos]) else ([], []))
  else if q < 25 then
    if r = 0 then (linForm 23 q z, [cpos])
    else if r = 2 then ([pos (portWord q 2) z], [cpos])
    else ([pos (portWord q 0) z], [cpos])
  else if q = 25 ∧ r ≠ 2 ∧ z = 1 then ([cpos], [cpos])
  else ([], [])

/-- The rows of round `j`'s run (`row_values_walk`'s round loop): lane field `r < 25` the products `t_j`, `32 ≤ r <
57` the states `A_j` (`j < 23`), the rest empty. -/
def roundRow (j r z : ℕ) : List Pos × List Pos :=
  if r < 25 then
    (cpos :: bForm j ((r % 5 + 1) % 5 + 5 * (r / 5)) z, bForm j ((r % 5 + 2) % 5 + 5 * (r / 5)) z)
  else if 32 ≤ r ∧ r < 57 ∧ j < 23 then (linForm j (r - 32) z, [cpos])
  else ([], [])

/-- The row of bit `z` of word `w`: the port region (words `< 128`), the rounds' runs (words `< 1664 = 64 · 26`),
empty past them. -/
def rowW (w z : ℕ) : List Pos × List Pos :=
  if w < 128 then portRow (w / 4) (w % 4) z
  else if w < 1664 then roundRow (w / 64 - 2) (w % 64) z
  else ([], [])

/-- **The row of position `k`**: the positions row `k` of `A` and of `B` sum. -/
def row (k : Pos) : List Pos × List Pos := rowW (k.val / 64) (k.val % 64)

theorem row_pos {w z : ℕ} (hw : w < 2048) (hz : z < 64) : row (pos w z) = rowW w z := by
  unfold row
  rw [pos_val hw hz, show (z + 64 * w) / 64 = w by omega, show (z + 64 * w) % 64 = z by omega]

/-! ## The matrices -/

/-- Whether `j` occurs an odd number of times in `L`. -/
def xorMem {n : ℕ} (L : List (Fin n)) (j : Fin n) : Bool := L.foldr (fun p b ↦ (p == j) ^^ b) false

/-- The left matrix: entry `(k, j)` set when `j` occurs (an odd number of times) in row `k`'s left list. -/
def matA (k j : Pos) : Bool := xorMem (row k).1 j

/-- The right matrix. -/
def matB (k j : Pos) : Bool := xorMem (row k).2 j

section CharTwo

variable {R : Type*} [CommRing R] [CharP R 2]

/-- In characteristic two, a row of an occurrence-parity matrix applied to a vector is the sum of the list's
entries. -/
theorem sum_ite_xorMem {n : ℕ} (L : List (Fin n)) (f : Fin n → R) :
    (∑ j, if xorMem L j then f j else 0) = (L.map f).sum := by
  induction L with
  | nil => simp [xorMem]
  | cons p L ih =>
    have h : ∀ j, (if xorMem (p :: L) j then f j else 0) =
        (if p = j then f j else 0) + (if xorMem L j then f j else 0) := by
      intro j
      have e : xorMem (p :: L) j = ((p == j) ^^ xorMem L j) := rfl
      rw [e]
      by_cases h1 : p = j <;> cases h2 : xorMem L j <;>
        simp [h1, CharTwo.add_self_eq_zero]
    rw [Finset.sum_congr rfl fun j _ ↦ h j, Finset.sum_add_distrib, ih, Finset.sum_ite_eq]
    simp

end CharTwo

/-- The forward walk: each row's list summed (`row_values_walk`). -/
def walkRows (W : CMlPolynomialEval E m) : CMlPolynomialEval E m × CMlPolynomialEval E m :=
  (Vector.ofFn fun k ↦ ((row k).1.map fun p ↦ W[p]).sum, Vector.ofFn fun k ↦ ((row k).2.map fun p ↦ W[p]).sum)

/-- **The Keccak-f block's R1CS**: the matrices of `row`, the forward walk summing the rows' lists, the naive
backward walk. -/
def r1cs : BlockR1CS E m where
  A := matA
  B := matB
  rows := walkRows
  cols e := (Vector.ofFn fun j ↦ ∑ k, if matA k j then e[k] else 0,
    Vector.ofFn fun j ↦ ∑ k, if matB k j then e[k] else 0)
  rows_fst W k := by
    simp only [walkRows, Vector.getElem_ofFn, Fin.getElem_fin, matA]
    exact (sum_ite_xorMem _ _).symm
  rows_snd W k := by
    simp only [walkRows, Vector.getElem_ofFn, Fin.getElem_fin, matB]
    exact (sum_ite_xorMem _ _).symm
  cols_fst e j := by simp
  cols_snd e j := by simp

/-- The input port word of lane `l`: `C` of quad `l`, word `4l + 2` (`UniStatement.keccakSlot`). -/
def inSlot (l : Fin 25) : Fin (2 ^ KeccakVm.kWords) := ⟨portWord l 2, by rw [two_pow_kWords]; unfold portWord; omega⟩

/-- The output port word of lane `l`: `X` of quad `l`, word `4l`. -/
def outSlot (l : Fin 25) : Fin (2 ^ KeccakVm.kWords) := ⟨portWord l 0, by rw [two_pow_kWords]; unfold portWord; omega⟩

end KeccakFlock
