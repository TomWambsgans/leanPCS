-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import UniKeccakSound.Ids.FlockReg
import Std.Data.String.ToNat

/-!
# The lanes' slots (`LaneSlotsK`)

**`laneSlotsK : LaneSlotsK`**: the `SHA3` column `in_l` (`9 + l`) is `q_flock`'s input port word `4l + 2`, the
column `out_l` (`34 + l`) its output port word `4l`, for `l < 25` (`keccakSlot`).

The kernel does not evaluate `keccakSlot`'s `String.toNat?` (a loop over a slice), so the proof is by lemmas: the
column names are `"in_" ++ l.repr` and `"out_" ++ l.repr` (`sha3Columns_in`, `sha3Columns_out`, list lemmas);
`laneOf p (p ++ n.repr) = some n` (`laneOf_append`: `String.startsWith_string_iff` and `Nat.toNat?_repr`, the core
library's); `"in_"` is no prefix of `"out_" ++ _` (`laneOf_in_out`, on the two literals' characters).
-/

namespace UniKeccakSound.IdsReal

open UniStatement

/-- **The lane a name `p ++ n` names is `n`.** -/
theorem laneOf_append (p : String) (n : ℕ) : laneOf p (p ++ n.repr) = some n := by
  unfold laneOf
  have h1 : (p ++ n.repr).startsWith p = true := by
    rw [String.startsWith_string_iff, String.toList_append]
    exact List.prefix_append _ _
  simp only [h1, ↓reduceIte]
  rw [String.toList_append, ← String.length_toList, List.drop_left, String.ofList_toList]
  exact Nat.toNat?_repr n

/-- An output lane's name is no input lane's. -/
theorem laneOf_in_out (n : ℕ) : laneOf "in_" ("out_" ++ n.repr) = none := by
  unfold laneOf
  have h1 : ("out_" ++ n.repr).startsWith "in_" = false := by
    rw [String.startsWith_string_eq_false_iff, String.toList_append,
      show "in_".toList = ['i', 'n', '_'] by decide, show "out_".toList = ['o', 'u', 't', '_'] by decide]
    simp
  simp only [h1, Bool.false_eq_true, ↓reduceIte]

theorem toString_in : toString "in_" = "in_" := rfl

theorem toString_out : toString "out_" = "out_" := rfl

/-- Column `9 + l` is `in_l`. -/
theorem sha3Columns_in (l : ℕ) (hl : l < 25) : sha3Columns.getD (9 + l) "" = "in_" ++ l.repr := by
  unfold sha3Columns
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by simp), List.getElem?_append_left (by simp [hl])]
  simp [hl, toString_in]

/-- Column `34 + l` is `out_l`. -/
theorem sha3Columns_out (l : ℕ) (hl : l < 25) : sha3Columns.getD (34 + l) "" = "out_" ++ l.repr := by
  unfold sha3Columns
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.append_assoc, List.append_assoc,
    List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega),
    List.getElem?_append_left (by simp; omega)]
  simp only [List.length_cons, List.length_nil, List.length_map, List.length_range]
  rw [show 34 + l - (8 + 1) - 25 = l by omega]
  simp [hl, toString_out]

/-- **The lanes' slots**: `in_l` at port word `4l + 2`, `out_l` at `4l` (`keccakSlot`). -/
theorem laneSlotsK : Ids.LaneSlotsK := by
  intro l
  rw [sha3Columns_in l.val l.isLt, sha3Columns_out l.val l.isLt]
  refine ⟨?_, ?_⟩
  · simp only [keccakSlot, laneOf_append]
  · simp only [keccakSlot, laneOf_in_out, laneOf_append, Option.map_some]

end UniKeccakSound.IdsReal

/-- info: 'UniKeccakSound.IdsReal.laneSlotsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.IdsReal.laneSlotsK
