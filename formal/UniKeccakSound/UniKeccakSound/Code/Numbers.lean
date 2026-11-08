-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The shape is `formal/UniKeccak/UniKeccak/Opening.lean`'s
-- `keccakShapeOf` (the 128-signature run of `crates/leanvm/rec/tests/keccak_vm_rec.rs`).
import UniKeccakSound.Code.Link

/-!
# The Keccak code-level link's numbers

`uniCodeK D Fl hκ : UniCodeK D Fl valsCountK (varsOf (layoutsOfK D.shape))`:

* **`nV = valsCountK = 118`** for every shape: the Keccak tables' values at `t` (`tableReads`, `10, 13, 6, 13, 13, 56`
  for the six tables, `111` in all: `tablesReadsK_eq`) and seven more (the memory's final counts, address and pull
  fingerprint, the bytecode's final counts and pull fingerprint, `T(t)`, `Q_W(t)`);
* **`V = varsOf (layoutsOfK shape)`**, the longest of the three stacks' variables (`C1`, `C2`, the setup); at the
  reference shape `keccakShapeOf 721598 [24260, 36229, 24626, 35812, 15509, 17712]` (128 signatures: heights
  `[15, 16, 15, 16, 14, 15]`, `logMemory` 20, `logBytecode` 18) the stacks have `27`, `26`, `23` variables and
  `V = 27` (evaluated with `#eval`; not proved here: the kernel does not reduce `StackLayout.new`).

`nV` and the reference shape's heights by `decide +kernel`.
-/

namespace UniKeccakSound

open UniStatement UniSound UniKeccak

/-- The Keccak tables' values at `t`, table by table. -/
theorem tablesKeccak_reads : tablesKeccak.map tableReads = [10, 13, 6, 13, 13, 56] := by decide +kernel

theorem tablesReadsK_eq : tablesReadsK = 111 := by decide +kernel

/-- **`nV`**: `118` values at `t`, for every shape. -/
theorem valsCountK_eq : valsCountK = 118 := by decide +kernel

/-- The reference Keccak shape: 128 signatures. -/
def keccak128 : Shape := keccakShapeOf 721598 [24260, 36229, 24626, 35812, 15509, 17712]

theorem keccak128_heights : keccak128.heights = [15, 16, 15, 16, 14, 15] := by decide +kernel

end UniKeccakSound
