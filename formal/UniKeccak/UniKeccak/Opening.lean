-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `crates/leanvm/univariate/src/contract.rs`
-- (`variant_bytes`, `contract_iv`, `SetupRoots`) and `crates/leanvm/univariate/tests/keccak_vm.rs` (`KECCAK_RUNS`,
-- `KECCAK_LOG_BYTECODE`: leanVM 9d50c92a3's runs). The claims and their openings are `UniKeccak/Pcs.lean`'s.
module

public import UniKeccak.Verifier

/-!
# The Keccak contract's IV and the measured shapes

* **The setup commitment** (`SetupRootsK`, `SetupRoots`): the setup stack `F`'s commitment as the EIP's PCS claims
  carry it (`crates/pcs_claim`), its root and its out-of-domain answer: a constant of the contract.
* **The IV** (`contractIvKWith`, `contract_iv`): the Keccak-256 of the tag `"leanVM-univar-iv"`, the program's IV,
  the setup's root, its out-of-domain answer (`element_word(f_ood)[8..]`: limbs `c2, c1, c0` big-endian, 24 bytes),
  the shape's bytes, then the variant's bytes (`variantBytesK`: `"keccak-vm"`, the skip, the Fiat–Shamir shape's
  code `Main` 0, `Rec` 1, `Rec2` 2, `Rec3` 3). No layout words: a claim names its stack's size by its `n`. The seed
  is `keccak(name ‖ IV ‖ public input)`.
* **The measured shapes** (`keccakRuns`, `keccakShapeNamed`): leanVM 9d50c92a3's runs at 32, 128, 400 and 1,000
  signatures, the bytecode `2^18` instructions, the memory `⌈log₂ cells⌉`.
-/

@[expose] public section

namespace UniKeccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement

/-- The Fiat–Shamir shape's code in the IV (`v.fs as u8`: the enum's order). -/
def FsShape.code : FsShape → ℕ
  | .main => 0
  | .rec1 => 1
  | .rec2 => 2
  | .rec3 => 3

/-- **`variant_bytes(v)`**: the tag `"keccak-vm"`, then the skip and the Fiat–Shamir shape's code. -/
def variantBytesK (v : KeccakVariant) : List UInt8 :=
  "keccak-vm".toUTF8.toList ++ [v.skip.toUInt8, (FsShape.code v.fs).toUInt8]

/-- **The setup commitment** (`SetupRoots`): the setup stack `F`'s root and its out-of-domain answer `f(z)`, `z`
derived from the root (`crates/pcs_claim`), constants of the contract (`prover::setup::shape_roots`). -/
structure SetupRootsK where
  f : Digest
  fOod : E

/-- An element's 24 bytes as a PCS claim and the IV carry it (`element_word(x)[8..]`: limbs `c2, c1, c0`, each
eight bytes big-endian). -/
def elementBytes24 (x : E) : List UInt8 := (elementWord x).drop 8

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`contract_iv(shape, v, program_iv, roots)`** over `F`: the Keccak-256 of the tag, the program's IV, the setup's
root and out-of-domain answer, the shape's bytes and the variant's bytes. -/
def contractIvKWith (s : Shape) (v : KeccakVariant) (programIv : List UInt8) (roots : SetupRootsK) :
    m (List UInt8) := do
  let d ← keccak256With F (ivTag ++ programIv ++ digestBytes roots.f ++ elementBytes24 roots.fOod ++
    shapeBytes s ++ variantBytesK v)
  return digestBytes d

end With

/-- The Keccak contract's IV over Keccak-f[1600]: the deployed contract's constant. -/
def contractIvK (s : Shape) (v : KeccakVariant) (programIv : List UInt8) (roots : SetupRootsK) : List UInt8 :=
  Id.run (contractIvKWith (m := Id) (fun x ↦ pure (keccakF1600 x)) s v programIv roots)

/-! ### The measured shapes (`tests/keccak_vm.rs`) -/

/-- `KECCAK_LOG_BYTECODE`: the bytecode's `2^17.54` instructions, padded to `2^18`. -/
def keccakLogBytecode : ℕ := 18

/-- **`KECCAK_RUNS`**: leanVM 9d50c92a3's Keccak VM (`cargo leanvm aggregate --xmss N --log-inv-rate 1`): name,
signatures, the memory cells used, the rows in the order XOR, MUL, SET, DEREF, JUMP, SHA3. -/
def keccakRuns : List (String × ℕ × ℕ × List ℕ) :=
  [("keccak32", 32, 184479, [6956, 9877, 6578, 9652, 3995, 4440]),
    ("keccak128", 128, 721598, [24260, 36229, 24626, 35812, 15509, 17712]),
    ("keccak400", 400, 2243324, [73288, 110893, 75762, 109932, 48157, 55316]),
    ("keccak1000", 1000, 5600312, [181438, 275593, 188562, 273432, 120085, 138266])]

/-- A run's shape (`KeccakRun::shape`): the memory `⌈log₂ cells⌉`, the bytecode `2^18`, the heights. -/
def keccakShapeOf (cells : ℕ) (rows : List ℕ) : Shape := shapeWith (log2Ceil cells) keccakLogBytecode rows

/-- The shape of a run by name, and its row counts. -/
def keccakShapeNamed (n : String) : Option (Shape × List ℕ) :=
  (keccakRuns.find? (·.1 == n)).map fun (_, _, cells, rows) ↦ (keccakShapeOf cells rows, rows)

/-- **The Keccak VM at 400 signatures** (`KECCAK_400` of `crates/leanvm/rec/tests/keccak_vm_rec.rs`): the largest run
whose `C1` fits WHIR's `2^28` words. -/
def keccak400 : Shape := keccakShapeOf 2243324 [73288, 110893, 75762, 109932, 48157, 55316]

end UniKeccak

end
