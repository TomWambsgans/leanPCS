-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `crates/leanvm/univariate/src/contract.rs`
-- (`variant_bytes`, `contract_iv`, `layout_words`, `calls`) and
-- `crates/leanvm/univariate/tests/keccak_vm.rs` (`KECCAK_RUNS`, `KECCAK_LOG_BYTECODE`: leanVM 9d50c92a3's runs);
-- A declared claim's opening is `UniStatement`'s (`pcsOpenWith`, this repository's `formal/Statement` opening).
module

public import UniKeccak.Verifier

/-!
# The Keccak contract's IV, its claims, and the whole Keccak verifier

* **The layout words** (`layoutWordsK`, `layout_words(shape)`): the three words of `UniStatement.layoutWord`, `C1`,
  `C2` and the setup, from the Keccak VM's layouts (`layoutsOfK`).
* **The IV** (`contractIvKWith`, `contract_iv`): the Keccak-256 of the tag `"leanVM-univar-iv"`, the program's IV,
  the setup's root (`F`: the contract's constant, `SetupRoots::REFERENCE` in the Rust's tests), the shape's bytes, the
  three layout words, then the variant's bytes (`variantBytesK`: `"keccak-vm"`, the skip, the Fiat–Shamir shape's
  code `Main` 0, `Rec` 1, `Rec2` 2, `Rec3` 3). The seed is `keccak(name ‖ IV ‖ public input)`.
* **The calls** (`pcsCallsK`, `calls`): **three**, `C1`, `C2`, the setup, each its one point claim, its root (`C1`'s
  and `C2`'s the stream's, the setup's the constant `F` root) and its layout word.
* **The whole verifier** (`verifyWithK`): the run (`runWithK`, point claims), its verdict, the three calls, each the
  Statement's opening (`pcsOpenWith`) on its stack of `2^vars` words, `vars` its layout word's. A proof is the stream
  and three opening proofs (`KeccakProof`).
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

/-- **`layout_words(shape)`**: `C1`, `C2`, the setup, each its Keccak stack's `vars` and `placed` (`layoutsOfK`). -/
def layoutWordsK (s : Shape) : List (List UInt8) :=
  let stackLayouts := layoutsOfK s
  let wordOf (c : Commitment) : List UInt8 :=
    let l := (stackLayouts.lookup c).getD default
    layoutWord s (layoutCode c) l.vars l.words
  [wordOf .c1, wordOf .c2, wordOf .setup]

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **`contract_iv(shape, v, program_iv, roots)`** over `F`: the Keccak-256 of the tag, the program's IV, the setup's
root, the shape's bytes, the Keccak layout words and the variant's bytes. -/
def contractIvKWith (s : Shape) (v : KeccakVariant) (programIv : List UInt8) (roots : SetupRoots) :
    m (List UInt8) := do
  let d ← keccak256With F (ivTag ++ programIv ++ digestBytes roots.bytecode ++ shapeBytes s ++
    (layoutWordsK s).flatten ++ variantBytesK v)
  return digestBytes d

end With

/-- The Keccak contract's IV over Keccak-f[1600]: the deployed contract's constant. -/
def contractIvK (s : Shape) (v : KeccakVariant) (programIv : List UInt8) (roots : SetupRoots) : List UInt8 :=
  Id.run (contractIvKWith (m := Id) (fun x ↦ pure (keccakF1600 x)) s v programIv roots)

/-- **`calls`** on the Keccak VM: the claims the contract checks declared, in order, one per commitment (`C1`'s and
`C2`'s roots the stream's, the setup's a constant), each with its Keccak layout word; no matrices' claims. -/
def pcsCallsK (shape : Shape) (roots : SetupRoots) (r : Reduced) : List (List UInt8) :=
  let words := layoutWordsK shape
  let header : Commitment → List UInt8 × List UInt8
    | .c1 => (rootWord r.roots.1, words.getD 0 [])
    | .c2 => (rootWord r.roots.2, words.getD 1 [])
    | .setup => (digestBytes roots.bytecode, words.getD 2 [])
  r.openings.map fun (c, o) ↦ openingWords (header c).1 (header c).2 o

/-- **A Keccak proof**: the stream (the row counts, then the rest) and the opening proof the block holds for each of
the three claims (mumbai's format). -/
structure KeccakProof where
  stream : Array UInt8
  c1 : Compile.Proof
  c2 : Compile.Proof
  setup : Compile.Proof

/-- A proof's row counts: the six its stream announces (`rowsOf`). -/
def KeccakProof.rows (p : KeccakProof) : List ℕ := rowsOf p.stream

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The Keccak verifier** over `F`: the run on the stream (point claims; its row counts read and range-checked
there), its verdict, the three claims' openings (`C1`, `C2`, the setup) with their layout words. -/
def verifyWithK (shape : Shape) (v : KeccakVariant) (iv : List UInt8) (roots : SetupRoots)
    (publicInput : Vector UInt8 32) (proof : KeccakProof) : m Bool := do
  let o ← runWithK F shape iv publicInput.toList proof.stream v .point
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let words := layoutWordsK shape
    let callOf : Commitment → Digest × List UInt8 × Compile.Proof
      | .c1 => (rootOf r.roots.1, words.getD 0 [], proof.c1)
      | .c2 => (rootOf r.roots.2, words.getD 1 [], proof.c2)
      | .setup => (roots.bytecode, words.getD 2 [], proof.setup)
    -- C1, C2, the setup: one point claim each.
    let mut ok := r.openings.map (·.1) == commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        let (root, word, p) := callOf c
        ok := ok && (← pcsOpenWith F (layoutWordVars word) root [⟨pt, value⟩] p)
      | _ => ok := false
    -- No matrices' claims.
    if r.matrices.isSome then ok := false
    return ok

end With

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
