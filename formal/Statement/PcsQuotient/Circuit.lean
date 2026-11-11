-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Transcribed from `crates/membership/quotient/src/circuit.rs` (the wiring and the public rows adapted from leanVM,
-- branch PCS-openings-aggregation, commit 651453c6, `crates/flock/src/quotient/circuit.rs`) and
-- `crates/membership/quotient/src/protocol.rs` (`Index`). Keccak's constants and the WHIR commitment's encoder and
-- Merkle tree are leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Keccak.lean`,
-- `Statement/Prover/Ntt.lean`, `Statement/Prover/Run.lean`).
module

public import PcsQuotient.Relation
public import PcsQuotient.Domain
public import PcsQuotient.PcsOpening

/-!
# The circuit and its commitment

**The gate.** A row has four cells `X, Y, C, V` and says `V = Y + C + X·C` (`circuit.rs`). On bits that is
`Y ⊕ (C ∧ ¬X)`: Keccak's χ with `(X, Y, C) = (a[x+1], a[x], a[x+2])`, an XOR with `(0, a, b)`, a NOT with
`(0, 1, a)`. A free input bit is a row whose three inputs are wired to its own output (`v = v + v + v²`, so
`v² = v`).

**The builder** (`Builder`, `circuit.rs`) is transcribed step by step, in the Rust's order, since the order of
the rows is the circuit: the `11` anchor rows first, each later row reading constants or rows before it (or
itself, for an input), constants folded as the Rust folds them (`not`, `xor`, `chi`), Keccak-f[1600] one row per
χ bit and per XOR of θ (`keccakF`), the membership statement (`membership`). `finish` closes it on `2^logRows`
rows: the **packing rows** after every row built (each public `K`-word packed from its `64` bits by `63` rows of
Horner's rule, `(X, Y, C) = (3, b, acc)`, `V = b + 2·acc`), the **anchors** in the first `11` rows (anchor `k`
is `(0, 0, s_k)`, `s_k` the packed word `k` for `k < 8`, then `(0, 0, 0)`, `(0, 1, 1)`, `(0, 3, 3)`), the last
`16` rows **random rows** of three shapes (`RandomShape`, two free cells each), and the **wiring** `σ` sends
each cell to the next cell of its cycle, a cycle being a source (a constant, or a row's `V` cell) and the cells
that read it, in cell order; a free cell is its own cycle.

**The circuit's commitment** (`indexCommitmentWith`, `Index::new`, `Index::commit`, `protocol.rs`): the
wiring polynomial, `σ` read as the points `B(σ(i))` and taken to the novel basis (`Domain.coefficients`), is
the wiring table, committed as a PCS commitment (`PcsOpening.lean`'s `commitmentWith`): the root of leanVM's
WHIR commitment at rate `1/2` and the table's out-of-domain answer. The deployed verifier holds both, computed
over Keccak-f[1600]; in the model the setup computes them over `π` (`Security.lean`). `Index::new` also checks
two properties of the circuit, `errorsHaveTheirOwnPoles` (the soundness argument's) and the wiring's
coefficient `n − 2` nonzero (the honest prover's); `formal/EndToEnd` evaluates both at the membership circuit.

**Cells.** `cells` is every cell's value from the inputs, as the honest prover computes it
(`Circuit::outputs`, `Circuit::cells`, `circuit.rs`): the rows' bits, then the packing rows and the anchors
over `K`.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- `WORD_BITS` (`circuit.rs`): the bits of a public word. -/
def wordBits : ℕ := 64

/-- What a cell reads (`Src`, `circuit.rs`): a constant (`0`, `1`, `3`), row `r`'s `V` cell, or nothing (a
free cell, its own cycle: the random rows'). -/
inductive Src where
  | zero
  | one
  | three
  | row (r : ℕ)
  | free
  deriving DecidableEq, Inhabited

/-- One gate, `V = Y + C + X·C`, by what its three inputs read (`Row`, `circuit.rs`). -/
structure Row where
  x : Src
  y : Src
  c : Src
  deriving DecidableEq, Inhabited

/-- `IDLE`: a row reading zeros. -/
def idle : Row := ⟨.zero, .zero, .zero⟩

/-- `RANDOM_ROWS` (`circuit.rs`): the random rows, the last rows of the circuit. -/
def randomRows : ℕ := 16

/-- `RANDOM_WORDS` (`circuit.rs`): the random words a proof draws for them, two a row. -/
def randomWords : ℕ := 2 * randomRows

/-- The random rows' shapes (`RandomShape`, `circuit.rs`), `(X, Y, C, V)` for the words `(r, s)`:
`Sum` `(0, r, s, r + s)`, `Select` `(s, r, 0, r)`, `Pass` `(1, r, s, r)`. -/
inductive RandomShape where
  | sum
  | select
  | pass
  deriving DecidableEq, Inhabited

/-- `RandomShape::of`: the `k`-th random row's shape. -/
def RandomShape.of (k : ℕ) : RandomShape :=
  if k % 3 = 0 then .sum else if k % 3 = 1 then .select else .pass

/-- `RandomShape::row`: what the row's cells read. -/
def RandomShape.row : RandomShape → Row
  | .sum => ⟨.zero, .free, .free⟩
  | .select => ⟨.free, .free, .zero⟩
  | .pass => ⟨.one, .free, .free⟩

/-- `RandomShape::cells`: the row's four cells for its words. -/
def RandomShape.cells : RandomShape → K → K → K × K × K × K
  | .sum, r, s => (0, r, s, r + s)
  | .select, r, s => (s, r, 0, r)
  | .pass, r, s => (1, r, s, r)

/-- The gate on bits, `y ⊕ (c ∧ ¬x)` (`gate_bits`, `circuit.rs`). -/
def gateBits (x y c : Bool) : Bool := y ^^ (c && !x)

/-- The gate over `K`, `y + c + x·c` (`gate_k`, `circuit.rs`). -/
def gateK (x y c : K) : K := y + c + x * c

/-- **A circuit** (`Circuit`, `circuit.rs`): its rows (the anchors included, then idle rows up to
`2^logRows`, the random rows last), the rows that are free input bits in the order they are read, the
wiring, cell `4r + role` (roles `X, Y, C, V`) to the next cell of its cycle, and the packing rows
`[start, start + len)`. -/
structure Circuit where
  logRows : ℕ
  usedRows : ℕ
  rows : Array Row
  inputs : Array ℕ
  sigma : Array ℕ
  packing : ℕ × ℕ

/-! ### The builder -/

/-- The builder's state: the rows so far and the input rows. -/
structure Builder where
  rows : Array Row
  inputs : Array ℕ

/-- Building a circuit. -/
abbrev BuildM := StateM Builder

namespace Build

/-- A row; what reads its output. -/
def row (x y c : Src) : BuildM Src :=
  modifyGet fun b ↦ (.row b.rows.size, { b with rows := b.rows.push ⟨x, y, c⟩ })

/-- A free bit: a row reading its own output three times (`input`, `circuit.rs`). -/
def input : BuildM Src := do
  let b ← get
  set { b with inputs := b.inputs.push b.rows.size }
  row (.row b.rows.size) (.row b.rows.size) (.row b.rows.size)

/-- `¬a`, a constant folded (`not`, `circuit.rs`): `(0, 1, a)`. -/
def not : Src → BuildM Src
  | .zero => pure .one
  | .one => pure .zero
  | a => row .zero .one a

/-- `a ⊕ b`, constants folded (`xor`, `circuit.rs`): `(0, a, b)`. -/
def xor : Src → Src → BuildM Src
  | .zero, v => pure v
  | v, .zero => pure v
  | .one, v => not v
  | v, .one => not v
  | a, b => row .zero a b

/-- `a ⊕ (¬b ∧ c)`, Keccak's χ, in one row unless a constant makes it cheaper (`chi`, `circuit.rs`):
`(b, a, c)`. -/
def chi (a : Src) : Src → Src → BuildM Src
  | .one, _ => pure a
  | _, .zero => pure a
  | .zero, c => xor a c
  | b, .one => do xor a (← not b)
  | b, c => row b a c

/-- A Keccak state of wires: lane `x + 5y`, bit `z` at index `64·(x + 5y) + z`. -/
abbrev WireState : Type := Array Src

/-- Wire `(lane, z)` of a state. -/
def WireState.at (a : WireState) (lane z : ℕ) : Src := a.getD (64 * lane + z) .zero

/-- One round of Keccak-f[1600] with the round constant `rc` (`keccak_f`, `circuit.rs`), the
rows in the Rust's order: θ's column parities (lane `x`, bit `z`, folding `y = 1 … 4`), then its
`d`, then each lane XORed with its `d`; ρ and π as wiring (lane `i`, rotated left by `ρ_i`, goes to
`π_i`); χ, one row a bit, `y`, `x`, `z` in that order; ι, a NOT where `rc` has a one. -/
def round (a : WireState) (rc : UInt64) : BuildM WireState := do
  -- θ: the column parities.
  let mut c : Array Src := Array.replicate (5 * 64) .zero
  for x in [0:5] do
    for z in [0:64] do
      let mut acc := a.at x z
      for y in [1:5] do
        acc ← xor acc (a.at (x + 5 * y) z)
      c := c.set! (64 * x + z) acc
  let cAt (x z : ℕ) : Src := c.getD (64 * x + z) .zero
  let mut d : Array Src := Array.replicate (5 * 64) .zero
  for x in [0:5] do
    for z in [0:64] do
      d := d.set! (64 * x + z) (← xor (cAt ((x + 4) % 5) z) (cAt ((x + 1) % 5) ((z + 63) % 64)))
  let mut a := a
  for i in [0:25] do
    for z in [0:64] do
      a := a.set! (64 * i + z) (← xor (a.at i z) (d.getD (64 * (i % 5) + z) .zero))
  -- ρ and π: wiring only.
  let mut b : WireState := Array.replicate 1600 .zero
  for i in [0:25] do
    let r := LeanVM.Parameters.keccakRho.getD i 0
    for z in [0:64] do
      b := b.set! (64 * LeanVM.Parameters.keccakPi i + (z + r) % 64) (a.at i z)
  -- χ: one row a bit.
  for y in [0:5] do
    for x in [0:5] do
      for z in [0:64] do
        a := a.set! (64 * (x + 5 * y) + z)
          (← chi (b.at (x + 5 * y) z) (b.at ((x + 1) % 5 + 5 * y) z) (b.at ((x + 2) % 5 + 5 * y) z))
  -- ι.
  for z in [0:64] do
    if (rc >>> z.toUInt64) &&& 1 = 1 then
      a := a.set! z (← not (a.at 0 z))
  return a

/-- **Keccak-f[1600]** on wires: the `24` rounds (`keccak_f`). -/
def keccakF (a : WireState) : BuildM WireState :=
  LeanVM.Parameters.keccakRC.foldlM round a

/-- **Keccak-256 of a 64-byte block** on wires (`keccak256_64`, `circuit.rs`): the message's
`512` bits (byte order, low bit first) in the first eight lanes, Keccak's padding of a 64-byte
message in one block (`0x01` at byte `64`, `0x80` at byte `135`), the digest's `256` bits likewise.
-/
def keccak256Block (message : List Src) : BuildM (List Src) := do
  let state : WireState := Array.ofFn (n := 1600) fun i ↦
    if i.val < 512 then message.getD i.val .zero
    else if i.val = 64 * 8 ∨ i.val = 64 * 16 + 63 then .one
    else .zero
  let out ← keccakF state
  return (List.range 256).map fun b ↦ out.getD b .zero

end Build

/-! ### Closing a circuit: the packing rows, the anchors, the random rows and the wiring -/

/-- The wiring of `2^logRows` rows (`finish`, `circuit.rs`): every cell starts as its own successor; each
row's `V` cell opens its row's cycle (row order), then each reading cell joins the cycle of what it reads
(row order, roles `X, Y, C`; a free cell joins none), the last cell of a cycle sending back to its first. The
cycles' slots: `0`, `1`, `3`, then row `r` at `3 + r`. -/
def wiring (logRows : ℕ) (rows : Array Row) : Array ℕ := Id.run do
  let n := 2 ^ logRows
  let none := 4 * n
  let mut first : Array ℕ := Array.replicate (n + 3) none
  let mut last : Array ℕ := Array.replicate (n + 3) none
  let mut sigma : Array ℕ := Array.range (4 * n)
  let slot : Src → Option ℕ
    | .zero => some 0
    | .one => some 1
    | .three => some 2
    | .row r => some (3 + r)
    | .free => Option.none
  -- join `cell` to the cycle of source slot `at_`.
  for r in [0:n] do
    let (at_, cell) := (3 + r, 4 * r + 3)
    if first[at_]! = none then first := first.set! at_ cell
    else sigma := sigma.set! last[at_]! cell
    last := last.set! at_ cell
    sigma := sigma.set! cell first[at_]!
  for r in [0:n] do
    let row := rows.getD r idle
    for (role, src) in [(0, row.x), (1, row.y), (2, row.c)] do
      match slot src with
      | Option.none => pure ()
      | some at_ =>
        let cell := 4 * r + role
        if first[at_]! = none then first := first.set! at_ cell
        else sigma := sigma.set! last[at_]! cell
        last := last.set! at_ cell
        sigma := sigma.set! cell first[at_]!
  return sigma

/-- One public word packed from its `64` bit wires by `63` rows of Horner's rule (`finish`, `circuit.rs`):
`acc` starts at bit `63`, then for bits `62, …, 0` a row `(3, bit, acc)`, `V = bit + 2·acc`. -/
def packWord (bits : List Src) : BuildM Src :=
  ((bits.take (wordBits - 1)).reverse).foldlM (fun acc bit ↦ Build.row .three bit acc)
    (bits.getD (wordBits - 1) .zero)

/-- **Close the circuit** on `2^logRows` rows (`finish`, `circuit.rs`), `public[J][j]` being bit `j` of public
word `J < 8`: the packing rows after every row built; the anchors in the first `11` rows (anchor `k` is
`(0, 0, s_k)`, `s_k` the packed word `k` for `k < 8`, then the constants `0`, `1`, `3`, the anchors of `1` and
`3` reading their constant as `Y` too); idle rows to `2^logRows`; the last `16` rows random rows, the `k`-th
from the last of shape `RandomShape.of k` (the Rust asserts there is room: the membership circuit uses
`3 878 615` rows of `2^22`); the wiring. -/
def finish (logRows : ℕ) (public_ : List (List Src)) (b : Builder) : Circuit :=
  let start := b.rows.size
  let r := ((public_.mapM packWord).run b).run
  let words := r.1
  let b := r.2
  let sources : List Src := words ++ [.zero, .one, .three]
  let n := 2 ^ logRows
  let rows := Array.ofFn (n := n) fun r ↦
    if r.val < publicRows then
      let c := sources.getD r.val .zero
      ⟨.zero, (if c = .one ∨ c = .three then c else .zero), c⟩
    else if n - randomRows ≤ r.val then (RandomShape.of (n - 1 - r.val)).row
    else b.rows.getD r.val idle
  ⟨logRows, b.rows.size, rows, b.inputs, wiring logRows rows, (start, b.rows.size - start)⟩

/-- **The random rows** (`Circuit::random_rows`, `circuit.rs`), from the last: the `k`-th is of shape
`RandomShape.of k`, and takes the random words `2k`, `2k + 1`. -/
def Circuit.randomRows (c : Circuit) : List ℕ :=
  (List.range PcsQuotient.randomRows).map fun k ↦ c.rows.size - 1 - k

/-- `public_words` (`circuit.rs`): the `256` wires of `y` and of `root` (bit `i` bit `i % 8` of byte `i / 8`) as
the eight public words they are read as, a word being eight bytes, big-endian. -/
def publicWordWires (y root : List Src) : List (List Src) :=
  (List.range publicWords).map fun word ↦
    (List.range wordBits).map fun j ↦
      (if word < 4 then y else root).getD (8 * (8 * (word % 4) + 7 - j / 8) + j % 8) .zero

/-- `constant_block` (`circuit.rs`): the `256` constant wires of 32 copies of `byte`. -/
def constantBlock (byte : UInt8) : List Src :=
  (List.range 256).map fun i ↦ if (byte >>> (i % 8).toUInt8) &&& 1 = 1 then .one else .zero

/-- The builder of the membership statement (`membership`, `circuit.rs`): the `256` input
bits of `x`; `y = H(x ‖ 0x11^32)` and the leaf `H(x ‖ 0x22^32)`; then each level: the sibling's `256`
input bits, the direction's, and `left = node ⊕ (direction ∧ (node ⊕ sibling))` (one χ, which negates
its middle input, reading `¬direction`), `right = left ⊕ node ⊕ sibling`, the node `H(left ‖ right)`.
Returns the wires of `y` and of the root. -/
def membershipBuilder : BuildM (List Src × List Src) := do
  let x ← (List.range 256).mapM fun _ ↦ Build.input
  let y ← Build.keccak256Block (x ++ constantBlock yPad)
  let mut node ← Build.keccak256Block (x ++ constantBlock leafPad)
  for _ in [0:depth] do
    let sibling ← (List.range 256).mapM fun _ ↦ Build.input
    let direction ← Build.input
    let keep ← Build.not direction
    let mut left : Array Src := #[]
    let mut right : Array Src := #[]
    for i in [0:256] do
      let differ ← Build.xor (node.getD i .zero) (sibling.getD i .zero)
      let l ← Build.chi (node.getD i .zero) keep differ
      right := right.push (← Build.xor l differ)
      left := left.push l
    node ← Build.keccak256Block (left.toList ++ right.toList)
  return (y, node)

/-- An empty builder: the anchor rows, idle until `finish`. -/
def Builder.new : Builder := ⟨Array.replicate publicRows idle, #[]⟩

/-- **The membership circuit** on `2^logRows` rows (`membership`, `circuit.rs`; deployed at
`logRows = 22`, `3 878 615` rows used). The builder's run is read by its projections (`r.1.1` the
wires of `y`, `r.1.2` those of the root, `r.2` the builder), not by a pattern match, so that a proof
about the circuit's fields never has to evaluate the run (a match on it is reduced only once the
`2^22`-row run is computed). -/
def membership (logRows : ℕ) : Circuit :=
  let r := (membershipBuilder.run Builder.new).run
  finish logRows (publicWordWires r.1.1 r.1.2) r.2

/-- `membership_inputs` (`circuit.rs`): the free inputs of `membership` for a secret, `x`'s
bits, then each level's sibling's bits and its direction, a byte's bits low first. -/
def membershipInputs (w : Secret) : List Bool :=
  let bits (b : Bytes32) : List Bool := (List.range 256).map fun i ↦ (b.toList.getD (i / 8) 0 >>> (i % 8).toUInt8) &&& 1 = 1
  bits w.x ++ (List.finRange depth).flatMap fun i ↦ bits w.siblings[i] ++ [w.directions[i]]

/-- The secret the membership circuit's input bits spell (the inverse of `membershipInputs`): `x`
from the first `256`, then each level's sibling and direction from the next `257`. -/
def secretOfInputs (bits : List Bool) : Secret :=
  let bytes (from_ : ℕ) : Bytes32 := Vector.ofFn fun j : Fin 32 ↦
    (List.range 8).foldl (fun acc k ↦ if bits.getD (from_ + 8 * j.val + k) false then acc ||| (1 <<< k.toUInt8) else acc) 0
  ⟨bytes 0, Vector.ofFn fun i ↦ bytes (256 + 257 * i.val),
    Vector.ofFn fun i ↦ bits.getD (256 + 257 * i.val + 256) false⟩

/-! ### Cells -/

/-- The bit a source holds, given every row's output (`read`, `circuit.rs`): a free cell and the constant
three read as `0` (the bits are not the packing rows' values, which `cells` takes over `K`). -/
def readSrc (v : Array Bool) : Src → Bool
  | .zero => false
  | .one => true
  | .three => false
  | .row r => v.getD r false
  | .free => false

/-- Every row's output bit from the free inputs (`Circuit::outputs`, `circuit.rs`): the inputs set, then each
row from `11` on and the anchors last, each from rows before it. -/
def Circuit.outputs (c : Circuit) (inputs : List Bool) : Array Bool := Id.run do
  let mut v : Array Bool := Array.replicate c.rows.size false
  for (r, bit) in c.inputs.toList.zip inputs do
    v := v.set! r bit
  for r in List.range' publicRows (c.rows.size - publicRows) ++ List.range publicRows do
    let row := c.rows.getD r idle
    v := v.set! r (gateBits (readSrc v row.x) (readSrc v row.y) (readSrc v row.c))
  return v

/-- The `K` value a source holds, given every row's output (`read_k`, `circuit.rs`; a free cell's is the
witness's `0`). -/
def readK (v : Array K) : Src → K
  | .zero => 0
  | .one => 1
  | .three => three
  | .row r => v.getD r 0
  | .free => 0

/-- **Every row's output over `K`** (`Circuit::cells`, `circuit.rs`): the rows' bits, then the packing rows and
the anchors, in that order, over `K`. -/
def Circuit.outputsK (c : Circuit) (inputs : List Bool) : Array K := Id.run do
  let bits := c.outputs inputs
  let mut v : Array K := bits.map fun b ↦ if b then 1 else 0
  for r in List.range' c.packing.1 c.packing.2 ++ List.range publicRows do
    let row := c.rows.getD r idle
    v := v.set! r (gateK (readK v row.x) (readK v row.y) (readK v row.c))
  return v

/-- **Every cell's value from the free inputs** (`Circuit::cells`, `Circuit::cells_k`, `circuit.rs`): cell
`4r + role` holds what role `X`, `Y`, `C` of row `r` reads, or the row's output for `V`. The random rows' cells
are the witness's zeros; the prover fills them (`Prover.lean`). -/
def Circuit.cells (c : Circuit) (inputs : List Bool) : Array K :=
  let v := c.outputsK inputs
  Array.ofFn (n := 4 * c.rows.size) fun i ↦
    let row := c.rows.getD (i.val / 4) idle
    match i.val % 4 with
    | 0 => readK v row.x
    | 1 => readK v row.y
    | 2 => readK v row.c
    | _ => v.getD (i.val / 4) 0

/-! ### The conditions `Index::new` checks -/

/-- Walk a cycle of `sigma` from `at_` until a seen cell, marking each cell seen; the walk's length and whether
it met a cell `ok` holds of. At most `fuel` steps. -/
def walkCycle (sigma : Array ℕ) (ok : ℕ → Bool) :
    ℕ → Array Bool → ℕ → ℕ → Bool → Array Bool × ℕ × Bool
  | 0, seen, _, len, met => (seen, len, met)
  | fuel + 1, seen, at_, len, met =>
    if seen.getD at_ true then (seen, len, met)
    else walkCycle sigma ok fuel (seen.set! at_ true) (sigma.getD at_ at_) (len + 1) (met || ok at_)

/-- **`errors_have_their_own_poles`** (`Circuit::errors_have_their_own_poles`, `circuit.rs`): every cycle of the
wiring but a lone cell's holds a cell that is neither a row's first (`X`) cell nor a pinned one
(`anchorCell k`, `k < 11`), nor a cell of a random row. The soundness argument's condition on the circuit
(`docs/membership/PROTOCOL.md`, "The pole lemma"), computed by the Rust's walk from each cell not yet seen. -/
def Circuit.errorsHaveTheirOwnPoles (c : Circuit) : Bool :=
  let total := c.sigma.size
  let ok (cell : ℕ) : Bool :=
    cell % 4 != 0 && !(cell % 4 = 2 && cell / 4 < publicRows) && !(c.rows.size - PcsQuotient.randomRows ≤ cell / 4)
  ((List.range total).foldl
    (fun (st : Array Bool × Bool) start ↦
      if st.1.getD start true then st
      else
        let (seen, len, met) := walkCycle c.sigma ok total st.1 start 0 false
        (seen, st.2 && (len ≤ 1 || met)))
    (Array.replicate total false, true)).2

/-! ### The circuit's commitment -/

/-- **The wiring table** (`Index::new`, `protocol.rs`): `B(σ(i))` for every cell, in the novel
basis; it is committed as it is (`m` variables). -/
def Circuit.wiringTable (c : Circuit) : Array K :=
  Domain.coefficients (c.logRows + 2) 0 (c.sigma.map Domain.point)

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The circuit's commitment** over `F` (`Index::commit`): the PCS commitment of its wiring table, `m`
variables. -/
def Circuit.indexCommitmentWith (c : Circuit) : m Commitment := do
  return (← commitmentWith F (c.logRows + 2) c.wiringTable).2

/-- **The circuit's commitment's tree** over `F`: the Merkle tree of the WHIR commitment of its wiring
table, whose root is `indexCommitmentWith`'s (the setup computes it, `Security.lean`; the extractor reads its
Keccak-256 evaluations, `Tree.evaluations`). -/
def Circuit.indexTreeWith (c : Circuit) : m LeanVM.Prover.Tree :=
  commitWith F (c.logRows + 2) c.wiringTable

end With

/-- **The Keccak-256 evaluations a Merkle tree holds** (mumbai's `Tree`, as `buildTreeM` builds it),
in the order `buildTreeM` computes them: each of the `2^height` leaves' bytes (`kBytes` of its row's
words) with its digest, then, level by level from the leaves up, each node's `64` bytes (its two
children's digests) with its digest. A pure function of the tree. For the circuit's commitment
(`Circuit.indexTreeWith`) these are the setup's Keccak-256 evaluations, which the extractor reads
(`Security.lean`, `Extractor.lean`). -/
def Tree.evaluations (t : LeanVM.Prover.Tree) : List (List UInt8 × Digest) :=
  let level (l : ℕ) : Array Digest := t.levels.getD l #[]
  (List.range (2 ^ t.height)).map (fun i ↦ ((t.word i).flatMap kBytes, (level 0).getD i default)) ++
    (List.range t.height).flatMap fun l ↦ (List.range (2 ^ (t.height - (l + 1)))).map fun j ↦
      (digestBytes ((level l).getD (2 * j) default) ++ digestBytes ((level l).getD (2 * j + 1) default),
        (level (l + 1)).getD j default)

end PcsQuotient

end
