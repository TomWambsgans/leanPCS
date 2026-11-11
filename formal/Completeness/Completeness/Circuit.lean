-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): Keccak-256 (`Statement/Keccak.lean`, `keccak256`, `Digest.toBytes`).
import QuotientSecurity.Pinning
import Statement.Keccak

/-!
# The circuit's completeness: an honest witness satisfies the relation

`crates/membership/quotient/src/statement.rs`: the statement is `y = H(x ‖ 0x11^32)` and the root of a
Merkle path of depth `32` from `H(x ‖ 0x22^32)`, `H` Keccak-256 of a 64-byte block (`pair`); the
secret is `x`, the siblings and the directions (`Secret`, `Secret.statement`). Here they are
transcribed with leanerVM `mumbai`'s Keccak-256 (`keccak256`, the deployed function, transcribed
from leanVM's verifier and executed against it there).

**The interface F0b discharges** (`MembershipCircuit`): the deployed circuit as a Lean
`ChiCircuit` `C`, the assignment of its rows the Rust builder computes from a secret (`assign`,
the circuit evaluated on the secret's input bits), and, **in the forward direction, Keccak
correctness**: the assignment satisfies every gate (`satisfies`), and its public bits are the
bits of the statement the secret proves (`publicBits`, as `circuit::public_words` reads `y` and
`root`), with words 4 to 7 laid as `Builder::finish` lays them (`1, 0, 0, 0`) and the public rows
not random rows (`pubRows`). These are fields
of a structure, so every theorem below that takes a `MembershipCircuit` holds of whatever F0b
builds; nothing about Keccak is assumed beyond them.

`honest_relation`: on an instance whose wiring keeps what each cell carries (`WiringKeeps`: the
source it reads, or its row for a `V` cell; `wiringOf C` does, `wiringKeeps_wiringOf`, and so does
the deployed σ, `QuotientSecurity.deployedSigma_cellSrc`) and whose bit weights are
`coordinate_weight`'s, the cells of the assignment (`cellsOfBits`) satisfy the relation for the
statement's eight words (`statementWords`: the halves of `(y, root)`, then `1, 0, 0, 0`). F0a's
`relation_statementWords` (for `wiringOf C`) is the step from words to the relation, here for any
such wiring (`relation_statementWords_keeps`); the words are the bits' weighted sums
(`halves_eq_sum`), so no independence of the weights is needed in this direction.

**The random rows** (`honest_relation_random`): the honest prover fills the `X` and `V` cells of
each of the circuit's `16` random rows with a fresh value (`randomizeCells`, `prove` in
`protocol.rs`); with *any* values there (`cellsRandomized`), the cells still satisfy the relation:
a random row's gate is `V = V + 0 + 0`, its `X` cell and its `V` cell are the only cells carrying it
(`cellsRandomized_eq`: the cells are those of the row values, `cellsOfVals`), and no other row reads
it.
-/

set_option linter.unusedSectionVars false

open Finset

namespace Completeness

open QuotientSecurity

/-- Thirty-two bytes. -/
abbrev Bytes32 := Fin 32 → UInt8

/-- **`statement::pair`**: Keccak-256 of the 64 bytes `left ‖ right`. -/
def pair (left right : Bytes32) : Bytes32 := fun i =>
  (LeanVM.Protocol.Digest.toBytes
    (LeanVM.Protocol.KeccakHash.keccak256 (List.ofFn left ++ List.ofFn right)))[i]

/-- `Y_PAD`, `LEAF_PAD`. -/
def yPad : UInt8 := 0x11
def leafPad : UInt8 := 0x22

/-- **`statement::Secret`**: `x`, the `DEPTH = 32` siblings, and the directions (bit `i`: the
sibling is on the left at level `i`). -/
structure Secret where
  x : Bytes32
  siblings : Fin 32 → Bytes32
  directions : Fin 32 → Bool

/-- **`statement::Statement`**: the public values. -/
structure Statement where
  y : Bytes32
  root : Bytes32

/-- The leaf: `H(x ‖ 0x22^32)`. -/
def Secret.leaf (s : Secret) : Bytes32 := pair s.x fun _ => leafPad

/-- The root: the path folded from the leaf, level `0` first. -/
def Secret.root (s : Secret) : Bytes32 :=
  (List.finRange 32).foldl
    (fun node i => if s.directions i then pair (s.siblings i) node else pair node (s.siblings i))
    s.leaf

/-- **`Secret::statement`**: `y = H(x ‖ 0x11^32)` and the root. -/
def Secret.statement (s : Secret) : Statement :=
  ⟨pair s.x (fun _ => yPad), s.root⟩

/-- **What F0b proves of the deployed circuit** (layer F0 of `formal/README.md`): the circuit as
a Lean `ChiCircuit` on `2^22` rows, the assignment its builder computes from a secret, and Keccak
correctness in the forward direction: that assignment satisfies every gate, and its public bits
are the statement's (`y`'s and `root`'s bits as `circuit::public_words` reads them); words 4 to 7
read `1, 0, 0, 0`. -/
structure MembershipCircuit where
  C : ChiCircuit (Fin (2 ^ 22))
  /-- The rows' outputs the circuit computes from a secret (`Builder`'s evaluation). -/
  assign : Secret → Fin (2 ^ 22) → Bool
  /-- Every gate holds. -/
  satisfies : ∀ s, C.SatisfiesBits (assign s)
  /-- **Keccak correctness, forward**: the public bits are the statement's. -/
  publicBits : ∀ (s : Secret) (J : Fin 4) (j : Fin 128),
    C.pubBit (assign s) (Fin.castLE (by norm_num) J) j =
      statementBit s.statement.y s.statement.root J j
  word4_one : C.pubSrc 4 0 = .one
  word4 : ∀ j, j ≠ 0 → C.pubSrc 4 j = .zero
  word5 : ∀ j, C.pubSrc 5 j = .zero
  word6 : ∀ j, C.pubSrc 6 j = .zero
  word7 : ∀ j, C.pubSrc 7 j = .zero
  /-- The public rows are not random rows. -/
  pubRows : ∀ J j, ¬ C.isRandom (pubRow J j)

/-- **The wiring `σ` keeps what each cell carries in `C`** (`ChiCircuit.cellSrc`: the source an
`X`, `Y`, `C` cell reads, the row of a `V` cell): a cycle of `σ` never mixes two sources, so the
cells of a computation, each holding the bit of what it carries, are copied by `σ`. -/
def WiringKeeps (σ : Equiv.Perm (Fin (22 + 2) → Bool)) (C : ChiCircuit (Fin (2 ^ 22))) : Prop :=
  ∀ z, C.cellSrc (σ z) = C.cellSrc z

/-- `wiringOf C`, whose cycles are the classes of `cellSrc`, keeps them. -/
theorem wiringKeeps_wiringOf (C : ChiCircuit (Fin (2 ^ 22))) : WiringKeeps (wiringOf C) C :=
  wiringOf_cellSrc C

variable {F : Type} [Field F] [DecidableEq F] [CharP F 2]

/-- **The relation holds of `C`'s computations on a wiring keeping what the cells carry**
(F0a's `relation_wiringOf`, for any such wiring). -/
theorem relation_keeps (I : Instance F) (C : ChiCircuit (Fin (2 ^ 22))) {x Y : F}
    (hc : I.c = coordWeight x Y) (hw : WiringKeeps I.wiring C) (v : Fin (2 ^ 22) → Bool)
    (hv : C.SatisfiesBits v) : I.Relation (fun J => C.pubWord x Y v J) (C.cellsOfBits v) := by
  refine ⟨fun y => ?_, fun z => ?_, fun J => ?_⟩
  · obtain ⟨r, rfl⟩ := rowEquiv.surjective y
    have hcell : ∀ k : Fin 4, (C.cellsOfBits v (cellBits (rowEquiv r, k)) : F)
        = bitF ((C.srcOf r k).bval v) := fun k =>
      congrArg (fun s => bitF (Src.bval v s)) (C.cellSrc_rowCell r k)
    rw [hcell, hcell, hcell, hcell]
    exact (gate_bitF _ _ _ _).mpr (hv r)
  · simp only [ChiCircuit.cellsOfBits, hw z]
  · classical
    rw [hc, sum_regionWeight _ (coordWeight_one x Y)]
    unfold ChiCircuit.pubWord
    refine sum_congr rfl fun j _ => ?_
    rw [regionWeight_coordWeight]
    simp only [ChiCircuit.cellsOfBits, ChiCircuit.cellSrc_pubCell, ChiCircuit.pubBit]

/-- **Completeness of the circuit's relation for `(y, root)`** on a wiring keeping what the cells
carry (F0a's `relation_statementWords`, for any such wiring). -/
theorem relation_statementWords_keeps (I : Instance F) (C : ChiCircuit (Fin (2 ^ 22))) {x Y : F}
    (hc : I.c = coordWeight x Y) (hw : WiringKeeps I.wiring C)
    (h4one : C.pubSrc 4 0 = .one) (h4 : ∀ j, j ≠ 0 → C.pubSrc 4 j = .zero)
    (h5 : ∀ j, C.pubSrc 5 j = .zero) (h6 : ∀ j, C.pubSrc 6 j = .zero)
    (h7 : ∀ j, C.pubSrc 7 j = .zero) (v : Fin (2 ^ 22) → Bool) (hv : C.SatisfiesBits v)
    (y root : Fin 32 → UInt8)
    (hpub : ∀ J : Fin 4, C.pubWord x Y v (Fin.castLE (by norm_num) J) = halves x Y y root J) :
    I.Relation (statementWords x Y y root) (C.cellsOfBits v) := by
  have hs : (fun J => C.pubWord x Y v J) = statementWords x Y y root := by
    funext J
    fin_cases J
    · exact hpub 0
    · exact hpub 1
    · exact hpub 2
    · exact hpub 3
    · exact C.pubWord_four x Y v h4one h4
    · exact C.pubWord_zero x Y v 5 h5
    · exact C.pubWord_zero x Y v 6 h6
    · exact C.pubWord_zero x Y v 7 h7
  rw [← hs]
  exact relation_keeps I C hc hw v hv

/-- A public word of the assignment is the statement's half, as the bits are. -/
theorem pubWord_eq_halves (M : MembershipCircuit) (x Y : F) (s : Secret) (J : Fin 4) :
    M.C.pubWord x Y (M.assign s) (Fin.castLE (by norm_num) J) =
      halves x Y s.statement.y s.statement.root J := by
  rw [halves_eq_sum, ChiCircuit.pubWord]
  exact sum_congr rfl fun j _ => by rw [M.publicBits s J j]

/-- **The honest cells satisfy the relation.** On an instance whose wiring keeps what the
circuit's cells carry (`wiringOf M.C`, or the deployed σ) and whose bit weights are
`coordinate_weight`'s, the cells of the assignment of a secret satisfy the relation for the eight
words of the statement it proves. -/
theorem honest_relation (M : MembershipCircuit) (I : Instance F) {x Y : F}
    (hc : I.c = coordWeight x Y) (hw : WiringKeeps I.wiring M.C) (s : Secret) :
    I.Relation (statementWords x Y s.statement.y s.statement.root) (M.C.cellsOfBits (M.assign s)) :=
  relation_statementWords_keeps I M.C hc hw M.word4_one M.word4 M.word5 M.word6 M.word7 (M.assign s)
    (M.satisfies s) _ _ (pubWord_eq_halves M x Y s)

/-! ## The random rows filled with arbitrary values -/

/-- A row that is not a random row reads no random row: it is an input (reading itself) or reads
rows that are not random. -/
theorem srcs_not_random (C : ChiCircuit (Fin (2 ^ 22))) {r : Fin (2 ^ 22)} (hr : ¬ C.isRandom r)
    (s : Src (Fin (2 ^ 22))) (hs : s = C.x r ∨ s = C.y r ∨ s = C.c r) :
    ∀ r', s = .row r' → ¬ C.isRandom r' := by
  intro r' h
  by_cases hi : C.isInput r
  · obtain ⟨hx, hy, hc⟩ := C.hInput r hi
    rw [hx, hy, hc, h] at hs
    have e : r' = r := by rcases hs with hs | hs | hs <;> exact Src.row.inj hs
    rw [e]; exact hr
  · exact (C.reads hi hr s hs r' h).2

/-- What each cell carries, valued by the rows' values `u`. -/
noncomputable def _root_.QuotientSecurity.ChiCircuit.cellsOfVals (C : ChiCircuit (Fin (2 ^ 22))) (u : Fin (2 ^ 22) → F) :
    (Fin (22 + 2) → Bool) → F :=
  fun z => (C.cellSrc z).val u

/-- The rows' values: the computation's bits off the random rows, `rnd` on them. -/
noncomputable def _root_.QuotientSecurity.ChiCircuit.rowVals (C : ChiCircuit (Fin (2 ^ 22))) (v : Fin (2 ^ 22) → Bool)
    (rnd : Fin (2 ^ 22) → F) : Fin (2 ^ 22) → F :=
  open Classical in fun r => if C.isRandom r then rnd r else bitF (v r)

theorem val_rowVals (C : ChiCircuit (Fin (2 ^ 22))) (v : Fin (2 ^ 22) → Bool) (rnd : Fin (2 ^ 22) → F)
    (s : Src (Fin (2 ^ 22))) (hs : ∀ r', s = .row r' → ¬ C.isRandom r') :
    s.val (C.rowVals v rnd) = bitF (s.bval v) := by
  classical
  cases s with
  | zero => rfl
  | one => rfl
  | row r' =>
    show (if C.isRandom r' then rnd r' else bitF (v r')) = _
    rw [if_neg (hs r' rfl)]
    rfl

open Classical in
/-- **The honest cells with the random rows filled** (`randomizeCells`, `Prover.lean`): the cells of
the computation `v` (`cellsOfBits`), but the `X` and `V` cells of each random row `r` hold `rnd r`. -/
noncomputable def _root_.QuotientSecurity.ChiCircuit.cellsRandomized (C : ChiCircuit (Fin (2 ^ 22))) (v : Fin (2 ^ 22) → Bool)
    (rnd : Fin (2 ^ 22) → F) : (Fin (22 + 2) → Bool) → F :=
  fun z => if C.isRandom (cellRow z) ∧ (cellRole z = 0 ∨ cellRole z = 3) then rnd (cellRow z)
    else C.cellsOfBits v z

/-- **The randomized cells are the cells of the row values** `rowVals v rnd`: a random row's `X` and
`V` cells carry its value, its `Y` and `C` cells the one and the zero; every other cell carries a
row that is not random, or a constant. -/
theorem cellsRandomized_eq (C : ChiCircuit (Fin (2 ^ 22))) (v : Fin (2 ^ 22) → Bool)
    (rnd : Fin (2 ^ 22) → F) : C.cellsRandomized v rnd = C.cellsOfVals (C.rowVals v rnd) := by
  classical
  funext z
  obtain ⟨r, k, rfl⟩ : ∃ r k, rowCell r k = z := ⟨_, _, rowCell_cellRow z⟩
  obtain ⟨h1, h2⟩ := cellRow_rowCell r k
  unfold ChiCircuit.cellsRandomized ChiCircuit.cellsOfVals ChiCircuit.cellsOfBits
  rw [h1, h2, ChiCircuit.cellSrc_rowCell]
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> simp
  by_cases hr : C.isRandom r
  · obtain ⟨hx, hy, hc⟩ := C.hRandom r hr
    have hu : C.rowVals v rnd r = rnd r := if_pos hr
    rcases hk with rfl | rfl | rfl | rfl
    · rw [if_pos ⟨hr, Or.inl rfl⟩]
      show rnd r = (C.x r).val _
      rw [hx]; exact hu.symm
    · rw [if_neg (fun h => by rcases h.2 with h | h <;> exact absurd h (by decide))]
      show bitF ((C.y r).bval v) = (C.y r).val _
      rw [hy]; rfl
    · rw [if_neg (fun h => by rcases h.2 with h | h <;> exact absurd h (by decide))]
      show bitF ((C.c r).bval v) = (C.c r).val _
      rw [hc]; rfl
    · rw [if_pos ⟨hr, Or.inr rfl⟩]
      show rnd r = C.rowVals v rnd r
      exact hu.symm
  · rw [if_neg (fun h => hr h.1)]
    have hrow : ∀ r', Src.row r = Src.row r' → ¬ C.isRandom r' := fun r' h => by
      rw [← Src.row.inj h]; exact hr
    rcases hk with rfl | rfl | rfl | rfl
    · exact (val_rowVals C v rnd _ (srcs_not_random C hr _ (Or.inl rfl))).symm
    · exact (val_rowVals C v rnd _ (srcs_not_random C hr _ (Or.inr (Or.inl rfl)))).symm
    · exact (val_rowVals C v rnd _ (srcs_not_random C hr _ (Or.inr (Or.inr rfl)))).symm
    · exact (val_rowVals C v rnd _ hrow).symm

/-- **The relation holds of the row values `rowVals v rnd`**, any `rnd`, on a wiring keeping what
the cells carry: a random row's gate is `V = V + 0 + 0`, every other row's the gate on bits, and the
public rows read no random row. -/
theorem relation_vals (I : Instance F) (C : ChiCircuit (Fin (2 ^ 22))) {x Y : F}
    (hc : I.c = coordWeight x Y) (hw : WiringKeeps I.wiring C)
    (hpub : ∀ J j, ¬ C.isRandom (pubRow J j)) (v : Fin (2 ^ 22) → Bool) (hv : C.SatisfiesBits v)
    (rnd : Fin (2 ^ 22) → F) :
    I.Relation (fun J => C.pubWord x Y v J) (C.cellsOfVals (C.rowVals v rnd)) := by
  classical
  refine ⟨fun y => ?_, fun z => ?_, fun J => ?_⟩
  · obtain ⟨r, rfl⟩ := rowEquiv.surjective y
    have hcell : ∀ k : Fin 4, (C.cellsOfVals (C.rowVals v rnd) (cellBits (rowEquiv r, k)) : F)
        = (C.srcOf r k).val (C.rowVals v rnd) := fun k =>
      congrArg (fun s => Src.val (C.rowVals v rnd) s) (C.cellSrc_rowCell r k)
    rw [hcell, hcell, hcell, hcell]
    by_cases hr : C.isRandom r
    · obtain ⟨hx, hy, hc⟩ := C.hRandom r hr
      show gate ((C.x r).val (C.rowVals v rnd)) ((C.y r).val (C.rowVals v rnd))
        ((C.c r).val (C.rowVals v rnd)) ((Src.row r).val (C.rowVals v rnd)) = 0
      rw [hx, hy, hc]
      show gate (C.rowVals v rnd r) 1 0 (C.rowVals v rnd r) = 0
      rw [gate_eq]
      unfold chiOf
      rw [mul_zero, add_zero, add_zero]
      exact CharTwo.add_self_eq_zero _
    · have h0 := val_rowVals C v rnd _ (srcs_not_random C hr _ (Or.inl rfl))
      have h1 := val_rowVals C v rnd _ (srcs_not_random C hr _ (Or.inr (Or.inl rfl)))
      have h2 := val_rowVals C v rnd _ (srcs_not_random C hr _ (Or.inr (Or.inr rfl)))
      have h3 : (Src.row r).val (C.rowVals v rnd) = bitF (v r) := by
        show (if C.isRandom r then rnd r else bitF (v r)) = _
        rw [if_neg hr]
      show gate ((C.x r).val (C.rowVals v rnd)) ((C.y r).val (C.rowVals v rnd))
        ((C.c r).val (C.rowVals v rnd)) ((Src.row r).val (C.rowVals v rnd)) = 0
      rw [h0, h1, h2, h3]
      exact (gate_bitF _ _ _ _).mpr (hv r)
  · simp only [ChiCircuit.cellsOfVals, hw z]
  · rw [hc, sum_regionWeight _ (coordWeight_one x Y)]
    unfold ChiCircuit.pubWord
    refine sum_congr rfl fun j _ => ?_
    rw [regionWeight_coordWeight]
    simp only [ChiCircuit.cellsOfVals, ChiCircuit.cellSrc_pubCell, ChiCircuit.pubBit]
    rw [val_rowVals C v rnd _ (C.pubSrc_not_random J j (hpub J j))]

/-- **The honest cells satisfy the relation, the random rows' `X` and `V` cells holding any values.**
On an instance whose wiring keeps what the circuit's cells carry and whose bit weights are
`coordinate_weight`'s, the cells of the assignment of a secret, with the `X` and `V` cells of each
random row `r` set to `rnd r` (`cellsRandomized`, the Statement's `randomizeCells`), satisfy the
relation for the eight words of the statement it proves. -/
theorem honest_relation_random (M : MembershipCircuit) (I : Instance F) {x Y : F}
    (hc : I.c = coordWeight x Y) (hw : WiringKeeps I.wiring M.C) (s : Secret)
    (rnd : Fin (2 ^ 22) → F) :
    I.Relation (statementWords x Y s.statement.y s.statement.root)
      (M.C.cellsRandomized (M.assign s) rnd) := by
  have hs : (fun J => M.C.pubWord x Y (M.assign s) J) =
      statementWords x Y s.statement.y s.statement.root := by
    funext J
    fin_cases J
    · exact pubWord_eq_halves M x Y s 0
    · exact pubWord_eq_halves M x Y s 1
    · exact pubWord_eq_halves M x Y s 2
    · exact pubWord_eq_halves M x Y s 3
    · exact M.C.pubWord_four x Y _ M.word4_one M.word4
    · exact M.C.pubWord_zero x Y _ 5 M.word5
    · exact M.C.pubWord_zero x Y _ 6 M.word6
    · exact M.C.pubWord_zero x Y _ 7 M.word7
  rw [← hs, cellsRandomized_eq]
  exact relation_vals I M.C hc hw M.pubRows (M.assign s) (M.satisfies s) rnd

end Completeness
