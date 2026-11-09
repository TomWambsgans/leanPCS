-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows `crates/leanvm/univariate/src/prover/trace.rs`
-- (`Trace::place`) and `tests/prove_tiny.rs` (the padding rows' counters `1`); the stack is `formal/KeccakVm`'s
-- (`KeccakIsa.layout`, after leanerVM `mumbai` f0393df4's `LeanIsa.layout`, MIT OR Apache-2.0).
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/Witness.lean`.
import UniKeccakComplete.K.Prover

/-!
# The placed trace of a witness, and the honest prover

**`honestTrace D input rows q`**: the trace the honest prover proves, read off the Keccak VM's stack `q` (the
relation's witness, `D.Stack rows`) through the instance's own reading (`M3Instance.column` of `keccakIsaInstance`):

* each opcode table's column `i` (`⟨t + 3, i⟩`; every `SHA3` column, its 50 lanes included, is committed) at the
  Keccak VM's row `x`, placed at the univariate PIOP's row `rowPosition count h x` (the executed rows at the fixed
  cosets of the count's set bits, `activePositions`), the shape's height `h`;
* the padding rows' counters set to `1` (the PIOP requires `z_T Π c = 1` on every row);
* the padding rows' `SHA3` lanes set to their blocks' port words (`in_16` plus `END_BIT`): the copies `Q_W` checks
  hold on every row, as `trace.rs` pads them (the Keccak VM's padding rows are zero, its padding blocks any
  Keccak-f block, so a zero lane would not be its block's port word);
* the memory's four columns (`memCol`), the bytecode's final counts (`bfcntCol`), at their heights;
* `q_flock` (`flockCol`): the Keccak VM's block `x` (cells `w + 2^11 x`) at the PIOP's block
  `rowPosition count₅ h₅ x`, as `UniKeccak.kvColumn` reads it back;
* the bytecode's 16 tuple slots from the program (`tupleSlotK`, the setup's), the public input's bytes.

**The honest prover** (`uniProverWith`): `proveWith` on that trace, Flock's prover a parameter, at the main line
(`keccakMain`, point claims), `nonceFuel` nonces a proof of work, over `H` and `F`.
-/

namespace UniKeccakComplete

open UniComplete

open UniStatement UniKeccak LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open KeccakVm.KeccakIsa (Col kappa width memCol bfcntCol flockCol)

/-- Cell `x` of the Keccak VM's column `c` of the stack `q` (`0` past its height). -/
def kvCell (D : KDeployment) (rows : List ℕ) (q : D.Stack rows) (c : Col) (x : ℕ) : K :=
  if h : x < 2 ^ kappa D.prog (D.sizes rows) c then
    ((KeccakVm.keccakIsaInstance D.prog (D.sizes rows)).column q c).values.get ⟨x, h⟩
  else 0

/-- The Keccak VM's column `i` of opcode table `t` (`0` past its width). -/
def kvTableCell (D : KDeployment) (rows : List ℕ) (q : D.Stack rows) (t : Fin 6) (i x : ℕ) : K :=
  if h : i < width ⟨t.val + 3, by omega⟩ then kvCell D rows q ⟨⟨t.val + 3, by omega⟩, ⟨i, h⟩⟩ x else 0

/-- Scatter `2^r` values to their positions: value `x` at `pos x`. -/
def scatter (r : ℕ) (pos : ℕ → ℕ) (value : ℕ → K) : Array K :=
  (List.range (2 ^ r)).foldl (fun a x ↦ a.set! (pos x) (value x)) (Array.replicate (2 ^ r) 0)

/-- **The placed trace of a witness**. -/
def honestTrace (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : Trace :=
  let shape := D.shape
  let hB := shape.heights.getD 5 0
  let countB := rows.getD 5 0
  let qflock : Array K := (List.range (2 ^ (hB + 11))).foldl (fun a word ↦
      a.set! (word % 2048 + 2048 * rowPosition countB hB (word / 2048)) (kvCell D rows q flockCol word))
    (Array.replicate (2 ^ (hB + 11)) 0)
  let table (t : Fin 6) : List (Array K) :=
    let r := shape.heights.getD t.val 0
    let count := rows.getD t.val 0
    let counters := (tablesKeccak.getD t.val default).countColumns
    (List.range (tablesKeccak.getD t.val default).width).map fun i ↦
      let placed := scatter r (rowPosition count r) (kvTableCell D rows q t i)
      let name := (tablesKeccak.getD t.val default).columns.getD i ""
      if i ∈ counters then
        Array.ofFn (n := 2 ^ r) fun p ↦ if isActive p.val count r then placed.getD p.val 0 else 1
      else match (if t.val = 5 then keccakSlot name else none) with
        | some slot => Array.ofFn (n := 2 ^ r) fun p ↦ if isActive p.val count r then placed.getD p.val 0
            else qflock.getD (slot + 2048 * p.val) 0 + K.ofLane (keccakSlotOffset name)
        | none => placed
  let lb := shape.logBytecode
  ⟨shape, rows, (List.finRange 6).map table,
    (List.range 4).map fun k ↦ Array.ofFn (n := 2 ^ shape.logMemory) fun x ↦
      if h : k < 4 then kvCell D rows q (memCol ⟨k, h⟩) x.val else 0,
    Array.ofFn (n := 2 ^ lb) fun x ↦ kvCell D rows q bfcntCol x.val,
    qflock,
    (List.range 16).map fun s ↦ Array.ofFn (n := 2 ^ lb) fun i ↦
      if h : i.val < 2 ^ D.prog.logSize then tupleSlotK D.prog ⟨i.val, h⟩ s else 0,
    input.toList⟩

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **The honest prover** over `H`, `F`, Flock's prover given: `proveWith` on the placed trace of the witness, at
the main line, `nonceFuel` nonces a proof of work, the deployment's `A0`, `B0` constants in the IV. -/
def uniProverWith (flock : FlockProver m) (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) : m (Option KeccakProof) :=
  proveWith H F PcsQuotient.nonceFuel flock D.programIv (honestTrace D input rows q)

end With

end UniKeccakComplete
