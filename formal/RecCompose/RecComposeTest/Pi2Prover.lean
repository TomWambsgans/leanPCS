-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The parsing follows `formal/UniComplete`'s runner
-- (`UniCompleteTest/Runner.lean`).
import RecCompose.Pi2Prover
import RecCircuit.Check
import RecStatement.Data

/-!
# The differential test of π2's honest prover

`PI2_PROVER=<vectors> lake env lean ../RecCompose/RecComposeTest/Pi2Prover.lean` (from `formal/EndToEnd`), on the
vectors of `crates/leanvm/rec/tests/lean_pi2_prover.rs` (`PI2_PROVER_OUT=... cargo test --release -p leanvm_rec --test
lean_pi2_prover -- --ignored --nocapture`): the circuit compiler's example padded to `2^9`, `2^10` positions, through
`pi2::adapt`, and a variant of the first whose element is read narrow and with one hashed claim (a frame word). For
each vector the runner reads the interface's circuit as `RecCircuit.Circuit` (its hashed claims and narrow elements
from the reads; its PIOP form `toPiop`; its view `viewOf4`, π2v4's `pi2::adapt` transcribed: the frame reads first,
the public scalars after the hashes' words), the reads, the public values, the witness and π2's IV, computes the
setup's stack, tree and out-of-domain answer (`Pi2Circuit.setupStack`, `setupTreeWith`, `setupOod`), the circuit's
digest and π2's IV v3 (`RecStatement.iv` at π1's IV `0x11…11`), and runs the Lean prover (`pi2ProveStreamWith` from
the seed `keccak(NAME ‖ IV ‖ input ‖ frame words)`, Keccak-256 over Keccak-f[1600], interpreted, the
ports' `Φ` the view's `Spec.of`, `W`'s and `Q`'s out-of-domain points read off that Keccak-256 as `pi2ProverWith`
reads them, `WhirBridge.Pcs.oodPointM H`); it compares **the setup's root, π2's IV, `W`'s and `Q`'s roots** and **the stream
byte for byte** with the Rust prover's (`pi2::prover::prove`). It throws (so `lean` exits with an error) on any
disagreement.

**Result** (2026-11-11, the vectors of main `7e6d353c`'s Rust): 3/3 vectors agree (setup, `W` and `Q` roots, IV and stream; about 10, 23 and 10 minutes interpreted). π2v4: the stacks plain, `2^15` words at these sizes, `Q` sixteen slots, `H = x h` at
slots `0, 4, 8`, `q`'s digits at `1, 2` (and `5, 6`, `9, 10`), `P` at `12`, `q_P` at `13, 14`, `3, 7, 11, 15` zero,
each commitment its root's bytes and its out-of-domain answer in the stream.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash RecCompose RecStatement
open Primitives

namespace RecComposeTest

/-! ## `adapt`'s parts (copied from `RecCompose/ViewDefs.lean`, so that this runner reads no `RecCompose` module) -/

/-- `Coeff::k(x)`: an element of `K`. -/
def kCoeff (k : RecCircuit.K) : RecStatement.Coeff := ⟨K.lane k, 0, 0, 0⟩

/-- `Coeff::ONE`, `Coeff::e(Y)`, `Coeff::e(Y²)`, `Coeff::gamma(1)`, `γ Y`. -/
def oneC : RecStatement.Coeff := ⟨1, 0, 0, 0⟩
def yC : RecStatement.Coeff := ⟨0, 1, 0, 0⟩
def y2C : RecStatement.Coeff := ⟨0, 0, 1, 0⟩
def gC : RecStatement.Coeff := ⟨1, 0, 0, 1⟩
def gyC : RecStatement.Coeff := ⟨0, 1, 0, 1⟩

/-- `Lin::cell(c)`. -/
def cellLin (c : ℕ) : RecStatement.Lin := ⟨[(oneC, c)], none⟩

/-- **`expr(poly)`**: the linear terms `(k, cell)`, the products `k · cell_a · cell_b`. -/
def exprFormula (p : RecCircuit.Poly) : RecStatement.Formula :=
  ⟨⟨p.linear.map fun t ↦ (kCoeff t.2, t.1), none⟩,
    p.quadratic.map fun t ↦ (kCoeff t.2.2, cellLin t.1, cellLin t.2.1)⟩

/-- **`port_formula(limbs)`**: `1, Y, Y²` on three limbs, `1, Y, γ, γY` on four (other lengths, which the Rust
refuses, as `RecCircuit.portWeights` takes them: each limb once). -/
def portFormula : List ℕ → RecStatement.Formula
  | [a, b, d] => ⟨⟨[(oneC, a), (yC, b), (y2C, d)], none⟩, []⟩
  | [a, b, d, e] => ⟨⟨[(oneC, a), (yC, b), (gC, d), (gyC, e)], none⟩, []⟩
  | ls => ⟨⟨ls.map fun c ↦ (oneC, c), none⟩, []⟩

/-- A role's pair: its formula and whether it pulls (a port does not); none for a forward. -/
def roleFormula : RecCircuit.Formula → Option (RecStatement.Formula × Bool)
  | .forward => none
  | .expr p => some (exprFormula p, true)
  | .port ls => some (portFormula ls, false)

/-- A block's region's roles. -/
def blockRoles (c : RecCircuit.Circuit) (b : RecCircuit.Block) : List RecCircuit.Formula :=
  (c.regions.getD b.region default).roles.toList

/-- **The slots**: every non-forward role of every block, in block order, roles in order, with its pair's formula and
pull flag. -/
def slots (c : RecCircuit.Circuit) : List (RecCircuit.Block × ℕ × RecStatement.Formula × Bool) :=
  c.blocks.toList.flatMap fun b ↦
    (List.range (blockRoles c b).length).filterMap fun k ↦
      (roleFormula ((blockRoles c b).getD k .forward)).map fun fp ↦ (b, k, fp)

/-- A formula added unless already there (the Rust's `id`). -/
def addFormula (fs : List RecStatement.Formula) (f : RecStatement.Formula) : List RecStatement.Formula :=
  if f ∈ fs then fs else fs ++ [f]

/-- **The formulas**, deduplicated in first appearance. -/
def formulasOf (c : RecCircuit.Circuit) : List RecStatement.Formula :=
  (slots c).foldl (fun fs s ↦ addFormula fs s.2.2.1) []

/-- **The pairs**: one per slot, its formula's index the first appearance's. -/
def pairsOf (c : RecCircuit.Circuit) : List RecStatement.Pair :=
  (slots c).map fun s ↦ ⟨s.1.row, s.1.logRows, s.2.1, (formulasOf c).idxOf s.2.2.1, s.2.2.2⟩

/-- `public_counts`' step on a port's source. -/
def sourceCounts (acc : ℕ × ℕ) : RecCircuit.Source → ℕ × ℕ
  | .root i => (max acc.1 (i + 1), acc.2)
  | .element i => (acc.1, max acc.2 (i + 1))
  | _ => acc

/-- `public_counts`' step on a call word. -/
def wordCounts (acc : ℕ × ℕ) : RecCircuit.CallWord → ℕ × ℕ
  | .root i => (max acc.1 (i + 1), acc.2)
  | .element i => (acc.1, max acc.2 (i + 1))
  | .pair i _ => (acc.1, max acc.2 (i + 1))
  | .const _ => acc

/-- **`public_counts`**: one past the largest root and element the ports and the calls name. -/
def publicCounts (c : RecCircuit.Circuit) : ℕ × ℕ :=
  c.calls.flatten.foldl wordCounts (c.ports.toList.foldl (fun a p ↦ sourceCounts a p.source) (0, 0))

/-- The public terms' holes: port `j`'s position (which `σ` sends to the tag `N + j`). -/
def holesOf (c : RecCircuit.Circuit) : List ℕ :=
  (List.range c.ports.size).map fun j ↦ (c.ports.getD j default).position


def hexDigit (c : Char) : ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else 0

def hexNat (s : String) : ℕ := s.toList.foldl (fun acc c ↦ 16 * acc + hexDigit c) 0

def hexBytes (s : String) : List UInt8 :=
  let cs := s.toList.toArray
  (List.range (cs.size / 2)).map fun i ↦ UInt8.ofNat (16 * hexDigit (cs.getD (2 * i) '0') + hexDigit (cs.getD (2 * i + 1) '0'))

def hexOf (b : List UInt8) : String :=
  String.join (b.map fun x ↦
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    if s.length = 1 then "0" ++ s else s)

def kOf (s : String) : K := K.ofLane (UInt64.ofNat (hexNat s))

def rest (l : String) : List String := ((l.splitOn " ").drop 1).filter (· ≠ "")

def splitOn (c : String) (s : String) : List String := (s.splitOn c).filter (· ≠ "")

/-- A role: `F`, `E<lin>;<quad>` (`cell:coeff`, `a:b:coeff`), `P<limbs>`. -/
def roleOf (s : String) : RecCircuit.Formula :=
  match s.toList with
  | 'F' :: _ => .forward
  | 'P' :: r => .port ((splitOn "," (String.ofList r)).map String.toNat!)
  | 'E' :: r =>
    let parts := (String.ofList r).splitOn ";"
    let lin := (splitOn "," (parts.getD 0 "")).map fun t ↦
      let xs := t.splitOn ":"
      ((xs.getD 0 "0").toNat!, kOf (xs.getD 1 "0"))
    let quad := (splitOn "," (parts.getD 1 "")).map fun t ↦
      let xs := t.splitOn ":"
      ((xs.getD 0 "0").toNat!, (xs.getD 1 "0").toNat!, kOf (xs.getD 2 "0"))
    .expr ⟨lin, quad⟩
  | _ => .forward

def sourceOf (s : String) : RecCircuit.Source :=
  match s.toList with
  | 'S' :: _ => .statement
  | 'R' :: r => .root (String.ofList r).toNat!
  | 'L' :: r => .element (String.ofList r).toNat!
  | 'Z' :: _ => .zero
  | _ => .pad

def readOf (s : String) : Read :=
  match s.toList with
  | 'I' :: r => .integer (String.ofList r).toNat!
  | 'R' :: _ => .root
  | 'N' :: _ => .narrow
  | 'F' :: r => .frame (String.ofList r).toNat!
  | _ => .scalar

def valueOf (s : String) : PublicValue :=
  match s.toList with
  | 'I' :: r => .integer (hexNat (String.ofList r))
  | 'R' :: r => .root (hexBytes (String.ofList r))
  | 'W' :: r => .word (hexBytes (String.ofList r))
  | 'S' :: r =>
    let xs := (String.ofList r).splitOn ":"
    .scalar (UniStatement.eNew (UInt64.ofNat (hexNat (xs.getD 0 "0"))) (UInt64.ofNat (hexNat (xs.getD 1 "0")))
      (UInt64.ofNat (hexNat (xs.getD 2 "0"))))
  | _ => .scalar 0

structure Vec where
  name : String
  lines : List String

def vectors (ls : List String) : List Vec := Id.run do
  let mut out : Array Vec := #[]
  let mut cur : Option Vec := none
  for l in ls do
    if l.startsWith "VECTOR " then
      cur := some ⟨l, []⟩
    else if l == "END" then
      if let some v := cur then out := out.push ⟨v.name, v.lines.reverse⟩
      cur := none
    else
      cur := cur.map fun v ↦ ⟨v.name, l :: v.lines⟩
  return out.toList

def Vec.tagged (v : Vec) (tag : String) : List String :=
  match v.lines.find? (·.startsWith (tag ++ " ")) with
  | some l => rest l
  | none => []

def Vec.all (v : Vec) (tag : String) : List (List String) :=
  (v.lines.filter (·.startsWith (tag ++ " "))).map rest

/-- π2v4's public term of a port (`pi2::adapt`): the statement's words, a root's halves, a hashed claim's frame word's
four words (`hash_at`), an element; the roots' scalars after the hashes' words, the elements' after the roots'. -/
def termOf4 (hashes roots : ℕ) : RecCircuit.Source → List (RecStatement.Coeff × ℕ)
  | .statement => [(oneC, 0), (yC, 1), (gC, 2), (gyC, 3)]
  | .root i => [(oneC, 4 + 4 * hashes + 2 * i + 1), (gC, 4 + 4 * hashes + 2 * i)]
  | .claimHash i => [(oneC, 4 + 4 * i), (yC, 4 + 4 * i + 1), (gC, 4 + 4 * i + 2), (gyC, 4 + 4 * i + 3)]
  | .element i => [(oneC, 4 + 4 * hashes + 2 * roots + i)]
  | _ => []

/-- **π2v4's `adapt`** (test-local): the frame reads of the hashed claims, the roots, the elements (narrow ones read
narrow), and the public terms by `termOf4`. -/
def viewOf4 (c : RecCircuit.Circuit) : RecStatement.Circuit :=
  let (roots, elements) := publicCounts c
  ⟨c.logN, c.logWidth, formulasOf c, pairsOf c,
    c.hashed.map Read.frame ++ List.replicate roots .root ++
      (List.range elements).map fun e ↦ if e ∈ c.narrow then .narrow else .scalar,
    (List.range c.ports.size).map fun j ↦
      ⟨2 ^ c.logN + j, ⟨termOf4 c.hashed.length roots (c.ports.getD j default).source, none⟩⟩,
    holesOf c⟩

/-- Keccak-256 over Keccak-f[1600]. -/
def H : List UInt8 → Id Digest := keccak256With (m := Id) fun s ↦ pure (keccakF1600 s)

def run1 (v : Vec) : IO Unit := do
  let shape := v.tagged "SHAPE"
  let logN := (shape.getD 0 "0").toNat!
  let logW := (shape.getD 1 "0").toNat!
  let regions : Array RecCircuit.Region := ((v.all "REGION").map fun rs ↦ ⟨"", (rs.map roleOf).toArray⟩).toArray
  let blocks : Array RecCircuit.Block := ((v.all "BLOCK").map fun bs ↦
    ⟨(bs.getD 0 "0").toNat!, (bs.getD 1 "0").toNat!, (bs.getD 2 "0").toNat!⟩).toArray
  let sigma : Array ℕ := ((v.tagged "SIGMA").map String.toNat!).toArray
  let kappa : Array (ℕ × K) := ((v.all "KAPPA").map fun ks ↦ ((ks.getD 0 "0").toNat!, kOf (ks.getD 1 "0"))).toArray
  let ports : Array RecCircuit.Port := ((v.all "PORT").map fun ps ↦
    ⟨(ps.getD 0 "0").toNat!, sourceOf (ps.getD 1 "D")⟩).toArray
  let reads := (v.tagged "READS").map readOf
  let hashed := reads.filterMap fun r ↦ match r with
    | .frame p => some p
    | _ => none
  let elementReads := reads.filter fun r ↦ r == .scalar || r == .narrow
  let narrow := (List.range elementReads.length).filter fun e ↦ elementReads.getD e .scalar == .narrow
  let c : RecCircuit.Circuit := ⟨logN, logW, regions, blocks, sigma, kappa, ports, [], hashed, narrow⟩
  let G := c.toPiop
  let values := (v.tagged "VALUES").map valueOf
  let iv := hexBytes ((v.tagged "IV").getD 0 "")
  let input := hexBytes ((v.tagged "INPUT").getD 0 "")
  let wit : Array K := ((v.tagged "WITNESS").map kOf).toArray
  let w : ℕ → K := fun i ↦ wit.getD i 0
  let view := viewOf4 c
  let pc : Pi2Circuit := ⟨view, c.sigmaAt, c.kappaAt⟩
  let setupStack := pc.setupStack
  let start ← IO.monoMsNow
  let setupTree : LeanVM.Prover.Tree := Id.run (pc.setupTreeWith (m := Id) fun s ↦ pure (keccakF1600 s))
  let setupRoot := digestBytes setupTree.root
  IO.println s!"{v.name}: setup root {hexOf setupRoot} ({(← IO.monoMsNow) - start} ms)"
  if setupRoot != hexBytes ((v.tagged "SETUPROOT").getD 0 "") then
    throw (IO.userError s!"{v.name}: the setup's root differs")
  if view.reads != reads then
    throw (IO.userError s!"{v.name}: the view's reads differ")
  let digest := Id.run (pc.digestWith (m := Id) fun s ↦ pure (keccakF1600 s))
  let ivL := RecStatement.iv (List.replicate 32 0x11) setupRoot (pc.setupOod setupTree.root) digest logN
  IO.println s!"  IV {hexOf ivL}"
  if ivL != iv then throw (IO.userError s!"{v.name}: π2's IV differs")
  let seed := Id.run (H (RecStatement.name ++ iv ++ input ++ frameWordsOf values))
  let (out, _) := Id.run ((pi2ProveStreamWith H G (Spec.of view).core (WhirBridge.Pcs.oodPointM H) reads setupStack
    input values w).run
    (UniComplete.Wr.start seed))
  IO.println s!"{v.name}: proved ({(← IO.monoMsNow) - start} ms)"
  let wr := digestBytes out.wTree.root
  let qr := digestBytes out.qTree.root
  IO.println s!"  W root {hexOf wr}"
  IO.println s!"  Q root {hexOf qr}"
  if wr != hexBytes ((v.tagged "WROOT").getD 0 "") then throw (IO.userError s!"{v.name}: W's root differs")
  if qr != hexBytes ((v.tagged "QROOT").getD 0 "") then throw (IO.userError s!"{v.name}: Q's root differs")
  let expected := hexBytes ((v.tagged "STREAM").getD 0 "")
  if out.stream.toList != expected then
    throw (IO.userError s!"{v.name}: the stream differs ({out.stream.size} bytes, the Rust's {expected.length})")
  IO.println s!"{v.name}: the stream the same byte for byte ({expected.length} bytes)"

def main : IO Unit := do
  let path ← IO.getEnv "PI2_PROVER"
  let text ← IO.FS.readFile (path.getD "pi2_prover.txt")
  let vs := vectors (text.splitOn "\n")
  for v in vs do
    run1 v
  IO.println s!"{vs.length}/{vs.length} vectors agree"

end RecComposeTest

#eval RecComposeTest.main
