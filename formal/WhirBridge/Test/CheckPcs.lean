/-
Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Adapted from `Test/CheckLarge.lean` (this
repository): the same parsing, on PCS claims (version 1).

Runs the Lean `verify_claim` (`WhirBridge.Pcs.pcsVerifyWithHash`, over leanerVM mumbai's Keccak-256 and
Keccak-f[1600], the out-of-domain point `oodPoint`) on openings made by the Rust prover
(`crates/pcs_claim/examples/lean_vector.rs`): for each claim, the Lean `claimBytes` is compared with the
Rust's `PCS_claim` and its Keccak-256 with the dependency's payload, the Lean `oodPoint` with the Rust's
`ood_point`, the honest proof accepted, and a wrong value, a wrong out-of-domain answer, a wrong root, a
changed stream scalar, a changed leaf word and another out-of-domain point rejected.

  cargo run --release -p pcs_claim --example lean_vector > target/pcs_claim_vector.txt
  lake env lean --run Test/CheckPcs.lean ../../target/pcs_claim_vector.txt
-/
import WhirBridge.Pcs

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash WhirBridge WhirBridge.Pcs

instance : Inhabited Opening := ⟨⟨[], []⟩⟩

/-- The numbers after a line's tag. -/
def nums (l : String) : List ℕ := ((l.splitOn " ").drop 1).filterMap String.toNat?

/-- Scalars from their limbs, three at a time. -/
def scalars : List ℕ → List E
  | a :: b :: c :: rest =>
    E.ofLimbs (K.ofLane a.toUInt64) (K.ofLane b.toUInt64) (K.ofLane c.toUInt64) :: scalars rest
  | _ => []

/-- Digests from their words, four at a time. -/
def digests : List ℕ → List Digest
  | a :: b :: c :: d :: rest =>
    (Vector.ofFn fun i : Fin 4 ↦ ([a, b, c, d].getD i 0).toUInt64) :: digests rest
  | _ => []

def bytesNat (b : Bytes) : List ℕ := b.map (·.toNat)

/-- `verify_claim` in Lean, with the deployed Keccak and the out-of-domain derivation `zOf`. -/
def verifyId {n : ℕ} (zOf : Digest → Vector E n) (x : Claim1 n) (π : Proof) : Bool :=
  Id.run (pcsVerifyWithHash (m := Id) keccak256 keccakF1600 zOf x π)

/-- The vectors: the lines between `vector <name>` and `end`. -/
def vectors : List String → List (String × List String)
  | [] => []
  | l :: rest =>
    if l.startsWith "vector " then
      let body := rest.takeWhile (· != "end")
      ((l.drop 7).toString, body) :: vectors (rest.drop (body.length + 1))
    else vectors rest
termination_by ls => ls.length
decreasing_by all_goals (simp_wf; try omega)

/-- Check one claim and its opening; `true` when every check passes. -/
def checkVector (name : String) (lines : List String) : IO Bool := do
  let tagged := fun (t : String) ↦ (lines.filter fun l ↦ l.startsWith (t ++ " ")).map nums
  let n := ((tagged "n").headD []).headD 0
  let root := (digests ((tagged "root").headD [])).headD default
  let ood := (scalars ((tagged "ood").headD [])).headD 0
  let point := scalars ((tagged "point").headD [])
  let value := (scalars ((tagged "value").headD [])).headD 0
  let oodRust := scalars ((tagged "oodpoint").headD [])
  let stream := scalars ((tagged "stream").headD [])
  let openings := (tagged "open").map fun o ↦
    let k := o.getD 0 0
    (⟨((o.drop 1).take k).map fun w ↦ K.ofLane w.toUInt64, digests (o.drop (1 + k))⟩ : Opening)
  let π : Proof := ⟨stream, openings⟩
  if hp : point.length = n then
    let x : Claim1 n := ⟨root, ood, point, value, hp⟩
    IO.println s!"{name}: n = {n}; {stream.length} scalars, {openings.length} paths"
    let bytesOk := bytesNat (claimBytes x) == (tagged "claimbytes").headD []
    IO.println s!"  PCS_claim's bytes recomputed ({(claimBytes x).length} bytes): {bytesOk}"
    let payloadOk := bytesNat (digestBytes (keccak256 (claimBytes x))) == (tagged "payload").headD []
    IO.println s!"  payload keccak256(PCS_claim) recomputed: {payloadOk}"
    let oodOk := (oodPoint n root).toList == oodRust
    IO.println s!"  out-of-domain point recomputed: {oodOk}"
    let honest := verifyId (oodPoint n) x π
    IO.println s!"  honest proof accepted: {honest}"
    let rejectValue := !verifyId (oodPoint n) { x with value := x.value + 1 } π
    IO.println s!"  wrong value rejected: {rejectValue}"
    let rejectOod := !verifyId (oodPoint n) { x with ood := x.ood + 1 } π
    IO.println s!"  wrong out-of-domain answer rejected: {rejectOod}"
    let rejectRoot := !verifyId (oodPoint n) { x with root := root.set 0 (root[0] ^^^ 1) } π
    IO.println s!"  wrong root rejected: {rejectRoot}"
    let rejectStream := !verifyId (oodPoint n) x ⟨stream.set 5 (stream[5]! + 1), openings⟩
    IO.println s!"  tampered stream rejected: {rejectStream}"
    let rejectLeaf := !verifyId (oodPoint n) x ⟨stream, openings.set 0
      { openings[0]! with leaf := openings[0]!.leaf.set 63 (openings[0]!.leaf[63]! + 1) }⟩
    IO.println s!"  tampered leaf rejected: {rejectLeaf}"
    -- the weight reads the out-of-domain point: another point is rejected
    let rejectZ := !verifyId (fun _ ↦ Vector.replicate n 0) x π
    IO.println s!"  another out-of-domain point rejected: {rejectZ}"
    return bytesOk && payloadOk && oodOk && honest && rejectValue && rejectOod && rejectRoot &&
      rejectStream && rejectLeaf && rejectZ
  else
    IO.println s!"{name}: a point of {point.length} coordinates, not {n}"
    return false

def main (args : List String) : IO UInt32 := do
  let text ← IO.FS.readFile (args.getD 0 "pcs_claim_vector.txt")
  let vs := vectors (text.splitOn "\n")
  let mut ok := !vs.isEmpty
  for (name, body) in vs do
    ok := (← checkVector name body) && ok
  IO.println s!"{vs.length} PCS openings; all checks: {ok}"
  return if ok then 0 else 1
