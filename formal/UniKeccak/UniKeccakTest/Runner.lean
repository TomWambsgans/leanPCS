-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. The vector parser is
-- `formal/UniStatement/UniStatementTest/Runner.lean`'s, repeated (a test file is not a module).
import UniKeccak

/-!
# The Keccak VM's differential runner

`lake env lean ../UniKeccak/UniKeccakTest/Runner.lean` (from `formal/EndToEnd`), with the vectors of
`crates/leanvm/univariate/tests/lean_keccak_vectors.rs` at `$KECCAK_VECTORS`:

* **Terminal vectors** (`TERMINAL`): `UniKeccak.structuredTerminal` on the Rust's random inputs at every skip
  `k ≤ 6`, against the Rust's `structured_terminal` and walked terminal (which the writer asserts equal), and Lean's
  own walk of the block (`walkedTerminalK`) against the Rust's walked terminal.
* **Verifier vectors**: the Lean verifier (`UniKeccak.runK`, compiled evaluation, not the kernel) on every vector's
  calldata, compared with the Rust verifier's on every value it states: the verdict (stream error or not, and which),
  every challenge drawn, every value it requires to be zero, the accept bit, the number of relations, each stack's
  variables, every opening handed to `PCS_OPEN` (point claims with their points and values, or weighted claims with
  their points, terms in order, values) and no matrices; the setup (the five Keccak layout words, the Keccak
  contract's IV from the program's IV and the setup roots), the row counts the stream announces, the run's layouts
  against the shape's (`layoutsOfK`); on the real proofs, every `PCS_OPEN` input the contract calls with, word for
  word (`pcsCallsK`).
* **Self-tests**: every Keccak run's shape is valid, the Keccak layouts' `C1` holds `q_flock` at `h + 11` variables
  and the 50 lane columns, `SOURCE` is a permutation of the lanes.

It prints one line per test and per vector and a summary, and throws (so `lean` exits with an error) on any failure,
disagreement or unreadable vector.
-/

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement UniKeccak

namespace UniKeccakTest

/-- A parser of a line's tokens. -/
abbrev Parse := StateT (List String) (Except String)

def token : Parse String := do
  match ← get with
  | [] => throw "the line ended early"
  | t :: ts => set ts; pure t

def expect (s : String) : Parse Unit := do
  let t ← token
  if t ≠ s then throw s!"expected {s}, got {t}"

def hexDigit (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexNat (s : String) : Except String ℕ :=
  s.toList.foldlM (fun acc c ↦ match hexDigit c with
    | some d => pure (16 * acc + d)
    | none => throw s!"not hex: {s}") 0

def nat : Parse ℕ := do
  let t ← token
  match t.toNat? with
  | some n => pure n
  | none => throw s!"not a number: {t}"

def eOf (s : String) : Except String E :=
  match s.splitOn ":" with
  | [a, b, c] =>
    let limb (s : String) : Except String UInt64 := UInt64.ofNat <$> hexNat s
    return eNew (← limb a) (← limb b) (← limb c)
  | _ => throw s!"not an element of E: {s}"

def eElem : Parse E := do eOf (← token)

def many {α : Type} (p : Parse α) : Parse (List α) := do
  let n ← nat
  (List.range n).mapM fun _ ↦ p

/-- Bytes from hex. -/
def hexBytes (s : String) : Except String (Array UInt8) := do
  let cs := s.toList.toArray
  if cs.size % 2 ≠ 0 then throw "odd hex"
  let mut out : Array UInt8 := Array.mkEmpty (cs.size / 2)
  for i in [0:cs.size / 2] do
    match hexDigit (cs.getD (2 * i) '0'), hexDigit (cs.getD (2 * i + 1) '0') with
    | some a, some b => out := out.push (UInt8.ofNat (16 * a + b))
    | _, _ => throw "not hex"
  return out

/-- Lowercase hex of bytes. -/
def hexOf (b : Array UInt8) : String :=
  String.join (b.toList.map fun x ↦
    let d (n : ℕ) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
    String.ofList [d (x.toNat / 16), d (x.toNat % 16)])

def eHex (x : E) : String :=
  s!"{String.ofList (Nat.toDigits 16 (x.limb 0).lane.toNat)}:{String.ofList (Nat.toDigits 16 (x.limb 1).lane.toNat)}:{String.ofList (Nat.toDigits 16 (x.limb 2).lane.toNat)}"

/-- A combined claim as the Rust writes it. -/
structure RustCombined where
  points : List (List E)
  terms : List (ℕ × ℕ × ℕ × E)
  value : E
  relations : ℕ

def combinedP : Parse RustCombined := do
  expect "P"
  let points ← many (many eElem)
  expect "T"
  let terms ← many do
    let id ← hexNat (← token)
    let p ← nat
    let twist ← nat
    let c ← eElem
    pure (id, p, twist, c)
  expect "V"
  let value ← eElem
  expect "R"
  let relations ← nat
  pure ⟨points, terms, value, relations⟩

inductive RustOpening where
  | point (commitment : String) (pt : List E) (value : E) (bitSlice : Option RustCombined)
  | weighted (commitment : String) (claim : RustCombined)

def openingP : Parse RustOpening := do
  expect "OPENING"
  let c ← token
  match ← token with
  | "POINT" =>
    let pt ← many eElem
    expect "VALUE"
    let v ← eElem
    expect "BITSLICE"
    let bs ← match ← token with
      | "0" => pure none
      | "1" => some <$> combinedP
      | t => throw s!"BITSLICE {t}"
    pure (.point c pt v bs)
  | "WEIGHTED" => .weighted c <$> combinedP
  | t => throw s!"opening kind {t}"

/-- A vector: its configuration, its calldata, and the Rust's outcome. -/
structure Vector' where
  id : String
  shape : String
  flock : String
  claims : String
  kind : String
  iv : Array UInt8
  publicInput : Array UInt8
  stream : Array UInt8
  error : Option String
  challenges : List E
  zeros : List E
  nonzeros : List E
  accept : Bool
  relations : Option ℕ
  stackVars : List (String × ℕ)
  openings : List RustOpening
  matrices : Bool
  shapeLine : Option (ℕ × ℕ × List ℕ)
  programIv : Option (Array UInt8)
  setupRoots : List (Array UInt8)
  contractIv : Option (Array UInt8)
  layoutWords : List (Array UInt8)
  counts : Option (List ℕ)
  calls : List (Array UInt8)

/-- The tokens of a line. -/
def tokens (line : String) : List String := (line.splitOn " ").filter (· ≠ "")

/-- Parse one vector from its lines (`VECTOR` to `END`). -/
def parseVector (lines : List String) : Except String Vector' := do
  let byKey (k : String) : Option (List String) :=
    (lines.map tokens).find? (fun ts ↦ ts.head? == some k) |>.map (·.drop 1)
  let req (k : String) : Except String (List String) :=
    match byKey k with
    | some ts => pure ts
    | none => throw s!"no {k} line"
  let header ← req "VECTOR"
  let (id, shape, flock, claims, kind) ← match header with
    | [a, b, c, d, e] => pure (a, b, c, d, e)
    | _ => throw "bad VECTOR line"
  let iv ← hexBytes ((← req "IV").headD "")
  let publicInput ← hexBytes ((← req "PUBLIC").headD "")
  let stream ← hexBytes (((← req "STREAM").drop 1).headD "")
  let error := match byKey "RESULT" with
    | some ["ERR", e] => some e
    | _ => none
  let (challenges, _) ← (many eElem).run (← req "CHALLENGES")
  let (zeros, _) ← (many eElem).run (← req "ZEROS")
  let (nonzeros, _) ← (many eElem).run (← req "NONZEROS")
  let accept := byKey "ACCEPT" == some ["1"]
  let relations := (byKey "RELATIONS").bind (·.head?) |>.bind String.toNat?
  let stackVars ← match byKey "STACKVARS" with
    | some ts => (do
        let n ← nat
        (List.range n).mapM fun _ ↦ do
          let c ← token
          let v ← nat
          pure (c, v) : Parse _).run' ts
    | none => pure []
  let openings ← (lines.filter (·.startsWith "OPENING ")).mapM fun l ↦ openingP.run' (tokens l)
  let matrices := match byKey "MATRICES" with
    | some ("1" :: _) => true
    | _ => false
  let shapeLine := match byKey "SHAPE" with
    | some (lm :: lb :: rows) =>
      match lm.toNat?, lb.toNat?, rows.mapM String.toNat? with
      | some lm, some lb, some rows => some (lm, lb, rows)
      | _, _, _ => none
    | _ => none
  let programIv ← (byKey "PROGRAMIV").mapM fun ts ↦ hexBytes (ts.headD "")
  let setupRoots ← ((byKey "SETUPROOTS").getD []).mapM hexBytes
  let contractIv ← (byKey "CONTRACTIV").mapM fun ts ↦ hexBytes (ts.headD "")
  let layoutWords ← match byKey "LAYOUTWORDS" with
    | some (_ :: ws) => ws.mapM hexBytes
    | _ => pure []
  let counts := (byKey "COUNTS").map fun ts ↦ (ts.drop 1).filterMap String.toNat?
  let calls ← ((lines.map tokens).filter (·.head? == some "PCSOPEN")).mapM fun ts ↦ hexBytes ((ts.drop 1).headD "")
  pure ⟨id, shape, flock, claims, kind, iv, publicInput, stream, error, challenges, zeros, nonzeros,
    accept, relations, stackVars, openings, matrices, shapeLine, programIv, setupRoots, contractIv, layoutWords,
    counts, calls⟩

/-- The configuration a vector names. -/
def variantNamed : String → Option KeccakVariant
  | "keccak" => some keccakMain
  | "keccak_rec3" => some keccakRec3
  | _ => none

def modeNamed : String → Option ClaimsMode
  | "point" => some .point
  | "weighted" => some .weighted
  | _ => none

/-- Lean's combined claim against the Rust's: the same points, terms (in order), value, relations. -/
def sameCombined (lean : Combined) (rust : RustCombined) : Bool :=
  lean.points == rust.points &&
    lean.terms.map (fun (c, p, k, v) ↦ (c.id, p, k, v)) == rust.terms &&
    lean.value == rust.value && lean.relations == rust.relations

def sameOpening (lean : Commitment × Opening) (rust : RustOpening) : Bool :=
  match lean.2, rust with
  | .point pt v bs, .point c pt' v' bs' =>
    lean.1.name == c && pt == pt' && v == v' &&
      (match bs, bs' with
        | none, none => true
        | some a, some b => sameCombined a b
        | _, _ => false)
  | .weighted claim, .weighted c claim' => lean.1.name == c && sameCombined claim claim'
  | _, _ => false

/-- The first disagreement between the Lean run and the Rust's outcome, if any. -/
def compare (v : Vector') : Except String (Option String) := do
  let some (lm, lb, rows) := v.shapeLine | throw "no SHAPE line"
  let shape := shapeWith lm lb rows
  let some variant := variantNamed v.flock | throw s!"unknown flock {v.flock}"
  let some mode := modeNamed v.claims | throw s!"unknown claims {v.claims}"
  if !(shape.heights.length == 6 && shape.validate true) then
    return some s!"the shape is not valid (F5): {repr shape}"
  -- The setup: the Keccak layout words, the setup roots, the Keccak contract's IV.
  let words := layoutWordsK shape
  if words.map List.toArray != v.layoutWords then
    return some s!"layout words: Lean {words.map fun w ↦ hexOf w.toArray}, Rust {v.layoutWords.map hexOf}"
  let roots : SetupRoots ← match v.setupRoots with
    | [f, a, b] => pure ⟨digestOfBytes32 f.toList, digestOfBytes32 a.toList, digestOfBytes32 b.toList⟩
    | _ => throw "no SETUPROOTS line"
  if v.setupRoots.drop 1 != [(digestBytes referenceRoots.a0).toArray, (digestBytes referenceRoots.b0).toArray] then
    return some "the A0, B0 roots are not the reference's"
  match v.programIv, v.contractIv with
  | some p, some c =>
    let iv := contractIvK shape variant p.toList roots
    if iv.toArray != c then return some s!"contract IV: Lean {hexOf iv.toArray}, Rust {hexOf c}"
    if c != v.iv then return some "the vector's IV is not its contract's"
  | _, _ => return some "no PROGRAMIV or CONTRACTIV line"
  -- The row counts the stream announces.
  if let some counts := v.counts then
    if (rowsOf v.stream).take counts.length != counts then
      return some s!"counts: Lean {rowsOf v.stream}, Rust {counts}"
  let o := runK shape v.iv.toList v.publicInput.toList v.stream variant mode
  let leanError := match o.result with
    | .ok _ => none
    | .error e => some e.name
  if leanError != v.error then return some s!"result: Lean {leanError}, Rust {v.error}"
  if o.chan.challenges.toList.length != v.challenges.length then
    return some s!"challenges: Lean {o.chan.challenges.size}, Rust {v.challenges.length}"
  for (i, (a, b)) in (List.range v.challenges.length).zip (o.chan.challenges.toList.zip v.challenges) do
    if a != b then return some s!"challenge {i}: Lean {eHex a}, Rust {eHex b}"
  if o.chan.zeros.toList != v.zeros then
    return some s!"zeros: Lean {o.chan.zeros.toList.map eHex}, Rust {v.zeros.map eHex}"
  if !v.nonzeros.isEmpty then return some "the Rust checked a nonzero value; this verifier has none"
  if o.accepts != v.accept then return some s!"accept: Lean {o.accepts}, Rust {v.accept}"
  match o.result with
  | .error _ => return none
  | .ok r =>
    if some r.relations != v.relations then return some s!"relations: Lean {r.relations}, Rust {v.relations}"
    if r.stackVars.map (fun (c, n) ↦ (c.name, n)) != v.stackVars then
      return some s!"stack vars: Lean {r.stackVars.map fun (c, n) ↦ (c.name, n)}, Rust {v.stackVars}"
    if r.openings.length != v.openings.length then
      return some s!"openings: Lean {r.openings.length}, Rust {v.openings.length}"
    for (i, (a, b)) in (List.range r.openings.length).zip (r.openings.zip v.openings) do
      if !sameOpening a b then return some s!"opening {i} ({a.1.name}) differs"
    if r.matrices.isSome || v.matrices then return some "matrices: the Keccak verifier has none"
    -- The stacks' layouts are the shape's alone (layoutsOfK, the Rust's layouts_for(shape, Keccak)).
    let sameLayouts := (r.layouts.zip (layoutsOfK shape)).all fun ((c, l), (c', l')) ↦
      c == c' && l.vars == l'.vars && l.blocks == l'.blocks
    if !(sameLayouts && r.layouts.length == (layoutsOfK shape).length) then
      return some "the run's layouts are not layoutsOfK the shape"
    -- A real proof's PCS_OPEN inputs (the contract's), word for word: the Lean's calls at the vector's roots.
    if !v.calls.isEmpty then
      let lean := (pcsCallsK shape roots r).map List.toArray
      if lean.length != v.calls.length then
        return some s!"PCS_OPEN calls: Lean {lean.length}, the contract {v.calls.length}"
      for (i, (a, b)) in (List.range lean.length).zip (lean.zip v.calls) do
        if a != b then return some s!"PCS_OPEN call {i}: Lean {hexOf a}, the contract {hexOf b}"
    return none

/-- One terminal vector: `structuredTerminal` against the Rust's structured and walked values. -/
def terminalCheck (line : String) : Except String (Option String) := do
  let parse : Parse (ℕ × Option E × List E × List E × List E × List E × E × E × E) := do
    expect "TERMINAL"
    let k ← nat
    let z ← token
    let zSkip ← if z == "-" then pure none else some <$> eOf z
    let rowLow ← many eElem
    let chiIn ← many eElem
    let chiInPrime ← many eElem
    let s ← many eElem
    let alpha ← eElem
    let structured ← eElem
    let walked ← eElem
    pure (k, zSkip, rowLow, chiIn, chiInPrime, s, alpha, structured, walked)
  let (k, zSkip, rowLow, chiIn, chiInPrime, s, alpha, structured, walked) ← parse.run' (tokens line)
  let lean := structuredTerminal zSkip rowLow chiIn chiInPrime s alpha
  if lean != structured then return some s!"skip {k}: Lean {eHex lean}, Rust {eHex structured}"
  if structured != walked then return some s!"skip {k}: the Rust's structured and walked terminals differ"
  -- The Lean walk of the block (`walkedTerminalK`, `keccak_flock::row_values`) gives the same value.
  let leanWalked := walkedTerminalK zSkip rowLow chiIn chiInPrime s alpha
  if leanWalked != walked then return some s!"skip {k}: Lean's walked terminal {eHex leanWalked}, Rust {eHex walked}"
  -- A control: another α changes it.
  if structuredTerminal zSkip rowLow chiIn chiInPrime s (alpha + 1) == structured then
    return some s!"skip {k}: the terminal does not depend on α"
  return none

def vectorsOf (lines : List String) : List (List String) :=
  let (done, current) := lines.foldl (fun (acc : List (List String) × List String) l ↦
    if l.startsWith "VECTOR " then (if acc.2.isEmpty then acc.1 else acc.1 ++ [acc.2], [l])
    else if l == "END" then (acc.1 ++ [acc.2], []) else (acc.1, acc.2 ++ [l])) ([], [])
  if current.isEmpty then done else done ++ [current]

/-! ### Self-tests -/

def selfTests : List (String × Bool) :=
  let shapes := keccakRuns.map fun (_, _, cells, rows) ↦ keccakShapeOf cells rows
  let valid := shapes.all fun s ↦ s.heights.length == 6 && s.validate true
  let c1 (s : Shape) : StackLayout := ((layoutsOfK s).lookup .c1).getD default
  let qflock := shapes.all fun s ↦
    ((c1 s).limbs .qflock).map (·.2.1) == [s.heights.getD 5 0 + 11]
  let lanes := shapes.all fun s ↦
    (List.range 86).all fun i ↦ ((c1 s).limbs (.table 5 i)).length == 1
  let perm := ((source.toList.map (·.1)).mergeSort (fun a b ↦ decide (a ≤ b))) == List.range 25
  let rhoOk := (List.range 25).all fun i ↦ (source.getD i (0, 0)).2 == rho.getD (source.getD i (0, 0)).1 0
  let offsets := (shiftOffsets.toList.filter id).length == 40
  let c400 := ((c1 keccak400).vars == 28)
  [("every Keccak run's shape is valid", valid),
    ("C1 holds q_flock at h_SHA3 + 11 variables", qflock),
    ("C1 holds the SHA3 table's 86 columns, the 50 lanes included", lanes),
    ("SOURCE is a permutation of the lanes with RHO's rotations", perm && rhoOk),
    ("40 shift offsets (keccak_flock.rs)", offsets),
    ("C1 is 2^28 words at 400 signatures (KECCAK.md)", c400)]

def main : IO Unit := do
  for (n, ok) in selfTests do
    IO.println s!"{if ok then "SELF-TEST OK" else "SELF-TEST FAILED"} {n}"
  if !selfTests.all (·.2) then throw (IO.userError "a self-test failed")
  let path := (← IO.getEnv "KECCAK_VECTORS").getD "keccak_vectors.txt"
  let text ← IO.FS.readFile path
  let lines := (text.splitOn "\n").filter fun l ↦ !l.startsWith "#" && l ≠ ""
  let mut failures : List String := []
  let terminals := lines.filter (·.startsWith "TERMINAL ")
  let mut terminalOk := 0
  for l in terminals do
    match terminalCheck l with
    | .ok none => terminalOk := terminalOk + 1
    | .ok (some d) =>
      failures := failures ++ [s!"terminal: {d}"]
      IO.println s!"TERMINAL DISAGREE {d}"
    | .error e =>
      failures := failures ++ [s!"terminal: {e}"]
      IO.println s!"TERMINAL UNREADABLE {e}"
  IO.println s!"TERMINALS {terminalOk}/{terminals.length} agree (skips 0..6: structured, Rust walked, Lean walked)"
  let vectors := vectorsOf (lines.filter fun l ↦ !l.startsWith "TERMINAL ")
  let mut agree := 0
  let mut accepted := 0
  let mut rejected := 0
  let mut tally : List (String × ℕ × ℕ) := []
  let start ← IO.monoMsNow
  for vlines in vectors do
    match parseVector vlines with
    | .error e =>
      failures := failures ++ [s!"unreadable vector: {e}"]
      IO.println s!"UNREADABLE {e}"
    | .ok v =>
      match compare v with
      | .ok none =>
        agree := agree + 1
        if v.accept then accepted := accepted + 1 else rejected := rejected + 1
        let key := v.kind
        let (a, r) := ((tally.find? (·.1 == key)).map (·.2)).getD (0, 0)
        tally := (tally.filter (·.1 != key)) ++ [(key, if v.accept then (a + 1, r) else (a, r + 1))]
        IO.println s!"AGREE {v.id} {v.shape} {v.flock} {v.claims} {v.kind}: {if v.accept then "accept" else
          s!"reject{(v.error.map (" " ++ ·)).getD ""}"}, {v.challenges.length} challenges, {v.zeros.length} checks, {v.openings.length} openings{if v.calls.isEmpty then "" else s!", {v.calls.length} PCS_OPEN calls word for word"}"
      | .ok (some d) =>
        failures := failures ++ [s!"{v.id}: {d}"]
        IO.println s!"DISAGREE {v.id} {v.shape} {v.flock} {v.claims} {v.kind}: {d}"
      | .error e =>
        failures := failures ++ [s!"{v.id}: {e}"]
        IO.println s!"ERROR {v.id}: {e}"
  let stop ← IO.monoMsNow
  IO.println s!"SUMMARY {agree}/{vectors.length} vectors agree on every value; accepted by both {accepted}, rejected by both {rejected}; by kind (accept, reject): {tally}; {terminalOk}/{terminals.length} terminals; {(stop - start) / 1000} s"
  if !failures.isEmpty then throw (IO.userError s!"{failures.length} disagreements: {failures}")

end UniKeccakTest

#eval UniKeccakTest.main
