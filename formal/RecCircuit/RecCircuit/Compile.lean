-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `crates/leanvm/rec/src/circuit/compile.rs`
-- (`compile` with `D16::new`, `pair_coordinate`, `be_bits`, `le_bits`), `crates/leanvm/rec/src/count.rs` (`live`) and
-- `crates/leanvm/statement/src/evm/machine.rs` (`root_word`, `element_word`), `transcript.rs` (`cantor_beta1`).
import RecCircuit.Templates
import RecCircuit.Expand

/-!
# The compiler (`compile.rs`)

`compile r`: π1's recorded verifier `r` (its graph, where its roots are in the stream, π1's contract IV) to π2's
circuit in D16v (`pi2(recorded, Layout::D16v, ·)`), and what the checker and the theorems read: the final view, the
builder's traces, each node's limbs, the free bits. Every step is the Rust's, in the Rust's order (regions, rows, values
and `κ` are made in the same order, so the circuit is the same, which `RecCircuitTest` compares); the witness is not
computed (it is the Rust's, for the honest prover), so neither are the free bits' and free limbs' words.

**Deviations, all rejections** (the Rust would build a circuit; the Lean compiler refuses the graph, and π1-rec3's graph
has none of them): a read never hashed must be a 24-byte scalar (`compile.rs` makes the free limbs of a shorter one
free values, so their `c1`, `c2` limbs would be unconstrained, while the graph's are zero); a bit field's integer must
be at most 8 bytes (for a wider read, the circuit's field could take bits past the low limb that `E::bits` ignores).
-/

namespace RecCircuit

open Primitives

/-- π1's recorded verifier, as the compiler takes it (`Recorded`). -/
structure Recorded where
  graph : Graph
  /-- Where each of π1's roots starts in the stream (`roots_at`). -/
  rootsAt : List ℕ
  /-- π1's contract IV, which the seed hashes (`recorded.iv(program_iv)`). -/
  iv : List UInt8
  /-- π1's claims (indices among the calls) whose Keccak-256 π2's circuit computes (`compile::hashed_claims` of π1's
  Fiat–Shamir shape: the main line none, π1-rec3 `[0]`, π1-rec4 `[0, 1, 2]`); those past the calls are dropped, as in
  the Rust. -/
  hashed : List ℕ := []
  deriving Inhabited

/-! ## `RecGraph`'s graphs as the compiler's input -/

def ofRGWord : RecGraph.Word → Word
  | .node id => .node id
  | .const w => .const w
  | .stream a => .stream a

/-- **The compiler's input for a `RecGraph` graph**, its roots' offsets, π1's contract IV and the claims π2's circuit
hashes (`compile::hashed_claims` of π1's Fiat–Shamir shape; none by default, π1-rec3 at `f96a7938`). -/
def ofRG (g : RecGraph.Graph) (rootsAt : List ℕ) (iv : List UInt8) (hashed : List ℕ := []) : Recorded :=
  ⟨⟨g.nodes.map ofRGNode, g.zero, g.nonzero, g.kernels, g.calls.map (·.map ofRGWord), g.streamLen⟩, rootsAt, iv,
    hashed⟩

/-- The bits of a big-endian integer of `nbytes` bytes from byte `first`, as `(exponent, bit)` (`be_bits`). -/
def beBits {α : Type} (bit : ℕ → α) (first nbytes : ℕ) : List (ℕ × α) :=
  (List.range (8 * nbytes)).map fun e => (e, bit (8 * (first + nbytes - 1 - e / 8) + e % 8))

/-- The bits of a little-endian integer (`le_bits`). -/
def leBits {α : Type} (bit : ℕ → α) (first nbytes : ℕ) : List (ℕ × α) :=
  (List.range (8 * nbytes)).map fun e => (e, bit (8 * (first + e / 8) + e % 8))

/-- A number's 32 big-endian bytes. -/
def wordBytes32 (w : ℕ) : List UInt8 := (List.range 32).map fun i => (w / 256 ^ (31 - i) % 256).toUInt8

def bytesWord (bytes : List UInt8) : ℕ := beNat bytes

/-- `root_word`: each 16-byte half reversed. -/
def rootWord (w : ℕ) : ℕ :=
  let b := wordBytes32 w
  bytesWord ((b.take 16).reverse ++ (b.drop 16).reverse)

/-- `element_word`: `c0 + c1·2^64 + c2·2^128`. -/
def elementWord (x : F192) : ℕ := x.c0.toNat + x.c1.toNat * 2 ^ 64 + x.c2.toNat * 2 ^ 128

/-- The nodes `outputs` read, through their operands (`count::live`). -/
def live (nodes : Array Node) (outputs : List ℕ) : Array Bool := Id.run do
  let mut live := Array.replicate nodes.size false
  for o in outputs do live := live.set! o true
  for i' in [0:nodes.size] do
    let i := nodes.size - 1 - i'
    if live.getD i false then
      match nodes.getD i default with
      | .add a b | .mul a b => live := (live.set! a true).set! b true
      | .hash s _ _ => live := live.set! s true
      | .low h | .narrow h | .wide h _ | .bits h _ _ => live := live.set! h true
      | _ => pure ()
  return live

/-- A challenge node (`pair_coordinate`'s `is_challenge`). -/
def pairChallenge (nodes : Array Node) (z : ℕ) : Bool :=
  match nodes.getD z default with
  | .narrow _ | .low _ | .wide .. => true
  | _ => false

/-- `pair_coordinate`'s `y1_of`: node `i` is `y_1(z) = z·z + z` of a challenge `z`. -/
def pairY1 (nodes : Array Node) (i : ℕ) : Option ℕ :=
  match nodes.getD i default with
  | .add a b => [(a, b), (b, a)].findSome? fun (sq, z) => match nodes.getD sq default with
    | .mul x y => if x = z ∧ y = z ∧ pairChallenge nodes z = true then some z else none
    | _ => none
  | _ => none

/-- `pair_coordinate`: a call word's node `y_1(z) = z·z + z` or `y_0(z) = z + β_1 · y_1(z)` of a challenge `z`
(`β_1` is `UniStatement.cantorBeta1`, `transcript::cantor_beta1`). -/
def pairCoordinate (nodes : Array Node) (id : ℕ) : Option (ℕ × ℕ) :=
  match pairY1 nodes id with
  | some z => some (z, 1)
  | none => match nodes.getD id default with
    | .add a b => [(a, b), (b, a)].findSome? fun (z, product) => match nodes.getD product default with
      | .mul c y => [(c, y), (y, c)].findSome? fun (c, y) => match nodes.getD c default with
        | .const l0 l1 l2 => if F192.new l0 l1 l2 = UniStatement.cantorBeta1 ∧ pairY1 nodes y = some z then some (z, 0) else none
        | _ => none
      | _ => none
    | _ => none

/-- One of π1's claims hashed in the circuit (`compile.rs`'s hashed claims): its index among the calls, the message
its sponge absorbs (the claim's encoding as bits, byte order, low bit first), the digest's 256 values and its four
statement-order limbs (the `claimHash` port's), and each element of the claim whose bytes are free bits: its node,
its 192 free bits (byte `b`'s bit `j` at `8b + j`, the element's big-endian bytes `c2 ‖ c1 ‖ c0`), their packings into
three limbs and the sum `packed + limbs` (a zero port's). -/
structure ClaimT where
  ci : ℕ
  message : Array Bit
  digest : Array Val
  limbs4 : Array Val
  frees : Array (ℕ × Array Val × Array Val × Array Val)
  deriving Inhabited

/-- What the compiler returns: the circuit, the final view, the builder's final state (its traces), and per node of
the expanded graph its limbs and digest. -/
structure Compiled where
  circuit : Circuit
  view : View
  st : St
  nodes : Array Node
  map : Array ℕ
  live : Array Bool
  /-- An element node's three limb values. -/
  limbs : Array (Option (Array Val))
  /-- A seed's or hash's 256 digest values. -/
  digests : Array (Option (Array Val))
  /-- Each stream bit's free bit (`none`: not hashed), and each public-input bit's. -/
  bitSelf : Array (Option Val)
  /-- A first-block stream bit's copy, and each public-input bit's. -/
  bitCopy : Array (Option Val)
  publicSelf : Array Val
  publicCopy : Array Val
  /-- The never-hashed reads: offset and their three free limbs. -/
  freeReads : Array (ℕ × Array Val)
  statementLimb : Array Val
  /-- Each root's four limbs (as its port carries them). -/
  rootLimbs : Array (Array Val)
  /-- The zero checks' nodes (mapped), the calls' element nodes (by element index). -/
  zero : List ℕ
  elementNodes : Array ℕ
  /-- A hash's sponge rate values (`64 · lanes`, `lanes > 4`: a wide challenge reads it), by node. -/
  rates : Array (Option (Array Val)) := #[]
  /-- The claims hashed in the circuit, in order (`claimHash j` is `claims[j]`'s). -/
  claims : Array ClaimT := #[]
  /-- The stream offsets of the roots ported (those an encoded call names), in order. -/
  rootsAt : List ℕ := []
  deriving Inhabited

/-- The positions π2's circuit must fit: `2^24` (`compile::FIT_LOG_N`). -/
def FIT_LOG_N : ℕ := 24

namespace Builder

def constantBits (bytes : List UInt8) : Array Bit :=
  ((List.range (8 * bytes.length)).map fun i =>
    if (bytes.getD (i / 8) 0).toNat.testBit (i % 8) then Bit.one else Bit.zero).toArray

/-- An element of a hashed claim whose bytes are free bits (`compile.rs`'s hashed claims): the element's 24
big-endian bytes (`c2 ‖ c1 ‖ c0`) as free bits appended to `message` (a copy in the first block), packed into three
limbs, and their sum with the element's own limbs `l` (a zero port). Returns the message and the element's trace:
its node, its bits (byte by byte, low bit first), the packed limbs, the sum. -/
def freeElement (l : Array Val) (id : ℕ) (message : Array Bit) :
    BM (Array Bit × (ℕ × Array Val × Array Val × Array Val)) := do
  let mut message := message
  let mut bits : Array Val := #[]
  let mut limbBits : Array (List (ℕ × Val)) := #[[], [], []]
  for byte in [0:24] do
    let li := 2 - byte / 8
    let e0 := 8 * (7 - byte % 8)
    for bit in [0:8] do
      let e := e0 + bit
      let (v, c) ← bitAndCopy
      message := message.push (.v (if message.size < 1088 then c else v))
      bits := bits.push v
      limbBits := limbBits.modify li (· ++ [(e, v)])
  let mut packed : Array Val := #[]
  for li in [0:3] do packed := packed.push (← pack (limbBits.getD li []))
  let sum ← arith .add packed l true
  portOf sum .zero
  return (message, (id, bits, packed, sum))

/-- **π2's circuit for `r` in D16v** (`compile(recorded, 4, D16::new, ·)`). -/
def compileM (r : Recorded) (g : Array Node) (map : Array ℕ) : BM Compiled := do
  let streamLen := r.graph.streamLen
  let mapW := fun (w : Word) => match w with
    | .node id => Word.node (map.getD id 0)
    | other => other
  let callWords := r.graph.calls.map (·.map mapW)
  let zero := r.graph.zero.map fun id => map.getD id 0
  need r.graph.nonzero.isEmpty "π1's verifier checks nothing nonzero"
  let outputs := (callWords.flatten.filterMap fun w => match w with | .node id => some id | _ => none) ++ zero
  let live := RecCircuit.live g outputs
  let hashedClaims := r.hashed.filter (· < callWords.length)
  need (hashedClaims.Pairwise (· < ·)) "the hashed claims increase (Lean compiler's check)"
  initD16
  initXors
  initBools
  initPacker
  initArith
  initPorts
  initCopies
  -- The stream's hashed bytes, and those in a call's first block.
  let mut hashed := Array.replicate streamLen false
  let mut firstBlock := Array.replicate streamLen false
  for id in [0:g.size] do
    if live.getD id false then
      match g.getD id default with
      | .hash _ f t =>
        for i in [f:t] do hashed := hashed.set! i true
        for i in [f:min t (f + 136 - 32)] do firstBlock := firstBlock.set! i true
      | _ => pure ()
  -- Free bits: the stream's hashed bytes', then the public input's.
  let mut bitSelf : Array (Option Val) := Array.replicate (8 * streamLen) none
  let mut bitCopy : Array (Option Val) := Array.replicate (8 * streamLen) none
  for i in [0:streamLen] do
    if hashed.getD i false then
      for j in [0:8] do
        let (v, c) ← bitAndCopy
        bitSelf := bitSelf.set! (8 * i + j) (some v)
        if firstBlock.getD i false then bitCopy := bitCopy.set! (8 * i + j) (some c)
  let mut publicSelf : Array Val := #[]
  let mut publicCopy : Array Val := #[]
  for _ in [0:256] do
    let (v, c) ← bitAndCopy
    publicSelf := publicSelf.push v
    publicCopy := publicCopy.push c
  let streamBit := fun (i : ℕ) => (bitSelf.getD i none).getD NONE
  -- Keccak-256 calls, in the chain's order. A hash a live wide challenge reads gives its rate's lanes up to that
  -- challenge's (challenge `k`: bytes `8 + 24k .. 32 + 24k`, lanes `1 + 3k ..= 3 + 3k`); another, its digest's 4.
  let mut lanesOf : Array ℕ := Array.replicate g.size 4
  for id in [0:g.size] do
    if live.getD id false then
      match g.getD id default with
      | .wide h k => lanesOf := lanesOf.modify h (max · (4 + 3 * k))
      | _ => pure ()
  let mut digests : Array (Option (Array Val)) := Array.replicate g.size none
  let mut rates : Array (Option (Array Val)) := Array.replicate g.size none
  for id in [0:g.size] do
    if live.getD id false then
      match g.getD id default with
      | .seed =>
        let message := constantBits NAME ++ constantBits r.iv ++ publicCopy.map Bit.v
        digests := digests.set! id (some (← keccak256 message))
      | .hash s f t =>
        let state := (digests.getD s none).getD #[]
        let mut message : Array Bit := state.map Bit.v
        for i in [f:t] do
          for j in [0:8] do
            let k := 8 * i + j
            match bitCopy.getD k none with
            | some c => message := message.push (.v c)
            | none =>
              need ((bitSelf.getD k none).isSome) "a hashed bit"
              message := message.push (.v (streamBit k))
        let lanes := lanesOf.getD id 4
        let out ← keccak256Lanes message lanes
        digests := digests.set! id (some (out.extract 0 256))
        if lanes > 4 then rates := rates.set! id (some out)
      | _ => pure ()
  -- The statement's limbs, packed once.
  let mut statementLimb : Array Val := #[]
  for k in [0:4] do
    statementLimb := statementLimb.push (← pack (beBits (fun i => publicSelf.getD i 0) (8 * k) 8))
  -- Uses left of each node.
  let mut uses : Array ℕ := Array.replicate g.size 0
  for id in [0:g.size] do
    if live.getD id false then
      match g.getD id default with
      | .add a c | .mul a c =>
        uses := uses.modify a (· + 1)
        if a != c then uses := uses.modify c (· + 1)
      | _ => pure ()
  -- Element nodes' limbs, in node order.
  let mut limbs : Array (Option (Array Val)) := Array.replicate g.size none
  let mut endable : Array Bool := Array.replicate g.size false
  let mut freeReads : Array (ℕ × Array Val) := #[]
  for id in [0:g.size] do
    if live.getD id false then
      let node := g.getD id default
      let res : Option (Array Val × Bool) ← match node with
        | .const c0 c1 c2 => do
          let a ← fresh (F64.ofU64 c0)
          let b ← fresh (F64.ofU64 c1)
          let c ← fresh (F64.ofU64 c2)
          pure (some (#[a, b, c], true))
        | .statement k => do
          let z1 ← fresh 0
          let z2 ← fresh 0
          pure (some (#[statementLimb.getD k 0, z1, z2], true))
        | .input offset len => do
          let allHashed := (List.range len).all fun i => hashed.getD (offset + i) false
          need (allHashed || (List.range len).all fun i => !hashed.getD (offset + i) false) "a read partly hashed"
          if !allHashed then
            need (len == 24) "a read never hashed is a 24-byte scalar (Lean compiler's check)"
            let l0 ← free
            let l1 ← free
            let l2 ← free
            freeReads := freeReads.push (offset, #[l0, l1, l2])
            pure (some (#[l0, l1, l2], false))
          else
            let pk := fun (first n : ℕ) => pack (beBits streamBit first n)
            if len == 24 then do
              let a ← pk (offset + 16) 8
              let b ← pk (offset + 8) 8
              let c ← pk offset 8
              pure (some (#[a, b, c], true))
            else if len == 16 then do
              let c0 ← pk (offset + 8) 8
              let c1 ← pk offset 8
              let z ← fresh 0
              pure (some (#[c0, c1, z], true))
            else do
              let c0 ← pk offset len
              let z1 ← fresh 0
              let z2 ← fresh 0
              pure (some (#[c0, z1, z2], true))
        | .low h => do
          let d := (digests.getD h none).getD #[]
          let db := fun i => d.getD i 0
          let l0 ← pack (beBits db 24 8)
          let l1 ← pack (beBits db 16 8)
          let l2 ← pack (beBits db 8 8)
          pure (some (#[l0, l1, l2], true))
        | .narrow h => do
          let d := (digests.getD h none).getD #[]
          let db := fun i => d.getD i 0
          let l0 ← pack (beBits db 24 8)
          let l1 ← pack (beBits db 16 8)
          let l2 ← pack (beBits db 12 4)
          pure (some (#[l0, l1, l2], true))
        | .wide h k => do
          -- A wide draw's challenge `k`: the rate's bytes `8 + 24k .. 32 + 24k`, as `low` packs the digest's `8 .. 32`.
          let rt ← match rates.getD h none with
            | some rt => pure rt
            | none => throw "a wide challenge of a hash without its rate"
          let rb := fun i => rt.getD i 0
          let l0 ← pack (beBits rb (24 * k + 24) 8)
          let l1 ← pack (beBits rb (24 * k + 16) 8)
          let l2 ← pack (beBits rb (24 * k + 8) 8)
          pure (some (#[l0, l1, l2], true))
        | .bits v shift width => do
          let (offset, len) ← match g.getD v default with
            | .input offset len => pure (offset, len)
            | _ => throw "a bit field of a read integer"
          need (len ≤ 8) "a bit field of an integer of at most 8 bytes (Lean compiler's check)"
          let field := (beBits streamBit offset len).filterMap fun (e, x) =>
            if shift ≤ e && e < shift + width then some (e - shift, x) else none
          let z1 ← fresh 0
          let z2 ← fresh 0
          match field with
          | [] => do
            let z ← fresh 0
            pure (some (#[z, z1, z2], true))
          | [(0, x)] => pure (some (#[x, z1, z2], false))
          | _ => do
            let p ← pack field
            pure (some (#[p, z1, z2], true))
        | .add x y | .mul x y => do
          let op := match node with
            | .add .. => Op.add
            | _ => if x == y then Op.square else Op.mul
          let lx := (limbs.getD x none).getD #[]
          let ly := (limbs.getD y none).getD #[]
          let (ex, ey) := (endable.getD x false, endable.getD y false)
          let endX := ex && (!ey || uses.getD x 0 ≤ uses.getD y 0)
          let (a, c, en, ended) :=
            if op == .square then (lx, lx, ex, x)
            else if endX then (lx, ly, true, x)
            else if ey then (ly, lx, true, y)
            else (lx, ly, false, x)
          if en then endable := endable.set! ended false
          uses := uses.modify x (· - 1)
          if x != y then uses := uses.modify y (· - 1)
          pure (some (← arith op a c en, true))
        | .seed | .hash .. => pure none
        | .ringWeight .. => throw "expanded"
      match res with
      | some (l, canEnd) =>
        limbs := limbs.set! id (some l)
        endable := endable.set! id canEnd
      | none => pure ()
  -- π1's claims hashed here: each one's encoding as message bits (byte order, low bit first); its Keccak-256; the
  -- digest's four big-endian words, a port. A root's bytes and a hashed read's are the stream's bits (forwarded, or a
  -- copy where the first block ends them at the permutation's input); another element's 24 bytes are free bits,
  -- packed into limbs checked equal to its own (a sum, a zero port).
  let mut claims : Array ClaimT := #[]
  for j in [0:hashedClaims.length] do
    let ci := hashedClaims.getD j 0
    let words := callWords.getD ci []
    need (3 ≤ words.length && words.length - 3 < 256) "a claim's words (Lean compiler's check)"
    let n := words.length - 3
    let mut message : Array Bit := constantBits [1, n.toUInt8]
    let mut frees : Array (ℕ × Array Val × Array Val × Array Val) := #[]
    for k in [0:words.length] do
      match k, words.getD k default with
      | 0, .stream at_ =>
        need ((List.range 32).all fun i => hashed.getD (at_ + i) false) "a root is hashed"
        for i in [8 * at_:8 * (at_ + 32)] do
          let v := streamBit i
          message := message.push (.v (← if message.size < 1088 then copy v else pure v))
      | 0, .const w => message := message ++ constantBits (wordBytes32 w)
      | _, .const w =>
        need ((wordBytes32 w).take 8 == List.replicate 8 0) "an element word"
        message := message ++ constantBits ((wordBytes32 w).drop 8)
      | _, .node id =>
        let hashedRead := match g.getD id default with
          | .input offset len => len == 24 && (List.range 24).all fun i => hashed.getD (offset + i) false
          | _ => false
        match g.getD id default with
        | .const c0 c1 c2 =>
          message := message ++ constantBits ((wordBytes32 (elementWord (F192.new c0 c1 c2))).drop 8)
        | .input offset _ =>
          if hashedRead then
            for i in [8 * offset:8 * (offset + 24)] do
              let v := streamBit i
              message := message.push (.v (← if message.size < 1088 then copy v else pure v))
          else
            let l ← match limbs.getD id none with
              | some l => pure l
              | none => throw "a claim's element has limbs"
            let (msg, fr) ← freeElement l id message
            message := msg
            frees := frees.push fr
        | _ =>
          let l ← match limbs.getD id none with
            | some l => pure l
            | none => throw "a claim's element has limbs"
          let (msg, fr) ← freeElement l id message
          message := msg
          frees := frees.push fr
      | _, _ => throw "a claim's word"
    need (message.size == 8 * (82 + 24 * n)) "the claim's encoding"
    let digest ← keccak256 message
    let db := fun i => digest.getD i 0
    let mut limbs4 : Array Val := #[]
    for l in [0:4] do limbs4 := limbs4.push (← pack (beBits db (8 * l) 8))
    portOf limbs4 (.claimHash j)
    claims := claims.push ⟨ci, message, digest, limbs4, frees⟩
  -- Ports: the zero checks first, padded to a power of two; the statement, the roots, the calls' elements.
  let mut zeroPorts := 0
  for id in zero do
    match g.getD id default with
    | .const c0 c1 c2 => need (c0 == 0 && c1 == 0 && c2 == 0) "a zero check on a nonzero constant"
    | _ =>
      portOf ((limbs.getD id none).getD #[]) .zero
      zeroPorts := zeroPorts + 1
  if zeroPorts > 1 then
    for _ in [zeroPorts:nextPow2 zeroPorts] do
      let a ← fresh 0
      let b ← fresh 0
      let c ← fresh 0
      portOf #[a, b, c] .pad
  portOf statementLimb .statement
  -- The roots a call the contract encodes names (a hashed claim's root is the circuit's alone).
  let encoded := (List.range callWords.length).filter fun ci => !hashedClaims.contains ci
  let named := encoded.flatMap fun ci => (callWords.getD ci []).filterMap fun w => match w with
    | .stream at_ => some at_
    | _ => none
  let rootsAt := r.rootsAt.filter named.contains
  let mut rootOf : List (ℕ × ℕ) := []
  let mut nRoots := 0
  let mut rootLimbs : Array (Array Val) := #[]
  for at_ in rootsAt do
    need ((List.range 32).all fun i => hashed.getD (at_ + i) false) "a root is hashed"
    -- The root word is the stream's 32 bytes: limb `l` the big-endian word of bytes `24 − 8l`.
    let mut rl : Array Val := #[]
    for first in [24, 16, 8, 0] do
      rl := rl.push (← pack (beBits streamBit (at_ + first) 8))
    rootOf := rootOf ++ [(at_, nRoots)]
    rootLimbs := rootLimbs.push rl
    portOf rl (.root nRoots)
    nRoots := nRoots + 1
  let mut elementNodes : Array ℕ := #[]
  let mut circuitCalls : List (List CallWord) := []
  for call in encoded.map fun ci => callWords.getD ci [] do
    let mut words : List CallWord := []
    let mut k := 0
    for w in call do
      let cw ← match w with
        | .const bytes => pure (CallWord.const bytes)
        | .stream at_ => match rootOf.lookup at_ with
          | some i => pure (CallWord.root i)
          | none => throw "a stream word that is no root"
        | .node id =>
          match g.getD id default, pairCoordinate g id with
          | .const c0 c1 c2, _ => pure (CallWord.const (elementWord (F192.new c0 c1 c2)))
          | _, some (z, coordinate) => do
            let e ← match elementNodes.findIdx? (· == z) with
              | some e => pure e
              | none => do
                elementNodes := elementNodes.push z
                pure (elementNodes.size - 1)
            pure (CallWord.pair e coordinate)
          | _, none => do
            let e ← match elementNodes.findIdx? (· == id) with
              | some e => pure e
              | none => do
                elementNodes := elementNodes.push id
                pure (elementNodes.size - 1)
            pure (CallWord.element e)
      words := words ++ [cw]
      k := k + 1
    circuitCalls := circuitCalls ++ [words]
  for e in [0:elementNodes.size] do
    portOf ((limbs.getD (elementNodes.getD e 0) none).getD #[]) (.element e)
  -- The narrow challenges among the elements (π2 reads them as 20 bytes).
  let narrow := (List.range elementNodes.size).filter fun e => match g.getD (elementNodes.getD e 0) default with
    | .narrow _ => true
    | _ => false
  modify fun s => { s with calls := circuitCalls, hashed := hashedClaims, narrow := narrow }
  let (circuit, view) ← finish
  need (circuit.logN ≤ FIT_LOG_N) s!"π2's circuit does not fit 2^{FIT_LOG_N} positions: 2^{circuit.logN}"
  let st ← get
  return (Compiled.mk circuit view st g map live limbs digests bitSelf bitCopy publicSelf publicCopy freeReads
    statementLimb rootLimbs zero elementNodes rates claims rootsAt)

end Builder

/-- **The compiler**: π1's recorded verifier to π2's circuit (D16v), or why the Rust would panic (or the Lean
compiler refuses the graph). -/
def compileRaw (r : Recorded) : Except String Compiled := do
  if !r.graph.typed then throw "the graph is not well typed"
  let (g, map) ← expand r.graph
  let (c, _) ← (Builder.compileM r g map).run { logWidth := 4 }
  return { c with nodes := g, map := map }

end RecCircuit
