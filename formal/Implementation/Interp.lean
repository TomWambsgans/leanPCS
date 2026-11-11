-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Interprets the graph as `crates/membership/evm/src/codegen.rs` compiles it, with the claims' packing of
-- `crates/evm_link/src/assemble.rs` (`Item::DeclaredClaim`).
import Implementation.Graph
import Implementation.Arith

/-!
# The graph, interpreted on calldata

What the contract computes, node by node, as `crates/membership/evm/src/codegen.rs` compiles each node: every
value is an EVM word (a natural number below `2^256`), and

* `const c` is `c`;
* `statement k` and `root k` are the high (`k` even) or low (`k` odd) 128 bits of the word of the
  arguments at `32 ⌊k/2⌋` (the statement) or `64 + 32 ⌊k/2⌋` (the four roots), the arguments being
  calldata after the 4-byte selector (`CALLDATALOAD`, `SHR 128` or `AND 2^128 - 1`);
* `input i` is the word at `192 + 24 i` shifted right by 64 bits: the scalar's 24 big-endian bytes;
* `add` is `XOR`, `mul` is `FIELD_MUL` (`mulE`), `frob` the Frobenius (`frobE`);
* `seed` is the hash of the label: the 16-byte name, the circuit's commitment (its root, slot 0, and
  the low 24 bytes of its out-of-domain answer's word, slot 1, both read from storage), the 64 bytes of
  the statement;
* `hash st xs` is the hash of the words `st` and `xs`, each 32 bytes big-endian (`MSTORE`);
* `low a` is the low 192 bits of `a` (`AND 2^192 - 1`).

The hash `H` is a parameter: Keccak-256 (`KECCAK256`) as deployed, any function in the model.
`run` adds what the contract checks before its claims: the calldata's length and selector, and that
every node of `nonzero` is not zero; it gives the words written to its output region (`outputs`: a
node's value, a constant, a word of calldata, or a stored word). `calls` packs each PCS claim of
`claims` from those words as `Item::DeclaredClaim` does: `1 ‖ n ‖` the root's word (32 bytes) `‖` the low
24 bytes of the words of its out-of-domain answer, its point's `n` coordinates and its value.
`accepts`: the contract returns the word 1 exactly when it reaches its checks and claim `k` is
attested for every `k` (`attest k`: payload `k` of the frame of PCS claims the calldata's last byte
names is the claim's Keccak-256, so the block proves the claim). How the frame is checked is not
modelled.
-/

namespace Implementation

open Emitted

/-- The big-endian number of some bytes. -/
def beNat (l : List UInt8) : Nat := l.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- The `n` big-endian bytes of `w mod 256^n` (`MSTORE` for `n = 32`). -/
def beBytes (n w : Nat) : List UInt8 :=
  (List.range n).map fun k => ((w >>> (8 * (n - 1 - k))) % 256).toUInt8

/-- `CALLDATALOAD`: the big-endian word of the 32 bytes at `o`, zero past the end. -/
def cdWord (cd : List UInt8) (o : Nat) : Nat := beNat ((List.range 32).map fun k => cd.getD (o + k) 0)

/-- The high (`k` even) or low (`k` odd) 128 bits of a word. -/
def half (w k : Nat) : Nat := if k % 2 = 0 then w >>> 128 else w % 2 ^ 128

/-- Bytes from the numbers of `Graph.lean`. -/
def bytesOf (l : List Nat) : List UInt8 := l.map Nat.toUInt8

/-- **What a call reads**: the hash, the circuit's commitment in storage (the root's 32 bytes, slot 0;
the out-of-domain answer's word, slot 1) and the calldata. -/
structure Env where
  H : List UInt8 → Vector UInt8 32
  idx : List UInt8
  ood : Nat
  cd : List UInt8

/-- **One node's value**, from the values of the nodes before it. -/
def step (e : Env) (vals : Array Nat) : Node → Nat
  | .const c => c
  | .statement k => half (cdWord e.cd (4 + 32 * (k / 2))) k
  | .root k => half (cdWord e.cd (4 + 64 + 32 * (k / 2))) k
  | .input i => cdWord e.cd (4 + 192 + 24 * i) >>> 64
  | .add a b => vals.getD a 0 ^^^ vals.getD b 0
  | .mul a b => mulE (vals.getD a 0) (vals.getD b 0)
  | .frob a => frobE (vals.getD a 0)
  | .seed => beNat (e.H (bytesOf name ++ e.idx ++ (beBytes 32 e.ood).drop 8 ++ (e.cd.drop 4).take 64)).toList
  | .hash st xs =>
    beNat (e.H (beBytes 32 (vals.getD st 0) ++ xs.flatMap fun x => beBytes 32 (vals.getD x 0))).toList
  | .low a => vals.getD a 0 % B192

/-- The values of a list of nodes, in order. -/
def valuesOf (e : Env) (l : List Node) : Array Nat :=
  l.foldl (fun vals n => vals.push (step e vals n)) #[]

/-- **The values of the graph's nodes.** -/
def values (e : Env) : Array Nat := valuesOf e nodes

/-- An output word's value. -/
def wordOf (e : Env) (vals : Array Nat) : Word → Nat
  | .node i => vals.getD i 0
  | .const w => w
  | .calldata o => cdWord e.cd (4 + o)
  | .storedRoot => beNat e.idx
  | .storedOod => e.ood

/-- The calldata of a call of the verifier: `4 + 192 + 24 · inputs + 1` bytes (the last the frame's
index), the selector first. -/
def WellFormed (cd : List UInt8) : Prop :=
  cd.length = 4 + 192 + 24 * inputs + 1 ∧ cd.take 4 = bytesOf selector

instance (cd : List UInt8) : Decidable (WellFormed cd) := by unfold WellFormed; infer_instance

/-- **What the contract writes to its output region**, or `none` where it reverts before: on calldata
of another length or selector, or when a node of `nonzero` is zero. -/
def run (e : Env) : Option (List Nat) :=
  if WellFormed e.cd then
    let vals := values e
    if nonzero.all fun i => vals.getD i 0 != 0 then some (outputs.map (wordOf e vals))
    else none
  else none

/-- **A PCS claim's bytes**, packed from the output words (`Item::DeclaredClaim`): the version `1`, the
number `n` of the point's coordinates, the root's word (32 bytes), then the low 24 bytes of the words
of the out-of-domain answer, the `n` coordinates and the value. -/
def claimBytes (ws : List Nat) (c : Nat × Nat × List Nat × Nat) : List UInt8 :=
  [1, c.2.2.1.length.toUInt8] ++ beBytes 32 (ws.getD c.1 0) ++
    (c.2.1 :: (c.2.2.1 ++ [c.2.2.2])).flatMap fun i => beBytes 24 (ws.getD i 0)

/-- The PCS claims the contract checks declared, in order. -/
def calls (ws : List Nat) : List (List UInt8) := claims.map (claimBytes ws)

/-- Every claim attested, claim `k` by `attest k`. -/
def allAttested (attest : Nat → List UInt8 → Bool) : Nat → List (List UInt8) → Bool
  | _, [] => true
  | k, b :: bs => attest k b && allAttested attest (k + 1) bs

/-- **The contract's verdict**: it returns the word 1 exactly when it reaches its checks and claim `k` is
attested (`attest k`: declared as payload `k`, so proved by the block) for every `k`. -/
def accepts (attest : Nat → List UInt8 → Bool) (e : Env) : Bool :=
  match run e with
  | some ws => allAttested attest 0 (calls ws)
  | none => false

end Implementation
