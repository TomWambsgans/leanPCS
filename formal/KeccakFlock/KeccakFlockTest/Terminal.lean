-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md.
import KeccakFlock

/-!
# The two terminals against the Rust's

The vectors are `crates/leanvm/statement/tests/lean_keccak_block.rs`'s `terminal_vectors` (`cargo test --release -p
leanvm_statement --test lean_keccak_block -- --nocapture`): at every skip `k ≤ 6`, the inputs drawn from xorshift64
from `0x5eed ⊕ k` (`z_skip` when `k > 0`, `row_low` of `6 − k`, `chi_in`, `chi_in'` of 11, `s` of 64, `α`, each
element three draws), and the Rust's `structured_terminal` and `walked_terminal_with::<_, KeccakWalked>` there (equal).
Here `Terminal.structuredTerminal` is evaluated at all seven, `Terminal.walkedTerminal` (a walk of `2^17` rows, about
two minutes each in the interpreter) at skips 0, 3 and 6; the file takes about nine minutes. Run with
`lake env lean ../KeccakFlock/KeccakFlockTest/Terminal.lean` from `formal/EndToEnd`.
-/

open LeanVM.Parameters KeccakFlock.Terminal

namespace KeccakFlockTest.Terminal

/-- The inputs at skip `k`, as the Rust test draws them. -/
def inputs (k : ℕ) : Option E × List E × List E × List E × List E × E := Id.run do
  let mut x : UInt64 := 0x5eed ^^^ k.toUInt64
  let mut out : Array E := #[]
  for _ in [0:(if k > 0 then 1 else 0) + (6 - k) + 11 + 11 + 64 + 1] do
    x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 7); x := x ^^^ (x <<< 17)
    let c0 := x
    x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 7); x := x ^^^ (x <<< 17)
    let c1 := x
    x := x ^^^ (x <<< 13); x := x ^^^ (x >>> 7); x := x ^^^ (x <<< 17)
    out := out.push (E.ofLimbs (K.ofLane c0) (K.ofLane c1) (K.ofLane x))
  let l := out.toList
  let (zSkip, l) := if k > 0 then (l.head?, l.tail) else (none, l)
  return (zSkip, l.take (6 - k), (l.drop (6 - k)).take 11, (l.drop (17 - k)).take 11, (l.drop (28 - k)).take 64,
    l.getD (92 - k) 0)

def limbs (e : E) : UInt64 × UInt64 × UInt64 := ((e.limb 0).lane, (e.limb 1).lane, (e.limb 2).lane)

def structuredAt (k : ℕ) : E :=
  let (z, rl, ci, cp, s, a) := inputs k
  structuredTerminal z rl ci cp s a

def walkedAt (k : ℕ) : E :=
  let (z, rl, ci, cp, s, a) := inputs k
  walkedTerminal z rl ci cp s a

/-- The Rust's terminal at each skip (both terminals print the same limbs). -/
def rust : List (UInt64 × UInt64 × UInt64) :=
  [(0x251566f1e849567d, 0x044663645f378839, 0xc27d80a79a6f516b),
   (0x0262c14af1225af2, 0x9dfacc9a7e108520, 0x5e0b7705956d07fa),
   (0x37ae9bf4ed80ec6c, 0xdfc1af864fec0420, 0xad6b6e98fadfa0bd),
   (0x40da5a0cd369674b, 0x63e85ad8102365fb, 0x08408f8eaab9c03f),
   (0x35de7807e866aebd, 0xce3f006caf3eaf3d, 0x54a964b7c6a21528),
   (0x289d977c1ae9d419, 0x48c14d35843becee, 0xeac01335d7a9e08e),
   (0xed5a37217fcc4aae, 0x2579d2b9b50b8011, 0xb3c1121f547e915c)]

#guard (List.range 7).all fun k ↦ limbs (structuredAt k) == rust.getD k (0, 0, 0)

#guard limbs (walkedAt 0) == rust.getD 0 (0, 0, 0)
#guard limbs (walkedAt 3) == rust.getD 3 (0, 0, 0)
#guard limbs (walkedAt 6) == rust.getD 6 (0, 0, 0)

-- A changed slice changes the structured terminal: the check is not vacuous.
#guard
  let (z, rl, ci, cp, s, a) := inputs 3
  limbs (structuredTerminal z rl ci cp (s.set 7 0) a) != rust.getD 3 (0, 0, 0)

end KeccakFlockTest.Terminal
