-- Part of this repository (new here, not from leanVM). Transcribed from `crates/leanvm/statement/src/keccak_flock.rs`
-- (`row_values`, `t_word`, `state_word`) and `flock_min.rs` (`walked_terminal_with`, `known_weights_with`): the
-- forward walk of the Keccak-f[1600] Flock block of `crates/vendor/flock-42422001/src/keccak.rs` (`docs/leanvm/flock/KECCAK.md`
-- §4.2, M1). MIT OR Apache-2.0; see AGENTS.md.
module

public import UniKeccak.Terminal

/-!
# The Keccak-f block's walked lincheck terminal (the structured terminal's reference)

`keccakRowValues w` is `(A0 w, B0 w)` for the Keccak-f block's matrices, by one forward walk of the block
(`keccak_flock::row_values`): the port region (constants, inputs, the outputs' copies), then each round's `t` rows
(`A = 1 + b[x+1]`, `B = b[x+2]`) and state rows (`A = b + t`, ι's constant in lane 0, `B = 1`), `b = πρθ(A_{j−1})`.
`walkedTerminalK` is leanVM's walked terminal on it (`flock_min::walked_terminal_with::<S, KeccakWalked>`): the
matrices' sum weighed by `e = E ⊗ eq(chi_in, ·)` and `w = s ⊗ eq(chi_in', ·)`, the `C = I` claim's term and the
constant wire's pin. It is not part of the verifier: the runner checks `structuredTerminal = walkedTerminalK` on the
Rust's random inputs at every skip, as the Rust's own test does.
-/

@[expose] public section

namespace UniKeccak

open LeanVM.Parameters UniStatement

/-- `t_word(j, l)`: the word of `t_j`'s lane `l`. -/
def tWord (j l : ℕ) : ℕ := 64 * (j + 2) + l

/-- **`row_values(w)`**: `(A0 w, B0 w)`, every row's inner product with the column weights `w` (`2^17` of them). -/
def keccakRowValues (w : Array E) : Array E × Array E := Id.run do
  let size := 2 ^ logSize
  let mut left : Array E := Array.replicate size 0
  let mut right : Array E := Array.replicate size 0
  let one := w.getD constantColumn 0
  -- The port region: constants (every Y bit 0, the x quad's X and V bit 1), inputs, the outputs' copies.
  for q in [0:32] do
    let s := 64 * keccakPortWord q roleY
    left := left.set! s one
    right := right.set! s one
    if q < lanes then
      for z in [0:64] do
        let c := 64 * keccakPortWord q roleC + z
        left := left.set! c (w.getD c 0)
        right := right.set! c one
        let v := 64 * keccakPortWord q roleV + z
        left := left.set! v (w.getD (64 * keccakPortWord q roleX + z) 0)
        right := right.set! v one
  for role in [roleX, roleV] do
    let s := 64 * keccakPortWord xQuad role + 1
    left := left.set! s one
    right := right.set! s one
  for j in [0:rounds] do
    -- b's forms: θ's column sums of A_{j−1}, then each lane's terms at its ρ-rotated position.
    let lane (l z : ℕ) : E := w.getD (64 * keccakStateWord ((j : ℤ) - 1) l + z) 0
    let col : Array (Array E) := Array.ofFn (n := 5) fun x ↦ Array.ofFn (n := 64) fun z ↦
      sumRange 0 5 fun y ↦ lane (x.val + 5 * y) z.val
    let b : Array (Array E) := Array.ofFn (n := lanes) fun i ↦
      let (src, rot) := source.getD i.val (0, 0)
      let x := src % 5
      Array.ofFn (n := 64) fun z ↦
        let zp := (z.val + 64 - rot) % 64
        lane src zp + (col.getD ((x + 4) % 5) #[]).getD zp 0 + (col.getD ((x + 1) % 5) #[]).getD ((zp + 63) % 64) 0
    for l in [0:lanes] do
      let x := l % 5
      let y := l / 5
      for z in [0:64] do
        let t := 64 * tWord j l + z
        left := left.set! t (one + (b.getD ((x + 1) % 5 + 5 * y) #[]).getD z 0)
        right := right.set! t ((b.getD ((x + 2) % 5 + 5 * y) #[]).getD z 0)
        let s := 64 * keccakStateWord (j : ℤ) l + z
        let rcBit := l == 0 && ((rc.getD j 0) >>> z.toUInt64) &&& 1 == 1
        left := left.set! s ((b.getD l #[]).getD z 0 + w.getD t 0 + (if rcBit then one else 0))
        right := right.set! s one
  return (left, right)

/-- **`walked_terminal_with::<S, KeccakWalked>`**: the lincheck's terminal by the walk, `w = s ⊗ eq(chi_in', ·)`,
`(A0 w, B0 w)` weighed by `e = (L(z_skip) ⊗ eq(row_low)) ⊗ eq(chi_in)` and `α`, plus the `C = I` claim's term
`α² eq(chi_in, chi_in') Σ e_z s_z` and the constant wire's pin `α³ eq(bits(64 / 64), chi_in') s_0`
(`known_weights_with`). -/
def walkedTerminalK (zSkip : Option E) (rowLow chiIn chiInPrime s : List E) (alpha : E) : E := Id.run do
  let (_, lowWeightsL) := Flock.rowLowWeights zSkip rowLow
  let lowWeights := lowWeightsL.toArray
  let slices := s.toArray
  let high := eqKernel chiInPrime
  let mut w : Array E := Array.replicate (2 ^ logSize) 0
  for h in [0:high.size] do
    for l in [0:slices.size] do
      w := w.set! (h * Flock.kBits + l) (slices.getD l 0 * high.getD h 0)
  let (left, right) := keccakRowValues w
  let rows := eqKernel chiIn
  let mut matrix : E := 0
  for h in [0:rows.size] do
    let mut lSum : E := 0
    let mut rSum : E := 0
    for low in [0:lowWeights.size] do
      lSum := lSum + lowWeights.getD low 0 * left.getD (h * Flock.kBits + low) 0
      rSum := rSum + lowWeights.getD low 0 * right.getD (h * Flock.kBits + low) 0
    matrix := matrix + rows.getD h 0 * (lSum + alpha * rSum)
  let constantBits := (List.range chiInPrime.length).map (bitE (constantColumn / Flock.kBits))
  let pinWeight := epow alpha 3 * eqEval constantBits chiInPrime
  let cWeight := epow alpha 2 * eqEval chiIn chiInPrime
  return matrix + cWeight * dot lowWeightsL s + pinWeight * s.getD (constantColumn % Flock.kBits) 0

end UniKeccak

end
