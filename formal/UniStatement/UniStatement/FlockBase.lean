-- Part of this repository. Moved from `formal/UniStatement`'s `UniStatement/Flock.lean`, which imports this module (the
-- declarations keep their names and namespace): its constants and weights that do not depend on the BLAKE2s block,
-- transcribed from `crates/leanvm_flock_gas/src/flock_min.rs` and `flock.rs` (`PHI_BASIS`, `fixed_challenges`,
-- `lagrange_weights`, `row_low_weights`), adapted there from leanVM (https://github.com/leanEthereum/leanVM), commit
-- 42422001, `crates/verifier/src/flock.rs`. MIT OR Apache-2.0; see AGENTS.md.
module

public import UniStatement.Transcript

/-!
# Flock's block-independent constants and weights

The packing (`packing`, `kBits`), the PHI basis and points (`phi`, `fixedChallenges`), the skip's Lagrange weights
(`lagrangeWeights`) and the packing weights (`rowLowWeights`): the parts of `UniStatement.Flock` that do not depend on
the BLAKE2s block's size, which the Keccak-f block's terminal (`formal/KeccakFlock`) reads too.
-/

@[expose] public section

namespace UniStatement.Flock

open LeanVM.Parameters LeanVM.Semantics

/-- `PACKING`: 64 bits a `q_flock` word. -/
def packing : ℕ := 6

/-- `K_BITS`. -/
def kBits : ℕ := 64

/-- `N_FIXED_CHALLENGES`. -/
def nFixed : ℕ := 7

/-- `PHI_BASIS` (`flock.rs`). -/
def phiBasis : List UInt64 :=
  [0x0000000000000001, 0x033CE8BEDDC8A656, 0x512620375ED2A108, 0x0C9E636090AAFC01,
    0xBA4F3CD82801769C, 0xBA26E7904ADB4A47, 0x467698598926DC01, 0x4418AE808B28BDD0]

/-- `phi(value)`: the `GF(2)`-linear image of the byte `value` in the PHI basis. -/
def phi (value : ℕ) : E :=
  eK ((List.range 8).foldl (fun acc bit ↦ if value.testBit bit then acc ^^^ phiBasis.getD bit 0 else acc) 0)

/-- `MEDIUM_GENERATOR`. -/
def mediumGenerator : E := eNew 0x243F6A8885A308D3 0x13198A2E03707344 0xA4093822299F31D0

/-- `fixed_challenges()`: three PHI points, then `v/(1 + v)` for `v = MEDIUM_GENERATOR^(2^p)`, `p < 4`. -/
def fixedChallenges : List E :=
  let medium (p : ℕ) : E :=
    let v := epow mediumGenerator (2 ^ p)
    v * (1 + v)⁻¹
  [phi 0xF7, phi 0x53, phi 0xB5, medium 0, medium 1, medium 2, medium 3]

/-- `window_denominator(count) = (Π_{k=1}^{count−1} PHI[k])⁻¹`. -/
def windowDenominator (count : ℕ) : E := ((List.range' 1 (count - 1)).foldl (fun acc k ↦ acc * phi k) 1)⁻¹

/-- **`lagrange_weights(count, point)`**: the barycentric weights of `PHI[:count]` at `point`, by prefix
and suffix products of `point + PHI[node]`, the one denominator. -/
def lagrangeWeights (count : ℕ) (pt : E) : List E :=
  let differences : Array E := Array.ofFn (n := count) fun node ↦ pt + phi node.val
  let pre : Array E := (List.range count).foldl (fun acc i ↦ acc.push (acc.back?.getD 1 * differences.getD i 0))
    #[1]
  -- suffix[i] = Π_{j ≥ i} differences[j]
  let suf : Array E := ((List.range count).foldl (fun acc i ↦
    acc.push (acc.back?.getD 1 * differences.getD (count - 1 - i) 0)) #[1]).reverse
  let denominator := windowDenominator count
  (List.range count).map fun i ↦ pre.getD i 1 * suf.getD (i + 1) 1 * denominator

/-- `lagrange_interpolate(count, values, point)`. -/
def lagrangeInterpolate (count : ℕ) (values : List E) (pt : E) : E := dot (lagrangeWeights count pt) values

/-- `row_low_weights(z_skip, low)`: the skip's Lagrange weights, and their product with `eq(low, ·)` over
the 6 packing bits (`eq` outer, the skip inner). -/
def rowLowWeights (zSkip : Option E) (low : List E) : List E × List E :=
  let skip := match zSkip with
    | some z => lagrangeWeights (2 ^ (packing - low.length)) z
    | none => [1]
  let mle := (eqKernel low).toList
  (skip, mle.flatMap fun m ↦ skip.map fun l ↦ l * m)

end UniStatement.Flock

end
