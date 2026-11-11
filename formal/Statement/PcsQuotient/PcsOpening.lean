-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Transcribed from `crates/pcs_claim/src/lib.rs` (`PcsClaim::encode`, `element_bytes`, `element_of`,
-- `ood_point`, `commit_words`, `verify_claim`; `docs/PCS_CLAIM.md`, version 1) and
-- `crates/membership/quotient/src/opening.rs`. The WHIR verifier, its commitment and the multilinear evaluation
-- are leanerVM's (`Statement/LeanVmVerifier.lean`, `Statement/Prover/{Ntt,Run,Mle}.lean`, branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0: `verifyStackedOpening`, `verifyWhir`, the program `Prog` and its run,
-- `stackWordFast`, `buildTreeM`, `mleK`).
module

public import PcsQuotient.Opening
public import Statement.Prover.Run
public import Statement.Prover.Ntt
public import Statement.Prover.Mle

/-!
# The commitments and the openings: the EIP's PCS claims (version 1)

A table is a multilinear polynomial `f` over `K` in `n` variables, its `2^n` words `f_i`
(`f(x) = Σ_i f_i · eq(x, bits of i)`, bit `0` the least significant: `tableEval`). It is committed
(`commitmentWith`, `pcs_claim::commit_words`) as

* **its root**: leanVM's WHIR commitment of the `2^n` words as a stack of `64` lanes of `2^(n−6)` words
  (word `i` is word `i mod 2^(n−6)` of lane `⌊i / 2^(n−6)⌋`), every lane Reed–Solomon encoded at rate `1/2`,
  one Merkle leaf per codeword position (`commitWith`, mumbai's `stackWordFast` and `buildTreeM`);
* **its out-of-domain answer** `f(z)`, `z` the point derived from the root alone (`oodPointWith`): `z_j` the
  element the low `24` bytes of `keccak256("leanPCS-ood" ‖ 1 ‖ n ‖ root ‖ j)` encode.

**A PCS claim** (`pcsClaimBytes`, `PcsClaim::encode`) on a commitment is `1 ‖ n ‖ root ‖ ood ‖ point ‖ value`,
each element `24` bytes (`elementBytes`): the table's polynomial takes `value` at `point`.

**Its opening** (`pcsOpeningWith`, `verify_claim`): reject unless `15 ≤ n ≤ 28`; the duplex sponge seeded by
the IV `keccak256(PCS_claim)` and the zero public digest; the proof's first two scalars are the root (absorbed,
read as leanVM's halves, `digestOfScalars`) and must be the claim's; then mumbai's `verifyStackedOpening` of the
two stack claims `f(z) = ood` and `f(point) = value` (one challenge `λ`, the weight `eq(z, ·) + λ eq(point, ·)`,
`eq` the characteristic-two `eqEval`) and WHIR at rate `1/2` (leanVM's deployed ladder), the root as commitment
`0`; and nothing of the proof left unread.

**The openings run on mumbai's proof format** (`LeanVM.Protocol.Compile.Proof`): the scalar stream and one full
Merkle path per query; the Rust prover ships pruned paths, which the Rust verifier expands (not formalized; the
differential test converts them).

The openings are leanVM's WHIR, which is not zero-knowledge: the protocol's zero knowledge assumes a
zero-knowledge PCS (`Security.lean`, `docs/membership/HIDING.md`).
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier PcsQuotient.Transcript

/-! ### Constants (`pcs_claim`) -/

/-- `VERSION`: the PCS version. -/
def pcsVersion : ℕ := 1

/-- `MIN_VARIABLES`, `MAX_VARIABLES`: the variables version `1` opens, WHIR's stacks of `2^15` to `2^28`
words. -/
def minVars : ℕ := 15
def maxVars : ℕ := 28

/-! ### Bytes and the out-of-domain point -/

/-- **`PCS_claim`** (`PcsClaim::encode`): `VERSION ‖ n ‖ root ‖ ood ‖ point ‖ value`, `n` the point's
length, each element `24` bytes (`elementBytes`). -/
def pcsClaimBytes (c : Commitment) (claim : Claim) : List UInt8 :=
  [pcsVersion.toUInt8, claim.point.length.toUInt8] ++ digestBytes c.root ++ elementBytes c.ood ++
    claim.point.flatMap elementBytes ++ elementBytes claim.value

/-- `OOD_TAG`: the ASCII bytes of `leanPCS-ood`. -/
def oodTag : List UInt8 := "leanPCS-ood".toUTF8.toList

/-- The input of the out-of-domain point's coordinate `j` (`ood_point`): `OOD_TAG ‖ VERSION ‖ n ‖ root ‖ j`,
one byte each but the root (`46` bytes). -/
def oodInput (n : ℕ) (root : Digest) (j : ℕ) : List UInt8 :=
  oodTag ++ [pcsVersion.toUInt8, n.toUInt8] ++ digestBytes root ++ [j.toUInt8]

/-- **`element_of`**: the element `24` bytes encode, limbs `c2, c1, c0`, each big-endian. -/
def elementOf (bs : List UInt8) : E :=
  E.ofLimbs (K.ofLane (beWord bs 16)) (K.ofLane (beWord bs 8)) (K.ofLane (beWord bs 0))

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The out-of-domain point** of a root on `n` variables over `F` (`ood_point`): coordinate `j` the
element the low `24` bytes of `keccak256(oodInput n root j)` encode, `j = 0, …, n − 1`. -/
def oodPointWith (n : ℕ) (root : Digest) : m (List E) :=
  (List.range n).mapM fun j ↦ do
    return elementOf ((digestBytes (← keccak256With F (oodInput n root j))).drop 8)

end With

/-! ### Tables and commitments -/

/-- **A table's polynomial at a point** (`pcs_claim::evaluate`): `Σ_i f_i · eq(point, bits of i)`, coordinate
`0` the lowest bit (mumbai's `mleK`: one fold of adjacent entries per coordinate). -/
def tableEval (table : Array K) (point : List E) : E := LeanVM.Prover.mleK table point

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The WHIR commitment of a table** of `2^μ` words of `K` over `F`, at rate `1/2` (`pcs::whir::commit`):
the Merkle tree of Keccak-256 over `F` of the `64` lanes' codewords, leaf `p` the lanes' entries at `x_p`
(mumbai's `stackWordFast`, `buildTreeM`), `2^(μ − 6 + 1)` leaves. -/
def commitWith (μ : ℕ) (table : Array K) : m LeanVM.Prover.Tree :=
  LeanVM.Prover.buildTreeM F (μ - laneFold + logInvRate) (LeanVM.Prover.stackWordFast μ logInvRate table)

/-- **A table's commitment** over `F` (`commit_words`): its WHIR tree, and the commitment, the tree's root
with the table's polynomial at the root's out-of-domain point. -/
def commitmentWith (μ : ℕ) (table : Array K) : m (LeanVM.Prover.Tree × Commitment) := do
  let tree ← commitWith F μ table
  let z ← oodPointWith F μ tree.root
  return (tree, ⟨tree.root, tableEval table z⟩)

end With

/-! ### The opening check (`verify_claim`) -/

/-- **The opening's two stack claims** (`verify_claim`): `f(z) = ood`, then `f(point) = value`, each weight
`eq(·, x)` on the stack point `x` in the order of the table's variables (`eqEval`, the Rust's closure
`c·p + (1 + c)(1 + p) = 1 + c + p`). -/
def pcsStackClaims (z : List E) (c : Commitment) (claim : Claim) : List StackClaim :=
  [(fun x ↦ eqEval z x, c.ood), (fun x ↦ eqEval claim.point x, claim.value)]

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The opening's initial sponge** over `F` (`Transcript::new(proof, iv, PUBLIC_DIGEST)`): the permutation of
the IV, Keccak-256 over `F` of the claim's bytes, and the zero public digest. -/
def pcsSpongeWith (c : Commitment) (claim : Claim) : m Sponge := do
  let iv ← keccak256With F (pcsClaimBytes c claim)
  return ⟨← F (seedInput iv zeroDigest), []⟩

/-- **The opening check** of the claim `claim` on the commitment `c` over the permutation `F`
(`verify_claim`): the claim has `15 ≤ n ≤ 28` variables; from the opening's initial sponge, the proof's first
two scalars absorbed and required to be the commitment's root (leanVM's halves); the out-of-domain point of the
root; then mumbai's `verifyStackedOpening` of the two stack claims (one challenge `λ`, then `verifyWhir` at
rate `1/2`) run on the rest of the proof with the root as commitment `0`, its level-0 rows `64` words at
height `n − 6 + 1`; and nothing of the proof left unread (`Transcript::finish`). -/
def pcsOpeningWith (c : Commitment) (claim : Claim) (proof : Compile.Proof) : m Bool := do
  let n := claim.point.length
  if minVars ≤ n ∧ n ≤ maxVars then
    let sp ← pcsSpongeWith F c claim
    match proof.stream with
    | x0 :: x1 :: rest =>
      let sp ← absorb F sp x0 dsObserve
      let sp ← absorb F sp x1 dsObserve
      if digestOfScalars (x0, x1) = some c.root then
        let z ← oodPointWith F n c.root
        let program := verifyStackedOpening n logInvRate (pcsStackClaims z c claim)
        let height := n - laneFold + logInvRate
        match ← run F program ⟨sp, rest, proof.openings, [(c.root, height, 2 ^ laneFold)]⟩ with
        | some (_, s) => return s.stream.isEmpty && s.openings.isEmpty
        | none => return false
      else return false
    | _ => return false
  else return false

end With

end PcsQuotient

end
