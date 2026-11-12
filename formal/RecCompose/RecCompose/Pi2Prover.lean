-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Transcribed from `crates/leanvm/rec/src/pi2/prover.rs`
-- (`halves`, `public_scalars`, `frame_words`, `prove_with`, `h_on_v`, `quotient_on_extension`, `open`, `claims`;
-- `PI2.md` §3), π2v4 (main 7e6d353c) on the EIP draft's PCS claims; `mulX` is `crates/membership/quotient`'s
-- `protocol::mul_x`. The writer and the commitments are `formal/UniComplete`'s (`Wr`, `sendRoot`,
-- `sampleW`, `commitWithH`), the PCS claims' openings `formal/UniKeccakComplete`'s (`pcsProveH`) at a given
-- out-of-domain point (`Pi2PcsZ`'s `pcsProveZH`), the point `WhirBridge.Pcs.oodPointM` (`pcs_claim::ood_point`), the
-- transforms `formal/Statement`'s (`PcsQuotient.Domain.values`, `coefficients`).
import RecStatement
import RecPiop
import RecCircuit.Piop
import RecCircuit.Check
import UniKeccakComplete.K.Prover
import UniKeccakComplete.K.PcsProver
import UniKeccakComplete.K.AlgHPoly
import WhirBridge.PcsClaim
import RecCompose.Pi2PcsZ

/-!
# π2's honest prover

`prover.rs`, phase by phase, over a Keccak-256 `H` (and the permutation `F` for WHIR's proofs of work), for any
circuit as π2's PIOP reads it (`RecPiop.Circuit E`: positions, roles, blocks, `σ`, `κ`, ports; the compiled circuit's
`toPiop` at the deployment):

1. **the public values** (`PublicValue`), each as its read takes it (`sendInteger`, `sendRoot` of `halvesOf`, `sendScalar`,
   `narrowWire`: 20 bytes; a frame word `.word` is not in the stream: the seed hashes it, `frameWordsOf`);
2. **`W`**: the witness's basis-`B` coefficients (`bCoefficients`), the leading words of `W`'s stack (`padStack`, zeros
   to `2^vars` words, `vars` of `stackVars`), committed (`commitWithH`), its out-of-domain point (`oodPt vars root`,
   a parameter: `ood_point(n, root)`, `n` Keccak-256 calls, `WhirBridge.Pcs.oodPointM H` in `pi2ProverWith`), its
   root's bytes (`rootHalves`) and its out-of-domain answer (`pi2OodAt`: the stack's multilinear extension at the
   point); `α, β, γ`;
3. **`h` and `P` on `V_m`** (`hValues`, `pColumn`): `h = (1 + 1_S)(1/(α + w_i + β ω_i) + 1/(α + P_v + κ + β ω_{σ_i}))`,
   zero at a hole, and `P_v = pushV + κ` (a pair's formula of its row, the position's own value at a forward and a hole,
   limb `0`); their novel coefficients;
4. **`q` and `q_P` on the extension coset** `D = β_{m+1} + V_{m+1}` (`qValues`, `qpValues`, `2N` points, disjoint from
   `V_m`): `w`, `σ`, `κ`, `h`, `P` by the transform (`onCoset`), the row's cells `w(x + ω_c)` (index `p ⊕ c`), each pair's
   indicator, `P_v` (`pvAtCoset`), the ports' `T = Σ I_p (E_p + Φ_k)` (`tAtCoset`, `Φ` the verifier's `phiAt`),
   `d_pull`, `d_push = α + P + κ + βσ`, `q = (h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T) / Z_V` and
   `q_P = (P + P_v) / Z_V`; their novel coefficients (`coefficients` at `D`'s offset);
5. **`Q`**: the plain stack of sixteen slots of `N` (`qEntry`: slot `b_0 + 2 b_1 + 4 limb`: for limbs `0, 1, 2`
   `H = x h` (`mulX` of `h`'s novel coefficients, its top one, zero for a witness, dropped) at `(0, 0)`, `q`'s two
   digits at `(1, 0)`, `(0, 1)`, `G` zero at `(1, 1)`; at limb code `3` `P`, `q_P`'s two digits, `S` zero: slots
   `3, 7, 11, 15` zero, `emptySlots`), zeros to `2^vars` words, committed, its point, its root's bytes and its
   answer; `t`;
6. **the values at `t`**: the `2^r` fold values (`foldValues`), `ξ = κ(t) + β σ(t)` (`xiOf`, PI2.md §9) and
   `s = P(t)` (`sOf`); `ρ`.

`pi2ProveWith` adds the seed `keccak(NAME ‖ IV ‖ public input ‖ frame words)` and the four PCS claims' openings
(`pcsProveZH`, one per claim: `W`'s, the setup's, `Q`'s identity and pushes' claims, in the contract's order, each a point of its
whole stack; `W`'s and `Q`'s at the points the stream's run asked, the setup's at the deployed `oodPoint`, as the
contract reads them: `RecStatement.pcsOpenWords`), the claims the verifier's arithmetic on the prover's own inputs
(`CoreSpec.run`, which the verifier's run on the stream reproduces); `none` if a proof of work fails.

Decisions: the prover is mathematical, not vectorised: one value per point, the indicators by their products (no
batched inversion); the kinds of read and value that do not match are skipped (the Rust panics). Every function here is
computable (the differential test runs it, `RecComposeTest/Pi2Prover.lean`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash Finset

/-! ## The public values -/

/-- **A public value** as the stream carries it (`PublicValue`): an integer, 32 bytes as they are (π1's roots as
the claims' root words), an element of `E` (read whole or narrow), or a frame word (`Read.frame`: not in the stream,
hashed by the seed). -/
inductive PublicValue where
  | integer (x : ℕ)
  | root (bytes : List UInt8)
  | scalar (x : E)
  | word (bytes : List UInt8)
  deriving Inhabited

/-- **`halves(bytes)`**: the two scalars `next_root` reads from 32 bytes, each 16-byte half big-endian limbs `1, 0`. -/
def halvesOf (b : List UInt8) : E × E :=
  (UniStatement.eNew (UniStatement.beWordAt b.toArray 8) (UniStatement.beWordAt b.toArray 0) 0,
    UniStatement.eNew (UniStatement.beWordAt b.toArray 24) (UniStatement.beWordAt b.toArray 16) 0)

/-- A public value's scalars (`public_scalars`' arms). -/
def PublicValue.scalars : PublicValue → List E
  | .integer x => [UniStatement.eK (UInt64.ofNat x)]
  | .root b => [(halvesOf b).1, (halvesOf b).2]
  | .scalar x => [x]
  | .word b => UniStatement.publicWordsOf b

/-- **`frame_words(values)`**: the frame words among the values, in order, as the seed hashes them. -/
def frameWordsOf (values : List PublicValue) : List UInt8 :=
  values.flatMap fun v ↦ match v with
    | .word b => b
    | _ => []

/-- **`public_scalars(public_input, values)`**: the public input's four words, then the values'. -/
def publicScalarsOf (input : List UInt8) (values : List PublicValue) : List E :=
  UniStatement.publicWordsOf input ++ values.flatMap PublicValue.scalars

/-- A narrow element's 20 bytes (`send_narrow`): its scalar's 24 bytes without the first four (`c2 < 2^32`). -/
def narrowWire (x : E) : List UInt8 := (UniComplete.scalarWire x).drop 4

section Send

variable {m : Type → Type} [Monad m]

/-- **A public value's bytes** as its read takes it (`send_integer`, `send_root(halves)`, `send`, `send_narrow`; a
frame word, and a value of another kind than its read, nothing: the Rust panics on the latter). -/
def publicBytes : Read × PublicValue → List UInt8
  | (.integer b, .integer x) => UniComplete.integerWire x b
  | (.root, .root bytes) => UniStatement.rootWord (halvesOf bytes)
  | (.scalar, .scalar x) => UniComplete.scalarWire x
  | (.narrow, .scalar x) => narrowWire x
  | _ => []

/-- **The public values written**, in order (`publicBytes` each). -/
def sendPublic (ps : List (Read × PublicValue)) : UniComplete.WrM m Unit :=
  UniComplete.sendBytes (ps.flatMap publicBytes)

end Send

/-! ## The tables -/

/-- **A stack of `2^vars` words** (`pcs_claim::commit_words`' zero padding): the table's words, then zeros. -/
def padStack (vars : ℕ) (T : ℕ → K) : Array K := Array.ofFn (n := 2 ^ vars) fun p ↦ T p.val

section Honest

variable (G : RecPiop.Circuit E) (w : ℕ → K)

/-- The witness's values, in `K` (`2^m` of them). -/
def wValues : Array K := Array.ofFn (n := G.N) fun i ↦ w i.val

/-- **`W`'s table**: the witness's basis-`B` coefficients (`b_coefficients` of its novel ones). -/
def wTableB : Array K := UniStatement.bCoefficients G.logN (wValues G w)

/-- **`P_v` at position `i`** (`h_on_v`'s `p`): `pushV + κ`, a pair's formula of its row, the position's own value at a
forward and at a hole. -/
def pvValue (i : ℕ) : E := G.pushV (RecCircuit.emb w) i + G.kappa i

/-- **`P`'s column on `V_m`**: `P_v`'s limb `0` (`P_v` is in `K` for a witness). -/
def pColumn : Array K := Array.ofFn (n := G.N) fun i ↦ (pvValue G w i.val).limb 0

/-- **`h` on `V_m`** (`h_on_v`): `(1 + 1_S)(1/d_pull + 1/d_push)`, `d_pull = α + w_i + β ω_i`,
`d_push = α + P_v + κ + β ω_{σ_i}`: zero at a hole. -/
def hValues (α β : E) : Array E :=
  Array.ofFn (n := G.N) fun i ↦
    if (G.role i.val).isPort then 0 else
      (α + ofK (w i.val) + β * UniStatement.pointE i.val)⁻¹ +
        (α + G.pushV (RecCircuit.emb w) i.val + β * UniStatement.pointE (G.sigma i.val))⁻¹

/-- `σ`'s points on `V_m`. -/
def sigmaValues : Array E := Array.ofFn (n := G.N) fun i ↦ UniStatement.pointE (G.sigma i.val)

/-- `κ` on `V_m`. -/
def kappaValues : Array E := Array.ofFn (n := G.N) fun i ↦ G.kappa i.val

/-- **The extension coset's offset** `β_{m+1}` (`extension_offset`). -/
def cosetOffset (m : ℕ) : K := UniStatement.beta.getD (m + 1) 0

/-- The coset's point `p`: `β_{m+1} + B(p)`. -/
def cosetPoint (m p : ℕ) : E := ofK (cosetOffset m + PcsQuotient.Domain.point p)

/-- **Novel coefficients' polynomial on the coset** (`on_extension`): `2N` values, the coefficients padded with zeros. -/
def onCoset (m : ℕ) (c : Array E) : Array E :=
  PcsQuotient.Domain.values (m + 1) (cosetOffset m) (Array.ofFn (n := 2 ^ (m + 1)) fun i ↦ c.getD i.val 0)

/-- `Z_V(x) = w_m(x)`. -/
def zvAt (m : ℕ) (x : E) : E := (fun y ↦ y * y + y)^[m] x

/-- **The pairs as a list** (`G.pairs`' elements, each once): every non-forward role of every block. -/
def pairsList : List (RecPiop.Block × ℕ) :=
  (G.blocks.dedup ×ˢ List.range G.W).filter fun p ↦ !(G.regionRole p.1 p.2).isForward

/-- **Each pair's data, once** (`spec.pairs`): the pair, its indicator's constant `Π_{j ∉ p} (ω_{c_p} + ω_j)`, its
positions. -/
def pairData : List ((RecPiop.Block × ℕ) × E × List ℕ) :=
  (pairsList G).map fun q ↦
    (q, ∏ j ∈ G.compl q, (UniStatement.pointE (G.pairBase q) + UniStatement.pointE j),
      (List.range G.N).filter fun j ↦ decide (G.InPair q j))

/-- A pair's indicator at `x` from its data: `Z_V(x) / (c · Π_{j ∈ p} (x + ω_j))`. -/
def indFrom (m : ℕ) (c : E) (pos : List ℕ) (x : E) : E :=
  zvAt m x * (c * (pos.map fun j ↦ x + UniStatement.pointE j).prod)⁻¹

/-- **A pair's formula at coset point `p`**, from `w` on the coset: the cells `w(x + ω_c)` at `p ⊕ c`. -/
def formulaAtCoset (d : (RecPiop.Block × ℕ) × E × List ℕ) (wD : Array E) (γ : E) (p : ℕ) : E :=
  (G.regionRole d.1.1 d.1.2).value γ (wD.getD p 0) (fun c ↦ wD.getD (p ^^^ (d.1.2 ^^^ c)) 0)

/-- **`P_v` at coset point `p`** (`w + Σ_{internal p} I_p (E_p + w)`). -/
def pvAtCoset (pd : List ((RecPiop.Block × ℕ) × E × List ℕ)) (m : ℕ) (wD : Array E) (γ : E) (p : ℕ) : E :=
  wD.getD p 0 + ((pd.filter fun d ↦ !(G.regionRole d.1.1 d.1.2).isPort).map fun d ↦
    indFrom m d.2.1 d.2.2 (cosetPoint m p) * (formulaAtCoset G d wD γ p + wD.getD p 0)).sum

/-- **The ports' `T` at coset point `p`** (`Σ_{port p} I_p (E_p + Φ_k)`, `Φ` given). -/
def tAtCoset (pd : List ((RecPiop.Block × ℕ) × E × List ℕ)) (m : ℕ) (wD : Array E) (γ : E) (phi : E → ℕ → E)
    (p : ℕ) : E :=
  ((pd.filter fun d ↦ (G.regionRole d.1.1 d.1.2).isPort).map fun d ↦
    indFrom m d.2.1 d.2.2 (cosetPoint m p) * (formulaAtCoset G d wD γ p + phi (cosetPoint m p) d.1.2)).sum

/-- **The holes' indicator at coset point `p`** (`1_S`): the port pairs' indicators. -/
def holeAtCoset (pd : List ((RecPiop.Block × ℕ) × E × List ℕ)) (m p : ℕ) : E :=
  ((pd.filter fun d ↦ (G.regionRole d.1.1 d.1.2).isPort).map fun d ↦ indFrom m d.2.1 d.2.2 (cosetPoint m p)).sum

/-- **`h`'s novel coefficients** (`2^m`). -/
def hNovel (α β : E) : Array E := UniComplete.novelOfValuesE G.logN (hValues G w α β)

/-- **`P`'s novel coefficients** (`2^m`, in `K`). -/
def pNovel : Array K := PcsQuotient.Domain.coefficients G.logN 0 (pColumn G w)

/-- **`q` on the extension coset** (`quotient_on_extension`):
`(h d_pull d_push + (1 + 1_S)(d_push + d_pull) + T) / Z_V`, `d_push = α + P + κ + βσ`. -/
def qValues (α β γ : E) (phi : E → ℕ → E) : Array E :=
  let m := G.logN
  let wD := onCoset m (UniComplete.novelOfValuesK m (wValues G w))
  let σD := onCoset m (UniComplete.novelOfValuesE m (sigmaValues G))
  let κD := onCoset m (UniComplete.novelOfValuesE m (kappaValues G))
  let hD := onCoset m (hNovel G w α β)
  let pD := onCoset m ((pNovel G w).map ofK)
  let pd := pairData G
  Array.ofFn (n := 2 ^ (m + 1)) fun p ↦
    let x := cosetPoint m p.val
    let dPull := α + wD.getD p.val 0 + β * x
    let dPush := α + pD.getD p.val 0 + κD.getD p.val 0 + β * σD.getD p.val 0
    (hD.getD p.val 0 * dPull * dPush + (1 + holeAtCoset G pd m p.val) * (dPush + dPull) +
      tAtCoset G pd m wD γ phi p.val) * (zvAt m x)⁻¹

/-- **`q_P` on the extension coset**: `(P + P_v) / Z_V`. -/
def qpValues (γ : E) : Array E :=
  let m := G.logN
  let wD := onCoset m (UniComplete.novelOfValuesK m (wValues G w))
  let pD := onCoset m ((pNovel G w).map ofK)
  Array.ofFn (n := 2 ^ (m + 1)) fun p ↦
    (pD.getD p.val 0 + pvAtCoset G (pairData G) m wD γ p.val) * (zvAt m (cosetPoint m p.val))⁻¹

/-- **`q`'s novel coefficients** (`2N`): the transform at the coset's offset. -/
def qNovel (α β γ : E) (phi : E → ℕ → E) : Array E :=
  PcsQuotient.Domain.coefficients (G.logN + 1) (cosetOffset G.logN) (qValues G w α β γ phi)

/-- **`q_P`'s novel coefficients** (`2N`, in `K`: the transform of its values' limb `0`, `q_P` being in `K` for a
witness). -/
def qpNovel (γ : E) : Array K :=
  PcsQuotient.Domain.coefficients (G.logN + 1) (cosetOffset G.logN) ((qpValues G w γ).map fun x ↦ x.limb 0)

/-- Limb `l` of an element of `E` (`0` past the third). -/
def limbN (x : E) (l : ℕ) : K := if h : l < 3 then x.limb ⟨l, h⟩ else 0

/-- `low(j)`, the lowest power of two in `j > 0` (`0` at `0`). -/
def lowBit : ℕ → ℕ
  | 0 => 0
  | j + 1 => if (j + 1) % 2 = 1 then 1 else 2 * lowBit ((j + 1) / 2)

/-- **`mul_x`** (`quotient::protocol::mul_x`): `x F` in the novel basis, `F` of `f.size` (a power of two) coefficients:
the product's first `f.size` coefficients, coefficient `0` zero and coefficient `j ≥ 1` `f[j − 1] + f[j + low(j) − 1]`
(`x X_{j−1} = …`; `F`'s top coefficient, the product's coefficient `f.size`, dropped). -/
def mulX (f : Array E) : Array E :=
  Array.ofFn (n := f.size) fun j ↦
    if j.val = 0 then 0 else f.getD (j.val - 1) 0 + f.getD (j.val + lowBit j.val - 1) 0

/-- **`Q`'s table** (sixteen slots of `2^m`, `verifier::QUOTIENT_SLOTS`): entry `pos + 2^m (b + 4 limb)`, `pos < 2^m`,
`b = b_0 + 2 b_1`: at limbs `0, 1, 2`, `H`'s (`b = 0`, `hxN` its novel coefficients) or `q`'s (`b = 1, 2`: its
coefficient `pos`, `2^m + pos`) novel coefficient, that limb, `G` zero (`b = 3`); at limb code `3`, `P`'s coefficient
(`b = 0`), `q_P`'s (`b = 1, 2`), `S` zero (`b = 3`); zero past the sixteen slots. -/
def qEntry (m : ℕ) (hxN qN : Array E) (pN qpN : Array K) (i : ℕ) : K :=
  let pos := i % 2 ^ m
  let slot := i / 2 ^ m
  let b := slot % 4
  let limb := slot / 4
  if limb < 3 then
    (if b = 0 then limbN (hxN.getD pos 0) limb
      else if b = 1 then limbN (qN.getD pos 0) limb
      else if b = 2 then limbN (qN.getD (2 ^ m + pos) 0) limb
      else 0)
  else if limb = 3 then
    (if b = 0 then pN.getD pos 0
      else if b = 1 then qpN.getD pos 0
      else if b = 2 then qpN.getD (2 ^ m + pos) 0
      else 0)
  else 0

/-- **The fold values at `t`** (`folds`): `a_k = Σ_j eq(j; w_r(t), …, w_{m−1}(t)) T_{k + 2^r j}`, `k < 2^r`. -/
def foldValues (m r : ℕ) (T : Array K) (t : E) : List E :=
  (List.range (2 ^ r)).map fun k ↦
    ∑ j ∈ range (2 ^ (m - r)), ofK (T.getD (k + 2 ^ r * j) 0) *
      ∏ l ∈ range (m - r), if j.testBit l then (digitsList t (m + 3)).getD (r + l) 0
        else 1 + (digitsList t (m + 3)).getD (r + l) 0

/-- **`ξ = κ(t) + β σ(t)`** from the setup's halves `κ` and `κ + σ` (`mle_eval` at `w_0(t), …, w_{m−1}(t)`). -/
def xiOf (m : ℕ) (setupStack : Array K) (β t : E) : E :=
  let pt := (digitsList t (m + 3)).take m
  let kappaT := UniStatement.multilinearEval ((setupStack.extract 0 (2 ^ m)).toList.map ofK) pt
  let sumT := UniStatement.multilinearEval ((setupStack.extract (2 ^ m) (2 * 2 ^ m)).toList.map ofK) pt
  kappaT + β * (kappaT + sumT)

/-- **`s = P(t)`** from `P`'s novel coefficients: `Σ_k P_k Π_{l : k_l = 1} w_l(t)`. -/
def sOf (m : ℕ) (pN : Array K) (t : E) : E :=
  ∑ k ∈ range (2 ^ m), ofK (pN.getD k 0) *
    ∏ l ∈ range m, if k.testBit l then (digitsList t (m + 3)).getD l 0 else 1

/-- **The ports' `Φ_k(x)`** the prover uses: the verifier's (`phiAt`) at the public scalars. -/
def phiOn (S : CoreSpec E) (pubs : List E) (γ : E) (x : E) (k : ℕ) : E :=
  phiAt S (powersList γ (S.maxGamma + 1)) pubs x k

end Honest

/-! ## The prover -/

/-- **What the prover leaves**: the stream, `W`'s and `Q`'s stacks and trees, the inputs of the verifier's
arithmetic (its public scalars, challenges and values), and `W`'s and `Q`'s out-of-domain points. -/
structure Pi2Out where
  stream : Array UInt8
  wStack : Array K
  wTree : LeanVM.Prover.Tree
  qStack : Array K
  qTree : LeanVM.Prover.Tree
  inputs : Inputs E
  wPoint : List E
  qPoint : List E

/-- **The out-of-domain answer** at the point `z` (`pcs_claim::commit_words`' `ood`): the stack's multilinear
extension there, bit `0` of an index the first coordinate (`UniComplete.stackEval`). -/
def pi2OodAt (stack : Array K) (z : List E) : E := UniStatement.multilinearEval (stack.toList.map ofK) z

theorem pi2OodAt_eq (stack : Array K) (z : List E) : pi2OodAt stack z = UniComplete.stackEval stack z := rfl

/-- **A pure point function** as the prover's point parameter. -/
abbrev pureZ {m : Type → Type} [Monad m] (zf : ℕ → Digest → List E) : ℕ → Digest → m (List E) :=
  fun n r ↦ pure (zf n r)

/-- **The out-of-domain point at a Keccak-256 function `Hk`** (`WhirBridge.Pcs.oodPointWith`): what
`WhirBridge.Pcs.oodPointM` computes at `Pure.pure ∘ Hk`. -/
def pi2Z (Hk : List UInt8 → Digest) (n : ℕ) (r : Digest) : List E := (WhirBridge.Pcs.oodPointWith Hk n r).toList

/-- **`oodPointM` at a pure Keccak-256** is the pure point function `pi2Z`. -/
theorem oodPointM_id_eq (Hk : List UInt8 → Digest) :
    WhirBridge.Pcs.oodPointM (m := Id) (Pure.pure ∘ Hk) = pureZ (m := Id) (pi2Z Hk) := by
  funext n r
  exact PcsZ.oodPointM_id Hk n r

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **The prover's stream** (`prove_with`), from the seed: the public values, `W` (its point `oodPt n root`, its root,
its out-of-domain answer `pi2OodAt stack point`) and `α, β, γ`, `Q` (its point, its root, its answer) and `t`, the
values at `t` (`a`, `ξ`, `s`) and `ρ`. -/
def pi2ProveStreamWith (G : RecPiop.Circuit E) (S : CoreSpec E) (oodPt : ℕ → Digest → m (List E))
    (reads : List Read) (setupStack : Array K) (input : List UInt8) (values : List PublicValue) (w : ℕ → K) :
    UniComplete.WrM m Pi2Out := do
  let n := G.logN
  let wv := (stackVars n).1
  let qv := (stackVars n).2.1
  sendPublic (reads.zip values)
  let pubs := publicScalarsOf input values
  -- W
  let tb := wTableB G w
  let wStack := padStack wv fun i ↦ tb.getD i 0
  let wTree ← (StateT.lift (E2ECompleteness.commitWithH H wv wStack) : UniComplete.WrM m LeanVM.Prover.Tree)
  let wz ← (StateT.lift (oodPt wv wTree.root) : UniComplete.WrM m (List E))
  UniComplete.sendRoot (UniStatement.rootHalves wTree.root)
  UniComplete.sendScalar (pi2OodAt wStack wz)
  let α ← UniComplete.sampleW H
  let β ← UniComplete.sampleW H
  let γ ← UniComplete.sampleW H
  -- Q
  let hxN := mulX (hNovel G w α β)
  let qN := qNovel G w α β γ (phiOn S pubs γ)
  let pN := pNovel G w
  let qpN := qpNovel G w γ
  let qStack := padStack qv (qEntry n hxN qN pN qpN)
  let qTree ← (StateT.lift (E2ECompleteness.commitWithH H qv qStack) : UniComplete.WrM m LeanVM.Prover.Tree)
  let qz ← (StateT.lift (oodPt qv qTree.root) : UniComplete.WrM m (List E))
  UniComplete.sendRoot (UniStatement.rootHalves qTree.root)
  UniComplete.sendScalar (pi2OodAt qStack qz)
  let t ← UniComplete.sampleW H
  -- the values at t
  let a := foldValues n G.logW tb t
  let ξ := xiOf n setupStack β t
  let s := sOf n pN t
  UniComplete.sendScalars (a ++ [ξ, s])
  let ρ ← UniComplete.sampleW H
  let c ← get
  return ⟨c.stream, wStack, wTree, qStack, qTree, ⟨pubs, α, β, γ, t, a, ξ, s, ρ⟩, wz, qz⟩

/-- **The four opening proofs** of π2's claims, in the contract's order (`claims`): `W`'s, the setup's, `Q`'s identity
and pushes' claims. -/
structure Pi2Openings where
  w : Compile.Proof
  setup : Compile.Proof
  qId : Compile.Proof
  qPush : Compile.Proof

/-- **π2's honest prover** over `H`, `F` (`prove_with`, then `open`): the seed `keccak(NAME ‖ IV ‖ public input ‖
frame words)` (`frameWordsOf values`), the stream (`W`'s and `Q`'s out-of-domain points by `oodPt`), then the four PCS
claims' openings (`pcsProveZH`, one per claim, in the contract's order: `W`'s, the setup's, `Q`'s identity and pushes'
claims; `W`'s and `Q`'s at the
points the stream asked, the setup's at the deployed `oodPoint`, `pcsZ`), at the claims of the verifier's arithmetic
(`CoreSpec.run` of the circuit's view) on the prover's inputs, each on its commitment's whole stack (`stackVars`; the
setup's table `setupStack` and its tree given, the table padded with zeros to its stack, `padStack`); the stream and
the four proofs, or `none` if a proof of work fails. -/
def pi2ProveWith (fuel : ℕ) (G : RecPiop.Circuit E) (oodPt : ℕ → Digest → m (List E)) (view : Circuit)
    (setupStack : Array K) (setupTree : LeanVM.Prover.Tree) (iv input : List UInt8) (values : List PublicValue)
    (w : ℕ → K) : m (Option (Array UInt8 × Pi2Openings)) := do
  let seed ← H (RecStatement.name ++ iv ++ input ++ frameWordsOf values)
  let (out, _) ← (pi2ProveStreamWith H G (Spec.of view).core oodPt view.reads setupStack input values w).run
    (UniComplete.Wr.start seed)
  let o := (Spec.of view).core.run out.inputs
  let wv := (stackVars G.logN).1
  let qv := (stackVars G.logN).2.1
  let sv := (stackVars G.logN).2.2
  let pW ← PcsZ.pcsProveZH H F fuel wv out.wPoint out.wTree out.wStack o.witnessPoint o.fold
  let pS ← PcsZ.pcsProveZH H F fuel sv (UniKeccakComplete.pcsZ sv setupTree.root) setupTree
    (padStack sv fun i ↦ setupStack.getD i 0) o.setupPoint out.inputs.ξ
  let pQ1 ← PcsZ.pcsProveZH H F fuel qv out.qPoint out.qTree out.qStack o.quotientPoint o.quotientValue
  let pQ2 ← PcsZ.pcsProveZH H F fuel qv out.qPoint out.qTree out.qStack o.pushesPoint o.pushesValue
  return do
    let a ← pW
    let b ← pS
    let c ← pQ1
    let d ← pQ2
    pure (out.stream, ⟨a, b, c, d⟩)

end With

/-- **The deployed out-of-domain answer** (`pcs_claim::commit_words`' `ood`): the stack's multilinear polynomial at the
root's out-of-domain point (`WhirBridge.Pcs.oodPoint`, `ood_point`), bit `0` of an index the first coordinate: the PCS
prover's `UniKeccakComplete.pcsOod n stack root` (`pi2Ood_eq`), `pi2OodAt` at `pi2Z keccak256`. -/
def pi2Ood (n : ℕ) (root : Digest) (stack : Array K) : E :=
  UniStatement.multilinearEval (stack.toList.map ofK) (WhirBridge.Pcs.oodPoint n root).toList

theorem pi2Ood_eq (n : ℕ) (root : Digest) (stack : Array K) :
    pi2Ood n root stack = UniKeccakComplete.pcsOod n stack root := rfl

end RecCompose
