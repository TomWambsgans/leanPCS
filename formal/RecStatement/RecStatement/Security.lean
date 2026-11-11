-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The model, the experiments' shape and the form of the
-- statements are `formal/UniStatement`'s and `formal/UniKeccak`'s (`Security.lean`, after `formal/Statement`'s
-- `PcsQuotient.Security` and leanerVM `mumbai` 6175f1a0's `Statement/LeanVm.lean`, MIT OR Apache-2.0); the relation is
-- the Keccak VM's (`formal/KeccakVm`, `KvHolds`, through `UniKeccak.KDeployment.Relation`); the Keccak π1-rec3's
-- recorded graph and its merge hazard are `formal/RecGraphKeccak`'s. Transcribed from
-- `crates/leanvm/rec/src/pi2/circuit.rs` (`Circuit::digest`), `prover.rs` (`Setup::new`, `iv`) and `contract.rs`
-- (`claim_words`, `claim_of_words`: the eight PCS claims); a claim's opening is `formal/WhirBridge`'s transcription of
-- `crates/pcs_claim`'s `verify_claim` (`WhirBridge.Pcs.pcsVerifyWithHash`, through `UniKeccak.pcsOpenK`, and
-- `WhirBridge.Pcs.pcsVerifyWithHashO`, the out-of-domain point computed over `F`, through `pcsOpenKO`).
import RecStatement.Calls
import WhirBridge.PcsUnionOracle
import RecStatement.Data
import UniKeccak.Security
import RecGraphKeccak.Main
import RecGraphKeccak.Emitted
import RecCircuit.Sound
import KeccakFlock.Complete

/-!
# The recursive verifier's end statements, against the Keccak VM's relation

Statements only, no proof (the composition proves them). The recursion's inner proof π1 is the Keccak VM's verifier
(`formal/UniKeccak`, leanVM 9d50c92a3's Keccak VM) at π1-rec3's Fiat–Shamir shape (`UniKeccak.keccakRec3`) and the
point-claim ABI; π2's verifier, circuit, setup and openings are generic in π2's circuit (`Core`, `Spec`, `Verifier`,
`Calls`).

**Two models, which do not compose formally.** π2's circuit computes π1-rec3's Fiat–Shamir challenges with the
**real Keccak-f[1600]**: a circuit is a fixed function (`RecCircuit.compile_sound`, `keccak_out`; for the Keccak
π1-rec3's graph `RecGraphKeccak.pi1rec3K_end`: its ports carry `RecGraph.evalNodes` over Keccak-f[1600]).
π1-rec3's knowledge soundness is proved in the **random-permutation model**
(`UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_closed`: error `uniBound128 (2^35/|E|) Q`, at most `2^-64` for
`Q ≤ 2^64`). No circuit computes a random permutation, so the
statements come in two parts, as the earlier proofs' caveat says (AGENTS.md: "the theorems are in the
random-permutation model and do not formally compose with the EVM one, which holds at the real Keccak-f[1600]"):

1. **π2's part, in the random-permutation model** (`RecKnowledgeSoundness2`, `RecCompleteness2`): one random
   permutation `π` for π2's own Fiat–Shamir (the contract's transcript and IV), the circuit's digest, the WHIR
   commitments and the eight openings. If the contract accepts, π2's explicit extractor (`recExtractor2`) outputs
   π1's stream `s` on which **the Keccak π1-rec3's recorded graph, run with Keccak-f[1600]**, accepts, its three
   claims being the contract's (which the block proved) (`Pi1GraphAccepts`); but with probability `ε2 Q`.
2. **End to end, against the Keccak VM's `KvHolds`, as an explicit reduction** (`RecKnowledgeSoundnessReduction`,
   `Reduction.lean`): for every adversary `A` of `Q` queries against the recursive verifier, the end-to-end
   extractor fails while the contract accepts with probability at most `ε2 Q` plus the probabilities that two
   **explicit derived adversaries** (`pi1Adversary A`, `hazardAdversary A`: they run `A`, then π2's extractor, and make
   `A`'s `Q` queries) break π1-rec3 at Keccak-f[1600] (`pi1KeccakSoundnessExperiment`) and hit the merge hazard on a
   stream π1-rec3's graph accepts (`pi1HazardExperiment`, `Pi1HazardAccepted`). No Fiat–Shamir hypothesis: the reader
   applies the Fiat–Shamir heuristic for Keccak-f[1600] to these two adversaries, which run in `A`'s time plus π2's
   extractor's.
3. **The end-to-end corollaries, against the Keccak VM's `KvHolds`** (`RecKnowledgeSoundness`, `RecCompleteness`),
   under named hypotheses about π1-rec3 **at Keccak-f[1600]**:
   * `Pi1FsKeccak ε1`: π1-rec3 is knowledge sound with its Fiat–Shamir instantiated by Keccak-f[1600] (its openings
     and commitments over `π`), error `ε1 Q`. Its motivation is π1-rec3's random-permutation theorem
     (`uniKnowledgeSoundnessKeccakRec3_closed`). **As stated it is false**: it quantifies over every adversary, and
     charges only calls of `π`, so an adversary grinds π1's Keccak-f[1600] challenges offline for free.
     It is the Fiat–Shamir heuristic **for adversaries of bounded Keccak-f[1600] work**, which Lean does not
     model; the reduction form (2) does not need it.
   * `Pi1HazardKeccak εh`: π1-rec3's run at Keccak-f[1600] avoids the merge hazard on the streams its graph accepts
     (`Pi1HazardAccepted`: `RecGraphKeccak.MergeHazardK`, the run drawing `t` (challenge 52) and `t` a root of
     `Z_bad(p_0)`, where the recorded graph merges by symbol what the verifier merges by value), but with probability
     `εh Q`; motivated by `RecGraphKeccak.hazard_probK` (`2^16/|E|` a challenge) for random challenges. False as
     stated for the same reason (an unbounded adversary grinds `t`); the same heuristic for bounded adversaries.
   * `RecGraphKeccak.Pi1GraphIsVerifierK`: off the hazard, the recorded graph is the Keccak π1-rec3's verifier
     (RecGraphKeccak's target, proved: `RecGraphKeccak.Sim.pi1GraphIsVerifierK`).

   The conclusion's error is `ε2 + ε1 + εh`. Completeness likewise: π2's completeness is over its own coins and `π`
   (`RecCompleteness2`); π1-rec3's completeness at Keccak-f[1600] is the named hypothesis `Pi1CompletenessKeccak δ1`
   (its random-permutation analogue is `UniKeccak.UniCompletenessKeccakRec3`, a statement: no proof of it is used
   here), its honest proofs off the hazard `Pi1HazardKeccakHonest δh` (motivated only by
   `RecGraphKeccak.hazard_probK`, a count for a uniform `t`; its random-permutation reading is not proved).

**The recursive verifier** (`RecDeployment.contractWith`) is the contract (`pi2::contract`): π2's verifier on the
calldata (`runWith`: the public input, then the stream with π1's roots and claims' elements, `W`'s and `Q`'s roots and
out-of-domain answers and the 18 values), then **eight declared claims**, each the EIP draft's PCS claim (`crates/pcs_claim`:
a root, its out-of-domain answer, one point, a value), decoded from its words (`claimOfWords`: every element's top 64
bits zero) and opened by `crates/pcs_claim`'s `verify_claim` on the point's length (`pcsOpenWords`): **π1's three**
(`C1`, `C2`, π1's setup `F`; their points the coordinates the contract derives from π1-rec3's pair challenges, `F`'s
commitment the setup's; `2^27`, `2^26`, `2^23` words) and **π2's five** (`W`, the setup, `Q`'s identity, pushes' and
sum claims; `2^24`, `2^25`, `2^28` words). **The out-of-domain point.** `verify_claim` derives each claim's point from
its root with Keccak-256 (`ood_point`). π2's five claims are opened by `pcsOpenKO` (`WhirBridge.Pcs.pcsVerifyWithHashO`):
the verifier computes the point over `F` (`keccak256With F`, `n` calls at `oodInput n root j`), so in the
random-permutation model it is read off the permutation, which `Q`'s three claims on one commitment need (the
out-of-domain answer binds the root: `WhirBridge.Pcs.ood_binding_coords`). π1's three keep `UniKeccak.pcsOpenK`
(`WhirBridge.Pcs.pcsVerifyWithHash` at the fixed `WhirBridge.Pcs.oodPoint`, Keccak-256 itself), as π1's own verifier
and theorems take it (one claim per commitment: no binding needed). The two are told apart by the claim's size
(`pi2Size`: `24`, `25`, `28`; π1's are `27`, `26`, `23`). **At the real Keccak-f[1600] both points are the deployed
`ood_point`** (`pcsOpenKO_keccakF1600`: `pcsOpenKO` over Keccak-f[1600] is `UniKeccak.pcsOpenK`). π1's verifier itself never runs: π2 proves its graph accepted. The deployed EVM bytecode is linked to this
model **by transcription and test**, not by a Lean proof (unlike the membership verifier's
`Evm.evm_accepts_iff_verifyWith`): `contract.rs`'s parity tests (`parity`, `parity_deployable`). The deployed contract
hard-codes π2's IV (`inst.iv`, the Rust's from its digest and setup commitment); `RecDeployment.Real` pins those
(`Data.digest`, `Data.setupRoot`) at π1's reference IV (`Data.pi1Iv`).

**The deployment** (`RecDeployment`): π1's (`UniKeccak.KDeployment`: the Keccak VM's program, the shape, leanVM's
program IV), **π2's circuit for π1's contract IV** (`Pi2Circuit`: the verifier's
view, `Circuit`, and the setup columns `σ`, `κ`; the IV is among `κ`'s constants, the seed of π1's transcript), π1's
calls as the circuit names their words, **where π2's witness holds π1's stream** (`pi1Stream`: the circuit compiler's
free bits, `RecCircuit.Compiled.decodeStream`), and the **Keccak-f block** (`flock : KeccakVm.KeccakFlockSpec`) of
the relation. `RecDeployment.Real` pins it to the circuit of the Keccak π1-rec3's graph at the 128-signature reference
and the block to `KeccakFlock.keccakFlockSpec`. **π1's contract IV** is computed with Keccak-f[1600] at π1's setup
commitment (`pi1IvAt`, `UniKeccak.contractIvK … keccakRec3`: it is π1's Fiat–Shamir's, which the circuit computes);
**π2's IV** (`RecDeployment.ivWith`, `prover::iv`) over `π`: π1's IV, π2's setup root and out-of-domain answer, the
circuit's digest, `log_n`.

**The setup** (`RecDeployment.setupTreesWith`): π1's is **one** WHIR commitment, of the Keccak setup stack
(`UniKeccak.setupTreeKWith`), with its out-of-domain answer (`UniKeccak.setupOodK`); the Keccak-f block's matrices are
never committed. π2's is the commitment of `κ`, `κ + σ`, with its answer (`Pi2Circuit.setupOod`). The answers are the
stacks' values at the roots' out-of-domain points (the deployed Keccak-256), constants of the verifiers.

**The relation** is the Keccak VM's, as `UniKeccak.KDeployment.Relation`: `KvHolds D.flock prog s input q`
(`M3Holds (keccakIsaInstance prog s) input q ∧ KeccakAux D.flock prog s q`) at the sizes `s` of π1's row counts,
which are π1's stream's (π2's witness), so the extractor outputs them with the stack.

**The extractors** are explicit and computable. `recExtractor2`: the transcript's and the setup's Keccak-256
evaluations replayed; **π2's `W`** inverted under the root the stream names and decoded (the fast path, the unique
decoder, the list decoder, at `W`'s stack, rate `1/2`), each candidate's witness values read (`basisValue`, the `B`
basis, of the stack's leading `N` words) and **π1's stream** read off them (`pi1Stream`), the first on which the Keccak π1-rec3's graph accepts at
Keccak-f[1600] with the contract's π1 openings. `recExtractor`: then the Keccak π1's own extractor
(`UniKeccak.uniExtractorK D.flock`) on that stream with the proof's three π1 opening proofs, its row counts the stream's.
-/

namespace RecStatement

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics (KeccakState)
open LeanVM.Extraction
open OracleComp OracleSpec Common
open scoped ENNReal

/-! ## π2's circuit with its setup columns -/

/-- **π2's circuit**: the verifier's view (`Circuit`) and the setup columns `σ` (each position's push tag, an index) and
`κ` (the constants), `2^logN` positions. -/
structure Pi2Circuit where
  circuit : Circuit
  sigma : ℕ → ℕ
  kappa : ℕ → K

/-- Eight little-endian bytes of `n` (`put`). -/
def le64 (n : ℕ) : List UInt8 := (List.range 8).map fun k ↦ (n >>> (8 * k)).toUInt8

/-- A coefficient's encoding: its limbs, its power of `γ`. -/
def Coeff.encoding (c : Coeff) : List UInt8 :=
  le64 c.c0.toNat ++ le64 c.c1.toNat ++ le64 c.c2.toNat ++ le64 c.gamma

/-- A linear form's encoding: its terms' count, each coefficient and cell, the constant (`0`, or `1` and it). -/
def Lin.encoding (l : Lin) : List UInt8 :=
  le64 l.terms.length ++ l.terms.flatMap (fun t ↦ t.1.encoding ++ le64 t.2) ++
    match l.constant with
    | none => le64 0
    | some c => le64 1 ++ c.encoding

/-- **The circuit's encoding** (`Circuit::digest`'s bytes before the setup columns' hashes). -/
def Circuit.encoding (c : Circuit) : List UInt8 :=
  le64 c.logN ++ le64 c.logRow ++ le64 c.formulas.length ++
    c.formulas.flatMap (fun f ↦ f.lin.encoding ++ le64 f.products.length ++
      f.products.flatMap fun p ↦ p.1.encoding ++ p.2.1.encoding ++ p.2.2.encoding) ++
    le64 c.pairs.length ++
    c.pairs.flatMap (fun p ↦ le64 p.firstRow ++ le64 p.logRows ++ le64 p.role ++ le64 p.formula ++
      le64 (if p.pulls then 1 else 0)) ++
    le64 c.reads.length ++
    c.reads.flatMap (fun rd ↦ match rd with
      | .integer b => le64 0 ++ le64 b
      | .root => le64 1 ++ le64 32
      | .scalar => le64 2 ++ le64 24) ++
    le64 c.publicTerms.length ++ c.publicTerms.flatMap fun t ↦ le64 t.tag ++ t.value.encoding

/-- The positions' count, `N = 2^logN`. -/
def Pi2Circuit.n (c : Pi2Circuit) : ℕ := 2 ^ c.circuit.logN

/-- **The setup's table** (`Setup::new`): the basis-`B` coefficients of `κ` (on `V_m`), then of `κ + σ` (`σ`'s values the
points `ω_{σ_i}`), `2^(m+1)` words (the setup stack's, its zero tail to the stack's `2^vars` words implicit). -/
def Pi2Circuit.setupStack (c : Pi2Circuit) : Array K :=
  let m := c.circuit.logN
  let kb := UniStatement.bCoefficients m (Array.ofFn (n := 2 ^ m) fun i ↦ c.kappa i.val)
  let sb := UniStatement.bCoefficients m (Array.ofFn (n := 2 ^ m) fun i ↦ UniStatement.point (c.sigma i.val))
  kb ++ Array.ofFn (n := 2 ^ m) fun i ↦ kb.getD i.val 0 + sb.getD i.val 0

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The circuit's digest** over `F` (`Circuit::digest`): Keccak-256 of the encoding, `σ`'s hash (its tags, four
little-endian bytes each) and `κ`'s (eight bytes each). -/
def Pi2Circuit.digestWith (c : Pi2Circuit) : m (List UInt8) := do
  let sigma ← keccak256With F ((List.range c.n).flatMap fun i ↦ (le64 (c.sigma i)).take 4)
  let kappa ← keccak256With F ((List.range c.n).flatMap fun i ↦ le64 (c.kappa i).lane.toNat)
  let d ← keccak256With F (c.circuit.encoding ++ digestBytes sigma ++ digestBytes kappa)
  return digestBytes d

/-- **π2's setup tree** over `F`: the WHIR commitment of the setup's table (`opening::commit`). -/
def Pi2Circuit.setupTreeWith (c : Pi2Circuit) : m LeanVM.Prover.Tree :=
  PcsQuotient.commitWith F (stackVars c.circuit.logN).2.2 c.setupStack

end With

/-- **π2's setup's out-of-domain answer** at a root: the setup stack (`setupStack`, zeros to `2^vars` words, `vars` the
setup's stack variables) as a multilinear polynomial (word `i` at the cube point of `i`'s bits, bit `0` first:
`UniStatement.multilinearEval`) at the root's out-of-domain point (`WhirBridge.Pcs.oodPoint`), as
`UniKeccak.setupOodK`. -/
def Pi2Circuit.setupOod (c : Pi2Circuit) (root : Digest) : E :=
  let vars := (stackVars c.circuit.logN).2.2
  let words := c.setupStack.toList.map ofK
  UniStatement.multilinearEval (words ++ List.replicate (2 ^ vars - words.length) 0)
    (WhirBridge.Pcs.oodPoint vars root).toList

/-! ## The deployment -/

/-- **The recursive verifier's deployment**: π1's (the Keccak VM's program, shape, program IV); π2's circuit **for
π1's contract IV** (the IV is among the circuit's constants: the seed of π1's transcript, which the circuit hashes with
Keccak-f[1600]); π1's calls as the circuit names their words; π1's stream as π2's witness holds it (the compiler's free
bits, `RecCircuit.Compiled.decodeStream`), a function of the witness's values at the positions; and the Keccak-f block
of the relation (`KvHolds flock`: what the `QFLOCK` region means; the verifier does not read it, the relation and π1's
extractor do). -/
structure RecDeployment where
  pi1 : UniKeccak.KDeployment
  pi2 : List UInt8 → Pi2Circuit
  pi1Calls : List (List CallWord)
  pi1Stream : (ℕ → K) → Array UInt8
  flock : KeccakVm.KeccakFlockSpec

/-- **π1's contract IV** at π1's setup commitment, over Keccak-f[1600] (`contract_iv_for` at `KECCAK_REC3`,
`UniKeccak.contractIvK … keccakRec3`): π1-rec3's Fiat–Shamir is the circuit's, which computes Keccak-f[1600]. -/
def RecDeployment.pi1IvAt (D : RecDeployment) (roots : UniKeccak.SetupRootsK) : List UInt8 :=
  pi1Iv D.pi1.shape D.pi1.programIv roots

/-- π2's circuit at π1's setup commitment: for its contract IV. -/
def RecDeployment.circuitAt (D : RecDeployment) (roots : UniKeccak.SetupRootsK) : Pi2Circuit :=
  D.pi2 (D.pi1IvAt roots)

/-- **The real deployment's setup columns are the circuit compiler's** (how the deployment builds them: `Setup::new`
of `adapt` of `compile`, at π1's contract IV): at every 32-byte π1 IV (π1's contract IV is a Keccak-256 digest) at
which the Lean compiler (`RecCircuit.compile`, the Rust's by `RecCircuitTest`) accepts the Keccak π1-rec3's recorded
graph (`RecGraphKeccak.Pi1.pi1GraphK`) at the emitted graph's roots (`RecGraphKeccak.Emitted.rootsAt`), π2's `σ` and
`κ` are the compiled circuit's (`sigmaAt`, `kappaAt`). -/
def RecDeployment.SetupFromCompiler (D : RecDeployment) : Prop :=
  ∀ (iv : List UInt8), iv.length = 32 → ∀ (c : RecCircuit.Compiled),
    RecCircuit.compile (RecCircuit.ofRG RecGraphKeccak.Pi1.pi1GraphK RecGraphKeccak.Emitted.rootsAt iv) = .ok c →
      (D.pi2 iv).sigma = c.circuit.sigmaAt ∧ (D.pi2 iv).kappa = c.circuit.kappaAt

/-- **The real deployment's data**: π2's circuit for the Keccak π1-rec3's graph at the 128-signature reference (the
emitted tables at every IV, and at π1's reference IV the `σ`, `κ` whose digest and setup root the Rust computed),
π1's calls, the reference shape (`RecGraphKeccak.Pi1.keccak128`, at which the graph is recorded) and leanVM's program
IV, the setup columns the compiler's at every 32-byte IV (`SetupFromCompiler`), and the Keccak-f block
`KeccakFlock.keccakFlockSpec` (the one π1-rec3's random-permutation theorem is proved at).

`Data.pi1Iv`, π1's reference IV, is the Rust's `contract_iv(KECCAK_128, KECCAK_REC3, PROGRAM_IV,
SetupRoots::REFERENCE)`: at the reference commitment `RecGraphKeccak.Pi1.referenceRootsK` (`F` the Keccak 128 setup's
root and out-of-domain answer). The digest and setup root clauses are used by no proof: they pin the model's σ, κ (from
which the model's contract computes π2's IV over `π`) to the deployed contract's constant IV, which the Rust computed
from them. **The program is not pinned** (`D.pi1.prog`): the end theorems hold for every program of the reference
shape. -/
def RecDeployment.Real (D : RecDeployment) : Prop :=
  (∀ iv, (D.pi2 iv).circuit = Data.circuit) ∧ D.pi1Calls = Data.pi1Calls ∧ D.pi1.shape = RecGraphKeccak.Pi1.keccak128 ∧
    D.pi1.programIv = UniStatement.programIv ∧
    Id.run ((D.pi2 Data.pi1Iv).digestWith (m := Id) fun x ↦ pure (LeanVM.Semantics.keccakF1600 x)) = Data.digest ∧
    digestBytes (Id.run ((D.pi2 Data.pi1Iv).setupTreeWith (m := Id)
      fun x ↦ pure (LeanVM.Semantics.keccakF1600 x))).root = Data.setupRoot ∧
    D.SetupFromCompiler ∧ D.flock = KeccakFlock.keccakFlockSpec

/-- **The setup's commitments**: π1's (`F`'s root and out-of-domain answer) and π2's (the commitment of `κ`, `κ + σ`:
its root and out-of-domain answer). -/
structure RecSetupRoots where
  pi1 : UniKeccak.SetupRootsK
  pi2 : Digest
  pi2Ood : E

/-- **The setup's trees**: π1's one tree (the Keccak setup stack's commitment) and π2's tree, with their out-of-domain
answers (the verifier's constants, computed from the stacks at the roots' out-of-domain points). -/
structure RecSetupTrees where
  pi1 : LeanVM.Prover.Tree
  pi2 : LeanVM.Prover.Tree
  pi1Ood : E
  pi2Ood : E

/-- The setup's commitments: each tree's root and its out-of-domain answer. -/
def RecSetupTrees.roots (t : RecSetupTrees) : RecSetupRoots := ⟨⟨t.pi1.root, t.pi1Ood⟩, t.pi2.root, t.pi2Ood⟩

/-- The setup's Keccak-256 evaluations, which the extractors read: π1's tree's, then π2's. -/
def RecSetupTrees.evaluations (t : RecSetupTrees) : List (List UInt8 × Digest) :=
  PcsQuotient.Tree.evaluations t.pi1 ++ PcsQuotient.Tree.evaluations t.pi2

/-! ## The declared claims' openings -/

/-- An element word's element, if its top 64 bits are zero (`claim_of_words`' `element`). -/
def elementOfWord (w : List UInt8) : Option E :=
  let be (at' : ℕ) : UInt64 := (List.range 8).foldl (fun acc k ↦ (acc <<< 8) ||| (w.getD (at' + k) 0).toUInt64) 0
  if w.length = 32 ∧ (w.take 8).all (· = 0) then some (UniStatement.eNew (be 24) (be 16) (be 8)) else none

/-- The root a claim's root word names: the digest whose bytes are the word's 32 bytes, as they are (a PCS claim's
root field). -/
def rootOfWord (w : List UInt8) : Digest := UniStatement.digestOfBytes32 w

/-- **A PCS claim's fields from its words** (`claim_of_words`): the root (32 bytes), the out-of-domain answer, the
point's coordinates, the value; every element's top 64 bits zero, at least the three words. -/
def claimOfWords (words : List (List UInt8)) : Option (Digest × E × List E × E) := do
  let root ← words.head?
  let oodW ← words[1]?
  let valueW ← words.getLast?
  if !(3 ≤ words.length ∧ root.length = 32) then none
  let ood ← elementOfWord oodW
  let point ← ((words.drop 2).dropLast).mapM elementOfWord
  let value ← elementOfWord valueW
  pure (rootOfWord root, ood, point, value)

/-- **π2's claims' sizes**: `W`'s `2^24` words, the setup's `2^25`, `Q`'s `2^28` (π1's are `2^27`, `2^26`, `2^23`). -/
def pi2Size (n : ℕ) : Bool := n == 24 || n == 25 || n == 28

/-- **A claim's opening with the out-of-domain point computed over `F`** (`pcs_claim::verify_claim`, `ood_point` over
`keccak256With F`; `WhirBridge.Pcs.pcsVerifyWithHashO`): the point claim `(pt, v)` on the commitment `(root, ood)` of a
stack of `n` variables, its point required to have `n` coordinates. -/
def pcsOpenKO {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (n : ℕ) (root : Digest) (ood : E)
    (pt : List E) (v : E) (p : Compile.Proof) : m Bool :=
  if h : pt.length = n then
    WhirBridge.Pcs.pcsVerifyWithHashO (keccak256With F) F ⟨root, ood, pt, v, h⟩ p
  else pure false

/-- **A declared claim's opening** over `F` on its words (`pcs_claim::verify_claim`): decoded (`claimOfWords`), then
opened on `n` the point's length (`WhirBridge.Pcs.pcsVerifyWithHash`, which rejects `n` outside version 1's sizes):
π2's sizes by `pcsOpenKO` (the out-of-domain point computed over `F`), the others by `UniKeccak.pcsOpenK` (at
`WhirBridge.Pcs.oodPoint`, as π1's verifier). -/
def pcsOpenWords {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (words : List (List UInt8))
    (proof : Compile.Proof) : m Bool :=
  match claimOfWords words with
  | none => pure false
  | some (root, ood, point, value) =>
    if pi2Size point.length then pcsOpenKO F point.length root ood point value proof
    else UniKeccak.pcsOpenK F point.length root ood point value proof

open LeanVM.Semantics LeanVM.Protocol.KeccakHash in
/-- **At the real Keccak-f[1600] the two openings agree**: the out-of-domain point computed over Keccak-f[1600] is the
deployed `WhirBridge.Pcs.oodPoint` (`keccak256With keccakF1600 = keccak256`). -/
theorem pcsOpenKO_keccakF1600 (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    pcsOpenKO (m := Id) keccakF1600 n root ood pt v p =
      UniKeccak.pcsOpenK (m := Id) keccakF1600 n root ood pt v p := by
  unfold pcsOpenKO UniKeccak.pcsOpenK
  split
  · rw [LeanVM.Protocol.keccak256With_keccakF1600, WhirBridge.Pcs.UnionO.pcsVerifyWithHashO_id]
    rfl
  · rfl

/-- π1's calls with the setup's commitment the deployment's: the constant root and answer words of the call that has
them (the setup's), replaced by `F`'s root's 32 bytes and its answer's word. -/
def pi1CallsWith (calls : List (List CallWord)) (roots : UniKeccak.SetupRootsK) : List (List CallWord) :=
  calls.map fun call ↦ match call with
    | .const _ :: .const _ :: rest =>
      .const (digestBytes roots.f) :: .const (UniStatement.elementWord roots.fOod) :: rest
    | other => other

/-- **A proof of the recursive verifier**: the stream (calldata after the selector and the public input) and the eight
opening proofs the block holds, in claim order: π1's `C1`, `C2`, `F`, then π2's `W`, the setup, `Q`'s identity,
pushes' and sum claims. -/
structure RecProof where
  stream : Array UInt8
  c1 : Compile.Proof
  c2 : Compile.Proof
  f : Compile.Proof
  w : Compile.Proof
  setup : Compile.Proof
  qId : Compile.Proof
  qPush : Compile.Proof
  qSum : Compile.Proof

def RecProof.openings (p : RecProof) : List Compile.Proof := [p.c1, p.c2, p.f, p.w, p.setup, p.qId, p.qPush, p.qSum]

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **π2's IV** over `F` (`prover::iv`): the Keccak π1-rec3's contract IV (Keccak-f[1600]) at π1's setup commitment,
π2's setup root and out-of-domain answer, the circuit's digest, `log_n`. -/
def RecDeployment.ivWith (D : RecDeployment) (roots : RecSetupRoots) : m (List UInt8) := do
  let c := D.circuitAt roots.pi1
  let digest ← c.digestWith F
  RecStatement.ivWith F (D.pi1IvAt roots.pi1) (digestBytes roots.pi2) roots.pi2Ood digest c.circuit.logN

/-- **The contract** over `F` on the setup's commitments: π2's verifier on the calldata (its IV `ivWith`), its verdict,
then the eight claims, word for word as the contract checks them declared (`pcsCalls`, π1's setup commitment and π2's
the setup's), each decoded and opened (`pcsOpenWords`). Its verdict, and the claims' words (none if the verifier
rejects). -/
def RecDeployment.contractWith (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (proof : RecProof) : m (Bool × List (List (List UInt8))) := do
  let c := D.circuitAt roots.pi1
  let iv ← D.ivWith F roots
  let o ← runWith F (Spec.of c.circuit) iv input.toList proof.stream
  match o.result with
  | .error _ => return (false, [])
  | .ok r =>
    if !o.accepts then return (false, []) else
    let calls := pcsCalls c.circuit (pi1CallsWith D.pi1Calls roots.pi1) (digestBytes roots.pi2) roots.pi2Ood
      proof.stream r
    if calls.length ≠ 8 then return (false, calls) else
    let mut ok := true
    for (words, p) in calls.zip proof.openings do
      ok := ok && (← pcsOpenWords F words p)
    return (ok, calls)

/-- **The recursive verifier** over `F`: the contract's verdict. -/
def RecDeployment.verifierWith (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (proof : RecProof) : m Bool := do
  return (← D.contractWith F roots input proof).1

/-- **The setup** over `F`: π1's (the one commitment of the Keccak setup stack, `UniKeccak.setupTreeKWith`, and its
out-of-domain answer `UniKeccak.setupOodK`) and π2's (`κ`, `κ + σ` of the circuit for π1's contract IV at π1's setup
commitment, and its answer `Pi2Circuit.setupOod`). -/
def RecDeployment.setupTreesWith (D : RecDeployment) : m RecSetupTrees := do
  let t1 ← UniKeccak.setupTreeKWith F D.pi1
  let r1 := D.pi1.setupRoots t1
  let t2 ← (D.circuitAt r1).setupTreeWith F
  return ⟨t1, t2, r1.fOod, (D.circuitAt r1).setupOod t2.root⟩

end With

/-! ## π1-rec3 at Keccak-f[1600] -/

/-- A π1 opening: the claim's root, out-of-domain answer, point and value. -/
abbrev Pi1Opening : Type := Digest × E × List E × E

/-- **A call of π1's own contract** (the bytes `RecGraph`'s outputs and `UniKeccak.pcsClaimWordsK` give: the root's 32
bytes, the out-of-domain answer, the point, the value, 32-byte words), decoded (`claimOfWords`). -/
def decodePi1Call (call : List UInt8) : Option Pi1Opening :=
  if call.length % 32 ≠ 0 then none else
  claimOfWords ((List.range (call.length / 32)).map fun j ↦ (call.drop (32 * j)).take 32)

/-- **The contract's π1 openings**: its first three claims decoded. -/
def contractPi1Openings (calls : List (List (List UInt8))) : Option (List Pi1Opening) :=
  (calls.take 3).mapM claimOfWords

/-- **The Keccak π1-rec3's graph accepts at Keccak-f[1600], its claims the contract's** (π2's part's conclusion): π2's
circuit computes the Keccak π1-rec3's recorded verifier graph (`RecGraphKeccak.Pi1.pi1GraphK`) with the real
Keccak-f[1600] (`RecCircuit.compile_sound`, `RecGraphKeccak.pi1rec3K_end`); on π1's IV, the public input and the
stream `s`, the graph's checks hold and its three claims are the contract's `ops`: their points and values, and `C1`'s
and `C2`'s roots and out-of-domain answers, which `s` carries (`F`'s commitment is the setup's, a constant of the
contract, which the graph holds as the code's reference). -/
def Pi1GraphAccepts (iv1 : List UInt8) (input : Vector UInt8 32) (s : Array UInt8) (ops : List Pi1Opening) : Prop :=
  ∃ out gops, RecGraph.evalGraphDeployed RecGraphKeccak.Pi1.pi1GraphK iv1 input.toList s = some out ∧
    (∀ z ∈ out.zeros, z = 0) ∧ (∀ z ∈ out.nonzeros, z ≠ 0) ∧ out.calls.mapM decodePi1Call = some gops ∧
    gops.map (·.2.2) = ops.map (·.2.2) ∧
      (gops.take 2).map (fun o ↦ (o.1, o.2.1)) = (ops.take 2).map (fun o ↦ (o.1, o.2.1))

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The Keccak π1-rec3's verifier with its Fiat–Shamir over Keccak-f[1600]** and its three openings over `F`:
`UniKeccak.verifyWithK` at `keccakRec3` with its IV and run over Keccak-f[1600] (`pi1Iv`, `UniKeccak.runK …
keccakRec3 .point`), then `C1`, `C2`, the setup opened over `F` (`UniKeccak.pcsOpenK` on their stacks' variables). -/
def pi1KeccakVerifierWith (D : UniKeccak.KDeployment) (roots : UniKeccak.SetupRootsK) (input : Vector UInt8 32)
    (proof : UniKeccak.KeccakProof) : m Bool := do
  let iv := pi1Iv D.shape D.programIv roots
  let o := UniKeccak.runK D.shape iv input.toList proof.stream UniKeccak.keccakRec3 .point
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let mut ok := r.openings.map (·.1) == UniStatement.commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        ok := ok && (← UniKeccak.pcsOpenK F (UniKeccak.stackVarsK D.shape c) (UniKeccak.commitOfK roots r c).1
          (UniKeccak.commitOfK roots r c).2 pt value (proof.openingOf c))
      | _ => ok := false
    if r.matrices.isSome then ok := false
    return ok

/-- **The Keccak π1-rec3's graph at Keccak-f[1600], its three openings over `F`**: the graph's checks hold and its
claims (`F`'s commitment the setup's) are opened as `UniKeccak.pcsOpenK` on `C1`'s, `C2`'s and the setup's stack
variables, with the proof's `C1`, `C2`, setup opening proofs. -/
def pi1GraphVerifierWith (D : RecDeployment) (roots : UniKeccak.SetupRootsK) (input : Vector UInt8 32)
    (proof : UniKeccak.KeccakProof) : m Bool := do
  match RecGraph.evalGraphDeployed RecGraphKeccak.Pi1.pi1GraphK (D.pi1IvAt roots) input.toList proof.stream with
  | none => return false
  | some out =>
    if !(out.zeros.all (· == 0) && out.nonzeros.all (· != 0)) then return false
    match out.calls.mapM decodePi1Call with
    | none => return false
    | some ops =>
      if ops.length ≠ 3 then return false
      let ops := ops.modify 2 fun o ↦ (roots.f, roots.fOod, o.2.2)
      let mut ok := true
      for ((o, c), p) in (ops.zip UniStatement.commitments).zip [proof.c1, proof.c2, proof.setup] do
        ok := ok && (← UniKeccak.pcsOpenK F (UniKeccak.stackVarsK D.pi1.shape c) o.1 o.2.1 o.2.2.1 o.2.2.2 p)
      return ok

end With

/-! ## The extractors -/

/-- The digest a root word of the stream names, at a stream offset. -/
def streamRoot (stream : Array UInt8) (at' : ℕ) : Digest := rootOfWord (streamWord stream at')

/-- **A committed word** under a root: the leaves the unique preimages `pre` commit to, `2^(μ − 6 + 1)` leaves of `64`
words (`Replay.leavesUnder`). -/
def committedWord (pre : Digest → ℕ → Option (List UInt8)) (μ : ℕ) (root : Digest) : ℕ → List K :=
  let height := μ - 6 + 1
  leafAt (PcsQuotient.Replay.leavesUnder pre 64 height root) height 64

/-- A word's candidate stacks: the fast path's, the unique decoder's, the list decoder's. -/
def candidates (μ : ℕ) (word : ℕ → List K) : List (Vector K (2 ^ μ)) :=
  fastStacks μ 1 word ++ PcsQuotient.UniqueDecoding.uniqueStacks μ 1 word ++ decodeStacks μ 1 word

/-- The Keccak π1-rec3's graph's checks at Keccak-f[1600] on a stream. -/
def pi1GraphChecks (iv1 : List UInt8) (input : Vector UInt8 32) (s : Array UInt8) : Bool :=
  match RecGraph.evalGraphDeployed RecGraphKeccak.Pi1.pi1GraphK iv1 input.toList s with
  | some out => out.zeros.all (· == 0) && out.nonzeros.all (· != 0)
  | none => false

/-- **`Pi1GraphAccepts`, decided**: the graph's checks hold at Keccak-f[1600] and its three calls, decoded, are the
openings `ops` (their points and values, `C1`'s and `C2`'s roots and answers). -/
def pi1GraphAcceptsB (iv1 : List UInt8) (input : Vector UInt8 32) (s : Array UInt8) (ops : List Pi1Opening) : Bool :=
  match RecGraph.evalGraphDeployed RecGraphKeccak.Pi1.pi1GraphK iv1 input.toList s with
  | none => false
  | some out =>
    out.zeros.all (· == 0) && out.nonzeros.all (· != 0) &&
      match out.calls.mapM decodePi1Call with
      | none => false
      | some gops => decide (gops.map (·.2.2) = ops.map (·.2.2) ∧
          (gops.take 2).map (fun o ↦ (o.1, o.2.1)) = (ops.take 2).map (fun o ↦ (o.1, o.2.1)))

/-- **The contract's π1 openings from the calldata alone**: π2's run over Keccak-f[1600] (any IV: π1's three claims
read only the stream's public data, π1's roots and claims' elements, and the setup's commitment, not the transcript's
hashes), its first three claims decoded (`contractPi1Openings`). Composition: `RecCompose.pi1OpsOf_eq`. -/
def pi1OpsOf (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (stream : Array UInt8) :
    Option (List Pi1Opening) :=
  let c := (D.circuitAt roots.pi1).circuit
  match (run (Spec.of c) [] input.toList stream).result with
  | .error _ => none
  | .ok r => contractPi1Openings
      (pcsCalls c (pi1CallsWith D.pi1Calls roots.pi1) (digestBytes roots.pi2) roots.pi2Ood stream r)

/-- **π2's extractor on given preimages**: for each candidate of π2's `W` stack (its root after π1's public data), π1's
stream its witness values hold (`pi1Stream`; `w`'s `B` coefficients the stack's leading `N` words); the first on which
the Keccak π1-rec3's graph accepts at Keccak-f[1600] with the contract's π1 openings (`pi1GraphAcceptsB`: its checks,
and its three claims those the contract makes, `pi1OpsOf`).

(Composition, `lean-rec-compose`: the search must test the calls too, not only the graph's checks. `W`'s list may hold
two candidates whose π1 streams both pass the checks, the first one's calls not the contract's: the adversary commits a
word within the list-decoding radius of two codewords, `c'` first in the list, its stream an honest π1 proof of another
transcript, and `c` the one the openings' claims hold of. Searching by the checks alone, the extractor would output
`c'`'s stream, on which `Pi1GraphAccepts` with the contract's openings fails.) -/
def recExtractFrom2 (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (pre : Digest → ℕ → Option (List UInt8)) (proof : RecProof) : Option (Array UInt8) :=
  let c := (D.circuitAt roots.pi1).circuit
  let at' := rootsAt c.reads
  let μ := (stackVars c.logN).1
  let wWord := committedWord pre μ (streamRoot proof.stream (at'.getD (rootReads c.reads) 0))
  match pi1OpsOf D roots input proof.stream with
  | none => none
  | some ops =>
    (candidates μ wWord).findSome? fun w ↦
      let table := Array.ofFn (n := 2 ^ c.logN) fun i ↦ w.toArray.getD i.val 0
      let s := D.pi1Stream fun i ↦ UniStatement.basisValue table c.logN i
      if pi1GraphAcceptsB (D.pi1IvAt roots.pi1) input s ops then some s else none

/-- The unique preimages of the setup's evaluations and the transcript's (the lengths a Merkle tree hashes). -/
def preimagesOf (setupEvals : List (List UInt8 × Digest)) (T : OracleQueryLog) :
    Digest → ℕ → Option (List UInt8) :=
  PcsQuotient.Replay.preimageIn (PcsQuotient.Replay.preimageIndex (setupEvals ++
    PcsQuotient.Replay.transcriptEvaluations PcsQuotient.merkleLengths (LeanVM.permutationQueries T)))

/-- **π2's extractor** in the random-permutation model: π1's stream. -/
def recExtractor2 (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (setupEvals : List (List UInt8 × Digest)) (T : OracleQueryLog) (proof : RecProof) : Option (Array UInt8) :=
  recExtractFrom2 D roots input (preimagesOf setupEvals T) proof

/-- π1's Keccak proof from π1's stream and the recursive proof's three π1 opening proofs (`C1`, `C2`, the setup). -/
def RecProof.pi1Proof (p : RecProof) (s : Array UInt8) : UniKeccak.KeccakProof := ⟨s, p.c1, p.c2, p.f⟩

/-- **The end-to-end extractor**: π2's (π1's stream), then the Keccak π1's own (`UniKeccak.uniExtractorK D.flock`:
`C1`'s word under the root the stream names, decoded, read as the Keccak VM's stack at the stream's row counts, the
first satisfying `KvHolds D.flock`). -/
def recExtractor (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32)
    (setupEvals : List (List UInt8 × Digest)) (T : OracleQueryLog) (proof : RecProof) :
    Option ((rows : List ℕ) × D.pi1.Stack rows) :=
  (recExtractor2 D roots input setupEvals T proof).bind fun s ↦
    (UniKeccak.uniExtractorK D.flock D.pi1 input setupEvals T (proof.pi1Proof s)).map fun q ↦ ⟨_, q⟩

/-- π2's extractor's shape. -/
abbrev RecExtractor2 : Type :=
  RecSetupRoots → Vector UInt8 32 → List (List UInt8 × Digest) → OracleQueryLog → RecProof → Option (Array UInt8)

/-- The end-to-end extractor's shape: π1's row counts and a stack at them. -/
abbrev RecExtractor (D : RecDeployment) : Type :=
  RecSetupRoots → Vector UInt8 32 → List (List UInt8 × Digest) → OracleQueryLog → RecProof →
    Option ((rows : List ℕ) × D.pi1.Stack rows)

/-! ## Knowledge soundness, part 1: π2's, in the random-permutation model -/

/-- An adversary: given the setup's roots, a public input and a proof, with coins, `π` and `π⁻¹`. -/
abbrev RecAdversary : Type := RecSetupRoots → OracleComp RandomPermutationOracles (Vector UInt8 32 × RecProof)

/-- π2's outcome: the statement and the proof, the verdict, the setup's evaluations, the transcript, the setup's roots,
the contract's calls. -/
abbrev RecOutcome2 : Type :=
  ((Vector UInt8 32 × RecProof) × Bool) × List (List UInt8 × Digest) × OracleQueryLog × RecSetupRoots ×
    List (List (List UInt8))

/-- **π2's knowledge-soundness experiment**: the setup over `π`, the adversary given its roots (its queries logged),
then the contract over `π` (its verdict and calls). -/
noncomputable def recSoundnessExperiment2 (D : RecDeployment) (A : RecAdversary) : ProbComp RecOutcome2 :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles (A trees.roots)).run []
    let (accepted, calls) ← D.contractWith queryPermutation trees.roots z.1 z.2
    return ((z, accepted), trees.evaluations, transcript, trees.roots, calls)

/-- **The adversary breaks π2's knowledge soundness**: the contract accepts, and π2's extractor outputs no stream on
which the Keccak π1-rec3's graph accepts at Keccak-f[1600] with the contract's π1 openings. -/
def RecBreaksKnowledgeSoundness2 (D : RecDeployment) (ext : RecExtractor2) (z : RecOutcome2) : Prop :=
  z.1.2 = true ∧ ¬ ∃ s ops, ext z.2.2.2.1 z.1.1.1 z.2.1 z.2.2.1 z.1.1.2 = some s ∧
    contractPi1Openings z.2.2.2.2 = some ops ∧
    Pi1GraphAccepts (D.pi1IvAt z.2.2.2.1.pi1) z.1.1.1 s ops

/-- **π2's knowledge soundness for the extractor `ext`**, error `ε2 Q` for `Q` calls of `π` and `π⁻¹`. -/
def RecKnowledgeSoundness2With (D : RecDeployment) (ext : RecExtractor2) (ε2 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← recSoundnessExperiment2 D A}[RecBreaksKnowledgeSoundness2 D ext z] ≤ ε2 Q

/-- **π2's knowledge soundness** (provable in the random-permutation model): if the contract accepts, π2's explicit
extractor `recExtractor2` outputs π1's stream, on which the Keccak π1-rec3's recorded graph run with Keccak-f[1600]
accepts, its three claims the contract's (which the block proved); but with probability `ε2 Q`. -/
def RecKnowledgeSoundness2 (D : RecDeployment) (ε2 : ℕ → ℝ≥0∞) : Prop :=
  RecKnowledgeSoundness2With D (recExtractor2 D) ε2

/-! ## The hypotheses about π1-rec3 at Keccak-f[1600] -/

/-- A π1 adversary of the recursive setup: given its roots and its trees' Keccak-256 evaluations (the setup is public;
the derived adversary runs π2's extractor, which reads them), a public input and π1's Keccak proof.

(Composition, `lean-rec-compose`: with the roots alone, the adversary built from π2's must recompute the setup, many
calls of `π` that `ε1` would be charged at, and whose transcript `uniExtractorK` would read with π2's adversary's.) -/
abbrev Pi1Adversary : Type :=
  RecSetupRoots → List (List UInt8 × Digest) →
    OracleComp RandomPermutationOracles (Vector UInt8 32 × UniKeccak.KeccakProof)

/-- **π1-rec3's knowledge-soundness experiment at Keccak-f[1600]**: the recursive setup over `π`, the adversary, then
the Keccak π1-rec3's verifier with its Fiat–Shamir over Keccak-f[1600] and its openings over `π`
(`pi1KeccakVerifierWith`). -/
noncomputable def pi1KeccakSoundnessExperiment (D : RecDeployment) (A : Pi1Adversary) :
    ProbComp UniKeccak.KOutcome :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles (A trees.roots trees.evaluations)).run []
    let accepted ← pi1KeccakVerifierWith queryPermutation D.pi1 trees.roots.pi1 z.1 z.2
    return ((z, accepted), trees.evaluations, transcript)

/-- **Hypothesis: π1-rec3 is knowledge sound with its Fiat–Shamir instantiated by Keccak-f[1600]**, error `ε1 Q`, for
its own extractor `UniKeccak.uniExtractorK D.flock`, against the Keccak VM's relation `KvHolds D.flock`, against every
π1 adversary of the recursive setup, `Q` counting its calls of `π` and `π⁻¹` only.

**As stated it is false.** Keccak-f[1600] is a fixed public function, which an `OracleComp` adversary computes for free:
it commits a non-satisfying table, grinds each round's prover message offline until the Keccak-derived challenge
escapes the round's doom, and opens honestly. It is the Fiat–Shamir heuristic **for
adversaries of bounded Keccak-f[1600] work**, which Lean does not model, motivated by π1-rec3's random-permutation
theorem (`UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_closed`: error `uniBound128 (2^35/|E|) Q`, at most `2^-64`
for `Q ≤ 2^64`), where each grinding step costs a query. The end-to-end theorem does not take it:
`RecKnowledgeSoundnessReduction` (`Reduction.lean`) bounds the break by this experiment's probability for one explicit
adversary, `pi1Adversary A`. -/
def Pi1FsKeccak (D : RecDeployment) (ε1 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : Pi1Adversary) (Q : ℕ), (∀ roots evals, QueryCostAtMost (A roots evals) permutationCallCost Q) →
    Pr{let z ← pi1KeccakSoundnessExperiment D A}[
      UniKeccak.KBreaksKnowledgeSoundness D.flock D.pi1 (UniKeccak.uniExtractorK D.flock D.pi1) z] ≤ ε1 Q

/-- An adversary choosing a public input and π1's stream, given the recursive setup's roots and its trees' Keccak-256
evaluations (as `Pi1Adversary`). -/
abbrev Pi1StreamAdversary : Type :=
  RecSetupRoots → List (List UInt8 × Digest) →
    OracleComp RandomPermutationOracles (Vector UInt8 32 × Array UInt8)

/-- The merge hazard's experiment: the recursive setup, the adversary's public input and stream, π1's IV. -/
noncomputable def pi1HazardExperiment (D : RecDeployment) (B : Pi1StreamAdversary) :
    ProbComp (List UInt8 × Vector UInt8 32 × Array UInt8) :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    let (z, _) ← (simulateQ loggedOracles (B trees.roots trees.evaluations)).run []
    return (D.pi1IvAt trees.roots.pi1, z)

/-- **The merge hazard on a stream whose Keccak π1-rec3 graph checks hold**, at Keccak-f[1600]: the graph's checks hold
on the stream (`pi1GraphChecks`), and the Keccak π1-rec3's run on it draws `t` (challenge 52), `t` a root of
`Z_bad(p_0)` (`RecGraphKeccak.MergeHazardK`, `p_0` challenge 45). It asks only `pi1GraphChecks`, not the full
`Pi1GraphAccepts`: a larger event than needed, which is harmless, since the term is only larger. The empty stream, and
every stream on which the run stops before `t`, is not on it. -/
def Pi1HazardAccepted (iv1 : List UInt8) (input : Vector UInt8 32) (s : Array UInt8) : Prop :=
  pi1GraphChecks iv1 input s = true ∧ RecGraphKeccak.MergeHazardK LeanVM.Semantics.keccakF1600 iv1 input.toList s

/-- **Hypothesis: π1-rec3's run at Keccak-f[1600] avoids the merge hazard** on the streams its graph accepts
(`Pi1HazardAccepted`; `RecGraphKeccak.MergeHazardK`: the run draws `t` and `t` is where the recorded graph, merging by
symbol, and the verifier, merging by value, may differ), but with probability `εh Q`, `Q` counting calls of `π` and
`π⁻¹` only. Motivated by `RecGraphKeccak.hazard_probK` (`2^16/|E|` a uniform `t`).

**As stated it is false** for the same reason as `Pi1FsKeccak`: an adversary writes an accepted-looking stream and
grinds its free bytes offline until Keccak-f[1600]'s `t` lands on one of the `≤ 2^16` hazardous values, about `2^176`
evaluations and no query. It is the Fiat–Shamir heuristic **for adversaries of bounded Keccak-f[1600] work**, which
Lean does not model. The end-to-end theorem does not take it: `RecKnowledgeSoundnessReduction` bounds the hazard by
this experiment's probability for one explicit adversary, `hazardAdversary A`. -/
def Pi1HazardKeccak (D : RecDeployment) (εh : ℕ → ℝ≥0∞) : Prop :=
  ∀ (B : Pi1StreamAdversary) (Q : ℕ), (∀ roots evals, QueryCostAtMost (B roots evals) permutationCallCost Q) →
    Pr{let z ← pi1HazardExperiment D B}[Pi1HazardAccepted z.1 z.2.1 z.2.2] ≤ εh Q

/-! ## Knowledge soundness, part 2: end to end, against the Keccak VM's `KvHolds` -/

/-- An outcome: the statement and the proof, the verdict, the setup's evaluations, the transcript, the setup's roots. -/
abbrev RecOutcome : Type :=
  ((Vector UInt8 32 × RecProof) × Bool) × List (List UInt8 × Digest) × OracleQueryLog × RecSetupRoots

/-- **The knowledge-soundness experiment**: the setup over `π`, the adversary given its roots (its queries logged),
then the recursive verifier over `π`. -/
noncomputable def recSoundnessExperiment (D : RecDeployment) (A : RecAdversary) : ProbComp RecOutcome :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles (A trees.roots)).run []
    let accepted ← D.verifierWith queryPermutation trees.roots z.1 z.2
    return ((z, accepted), trees.evaluations, transcript, trees.roots)

/-- **The adversary breaks knowledge soundness**: the recursive verifier accepts, and the extractor outputs no row
counts and stack satisfying the Keccak VM's relation (`KvHolds D.flock`) for the public input. -/
def RecBreaksKnowledgeSoundness (D : RecDeployment) (ext : RecExtractor D) (z : RecOutcome) : Prop :=
  z.1.2 = true ∧ ¬ ∃ w, ext z.2.2.2 z.1.1.1 z.2.1 z.2.2.1 z.1.1.2 = some w ∧ D.pi1.Relation D.flock w.1 z.1.1.1 w.2

/-- **Knowledge soundness for the extractor `ext`**, error `ε Q` for `Q` calls of `π` and `π⁻¹`. -/
def RecKnowledgeSoundnessWith (D : RecDeployment) (ext : RecExtractor D) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← recSoundnessExperiment D A}[RecBreaksKnowledgeSoundness D ext z] ≤ ε Q

/-- **Knowledge soundness of the recursive verifier against the Keccak VM's relation, end to end, the Prop-premise
corollary** (π2's verifier and the eight openings; the explicit extractor `recExtractor`: π2's, then the Keccak π1's),
error `ε2 + ε1 + εh`, under the named hypotheses: the recorded graph is the Keccak π1-rec3's verifier off the merge
hazard (`RecGraphKeccak.Pi1GraphIsVerifierK`, proved: `RecGraphKeccak.Sim.pi1GraphIsVerifierK`), π1-rec3 is knowledge
sound with its Fiat–Shamir over Keccak-f[1600] (`Pi1FsKeccak ε1`), and its run at Keccak-f[1600] avoids the merge
hazard on accepted streams (`Pi1HazardKeccak εh`). `ε2` is π2's part's (`RecKnowledgeSoundness2`). The
random-permutation theorems do not formally compose with the circuit's Keccak-f[1600]: these hypotheses are where they
meet. **`Pi1FsKeccak` and `Pi1HazardKeccak` are false as stated** (they quantify over adversaries that grind
Keccak-f[1600] offline for free): read them as the Fiat–Shamir heuristic for adversaries of bounded Keccak-f[1600]
work. The end-to-end statement without them is the explicit reduction `RecKnowledgeSoundnessReduction`
(`Reduction.lean`). -/
def RecKnowledgeSoundness (D : RecDeployment) (ε2 ε1 εh : ℕ → ℝ≥0∞) : Prop :=
  RecGraphKeccak.Pi1GraphIsVerifierK → Pi1FsKeccak D ε1 → Pi1HazardKeccak D εh →
    RecKnowledgeSoundnessWith D (recExtractor D) fun Q ↦ ε2 Q + ε1 Q + εh Q

/-! ## Completeness -/

/-- π1-rec3's prover (in the recursion, its Fiat–Shamir over Keccak-f[1600], its openings over `π`): a prover of the
Keccak verifier (`UniKeccak.KProver`). -/
abbrev Pi1Prover (D : RecDeployment) : Type := UniKeccak.KProver D.pi1

/-- π2's prover: from the public input and π1's Keccak proof, a proof of the recursive verifier (or none), with coins,
`π` and `π⁻¹` (it recomputes the public setup as it needs). -/
abbrev Pi2Prover : Type :=
  Vector UInt8 32 → UniKeccak.KeccakProof → OracleComp RandomPermutationOracles (Option RecProof)

/-- A prover of the recursive verifier: from the public input, π1's row counts and a stack of the Keccak VM's layout at
them. -/
abbrev RecProver (D : RecDeployment) : Type :=
  Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp RandomPermutationOracles (Option RecProof)

/-- The recursive prover: π1-rec3's, then π2's on its proof. -/
def composeProver (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) : RecProver D :=
  fun input rows q ↦ do
    match ← P1 input rows q with
    | none => return none
    | some p1 => P2 input p1

/-- **π2's completeness experiment**: the setup, π1's proof (from any π1 prover), whether the Keccak π1-rec3's graph
accepts it at Keccak-f[1600] with its openings over `π` (`pi1GraphVerifierWith`), and whether the contract accepts π2's
proof of it. -/
noncomputable def recCompletenessExperiment2 (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) : ProbComp (Bool × Bool) :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← P1 input rows q with
    | none => return (false, false)
    | some p1 =>
      let a1 ← pi1GraphVerifierWith queryPermutation D trees.roots.pi1 input p1
      match ← P2 input p1 with
      | none => return (a1, false)
      | some p2 => return (a1, ← D.verifierWith queryPermutation trees.roots input p2)

/-- **π2's completeness** (over its own coins and `π`), on π1-rec3's prover `P1`'s proofs of honest statements
(`KvHonest D.flock`): a π1 proof on which the Keccak π1-rec3's graph accepts at Keccak-f[1600], its openings verifying
over `π`, is turned by `P2` into a proof the contract accepts, but with probability `δ2`.

(Composition, `lean-rec-compose`: for π1-rec3's prover, not every `P1`. A `P1` of unbounded queries can grind its
proof, the graph still accepting, until π2's honest run on it hits one of π2's degenerate challenges (the one value the
contract requires nonzero, `all = 0`), which no `δ2` below one bounds.) -/
def RecCompleteness2 (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) (δ2 : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let v ← recCompletenessExperiment2 D P1 P2 input rows q}[v.1 = true ∧ v.2 = false] ≤ δ2

/-- **π1-rec3's completeness experiment at Keccak-f[1600]**: the recursive setup, the prover's proof, the Keccak
π1-rec3's verifier with its Fiat–Shamir over Keccak-f[1600] and its openings over `π`. -/
noncomputable def pi1KeccakCompletenessExperiment (D : RecDeployment) (P1 : Pi1Prover D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.pi1.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← P1 input rows q with
    | none => return false
    | some p1 => pi1KeccakVerifierWith queryPermutation D.pi1 trees.roots.pi1 input p1

/-- **Hypothesis: π1-rec3 is complete with its Fiat–Shamir instantiated by Keccak-f[1600]**, error `δ1`, on honest
statements (`KvHonest D.flock`). Its random-permutation analogue is `UniKeccak.UniCompletenessKeccakRec3` (a
statement; no proof of it is used here), about one fixed honest prover: no adversary grinds there. -/
def Pi1CompletenessKeccak (D : RecDeployment) (P1 : Pi1Prover D) (δ1 : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let v ← pi1KeccakCompletenessExperiment D P1 input rows q}[v = false] ≤ δ1

/-- The honest proofs' merge hazard experiment: the recursive setup, the prover's proof, whether its run at
Keccak-f[1600] hits the merge hazard. -/
noncomputable def pi1HonestHazardExperiment (D : RecDeployment) (P1 : Pi1Prover D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.pi1.Stack rows) : ProbComp (Option (List UInt8 × Array UInt8)) :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← P1 input rows q with
    | none => return none
    | some p1 => return some (D.pi1IvAt trees.roots.pi1, p1.stream)

/-- **Hypothesis: π1-rec3's honest proofs avoid the merge hazard at Keccak-f[1600]**, but with probability `δh`.
Motivated only by `RecGraphKeccak.hazard_probK` (at most `2^16` hazardous `t` per `p_0`, `2^-176` for a uniform `t`),
a count, not a game: its random-permutation reading is not proved. `RecGraphKeccak.MergeHazardK` asks that the run
draw `t` (challenge 52), so a proof whose run stops before `t` is not on it. -/
def Pi1HazardKeccakHonest (D : RecDeployment) (P1 : Pi1Prover D) (δh : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let z ← pi1HonestHazardExperiment D P1 input rows q}[
      ∃ iv s, z = some (iv, s) ∧ RecGraphKeccak.MergeHazardK LeanVM.Semantics.keccakF1600 iv input.toList s] ≤ δh

/-- **The completeness experiment**: the setup, the prover's proof, the recursive verifier's verdict, over `π`. -/
noncomputable def recCompletenessExperiment (D : RecDeployment) (P : RecProver D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.pi1.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← P input rows q with
    | none => return false
    | some proof => D.verifierWith queryPermutation trees.roots input proof

/-- **Completeness of the prover `P`**: its proof of a public input with a `KvHonest D.flock` stack, at row counts that
fit π1's shape, is rejected with probability at most `δ`. -/
def RecCompletenessWith (D : RecDeployment) (P : RecProver D) (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let v ← recCompletenessExperiment D P input rows q}[v = false] ≤ δ

/-- **Completeness of the recursive verifier, end to end**: π1-rec3's prover then π2's (`composeProver`), error
`δ1 + δh + δ2`, under the named hypotheses: the recorded graph is the Keccak π1-rec3's verifier off the merge hazard
(`RecGraphKeccak.Pi1GraphIsVerifierK`, proved), π1-rec3 is complete with its Fiat–Shamir over Keccak-f[1600]
(`Pi1CompletenessKeccak δ1`) and its honest proofs avoid the merge hazard (`Pi1HazardKeccakHonest δh`, motivated by
`hazard_probK` only). `δ2` is π2's part's (`RecCompleteness2`). -/
def RecCompleteness (D : RecDeployment) (P1 : Pi1Prover D) (P2 : Pi2Prover) (δ1 δh δ2 : ℝ≥0∞) : Prop :=
  RecGraphKeccak.Pi1GraphIsVerifierK → Pi1CompletenessKeccak D P1 δ1 → Pi1HazardKeccakHonest D P1 δh →
    RecCompletenessWith D (composeProver D P1 P2) (δ1 + δh + δ2)

end RecStatement
