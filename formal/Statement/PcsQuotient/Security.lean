-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The model, the experiment's shape and the form of the statements are leanerVM's (branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0: `Statement/RandomPermutation.lean`, `Statement/LeanVm.lean`'s
-- `soundnessExperiment`, `KnowledgeSoundness`, `Completeness`), adapted to this protocol.
module

public import PcsQuotient.Extractor
public import PcsQuotient.Prover
public import VCVio.EvalDist.ProbabilityNotation

/-!
# Knowledge soundness, completeness and zero knowledge

The end statements, in the **random-permutation model** of leanerVM's `mumbai`
(`Statement/RandomPermutation.lean` there): one uniformly random permutation `π` of the Keccak-f[1600]
state, lazily sampled, which every party queries forward (`π x`) and inverse (`π⁻¹ y`); Keccak-256 is
the sponge over `π`. Every hash of the protocol is Keccak-256 over `π`: the reduction's chain
(`Transcript.lean`), the WHIR commitments' Merkle trees and the openings' duplex (`Opening.lean`), and
the circuit's commitment, computed over `π` by the **setup** before the adversary runs (`setupWith`).
The relation's hashes are the deployed Keccak-256 (`Relation.lean`): the circuit computes the
deployed Keccak-f[1600], independent of `π`.

* **Knowledge soundness** (`KnowledgeSoundness ε`): for every adversary of at most `Q` calls of `π`
  and `π⁻¹`, given the setup's commitment (the circuit's index root), the verifier accepts its
  statement and proof while **`extractor`**, reading only the
  statement, the proof, the adversary's transcript and the public setup's tree (the circuit
  commitment's Merkle tree, as its Keccak-256 evaluations), outputs no witness, with probability at
  most `ε Q`.
* **Completeness** (`Completeness δ`): for every statement and witness of the relation, the honest
  prover's (`prover`) proof, with uniform coins (random rows, blinding), is rejected with probability at
  most `δ`.
* **Zero knowledge** (`ZeroKnowledgeWith s₀ sim simOracle ζ`, statistical, the permutation programmable): for
  every statement and witness of the relation and every distinguisher of at most `Q` calls of `π` and
  `π⁻¹`, its verdict on the honest proof in the model and on the simulator `sim`'s proof, the simulator's
  oracle `simOracle` answering its queries, differ in probability by at most `ζ Q`. One proof, from an empty
  `π`, the distinguisher's queries after it: no query before the proof, no second proof under the same `π`.
  The protocol is zero-knowledge **assuming a zero-knowledge PCS** (`docs/membership/PROTOCOL.md`, "Zero
  knowledge"): the end
  theorem (`formal/EndToEnd/ZK`) states its hypothesis on the PCS explicitly.

**The bounds are parameters** (`ε`, `δ`, `ζ`). A bound is part of what is proved: `KnowledgeSoundness ε`
for `ε = 1` says nothing. The end theorems (`formal/EndToEnd`) fix them (`README.md`, "What is proved").

**Zero knowledge rests on a zero-knowledge PCS and the prover's randomness** (`docs/membership/PROTOCOL.md`,
"Zero knowledge"): the openings are assumed to reveal nothing beyond their claims; the random rows and the
blinding of `h` make the revealed scalars (the two out-of-domain answers and the three values `X`, `C`, `V + Y`
at `t`) uniform.
The statement's prover takes its randomness uniform; the deployed one derives it from a 32-byte seed by a
Keccak-256 KDF (outside this model).

**One Keccak-256.** Deployed, one Keccak-256 serves the reduction's chain, the WHIR Merkle trees
(`hash_pair` is byte for byte the relation's `pair`), the openings' duplex and the relation. As in mumbai, the
model has one random permutation `π`, which every hash of the protocol queries (there is no private oracle);
the relation is over the deployed Keccak-256, which the circuit computes. Knowledge soundness needs no
collision clause: the extracted secret satisfies the relation exactly. A consumer that reads more from a
statement than the relation says (that `y` names one `x`) gets it up to a collision of the deployed
Keccak-256, `StatementBinds`, as mumbai's `DigestBinds`.
-/

@[expose] public section

namespace PcsQuotient

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-! ### The deployed system -/

/-- **The setup** over `F`: the membership circuit's commitment (`Circuit.indexCommitmentWith`, at
`logRows = 22`) with its Merkle tree: the tree of the WHIR commitment of the circuit's wiring table, and the
commitment (its root, the table's out-of-domain answer). The experiments compute it; the knowledge-soundness
extractor reads the tree's Keccak-256 evaluations (`Tree.evaluations`): the setup is public. -/
def setupWith {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) :
    m (LeanVM.Prover.Tree × Commitment) :=
  commitmentWith F (cellVars logRows) (membership logRows).wiringTable

/-- **The verifier** over `F`, on the circuit committed as `index` (`Verifier.lean`'s `verifyWith`,
at the membership circuit's size). -/
def verifier {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (index : Commitment)
    (stmt : Statement) (proof : Proof) : m Bool :=
  verifyWith F logRows index stmt proof

/-- Proofs of work: the honest prover tries `2^25` nonces each (as mumbai's prover). -/
def nonceFuel : ℕ := 2 ^ 25

/-- **The deployed circuit commitment**, over Keccak-f[1600]: the root and the out-of-domain answer the
deployed verifier holds (the contract's two storage slots; the differential test checks that the Lean
circuit's commitment is the Rust's, `--index`; computing it takes minutes, so it is a function of `()`: a
compiled constant would be computed whenever a program importing it starts). -/
def deployedIndex (_ : Unit) : Commitment :=
  (Id.run (setupWith (m := Id) fun s ↦ pure (keccakF1600 s))).2

set_option compiler.extract_closed false in
/-- **The deployed verifier**, over Keccak-f[1600], on the deployed circuit commitment. -/
def deployedVerifier (stmt : Statement) (proof : Proof) : Bool :=
  Id.run (verifier (m := Id) (fun s ↦ pure (keccakF1600 s)) (deployedIndex ()) stmt proof)

/-! ### The model's calls -/

/-- A uniform 64-bit word from the model's coins. -/
def coinWord : OracleComp RandomPermutationOracles UInt64 := do
  let n ← liftM (RandomPermutationOracles.query (.inl (2 ^ 64 - 1)))
  return UInt64.ofNat (n : Fin (2 ^ 64 - 1 + 1)).val

/-- **Uniform randomness** from the model's coins (`Randomness`): the thirty-two random rows' words, the six
blinding words and the four slack words, each a uniform word of `K`, in the order the Rust's KDF derives them
(`Randomness::derive`: `blind[e][i]` is word `32 + 2 e + i`, slack word `k` is word `38 + k`). -/
def sampleCoins : OracleComp RandomPermutationOracles Coins := do
  let w ← (List.range (randomWords + 3 * freeBlind + slackWords)).mapM fun _ ↦ coinWord
  let word (k : ℕ) : K := K.ofLane (w.getD k 0)
  return ⟨fun r ↦ word r.val, fun e i ↦ word (randomWords + freeBlind * e.val + i.val),
    fun k ↦ word (randomWords + 3 * freeBlind + k.val)⟩

/-! ### The honest prover and the extractor -/

/-- **The honest prover** over `F`: `proverWith` (`Prover.lean`), the Rust's `prove` then `open`, on the
membership circuit's cells of the secret, with the coins given (the random rows, the blinding),
`2^25` nonces per proof of work. -/
def prover {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState) (stmt : Statement)
    (w : Secret) (coins : Coins) : m (Option Proof) :=
  proverWith F nonceFuel stmt w coins

/-- **The extractor**: `transcriptExtractorFor` (`Extractor.lean`) at the membership circuit. From the
statement, the public setup's tree (its Keccak-256 evaluations `setupEvals`, `Tree.evaluations`), the
adversary's transcript and the proof, a secret: the witness table's tree inverted through the setup's
and the transcript's Keccak-256 evaluations (hash maps), its word decoded (interpolation, then unique
decoding, then list decoding, each only if the stages before give no witness), and the first
candidate's cells' input bits that spell a witness. Straight-line: it reads the setup's tree and the
transcript, it neither queries `π` nor runs the adversary again. Its cost is `Extractor.lean`'s table. -/
def extractor (stmt : Statement) (setupEvals : List (List UInt8 × Digest)) (T : OracleQueryLog)
    (proof : Proof) : Option Secret :=
  transcriptExtractorFor (membership logRows) stmt setupEvals T proof

/-! ### Knowledge soundness -/

/-- An adversary in the random-permutation model: given the public setup's commitment (the circuit's
index commitment, which it could also recompute with `π`), a computation with private coins and oracle
access to `π` and `π⁻¹` that outputs a statement and a proof. -/
abbrev Adversary : Type := Commitment → OracleComp RandomPermutationOracles (Statement × Proof)

/-- An outcome of the experiment: the statement and the proof, the verdict, the setup's Keccak-256
evaluations (its tree, `Tree.evaluations`), and the adversary's transcript, its queries and their
answers in order. -/
abbrev Outcome : Type :=
  ((Statement × Proof) × Bool) × List (List UInt8 × Digest) × OracleQueryLog

abbrev Outcome.statement (z : Outcome) : Statement := z.1.1.1
abbrev Outcome.proof (z : Outcome) : Proof := z.1.1.2
abbrev Outcome.accepted (z : Outcome) : Prop := z.1.2 = true
abbrev Outcome.setupEvaluations (z : Outcome) : List (List UInt8 × Digest) := z.2.1
abbrev Outcome.transcript (z : Outcome) : OracleQueryLog := z.2.2

/-- **The knowledge-soundness experiment**: the setup (the circuit's commitment and its tree over `π`), the
adversary given the commitment, its queries recorded (`Common.loggedOracles`), then the verifier over
`π` on its statement and proof with the commitment, the whole game run against the lazily sampled
permutation from no edge; the outcome holds the setup tree's Keccak-256 evaluations, public, for the
extractor. -/
noncomputable def soundnessExperiment (A : Adversary) : ProbComp Outcome :=
  runWithRandomPermutation do
    let (tree, index) ← setupWith queryPermutation
    let (z, transcript) ← (simulateQ loggedOracles (A index)).run []
    let accepted ← verifier queryPermutation index z.1 z.2
    return ((z, accepted), Tree.evaluations tree, transcript)

/-- **The adversary breaks knowledge soundness**: the verifier accepts, and `extractor`, on the setup's
tree and the adversary's transcript, outputs no witness of the statement. -/
def BreaksKnowledgeSoundness (z : Outcome) : Prop :=
  z.accepted ∧ ¬ ∃ w, extractor z.statement z.setupEvaluations z.transcript z.proof = some w ∧
    Relation z.statement w

/-- **Knowledge soundness in the random-permutation model**, for the extractor `extractor`, with the
error `ε Q` for `Q` calls of `π` and `π⁻¹` by the adversary on any commitment it is given (its coins
free). -/
def KnowledgeSoundness (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : Adversary) (Q : ℕ), (∀ index, QueryCostAtMost (A index) permutationCallCost Q) →
    Pr{let z ← soundnessExperiment A}[BreaksKnowledgeSoundness z] ≤ ε Q

/-! ### Completeness -/

/-- **The completeness experiment**: the setup, the honest prover's proof with uniform coins, then the
verifier's verdict, all over `π`; no proof is a failure. -/
noncomputable def completenessExperiment (stmt : Statement) (w : Secret) : ProbComp Bool :=
  runWithRandomPermutation do
    let (_, index) ← setupWith queryPermutation
    let coins ← sampleCoins
    match ← prover queryPermutation stmt w coins with
    | none => return false
    | some proof => verifier queryPermutation index stmt proof

/-- **Completeness in the random-permutation model**: the honest prover's proof of a statement it has
a witness for is rejected with probability at most `δ`. -/
def Completeness (δ : ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
    Pr{let v ← completenessExperiment stmt w}[v = false] ≤ δ

/-! ### Zero knowledge -/

/-- A distinguisher: from the proof (`none` if the prover made none), a verdict, with private coins
and oracle access to `π` and `π⁻¹`. It may depend on the statement and the witness (it is quantified
after them). -/
abbrev Distinguisher : Type := Option Proof → OracleComp RandomPermutationOracles Bool

/-- **The real experiment**: the honest prover's proof of `stmt` from `w` with uniform coins over `π`,
then the distinguisher, against the lazily sampled permutation. -/
noncomputable def realExperiment (stmt : Statement) (w : Secret) (D : Distinguisher) :
    ProbComp Bool :=
  runWithRandomPermutation do
    let coins ← sampleCoins
    D (← prover queryPermutation stmt w coins)

/-- **The ideal experiment of a simulator**: `sim`'s proof of `stmt`, without the witness, then the
distinguisher, its every query answered by the simulator's oracle `simOracle`, the simulator's state
(of type `S`) starting at `s₀`. -/
def idealExperimentWith {S : Type} (s₀ : S) (sim : Statement → StateT S ProbComp (Option Proof))
    (simOracle : QueryImpl RandomPermutationOracles (StateT S ProbComp)) (stmt : Statement)
    (D : Distinguisher) : ProbComp Bool :=
  (do
    let proof ← sim stmt
    simulateQ simOracle (D proof)).run' s₀

/-- **Statistical zero knowledge in the programmable random-permutation model, for a simulator**
`sim` with its oracle `simOracle` (from the state `s₀`), with the error `ζ Q` for a distinguisher of at
most `Q` calls of `π` and `π⁻¹` (its coins free): its verdicts in the real experiment and in the ideal
experiment of `sim` differ in probability by at most `ζ Q`. The simulator is a parameter so that the end
theorem can name the simulator it proves (`README.md`, "The simulator").

**Scope: one proof, the distinguisher after it.** `realExperiment` starts from an empty, lazily sampled
`π`; the prover goes first and makes every query before the distinguisher's; the distinguisher, quantified
after the statement and the witness, queries `π` and `π⁻¹` only after it is given the proof (`Distinguisher`
is a function of the proof). Not covered: oracle queries before the proof (a distinguisher's precomputation,
or auxiliary input that depends on `π`), and several proofs under one `π`. -/
def ZeroKnowledgeWith {S : Type} (s₀ : S) (sim : Statement → StateT S ProbComp (Option Proof))
    (simOracle : QueryImpl RandomPermutationOracles (StateT S ProbComp)) (ζ : ℕ → ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w →
  ∀ (D : Distinguisher) (Q : ℕ), (∀ proof, QueryCostAtMost (D proof) permutationCallCost Q) →
    Pr{let b ← realExperiment stmt w D}[b = true] ≤
        Pr{let b ← idealExperimentWith s₀ sim simOracle stmt D}[b = true] + ζ Q ∧
      Pr{let b ← idealExperimentWith s₀ sim simOracle stmt D}[b = true] ≤
        Pr{let b ← realExperiment stmt w D}[b = true] + ζ Q

/-! ### Collisions of the deployed Keccak-256 -/

/-- **A collision of the deployed Keccak-256** on two 64-byte blocks (`pair`, `Relation.lean`). -/
def PairCollision (a b : Bytes32 × Bytes32) : Prop := a ≠ b ∧ pair a.1 a.2 = pair b.1 b.2

/-- **The statement binds `x`, up to a collision** (mumbai's `DigestBinds` for this relation): two secrets of
one statement have the same `x`, or their hashes of `y`, `(x, 0x11^32)` and `(x', 0x11^32)`, collide. -/
def StatementBinds : Prop :=
  ∀ w w' : Secret, w.statement = w'.statement →
    w.x = w'.x ∨ PairCollision (w.x, Vector.replicate 32 yPad) (w'.x, Vector.replicate 32 yPad)

/-! ### The end theorems -/

/-- **The end theorems** with no hypothesis, at the bounds `ε`, `δ`. Both fields are proved in
`formal/EndToEnd` (`Soundness.knowledgeSoundness`, `E2ECompleteness.completeness_end`); `statementBinds` is
immediate and not proved in Lean. Zero knowledge (`ZeroKnowledgeWith`) is proved under a hypothesis on the PCS,
stated in its theorem (`formal/EndToEnd/ZK`; `README.md`, "What is proved"). -/
structure Theorems (ε : ℕ → ℝ≥0∞) (δ : ℝ≥0∞) : Prop where
  /-- Knowledge soundness for the straight-line `extractor`. -/
  knowledgeSoundness : KnowledgeSoundness ε
  /-- Completeness of the honest `prover`. -/
  completeness : Completeness δ
  /-- The statement binds `x` up to a collision of the deployed Keccak-256 (needed by no other field: an
  extracted secret satisfies the relation exactly). -/
  statementBinds : StatementBinds

end PcsQuotient

end
