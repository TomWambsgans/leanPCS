-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The model, the experiments' shape and the form of the
-- statements are `UniStatement/Security.lean`'s and `RecSecurity.lean`'s (after `formal/Statement`'s
-- `PcsQuotient.Security` and leanerVM `mumbai` 6175f1a0's `Statement/LeanVm.lean`, MIT OR Apache-2.0); the relation is
-- `formal/KeccakVm`'s (`KvHolds`). A non-module file (it imports `UniKeccak/Pcs.lean`).
import UniKeccak.Mapping
import UniKeccak.Pcs
import UniStatement.Security

/-!
# Knowledge soundness and completeness of the Keccak verifier, against the Keccak VM's relation

Statements only, no proof. They are `UniStatement/Security.lean`'s (and `RecSecurity.lean`'s for π1-rec3's shape)
with the Keccak VM in place of leanVM 42422001:

* **The deployment** (`KDeployment`): the Keccak VM's program (`KeccakVm.Program`, `2^logBytecode` instructions), the
  shape (valid: `Shape.validate` with Flock, so `h_SHA3 ≥ 7`), leanVM's program IV.
* **The setup** (`setupTreeKWith`): the one WHIR commitment of the setup stack (`setupStackK`: the bytecode's tuples
  with the Keccak VM's entries, the memory's addresses). The Keccak-f block's matrices (`2^34` entries) are never
  committed. The verifier's setup commitment is its root and the stack's value at the root's out-of-domain point
  (`KDeployment.setupRoots`, `setupOodK`: the EIP's PCS commitment, `crates/pcs_claim`).
* **The verifier** (`KDeployment.verifierWith … v`): the Keccak contract's IV (`contractIvKWith`, binding the variant
  `v` and the setup commitment), then `verifyWithK` (the run, three PCS claims' openings). `keccakMain` is the main
  line, `keccakRec3` π1-rec3's shape under the recursion.
* **The relation** (`KDeployment.RelationK F`): `KeccakVm.KvHolds F prog s input q`, `M3Holds (keccakIsaInstance prog
  s) input q ∧ KeccakAux F prog s q`, at the proof's sizes `s` (the shape's memory, the proof's row counts), `F` the
  Keccak-f block (`KeccakVm.KeccakFlockSpec`, a parameter: its inhabitant is built elsewhere; the verifier fixes its
  ports and constant wire, `KeccakFlockFits`).
* **The extractor** (`uniExtractorK F`): explicit and computable, as `uniExtractor`: the Keccak-256 evaluations of the
  setup and of the transcript replayed, `C1`'s Merkle tree inverted under the root the stream names, its candidate
  stacks (the fast path, the unique decoder, the list decoder at `C1`'s `2^μ`, rate `1/2`), each read as the Keccak
  VM's stack (`kvStack`) at the proof's row counts, the first satisfying `KvHolds F` (decidable).
* **Completeness** is for a prover given as a parameter (`KProver`): its proof of a statement with a `KvHonest` stack,
  at row counts that fit the shape (`Shape.RowsFit`), is rejected with probability at most `δ`.
-/

namespace UniKeccak

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash UniStatement
open LeanVM.Semantics (KeccakState)
open LeanVM.Extraction
open OracleComp OracleSpec Common
open KeccakVm.KeccakIsa (keccakIsaμ)
open Lv42.Protocol.LeanIsa (Sizes)
open scoped ENNReal

/-- **The Keccak VM's deployment**: the program, the shape (its heights; valid), leanVM's program IV. -/
structure KDeployment where
  prog : KeccakVm.Program
  shape : UniStatement.Shape
  programIv : List UInt8
  valid : shape.Valid
  logBytecode_eq : shape.logBytecode = prog.logSize

/-- The memory has at least two cells. -/
theorem KDeployment.logMemory_pos (D : KDeployment) : 0 < D.shape.logMemory := by
  have h := D.valid.2
  unfold UniStatement.Shape.validate at h
  by_contra hc
  have hlt : D.shape.logMemory < 1 := by omega
  simp [hlt] at h

/-- A proof's sizes: the shape's memory, the proof's row counts. -/
def KDeployment.sizes (D : KDeployment) (rows : List ℕ) : Sizes := sizesOf D.shape D.logMemory_pos rows

/-- **The instance** at a proof's row counts: the Keccak VM's (`keccakIsaInstance`). -/
abbrev KDeployment.inst (D : KDeployment) (rows : List ℕ) : Lv42.Protocol.M3Instance :=
  KeccakVm.keccakIsaInstance D.prog (D.sizes rows)

/-- The Keccak VM's stack at a proof's sizes. -/
abbrev KDeployment.Stack (D : KDeployment) (rows : List ℕ) : Type :=
  LeanVM.Protocol.Column (keccakIsaμ D.prog (D.sizes rows))

/-- **The relation**: `KvHolds` of the Keccak-f block `F` at the row counts, the public input the calldata's 32 bytes
(`publicInputOf`: big-endian words, as the contract reads them). -/
def KDeployment.Relation (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (rows : List ℕ)
    (input : Vector UInt8 32) (q : D.Stack rows) : Prop :=
  KeccakVm.KvHolds F D.prog (D.sizes rows) (publicInputOf input.toList) q

instance (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (rows : List ℕ) (input : Vector UInt8 32)
    (q : D.Stack rows) : Decidable (D.Relation F rows input q) := by
  unfold KDeployment.Relation KeccakVm.KvHolds KeccakVm.KeccakAux
  infer_instance

/-- **The relation completeness starts from**: `KvHonest` (`M3Honest` and the Keccak-f region with the lanes'
copies). -/
def KDeployment.HonestRelation (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (rows : List ℕ)
    (input : Vector UInt8 32) (q : D.Stack rows) : Prop :=
  KeccakVm.KvHonest F D.prog (D.sizes rows) (publicInputOf input.toList) q

/-! ### The setup -/

/-- **The setup's out-of-domain answer** at a root: the setup stack's multilinear polynomial (word `i` at the cube
point of `i`'s bits, bit `0` first: `multilinearEval`) at the root's out-of-domain point
(`WhirBridge.Pcs.oodPoint`, on the setup stack's variables). -/
def setupOodK (D : KDeployment) (root : Digest) : E :=
  multilinearEval ((setupStackK D.prog D.shape).toList.map ofK)
    (WhirBridge.Pcs.oodPoint (setupLayout D.shape).vars root).toList

/-- **The setup commitment the verifier holds**: the setup stack's root (`F`) and its out-of-domain answer. -/
def KDeployment.setupRoots (D : KDeployment) (tree : LeanVM.Prover.Tree) : SetupRootsK :=
  ⟨tree.root, setupOodK D tree.root⟩

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The setup** over `F`: the commitment of the setup stack (`setupStackK`), the only one. -/
def setupTreeKWith (D : KDeployment) : m LeanVM.Prover.Tree :=
  PcsQuotient.commitWith F (setupLayout D.shape).vars (setupStackK D.prog D.shape)

/-- **The transcript's IV** over `F` (`contract_iv` at the variant `v`). -/
def KDeployment.ivWith (D : KDeployment) (v : KeccakVariant) (roots : SetupRootsK) : m (List UInt8) :=
  contractIvKWith F D.shape v D.programIv roots

/-- **The deployed Keccak verifier** of variant `v` over `F` on the setup's roots: its IV, then `verifyWithK`. -/
def KDeployment.verifierWith (D : KDeployment) (v : KeccakVariant) (roots : SetupRootsK) (input : Vector UInt8 32)
    (proof : KeccakProof) : m Bool := do
  verifyWithK F D.shape v (← D.ivWith F v roots) roots input proof

/-- **The deployed Keccak verifier at π1-rec4** over `F` on the setup's roots: its IV (`contract_iv` at `keccakRec4`,
code 4), then `verifyWithK4` (π1-rec4's run, the same three claims' openings). -/
def KDeployment.verifierWith4 (D : KDeployment) (roots : SetupRootsK) (input : Vector UInt8 32)
    (proof : KeccakProof) : m Bool := do
  verifyWithK4 F D.shape keccakRec4 (← D.ivWith F keccakRec4 roots) roots input proof

end With

/-! ### The extractor -/

/-- `C1`'s root as the stream names it: its 32 bytes after the six row counts, two 16-byte halves (`next_root`). -/
def c1RootOfK (proof : KeccakProof) : Digest :=
  let b := proof.stream
  let half (o : ℕ) : E := eNew (beWordAt b (o + 8)) (beWordAt b o) 0
  rootOf (half 24, half 40)

/-- **`C1`'s committed word** on the Keccak VM: under the root the stream names, the leaves the unique preimages `pre`
commit to: `2^(μ − 6 + 1)` leaves of `64` words, `μ` the Keccak `C1`'s variables. -/
def c1WordK (D : KDeployment) (pre : Digest → ℕ → Option (List UInt8)) (proof : KeccakProof) : ℕ → List K :=
  let height := (c1LayoutK D.shape).vars - 6 + 1
  leafAt (PcsQuotient.Replay.leavesUnder pre 64 height (c1RootOfK proof)) height 64

/-- **The extractor on given preimages**: the first candidate `C1` stack whose Keccak VM stack, at the proof's row
counts, satisfies `KvHolds F`; the fast path's first, then the unique decoder's, then the list decoder's. -/
def extractFromK (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (input : Vector UInt8 32)
    (pre : Digest → ℕ → Option (List UInt8)) (proof : KeccakProof) : Option (D.Stack proof.rows) :=
  let word := c1WordK D pre proof
  let μ := (c1LayoutK D.shape).vars
  let candidate (stack : Vector K (2 ^ μ)) : Option (D.Stack proof.rows) :=
    let q := kvStack D.prog (D.sizes proof.rows) D.shape fun i ↦ stack.toArray.getD i 0
    if D.Relation F proof.rows input q then some q else none
  (fastStacks μ 1 word).findSome? candidate <|>
    (PcsQuotient.UniqueDecoding.uniqueStacks μ 1 word).findSome? candidate <|>
    (decodeStacks μ 1 word).findSome? candidate

/-- **The extractor** in the random-permutation model: `extractFromK` on the unique preimages of the setup's
evaluations and the transcript's. -/
def uniExtractorK (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (input : Vector UInt8 32)
    (setupEvals : List (List UInt8 × Digest)) (T : OracleQueryLog) (proof : KeccakProof) :
    Option (D.Stack proof.rows) :=
  let paths := setupEvals ++
    PcsQuotient.Replay.transcriptEvaluations PcsQuotient.merkleLengths (LeanVM.permutationQueries T)
  extractFromK F D input (PcsQuotient.Replay.preimageIn (PcsQuotient.Replay.preimageIndex paths)) proof

/-- An extractor's shape: from the statement, the setup's evaluations, the transcript and the proof, a stack at the
proof's row counts. -/
abbrev KExtractor (D : KDeployment) : Type :=
  Vector UInt8 32 → List (List UInt8 × Digest) → OracleQueryLog → (proof : KeccakProof) → Option (D.Stack proof.rows)

/-! ### Knowledge soundness -/

/-- An adversary: given the setup commitment, a public input and a Keccak proof, with coins, `π` and `π⁻¹`. -/
abbrev KAdversary : Type := SetupRootsK → OracleComp RandomPermutationOracles (Vector UInt8 32 × KeccakProof)

/-- An outcome: the statement and the proof, the verdict, the setup's evaluations, the transcript. -/
abbrev KOutcome : Type :=
  ((Vector UInt8 32 × KeccakProof) × Bool) × List (List UInt8 × Digest) × OracleQueryLog

/-- **The knowledge-soundness experiment** of variant `v`: the setup over `π`, the adversary given its roots (its
queries logged), then the deployed Keccak verifier over `π`. -/
noncomputable def keccakSoundnessExperiment (D : KDeployment) (v : KeccakVariant) (A : KAdversary) :
    ProbComp KOutcome :=
  runWithRandomPermutation do
    let tree ← setupTreeKWith queryPermutation D
    let roots := D.setupRoots tree
    let (z, transcript) ← (simulateQ loggedOracles (A roots)).run []
    let accepted ← D.verifierWith queryPermutation v roots z.1 z.2
    return ((z, accepted), PcsQuotient.Tree.evaluations tree, transcript)

/-- **The adversary breaks knowledge soundness**: the verifier accepts, and the extractor outputs no stack satisfying
the Keccak VM's relation for the public input at the proof's row counts. -/
def KBreaksKnowledgeSoundness (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (ext : KExtractor D)
    (z : KOutcome) : Prop :=
  z.1.2 = true ∧ ¬ ∃ q, ext z.1.1.1 z.2.1 z.2.2 z.1.1.2 = some q ∧ D.Relation F z.1.1.2.rows z.1.1.1 q

/-- **Knowledge soundness of the Keccak verifier of variant `v` for the extractor `ext`**, error `ε Q` for `Q` calls
of `π` and `π⁻¹`. -/
def UniKnowledgeSoundnessKeccakWith (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (v : KeccakVariant)
    (ext : KExtractor D) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : KAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← keccakSoundnessExperiment D v A}[KBreaksKnowledgeSoundness F D ext z] ≤ ε Q

/-- **Knowledge soundness of the Keccak verifier** (the main line, `KECCAK_MAIN`) against the Keccak VM's relation
with the Keccak-f block `F`, for the explicit extractor `uniExtractorK F`. -/
def UniKnowledgeSoundnessKeccak (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (ε : ℕ → ℝ≥0∞) : Prop :=
  UniKnowledgeSoundnessKeccakWith F D keccakMain (uniExtractorK F D) ε

/-- **Knowledge soundness of the Keccak π1 at π1-rec3's shape** (`KECCAK_REC3`, the recursion's) against the Keccak
VM's relation with the Keccak-f block `F`, for the explicit extractor `uniExtractorK F`. -/
def UniKnowledgeSoundnessKeccakRec3 (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (ε : ℕ → ℝ≥0∞) : Prop :=
  UniKnowledgeSoundnessKeccakWith F D keccakRec3 (uniExtractorK F D) ε

/-- **The knowledge-soundness experiment at π1-rec4**: `keccakSoundnessExperiment` with π1-rec4's verifier
(`KDeployment.verifierWith4`). -/
noncomputable def keccakSoundnessExperiment4 (D : KDeployment) (A : KAdversary) : ProbComp KOutcome :=
  runWithRandomPermutation do
    let tree ← setupTreeKWith queryPermutation D
    let roots := D.setupRoots tree
    let (z, transcript) ← (simulateQ loggedOracles (A roots)).run []
    let accepted ← D.verifierWith4 queryPermutation roots z.1 z.2
    return ((z, accepted), PcsQuotient.Tree.evaluations tree, transcript)

/-- **Knowledge soundness of the Keccak π1 at π1-rec4's shape** (`KECCAK_REC4`, the recursion's since π1-rec4) against
the Keccak VM's relation with the Keccak-f block `F`, for the explicit extractor `uniExtractorK F`. -/
def UniKnowledgeSoundnessKeccakRec4 (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : KAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← keccakSoundnessExperiment4 D A}[KBreaksKnowledgeSoundness F D (uniExtractorK F D) z] ≤ ε Q

/-! ### Completeness -/

/-- A prover: from the public input, the row counts and a stack of the Keccak VM's layout at them, a proof (or none),
with coins, `π` and `π⁻¹`. -/
abbrev KProver (D : KDeployment) : Type :=
  Vector UInt8 32 → (rows : List ℕ) → D.Stack rows → OracleComp RandomPermutationOracles (Option KeccakProof)

/-- **The completeness experiment** of variant `v`: the setup, the prover's proof, the Keccak verifier's verdict, over
`π`. -/
noncomputable def keccakCompletenessExperiment (D : KDeployment) (v : KeccakVariant) (P : KProver D)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let tree ← setupTreeKWith queryPermutation D
    match ← P input rows q with
    | none => return false
    | some proof => D.verifierWith queryPermutation v (D.setupRoots tree) input proof

/-- **Completeness of the prover `P` for the Keccak verifier of variant `v`**: its proof of a public input with a
`KvHonest F` stack, at row counts that fit the shape, is rejected with probability at most `δ`. -/
def UniCompletenessKeccakWith (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (v : KeccakVariant) (P : KProver D)
    (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation F rows input q →
    Pr{let b ← keccakCompletenessExperiment D v P input rows q}[b = false] ≤ δ

/-- **Completeness** of the Keccak verifier (the main line), for a prover given explicitly. -/
def UniCompletenessKeccak (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (P : KProver D) (δ : ℝ≥0∞) : Prop :=
  UniCompletenessKeccakWith F D keccakMain P δ

/-- **Completeness** of the Keccak π1 at π1-rec3's shape, for a prover given explicitly. -/
def UniCompletenessKeccakRec3 (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (P : KProver D) (δ : ℝ≥0∞) :
    Prop :=
  UniCompletenessKeccakWith F D keccakRec3 P δ

/-- **The completeness experiment at π1-rec4**: `keccakCompletenessExperiment` with π1-rec4's verifier. -/
noncomputable def keccakCompletenessExperiment4 (D : KDeployment) (P : KProver D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let tree ← setupTreeKWith queryPermutation D
    match ← P input rows q with
    | none => return false
    | some proof => D.verifierWith4 queryPermutation (D.setupRoots tree) input proof

/-- **Completeness** of the Keccak π1 at π1-rec4's shape, for a prover given explicitly. -/
def UniCompletenessKeccakRec4 (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (P : KProver D) (δ : ℝ≥0∞) :
    Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation F rows input q →
    Pr{let b ← keccakCompletenessExperiment4 D P input rows q}[b = false] ≤ δ

end UniKeccak
