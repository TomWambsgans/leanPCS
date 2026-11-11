-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Basic
import RecCompose.IvLength
import RecCircuit.Check

/-!
# π2's part: `RecKnowledgeSoundness2`, from π2's layers

`recKnowledgeSoundness2_of_layers`: `RecStatement.RecKnowledgeSoundness2 D ε2` (if the contract accepts, π2's
extractor outputs π1's stream, on which π1-rec4's recorded graph at π1's setup commitment, run with Keccak-f[1600],
accepts with its claims' Keccak-256s those of the claims the frame declares), from two named inputs:

* **`Pi2Layers D ε2`**: π2's circuit as the Lean compiler builds it from π1-rec4's recorded graph at each π1 setup
  commitment (`RecCircuit.compile` of `pi1GraphAt roots` at π1's contract IV, π1's claims `Data.hashed` hashed in the
  circuit), public limbs of its ports read off the statement (the public input and the proof: its frame words, the
  declared claims' Keccak-256s), and two layers on them:
  - `extraction` (**π2's Fiat–Shamir, openings and PIOP**, `Pi2Extraction`): if the contract accepts, some candidate
    of `W`'s committed word (as π2's extractor lists them) has witness values satisfying the circuit's relation
    (`RecPiop.Circuit.Satisfies`), but with probability `ε2 Q`;
  - `circuit` (**the circuit computes π1-rec4's graph and its claims' Keccak-256s**): a witness satisfying the
    circuit, for the public limbs of `(roots, input, proof)`, holds a π1 stream (`D.pi1Stream`, RecCircuit's
    `decodeStream`) on which the graph accepts with its claims hashing to the declared ones (RecCircuit's end
    theorem, its `ClaimHash` ports).
* **`DeclaredClaims D`**: on every outcome of π2's experiment the contract accepts, the proof declares as many π1
  claims as π1-rec4's graph makes (three).
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open scoped ENNReal

/-- **The contract declares π1's claims**: on every outcome of π2's knowledge-soundness experiment whose contract
accepts, the proof declares as many π1 claims as π1-rec4's graph (at any setup commitment) makes. -/
def DeclaredClaims (D : RecDeployment) : Prop :=
  ∀ (A : RecAdversary), ∀ z ∈ support (recSoundnessExperiment2 D A), (acc z) = true →
    (prf z).pi1Claims.length = RecGraphKeccak.Pi1.pi1GraphK4.calls.length

/-- **π2's extraction for a relation `Rel` of `W`'s candidates**: in π2's experiment, the contract accepts while no
candidate of `W`'s committed word (read off the setup's evaluations and the transcript, decoded as π2's extractor
decodes it) has witness values in `Rel`, with probability at most `ε2 Q`. -/
def Pi2Extraction (D : RecDeployment) (Rel : RecSetupRoots → Vector UInt8 32 → RecProof → (ℕ → K) → Prop)
    (ε2 : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : RecAdversary) (Q : ℕ), (∀ roots, QueryCostAtMost (A roots) permutationCallCost Q) →
    Pr{let z ← recSoundnessExperiment2 D A}[(acc z) = true ∧
      ¬ ∃ w ∈ outcomeCandidates D z, Rel (rts z) (inp z) (prf z) (witnessOf D (rts z) w)] ≤ ε2 Q

/-- **π2's layers**: π2's circuit as the Lean compiler builds it from π1-rec4's recorded graph at every π1 setup
commitment, the public limbs of its ports for a statement, π2's extraction for that circuit's relation, and the
circuit's corollary.

* `rootsAt`, `compiled`, `compile_ok`: the compiler's input (π1's roots' stream offsets, the graph at π1's setup
  commitment, π1's contract IV, the hashed claims) and output; checked by evaluation (`rec-real-check`), not in the
  kernel, and assumed at the setup commitments not evaluated;
* `stream_eq`: the deployment's π1 stream is the compiler's decoding of the witness's free bits, `streamW`;
* `pub`: port `J`'s public limbs, for the setup's roots, the public input and the proof (the statement's four words,
  the frame words' limbs, π1's roots' limbs and claims' elements where the contract encodes claims, zeros);
* `extraction`: π2's Fiat–Shamir layer, openings, PIOP and tables' layer;
* `circuit`: a satisfying witness holds a π1 stream π1-rec4's graph accepts, its claims hashing to the declared ones
  (`RecCircuit`'s end theorem). -/
structure Pi2Layers (D : RecDeployment) (ε2 : ℕ → ℝ≥0∞) where
  rootsAt : List ℕ
  compiled : UniKeccak.SetupRootsK → RecCircuit.Compiled
  compile_ok : ∀ roots,
    RecCircuit.compile (RecCircuit.ofRG (pi1GraphAt roots) rootsAt (D.pi1IvAt roots) Data.hashed) =
      .ok (compiled roots)
  stream_eq : ∀ roots (w : ℕ → K),
    D.pi1Stream w =
      ((compiled roots).streamW (RecCircuit.ofRG (pi1GraphAt roots) rootsAt (D.pi1IvAt roots) Data.hashed) w).toArray
  pub : RecSetupRoots → Vector UInt8 32 → RecProof → ℕ → List Primitives.F192
  extraction : Pi2Extraction D (fun roots input proof w ↦
    ((compiled roots.pi1).circuit.toPiop).Satisfies (pub roots input proof) (RecCircuit.emb w)) ε2
  circuit : ∀ (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) (w : ℕ → K),
    proof.pi1Claims.length = RecGraphKeccak.Pi1.pi1GraphK4.calls.length →
    ((compiled roots.pi1).circuit.toPiop).Satisfies (pub roots input proof) (RecCircuit.emb w) →
      Pi1GraphAccepts (pi1GraphAt roots.pi1) (D.pi1IvAt roots.pi1) input (D.pi1Stream w) proof.pi1Claims

/-- **π2's part, from π2's layers**: `RecKnowledgeSoundness2 D ε2`. -/
theorem recKnowledgeSoundness2_of_layers {D : RecDeployment} {ε2 : ℕ → ℝ≥0∞} (L : Pi2Layers D ε2)
    (hdecl : DeclaredClaims D) : RecKnowledgeSoundness2 D ε2 := by
  intro A Q hQ
  refine (prEvent_mono_of_support _ _ _ ?_).trans (L.extraction A Q hQ)
  rintro z hz ⟨hacc, hno⟩
  refine ⟨hacc, fun ⟨w, hw, hrel⟩ ↦ hno ?_⟩
  obtain ⟨s, hs, hsacc⟩ := recExtractFrom2_of_mem D (rts z) (inp z) _ (prf z) w hw
    (L.circuit _ _ _ _ (hdecl A z hz hacc) hrel)
  exact ⟨s, hs, hsacc⟩

end RecCompose

/-- info: 'RecCompose.recKnowledgeSoundness2_of_layers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.recKnowledgeSoundness2_of_layers
