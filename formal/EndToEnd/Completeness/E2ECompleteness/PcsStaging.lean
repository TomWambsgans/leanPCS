-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/Staging.lean` (the previous protocol's three stages) to the PCS claims'
-- four challenges. The roots' round trip (`rootOfHalves_rootHalves`) follows the `formal/Implementation`
-- proof of the same fact (branch `lean-mem-evm`), here from `E2ECompleteness/Regular.lean`'s bytes.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the lanes' bytes (`leLane_lanesBytes`, `common/Common/Lanes.lean`).
import E2ECompleteness.PcsExperiment
import E2ECompleteness.PcsChain
import E2ECompleteness.Regular

/-!
# The two-call experiment in the chain's shape (the PCS claims)

`expH stmt w coins` (`PcsExperiment.lean`: the setup, the honest prover, the verifier, with Keccak-256
and Keccak-f[1600] the calls) is the chain's shape `staged4 challengeOf A B C D` (`PcsChain.lean`), its
verdict the first component (`expH_eq_staged`):

* `stageA`: the setup, the prover's index and witness commitments, the label's hash `s₀`; it returns
  the witness commitment's three scalars;
* `stageB`: from `α, β, γ` (the low bits of `s₁, s₂, s₃`) the three parts and their commitments; it
  returns their nine scalars;
* `stageC`: from `t` (the low bits of `s₄`) the values, then the prover's reduction up to `ρ`'s query:
  the label, `α`'s, `β`'s, `γ`'s and `t`'s queries again (a function answers them as before); it
  returns `t`'s state and the five values;
* `stageD`: from `ρ`, the prover's claims, its second reduction, the six openings, and the verifier.

The prover's reduction is the chain on commitments it computed (`reduceWithH_eq_chain`: a root's
halves always name the root, `rootOfHalves_rootHalves`). Everything is stated for **any setup, circuit
and cells** (`…G`) of a supported size and then instantiated.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Prover (Tree)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-! ## Roots -/

theorem beBytes_beWord (b : List UInt8) (s : ℕ) :
    beBytes (beWord b s) = [b.getD s 0, b.getD (s + 1) 0, b.getD (s + 2) 0, b.getD (s + 3) 0,
      b.getD (s + 4) 0, b.getD (s + 5) 0, b.getD (s + 6) 0, b.getD (s + 7) 0] := by
  rw [E2ECompleteness.beWord_drop, beBytes, E2ECompleteness.wordBytes_beWord]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem list32_ext (b b' : List UInt8) (hb : b.length = 32) (hb' : b'.length = 32)
    (h : ∀ i < 32, b'.getD i 0 = b.getD i 0) : b' = b := by
  refine List.ext_getElem (by rw [hb, hb']) fun i h1 h2 ↦ ?_
  have := h i (by omega)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-- **A root's halves name the root** (`transcript.rs`'s `halves_root ∘ root_halves`). -/
theorem rootOfHalves_rootHalves (d : Digest) : rootOfHalves (rootHalves d) = some d := by
  have hl := length_digestBytes d
  have hb : (Digest.toBytes d).toList = digestBytes d := rfl
  have hlb : digestBytes d = LeanVM.Rpm.lanesBytes d.toList := rfl
  have l1 : ∀ x y : K, (E.ofLimbs x y 0).limb 1 = y := fun x y ↦ by
    rw [LeanVM.Parameters.limb_ofLimbs]; rfl
  have l0 : ∀ x y : K, (E.ofLimbs x y 0).limb 0 = x := fun x y ↦ by
    rw [LeanVM.Parameters.limb_ofLimbs]; rfl
  have e : beBytes (K.ofLane (beWord (digestBytes d) 0)).lane ++
      beBytes (K.ofLane (beWord (digestBytes d) 8)).lane ++
      beBytes (K.ofLane (beWord (digestBytes d) 16)).lane ++
      beBytes (K.ofLane (beWord (digestBytes d) (16 + 8))).lane = digestBytes d := by
    refine list32_ext _ _ hl (by simp [beBytes, LeanVM.Rpm.wordBytes_len]) fun i hi ↦ ?_
    show (beBytes (beWord (digestBytes d) 0) ++ beBytes (beWord (digestBytes d) 8) ++
      beBytes (beWord (digestBytes d) 16) ++ beBytes (beWord (digestBytes d) (16 + 8))).getD i 0 = _
    rw [beBytes_beWord, beBytes_beWord, beBytes_beWord, beBytes_beWord]
    interval_cases i <;> rfl
  unfold rootOfHalves rootHalves halves
  rw [ite_eq_left_iff.mpr (fun h ↦ absurd ⟨rfl, rfl⟩ h)]
  simp only [hb, l1, l0, Nat.mul_zero, Nat.zero_add, Nat.mul_one, e]
  congr 1
  apply Vector.ext
  intro i hi
  have hL : ∀ j (hj : j < 4), leLane (digestBytes d) j = d.toList[j]'(by simpa using hj) :=
      fun j hj ↦ by
    rw [hlb, LeanVM.Rpm.leLane_lanesBytes _ _ (by simp; omega)]
  interval_cases i
  · exact (hL 0 (by norm_num)).trans (by simp)
  · exact (hL 1 (by norm_num)).trans (by simp)
  · exact (hL 2 (by norm_num)).trans (by simp)
  · exact (hL 3 (by norm_num)).trans (by simp)

/-! ## The prover's reduction is the chain -/

theorem foldl_absorb (l : List E) (c : Chain) : l.foldl Chain.absorb c = ⟨c.state, c.pending ++ l⟩ := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => simp [List.foldl_cons, ih, Chain.absorb, List.append_assoc]

theorem readCommitment_of (c : Chain) (com : Commitment) :
    readCommitment c (CommitmentScalars.of com) = some (com, c.absorbCommitment (.of com)) := by
  simp [readCommitment, CommitmentScalars.of, rootOfHalves_rootHalves, Chain.absorbCommitment]

/-- **The reduction on commitments it names** is the chain: the label's hash, then `α`'s, `β`'s, `γ`'s,
`t`'s and `ρ`'s queries, then the claims. -/
theorem reduceWithH_eq_chain {m : Type → Type} [Monad m] [LawfulMonad m] (H : Bytes → m Digest)
    {lr : ℕ} (hS : Supported lr) (index : Commitment) (stmt : Statement) (cw ch cq cg : Commitment)
    (a : Vector E 4) (next qv gv : E) :
    reduceWithH H lr index stmt ⟨.of cw, .of ch, .of cq, .of cg, a, next, qv, gv⟩ = do
      let s₀ ← H (label index stmt)
      let s₁ ← H (in3 s₀ (.of cw))
      let s₂ ← H (digestBytes s₁)
      let s₃ ← H (digestBytes s₂)
      let s₄ ← H (in9 s₃ (.of ch, .of cq, .of cg))
      let s₅ ← H (in5 s₄ (a, next))
      return (claimsAt lr stmt (challengeOf s₁) (challengeOf s₂) (challengeOf s₃) (challengeOf s₄)
        (challengeOf s₅) a next qv gv).map fun claims ↦ ⟨⟨cw, ch, cq, cg⟩, claims⟩ := by
  simp only [reduceWithH, hS, not_true_eq_false, ite_false, startWithH, squeezeWithH,
    readCommitment_of, bind_assoc, pure_bind, foldl_absorb]
  simp only [Chain.absorbCommitment, Chain.absorb, List.nil_append, List.cons_append,
    List.append_nil, in3, in9, in5, CommitmentScalars.stream, CommitmentScalars.of,
    List.flatMap_nil, List.flatMap_cons, List.flatMap_append]

/-! ## The stages -/

/-- What the first stage hands on: the setup's commitment, the index tree and commitment, the witness
tree and commitment. -/
abbrev AuxA : Type := Commitment × Tree × Commitment × Tree × Commitment

/-- What the second stage hands on: the three parts' trees and commitments. -/
abbrev AuxB : Type := Tree × Commitment × Tree × Commitment × Tree × Commitment

/-- What the third stage hands on: the prover's own chain states `s₁ … s₄`. -/
abbrev AuxC : Type := Digest × Digest × Digest × Digest

section Stages

variable (setup : OracleComp KeccakCalls (Tree × Commitment)) (circuit : Circuit) (cells₀ : Array K)
  (coins : Coins) (fuel vLogRows : ℕ) (stmt : Statement)

/-- **Stage A**: the setup, the prover's index and witness commitments, the label's hash `s₀`. -/
def stageAG : OracleComp KeccakCalls (AuxA × Digest × CommitmentScalars) := do
  let idx ← Prod.snd <$> setup
  let (indexTree, index) ← commitmentWithH callKeccak256 (cellVars circuit.logRows)
    circuit.wiringTable
  let (wTree, wCom) ← commitmentWithH callKeccak256 (cellVars circuit.logRows + 1)
    (witnessTable circuit cells₀ coins)
  let s₀ ← callKeccak256 (label index stmt)
  return ((idx, indexTree, index, wTree, wCom), s₀, .of wCom)

/-- The quotient table's parts at the challenges of `s₁, s₂, s₃`. -/
def tablesAt (s₁ s₂ s₃ : Digest) : Array K × Array K × Array K :=
  quotientTables circuit cells₀ coins (challengeOf s₁) (challengeOf s₂) (challengeOf s₃)

/-- **Stage B**: from `s₁, s₂, s₃` the parts and their commitments. -/
def stageBG (_a : AuxA) (s₁ s₂ s₃ : Digest) : OracleComp KeccakCalls (AuxB × Scalars9) := do
  let T := tablesAt circuit cells₀ coins s₁ s₂ s₃
  let (hTree, hCom) ← commitmentWithH callKeccak256 (cellVars circuit.logRows + 3) T.1
  let (qTree, qCom) ← commitmentWithH callKeccak256 (cellVars circuit.logRows + 4) T.2.1
  let (gTree, gCom) ← commitmentWithH callKeccak256 (cellVars circuit.logRows + 1) T.2.2
  return ((hTree, hCom, qTree, qCom, gTree, gCom), (.of hCom, .of qCom, .of gCom))

/-- **Stage C**: from `s₄` the values, then the prover's reduction up to `ρ`'s query. -/
def stageCG (a : AuxA) (b : AuxB) (_s₁ _s₂ _s₃ s₄ : Digest) :
    OracleComp KeccakCalls (AuxC × Digest × (Vector E 4 × E)) := do
  let s₀' ← callKeccak256 (label a.2.2.1 stmt)
  let s₁' ← callKeccak256 (in3 s₀' (.of a.2.2.2.2))
  let s₂' ← callKeccak256 (digestBytes s₁')
  let s₃' ← callKeccak256 (digestBytes s₂')
  let s₄' ← callKeccak256 (in9 s₃' (.of b.2.1, .of b.2.2.2.1, .of b.2.2.2.2.2))
  return ((s₁', s₂', s₃', s₄'), s₄', rowValues circuit cells₀ coins (challengeOf s₄))

/-- The prover's reduction proof before `Q`'s and `G`'s values. -/
def proof₀Of (a : AuxA) (b : AuxB) (s₄ : Digest) : ReductionProof :=
  ⟨.of a.2.2.2.2, .of b.2.1, .of b.2.2.2.1, .of b.2.2.2.2.2,
    (rowValues circuit cells₀ coins (challengeOf s₄)).1,
    (rowValues circuit cells₀ coins (challengeOf s₄)).2, 0, 0⟩

/-- The prover's first claims, from its chain and `ρ`'s state `s₅`. -/
def claims₀Of (a : AuxA) (b : AuxB) (c : AuxC) (s₄ s₅ : Digest) : Option Reduced :=
  (claimsAt circuit.logRows stmt (challengeOf c.1) (challengeOf c.2.1) (challengeOf c.2.2.1)
      (challengeOf c.2.2.2) (challengeOf s₅) (rowValues circuit cells₀ coins (challengeOf s₄)).1
      (rowValues circuit cells₀ coins (challengeOf s₄)).2 0 0).map
    fun claims ↦ ⟨⟨a.2.2.2.2, b.2.1, b.2.2.2.1, b.2.2.2.2.2⟩, claims⟩

/-- The prover's last stretch from `ρ`: its claims, its second reduction, the six openings. -/
def proverTailG (a : AuxA) (b : AuxB) (c : AuxC) (s₁ s₂ s₃ s₄ s₅ : Digest) :
    OracleComp KeccakCalls (Option PcsQuotient.Proof) := do
  let T := tablesAt circuit cells₀ coins s₁ s₂ s₃
  let some r₀ := claims₀Of circuit cells₀ coins stmt a b c s₄ s₅ | return none
  let proof : ReductionProof :=
    { proof₀Of circuit cells₀ coins a b s₄ with qValue := tableEval T.2.1 r₀.claims.q.point,
                                                  gValue := tableEval T.2.2 r₀.claims.g.point }
  let some r ← reduceWithH callKeccak256 circuit.logRows a.2.2.1 stmt proof | return none
  let some oW ← proveClaimWithH callKeccak256 callKeccakF1600 fuel a.2.2.2.1
    (witnessTable circuit cells₀ coins) r.commitments.witness r.claims.witness | return none
  let some oσ ← proveClaimWithH callKeccak256 callKeccakF1600 fuel a.2.1 circuit.wiringTable a.2.2.1
    r.claims.wiring | return none
  let some oH ← proveClaimWithH callKeccak256 callKeccakF1600 fuel b.1 T.1 r.commitments.h
    r.claims.h | return none
  let some oQ ← proveClaimWithH callKeccak256 callKeccakF1600 fuel b.2.2.1 T.2.1 r.commitments.q
    r.claims.q | return none
  let some oG ← proveClaimWithH callKeccak256 callKeccakF1600 fuel b.2.2.2.2.1 T.2.2
    r.commitments.g r.claims.g | return none
  let some oS ← proveClaimWithH callKeccak256 callKeccakF1600 fuel b.1 T.1 r.commitments.h
    r.claims.sum | return none
  return some ⟨proof, ⟨oW, oσ, oH, oQ, oG, oS⟩⟩

/-- **Stage D**: the prover's tail, then the verifier. -/
def stageDG (a : AuxA) (b : AuxB) (c : AuxC) (s₁ s₂ s₃ s₄ s₅ : Digest) :
    OracleComp KeccakCalls Bool := do
  match ← proverTailG circuit cells₀ coins fuel stmt a b c s₁ s₂ s₃ s₄ s₅ with
  | none => return false
  | some proof => verifyWithH callKeccak256 callKeccakF1600 vLogRows a.1 stmt proof

/-- The two-call experiment for any setup, circuit and cells. -/
def expHG : OracleComp KeccakCalls Bool := do
  let idx ← Prod.snd <$> setup
  match ← proveWithH callKeccak256 callKeccakF1600 fuel circuit stmt cells₀ coins with
  | none => return false
  | some proof => verifyWithH callKeccak256 callKeccakF1600 vLogRows idx stmt proof

/-- The staged run for any setup, circuit and cells. -/
def stagedRunG : OracleComp KeccakCalls (Bool × (E × E × E × E)) :=
  staged4 challengeOf (stageAG setup circuit cells₀ coins stmt) (stageBG circuit cells₀ coins)
    (stageCG circuit cells₀ coins stmt) (stageDG circuit cells₀ coins fuel vLogRows stmt)

/-- **For any setup, circuit and cells of a supported size, the two-call experiment is the staged
run's verdict.** -/
theorem expHG_eq_staged (hS : Supported circuit.logRows) :
    expHG setup circuit cells₀ coins fuel vLogRows stmt =
      (·.1) <$> stagedRunG setup circuit cells₀ coins fuel vLogRows stmt := by
  simp only [expHG, proveWithH, proveWithPcsH, realPcsH, stagedRunG, staged4, stageAG, stageBG,
    stageCG, stageDG, proverTailG, startWithH, squeezeWithH, bind_assoc, pure_bind, map_bind,
    map_pure, proof₀Of, claims₀Of, tablesAt, reduceWithH_eq_chain _ hS]
  simp only [in3, in9, in5, Chain.absorbCommitment, Chain.absorb, CommitmentScalars.stream,
    List.nil_append, List.cons_append, List.append_nil, List.flatMap_nil, List.flatMap_cons,
    List.flatMap_append]
  refine bind_congr fun _ ↦ bind_congr fun _ ↦ bind_congr fun _ ↦ bind_congr fun _ ↦
    bind_congr fun _ ↦ bind_congr fun _ ↦ bind_congr fun _ ↦ bind_congr fun _ ↦
    bind_congr fun _ ↦ bind_congr fun _ ↦ bind_congr fun _ ↦ bind_congr fun _ ↦
    bind_congr fun _ ↦ bind_congr fun _ ↦ bind_congr fun _ ↦ bind_congr fun _ ↦
    bind_congr fun _ ↦ bind_congr fun o ↦ ?_
  rcases o with _ | proof <;> simp

end Stages

/-! ## The deployed instance -/

/-- The deployed circuit's cells for a secret (the random rows zero; the prover fills them). -/
def cellsOf (w : Secret) : Array K := (membership logRows).cells (membershipInputs w)

/-- **The staged run** of the deployed experiment. -/
def stagedRun (stmt : Statement) (w : Secret) (coins : Coins) :
    OracleComp KeccakCalls (Bool × (E × E × E × E)) :=
  stagedRunG (setupWithH callKeccak256) (membership logRows) (cellsOf w) coins nonceFuel logRows stmt

theorem membership_logRows : (membership logRows).logRows = 22 := rfl

theorem supported_membership : Supported (membership logRows).logRows := by
  rw [membership_logRows]; decide

/-- **The two-call experiment is the staged run's verdict.** -/
theorem expH_eq_staged (stmt : Statement) (w : Secret) (coins : Coins) :
    expH stmt w coins = (·.1) <$> stagedRun stmt w coins :=
  expHG_eq_staged _ _ _ _ _ _ _ supported_membership

end E2ECompleteness.Pcs
