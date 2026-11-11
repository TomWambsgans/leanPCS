-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from the previous protocol's prover bridge (`E2ECompleteness/ProverStaged.lean`,
-- `ProverBridge.lean`, `ProverAccept.lean`) to the deployed protocol. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the
-- two calls answered by functions (`totalImpl`).
import E2ECompleteness.PcsGrinding
import E2ECompleteness.PcsSizes

/-!
# The prover bridge on the staged run

At every hash function `H` and permutation `F`, on the deployed staged run (`stagedRun`): when the challenges
`(α, β, t, ρ)` avoid a degenerate set `bad` for which the honest tables satisfy the claims (**`HonestClaims bad`**:
at non-degenerate challenges the reduction returns claims, true of the honest tables),

* **`tailReduces`** (Red): the prover's reduction returns claims;
* **`tailAccepts`** (Acc): when the prover's tail returns a proof, the verifier accepts it;

by the WHIR opening's completeness (`pcsOpeningWithH_commitmentWithH`, `PcsOpening.lean`). The stages at
functions (`stageAG_id`, `stageBG_id`, `stageCG_id`) are their stretches of the prover; the prover's reduction is
the chain (`reduceWithH_eq_chain`), at the very states of the staged run.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Prover (Tree)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript
open E2ECompleteness (runAt)
open scoped ENNReal

set_option autoImplicit false

-- The membership circuit is a closed term of `2^22` rows: never evaluate it.
attribute [local irreducible] PcsQuotient.membershipBuilder

namespace E2ECompleteness.Pcs

/-! ## The algebraic fact -/

/-- **The honest tables satisfy the three claims** at the challenges outside `bad`: for every `μ` the reduction
returns claims, true of the witness table, the wiring table and the quotient table at `α, β, μ`. -/
def HonestClaims (bad : Secret → Coins → Finset (E × E × E × E)) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w → ∀ (coins : Coins) (α β μ t ρ : E),
    (α, β, t, ρ) ∉ bad w coins →
    ∃ cl : Claims,
      claimsAt 22 stmt α β μ t ρ (valuesAt (membership logRows) (cellsOf w) coins t).1
        (valuesAt (membership logRows) (cellsOf w) coins t).2 = some cl ∧
      tableEval (witnessTable (membership logRows) (cellsOf w) coins) cl.witness.point =
        cl.witness.value ∧
      tableEval (membership logRows).wiringTable cl.wiring.point = cl.wiring.value ∧
      tableEval (quotientTable (membership logRows) stmt (cellsOf w) coins α β μ) cl.copy.point =
        cl.copy.value

/-- **The claims' points**: `W`'s and the wiring's `m` coordinates, `T`'s `m + 4`. -/
theorem claimsAt_lengths {logRows : ℕ} {stmt : Statement} {α β μ t ρ : E} {v : Vector E 3} {next : E}
    {cl : Claims} (h : claimsAt logRows stmt α β μ t ρ v next = some cl) (hm : 2 ≤ cellVars logRows) :
    cl.witness.point.length = cellVars logRows ∧ cl.wiring.point.length = cellVars logRows ∧
      cl.copy.point.length = cellVars logRows + 4 := by
  unfold claimsAt at h
  simp only at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    subst h
    simp only [copyPoint, List.length_append, List.length_cons, List.length_nil,
      List.length_take, List.length_drop, List.length_map, List.length_range]
    exact ⟨by omega, by omega, trivial⟩

/-! ## The stages at functions -/

theorem id_bind' {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

theorem id_pure' {α : Type} (a : α) : (pure a : Id α) = a := rfl

section Stages

variable (H : Bytes → Digest) (F : KeccakState → KeccakState)

theorem runAt_reduceWithH (lr : ℕ) (index : Commitment) (stmt : Statement) (p : ReductionProof) :
    runAt H F (reduceWithH callKeccak256 lr index stmt p) = reduceWithH (m := Id) H lr index stmt p := by
  rw [runAt, simulateQ_reduceWithH, implH_totalImpl]

theorem runAt_verifyWithH (lr : ℕ) (index : Commitment) (stmt : Statement) (π : PcsQuotient.Proof) :
    runAt H F (verifyWithH callKeccak256 callKeccakF1600 lr index stmt π) =
      verifyWithH (m := Id) H F lr index stmt π := by
  rw [runAt, simulateQ_verifyWithH, implH_totalImpl, implF_totalImpl]

/-- **Stage A at functions.** -/
theorem stageAG_id (setup : OracleComp KeccakCalls (Tree × Commitment)) (C : Circuit)
    (cells₀ : Array K) (coins : Coins) (stmt : Statement) :
    runAt H F (stageAG setup C cells₀ coins stmt) =
      ((runAt H F (Prod.snd <$> setup),
        (commitmentWithH (m := Id) H (cellVars C.logRows) C.wiringTable).1,
        (commitmentWithH (m := Id) H (cellVars C.logRows) C.wiringTable).2,
        (commitmentWithH (m := Id) H (cellVars C.logRows) (witnessTable C cells₀ coins)).1,
        (commitmentWithH (m := Id) H (cellVars C.logRows) (witnessTable C cells₀ coins)).2),
      H (label (commitmentWithH (m := Id) H (cellVars C.logRows) C.wiringTable).2 stmt),
      .of (commitmentWithH (m := Id) H (cellVars C.logRows) (witnessTable C cells₀ coins)).2) := by
  simp only [stageAG, runAt, simulateQ_bind, simulateQ_pure, simulateQ_commitmentWithH,
    LeanVM.Protocol.Compile.Rom.simulateQ_queryH, implH_totalImpl]
  rfl

/-- **Stage B at functions.** -/
theorem stageBG_id (C : Circuit) (cells₀ : Array K) (coins : Coins) (stmt : Statement) (a : AuxA)
    (s₁ s₂ s₃ : Digest) :
    runAt H F (stageBG C cells₀ coins stmt a s₁ s₂ s₃) =
      (((commitmentWithH (m := Id) H (cellVars C.logRows + 4) (tableAt C cells₀ coins stmt s₁ s₂ s₃)).1,
        (commitmentWithH (m := Id) H (cellVars C.logRows + 4) (tableAt C cells₀ coins stmt s₁ s₂ s₃)).2),
      .of (commitmentWithH (m := Id) H (cellVars C.logRows + 4) (tableAt C cells₀ coins stmt s₁ s₂ s₃)).2) := by
  simp only [stageBG, runAt, simulateQ_bind, simulateQ_pure, simulateQ_commitmentWithH,
    implH_totalImpl]
  rfl

/-- **Stage C at functions.** -/
theorem stageCG_id (C : Circuit) (cells₀ : Array K) (coins : Coins) (stmt : Statement) (a : AuxA)
    (b : AuxB) (s₁ s₂ s₃ s₄ : Digest) :
    runAt H F (stageCG C cells₀ coins stmt a b s₁ s₂ s₃ s₄) =
      let s₀' := H (label a.2.2.1 stmt)
      let s₁' := H (in3 s₀' (.of a.2.2.2.2))
      let s₂' := H (digestBytes s₁')
      let s₃' := H (digestBytes s₂')
      let s₄' := H (in3 s₃' (.of b.2))
      ((s₁', s₂', s₃', s₄'), s₄', valuesAt C cells₀ coins (challengeOf s₄)) := by
  simp only [stageCG, runAt, simulateQ_bind, simulateQ_pure,
    LeanVM.Protocol.Compile.Rom.simulateQ_queryH, implH_totalImpl]
  rfl

end Stages

/-! ## The reduction at functions, on the run's states -/

/-- **The prover's reduction at functions**: on commitments it computed, at the run's states, the reduction
returns the claims `claimsAt` gives at the run's challenges. -/
theorem reduce_core (H : Bytes → Digest) (stmt : Statement) (index wCom tCom : Commitment)
    (s₀ s₁ s₂ s₃ s₄ s₅ : Digest) (rv : Vector E 3 × E)
    (h₀ : H (label index stmt) = s₀) (h₁ : H (in3 s₀ (.of wCom)) = s₁) (h₂ : H (digestBytes s₁) = s₂)
    (h₃ : H (digestBytes s₂) = s₃) (h₄ : H (in3 s₃ (.of tCom)) = s₄) (h₅ : H (in4 s₄ rv) = s₅) :
    reduceWithH (m := Id) H 22 index stmt ⟨.of wCom, .of tCom, rv.1, rv.2⟩ =
      (claimsAt 22 stmt (challengeOf s₁) (challengeOf s₂) (challengeOf s₃) (challengeOf s₄)
        (challengeOf s₅) rv.1 rv.2).map fun claims ↦ ⟨⟨wCom, tCom⟩, claims⟩ := by
  rw [reduceWithH_eq_chain (m := Id) H (by decide : Supported 22)]
  show (pure (Option.map _ (claimsAt 22 stmt (challengeOf (H (in3 (H (label index stmt)) _)))
    _ _ _ _ _ _)) : Id _) = _
  rw [h₀, h₁, h₂, h₃, h₄, show (rv.1, rv.2) = rv from rfl, h₅]
  rfl

/-- All openings of a list accepted: the check accepts. -/
theorem checkAll_true (H : Bytes → Digest) (F : KeccakState → KeccakState) :
    ∀ l : List (Commitment × Claim × Compile.Proof),
      (∀ e ∈ l, pcsOpeningWithH (m := Id) H F e.1 e.2.1 e.2.2 = true) →
      checkAllWithH (m := Id) H F l = true
  | [], _ => rfl
  | (c, claim, proof) :: rest, h => by
    have h1 := h (c, claim, proof) (List.mem_cons_self ..)
    simp only at h1
    show (if !(pcsOpeningWithH (m := Id) H F c claim proof) then (pure false : Id Bool)
      else checkAllWithH (m := Id) H F rest) = true
    rw [h1]
    exact checkAll_true H F rest fun e he ↦ h e (List.mem_cons_of_mem _ he)

/-- **An honest opening of a true claim on a committed table is accepted.** -/
theorem opening_ok (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel n : ℕ)
    (hr : minVars ≤ n ∧ n ≤ maxVars) (table : Array K) (hsz : table.size = 2 ^ n) (claim : Claim)
    (hp : claim.point.length = n) (hval : tableEval table claim.point = claim.value)
    {π : Compile.Proof}
    (hπ : proveClaimWithH (m := Id) H F fuel (commitmentWithH (m := Id) H n table).1 table
      (commitmentWithH (m := Id) H n table).2 claim = some π) :
    pcsOpeningWithH (m := Id) H F (commitmentWithH (m := Id) H n table).2 claim π = true :=
  pcsOpeningWithH_commitmentWithH H F fuel hr table hsz claim hp hval hπ

/-- The setup's commitment is the prover's index commitment. -/
theorem setup_index (H : Bytes → Digest) (F : KeccakState → KeccakState) :
    runAt H F (Prod.snd <$> setupWithH callKeccak256) =
      (commitmentWithH (m := Id) H (cellVars (membership logRows).logRows)
        (membership logRows).wiringTable).2 := by
  rw [runAt, simulateQ_map, simulateQ_setupWithH, implH_totalImpl]
  rfl

theorem cellVars_membership : cellVars (membership logRows).logRows = 24 := rfl

/-! ## (Red), (Acc) -/

section Bridge

variable (bad : Secret → Coins → Finset (E × E × E × E)) (hC : HonestClaims bad)
include hC

/-- **(Red)** on the deployed instance. -/
theorem tailReduces (stmt : Statement) (w : Secret) (hrel : Relation stmt w) (coins : Coins) :
    TailReducesG (setupWithH callKeccak256) (membership logRows) (cellsOf w) coins stmt (bad w coins) := by
  intro H F x s₁ s₂ s₃ y s₄ z s₅ hst hgood
  obtain ⟨hA, h₁, h₂, h₃, hB, h₄, hCz, h₅⟩ := hst
  rw [stageAG_id] at hA
  rw [stageBG_id] at hB
  subst hA hB
  rw [stageCG_id] at hCz
  subst hCz
  dsimp only at h₁ h₄ h₅ ⊢
  obtain ⟨cl, hcl, -⟩ := hC stmt w hrel coins _ _ (challengeOf s₃) _ _ hgood
  simp only [claimsOf, h₁, h₂, h₃, h₄]
  simp only [membership_logRows]
  rw [hcl]
  exact ⟨_, rfl⟩

set_option maxHeartbeats 2000000 in
/-- **(Acc)** on the deployed instance. -/
theorem tailAccepts (stmt : Statement) (w : Secret) (hrel : Relation stmt w) (coins : Coins) :
    TailAcceptsG (setupWithH callKeccak256) (membership logRows) (cellsOf w) coins nonceFuel logRows
      stmt (bad w coins) := by
  intro H F x s₁ s₂ s₃ y s₄ z s₅ hst hgood π hπ
  obtain ⟨hA, h₁, h₂, h₃, hB, h₄, hCz, h₅⟩ := hst
  rw [stageAG_id] at hA
  rw [stageBG_id] at hB
  generalize hcI : commitmentWithH (m := Id) H (cellVars (membership logRows).logRows)
    (membership logRows).wiringTable = cI at hA
  generalize hcW : commitmentWithH (m := Id) H (cellVars (membership logRows).logRows)
    (witnessTable (membership logRows) (cellsOf w) coins) = cW at hA
  generalize hcT : commitmentWithH (m := Id) H (cellVars (membership logRows).logRows + 4)
    (tableAt (membership logRows) (cellsOf w) coins stmt s₁ s₂ s₃) = cT at hB
  subst hA hB
  rw [stageCG_id] at hCz
  subst hCz
  dsimp only at h₁ h₄ h₅ hπ ⊢
  obtain ⟨cl, hcl, hW, hσ, hT⟩ := hC stmt w hrel coins _ _ (challengeOf s₃) _ _ hgood
  have hlen := claimsAt_lengths hcl (by decide)
  have hred := reduce_core H stmt cI.2 cW.2 cT.2 _ s₁ s₂ s₃ s₄ s₅
    (valuesAt (membership logRows) (cellsOf w) coins (challengeOf s₄)) rfl h₁ h₂ h₃ h₄
    (by rw [h₁, h₂, h₃, h₄] at h₅; exact h₅)
  rw [hcl, Option.map_some] at hred
  -- The prover's tail.
  simp only [proverTailG, claimsOf, proofOf, h₁, h₂, h₃, h₄] at hπ
  simp only [membership_logRows] at hπ
  rw [hcl] at hπ
  simp only [Option.map_some, openTailH, realPcsH, runAt, simulateQ_bind, simulateQ_pure,
    simulateQ_proveClaimWithH, implH_totalImpl, implF_totalImpl, id_bind', id_pure'] at hπ
  split at hπ
  swap
  · simp at hπ
  rename_i oW hoW
  simp only [id_bind', id_pure', simulateQ_bind, simulateQ_pure, simulateQ_proveClaimWithH,
    implH_totalImpl, implF_totalImpl] at hπ
  split at hπ
  swap
  · simp at hπ
  rename_i oσ hoσ
  simp only [id_bind', id_pure', simulateQ_bind, simulateQ_pure, simulateQ_proveClaimWithH,
    implH_totalImpl, implF_totalImpl] at hπ
  split at hπ
  swap
  · simp at hπ
  rename_i oT hoT
  simp only [id_pure', simulateQ_pure, Option.some.injEq] at hπ
  subst hπ
  -- The verifier.
  have hidx : runAt H F (Prod.snd <$> setupWithH callKeccak256) = cI.2 := by
    rw [← hcI]; exact setup_index H F
  rw [runAt_verifyWithH, hidx]
  unfold verifyWithH
  dsimp only
  erw [hred]
  simp only [id_bind']
  have hsT := quotientTable_size (membership logRows) stmt (cellsOf w) coins (challengeOf s₁)
    (challengeOf s₂) (challengeOf s₃)
  subst hcI hcW hcT
  apply checkAll_true
  intro e he
  simp only [Reduced.checks, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact opening_ok H F _ _ (by decide) _ (witnessTable_size w coins) _
      hlen.1 hW hoW
  · exact opening_ok H F _ _ (by decide) _ wiringTable_size _
      hlen.2.1 hσ hoσ
  · exact opening_ok H F _ _ (by decide) _ hsT _
      hlen.2.2 hT hoT

end Bridge

end E2ECompleteness.Pcs
