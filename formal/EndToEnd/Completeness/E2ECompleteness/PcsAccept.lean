-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from the previous protocol's prover bridge (`E2ECompleteness/ProverStaged.lean`,
-- `ProverBridge.lean`, `ProverAccept.lean`) to the PCS claims. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the
-- two calls answered by functions (`totalImpl`).
import E2ECompleteness.PcsGrinding
import E2ECompleteness.PcsBad
import E2ECompleteness.PcsCircuit

/-!
# The prover bridge on the staged run (the PCS claims)

At every hash function `H` and permutation `F`, on the deployed staged run (`stagedRun`): when the challenges
`(α, β, t, ρ)` avoid the degenerate set `badSet` (`PcsBad.lean`, for the honest first message of the witness and
the coins),

* **`tailReduces`** (Red): the prover's two reductions return claims;
* **`tailAccepts`** (Acc): when the prover's tail returns a proof, the verifier accepts it;

from the algebraic fact **`HonestClaims`** (the honest tables satisfy the six claims, `PcsClaims.lean`) and the
WHIR opening's completeness (`pcsOpeningWithH_commitmentWithH`, `PcsOpening.lean`). The stages at functions
(`stageAG_id`, `stageBG_id`, `stageCG_id`) are their stretches of the prover; the prover's reductions are
the chain (`reduceWithH_eq_chain`), at the very states of the staged run.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Prover (Tree)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript
open E2ECompleteness (runAt)
open QuotientSecurity Polynomial
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-! ## The witness, the degenerate challenges -/

/-- The deployed cells of a witness, with the random rows filled, as a table on the cells' bits. -/
def cellFn (w : Secret) (coins : Coins) : (Fin (22 + 2) → Bool) → K :=
  fun b ↦ (cellsR (membership logRows) (cellsOf w) coins).getD (Completeness.idx b) 0

/-- The honest first message (F1's four row polynomials) of a witness and coins. -/
noncomputable def gW (w : Secret) (coins : Coins) : Fin 4 → E[X] :=
  witnessOfTable fun b ↦ algebraMap K E (Completeness.witnessTable deployedBasis (cellFn w coins)
    coins.masks b)

open Classical in
/-- **The degenerate challenges** of a witness and coins (`BadP4`). -/
noncomputable def badSet (w : Secret) (coins : Coins) : Finset (E × E × E × E) :=
  Finset.univ.filter fun x ↦ BadP4 Completeness.deployedInstanceE (gW w coins) x

theorem badSet_density (w : Secret) (coins : Coins) :
    ((badSet w coins).card : ℝ≥0∞) / 2 ^ 768 ≤ (19 * 2 ^ 24 + 31 : ℝ≥0∞) / 2 ^ 192 := by
  classical
  exact badP4_fraction_le _ _ (Completeness.natDegree_witnessOfTable_le (algebraMap K E) deployedBasis
    _ coins.masks)

/-! ## The algebraic fact -/

/-- **The honest tables satisfy the six claims** at non-degenerate challenges: for every value of `Q`'s and
`G`'s claims the reduction returns claims (`cl`), whose points do not depend on those values; at `Q`'s and
`G`'s own values the six claims hold of the tables, with points of the tables' lengths. Proved in
`PcsClaims.lean` (`honestClaims`). -/
def HonestClaims : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w → ∀ (coins : Coins) (α β γ t ρ : E),
    (α, β, t, ρ) ∉ badSet w coins →
    ∃ cl : E → E → Claims,
      (∀ qv gv, claimsAt 22 stmt α β γ t ρ (rowValues (membership logRows) (cellsOf w) coins t).1
        (rowValues (membership logRows) (cellsOf w) coins t).2 qv gv = some (cl qv gv)) ∧
      (∀ qv gv, (cl qv gv).q.point = (cl 0 0).q.point ∧ (cl qv gv).g.point = (cl 0 0).g.point) ∧
      (let T := quotientTables (membership logRows) (cellsOf w) coins α β γ
       let c := cl (tableEval T.2.1 (cl 0 0).q.point) (tableEval T.2.2 (cl 0 0).g.point)
       (c.witness.point.length = 25 ∧
          tableEval (witnessTable (membership logRows) (cellsOf w) coins) c.witness.point =
            c.witness.value) ∧
       (c.wiring.point.length = 24 ∧
          tableEval (membership logRows).wiringTable c.wiring.point = c.wiring.value) ∧
       (c.h.point.length = 27 ∧ tableEval T.1 c.h.point = c.h.value) ∧
       (c.q.point.length = 28 ∧ tableEval T.2.1 c.q.point = c.q.value) ∧
       (c.g.point.length = 25 ∧ tableEval T.2.2 c.g.point = c.g.value) ∧
       (c.sum.point.length = 27 ∧ tableEval T.1 c.sum.point = c.sum.value))

/-! ## The stages at functions -/

theorem id_bind' {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

theorem id_pure' {α : Type} (a : α) : (pure a : Id α) = a := rfl

section Stages

variable (H : Bytes → Digest) (F : KeccakState → KeccakState)

theorem runAt_commitmentWithH (μ : ℕ) (T : Array K) :
    runAt H F (commitmentWithH callKeccak256 μ T) = commitmentWithH (m := Id) H μ T := by
  rw [runAt, simulateQ_commitmentWithH, implH_totalImpl]

theorem runAt_reduceWithH (lr : ℕ) (index : Commitment) (stmt : Statement) (p : ReductionProof) :
    runAt H F (reduceWithH callKeccak256 lr index stmt p) = reduceWithH (m := Id) H lr index stmt p := by
  rw [runAt, simulateQ_reduceWithH, implH_totalImpl]

theorem runAt_proveClaimWithH (fuel : ℕ) (tree : Tree) (table : Array K) (c : Commitment)
    (claim : Claim) :
    runAt H F (proveClaimWithH callKeccak256 callKeccakF1600 fuel tree table c claim) =
      proveClaimWithH (m := Id) H F fuel tree table c claim := by
  rw [runAt, simulateQ_proveClaimWithH, implH_totalImpl, implF_totalImpl]

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
        (commitmentWithH (m := Id) H (cellVars C.logRows + 1) (witnessTable C cells₀ coins)).1,
        (commitmentWithH (m := Id) H (cellVars C.logRows + 1) (witnessTable C cells₀ coins)).2),
      H (label (commitmentWithH (m := Id) H (cellVars C.logRows) C.wiringTable).2 stmt),
      .of (commitmentWithH (m := Id) H (cellVars C.logRows + 1) (witnessTable C cells₀ coins)).2) := by
  simp only [stageAG, runAt, simulateQ_bind, simulateQ_pure, simulateQ_commitmentWithH,
    LeanVM.Protocol.Compile.Rom.simulateQ_queryH, implH_totalImpl]
  rfl

/-- **Stage B at functions.** -/
theorem stageBG_id (C : Circuit) (cells₀ : Array K) (coins : Coins) (a : AuxA) (s₁ s₂ s₃ : Digest) :
    runAt H F (stageBG C cells₀ coins a s₁ s₂ s₃) =
      (((commitmentWithH (m := Id) H (cellVars C.logRows + 3) (tablesAt C cells₀ coins s₁ s₂ s₃).1).1,
        (commitmentWithH (m := Id) H (cellVars C.logRows + 3) (tablesAt C cells₀ coins s₁ s₂ s₃).1).2,
        (commitmentWithH (m := Id) H (cellVars C.logRows + 4)
          (tablesAt C cells₀ coins s₁ s₂ s₃).2.1).1,
        (commitmentWithH (m := Id) H (cellVars C.logRows + 4)
          (tablesAt C cells₀ coins s₁ s₂ s₃).2.1).2,
        (commitmentWithH (m := Id) H (cellVars C.logRows + 1)
          (tablesAt C cells₀ coins s₁ s₂ s₃).2.2).1,
        (commitmentWithH (m := Id) H (cellVars C.logRows + 1)
          (tablesAt C cells₀ coins s₁ s₂ s₃).2.2).2),
      (.of (commitmentWithH (m := Id) H (cellVars C.logRows + 3) (tablesAt C cells₀ coins s₁ s₂ s₃).1).2,
        .of (commitmentWithH (m := Id) H (cellVars C.logRows + 4)
          (tablesAt C cells₀ coins s₁ s₂ s₃).2.1).2,
        .of (commitmentWithH (m := Id) H (cellVars C.logRows + 1)
          (tablesAt C cells₀ coins s₁ s₂ s₃).2.2).2)) := by
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
      let s₄' := H (in9 s₃' (.of b.2.1, .of b.2.2.2.1, .of b.2.2.2.2.2))
      ((s₁', s₂', s₃', s₄'), s₄', rowValues C cells₀ coins (challengeOf s₄)) := by
  simp only [stageCG, runAt, simulateQ_bind, simulateQ_pure,
    LeanVM.Protocol.Compile.Rom.simulateQ_queryH, implH_totalImpl]
  rfl

end Stages

/-! ## The reduction at functions, on the run's states -/

/-- **The prover's reductions at functions**: on commitments it computed, at the run's states, the reduction
returns the claims `claimsAt` gives at the run's challenges. -/
theorem reduce_core (H : Bytes → Digest) (stmt : Statement) (index wCom hCom qCom gCom : Commitment)
    (s₀ s₁ s₂ s₃ s₄ s₅ : Digest) (rv : Vector E 4 × E) (qv gv : E)
    (h₀ : H (label index stmt) = s₀) (h₁ : H (in3 s₀ (.of wCom)) = s₁) (h₂ : H (digestBytes s₁) = s₂)
    (h₃ : H (digestBytes s₂) = s₃) (h₄ : H (in9 s₃ (.of hCom, .of qCom, .of gCom)) = s₄)
    (h₅ : H (in5 s₄ rv) = s₅) :
    reduceWithH (m := Id) H 22 index stmt ⟨.of wCom, .of hCom, .of qCom, .of gCom, rv.1, rv.2, qv, gv⟩ =
      (claimsAt 22 stmt (challengeOf s₁) (challengeOf s₂) (challengeOf s₃) (challengeOf s₄)
        (challengeOf s₅) rv.1 rv.2 qv gv).map fun claims ↦ ⟨⟨wCom, hCom, qCom, gCom⟩, claims⟩ := by
  rw [reduceWithH_eq_chain (m := Id) H (by decide : Supported 22)]
  show (pure (Option.map _ (claimsAt 22 stmt (challengeOf (H (in3 (H (label index stmt)) _)))
    _ _ _ _ _ _ _ _)) : Id _) = _
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

/-! ## (Red) -/

theorem cellVars_membership : cellVars (membership logRows).logRows = 24 := rfl

section Bridge

variable (hC : HonestClaims)
include hC

/-- **(Red)** on the deployed instance. -/
theorem tailReduces (stmt : Statement) (w : Secret) (hrel : Relation stmt w) (coins : Coins) :
    TailReducesG (setupWithH callKeccak256) (membership logRows) (cellsOf w) coins stmt
      (badSet w coins) := by
  intro H F x s₁ s₂ s₃ y s₄ z s₅ hst hgood
  obtain ⟨hA, h₁, h₂, h₃, hB, h₄, hCz, h₅⟩ := hst
  rw [stageAG_id] at hA
  rw [stageBG_id] at hB
  generalize commitmentWithH (m := Id) H (cellVars (membership logRows).logRows)
    (membership logRows).wiringTable = cI at hA
  generalize commitmentWithH (m := Id) H (cellVars (membership logRows).logRows + 1)
    (witnessTable (membership logRows) (cellsOf w) coins) = cW at hA
  generalize commitmentWithH (m := Id) H (cellVars (membership logRows).logRows + 3)
    (tablesAt (membership logRows) (cellsOf w) coins s₁ s₂ s₃).1 = cH at hB
  generalize commitmentWithH (m := Id) H (cellVars (membership logRows).logRows + 4)
    (tablesAt (membership logRows) (cellsOf w) coins s₁ s₂ s₃).2.1 = cQ at hB
  generalize commitmentWithH (m := Id) H (cellVars (membership logRows).logRows + 1)
    (tablesAt (membership logRows) (cellsOf w) coins s₁ s₂ s₃).2.2 = cG at hB
  subst hA hB
  rw [stageCG_id] at hCz
  subst hCz
  dsimp only at h₁ h₄ h₅ ⊢
  obtain ⟨cl, hcl, hpts, -⟩ := hC stmt w hrel coins _ _ (challengeOf s₃) _ _ hgood
  have hred := fun qv gv ↦ reduce_core H stmt cI.2 cW.2 cH.2 cQ.2 cG.2 _ s₁ s₂ s₃ s₄ s₅
    (rowValues (membership logRows) (cellsOf w) coins (challengeOf s₄)) qv gv rfl h₁ h₂ h₃ h₄
    (by rw [h₁, h₂, h₃, h₄] at h₅; exact h₅)
  refine ⟨⟨⟨cW.2, cH.2, cQ.2, cG.2⟩, cl 0 0⟩, ?_, ?_⟩
  · simp only [claims₀Of, h₁, h₂, h₃, h₄, membership_logRows]
    rw [hcl 0 0]
    rfl
  · rw [runAt_reduceWithH]
    simp only [proof₀Of, membership_logRows]
    rw [hred, hcl]
    simp

set_option maxHeartbeats 2000000 in
/-- **(Acc)** on the deployed instance. -/
theorem tailAccepts (stmt : Statement) (w : Secret) (hrel : Relation stmt w) (coins : Coins) :
    TailAcceptsG (setupWithH callKeccak256) (membership logRows) (cellsOf w) coins nonceFuel logRows
      stmt (badSet w coins) := by
  intro H F x s₁ s₂ s₃ y s₄ z s₅ hst hgood π hπ
  obtain ⟨hA, h₁, h₂, h₃, hB, h₄, hCz, h₅⟩ := hst
  rw [stageAG_id] at hA
  rw [stageBG_id] at hB
  generalize hcI : commitmentWithH (m := Id) H (cellVars (membership logRows).logRows)
    (membership logRows).wiringTable = cI at hA
  generalize hcW : commitmentWithH (m := Id) H (cellVars (membership logRows).logRows + 1)
    (witnessTable (membership logRows) (cellsOf w) coins) = cW at hA
  generalize hcH : commitmentWithH (m := Id) H (cellVars (membership logRows).logRows + 3)
    (tablesAt (membership logRows) (cellsOf w) coins s₁ s₂ s₃).1 = cH at hB
  generalize hcQ : commitmentWithH (m := Id) H (cellVars (membership logRows).logRows + 4)
    (tablesAt (membership logRows) (cellsOf w) coins s₁ s₂ s₃).2.1 = cQ at hB
  generalize hcG : commitmentWithH (m := Id) H (cellVars (membership logRows).logRows + 1)
    (tablesAt (membership logRows) (cellsOf w) coins s₁ s₂ s₃).2.2 = cG at hB
  subst hA hB
  rw [stageCG_id] at hCz
  subst hCz
  dsimp only at h₁ h₄ h₅ hπ ⊢
  obtain ⟨cl, hcl, hpts, hW, hσ, hH, hQ, hG, hS⟩ := hC stmt w hrel coins _ _ (challengeOf s₃) _ _ hgood
  have hred := fun qv gv ↦ reduce_core H stmt cI.2 cW.2 cH.2 cQ.2 cG.2 _ s₁ s₂ s₃ s₄ s₅
    (rowValues (membership logRows) (cellsOf w) coins (challengeOf s₄)) qv gv rfl h₁ h₂ h₃ h₄
    (by rw [h₁, h₂, h₃, h₄] at h₅; exact h₅)
  -- The prover's tail.
  simp only [proverTailG, claims₀Of, proof₀Of, tablesAt, h₁, h₂, h₃, h₄, membership_logRows] at hπ
  rw [hcl 0 0] at hπ
  simp only [Option.map_some, runAt, simulateQ_bind, simulateQ_pure, simulateQ_reduceWithH,
    simulateQ_proveClaimWithH, implH_totalImpl, implF_totalImpl] at hπ
  rw [hred, hcl] at hπ
  simp only [tablesAt] at hcH hcQ hcG
  generalize hTq : quotientTables (membership logRows) (cellsOf w) coins (challengeOf s₁) (challengeOf s₂)
    (challengeOf s₃) = T at hπ hW hσ hH hQ hG hS hcH hcQ hcG
  generalize hc : cl (tableEval T.2.1 (cl 0 0).q.point) (tableEval T.2.2 (cl 0 0).g.point) = c
    at hπ hW hσ hH hQ hG hS
  simp only [Option.map_some, id_bind', id_pure', simulateQ_bind, simulateQ_pure,
    simulateQ_proveClaimWithH, implH_totalImpl, implF_totalImpl] at hπ
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
  rename_i oH hoH
  simp only [id_bind', id_pure', simulateQ_bind, simulateQ_pure, simulateQ_proveClaimWithH,
    implH_totalImpl, implF_totalImpl] at hπ
  split at hπ
  swap
  · simp at hπ
  rename_i oQ hoQ
  simp only [id_bind', id_pure', simulateQ_bind, simulateQ_pure, simulateQ_proveClaimWithH,
    implH_totalImpl, implF_totalImpl] at hπ
  split at hπ
  swap
  · simp at hπ
  rename_i oG hoG
  simp only [id_bind', id_pure', simulateQ_bind, simulateQ_pure, simulateQ_proveClaimWithH,
    implH_totalImpl, implF_totalImpl] at hπ
  split at hπ
  swap
  · simp at hπ
  rename_i oS hoS
  simp only [id_pure', simulateQ_pure, Option.some.injEq] at hπ
  subst hπ
  -- The verifier.
  have hidx : runAt H F (Prod.snd <$> setupWithH callKeccak256) = cI.2 := by
    rw [← hcI]; exact setup_index H F
  rw [runAt_verifyWithH, hidx]
  have hr := hred (tableEval T.2.1 (cl 0 0).q.point) (tableEval T.2.2 (cl 0 0).g.point)
  rw [hcl, hc, Option.map_some] at hr
  unfold verifyWithH
  dsimp only
  erw [hr]
  simp only [id_bind']
  -- The sizes.
  have hsW : (witnessTable (membership logRows) (cellsOf w) coins).size =
      2 ^ (cellVars (membership logRows).logRows + 1) := by
    rw [witnessTable_eq, Array.size_ofFn, pow_succ, mul_comm]
  have hsσ : (membership logRows).wiringTable.size = 2 ^ cellVars (membership logRows).logRows := by
    rw [wiringTable_eq, Bridge.Ntt.coefficients_size, Array.size_map, sigma_size]
    rfl
  have hsT : T.1.size = 2 ^ (cellVars (membership logRows).logRows + 3) ∧
      T.2.1.size = 2 ^ (cellVars (membership logRows).logRows + 4) ∧
      T.2.2.size = 2 ^ (cellVars (membership logRows).logRows + 1) := by
    rw [← hTq, quotientTables_eq]
    simp only [hTableOf, qTableOf, gTableOf, Array.size_ofFn]
    refine ⟨?_, ?_, ?_⟩ <;> rw [membership_logRows] <;> ring
  subst hcI hcW hcH hcQ hcG
  apply checkAll_true
  intro e he
  simp only [Reduced.checks, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact opening_ok H F _ _ (by rw [cellVars_membership]; decide) _ hsW _
      (by rw [hW.1]; rfl) hW.2 hoW
  · exact opening_ok H F _ _ (by rw [cellVars_membership]; decide) _ hsσ _
      (by rw [hσ.1]; rfl) hσ.2 hoσ
  · exact opening_ok H F _ _ (by rw [cellVars_membership]; decide) _ hsT.1 _
      (by rw [hH.1]; rfl) hH.2 hoH
  · exact opening_ok H F _ _ (by rw [cellVars_membership]; decide) _ hsT.2.1 _
      (by rw [hQ.1]; rfl) hQ.2 hoQ
  · exact opening_ok H F _ _ (by rw [cellVars_membership]; decide) _ hsT.2.2 _
      (by rw [hG.1]; rfl) hG.2 hoG
  · exact opening_ok H F _ _ (by rw [cellVars_membership]; decide) _ hsT.1 _
      (by rw [hS.1]; rfl) hS.2 hoS

end Bridge

end E2ECompleteness.Pcs
