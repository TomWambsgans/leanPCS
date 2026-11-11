-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows `formal/UniComplete/UniComplete/VerifierHSim.lean`
-- and `ProverSim.lean` (`UniKeccakComplete.Morph`, its channel and writer liftings) for π2's code (`Pi2CompleteH`'s contract,
-- setup and graph verifier with Keccak-256 explicit, `Pi2Prover`'s honest prover, `Pi2ProbStaged`'s stages), over
-- leanerVM's two calls (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR
-- Apache-2.0: `implH`, `implF`, `simulateQ_queryH`) and `formal/UniKeccakComplete`'s `simulateQ_pcsVerify`,
-- `Morph.app_pcsOpenKH`; `FsOod`'s `simulateQ_pcsVerifierO`, `Pi2PcsZ`'s `simulateQ_pcsProveZH`.
import RecCompose.Pi2ProbStaged
import RecCompose.FsOod

/-!
# π2's code commutes with simulation

Every function of π2's completeness experiment is written over any monad, Keccak-256 `H` and the permutation `F`
explicit. Read through a monad morphism `φ` (`UniKeccakComplete.Morph`) that commutes with the PCS claim's checks (at the
fixed point, `hopen`; at the point read off `H`, `hopenO`) and its prover (`hprove`), each is the same function over
`φ ∘ H`, `φ ∘ F` (`app_…`, `chan_…`, `wr_…`; the out-of-domain point `app_oodPointM`): the setup
(`app_setupTreesWithH2`), the IV (`app_ivOfH`), π1-rec4's graph with its openings (`app_pi1GraphVerifierWithH`), π2's
run and contract (`chan_reduceWithH2`, `app_runWithH2`, `app_contractWithH`, `app_verifierWithH2`), π2's honest prover
(`wr_pi2ProveStreamWith`, `app_pi2ProveWith`, `app_pi2ProverWith`), the experiment `expW2` and its stages
(`app_expW2`, `wr_pre2`, `wr_mid2`, `wr_post2`, `app_stageA`, `app_stageB`, `app_restC`, `app_stageC`), at π2v4 (the
frame words in the seed, four openings).

**`sim_…`**: over the two calls, with `φ = Morph.sim impl` (`simulateQ impl`), the two hypotheses WithHash's.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2Sim

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF)
open UniStatement (Chan ChanM)
open UniKeccakComplete (Morph)
open Pi2S Pi2K Pi2P Pi2E Pi2G

section Morph

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
  (H : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-! ## The setup, the IV -/

theorem app_setupTreesWithH2 (D : RecDeployment) :
    φ.app (Pi2H.setupTreesWithH H F D) =
      Pi2H.setupTreesWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D := by
  simp only [Pi2H.setupTreesWithH, Pi2H.setupTreeKWithH, Pi2H.setupTreeWithH, φ.app_bind, φ.app_pure,
    Morph.app_commitWithH]

theorem app_digestWithH (c : Pi2Circuit) :
    φ.app (Pi2H.digestWithH H c) = Pi2H.digestWithH (fun x ↦ φ.app (H x)) c := by
  simp only [Pi2H.digestWithH, φ.app_bind, φ.app_pure]

theorem app_ivWithH2 (pi1Iv setupRoot : List UInt8) (setupOod : E) (digest : List UInt8) (logN : ℕ) :
    φ.app (Pi2H.ivWithH H pi1Iv setupRoot setupOod digest logN) =
      Pi2H.ivWithH (fun x ↦ φ.app (H x)) pi1Iv setupRoot setupOod digest logN := by
  simp only [Pi2H.ivWithH, φ.app_bind, φ.app_pure]

theorem app_ivOfH (D : RecDeployment) (roots : RecSetupRoots) :
    φ.app (Pi2H.ivOfH H D roots) = Pi2H.ivOfH (fun x ↦ φ.app (H x)) D roots := by
  simp only [Pi2H.ivOfH, φ.app_bind, app_digestWithH, app_ivWithH2]

/-! ## The openings -/

variable (hopen : ∀ (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (proof : LeanVM.Protocol.Compile.Proof),
    φ.app (UniKeccakComplete.pcsOpenKH H F n root ood pt v proof) =
      UniKeccakComplete.pcsOpenKH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) n root ood pt v proof)

include hopen in
/-- **π1-rec4's graph with its three openings.** -/
theorem app_pi1GraphVerifierWithH (D : RecDeployment) (roots : UniKeccak.SetupRootsK) (input : Vector UInt8 32)
    (proof : UniKeccak.KeccakProof) :
    φ.app (Pi2H.pi1GraphVerifierWithH H F D roots input proof) =
      Pi2H.pi1GraphVerifierWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D roots input proof := by
  unfold Pi2H.pi1GraphVerifierWithH
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · split
      · exact φ.app_pure _
      · split
        · exact φ.app_pure _
        · simp only [φ.app_bind, Morph.app_forIn_list, φ.app_pure, hopen]

variable (hopenO : ∀ (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E)
    (proof : LeanVM.Protocol.Compile.Proof),
    φ.app (Pi2H.pcsOpenKOH H F n root ood pt v proof) =
      Pi2H.pcsOpenKOH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) n root ood pt v proof)

include hopen hopenO in
theorem app_pcsOpenWordsH (words : List (List UInt8)) (proof : LeanVM.Protocol.Compile.Proof) :
    φ.app (Pi2H.pcsOpenWordsH H F words proof) =
      Pi2H.pcsOpenWordsH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) words proof := by
  unfold Pi2H.pcsOpenWordsH
  split
  · exact φ.app_pure _
  · split
    · exact hopenO _ _ _ _ _ _
    · exact hopen _ _ _ _ _ _

include hopen hopenO in
theorem app_openAtH (o : Pi1Opening) (proof : LeanVM.Protocol.Compile.Proof) :
    φ.app (Pi2H.openAtH H F o proof) = Pi2H.openAtH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) o proof := by
  unfold Pi2H.openAtH
  split
  · exact hopenO _ _ _ _ _ _
  · exact hopen _ _ _ _ _ _

/-- **The out-of-domain point** (`n` calls of `H`). -/
theorem app_oodPointM (n : ℕ) (r : Digest) :
    φ.app (WhirBridge.Pcs.oodPointM H n r) = WhirBridge.Pcs.oodPointM (fun x ↦ φ.app (H x)) n r := by
  unfold WhirBridge.Pcs.oodPointM
  generalize List.range n = l
  induction l with
  | nil => simp only [List.mapM_nil, φ.app_pure]
  | cons j l ih => simp only [List.mapM_cons, φ.app_bind, φ.app_pure, ih, bind_assoc, pure_bind]

/-! ## π2's run and the contract -/

theorem chan_nextNarrow : φ.chan (nextNarrow (m := m)) = nextNarrow := by
  simp only [nextNarrow, Morph.chan_bind, Morph.chan_takeBytes, Morph.chan_pure]

theorem chan_reduceWithH2 (s : Spec) (statement : List E) (frameAt : ℕ → List UInt8) :
    φ.chan (Pi2H.reduceWithH H s statement frameAt) =
      Pi2H.reduceWithH (fun x ↦ φ.app (H x)) s statement frameAt := by
  simp only [Pi2H.reduceWithH, Morph.chan_bind, Morph.chan_forIn_list, Morph.chan_pure, Morph.chan_nextRoot,
    Morph.chan_sampleH, Morph.chan_nextScalars, Morph.chan_nextScalar]
  congr 1
  congr 1
  funext rd pubs
  split <;> simp only [Morph.chan_bind, Morph.chan_pure, Morph.chan_nextInteger, Morph.chan_nextRoot,
    Morph.chan_nextScalar, chan_nextNarrow]

theorem app_runWithH2 (s : Spec) (iv publicInput : List UInt8) (frameAt : ℕ → List UInt8) (stream : Array UInt8) :
    φ.app (Pi2H.runWithH H s iv publicInput frameAt stream) =
      Pi2H.runWithH (fun x ↦ φ.app (H x)) s iv publicInput frameAt stream := by
  simp only [Pi2H.runWithH, φ.app_bind, φ.app_pure, ← Morph.chan_run φ, Morph.chan_bind, chan_reduceWithH2,
    Morph.chan_finish, Morph.chan_pure]

include hopen hopenO in
/-- **The contract.** -/
theorem app_contractWithH (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    φ.app (Pi2H.contractWithH H F D roots input proof) =
      Pi2H.contractWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D roots input proof := by
  simp only [Pi2H.contractWithH, φ.app_bind, app_ivOfH, app_runWithH2]
  refine bind_congr fun iv ↦ bind_congr fun o ↦ ?_
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · split
      · exact φ.app_pure _
      · split
        · exact φ.app_pure _
        · simp only [φ.app_bind, Morph.app_forIn_list, φ.app_pure, app_pcsOpenWordsH φ H F hopen hopenO]

include hopen hopenO in
theorem app_verifierWithH2 (D : RecDeployment) (roots : RecSetupRoots) (input : Vector UInt8 32) (proof : RecProof) :
    φ.app (Pi2H.verifierWithH H F D roots input proof) =
      Pi2H.verifierWithH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D roots input proof := by
  simp only [Pi2H.verifierWithH, φ.app_bind, φ.app_pure, app_contractWithH φ H F hopen hopenO]

/-! ## π2's honest prover -/

theorem wr_sendPublic (l : List (Read × PublicValue)) : φ.wr (sendPublic (m := m) l) = sendPublic l := by
  simp only [sendPublic, Morph.wr_sendBytes]

theorem wr_pi2ProveStreamWith (G : RecPiop.Circuit E) (S : CoreSpec E) (oodPt : ℕ → Digest → m (List E))
    (reads : List Read) (setupStack : Array K)
    (input : List UInt8) (values : List PublicValue) (w : ℕ → K) :
    φ.wr (pi2ProveStreamWith H G S oodPt reads setupStack input values w) =
      pi2ProveStreamWith (fun x ↦ φ.app (H x)) G S (fun n r ↦ φ.app (oodPt n r)) reads setupStack input values w := by
  simp only [pi2ProveStreamWith, Morph.wr_bind, wr_sendPublic, Morph.wr_lift, Morph.app_commitWithH,
    Morph.wr_sendRoot, Morph.wr_sendScalar, Morph.wr_sampleW, Morph.wr_sendScalars, Morph.wr_get, Morph.wr_pure]

variable (hprove : ∀ (fuel n : ℕ) (z : List E) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E),
    φ.app (PcsZ.pcsProveZH H F fuel n z tree stack pt v) =
      PcsZ.pcsProveZH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel n z tree stack pt v)

include hprove in
theorem app_pi2ProveWith (fuel : ℕ) (G : RecPiop.Circuit E) (oodPt : ℕ → Digest → m (List E)) (view : Circuit)
    (setupStack : Array K) (setupTree : LeanVM.Prover.Tree) (iv input : List UInt8) (values : List PublicValue)
    (w : ℕ → K) :
    φ.app (pi2ProveWith H F fuel G oodPt view setupStack setupTree iv input values w) =
      pi2ProveWith (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel G (fun n r ↦ φ.app (oodPt n r)) view setupStack
        setupTree iv input values w := by
  simp only [pi2ProveWith, φ.app_bind, φ.app_pure, ← Morph.wr_run φ, wr_pi2ProveStreamWith, hprove]

include hprove in
theorem app_pi2ProverWith (D : RecDeployment) (G : RecSetupRoots → RecPiop.Circuit E)
    (pubOf : RecSetupRoots → List E → ℕ → List E) (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof) :
    φ.app (pi2ProverWith H F D G pubOf fuel input p1) =
      pi2ProverWith (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D G pubOf fuel input p1 := by
  simp only [pi2ProverWith, φ.app_bind, φ.app_pure, app_setupTreesWithH2, app_ivOfH,
    app_pi2ProveWith φ H F hprove, app_oodPointM]

/-! ## The experiment and its stages -/

include hopen hopenO hprove in
theorem app_expW2 (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (p1o : m (Option UniKeccak.KeccakProof)) (input : Vector UInt8 32) :
    φ.app (expW2 H F D C Fa p1o input) =
      expW2 (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D C Fa (φ.app p1o) input := by
  simp only [expW2, φ.app_bind, app_setupTreesWithH2]
  refine bind_congr fun trees ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => exact φ.app_pure _
  | some p1 =>
    simp only [φ.app_bind, app_pi1GraphVerifierWithH φ H F hopen, app_pi2ProverWith φ H F hprove]
    refine bind_congr fun a1 ↦ bind_congr fun r ↦ ?_
    cases r with
    | none => exact φ.app_pure _
    | some p2 => simp only [φ.app_bind, φ.app_pure, app_verifierWithH2 φ H F hopen hopenO]

theorem wr_pre2 (G : RecPiop.Circuit E) (oodPt : ℕ → Digest → m (List E)) (reads : List Read)
    (values : List PublicValue) (w : ℕ → K) :
    φ.wr (pre2 H G oodPt reads values w) = pre2 (fun x ↦ φ.app (H x)) G (fun n r ↦ φ.app (oodPt n r)) reads values w := by
  simp only [pre2, Morph.wr_bind, wr_sendPublic, Morph.wr_lift, Morph.app_commitWithH, Morph.wr_sendRoot,
    Morph.wr_sendScalar, Morph.wr_pure]

theorem wr_mid2 (G : RecPiop.Circuit E) (S : CoreSpec E) (oodPt : ℕ → Digest → m (List E)) (pubs : List E)
    (w : ℕ → K) (α β γ : E) :
    φ.wr (mid2 H G S oodPt pubs w α β γ) = mid2 (fun x ↦ φ.app (H x)) G S (fun n r ↦ φ.app (oodPt n r)) pubs w α β γ := by
  simp only [mid2, Morph.wr_bind, Morph.wr_lift, Morph.app_commitWithH, Morph.wr_sendRoot, Morph.wr_sendScalar,
    Morph.wr_pure]

theorem wr_post2 (G : RecPiop.Circuit E) (setupStack : Array K) (input : List UInt8) (values : List PublicValue)
    (w : ℕ → K) (wS : Array K) (wT : LeanVM.Prover.Tree) (qS : Array K) (qT : LeanVM.Prover.Tree) (α β γ t : E)
    (wP qP : List E) :
    φ.wr (post2 H G setupStack input values w wS wT qS qT α β γ t wP qP) =
      post2 (fun x ↦ φ.app (H x)) G setupStack input values w wS wT qS qT α β γ t wP qP := by
  simp only [post2, Morph.wr_bind, Morph.wr_sendScalars, Morph.wr_sampleW, Morph.wr_get, Morph.wr_pure]

include hopen in
theorem app_stageA (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (p1o : m (Option UniKeccak.KeccakProof)) (input : Vector UInt8 32) :
    φ.app (stageA H F D C Fa p1o input) =
      stageA (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D C Fa (φ.app p1o) input := by
  simp only [stageA, φ.app_bind, app_setupTreesWithH2]
  refine bind_congr fun trees ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => exact φ.app_pure _
  | some p1 =>
    simp only [φ.app_bind, φ.app_pure, app_pi1GraphVerifierWithH φ H F hopen, app_setupTreesWithH2, app_ivOfH,
      ← Morph.wr_run φ, wr_pre2, app_oodPointM]

theorem app_stageB (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (a : StA) (s₁ s₂ s₃ : Digest) :
    φ.app (stageB H D C input a s₁ s₂ s₃) = stageB (fun x ↦ φ.app (H x)) D C input a s₁ s₂ s₃ := by
  simp only [stageB, φ.app_bind, φ.app_pure, ← Morph.wr_run φ, wr_mid2, app_oodPointM]

include hopen hopenO hprove in
theorem app_restC (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (b : StB)
    (p1 : UniKeccak.KeccakProof) (out : Pi2Out) :
    φ.app (restC H F D C input b p1 out) = restC (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D C input b p1 out := by
  simp only [restC, φ.app_bind, hprove]
  refine bind_congr fun pW ↦ bind_congr fun pS ↦ bind_congr fun pQ1 ↦ bind_congr fun pQ2 ↦ ?_
  split
  · simp only [φ.app_bind, φ.app_pure, app_verifierWithH2 φ H F hopen hopenO]
  · exact φ.app_pure _

include hopen hopenO hprove in
theorem app_stageC (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (b : StB) (st : Digest) :
    φ.app (stageC H F D C input b st) =
      stageC (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) D C input b st := by
  unfold stageC
  split
  · exact φ.app_pure _
  · simp only [φ.app_bind, ← Morph.wr_run φ, wr_post2]
    refine bind_congr fun x ↦ ?_
    rcases x with ⟨out, w⟩
    simp only [φ.app_pure, app_restC φ H F hopen hopenO hprove]

end Morph

/-! ## Over the two calls -/

section Sim

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

theorem hopen_sim : ∀ (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E)
    (proof : LeanVM.Protocol.Compile.Proof),
    (Morph.sim impl).app (UniKeccakComplete.pcsOpenKH callKeccak256 callKeccakF1600 n root ood pt v proof) =
      UniKeccakComplete.pcsOpenKH (fun x ↦ (Morph.sim impl).app (callKeccak256 x))
        (fun s ↦ (Morph.sim impl).app (callKeccakF1600 s)) n root ood pt v proof := by
  intro n root ood pt v proof
  refine UniKeccakComplete.Morph.app_pcsOpenKH (φ := Morph.sim impl) (H := callKeccak256) (F := callKeccakF1600)
    (fun n zOf x p ↦ ?_) n root ood pt v proof
  rw [Morph.sim_H, Morph.sim_F]
  exact UniKeccakComplete.simulateQ_pcsVerify impl zOf x p

theorem hopenO_sim : ∀ (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E)
    (proof : LeanVM.Protocol.Compile.Proof),
    (Morph.sim impl).app (Pi2H.pcsOpenKOH callKeccak256 callKeccakF1600 n root ood pt v proof) =
      Pi2H.pcsOpenKOH (fun x ↦ (Morph.sim impl).app (callKeccak256 x))
        (fun s ↦ (Morph.sim impl).app (callKeccakF1600 s)) n root ood pt v proof := by
  intro n root ood pt v proof
  rw [Morph.sim_H, Morph.sim_F]
  unfold Pi2H.pcsOpenKOH
  split
  · exact simulateQ_pcsVerifierO impl _ proof
  · exact (Morph.sim impl).app_pure _

theorem hprove_sim : ∀ (fuel n : ℕ) (z : List E) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E),
    (Morph.sim impl).app (PcsZ.pcsProveZH callKeccak256 callKeccakF1600 fuel n z tree stack pt v) =
      PcsZ.pcsProveZH (fun x ↦ (Morph.sim impl).app (callKeccak256 x))
        (fun s ↦ (Morph.sim impl).app (callKeccakF1600 s)) fuel n z tree stack pt v := by
  intro fuel n z tree stack pt v
  rw [Morph.sim_H, Morph.sim_F]
  exact PcsZ.simulateQ_pcsProveZH impl fuel n z tree stack pt v

/-- **The experiment over the two calls commutes with any simulation.** -/
theorem sim_expW2 (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (p1o : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) (input : Vector UInt8 32) :
    simulateQ impl (expW2 callKeccak256 callKeccakF1600 D C Fa p1o input) =
      expW2 (implH impl) (implF impl) D C Fa (simulateQ impl p1o) input := by
  have h := app_expW2 (Morph.sim impl) callKeccak256 callKeccakF1600 (hopen_sim impl) (hopenO_sim impl)
    (hprove_sim impl) D C Fa p1o input
  rw [Morph.sim_H, Morph.sim_F] at h
  exact h

theorem sim_stageA (D : RecDeployment) (C : Pi2Circuits D) (Fa : Pi2Facts D C)
    (p1o : OracleComp KeccakCalls (Option UniKeccak.KeccakProof)) (input : Vector UInt8 32) :
    simulateQ impl (stageA callKeccak256 callKeccakF1600 D C Fa p1o input) =
      stageA (implH impl) (implF impl) D C Fa (simulateQ impl p1o) input := by
  have h := app_stageA (Morph.sim impl) callKeccak256 callKeccakF1600 (hopen_sim impl) D C Fa p1o input
  rw [Morph.sim_H, Morph.sim_F] at h
  exact h

theorem sim_stageB (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (a : StA) (s₁ s₂ s₃ : Digest) :
    simulateQ impl (stageB callKeccak256 D C input a s₁ s₂ s₃) = stageB (implH impl) D C input a s₁ s₂ s₃ := by
  have h := app_stageB (Morph.sim impl) callKeccak256 D C input a s₁ s₂ s₃
  rw [Morph.sim_H] at h
  exact h

theorem sim_stageC (D : RecDeployment) (C : Pi2Circuits D) (input : Vector UInt8 32) (b : StB) (st : Digest) :
    simulateQ impl (stageC callKeccak256 callKeccakF1600 D C input b st) =
      stageC (implH impl) (implF impl) D C input b st := by
  have h := app_stageC (Morph.sim impl) callKeccak256 callKeccakF1600 (hopen_sim impl) (hopenO_sim impl)
    (hprove_sim impl) D C input b st
  rw [Morph.sim_H, Morph.sim_F] at h
  exact h

end Sim

end RecCompose.Pi2Sim

/-- info: 'RecCompose.Pi2Sim.sim_expW2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2Sim.sim_expW2
