-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows `VerifierHSim.lean` (the morphism calculus),
-- `Rec3ProbExp.lean` (`expW3`, `experiment_eq3`) and leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch
-- `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls' simulation lemmas (`implH`, `implF`), the lazy
-- permutation (`Common.lazyRandomPermutationOracles`).
import UniKeccakComplete.K.Rec4Prover

/-!
# π1-rec4's experiment over its calls

* **The verifier commutes with every monad morphism** that commutes with the PCS check (`Morph.chan_reduceWithKH4`,
  `Morph.app_verifierWith4H`), as `VerifierHSim.lean`'s.
* **The experiment with Keccak-256, its rate and the permutation explicit** (`expW4 H W F D`: the setup, π1-rec4's
  honest prover, the verdict of π1-rec4's verifier) commutes with every monad morphism that commutes with the PCS
  check and opening (`Morph.app_expW4`).
* **Three readings of it**, each `simulateQ` of a morphism:
  - over **π1-rec4's calls** `KeccakCallsW` (`expWW`: `H` the digest of the rate call, `W` the rate call): the
    completeness experiment is its run against the random permutation (**`experiment4_eq`**);
  - over the **five-digest reading** (`tauW`, `Rec4Couple.lean`): `simulateQ tauW expWW` is the experiment at
    `H = H5`, `W = rate5` over leanerVM's two calls (**`simulateQ_tauW_expWW`**);
  - over **three calls** `KeccakCalls3` (`H`, `W`, `F` separate): `expWW` is its image by `nu3`
    (**`simulateQ_nu3_exp3`**), the form the block count is proved on (`Rec4Cost.lean`).

The PCS check and opening over the rate call are leanerVM's two calls' simulated by `nuW` (the hash the digest of the
rate call), so they commute with every simulation (`simulateQ_pcsVerify_nuW`, `simulateQ_pcsProveH_nuW`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF)
open UniStatement UniKeccak

set_option autoImplicit false

namespace UniKeccakComplete.Rec4

open UniKeccakComplete.Morph

/-! ## The verifier commutes with every monad morphism -/

section Verifier

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
  (H : List UInt8 → m Digest) (W : List UInt8 → m RateB)

theorem chan_sampleWideH (count : ℕ) : φ.chan (sampleWideH W count) = sampleWideH (fun x ↦ φ.app (W x)) count := by
  simp only [sampleWideH, chan_bind, chan_get, chan_lift, chan_set, chan_pure]

theorem chan_zerocheckFirstH (logN k : ℕ) (c : E) :
    φ.chan (Flock.zerocheckFirstH H logN k c) = Flock.zerocheckFirstH (fun x ↦ φ.app (H x)) logN k c := by
  simp only [Flock.zerocheckFirstH, chan_bind, chan_ite, chan_nextScalars, chan_sampleH, chan_pure,
    chan_sumcheckH, chan_nextScalar]

theorem chan_verifyWalkedKH4 (logN : ℕ) (v : KeccakVariant) (c : E) :
    φ.chan (verifyWalkedKH4 H logN v c) = verifyWalkedKH4 (fun x ↦ φ.app (H x)) logN v c := by
  simp only [verifyWalkedKH4, frontKH4, chan_bind, chan_zerocheckFirstH, chan_sampleH, chan_sumcheckH, chan_pure,
    chan_nextScalars, chan_requireZero]

set_option linter.unusedSimpArgs false in
theorem chan_batchKH4 (lambda : E) (combined : List (Commitment × Combined))
    (layouts : List (Commitment × StackLayout)) (ringMap : Option (List E)) :
    φ.chan (batchKH4 H lambda combined layouts ringMap) = batchKH4 (fun x ↦ φ.app (H x)) lambda combined layouts ringMap := by
  simp only [batchKH4, chan_bind, chan_sumcheckPairsDrawnH, chan_nextScalars, chan_nextScalar, chan_pure, pure_bind,
    chan_requireZero]

/-- Push the morphism through π1-rec4's walk's binds. -/
macro "chan_pushK4" : tactic => `(tactic| simp only [chan_bind, chan_ite, chan_throw, chan_pure, chan_countBits,
  chan_nextRoot, chan_sampleWideH, chan_verifyWalkedKH4, chan_forIn_list, chan_tablePart, chan_nextScalar,
  chan_batchKH4, pure_bind])

/-- The walk's closing tactic (`chan_closeK` at π1-rec4). -/
macro "chan_closeK4" : tactic => `(tactic| (chan_pushK4; repeat (first
  | with_reducible rfl
  | (with_reducible refine bind_congr fun _ ↦ ?_)
  | split
  | chan_pushK4)))

/-- **π1-rec4's walk commutes with the morphism.** -/
theorem chan_reduceWithKH4 (shape : UniStatement.Shape) (publicWords : List E) (v : KeccakVariant)
    (mode : ClaimsMode) :
    φ.chan (reduceWithKH4 H W shape publicWords v mode) =
      reduceWithKH4 (fun x ↦ φ.app (H x)) (fun x ↦ φ.app (W x)) shape publicWords v mode := by
  unfold reduceWithKH4
  chan_closeK4

theorem app_runWithKH4 (shape : UniStatement.Shape) (iv publicInput : List UInt8) (stream : Array UInt8)
    (v : KeccakVariant) (mode : ClaimsMode) :
    φ.app (runWithKH4 H W shape iv publicInput stream v mode) =
      runWithKH4 (fun x ↦ φ.app (H x)) (fun x ↦ φ.app (W x)) shape iv publicInput stream v mode := by
  simp only [runWithKH4, φ.app_bind, app_seedWithH, φ.app_pure, ← chan_run φ, chan_bind, chan_reduceWithKH4,
    chan_finish, chan_pure]

variable (F : KeccakState → m KeccakState)

/-- **π1-rec4's verifier commutes with a monad morphism that commutes with the PCS check.** -/
theorem app_verifyWithKH4
    (hopen : ∀ (n : ℕ) (zOf : Digest → Vector E n) (x : WhirBridge.Pcs.Claim1 n)
      (proof : LeanVM.Protocol.Compile.Proof),
      φ.app (WhirBridge.Pcs.pcsVerifyWithHash H F zOf x proof) =
        WhirBridge.Pcs.pcsVerifyWithHash (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) zOf x proof)
    (shape : UniStatement.Shape) (v : KeccakVariant) (iv : List UInt8) (roots : SetupRootsK)
    (publicInput : Vector UInt8 32) (proof : KeccakProof) :
    φ.app (verifyWithKH4 H W F shape v iv roots publicInput proof) =
      verifyWithKH4 (fun x ↦ φ.app (H x)) (fun x ↦ φ.app (W x)) (fun s ↦ φ.app (F s)) shape v iv roots publicInput
        proof := by
  simp only [verifyWithKH4, φ.app_bind, app_runWithKH4]
  congr 1; funext o
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · simp only [φ.app_bind, app_forIn_list]
      congr 1
      · congr 1; funext x s
        split
        · simp only [φ.app_bind, φ.app_pure, app_pcsOpenKH φ H F hopen]
        · exact φ.app_pure _
      · funext s
        split <;> exact φ.app_pure _

/-- **π1-rec4's deployed verifier commutes with a monad morphism that commutes with the PCS check.** -/
theorem app_verifierWith4H
    (hopen : ∀ (n : ℕ) (zOf : Digest → Vector E n) (x : WhirBridge.Pcs.Claim1 n)
      (proof : LeanVM.Protocol.Compile.Proof),
      φ.app (WhirBridge.Pcs.pcsVerifyWithHash H F zOf x proof) =
        WhirBridge.Pcs.pcsVerifyWithHash (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) zOf x proof)
    (D : KDeployment) (roots : SetupRootsK) (input : Vector UInt8 32) (proof : KeccakProof) :
    φ.app (KDeployment.verifierWith4H H W F D roots input proof) =
      KDeployment.verifierWith4H (fun x ↦ φ.app (H x)) (fun x ↦ φ.app (W x)) (fun s ↦ φ.app (F s)) D roots input
        proof := by
  simp only [KDeployment.verifierWith4H, φ.app_bind, app_ivWithH, app_verifyWithKH4 φ H W F hopen]

end Verifier

/-! ## The experiment -/

section With

variable {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (W : List UInt8 → m RateB)
  (F : KeccakState → m KeccakState)

/-- The verdict on the prover's output: no proof is rejected, a proof goes to π1-rec4's deployed verifier. -/
def verdictW4 (D : KDeployment) (tree : LeanVM.Prover.Tree) (input : Vector UInt8 32) :
    Option KeccakProof → m Bool
  | none => pure false
  | some proof => KDeployment.verifierWith4H H W F D (D.setupRoots tree) input proof

/-- **π1-rec4's experiment with Keccak-256, its rate and the permutation explicit**: the setup, the honest prover,
the verdict. -/
def expW4 (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : m Bool := do
  let tree ← setupTreeKWithH H F D
  let o ← uniProverRec4With H W F D input rows q
  verdictW4 H W F D tree input o

end With

section MorphExp

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
  (H : List UInt8 → m Digest) (W : List UInt8 → m RateB) (F : KeccakState → m KeccakState)

/-- **The experiment commutes with a monad morphism** that commutes with the PCS check and opening. -/
theorem app_expW4
    (hopen : ∀ (n : ℕ) (zOf : Digest → Vector E n) (x : WhirBridge.Pcs.Claim1 n)
      (proof : LeanVM.Protocol.Compile.Proof),
      φ.app (WhirBridge.Pcs.pcsVerifyWithHash H F zOf x proof) =
        WhirBridge.Pcs.pcsVerifyWithHash (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) zOf x proof)
    (hprove : ∀ (fuel n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E),
      φ.app (pcsProveH H F fuel n tree stack pt v) =
        pcsProveH (fun x ↦ φ.app (H x)) (fun s ↦ φ.app (F s)) fuel n tree stack pt v)
    (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    φ.app (expW4 H W F D input rows q) =
      expW4 (fun x ↦ φ.app (H x)) (fun x ↦ φ.app (W x)) (fun s ↦ φ.app (F s)) D input rows q := by
  simp only [expW4, φ.app_bind, setupTreeKWithH, app_commitWithH, app_uniProverRec4With φ H W F hprove]
  refine bind_congr fun tree ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => exact φ.app_pure _
  | some proof => exact app_verifierWith4H φ H W F hopen D _ input proof

end MorphExp

/-! ## The PCS over the rate call -/

/-- **leanerVM's two calls over π1-rec4's**: the hash the digest of the rate call. -/
def nuW : QueryImpl KeccakCalls (OracleComp KeccakCallsW)
  | .inl x => digestOfRate <$> callRate x
  | .inr s => callFW s

/-- The hash over the rate call. -/
def hashW (x : Bytes) : OracleComp KeccakCallsW Digest := digestOfRate <$> callRate x

theorem implH_nuW : implH nuW = hashW := rfl

theorem implF_nuW : implF nuW = callFW := rfl

section Sim

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCallsW r)

omit [LawfulMonad r] in
theorem implH_comp_nuW : implH (impl ∘ₛ nuW) = fun x ↦ simulateQ impl (hashW x) := by
  funext x; rw [implH, QueryImpl.apply_compose]; rfl

omit [LawfulMonad r] in
theorem implF_comp_nuW : implF (impl ∘ₛ nuW) = fun s ↦ simulateQ impl (callFW s) := by
  funext s; rw [implF, QueryImpl.apply_compose]; rfl

/-- **The PCS check over the rate call commutes with every simulation.** -/
theorem simulateQ_pcsVerify_nuW {n : ℕ} (zOf : Digest → Vector E n) (x : WhirBridge.Pcs.Claim1 n)
    (proof : LeanVM.Protocol.Compile.Proof) :
    simulateQ impl (WhirBridge.Pcs.pcsVerifyWithHash hashW callFW zOf x proof) =
      WhirBridge.Pcs.pcsVerifyWithHash (fun x ↦ simulateQ impl (hashW x)) (fun s ↦ simulateQ impl (callFW s)) zOf
        x proof := by
  rw [← implH_nuW, ← implF_nuW, ← simulateQ_pcsVerify nuW, ← QueryImpl.simulateQ_compose, simulateQ_pcsVerify,
    implH_comp_nuW, implF_comp_nuW]
  rfl

/-- **The PCS opening over the rate call commutes with every simulation.** -/
theorem simulateQ_pcsProveH_nuW (fuel n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E) :
    simulateQ impl (pcsProveH hashW callFW fuel n tree stack pt v) =
      pcsProveH (fun x ↦ simulateQ impl (hashW x)) (fun s ↦ simulateQ impl (callFW s)) fuel n tree stack pt v := by
  rw [← implH_nuW, ← implF_nuW, ← simulateQ_pcsProveH nuW, ← QueryImpl.simulateQ_compose, simulateQ_pcsProveH,
    implH_comp_nuW, implF_comp_nuW]
  rfl

/-- **The experiment over π1-rec4's calls commutes with every simulation.** -/
theorem simulateQ_expWW (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ impl (expW4 hashW callRate callFW D input rows q) =
      expW4 (fun x ↦ simulateQ impl (hashW x)) (fun x ↦ simulateQ impl (callRate x))
        (fun s ↦ simulateQ impl (callFW s)) D input rows q :=
  app_expW4 (Morph.sim impl) hashW callRate callFW (fun _n zOf x proof ↦ simulateQ_pcsVerify_nuW impl zOf x proof)
    (fun fuel _n tree stack pt v ↦ simulateQ_pcsProveH_nuW impl fuel _n tree stack pt v) D input rows q

end Sim

/-! ## The random-permutation model -/

theorem simulateQ_hashW_qp (x : Bytes) :
    simulateQ keccakCallsWOverQueryPermutation (hashW x) = keccak256With Common.queryPermutation x := by
  simp only [hashW, simulateQ_map, callRate, simulateQ_spec_query, keccakCallsWOverQueryPermutation]
  rw [keccak256With_eq, Functor.map_map]
  congr 1
  funext st
  exact digestOfRate_rateOfState st

theorem simulateQ_callRate_qp (x : Bytes) :
    simulateQ keccakCallsWOverQueryPermutation (callRate x) = rateWith Common.queryPermutation x := by
  simp only [callRate, simulateQ_spec_query]
  rfl

theorem simulateQ_callFW_qp (s : KeccakState) :
    simulateQ keccakCallsWOverQueryPermutation (callFW s) = Common.queryPermutation s := by
  simp only [callFW, simulateQ_spec_query]
  rfl

/-- **π1-rec4's completeness experiment is the experiment over its calls against the random permutation.** -/
theorem experiment4_eq (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    keccakCompletenessExperiment4 D (uniProverRec4RP D) input rows q =
      (simulateQ keccakCallsWOverRandomPermutation (expW4 hashW callRate callFW D input rows q)).run' [] := by
  rw [← simulateQ_lazy_keccakCallsWOverQueryPermutation, simulateQ_expWW]
  simp only [simulateQ_hashW_qp, simulateQ_callRate_qp, simulateQ_callFW_qp]
  unfold keccakCompletenessExperiment4 Common.runWithRandomPermutation
  congr 2
  rw [setupTreeKWith_eqH]
  unfold expW4
  refine bind_congr fun tree ↦ bind_congr fun o ↦ ?_
  cases o with
  | none => rfl
  | some proof => simp only [verdictW4, verifierWith4_eqH4]

/-! ## The five-digest reading -/

/-- **The hash of the five-digest reading**: the first digest of `rate5`. -/
def hash5 (x : Bytes) : OracleComp KeccakCalls Digest := digestOfRate <$> rate5 x

theorem simulateQ_tauW_hashW (x : Bytes) : simulateQ tauW (hashW x) = hash5 x := by
  simp only [hashW, simulateQ_map, callRate, simulateQ_spec_query]
  rfl

theorem simulateQ_tauW_callRate (x : Bytes) : simulateQ tauW (callRate x) = rate5 x := by
  simp only [callRate, simulateQ_spec_query]
  rfl

theorem simulateQ_tauW_callFW (s : KeccakState) : simulateQ tauW (callFW s) = callKeccakF1600 s := by
  simp only [callFW, simulateQ_spec_query]
  rfl

/-- **The experiment's five-digest reading**: at `H = hash5`, `W = rate5` over leanerVM's two calls. -/
theorem simulateQ_tauW_expWW (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ tauW (expW4 hashW callRate callFW D input rows q) =
      expW4 hash5 rate5 callKeccakF1600 D input rows q := by
  rw [simulateQ_expWW]
  simp only [simulateQ_tauW_hashW, simulateQ_tauW_callRate, simulateQ_tauW_callFW]

/-! ## Three calls -/

/-- **Three calls**: Keccak-256, its rate, the permutation, separate. -/
abbrev KeccakCalls3 : OracleSpec (Bytes ⊕ (Bytes ⊕ KeccakState)) :=
  (Bytes →ₒ Digest) + ((Bytes →ₒ RateB) + (KeccakState →ₒ KeccakState))

def call3H (x : Bytes) : OracleComp KeccakCalls3 Digest := liftM (KeccakCalls3.query (.inl x))

def call3W (x : Bytes) : OracleComp KeccakCalls3 RateB := liftM (KeccakCalls3.query (.inr (.inl x)))

def call3F (s : KeccakState) : OracleComp KeccakCalls3 KeccakState := liftM (KeccakCalls3.query (.inr (.inr s)))

/-- leanerVM's two calls as three. -/
def iota3 : QueryImpl KeccakCalls (OracleComp KeccakCalls3)
  | .inl x => call3H x
  | .inr s => call3F s

/-- **Three calls over π1-rec4's**: the hash the digest of the rate call. -/
def nu3 : QueryImpl KeccakCalls3 (OracleComp KeccakCallsW)
  | .inl x => hashW x
  | .inr (.inl x) => callRate x
  | .inr (.inr s) => callFW s

theorem implH_iota3 : implH iota3 = call3H := rfl

theorem implF_iota3 : implF iota3 = call3F := rfl

section Sim3

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls3 r)

omit [LawfulMonad r] in
theorem implH_comp_iota3 : implH (impl ∘ₛ iota3) = fun x ↦ simulateQ impl (call3H x) := by
  funext x; rw [implH, QueryImpl.apply_compose]; rfl

omit [LawfulMonad r] in
theorem implF_comp_iota3 : implF (impl ∘ₛ iota3) = fun s ↦ simulateQ impl (call3F s) := by
  funext s; rw [implF, QueryImpl.apply_compose]; rfl

theorem simulateQ_pcsVerify_iota3 {n : ℕ} (zOf : Digest → Vector E n) (x : WhirBridge.Pcs.Claim1 n)
    (proof : LeanVM.Protocol.Compile.Proof) :
    simulateQ impl (WhirBridge.Pcs.pcsVerifyWithHash call3H call3F zOf x proof) =
      WhirBridge.Pcs.pcsVerifyWithHash (fun x ↦ simulateQ impl (call3H x)) (fun s ↦ simulateQ impl (call3F s)) zOf
        x proof := by
  rw [← implH_iota3, ← implF_iota3, ← simulateQ_pcsVerify iota3, ← QueryImpl.simulateQ_compose,
    simulateQ_pcsVerify, implH_comp_iota3, implF_comp_iota3]
  rfl

theorem simulateQ_pcsProveH_iota3 (fuel n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E) :
    simulateQ impl (pcsProveH call3H call3F fuel n tree stack pt v) =
      pcsProveH (fun x ↦ simulateQ impl (call3H x)) (fun s ↦ simulateQ impl (call3F s)) fuel n tree stack pt v := by
  rw [← implH_iota3, ← implF_iota3, ← simulateQ_pcsProveH iota3, ← QueryImpl.simulateQ_compose,
    simulateQ_pcsProveH, implH_comp_iota3, implF_comp_iota3]
  rfl

/-- **The experiment over three calls commutes with every simulation.** -/
theorem simulateQ_exp3 (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ impl (expW4 call3H call3W call3F D input rows q) =
      expW4 (fun x ↦ simulateQ impl (call3H x)) (fun x ↦ simulateQ impl (call3W x))
        (fun s ↦ simulateQ impl (call3F s)) D input rows q :=
  app_expW4 (Morph.sim impl) call3H call3W call3F (fun _n zOf x proof ↦ simulateQ_pcsVerify_iota3 impl zOf x proof)
    (fun fuel _n tree stack pt v ↦ simulateQ_pcsProveH_iota3 impl fuel _n tree stack pt v) D input rows q

end Sim3

/-- **The experiment over π1-rec4's calls is the three calls' read by `nu3`.** -/
theorem simulateQ_nu3_exp3 (D : KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ nu3 (expW4 call3H call3W call3F D input rows q) = expW4 hashW callRate callFW D input rows q := by
  rw [simulateQ_exp3]
  rfl

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.experiment4_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.experiment4_eq
