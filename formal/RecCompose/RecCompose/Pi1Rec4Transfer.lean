-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The facts transferred are `formal/UniKeccakComplete`'s
-- (`K/Rec4CostBound.lean`'s `costP_proveRec4With`, `proverBlocks4_reference`; `K/Rec4Cost.lean`'s `rateSigma`,
-- `rateMix_surj`); the discipline is walked as `K/Rec4Duplex.lean`'s `discW_uniProverRec4With` (the hash-only parts
-- read off the morphism calculus) over leanerVM's two calls. Ported from this library's π1-rec3 version
-- (`Pi1KeccakTransfer.lean`, retired). Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0): the two calls `KeccakCalls`, `HOnly`, the block cost `hashBlocks`,
-- `QueryCostAtMost`; VCVio's `simulateQ`, `IsQueryBound`; and `formal/EndToEnd/Completeness/E2ECompleteness`'s
-- `Disc`, `HashOK`.
import RecCompose.Pi1Rec4Prover
import UniKeccakComplete.K.Rec4End

/-!
# The recursion's π1-rec4 prover: discipline, block count, and the hash queries of UniKeccakComplete's prover

`p1kK4 D` (`Pi1Rec4Prover.lean`) is π1-rec4's prover over leanerVM's two calls with its Fiat–Shamir hash and rate the
pure `keccak256`, `rateKF`: its only calls are its trees' Keccak-256s and WHIR's (the three openings).

* **The discipline, walked** (**`disc_p1kK4`**): the setup's tree, the IV, the seed and the stream only hash (the
  stream is a simulation of the hash alone, `hOnly_simulateQ_hash`, its draws being pure); the permutation is called
  by the three openings only, each disciplined (`disc_pcsProveH`).
* **The transfer from UniKeccakComplete's prover.** `p1kK4` and UniKeccakComplete's prover at `H = callKeccak256`,
  `W = rateSigma` (the one π1-rec4's block count is proved for, `costP_proveRec4With`) are simulations of **one program
  over four calls** (`FsCalls4`: the Fiat–Shamir hash `qFs`, its rate `qW`, the trees' hash `qH`, the permutation
  `qF`), `uprover4 D = uniProverRec4With2 qFs qW qH qF D` (`sim_uprover4_old`, `sim_uprover4_new`). A fact holding on
  every path and only weakening when a call is dropped transfers from the first to the second, by induction on the
  four-call program, a `qW` call of the first reaching every rate (`rateMix_surj`):
  - **`qc_new4`** (a block count), hence **`qc_p1kK4`**: at most `2^47` block calls at the reference shape
    (`costP_proveRec4With`, `proverBlocks4_reference`);
  - **`hashOK_new4`** (every hash query satisfies `P`), hence **`hashOK_p1kK4_of`**, for the census
    (`Pi1Rec4Census.lean`).
-/

set_option autoImplicit false

namespace RecCompose.Pi1K

open UniStatement LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open UniKeccakComplete UniKeccakComplete.Rec4
open LeanVM.Protocol.Compile.Rom (implH implF)
open E2ECompleteness (Disc HashOK disc_of_hOnly)
open RecStatement (RecDeployment)

/-! ## The discipline -/

/-- **The stream with its Fiat–Shamir pure only hashes**: it is the hash alone's stream, simulated. -/
theorem hOnly_stream4 (tr : Trace) (w : UniComplete.Wr) :
    HOnly ((proveStreamRec4With hKF wKF (commitReal callKeccak256) tr).run w) := by
  have h := wr_proveStreamRec4With (Morph.sim hashToCalls) hKF wKF (commitReal callHash)
    (commitReal fun x ↦ (Morph.sim hashToCalls).app (callHash x)) (Morph.app_commitReal (Morph.sim hashToCalls) callHash)
    tr
  rw [sim_callHash, sim_hKF, sim_wKF] at h
  rw [← h, Morph.wr_run]
  exact hOnly_simulateQ_hash _

/-- **The recursion's π1-rec4 prover is disciplined**, from any earlier answers. -/
theorem disc_p1kK4 (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) :
    Disc (p1kK4 D input rows q) := by
  show Disc (proveRec4With2 hKF wKF callKeccak256 callKeccakF1600 _ _ _)
  unfold proveRec4With2
  refine (disc_of_hOnly (hOnly_setupTreeOf _)).bind fun tree ↦ ?_
  refine (disc_of_hOnly ((hOnly_pure _).bind fun _ ↦ hOnly_pure _)).bind fun iv ↦ ?_
  refine (disc_of_hOnly (hOnly_pure _)).bind fun seed ↦ ?_
  refine (disc_of_hOnly (hOnly_stream4 _ _)).bind fun x ↦ ?_
  obtain ⟨out, _⟩ := x
  dsimp only
  unfold Rec3.openingsTail3
  generalize List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    dsimp only <;>
    repeat (first
      | exact E2ECompleteness.disc_pure _
      | refine (disc_pcsProveH _ _ _ _ _ _).bind fun _ ↦ ?_
      | refine (E2ECompleteness.disc_pure _).bind fun _ ↦ ?_)

/-! ## Four calls -/

/-- **The four calls**: the Fiat–Shamir hash, its rate, then the two calls (the trees' Keccak-256, Keccak-f[1600]). -/
abbrev FsCalls4 : OracleSpec (List UInt8 ⊕ (List UInt8 ⊕ (List UInt8 ⊕ KeccakState))) :=
  (List UInt8 →ₒ Digest) + ((List UInt8 →ₒ RateB) + KeccakCalls)

/-- The Fiat–Shamir hash's call. -/
def qFs (x : List UInt8) : OracleComp FsCalls4 Digest := liftM (FsCalls4.query (.inl x))

/-- The Fiat–Shamir rate's call. -/
def qW (x : List UInt8) : OracleComp FsCalls4 RateB := liftM (FsCalls4.query (.inr (.inl x)))

/-- The trees' hash's call. -/
def qH (x : List UInt8) : OracleComp FsCalls4 Digest := liftM (FsCalls4.query (.inr (.inr (.inl x))))

/-- The permutation's call. -/
def qF (s : KeccakState) : OracleComp FsCalls4 KeccakState := liftM (FsCalls4.query (.inr (.inr (.inr s))))

/-- The two calls inside the four. -/
def liftImpl4 : QueryImpl KeccakCalls (OracleComp FsCalls4) := fun t ↦ liftM (FsCalls4.query (.inr (.inr t)))

/-- **UniKeccakComplete's reading**: the Fiat–Shamir and the trees' calls `callKeccak256`, the rate `rateSigma`
(a digest query and a permutation call). -/
def implOld4 : QueryImpl FsCalls4 (OracleComp KeccakCalls)
  | .inl x => callKeccak256 x
  | .inr (.inl x) => rateSigma x
  | .inr (.inr t) => liftM (KeccakCalls.query t)

/-- **The Fiat–Shamir pure** (`keccak256`, `rateKF`), the two calls as they are. -/
def implNew4 : QueryImpl FsCalls4 (OracleComp KeccakCalls)
  | .inl x => pure (keccak256 x)
  | .inr (.inl x) => pure (rateKF x)
  | .inr (.inr t) => liftM (KeccakCalls.query t)

theorem sim_old4_lift {α : Type} (X : OracleComp KeccakCalls α) :
    simulateQ implOld4 (simulateQ liftImpl4 X) = X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, liftImpl4, implOld4, ih]

theorem sim_new4_lift {α : Type} (X : OracleComp KeccakCalls α) :
    simulateQ implNew4 (simulateQ liftImpl4 X) = X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, liftImpl4, implNew4, ih]

/-- The opening over four calls is the lifted two-call one. -/
theorem open_lift4 (fuel n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E) :
    pcsProveH qH qF fuel n tree stack pt v =
      simulateQ liftImpl4 (pcsProveH callKeccak256 callKeccakF1600 fuel n tree stack pt v) := by
  rw [simulateQ_pcsProveH liftImpl4]
  rfl

theorem sim_old4_qFs : (fun x ↦ (Morph.sim implOld4).app (qFs x)) = callKeccak256 := by
  funext x
  exact simulateQ_spec_query implOld4 (.inl x)

theorem sim_old4_qW : (fun x ↦ (Morph.sim implOld4).app (qW x)) = rateSigma := by
  funext x
  exact simulateQ_spec_query implOld4 (.inr (.inl x))

theorem sim_old4_qH : (fun x ↦ (Morph.sim implOld4).app (qH x)) = callKeccak256 := by
  funext x
  exact simulateQ_spec_query implOld4 (.inr (.inr (.inl x)))

theorem sim_old4_qF : (fun s ↦ (Morph.sim implOld4).app (qF s)) = callKeccakF1600 := by
  funext s
  exact simulateQ_spec_query implOld4 (.inr (.inr (.inr s)))

theorem sim_new4_qFs : (fun x ↦ (Morph.sim implNew4).app (qFs x)) = hKF := by
  funext x
  exact simulateQ_spec_query implNew4 (.inl x)

theorem sim_new4_qW : (fun x ↦ (Morph.sim implNew4).app (qW x)) = wKF := by
  funext x
  exact simulateQ_spec_query implNew4 (.inr (.inl x))

theorem sim_new4_qH : (fun x ↦ (Morph.sim implNew4).app (qH x)) = callKeccak256 := by
  funext x
  exact simulateQ_spec_query implNew4 (.inr (.inr (.inl x)))

theorem sim_new4_qF : (fun s ↦ (Morph.sim implNew4).app (qF s)) = callKeccakF1600 := by
  funext s
  exact simulateQ_spec_query implNew4 (.inr (.inr (.inr s)))

/-! ## The program over four calls -/

/-- **π1-rec4's honest prover over four calls.** -/
def uprover4 (D : UniKeccak.KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    OracleComp FsCalls4 (Option UniKeccak.KeccakProof) :=
  uniProverRec4With2 qFs qW qH qF D input rows q

/-- **Read as UniKeccakComplete reads it**, its prover at `H = callKeccak256`, `W = rateSigma`. -/
theorem sim_uprover4_old (D : UniKeccak.KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    simulateQ implOld4 (uprover4 D input rows q) =
      uniProverRec4With callKeccak256 rateSigma callKeccakF1600 D input rows q := by
  have h := app_proveRec4With2 (Morph.sim implOld4) qFs qW qH qF
    (fun fuel n tree stack pt v ↦ by
      rw [sim_old4_qH, sim_old4_qF, open_lift4]
      exact sim_old4_lift _)
    PcsQuotient.nonceFuel D.programIv (honestTrace D input rows q)
  rw [sim_old4_qFs, sim_old4_qW, sim_old4_qH, sim_old4_qF] at h
  exact h

/-- **Answered with the Fiat–Shamir pure**, the recursion's π1-rec4 prover over the two calls. -/
theorem sim_uprover4_new (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) :
    simulateQ implNew4 (uprover4 D.pi1 input rows q) = p1kK4 D input rows q := by
  have h := app_proveRec4With2 (Morph.sim implNew4) qFs qW qH qF
    (fun fuel n tree stack pt v ↦ by
      rw [sim_new4_qH, sim_new4_qF, open_lift4]
      exact sim_new4_lift _)
    PcsQuotient.nonceFuel D.pi1.programIv (honestTrace D.pi1 input rows q)
  rw [sim_new4_qFs, sim_new4_qW, sim_new4_qH, sim_new4_qF] at h
  exact h

/-! ## The transfers -/

section Transfer

variable {α : Type}

/-- **A block count transfers**: a dropped call's blocks are left over (a rate call of the first reaches every
rate, `rateMix_surj`). -/
theorem qc_new4 (X : OracleComp FsCalls4 α) :
    ∀ (n n' : ℕ), Common.QueryCostAtMost (simulateQ implOld4 X) hashBlocks n → n ≤ n' →
      Common.QueryCostAtMost (simulateQ implNew4 X) hashBlocks n' := by
  induction X using OracleComp.inductionOn with
  | pure a => intro _ _ _ _; simp only [simulateQ_pure]; trivial
  | query_bind t k ih =>
    intro n n' hX hn
    rw [simulateQ_bind, simulateQ_spec_query] at hX ⊢
    rcases t with x | (x | t)
    · rw [implOld4, callKeccak256, Common.isWeightBound_query_bind_iff] at hX
      rw [implNew4, pure_bind]
      exact ih _ _ _ (hX.2 _) (by omega)
    · have hX' : Common.QueryCostAtMost (rateSigma x >>= fun u ↦ simulateQ implOld4 (k u)) hashBlocks n := hX
      simp only [rateSigma, bind_assoc, pure_bind] at hX'
      rw [callKeccak256, Common.isWeightBound_query_bind_iff] at hX'
      rw [implNew4, pure_bind]
      obtain ⟨d, st, hr⟩ := rateMix_surj (rateKF x)
      have h2 := hX'.2 d
      rw [callKeccakF1600, Common.isWeightBound_query_bind_iff] at h2
      have h3 := h2.2 st
      rw [hr] at h3
      exact ih _ _ _ h3 (by omega)
    · rw [implOld4, Common.isWeightBound_query_bind_iff] at hX
      rw [implNew4, Common.isWeightBound_query_bind_iff]
      exact ⟨hX.1.trans hn, fun u ↦ ih u _ _ (hX.2 u) (by omega)⟩

/-- **Every hash query satisfying `P` transfers** (the dropped calls' queries are not checked any more). -/
theorem hashOK_new4 (P : List UInt8 → Prop) (X : OracleComp FsCalls4 α) :
    HashOK P (simulateQ implOld4 X) → HashOK P (simulateQ implNew4 X) := by
  induction X using OracleComp.inductionOn with
  | pure a => intro _; simp only [simulateQ_pure]; trivial
  | query_bind t k ih =>
    intro hX
    rw [simulateQ_bind, simulateQ_spec_query] at hX ⊢
    rcases t with x | (x | t)
    · rw [implOld4, callKeccak256, HashOK, isQueryBound_query_bind_iff] at hX
      rw [implNew4, pure_bind]
      exact ih _ (hX.2 _)
    · have hX' : HashOK P (rateSigma x >>= fun u ↦ simulateQ implOld4 (k u)) := hX
      simp only [rateSigma, bind_assoc, pure_bind] at hX'
      rw [callKeccak256, HashOK, isQueryBound_query_bind_iff] at hX'
      rw [implNew4, pure_bind]
      obtain ⟨d, st, hr⟩ := rateMix_surj (rateKF x)
      have h2 := hX'.2 d
      rw [callKeccakF1600, isQueryBound_query_bind_iff] at h2
      have h3 := h2.2 st
      rw [hr] at h3
      exact ih _ h3
    · rw [implOld4, HashOK, isQueryBound_query_bind_iff] at hX
      rw [implNew4, HashOK, isQueryBound_query_bind_iff]
      exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

end Transfer

/-! ## The real deployment's π1 -/

/-- The reference shapes of RecGraphKeccak and UniKeccakSound are one. -/
theorem keccak128_eq_refShape : RecGraphKeccak.Pi1.keccak128 = UniKeccakSound.keccakRefShape := rfl

/-- leanVM's program IV: `32` bytes. -/
theorem programIv_length32 : UniStatement.programIv.length = 32 := by decide +kernel

/-- **The real deployment's π1 is at the reference shape.** -/
theorem real_shape {D : RecDeployment} (hD : D.Real) : D.pi1.shape = UniKeccakSound.keccakRefShape :=
  hD.2.2.1.trans keccak128_eq_refShape

/-- **The real deployment's program IV has at most `2^16` bytes** (`32`). -/
theorem real_programIv {D : RecDeployment} (hD : D.Real) : D.pi1.programIv.length ≤ 2 ^ 16 := by
  rw [hD.2.2.2.1, programIv_length32]
  norm_num

/-- **The real deployment's program IV has at least `32` bytes** (`32`). -/
theorem real_programIv32 {D : RecDeployment} (hD : D.Real) : 32 ≤ D.pi1.programIv.length := by
  rw [hD.2.2.2.1, programIv_length32]

/-- **The real deployment's honest relation is UniKeccakComplete's** (the Keccak-f block `keccakFlockSpec`). -/
theorem real_honest {D : RecDeployment} (hD : D.Real) {rows : List ℕ} {input : Vector UInt8 32}
    {q : D.pi1.Stack rows} (h : D.pi1.HonestRelation D.flock rows input q) :
    D.pi1.HonestRelation KeccakFlock.keccakFlockSpec rows input q := by
  rw [← hD.2.2.2.2.2.2.2]
  exact h

/-! ## The recursion's π1-rec4 prover's block count and hash queries -/

/-- **The recursion's π1-rec4 prover makes at most `2^47` block calls** at the reference shape (UniKeccakComplete's
prover's count at `W = rateSigma`, `costP_proveRec4With`, transferred: its Fiat–Shamir hashes and rates are no
calls). -/
theorem qc_p1kK4 (D : RecDeployment) (hD : D.pi1.shape = UniKeccakSound.keccakRefShape)
    (hIv : D.pi1.programIv.length ≤ 2 ^ 16) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows)
    (hfit : D.pi1.shape.RowsFit rows) :
    Common.QueryCostAtMost (p1kK4 D input rows q) hashBlocks (2 ^ 47) := by
  rw [← sim_uprover4_new]
  refine qc_new4 _ _ _ ?_ le_rfl
  rw [sim_uprover4_old]
  have h := Cost.CostP.toQC (costP_proveRec4With D.pi1.programIv (honestTrace D.pi1 input rows q)
    (by simp [honestTrace]))
  have hr : (honestTrace D.pi1 input rows q).rows.length = 6 := hfit.1
  rw [hr] at h
  exact h.mono (proverBlocks4_reference D.pi1 hD hIv)

/-- **Every hash query of the recursion's π1-rec4 prover satisfies `P`** when every one of UniKeccakComplete's
prover's at `W = rateSigma` does. -/
theorem hashOK_p1kK4_of (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows)
    (P : List UInt8 → Prop)
    (h : HashOK P (uniProverRec4With callKeccak256 rateSigma callKeccakF1600 D.pi1 input rows q)) :
    HashOK P (p1kK4 D input rows q) := by
  rw [← sim_uprover4_new]
  refine hashOK_new4 P _ ?_
  rw [sim_uprover4_old]
  exact h

end RecCompose.Pi1K

/-- info: 'RecCompose.Pi1K.disc_p1kK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.disc_p1kK4

/-- info: 'RecCompose.Pi1K.qc_p1kK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.qc_p1kK4

/-- info: 'RecCompose.Pi1K.hashOK_p1kK4_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.hashOK_p1kK4_of
