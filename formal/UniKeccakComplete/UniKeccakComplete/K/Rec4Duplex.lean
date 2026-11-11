-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. leanerVM's duplex discipline
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `lean_vm/LeanVM/Protocol/Rpm/Duplex.lean`, `DuplexP` and its rules) over π1-rec4's calls; the hash-only parts read
-- off the morphism calculus, as `VerifierHDuplex.lean` does; the openings through `PcsProver.lean`'s `disc_pcsProveH`,
-- `disc_pcsVerify`.
import UniKeccakComplete.K.Rec4ProbK
import UniKeccakComplete.K.VerifierHDuplex

/-!
# π1-rec4's experiment follows the duplex discipline (`ExpDuplex4`)

Over π1-rec4's calls (`KeccakCallsW`), **`expDuplex4`**: every permutation call of the experiment (`expW4 hashW
callRate callFW`) continues a duplex or starts one at a zero capacity (`DuplexW`, leanerVM's `DuplexVm`).

* **The discipline with a postcondition** (`DuplexPW`, leanerVM's `DuplexP` over `KeccakCallsW`) and its rules
  (`DuplexPW.bind`, `.mono`), `DiscW` (from any earlier answers);
* **what leanerVM's two calls read through `nuW` keep**: `DuplexP X h Q → DuplexPW (simulateQ nuW X) h Q`
  (`duplexPW_nuW`), so the PCS openings and checks over the rate call are disciplined (`disc_pcsProveH`,
  `disc_pcsVerify`);
* **the hash-only parts**, by naturality: what the rate call alone (`RateCalls`) simulates keeps the answers
  (`duplexPW_rateOnly`); the setup, the IV, the seed, the stream and the verifier's walk are such simulations by the
  morphism calculus (`Morph.app_…`, `wr_proveStreamRec4With`, `app_runWithKH4`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open LeanVM.Protocol.Compile.Rom (implH implF)
open UniStatement UniKeccak
open E2ECompleteness (Disc)

set_option autoImplicit false

namespace UniKeccakComplete.Rec4

/-! ## The discipline over π1-rec4's calls -/

/-- **The duplex discipline with a postcondition** over π1-rec4's calls (leanerVM's `DuplexP`). -/
def DuplexPW {α : Type} :
    OracleComp KeccakCallsW α → List KeccakState → (α → List KeccakState → Prop) → Prop
  | .pure a, h, Q => Q a h
  | .liftBind (.inr x) k, h, Q => AdmissibleVm h x ∧ ∀ y, DuplexPW (k y) (y :: h) Q
  | .liftBind _ k, h, Q => ∀ u, DuplexPW (k u) h Q

section Rules

variable {α β : Type}

theorem duplexPW_query_bind (t : KeccakCallsW.Domain) (k : KeccakCallsW.Range t → OracleComp KeccakCallsW α)
    (h : List KeccakState) (Q : α → List KeccakState → Prop) :
    DuplexPW (liftM (KeccakCallsW.query t) >>= k) h Q ↔
      match t with
      | .inr x => AdmissibleVm h x ∧ ∀ y, DuplexPW (k y) (y :: h) Q
      | .inl _ => ∀ u, DuplexPW (k u) h Q := by
  rcases t with x | x <;> exact Iff.rfl

theorem duplexW_query_bind (t : KeccakCallsW.Domain) (k : KeccakCallsW.Range t → OracleComp KeccakCallsW α)
    (h : List KeccakState) :
    DuplexW (liftM (KeccakCallsW.query t) >>= k) h ↔
      match t with
      | .inr x => AdmissibleVm h x ∧ ∀ y, DuplexW (k y) (y :: h)
      | .inl _ => ∀ u, DuplexW (k u) h := by
  rcases t with x | x <;> exact Iff.rfl

theorem duplexW_iff_duplexPW (X : OracleComp KeccakCallsW α) (h : List KeccakState) :
    DuplexW X h ↔ DuplexPW X h fun _ _ ↦ True := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => exact Iff.rfl
  | query_bind t k ih =>
    rw [duplexW_query_bind, duplexPW_query_bind]
    rcases t with x | x
    · exact forall_congr' fun u ↦ ih u h
    · exact and_congr Iff.rfl (forall_congr' fun y ↦ ih y _)

theorem DuplexPW.mono {X : OracleComp KeccakCallsW α} {h : List KeccakState}
    {Q R : α → List KeccakState → Prop} (hX : DuplexPW X h Q) (hQR : ∀ a h', Q a h' → R a h') :
    DuplexPW X h R := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => exact hQR a h hX
  | query_bind t k ih =>
    rw [duplexPW_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u)
    · exact ⟨hX.1, fun y ↦ ih y (hX.2 y)⟩

theorem DuplexPW.bind {X : OracleComp KeccakCallsW α} {f : α → OracleComp KeccakCallsW β}
    {h : List KeccakState} {Q : α → List KeccakState → Prop} {R : β → List KeccakState → Prop}
    (hX : DuplexPW X h Q) (hf : ∀ a h', Q a h' → DuplexPW (f a) h' R) :
    DuplexPW (X >>= f) h R := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => simpa using hf a h hX
  | query_bind t k ih =>
    rw [bind_assoc]
    rw [duplexPW_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u)
    · exact ⟨hX.1, fun y ↦ ih y (hX.2 y)⟩

/-- Disciplined from any earlier answers. -/
def DiscW (X : OracleComp KeccakCallsW α) : Prop := ∀ h : List KeccakState, DuplexPW X h fun _ _ ↦ True

theorem DiscW.bind {X : OracleComp KeccakCallsW α} {f : α → OracleComp KeccakCallsW β}
    (hX : DiscW X) (hf : ∀ a, DiscW (f a)) : DiscW (X >>= f) :=
  fun h ↦ (hX h).bind fun a h' _ ↦ hf a h'

theorem discW_pure (a : α) : DiscW (pure a : OracleComp KeccakCallsW α) := fun _ ↦ trivial

/-- **leanerVM's two calls read through `nuW` keep the discipline.** -/
theorem duplexPW_nuW {X : OracleComp KeccakCalls α} {h : List KeccakState} {Q : α → List KeccakState → Prop}
    (hX : DuplexP X h Q) : DuplexPW (simulateQ nuW X) h Q := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => exact hX
  | query_bind t k ih =>
    rw [duplexP_query_bind] at hX
    rw [simulateQ_query_bind]
    rcases t with x | s
    · show DuplexPW ((digestOfRate <$> callRate x) >>= fun d ↦ simulateQ nuW (k d)) h Q
      rw [bind_map_left]
      exact fun u ↦ ih _ (hX _)
    · exact ⟨hX.1, fun y ↦ ih y (hX.2 y)⟩

theorem discW_nuW {X : OracleComp KeccakCalls α} (hX : Disc X) : DiscW (simulateQ nuW X) :=
  fun h ↦ duplexPW_nuW (hX h)

/-! ## The rate call alone -/

/-- **The rate call alone**, as an oracle. -/
abbrev RateCalls : OracleSpec Bytes := (Bytes →ₒ RateB)

/-- A call of the rate alone. -/
def callR (x : Bytes) : OracleComp RateCalls RateB := liftM (RateCalls.query x)

/-- The rate alone, answered by π1-rec4's calls. -/
def rateToW : QueryImpl RateCalls (OracleComp KeccakCallsW) := fun x ↦ callRate x

/-- **What the rate alone simulates keeps the answers.** -/
theorem duplexPW_rateOnly (Y : OracleComp RateCalls α) (h : List KeccakState) :
    DuplexPW (simulateQ rateToW Y) h fun _ h' ↦ h' = h := by
  induction Y using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [simulateQ_query_bind]
    exact fun u ↦ ih u

theorem discW_rateOnly (Y : OracleComp RateCalls α) : DiscW (simulateQ rateToW Y) :=
  fun h ↦ (duplexPW_rateOnly Y h).mono fun _ _ _ ↦ trivial

/-- The hash over the rate alone. -/
def hashR (x : Bytes) : OracleComp RateCalls Digest := digestOfRate <$> callR x

theorem sim_hashR : (fun x ↦ (Morph.sim rateToW).app (hashR x)) = hashW := by
  funext x
  show simulateQ rateToW (digestOfRate <$> callR x) = digestOfRate <$> callRate x
  rw [simulateQ_map]
  unfold callR
  rw [simulateQ_spec_query]
  rfl

theorem sim_callR : (fun x ↦ (Morph.sim rateToW).app (callR x)) = callRate := by
  funext x
  show simulateQ rateToW (callR x) = callRate x
  unfold callR
  rw [simulateQ_spec_query]
  rfl

end Rules

/-! ## The experiment -/

variable (D : KDeployment)

theorem discW_commitWithH (μ : ℕ) (stack : Array K) : DiscW (E2ECompleteness.commitWithH hashW μ stack) := by
  have h := Morph.app_commitWithH (Morph.sim rateToW) hashR μ stack
  rw [sim_hashR] at h
  rw [← h]
  exact discW_rateOnly _

theorem discW_pcsProveH (fuel n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E) :
    DiscW (pcsProveH hashW callFW fuel n tree stack pt v) := by
  rw [← implH_nuW, ← implF_nuW, ← simulateQ_pcsProveH nuW]
  exact discW_nuW (disc_pcsProveH _ _ _ _ _ _)

theorem discW_pcsOpenKH (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E)
    (proof : LeanVM.Protocol.Compile.Proof) : DiscW (pcsOpenKH hashW callFW n root ood pt v proof) := by
  unfold pcsOpenKH
  split
  · rw [← implH_nuW, ← implF_nuW, ← simulateQ_pcsVerify nuW]
    exact discW_nuW (disc_pcsVerify _ _ _)
  · exact discW_pure _

theorem discW_forIn_list {γ β : Type} (l : List γ) (b : β) (f : γ → β → OracleComp KeccakCallsW (ForInStep β))
    (hf : ∀ a s, DiscW (f a s)) : DiscW (forIn l b f) := by
  induction l generalizing b with
  | nil => exact discW_pure b
  | cons a l ih =>
    rw [List.forIn_cons]
    refine (hf a b).bind fun s ↦ ?_
    cases s with
    | done b => exact discW_pure b
    | yield b => exact ih b

/-- **π1-rec4's honest prover is disciplined.** -/
theorem discW_uniProverRec4With (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    DiscW (uniProverRec4With hashW callRate callFW D input rows q) := by
  unfold uniProverRec4With proveRec4With
  have hset : ∀ tr, setupTreeOf hashW tr = simulateQ rateToW (setupTreeOf hashR tr) := fun tr ↦ by
    have h := Morph.app_setupTreeOf (Morph.sim rateToW) hashR tr
    rw [sim_hashR] at h
    exact h.symm
  have hiv : ∀ s v pIv roots, contractIvOf hashW s v pIv roots = simulateQ rateToW (contractIvOf hashR s v pIv roots) :=
    fun s v pIv roots ↦ by
      have h := Morph.app_contractIvOf (Morph.sim rateToW) hashR s v pIv roots
      rw [sim_hashR] at h
      exact h.symm
  have hseed : ∀ iv pi, seedOf hashW iv pi = simulateQ rateToW (seedOf hashR iv pi) := fun iv pi ↦ by
    have h := Morph.app_seedOf (Morph.sim rateToW) hashR iv pi
    rw [sim_hashR] at h
    exact h.symm
  have hstream : ∀ tr w, (proveStreamRec4With hashW callRate (commitReal hashW) tr).run w =
      simulateQ rateToW ((proveStreamRec4With hashR callR (commitReal hashR) tr).run w) := fun tr w ↦ by
    have h := wr_proveStreamRec4With (Morph.sim rateToW) hashR callR (commitReal hashR)
      (commitReal fun x ↦ (Morph.sim rateToW).app (hashR x)) (Morph.app_commitReal (Morph.sim rateToW) hashR) tr
    rw [sim_hashR, sim_callR] at h
    rw [← h, Morph.wr_run]
    rfl
  rw [hset]
  refine (discW_rateOnly _).bind fun tree ↦ ?_
  rw [hiv]
  refine (discW_rateOnly _).bind fun iv ↦ ?_
  rw [hseed]
  refine (discW_rateOnly _).bind fun seed ↦ ?_
  rw [hstream]
  refine (discW_rateOnly _).bind fun x ↦ ?_
  obtain ⟨out, _⟩ := x
  dsimp only
  unfold Rec3.openingsTail3
  generalize List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    dsimp only <;>
    repeat (first
      | exact discW_pure _
      | refine (discW_pcsProveH _ _ _ _ _ _).bind fun _ ↦ ?_
      | refine (discW_pure _).bind fun _ ↦ ?_)

/-- **π1-rec4's deployed verifier is disciplined.** -/
theorem discW_verifierWith4H (roots : SetupRootsK) (input : Vector UInt8 32) (proof : KeccakProof) :
    DiscW (KDeployment.verifierWith4H hashW callRate callFW D roots input proof) := by
  unfold KDeployment.verifierWith4H verifyWithKH4
  have hiv : KDeployment.ivWithH hashW D keccakRec4 roots =
      simulateQ rateToW (KDeployment.ivWithH hashR D keccakRec4 roots) := by
    have h := Morph.app_ivWithH (Morph.sim rateToW) hashR D keccakRec4 roots
    rw [sim_hashR] at h
    exact h.symm
  have hrun : ∀ (iv : List UInt8), runWithKH4 hashW callRate D.shape iv input.toList proof.stream keccakRec4 .point =
      simulateQ rateToW (runWithKH4 hashR callR D.shape iv input.toList proof.stream keccakRec4 .point) := fun iv ↦ by
    have h := app_runWithKH4 (Morph.sim rateToW) hashR callR D.shape iv input.toList proof.stream keccakRec4 .point
    rw [sim_hashR, sim_callR] at h
    exact h.symm
  rw [hiv]
  refine (discW_rateOnly _).bind fun iv ↦ ?_
  rw [hrun]
  refine (discW_rateOnly _).bind fun o ↦ ?_
  split
  · exact discW_pure _
  · split
    · exact discW_pure _
    · refine (discW_forIn_list _ _ _ fun x s ↦ ?_).bind fun s ↦ ?_
      · split
        split
        · exact (discW_pcsOpenKH _ _ _ _ _ _).bind fun _ ↦ discW_pure _
        · exact discW_pure _
      · split <;> exact discW_pure _

/-- **π1-rec4's experiment follows the duplex discipline.** -/
theorem expDuplex4 : ExpDuplex4 D := by
  intro input rows q _ _
  rw [duplexW_iff_duplexPW]
  refine DiscW.bind ?_ (fun tree ↦ DiscW.bind (discW_uniProverRec4With D input rows q) fun o ↦ ?_) []
  · exact discW_commitWithH _ _
  · cases o with
    | none => exact discW_pure _
    | some proof => exact discW_verifierWith4H D _ input proof

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.expDuplex4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.expDuplex4
