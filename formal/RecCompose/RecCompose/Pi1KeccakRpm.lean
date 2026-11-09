-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The statement read is `formal/RecStatement`'s
-- (`Pi1CompletenessKeccak`, `pi1KeccakVerifierWith`); its random-permutation reading is `formal/UniKeccak`'s
-- `UniCompletenessKeccakRec3` (`Security.lean`), proved by `formal/UniKeccakComplete`'s
-- `uniCompletenessKeccakRec3_closed`. The eager form of the
-- random-permutation model is `formal/EndToEnd/ZK/ProverBridgeEager.lean`'s; Keccak-256 through a monad morphism
-- `ProverBridgeParam.lean`'s (`keccak256With_hom`); VCVio's `prEvent_bind_mono_of_forall_le`.
import RecCompose.Pi1KeccakTransfer
import UniKeccakComplete.K.EndClosed
import ZK.ProverBridgeParam
import ZK.ProverBridgeEager

/-!
# `Pi1CompletenessKeccak` at the recursion's π1 prover: what it says, and its random-permutation reading

`RecStatement.Pi1CompletenessKeccak D P1 δ1` is a **premise** of the end-to-end completeness theorems: π1-rec3's honest
proof, its Fiat–Shamir over the real Keccak-f[1600], its openings over the random permutation `π`, is rejected by the
Keccak π1-rec3's verifier at Keccak-f[1600] (`pi1KeccakVerifierWith`, openings over `π`) with probability at most `δ1`.
At the recursion's prover `pi1Rec3ProverK` (`Pi1KeccakProver.lean`) prover and verifier hash the Fiat–Shamir with the
same Keccak-f[1600]. This file makes the premise's content explicit:

* **`pi1VerifierFsWith Φ F`**: `pi1KeccakVerifierWith` with its Fiat–Shamir over a permutation `Φ` (the Keccak
  contract's IV `contractIvKWith Φ … keccakRec3`, the run `runWithK Φ … keccakRec3 .point`), its openings over `F`; at
  `Φ = pure ∘ keccakF1600` it is `pi1KeccakVerifierWith` (**`pi1VerifierFsWith_kf`**, any lawful monad); at `Φ = F` it
  is the deployed Keccak verifier `KDeployment.verifierWith F keccakRec3` (**`verifierFs_eq`**, as programs: the matrices'
  check is in both).
* **`pi1FsCompletenessExperiment D Φ`**, **`Pi1CompletenessFs D Φ δ`**: the completeness experiment with
  Keccak-f[1600] replaced by `Φ` on both sides (the prover's Fiat–Shamir `keccak256With Φ`, the verifier's `Φ`), the
  trees and openings over `π`.
* **The Keccak reading** (**`pi1CompletenessKeccak_iff`**): `Pi1CompletenessKeccak D (pi1Rec3ProverK D) δ ↔
  Pi1CompletenessFs D (pure ∘ keccakF1600) δ`.
* **The random-permutation reading, proved** (**`pi1CompletenessFs_rpm`**): at `Φ = π` (Keccak-f[1600] read as the
  random permutation, one permutation for the Fiat–Shamir and the openings) the experiment is π1-rec3's own
  (`keccakCompletenessExperiment … keccakRec3` of `uniProverRec3RP flockProveH`, `pi1ProverFs_rpm`), but for π2's
  setup tree, built and unused; so `Pi1CompletenessFs D π deltaK` at the real deployment, from
  `uniCompletenessKeccakRec3_closed`, `deltaK < 2^-169`.

**The gap, stated plainly.** Nothing here proves the Keccak reading. `Pi1CompletenessKeccak D (pi1Rec3ProverK D) δ1`
is the heuristic "Keccak-f[1600] behaves as the random permutation for this fixed honest prover": the experiment at
`Φ = pure ∘ keccakF1600` has the error of the experiment at `Φ = π`, which is proved below `2^-169`. It is a heuristic
about one fixed, efficient, honest prover (no adversary: nobody grinds), the weakest form of the Fiat–Shamir heuristic;
it is not implied by anything proved, since a fixed function is not a random permutation (the model gap of the
recursion: π2's circuit computes the real Keccak-f[1600]).
-/

set_option autoImplicit false

namespace RecCompose.Pi1K

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec Common
open UniKeccakComplete
open RecStatement (RecDeployment Pi1Prover)
open PcsQuotient.EndToEnd.Eager
open scoped ENNReal

/-! ## The verifier with its Fiat–Shamir over `Φ` -/

section With

variable {m : Type → Type} [Monad m] (Φ F : KeccakState → m KeccakState)

/-- **The Keccak π1-rec3's verifier with its Fiat–Shamir over `Φ`** and its three openings over `F`:
`pi1KeccakVerifierWith` with `contractIvKWith Φ` and `runWithK Φ` for `pi1Iv` and `runK`. -/
def pi1VerifierFsWith (D : UniKeccak.KDeployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (proof : UniKeccak.KeccakProof) : m Bool := do
  let iv ← UniKeccak.contractIvKWith Φ D.shape UniKeccak.keccakRec3 D.programIv roots
  let o ← UniKeccak.runWithK Φ D.shape iv input.toList proof.stream UniKeccak.keccakRec3 .point
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let words := UniKeccak.layoutWordsK D.shape
    let callOf : UniStatement.Commitment → Digest × List UInt8 × Compile.Proof
      | .c1 => (UniStatement.rootOf r.roots.1, words.getD 0 [], proof.c1)
      | .c2 => (UniStatement.rootOf r.roots.2, words.getD 1 [], proof.c2)
      | .setup => (roots.bytecode, words.getD 2 [], proof.setup)
    let mut ok := r.openings.map (·.1) == UniStatement.commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        let (root, word, p) := callOf c
        ok := ok && (← UniStatement.pcsOpenWith F (UniStatement.layoutWordVars word) root [⟨pt, value⟩] p)
      | _ => ok := false
    if r.matrices.isSome then ok := false
    return ok

end With

section Lawful

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- `pure ∘ Id.run`, a morphism from `Id` (UniKeccakComplete's kind). -/
def idMorph : Morph Id m := ⟨fun x ↦ pure (Id.run x), fun _ ↦ rfl, fun x f ↦ by simp⟩

/-- `pure ∘ Id.run`, a morphism from `Id` (`ZK`'s kind). -/
def idMHom : PcsQuotient.EndToEnd.MHom Id m := ⟨fun x ↦ pure (Id.run x), fun _ ↦ rfl, fun x f ↦ by simp⟩

/-- **Keccak-256 over the real Keccak-f[1600], in any lawful monad, is the pure `keccak256`.** -/
theorem keccak256With_kf (x : List UInt8) :
    keccak256With (m := m) (fun s ↦ pure (keccakF1600 s)) x = pure (KeccakHash.keccak256 x) := by
  have h := PcsQuotient.EndToEnd.Param.keccak256With_hom (idMHom (m := m)) (fun s ↦ (pure (keccakF1600 s) : Id _)) x
  simp only [idMHom] at h
  exact h.symm

theorem keccak256With_kf_fun :
    keccak256With (m := m) (fun s ↦ pure (keccakF1600 s)) = hKF := funext keccak256With_kf

/-- The Keccak contract's IV over the real Keccak-f[1600], in any lawful monad: the pure `contractIvK`. -/
theorem contractIvKWith_kf (s : UniStatement.Shape) (v : UniKeccak.KeccakVariant) (programIv : List UInt8)
    (roots : SetupRoots) :
    UniKeccak.contractIvKWith (m := m) (fun x ↦ pure (keccakF1600 x)) s v programIv roots =
      pure (UniKeccak.contractIvK s v programIv roots) := by
  unfold UniKeccak.contractIvKWith
  rw [keccak256With_kf, pure_bind]
  rfl

/-- The Keccak verifier's run over the real Keccak-f[1600], in any lawful monad: the pure `runK`. -/
theorem runWithK_kf (shape : UniStatement.Shape) (iv publicInput : List UInt8) (stream : Array UInt8)
    (v : UniKeccak.KeccakVariant) (mode : ClaimsMode) :
    UniKeccak.runWithK (m := m) (fun x ↦ pure (keccakF1600 x)) shape iv publicInput stream v mode =
      pure (UniKeccak.runK shape iv publicInput stream v mode) := by
  have h := Morph.app_runWithKH (idMorph (m := m))
    (fun x ↦ (pure (KeccakHash.keccak256 x) : Id Digest)) shape iv publicInput stream v mode
  simp only [idMorph] at h
  have hid : keccak256With (m := Id) (fun x ↦ pure (keccakF1600 x)) =
      fun x ↦ (pure (KeccakHash.keccak256 x) : Id Digest) := rfl
  unfold UniKeccak.runK
  rw [runWithK_eqH, runWithK_eqH (m := Id), keccak256With_kf_fun, hid]
  exact h.symm

/-- **At `Φ = pure ∘ keccakF1600`, the verifier is `pi1KeccakVerifierWith`.** -/
theorem pi1VerifierFsWith_kf (F : KeccakState → m KeccakState) :
    pi1VerifierFsWith (fun s ↦ pure (keccakF1600 s)) F = RecStatement.pi1KeccakVerifierWith F := by
  funext D roots input proof
  unfold pi1VerifierFsWith RecStatement.pi1KeccakVerifierWith
  rw [contractIvKWith_kf, pure_bind, runWithK_kf, pure_bind]
  rfl

omit [LawfulMonad m] in
/-- **At `Φ = F`, the verifier is the deployed Keccak verifier at `keccakRec3`** (`KDeployment.verifierWith`, the
verifier of `UniCompletenessKeccakRec3`), as programs, in every monad. -/
theorem verifierFs_eq (F : KeccakState → m KeccakState) (D : UniKeccak.KDeployment) (roots : SetupRoots)
    (input : Vector UInt8 32) (p : UniKeccak.KeccakProof) :
    pi1VerifierFsWith F F D roots input p = D.verifierWith F UniKeccak.keccakRec3 roots input p := by
  unfold pi1VerifierFsWith UniKeccak.KDeployment.verifierWith UniKeccak.verifyWithK UniKeccak.KDeployment.ivWith
  rfl

/-- **At the real Keccak-f[1600], `pi1KeccakVerifierWith` with its openings over Keccak-f[1600] too is the deployed
Keccak verifier at `keccakRec3`** (`UniKeccakSound.uniKnowledgeSoundnessKeccakRec3_closed`'s verifier). -/
theorem pi1KeccakVerifierWith_kf_eq (D : UniKeccak.KDeployment) (roots : SetupRoots) (input : Vector UInt8 32)
    (p : UniKeccak.KeccakProof) :
    RecStatement.pi1KeccakVerifierWith (m := m) (fun s ↦ pure (keccakF1600 s)) D roots input p =
      D.verifierWith (fun s ↦ pure (keccakF1600 s)) UniKeccak.keccakRec3 roots input p := by
  rw [← pi1VerifierFsWith_kf]
  exact verifierFs_eq _ D roots input p

end Lawful

/-! ## The experiment with its Fiat–Shamir over `Φ` -/

/-- **π1-rec3's completeness experiment with Keccak-f[1600] replaced by `Φ`**: the recursive setup, the prover with its
Fiat–Shamir `keccak256With Φ` (its trees and openings over `π`), the verifier with its Fiat–Shamir over `Φ` (its
openings over `π`). -/
noncomputable def pi1FsCompletenessExperiment (D : RecDeployment)
    (Φ : KeccakState → OracleComp RandomPermutationOracles KeccakState) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← pi1ProverFs (keccak256With Φ) D input rows q with
    | none => return false
    | some p1 => pi1VerifierFsWith Φ queryPermutation D.pi1 trees.roots.pi1 input p1

/-- **π1-rec3's completeness with Keccak-f[1600] replaced by `Φ`**, error `δ`, on honest statements. -/
def Pi1CompletenessFs (D : RecDeployment) (Φ : KeccakState → OracleComp RandomPermutationOracles KeccakState)
    (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let v ← pi1FsCompletenessExperiment D Φ input rows q}[v = false] ≤ δ

/-- **The Keccak reading**: the experiment at `Φ = pure ∘ keccakF1600` is `Pi1CompletenessKeccak`'s at the recursion's
π1 prover. -/
theorem pi1FsCompletenessExperiment_kf (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) :
    pi1FsCompletenessExperiment D (fun s ↦ pure (keccakF1600 s)) input rows q =
      RecStatement.pi1KeccakCompletenessExperiment D (pi1Rec3ProverK D) input rows q := by
  unfold pi1FsCompletenessExperiment RecStatement.pi1KeccakCompletenessExperiment pi1Rec3ProverK
  rw [keccak256With_kf_fun, pi1VerifierFsWith_kf]
  rfl

/-- **`Pi1CompletenessKeccak` at the recursion's π1 prover is the completeness of π1-rec3 with its Fiat–Shamir over
the real Keccak-f[1600]** on both sides, its openings over `π`. -/
theorem pi1CompletenessKeccak_iff (D : RecDeployment) (δ : ℝ≥0∞) :
    RecStatement.Pi1CompletenessKeccak D (pi1Rec3ProverK D) δ ↔
      Pi1CompletenessFs D (fun s ↦ pure (keccakF1600 s)) δ := by
  unfold RecStatement.Pi1CompletenessKeccak Pi1CompletenessFs
  simp only [pi1FsCompletenessExperiment_kf]

/-! ## The random-permutation reading -/

/-- **A game rejecting at most as often as another, permutation by permutation.** -/
theorem eager_le {α β : Type} (X : OracleComp RandomPermutationOracles α) (Y : OracleComp RandomPermutationOracles β)
    (p : α → Prop) (q : β → Prop)
    (h : ∀ π : Equiv.Perm St, Pr{let a ← simulateQ (permImpl π) X}[p a] ≤ Pr{let b ← simulateQ (permImpl π) Y}[q b]) :
    Pr{let a ← runWithRandomPermutation X}[p a] ≤ Pr{let b ← runWithRandomPermutation Y}[q b] := by
  rw [prEvent_runWithRandomPermutation, prEvent_runWithRandomPermutation]
  exact mul_le_mul' le_rfl (Finset.sum_le_sum fun π _ ↦ h π)

/-- **The random-permutation reading of `Pi1CompletenessKeccak`, proved** at the real deployment: with
Keccak-f[1600] read as the random permutation (one `π` for π1's Fiat–Shamir, its trees and its openings), the
recursion's π1 prover is `uniProverRec3RP flockProveH D.pi1` (`pi1ProverFs_rpm`) and π1-rec3's completeness holds with
`deltaK < 2^-169` (`uniCompletenessKeccakRec3_closed`): π2's setup tree, built and unused, drops out permutation by
permutation, and the verifier is the deployed one (`verifierFs_eq`). The Keccak reading (`pi1CompletenessKeccak_iff`)
is not proved: it is the heuristic premise. -/
theorem pi1CompletenessFs_rpm {D : RecDeployment} (hD : D.Real) :
    Pi1CompletenessFs D queryPermutation Prob.deltaK := by
  intro input rows q hfit hrel
  refine le_trans ?_ (uniCompletenessKeccakRec3_closed D.pi1 (real_shape hD) (real_programIv hD) input rows q hfit
    (real_honest hD hrel))
  unfold pi1FsCompletenessExperiment UniKeccak.keccakCompletenessExperiment
  rw [pi1ProverFs_rpm]
  refine eager_le _ _ _ _ fun π ↦ ?_
  unfold RecDeployment.setupTreesWith
  simp only [bind_assoc, pure_bind, simulateQ_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun t1 ↦ ?_
  refine prEvent_bind_le_of_forall_le _ _ _ fun t2 ↦ ?_
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun o ↦ ?_
  cases o with
  | none => exact le_rfl
  | some p1 =>
    exact le_of_eq (congrArg (fun X ↦ Pr{let v ← simulateQ (permImpl π) X}[v = false])
      (verifierFs_eq queryPermutation D.pi1 (D.pi1.setupRoots t1) input p1))

end RecCompose.Pi1K

/-- info: 'RecCompose.Pi1K.pi1VerifierFsWith_kf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1VerifierFsWith_kf

/-- info: 'RecCompose.Pi1K.pi1CompletenessKeccak_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1CompletenessKeccak_iff

/-- info: 'RecCompose.Pi1K.verifierFs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.verifierFs_eq

/-- info: 'RecCompose.Pi1K.pi1CompletenessFs_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1CompletenessFs_rpm
