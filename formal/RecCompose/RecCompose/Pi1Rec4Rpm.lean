-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The statement read is `formal/RecStatement`'s
-- (`Pi1CompletenessKeccak`, `pi1KeccakVerifierWith`); its random-permutation reading is `formal/UniKeccak`'s
-- `UniCompletenessKeccakRec4` (`Security.lean`), proved by `formal/UniKeccakComplete`'s
-- `uniCompletenessKeccakRec4_closed`. Ported from this library's π1-rec3 version (`Pi1KeccakRpm.lean`, retired). The
-- eager form of the random-permutation model is `formal/EndToEnd/ZK/ProverBridgeEager.lean`'s; Keccak-256 through a
-- monad morphism `ProverBridgeParam.lean`'s (`keccak256With_hom`, `absorbWith_hom`); VCVio's
-- `prEvent_bind_mono_of_forall_le`.
import RecCompose.Pi1Rec4Transfer
import ZK.ProverBridgeParam
import ZK.ProverBridgeEager

/-!
# `Pi1CompletenessKeccak` at the recursion's π1-rec4 prover: what it says, and its random-permutation reading

`RecStatement.Pi1CompletenessKeccak D P1 δ1` is a **premise** of the end-to-end completeness theorems: π1-rec4's honest
proof, its Fiat–Shamir over the real Keccak-f[1600], its openings over the random permutation `π`, is rejected by the
Keccak π1-rec4's verifier at Keccak-f[1600] (`pi1KeccakVerifierWith`, openings over `π`) with probability at most `δ1`.
At the recursion's prover `pi1Rec4ProverK` (`Pi1Rec4Prover.lean`) prover and verifier hash the Fiat–Shamir with the
same Keccak-f[1600]. This file makes the premise's content explicit:

* **`pi1VerifierFsWith4 Φ F`**: `pi1KeccakVerifierWith` with its Fiat–Shamir over a permutation `Φ` (the Keccak
  contract's IV `contractIvKWith Φ … keccakRec4`, the run `runWithK4 Φ … keccakRec4 .point`), its openings over `F`; at
  `Φ = pure ∘ keccakF1600` it is `pi1KeccakVerifierWith` (**`pi1VerifierFsWith4_kf`**, any lawful monad); at `Φ = F`
  it is the deployed π1-rec4 verifier `KDeployment.verifierWith4 F` (**`verifierFs4_eq`**, as programs).
* **`pi1FsCompletenessExperiment4 D Φ`**, **`Pi1CompletenessFs4 D Φ δ`**: the completeness experiment with
  Keccak-f[1600] replaced by `Φ` on both sides (the prover's Fiat–Shamir `keccak256With Φ` and `rateWith Φ`, the
  verifier's `Φ`), the trees and openings over `π`.
* **The Keccak reading** (**`pi1CompletenessKeccak_iff4`**): `Pi1CompletenessKeccak D (pi1Rec4ProverK D) δ ↔
  Pi1CompletenessFs4 D (pure ∘ keccakF1600) δ`.
* **The random-permutation reading, proved** (**`pi1CompletenessFs4_rpm`**): at `Φ = π` (Keccak-f[1600] read as the
  random permutation, one permutation for the Fiat–Shamir and the openings) the experiment is π1-rec4's own
  (`keccakCompletenessExperiment4` of `uniProverRec4RP`, `pi1ProverFs4_rpm`), but for π2's setup tree, built and unused;
  so `Pi1CompletenessFs4 D π deltaK` at the real deployment, from `uniCompletenessKeccakRec4_closed`,
  `deltaK < 2^-169`.

**The gap, stated plainly.** Nothing here proves the Keccak reading. `Pi1CompletenessKeccak D (pi1Rec4ProverK D) δ1`
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
open UniKeccakComplete UniKeccakComplete.Rec4
open RecStatement (RecDeployment Pi1Prover)
open PcsQuotient.EndToEnd.Eager
open scoped ENNReal

/-! ## The verifier with its Fiat–Shamir over `Φ` -/

section With

variable {m : Type → Type} [Monad m] (Φ F : KeccakState → m KeccakState)

/-- **The Keccak π1-rec4's verifier with its Fiat–Shamir over `Φ`** and its three openings over `F`:
`pi1KeccakVerifierWith` with `contractIvKWith Φ` and `runWithK4 Φ` for `pi1Iv` and `runK4`. -/
def pi1VerifierFsWith4 (D : UniKeccak.KDeployment) (roots : UniKeccak.SetupRootsK) (input : Vector UInt8 32)
    (proof : UniKeccak.KeccakProof) : m Bool := do
  let iv ← UniKeccak.contractIvKWith Φ D.shape UniKeccak.keccakRec4 D.programIv roots
  let o ← UniKeccak.runWithK4 Φ D.shape iv input.toList proof.stream UniKeccak.keccakRec4 .point
  if !o.accepts then return false
  match o.result with
  | .error _ => return false
  | .ok r =>
    let mut ok := r.openings.map (·.1) == UniStatement.commitments
    for (c, opening) in r.openings do
      match opening with
      | .point pt value none =>
        ok := ok && (← UniKeccak.pcsOpenK F (UniKeccak.stackVarsK D.shape c) (UniKeccak.commitOfK roots r c).1
          (UniKeccak.commitOfK roots r c).2 pt value (proof.openingOf c))
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

/-- **Keccak-256's rate over the real Keccak-f[1600], in any lawful monad, is the pure `rateKF`.** -/
theorem rateWith_kf (x : List UInt8) :
    rateWith (m := m) (fun s ↦ pure (keccakF1600 s)) x = pure (rateKF x) := by
  have h := PcsQuotient.EndToEnd.Param.absorbWith_hom (idMHom (m := m)) (fun s ↦ (pure (keccakF1600 s) : Id _))
    (x.length / rate) (Vector.replicate 25 0) x
  simp only [idMHom] at h
  unfold rateWith keccak256StateWith
  rw [show absorbWith (m := m) (fun s ↦ pure (keccakF1600 s)) (x.length / rate) (Vector.replicate 25 0) x =
      pure (Id.run (absorbWith (m := Id) (fun s ↦ pure (keccakF1600 s)) (x.length / rate) (Vector.replicate 25 0) x))
      from h.symm, map_pure]
  rfl

theorem rateWith_kf_fun :
    rateWith (m := m) (fun s ↦ pure (keccakF1600 s)) = wKF := funext rateWith_kf

/-- The Keccak contract's IV over the real Keccak-f[1600], in any lawful monad: the pure `contractIvK`. -/
theorem contractIvKWith_kf (s : UniStatement.Shape) (v : UniKeccak.KeccakVariant) (programIv : List UInt8)
    (roots : UniKeccak.SetupRootsK) :
    UniKeccak.contractIvKWith (m := m) (fun x ↦ pure (keccakF1600 x)) s v programIv roots =
      pure (UniKeccak.contractIvK s v programIv roots) := by
  unfold UniKeccak.contractIvKWith
  rw [keccak256With_kf, pure_bind]
  rfl

/-- π1-rec4's run over the real Keccak-f[1600], in any lawful monad: the pure `runK4`. -/
theorem runWithK4_kf (shape : UniStatement.Shape) (iv publicInput : List UInt8) (stream : Array UInt8)
    (v : UniKeccak.KeccakVariant) (mode : ClaimsMode) :
    UniKeccak.runWithK4 (m := m) (fun x ↦ pure (keccakF1600 x)) shape iv publicInput stream v mode =
      pure (UniKeccak.runK4 shape iv publicInput stream v mode) := by
  have h := app_runWithKH4 (idMorph (m := m)) (fun x ↦ (pure (KeccakHash.keccak256 x) : Id Digest))
    (fun x ↦ (pure (rateKF x) : Id RateB)) shape iv publicInput stream v mode
  simp only [idMorph] at h
  have hid : keccak256With (m := Id) (fun x ↦ pure (keccakF1600 x)) =
      fun x ↦ (pure (KeccakHash.keccak256 x) : Id Digest) := rfl
  have hidw : rateWith (m := Id) (fun x ↦ pure (keccakF1600 x)) = fun x ↦ (pure (rateKF x) : Id RateB) := rfl
  unfold UniKeccak.runK4
  rw [runWithK4_eqH4, runWithK4_eqH4 (m := Id), keccak256With_kf_fun, rateWith_kf_fun, hid, hidw]
  exact h.symm

/-- **At `Φ = pure ∘ keccakF1600`, the verifier is `pi1KeccakVerifierWith`.** -/
theorem pi1VerifierFsWith4_kf (F : KeccakState → m KeccakState) :
    pi1VerifierFsWith4 (fun s ↦ pure (keccakF1600 s)) F = RecStatement.pi1KeccakVerifierWith F := by
  funext D roots input proof
  unfold pi1VerifierFsWith4 RecStatement.pi1KeccakVerifierWith
  rw [contractIvKWith_kf, pure_bind, runWithK4_kf, pure_bind]
  rfl

omit [LawfulMonad m] in
/-- **At `Φ = F`, the verifier is the deployed π1-rec4 verifier** (`KDeployment.verifierWith4`, the verifier of
`UniCompletenessKeccakRec4`), as programs, in every monad. -/
theorem verifierFs4_eq (F : KeccakState → m KeccakState) (D : UniKeccak.KDeployment) (roots : UniKeccak.SetupRootsK)
    (input : Vector UInt8 32) (p : UniKeccak.KeccakProof) :
    pi1VerifierFsWith4 F F D roots input p = D.verifierWith4 F roots input p := by
  unfold pi1VerifierFsWith4 UniKeccak.KDeployment.verifierWith4 UniKeccak.verifyWithK4 UniKeccak.KDeployment.ivWith
  rfl

end Lawful

/-! ## The experiment with its Fiat–Shamir over `Φ` -/

/-- **π1-rec4's completeness experiment with Keccak-f[1600] replaced by `Φ`**: the recursive setup, the prover with its
Fiat–Shamir `keccak256With Φ`, `rateWith Φ` (its trees and openings over `π`), the verifier with its Fiat–Shamir over
`Φ` (its openings over `π`). -/
noncomputable def pi1FsCompletenessExperiment4 (D : RecDeployment)
    (Φ : KeccakState → OracleComp RandomPermutationOracles KeccakState) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) : ProbComp Bool :=
  runWithRandomPermutation do
    let trees ← D.setupTreesWith queryPermutation
    match ← pi1ProverFs4 (keccak256With Φ) (rateWith Φ) D input rows q with
    | none => return false
    | some p1 => pi1VerifierFsWith4 Φ queryPermutation D.pi1 trees.roots.pi1 input p1

/-- **π1-rec4's completeness with Keccak-f[1600] replaced by `Φ`**, error `δ`, on honest statements. -/
def Pi1CompletenessFs4 (D : RecDeployment) (Φ : KeccakState → OracleComp RandomPermutationOracles KeccakState)
    (δ : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    Pr{let v ← pi1FsCompletenessExperiment4 D Φ input rows q}[v = false] ≤ δ

/-- **The Keccak reading**: the experiment at `Φ = pure ∘ keccakF1600` is `Pi1CompletenessKeccak`'s at the recursion's
π1-rec4 prover. -/
theorem pi1FsCompletenessExperiment4_kf (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.pi1.Stack rows) :
    pi1FsCompletenessExperiment4 D (fun s ↦ pure (keccakF1600 s)) input rows q =
      RecStatement.pi1KeccakCompletenessExperiment D (pi1Rec4ProverK D) input rows q := by
  unfold pi1FsCompletenessExperiment4 RecStatement.pi1KeccakCompletenessExperiment pi1Rec4ProverK
  rw [keccak256With_kf_fun, rateWith_kf_fun, pi1VerifierFsWith4_kf]
  rfl

/-- **`Pi1CompletenessKeccak` at the recursion's π1-rec4 prover is the completeness of π1-rec4 with its Fiat–Shamir
over the real Keccak-f[1600]** on both sides, its openings over `π`. -/
theorem pi1CompletenessKeccak_iff4 (D : RecDeployment) (δ : ℝ≥0∞) :
    RecStatement.Pi1CompletenessKeccak D (pi1Rec4ProverK D) δ ↔
      Pi1CompletenessFs4 D (fun s ↦ pure (keccakF1600 s)) δ := by
  unfold RecStatement.Pi1CompletenessKeccak Pi1CompletenessFs4
  simp only [pi1FsCompletenessExperiment4_kf]

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
recursion's π1 prover is `uniProverRec4RP D.pi1` (`pi1ProverFs4_rpm`) and π1-rec4's completeness holds with
`deltaK < 2^-169` (`uniCompletenessKeccakRec4_closed`): π2's setup tree, built and unused, drops out permutation by
permutation, and the verifier is the deployed one (`verifierFs4_eq`). The Keccak reading (`pi1CompletenessKeccak_iff4`)
is not proved: it is the heuristic premise. -/
theorem pi1CompletenessFs4_rpm {D : RecDeployment} (hD : D.Real) :
    Pi1CompletenessFs4 D queryPermutation Prob.deltaK := by
  intro input rows q hfit hrel
  refine le_trans ?_ (uniCompletenessKeccakRec4_closed D.pi1 (real_shape hD) (real_programIv hD)
    (real_programIv32 hD) input rows q hfit (real_honest hD hrel))
  unfold pi1FsCompletenessExperiment4 UniKeccak.keccakCompletenessExperiment4
  rw [pi1ProverFs4_rpm]
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
      (verifierFs4_eq queryPermutation D.pi1 (D.pi1.setupRoots t1) input p1))

end RecCompose.Pi1K

/-- info: 'RecCompose.Pi1K.pi1VerifierFsWith4_kf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1VerifierFsWith4_kf

/-- info: 'RecCompose.Pi1K.pi1CompletenessKeccak_iff4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1CompletenessKeccak_iff4

/-- info: 'RecCompose.Pi1K.verifierFs4_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.verifierFs4_eq

/-- info: 'RecCompose.Pi1K.pi1CompletenessFs4_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1CompletenessFs4_rpm
