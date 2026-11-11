-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π2's honest prover is `crates/leanvm/rec/src/pi2/prover.rs`'s
-- (`RecCompose.Pi2Prover`); the statements are `formal/RecStatement`'s.
import RecCompose.Pi2Accepts
import RecCompose.Pi2Witness

/-!
# π2's honest proof is accepted, from π1's graph verifier accepting (π2v4, π1-rec4)

`pi2_accepts` with its three hypotheses about π1's proof discharged (`Pi2Witness.lean`): the honest witness (`hgood`,
`Pi2W.pi2Good_of_checks`), π1's three claims (`hp3`) and their openings (`hpi1`, `Pi2W.pi1Openings_of_verifierH`), all
from π1-rec4's graph verifier accepting `p1` at the same pure `(Hk, F)` and setup (`Pi2H.pi1GraphVerifierWithH`, the first
verdict of `RecCompleteness2`'s experiment), and the circuit's shape (`logN`, `logW`) from `Pi2Facts`.

* **`pi2_accepts_of_verifier`**: at a `Real` deployment whose compiled circuits pass the view check, whose public limbs
  are `pubOfC` and whose graph is the emitted one;
* **`pi2_accepts_real`**: at `realDeployment prog hprog`, its circuits and facts, from `GraphsAgreeK4` and the evaluated
  checks `DigestChecked`, `SetupRootChecked`, `IvChecked`. What remains: π1's graph verifier accepting `p1`, π2's prover
  returning a proof, and its challenges off `BadCopy`, `BadT`, `BadRho`.
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2E

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Pi2S Pi2K

/-- **π2's honest proof is accepted, given π1's graph verifier accepts π1's proof**: `pi2_accepts` with `hgood`, `hp3`,
`hpi1` from the verifier's verdict, at a `Real` deployment whose compiled circuits pass the view check, whose public
limbs are `pubOfC` and whose π1 graph is the emitted one. -/
theorem pi2_accepts_of_verifier (D : RecDeployment) (hD : D.Real) (C : Pi2Circuits D) (hchk : Pi2ViewChecked C)
    (Fa : Pi2Facts D C) (hpub : ∀ roots, Fa.pubOf roots = pubOfC (C.compiled roots.pi1).circuit)
    (hgr : ∀ roots, pi1GraphAt roots = emittedAt roots)
    (F : KeccakState → Id KeccakState) (Hk : List UInt8 → Digest)
    (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof)
    (ha1 : Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Hk) F D
      (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots.pi1 input p1) = true)
    (proof : RecProof)
    (hp : Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Hk) F D C.G Fa.pubOf fuel input p1) = some proof)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt)
    (hbad : let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream
      let vw := pi2Choice D C.G Fa.pubOf trees.roots input p1.stream claims
      let out := outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2
      ¬ BadCopy (C.G trees.roots) vw.2 (Fa.pubOf trees.roots (publicScalarsOf input.toList vw.1))
        out.inputs.α out.inputs.β out.inputs.γ)
    (ht : let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream
      let vw := pi2Choice D C.G Fa.pubOf trees.roots input p1.stream claims
      let out := outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2
      ¬ BadT (C.G trees.roots) vw.2 out.inputs.α out.inputs.β out.inputs.γ out.inputs.t)
    (hρ : let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream
      let vw := pi2Choice D C.G Fa.pubOf trees.roots input p1.stream claims
      let out := outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2
      ¬ BadRho (C.G trees.roots) out.inputs.t out.inputs.ρ) :
    (Id.run (Pi2H.contractWithH (m := Id) (Pure.pure ∘ Hk) F D
      (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)).roots input proof)).1 = true := by
  obtain ⟨h3, h1, h2, hS⟩ := Pi2W.pi1Openings_of_verifierH hD.2.2.1 Hk F _ input p1 ha1
  exact pi2_accepts D hD C Fa F Hk fuel input p1
    (pi2Choice_good ⟨_, Pi2W.pi2Good_of_checks hD.1 C hchk Fa hpub hgr _ input p1.stream
      (Pi2W.graphChecks_of_verifier ha1)⟩)
    h3 (Fa.logN _) (by rw [Fa.logW]; rfl) proof hp hroots hbad ht hρ ⟨h1, h2, hS⟩

variable (prog : KeccakVm.Program) (hprog : RecGraphKeccak.Pi1.keccak128.logBytecode = prog.logSize)

/-- **π2's honest proof is accepted at the real deployment**, at a pure permutation `F` (Keccak-256 `Hk`): from
`GraphsAgreeK4` and the evaluated checks (`DigestChecked`, `SetupRootChecked`, `IvChecked`), if π1-rec4's graph
verifier accepts π1's proof `p1` at the setup (`RecCompleteness2`'s first verdict), π2's prover returns a proof and its
challenges are off `BadCopy`, `BadT` (`t`) and `BadRho` (`ρ`), the contract accepts it. -/
theorem pi2_accepts_real (hg : RecGraphKeccak.GraphsAgreeK4) (hd : DigestChecked) (hs : SetupRootChecked)
    (hiv : IvChecked) (F : KeccakState → Id KeccakState) (Hk : List UInt8 → Digest)
    (fuel : ℕ) (input : Vector UInt8 32) (p1 : UniKeccak.KeccakProof)
    (ha1 : Id.run (Pi2H.pi1GraphVerifierWithH (m := Id) (Pure.pure ∘ Hk) F (realDeployment prog hprog)
      (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F (realDeployment prog hprog))).roots.pi1 input p1) =
        true)
    (proof : RecProof)
    (hp : Id.run (pi2ProverWith (m := Id) (Pure.pure ∘ Hk) F (realDeployment prog hprog)
      (pi2Circuits_real prog hprog hg hiv).G (pi2Facts_real prog hprog hg hd hs hiv).pubOf fuel input p1) = some proof)
    (hbad : let D := realDeployment prog hprog
      let C := pi2Circuits_real prog hprog hg hiv
      let Fa := pi2Facts_real prog hprog hg hd hs hiv
      let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream
      let vw := pi2Choice D C.G Fa.pubOf trees.roots input p1.stream claims
      let out := outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2
      ¬ BadCopy (C.G trees.roots) vw.2 (Fa.pubOf trees.roots (publicScalarsOf input.toList vw.1))
        out.inputs.α out.inputs.β out.inputs.γ)
    (ht : let D := realDeployment prog hprog
      let C := pi2Circuits_real prog hprog hg hiv
      let Fa := pi2Facts_real prog hprog hg hd hs hiv
      let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream
      let vw := pi2Choice D C.G Fa.pubOf trees.roots input p1.stream claims
      let out := outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2
      ¬ BadT (C.G trees.roots) vw.2 out.inputs.α out.inputs.β out.inputs.γ out.inputs.t)
    (hρ : let D := realDeployment prog hprog
      let C := pi2Circuits_real prog hprog hg hiv
      let Fa := pi2Facts_real prog hprog hg hd hs hiv
      let trees := Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F D)
      let claims := pi1ClaimsOf D trees.roots.pi1 input p1.stream
      let vw := pi2Choice D C.G Fa.pubOf trees.roots input p1.stream claims
      let out := outOf D Hk trees.roots (C.G trees.roots) (pi2Z Hk) input vw.1 vw.2
      ¬ BadRho (C.G trees.roots) out.inputs.t out.inputs.ρ) :
    (Id.run (Pi2H.contractWithH (m := Id) (Pure.pure ∘ Hk) F (realDeployment prog hprog)
      (Id.run (Pi2H.setupTreesWithH (m := Id) (Pure.pure ∘ Hk) F (realDeployment prog hprog))).roots input
        proof)).1 = true :=
  pi2_accepts_of_verifier _ (realDeployment_real prog hprog hg hd hs) _ (pi2ViewChecked_real prog hprog hg hiv) _
    (fun _ ↦ rfl) (pi1GraphAt_eq hg) F Hk fuel input p1 ha1 proof hp rfl hbad ht hρ

end RecCompose.Pi2E

/-- info: 'RecCompose.Pi2E.pi2_accepts_of_verifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.pi2_accepts_of_verifier

/-- info: 'RecCompose.Pi2E.pi2_accepts_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2E.pi2_accepts_real
