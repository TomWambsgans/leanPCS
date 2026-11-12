-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import RecCompose.Tables

/-!
# The real deployment's inputs that follow from `RecDeployment.Real`

* **`pi2SetupColumns_of_real`**: `Pi2SetupColumns D C`. `RecDeployment.Real` says how the deployment builds its
  setup columns (`RecDeployment.SetupFromCompiler`: at every π1 setup commitment, `σ` and `κ` are the Lean compiler's
  on π1-rec4's recorded graph at that commitment, `pi1GraphAt roots`, at the emitted graph's roots, π1's contract IV
  and the hashed claims `Data.hashed`), so at every setup they are the compiled circuit's that `Pi2Circuits` holds
  (`compile` is a function: `C.compile_ok` names the same circuit).
-/

namespace RecCompose

open RecStatement LeanVM.Parameters

/-- **The deployment's setup columns are the compiled circuit's**, from `RecDeployment.Real`. -/
theorem pi2SetupColumns_of_real {D : RecDeployment} (hD : D.Real) (C : Pi2Circuits D)
    (hroots : C.rootsAt = RecGraphKeccak.Emitted.rootsAt) : Pi2SetupColumns D C := by
  intro roots i _
  have hc := C.compile_okAt roots.pi1
  rw [hroots] at hc
  obtain ⟨hs, hk⟩ := hD.2.2.2.2.2.2.1 roots.pi1 _ hc
  have hs' : (D.circuitAt roots.pi1).sigma = (C.compiled roots.pi1).circuit.sigmaAt := hs
  have hk' : (D.circuitAt roots.pi1).kappa = (C.compiled roots.pi1).circuit.kappaAt := hk
  refine ⟨?_, ?_⟩
  · rw [hk']
    rfl
  · rw [hs']
    rfl

end RecCompose

/-- info: 'RecCompose.pi2SetupColumns_of_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2SetupColumns_of_real
