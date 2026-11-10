-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniKeccakComplete.K.Reference
import RecCompose.Bridge

/-!
# π1's claims' shape at the real deployment

On the EIP draft's PCS claims there are no layout words (this file held their check against `Data.pi1Calls`): a claim
is its root, its out-of-domain answer, its point and its value, and the contract opens it at its point's length. What
the composition needs of π1's claims as the circuit names them is their shape, **`Pi1CallsShape`**
(`OpeningsAgree.lean`): three claims of `stackVarsK + 3` words at the reference shape (`30`, `29`, `26`: `C1`'s `27`,
`C2`'s `26`, the setup's `23` variables, `UniKeccakComplete.reference_stackVars_*`), the setup's starting with its root
and answer as constants. **`pi1CallsShape_of_real`**: it holds at the real deployment (`Data.pi1Calls`, by the kernel).
-/

namespace RecCompose

/-- **π1's claims' shape at the real deployment** (`Data.pi1Calls`). -/
theorem pi1CallsShape_of_real {D : RecStatement.RecDeployment} (hD : D.Real) : Pi1CallsShape D :=
  pi1CallsShape_data D hD.2.1

end RecCompose

/-- info: 'RecCompose.pi1CallsShape_of_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi1CallsShape_of_real
