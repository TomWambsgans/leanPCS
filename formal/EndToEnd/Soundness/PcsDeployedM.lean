-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- `formal/SoundPcs/SoundPcs/Final.lean`'s `knowledgeSoundness_deployed_pcs_of` of this repository, under the name
-- the end theorem uses: stated for any committed wiring table `q₀` and any `ClaimsMatch` of it (the honest table
-- `wiringCol`, chosen by `exists_table`, and its `claimsMatch` is `knowledgeSoundness_deployed_pcs`).
import SoundPcs

/-!
# The deployed composition, for any committed wiring table

`SoundPcs.knowledgeSoundness_deployed_pcs` is stated for the honest wiring table `wiringCol hc σ` (a table chosen to
carry `σ`) and its `claimsMatch`; it is `SoundPcs.knowledgeSoundness_deployed_pcs_of`, generic in the table and the
match. **`knowledgeSoundness_deployed_pcsM`** is that theorem for any table `q₀` and any `M : ClaimsMatch W q₀`: the
end theorem commits the Statement's own wiring table.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace SoundPcs

open Compose ComposePcs Compose.Reduce QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol
open LeanVM.Semantics LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open WhirBridge.Pcs PcsBridge

attribute [local irreducible] stage DA4 e1 e2 e3 e4 e5 dExp withSetup4 setupPcs loggedKC

variable (hc : IsCantor statementConsts.beta) (σ : Equiv.Perm (Fin (22 + 2) → Bool))
  (W : Wire (rustInstance statementConsts hc σ).params (rustInstance statementConsts hc σ).bounds)
  (q₀ : Column 24) (M : ClaimsMatch W q₀)

/-- **Knowledge soundness of the deployed verifier of the EIP's PCS claims**, for any committed wiring table and
any match of the claims (`SoundPcs.knowledgeSoundness_deployed_pcs`'s proof). -/
theorem knowledgeSoundness_deployed_pcsM
    (A₀ : QuotientRpm.Bytes32 × E → OracleComp KeccakCalls (RootProof4 E × Rest)) (Q : ℕ)
    (hQ : ∀ c, IsTotalQueryBound (A₀ c) Q) :
    Pr{let z ← (simulateQ randomOracle
        (dExp W pcsOpen (withSetup4 (setupPcs q₀) A₀))).run' ∅}[
        BreaksD W M.cW z] ≤ deployedBound Q :=
  knowledgeSoundness_deployed_pcs_of hc σ W q₀ M A₀ Q hQ

end SoundPcs

/-- info: 'SoundPcs.knowledgeSoundness_deployed_pcsM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SoundPcs.knowledgeSoundness_deployed_pcsM
