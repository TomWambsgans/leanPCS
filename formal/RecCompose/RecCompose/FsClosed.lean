-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md; conventions: see AGENTS.md. π2's Fiat–Shamir layer
-- proved (`pi2FsLayer_real`), as `formal/UniSound/UniSound/FsFinal128.lean`'s `fsLayer128_holds` for π1; the Keccak
-- π1's shape numbers are `formal/UniKeccakSound/UniKeccakSound/Fs/LayerK.lean`'s.
import RecCompose.FsGame
import RecCompose.FsCouple
import RecCompose.FsCost
import UniKeccakSound.Fs.LayerK
import RecCompose.FsBind

/-!
# π2's Fiat–Shamir layer, proved

**`pi2FsLayer_real`**: `Pi2FsLayer D` at the real deployment (`RecDeployment.Real D`: π2v4 over π1-rec4, π1's three
claims declared in the frame and hashed in π2's circuit), with no premise (`Q`'s out-of-domain binding is
`FsBind.qOodBinding`: the contract reads `W`'s and `Q`'s out-of-domain points off Keccak-256 over the permutation,
`RecStatement.pcsOpenKO`): `pi2FsLayer_of` (FsGame.lean) with its bridges proved, the coupling `pi2GameLeV`
(FsCouple.lean, from the setup's bridge `pi2SetupBridge`, the verifier's `pi2VerifierBridge` on the walk `pi2Walk`,
`pi2WalkReject`, and the extractor's reading `pi2ExtractBridge`) and the composed verifier's facts (FsCost.lean), π1's
shape the Keccak reference `keccak128` (`UniKeccakSound.uniShapesK_ref`: `C1`, `C2`, the setup at `2^27`, `2^26`,
`2^23` words; `UniKeccakSound.layoutVarsSmallK_ref`); the contract's seven PCS openings charged once and `Q`'s binding
(`FsBind.lean`) in `pi2Bound`'s openings term (`pi2OpenErr = 269 · 2^-137 + 2^-156`, `δc 28 ≤ 2^-160` within the
`2^-156`).

The end theorems take it with π2's tables' layer (`Tables.pi2Tables`) and the circuit's facts: `pi2Layers_of`
(`Layers.lean`) gives `Pi2Layers D pi2Bound`, which `End.lean`'s theorems take.
-/

namespace RecCompose

open RecStatement LeanVM.Parameters LeanVM.Protocol
open scoped ENNReal

/-- **π2's Fiat–Shamir layer at the real deployment** (`Pi2FsLayer D`): for every family over the setup's roots of
round-by-round sound protocols on π2's rounds, their errors times the lists of the roots before them at most `e`,
whose first state is a property `P` of `W`'s candidate and whose last state follows from π2's check with the four
claims true, the contract accepts while no candidate of `W`'s committed word has `P` with probability at most
`pi2BoundE e Q`. -/
theorem pi2FsLayer_real (D : RecDeployment) (hD : D.Real) : Pi2FsLayer D := by
  have hs : UniKeccakSound.UniShapesK D.pi1 := UniKeccakSound.uniShapesK_ref D.pi1 hD.2.2.1
  have hv : (UniStatement.setupLayout D.pi1.shape).vars < 256 :=
    (UniKeccakSound.layoutVarsSmallK_ref D.pi1 hD.2.2.1).setup
  exact pi2FsLayer_of D hD hs
    (fun P A => pi2GameLeV D hD hs hv (pi2VerifierBridge D hD pi2Walk pi2WalkReject) P A)
    (duplexVm_p2Ver D) (cost_p2Ver D hD) (isTotalQueryBound_p2IvAdv D) (expU_p2IvAdv D hs)
    (extractorK_ivLog D hD) (hlab_p2 D hs) p2BreaksRel_congr (by rw [nQ_p2]; norm_num)

end RecCompose

/-- info: 'RecCompose.pi2FsLayer_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pi2FsLayer_real
