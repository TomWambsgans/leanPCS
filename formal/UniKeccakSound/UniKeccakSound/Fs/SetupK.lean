-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. `UniSound/FsSetup.lean` (after
-- `formal/EndToEnd/Soundness/TreeLog.lean`'s `loggedKC_buildTree` and `Bridge/Setup.lean`'s `commitWith_eq`) for the
-- Keccak verifier's setup, one tree.
import UniKeccakSound.Fs.CoupleK
import Bridge.Setup

/-!
# The Keccak setup bridge: the composed setup, logged, is `setupTreeKWith`

**`uniSetupBridgeK`**: `UniSetupBridgeK D hs` (`CoupleK.lean`) for every Keccak deployment whose setup stack has
fewer than `256` variables (`LayoutVarsSmallK`, kept from the layout words' byte; the PCS claims' `n` is a byte too): the composed setup (`uSetupK`: the tree of `stackSetupS` at the plain
shape of the layout word's variables `wvK D 2`), logged and answered over `π`, is `setupTreeKWith π D` (the WHIR
commitment of `setupStackK` at `(setupLayout D.shape).vars`), its root as bytes and its log the tree's evaluations
(`simulateQ_loggedKC_stackSetupSK`, `UniSound.simulateQ_loggedKC_stackSetupS`'s proof at `2^23 ..= 2^28` words). The
hypothesis is `UniSound`'s (`FsSetup.lean`'s docstring): a layout word carries the variables in one byte.
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound UniKeccak
open OracleSpec OracleComp
open scoped ENNReal

/-- **The Keccak stacks the bridges read have fewer than `256` variables** (a layout word carries them in one byte):
`C1`'s (the extractor decodes at its variables) and the setup's (the setup commits at its variables). -/
structure LayoutVarsSmallK (D : KDeployment) : Prop where
  c1 : (c1LayoutK D.shape).vars < 256
  setup : (setupLayout D.shape).vars < 256

/-- **The logged setup of one plain tree** of `2^23 ..= 2^28` words, answered over `π`, is the WHIR commitment
(`PcsQuotient.commitWith`) of the array, its root as bytes and its log the tree's evaluations. -/
theorem simulateQ_loggedKC_stackSetupSK (v : ℕ) (h1 : 23 ≤ v) (h2 : v ≤ 28) (a : Array K) :
    simulateQ keccakCallsOverQueryPermutation
        (loggedKC (stackSetupS (plainShapeK v h1 h2) (colOf a v))) =
      (fun t : LeanVM.Prover.Tree => (toB t.root, Soundness.treeTr t)) <$>
        PcsQuotient.commitWith Common.queryPermutation v a := by
  unfold stackSetupS wiringSetup
  rw [Soundness.loggedKC_map, Soundness.loggedKC_buildTree,
    Functor.map_map, simulateQ_map, LeanVM.Protocol.Compile.simulateQ_buildTreeM,
    Bridge.Setup.commitWith_eq Common.queryPermutation v (by omega) (by omega) a]
  rfl

/-- **The setup's stack variables are the setup layout's** (`stackVarsK`: `layoutsOfK`'s setup entry does not depend
on the tables). -/
theorem wvK_two (D : KDeployment) (_hv : (setupLayout D.shape).vars < 256) :
    wvK D 2 = (setupLayout D.shape).vars := rfl

/-- **`C1`'s stack variables are `c1LayoutK`'s** (`layoutsOfK`'s `C1` entry does not depend on `C2`'s columns). -/
theorem wvK_zero (D : KDeployment) (_hv : (c1LayoutK D.shape).vars < 256) :
    wvK D 0 = (c1LayoutK D.shape).vars := rfl

/-- **SETUP** (`UniSetupBridgeK`), for a setup stack of fewer than `256` variables. -/
theorem uniSetupBridgeK (D : KDeployment) (hs : UniShapesK D) (hv : (setupLayout D.shape).vars < 256) :
    UniSetupBridgeK D hs := by
  have e := simulateQ_loggedKC_stackSetupSK (wvK D 2) (hs.lo 2 (by decide)) (hs.hi 2 (by decide))
    (setupStackK D.prog D.shape)
  unfold UniSetupBridgeK setupTreeKWith
  rw [← wvK_two D hv]
  exact e

end UniKeccakSound

/-- info: 'UniKeccakSound.uniSetupBridgeK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakSound.uniSetupBridgeK
