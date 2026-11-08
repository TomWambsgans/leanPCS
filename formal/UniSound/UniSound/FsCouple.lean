-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows
-- `formal/EndToEnd/Soundness/Final.lean` of this repository (`prEvent_le_of_continuations`,
-- `soundnessExperiment_eq`, `rpmGame_eq`, `step_le`) and `Soundness/Hypotheses.lean` (the bridge
-- facts as propositions about definitions).
import UniSound.FsGame
import Soundness.Final

/-!
# The univariate experiment and the composed game, coupled

**`uniGameLeV_of`**: the coupling `UniGameLeV` from three bridge facts, each a statement about
definitions or one verifier run, as `formal/EndToEnd/Soundness/Hypotheses.lean`'s for the
membership proof:

* **`UniSetupBridge`** (the setup): the composed setup over `π`, logged (`uSetup`: the three trees
  of `stackSetupS` at the plain shapes), is the Statement's `setupTreesWith` over `π`, its roots as
  bytes (`rootsB`) and its log the trees' evaluations (`setupTr`);
* **`UniVerifierBridge`** (the verifier): from any state of the lazily sampled permutation, the
  Statement's `verifyWith` (the run on the stream, its early stops, the five `PCS_OPEN` calls)
  accepts at most as often as the composed verifier (the chain over the univariate encoding and the
  five openings, `verU`) satisfies `uniCheck` and all five openings accept;
* **`UniExtractBridge`** (the extractor's reading): a candidate of `C1`'s root that the composed
  extractor reads off the setup's log and the adversary's permutation transcript, and that satisfies
  leanVM 42422001's relation, makes the Statement's `uniExtractor` find a stack satisfying it.

The proof: both experiments are the setup's trees and the adversary given their roots, its queries
logged (`prefixU`, `uniSoundnessExperiment_eq`, `rpmGameS_eq` by `UniSetupBridge`), then their
verifiers on the same state of the permutation (`Soundness.prEvent_le_of_continuations`); there
both first compute the contract's IV, the same Keccak-256 call (`ivWith_eq`), then (`step_le`) the
Statement's event is impossible if its extractor finds a stack, and otherwise follows from the
verifier's acceptance, which `UniVerifierBridge` bounds by the composed event's.
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.layoutWords UniStatement.setupStack

/-! ## The bridge facts -/

/-- The setup's roots as bytes. -/
def rootsB (t : SetupTrees) : Bytes32 × Bytes32 × Bytes32 :=
  (toB t.bytecode.root, toB t.a0.root, toB t.b0.root)

/-- The setup's Keccak-256 evaluations as a transcript. -/
def setupTr (t : SetupTrees) : Transcript := t.evaluations.map fun e => (e.1, toB e.2)

/-! ## The experiments, a common prefix then the verifiers -/

theorem rootsOfS_rootsB (t : SetupTrees) : rootsOfS (rootsB t) = t.roots := by
  simp only [rootsOfS, rootsB, SetupTrees.roots, Soundness.ofB_toB_root]

/-- The proof the composed game's verifier reads, from the setup's trees and the adversary's
output. -/
def piOf (a : SetupTrees × ((Vector UInt8 32 × UniProof) × Common.OracleQueryLog)) : UPf :=
  ⟨a.2.1.1, a.2.1.2, Vector.replicate 32 0, a.1.roots⟩

theorem run_logged_uAdv (A : UniAdversary) (s : Bytes32 × Bytes32 × Bytes32) :
    (simulateQ Common.loggedOracles (uAdv A s)).run [] =
      (fun p => ((⟨p.1.1, p.1.2, Vector.replicate 32 0, rootsOfS s⟩ : UPf), p.2)) <$>
        (simulateQ Common.loggedOracles (A (rootsOfS s))).run [] := by
  rw [uAdv, simulateQ_map, StateT.run_map]

theorem uFix_rootsB (t : SetupTrees) (π : UPf) : uFix (rootsB t) π = { π with roots := t.roots } := by
  rw [← rootsOfS_rootsB t]
  rfl

theorem run'_map_lazy {α β : Type} (f : α → β) (X : OracleComp Common.RandomPermutationOracles α)
    (s : Common.PermutationEdges KeccakState) :
    (simulateQ Common.lazyRandomPermutationOracles (f <$> X)).run' s =
      f <$> (simulateQ Common.lazyRandomPermutationOracles X).run' s := by
  rw [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, StateT.run'_eq,
    Functor.map_map]

/-! ## The verifiers, outcome by outcome -/

/-! ## The coupling -/

end UniSound

