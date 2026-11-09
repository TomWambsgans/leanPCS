-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Copied from `formal/UniSound/UniSound/FsSetup.lean`
-- (removed; `simulateQ_loggedKC_stackSetupS`, `run_logImplKC`, `loggedKC_bind`, `loggedKC_pure`, statements and proofs
-- verbatim), which follows `formal/EndToEnd/Soundness/TreeLog.lean` (`loggedKC_buildTree`) and `Bridge/Setup.lean`
-- (`commitWith_eq`) of this repository. These lemmas do not depend on the VM.
import UniSound.FsWalk
import Bridge.Setup

/-!
# One plain tree, logged, and logging a bind (VM-generic)

The two VM-generic facts about the logged setup that π2's setup bridge (`FsSetup.lean`, `pi2SetupBridge`) uses:

* **`simulateQ_loggedKC_stackSetupS`**: the logged setup of `colOf a v` at the plain shape of `2^v` words
  (`24 ≤ v ≤ 28`), answered over `π`, is `PcsQuotient.commitWith π v a`'s tree, its root as bytes and its log
  `Soundness.treeTr` (TreeLog's `loggedKC_buildTree`, mumbai's `simulateQ_buildTreeM`, `Bridge.Setup.commitWith_eq`).
* **`loggedKC_bind`**, **`loggedKC_pure`** (from `run_logImplKC`): logging a bind logs the first computation, then
  the second with its log appended.
-/

namespace RecCompose

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniSound
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-- **The logged setup of one plain tree**, answered over `π`, is the Statement's WHIR commitment
(`PcsQuotient.commitWith`) of the array, its root as bytes and its log the tree's evaluations. -/
theorem simulateQ_loggedKC_stackSetupS (v : ℕ) (h1 : 24 ≤ v) (h2 : v ≤ 28) (a : Array K) :
    simulateQ keccakCallsOverQueryPermutation
        (loggedKC (stackSetupS (plainShape v h1 h2) (colOf a v))) =
      (fun t : LeanVM.Prover.Tree => (toB t.root, Soundness.treeTr t)) <$>
        PcsQuotient.commitWith Common.queryPermutation v a := by
  unfold stackSetupS wiringSetup
  rw [Soundness.loggedKC_map, Soundness.loggedKC_buildTree,
    Functor.map_map, simulateQ_map, LeanVM.Protocol.Compile.simulateQ_buildTreeM,
    Bridge.Setup.commitWith_eq Common.queryPermutation v (by omega) (by omega) a]
  rfl

/-- **Logging from a log** appends to it the log from the empty one. -/
theorem run_logImplKC {α : Type} (oa : OracleComp KeccakCalls α) :
    ∀ l : Transcript, (simulateQ logImplKC oa).run l =
      (fun q => (q.1, l ++ q.2)) <$> (simulateQ logImplKC oa).run [] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro l; simp
  | query_bind t k ih =>
    intro l
    rw [loggedKC_run_query_bind, loggedKC_run_query_bind, map_bind]
    refine bind_congr fun u => ?_
    rw [ih u (l ++ (inlEntry ⟨t, u⟩).toList), ih u ([] ++ (inlEntry ⟨t, u⟩).toList),
      Functor.map_map]
    simp only [List.nil_append, List.append_assoc]

/-- **Logging a bind**: the first computation's log, then the second's appended. -/
theorem loggedKC_bind {α β : Type} (oa : OracleComp KeccakCalls α)
    (f : α → OracleComp KeccakCalls β) :
    loggedKC (oa >>= f) =
      loggedKC oa >>= fun p => (fun q => (q.1, p.2 ++ q.2)) <$> loggedKC (f p.1) := by
  unfold loggedKC
  rw [logImplKC_bind]
  exact bind_congr fun p => run_logImplKC (f p.1) p.2

theorem loggedKC_pure {α : Type} (a : α) :
    loggedKC (pure a : OracleComp KeccakCalls α) = pure (a, []) := by
  simp [loggedKC]

end RecCompose

/-- info: 'RecCompose.simulateQ_loggedKC_stackSetupS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.simulateQ_loggedKC_stackSetupS
