-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The walks of
-- `formal/EndToEnd/Completeness/E2ECompleteness/Cost.lean` (`cost_runFromWithHash`, `cost_proveOpeningWithH`,
-- `qc_findNonceM`), redone for the lengths of the hashed inputs; uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- `KeccakCalls`, the block cost `hashBlocks`, the weight calculus `Common.QueryCostAtMost`, VCVio's `IsQueryBound`.
import RecCompose.Pi2RunCost
import RecCompose.HashShort

/-!
# Before π2's IV, nothing of `2^26` bytes is hashed

π2's IV starts with a hash of `σ`'s `4 · 2^24 = 2^26` bytes (`Pi2H.digestWithH`). Every Keccak-256 query before it,
in `pi2Staged`'s stage A, is shorter (`Short`):

* **`hashOK_setupTreesWithH2`**: the setup's two trees (π1's Keccak setup stack, π2's `κ`, `κ + σ`: `512`-byte leaves,
  `64`-byte nodes);
* **`hashOK_graph`**: π1-rec4's graph with its three claims' openings, from its block count (`3 · gOpen` blocks, so no
  query of `136 · 3 · gOpen < 2^26` bytes or more; **`hashOK_of_qc`**);
* π1-rec4's prover: the named `Pi1HashShort` (`Pi2P1`). The tools a concrete prover's census uses are here: Merkle
  trees of rows of at most `192` words (`hashOK_buildTree`, `hashOK_commitWithH`), WHIR openings
  (**`hashOK_proveOpeningWithH`**: the seed of `76 + 24 · k(v + 1)` bytes at most, the trees, the sponge and the
  proof-of-work search through the permutation only), a writer's walk in the calculus `WS` (every query short, the
  stream at most `2^14` bytes; `ws_of_wc` from UniComplete's `WC` costs, `ws_seq`, `ws_lift`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open LeanVM.Prover (Tree Script)
open RecStatement
open UniStatement
open E2ECompleteness (HashOK hashOK_callKeccak256 hashOK_callKeccakF1600)
open E2ECompleteness.Cost (qc_absorb qc_squeeze qc_powStepM qc_openingSpongeWithH OWordsLE
  oWordsLE_afterSend oWordsLE_afterSample oWordsLE_afterGrind oWordsLE_afterCommit oWordsLE_afterQuery
  length_wordOf_le wordsLE_openingScript)
open UniKeccakComplete.Cost (CostP costP_query_bind WC WInv wpot)

namespace RecCompose.Pi2A

/-- **The setup's two trees.** -/
theorem hashOK_setupTreesWithH2 (D : RecDeployment) :
    HashOK Short (Pi2H.setupTreesWithH callKeccak256 callKeccakF1600 D) := by
  unfold Pi2H.setupTreesWithH Pi2H.setupTreeKWithH Pi2H.setupTreeWithH
  exact E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦
    E2ECompleteness.HashOK.bind (hashOK_commitWithH _ _) fun _ ↦ E2ECompleteness.HashOK.pure _ _

/-! ## π1-rec4's graph -/

/-- **π1-rec4's graph with its three claims' openings** (`3 · gOpen` blocks). -/
theorem hashOK_graph (D : RecDeployment) (roots : UniKeccak.SetupRootsK)
    (input : Vector UInt8 32) (p : UniKeccak.KeccakProof) :
    HashOK Short (Pi2H.pi1GraphVerifierWithH callKeccak256 callKeccakF1600 D roots input p) :=
  hashOK_of_qc (Pi2G.Cost2.qc_pi1GraphVerifierWithH D roots input p) (by
    unfold Pi2G.Cost2.gOpen UniKeccakComplete.Cost.openCost E2ECompleteness.Cost.vOpen
    norm_num [LeanVM.Protocol.Verifier.whirBound])

end RecCompose.Pi2A

/-- info: 'RecCompose.Pi2A.hashOK_setupTreesWithH2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2A.hashOK_setupTreesWithH2

/-- info: 'RecCompose.Pi2A.hashOK_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi2A.hashOK_graph

