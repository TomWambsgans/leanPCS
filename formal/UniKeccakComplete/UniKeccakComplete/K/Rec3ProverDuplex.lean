-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the duplex discipline (`LeanVM.Rpm.DuplexVm`, `DuplexP`, `HOnly`), and
-- `formal/EndToEnd/Completeness/E2ECompleteness/Duplex.lean`'s `Disc`, `disc_proveOpeningWithH`,
-- `hOnly_commitWithH`.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/Rec3ProverDuplex.lean`.
import UniKeccakComplete.K.Rec3ProverSim

/-!
# The duplex discipline of π1-rec3's honest prover

The port of `ProverDuplex.lean` to π1-rec3's prover (`Rec3Prover.lean`): over the two calls, every Keccak-f[1600]
call of the prover continues a duplex or starts one at a zero capacity, from any earlier answers
(**`disc_uniProverRec3With`**, `duplexVm_uniProverRec3With`), hence **`disc_rec3_flockProveH`** for the honest Flock
prover (`flockHashOnly_flockProveH`, through the main line's `flockHashOnly_of_commutes`).

* **The stream only hashes** (`wHOnly_proveStreamRec3With`): π1-rec3's new draws are Keccak-256 calls (the narrow
  draw `sampleNarrowW`, the run of squares `drawRunW`), the paired batch's rounds write and draw only
  (`wHOnly_pairRound3`, `wHOnly_plainRound3`, `wHOnly_batchRounds3`); the commitments, the writes, `sampleW` and
  Flock's prover (`FlockHashOnly`) are the main line's (`ProverDuplex.lean`'s `WHOnly` calculus).
* **The setup, π1-rec3's IV and the seed only hash** (`hOnly_setupTreeOf`, `hOnly_contractIvOf` at `keccakRec3`).
* **The permutation is called by the three openings only**, each disciplined (E2ECompleteness's
  `disc_proveOpeningWithH`).

Decision (recorded): the stream's walk is the main line's `wh_step` with π1-rec3's two new leaves tried first
(`wh3_step`: `drawRunW`, `batchRounds3`); the openings' walk is the main line's `disc_step`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open UniStatement
open E2ECompleteness (Disc disc_pure disc_of_hOnly)

set_option autoImplicit false

namespace UniKeccakComplete.Rec3

open UniComplete

/-! ## The stream -/

section Stream

/-- **The narrow draw only hashes.** -/
theorem wHOnly_sampleNarrowW : WHOnly (sampleNarrowW callKeccak256) := by
  unfold sampleNarrowW
  exact wHOnly_get.bind fun _ ↦ (wHOnly_lift (hOnly_queryH _)).bind fun _ ↦ (wHOnly_set _).bind fun _ ↦
    wHOnly_pure _

/-- **A run of squares only hashes** (one draw, none for an empty run). -/
theorem wHOnly_drawRunW (count : ℕ) : WHOnly (drawRunW callKeccak256 count) := by
  unfold drawRunW
  split
  · exact wHOnly_pure _
  · exact wHOnly_sampleW.bind fun _ ↦ wHOnly_pure _

/-- **A pair round only hashes.** -/
theorem wHOnly_pairRound3 (lambda : E) (nq : ℕ) (st : BatchState) :
    WHOnly (pairRound3 callKeccak256 lambda nq st) := by
  unfold pairRound3
  exact (wHOnly_sendScalars _).bind fun _ ↦ wHOnly_sampleNarrowW.bind fun _ ↦ wHOnly_pure _

/-- **The last plain round only hashes.** -/
theorem wHOnly_plainRound3 (lambda : E) (nh : ℕ) (st : BatchState) :
    WHOnly (plainRound3 callKeccak256 lambda nh st) := by
  unfold plainRound3
  exact (wHOnly_sendScalar _).bind fun _ ↦ (wHOnly_sendScalar _).bind fun _ ↦ wHOnly_sampleNarrowW.bind fun _ ↦
    wHOnly_pure _

/-- **π1-rec3's batching sumcheck's rounds only hash.** -/
theorem wHOnly_batchRounds3 (lambda : E) (vars : ℕ) (st : BatchState) :
    WHOnly (batchRounds3 callKeccak256 lambda vars st) := by
  unfold batchRounds3
  refine (wHOnly_forIn_list _ _ _ fun _ _ ↦ (wHOnly_pairRound3 _ _ _).bind fun _ ↦ wHOnly_pure _).bind
    fun _ ↦ ?_
  dsimp only
  split
  · exact (wHOnly_plainRound3 _ _ _).bind fun _ ↦ wHOnly_pure _
  · exact wHOnly_pure _

set_option hygiene false in
/-- One step of π1-rec3's stream's walk: its two new leaves (the run of squares, the paired batch), else the main
line's `wh_step` (`hcommit`, `hflock` the local hypotheses on the commitment and Flock's prover). -/
macro "wh3_step" : tactic => `(tactic| first
  | with_reducible_and_instances refine (wHOnly_drawRunW _).bind fun _ ↦ ?_
  | with_reducible_and_instances refine (wHOnly_batchRounds3 _ _ _).bind fun _ ↦ ?_
  | wh_step)

/-- **π1-rec3's stream only hashes**, given that the commitment and Flock's prover do. -/
theorem wHOnly_proveStreamRec3With (commit : Commitment → ℕ → Array K → OracleComp KeccakCalls Committed)
    (hcommit : ∀ c v s, HOnly (commit c v s)) (flock : FlockProver (OracleComp KeccakCalls))
    (hflock : ∀ logN v q, WHOnly (flock logN v q)) (tr : Trace) :
    WHOnly (proveStreamRec3With callKeccak256 commit flock tr) := by
  unfold proveStreamRec3With
  repeat wh3_step

end Stream

/-! ## The prover -/

section Prover

/-- **π1-rec3's honest prover is disciplined**, from any earlier answers, given that Flock's prover only hashes. -/
theorem disc_proveRec3With (flock : FlockProverH) (hflock : FlockHashOnly flock) (fuel : ℕ) (a0 b0 : Digest)
    (programIv : List UInt8) (tr : Trace) :
    Disc (proveRec3With callKeccak256 callKeccakF1600 fuel (flock callKeccak256) a0 b0 programIv tr) := by
  unfold proveRec3With
  refine (disc_of_hOnly (hOnly_setupTreeOf tr)).bind fun tree ↦ ?_
  refine (disc_of_hOnly (hOnly_contractIvOf _ _ _ _)).bind fun iv ↦ ?_
  refine (disc_of_hOnly (hOnly_queryH _)).bind fun seed ↦ ?_
  refine (disc_of_hOnly (wHOnly_proveStreamRec3With _ hOnly_commitReal _ (hflock · · ·) tr _)).bind
    fun x ↦ ?_
  obtain ⟨out, _⟩ := x
  dsimp only
  generalize List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    repeat disc_step

/-- **π1-rec3's deployed honest prover is disciplined**, from any earlier answers. -/
theorem disc_uniProverRec3With (flock : FlockProverH) (hflock : FlockHashOnly flock) (D : UniKeccak.KDeployment)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    Disc (uniProverRec3With callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) :=
  disc_proveRec3With flock hflock _ _ _ _ _

/-- **π1-rec3's deployed honest prover follows the duplex discipline** (mumbai's `DuplexVm`, from no earlier
answer), given that Flock's prover only hashes. -/
theorem duplexVm_uniProverRec3With (flock : FlockProverH) (hflock : FlockHashOnly flock) (D : UniKeccak.KDeployment)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    DuplexVm (uniProverRec3With callKeccak256 callKeccakF1600 (flock callKeccak256) D input rows q) [] :=
  (duplexVm_iff_duplexP _ _).mpr (disc_uniProverRec3With flock hflock D input rows q [])

end Prover

/-- **π1-rec3's prover with the honest Flock prover is disciplined**, from any earlier answers (the π1-rec3 analogue
of `Prob.ProverDuplex`, without its hypotheses). -/
theorem disc_rec3_flockProveH (D : UniKeccak.KDeployment) (input : Vector UInt8 32) (rows : List ℕ)
    (q : D.Stack rows) :
    Disc (uniProverRec3With callKeccak256 callKeccakF1600 (flockProveH callKeccak256) D input rows q) :=
  disc_uniProverRec3With flockProveH flockHashOnly_flockProveH D input rows q

end UniKeccakComplete.Rec3

/-! ## Axioms -/

/-- info: 'UniKeccakComplete.Rec3.disc_uniProverRec3With' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.disc_uniProverRec3With

/-- info: 'UniKeccakComplete.Rec3.duplexVm_uniProverRec3With' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.duplexVm_uniProverRec3With

/-- info: 'UniKeccakComplete.Rec3.disc_rec3_flockProveH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec3.disc_rec3_flockProveH
