-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The two calls and their answer over `π` are leanerVM's
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `KeccakCalls`, `keccakCallsOverQueryPermutation`); the duplex discipline, the block count and the hash census are
-- `formal/EndToEnd/Completeness`'s (`E2ECompleteness.Disc`, `E2ECompleteness.Cost.QC`, `E2ECompleteness.HashOK`).
import RecStatement.Security
import E2ECompleteness.Duplex
import E2ECompleteness.Cost
import E2ECompleteness.Chain
import LeanVM.Protocol.ExperimentBridge

/-!
# π1-rec4's prover, as π2's completeness takes it: an abstract program and four named facts

π2's completeness is stated for an **abstract** π1 prover `P1 : Pi1Prover D` (over the random permutation, as
`RecCompleteness2` takes it) together with a **two-call program** `P1k : Pi1ProverK D` (its Keccak-256 and
Keccak-f[1600] queries explicit), and the four properties the proof uses, each a named `Prop` about `P1k`, on honest
statements only (row counts fitting the shape, `KvHonest D.flock`). The recursion's π1-rec4 prover meets them:
`Pi1K.pi1ProverFactsK4` (`CompleteReal.lean`) for `Pi1K.pi1Rec4ProverK` and `Pi1K.p1kK4` (`Pi1Rec4Prover.lean`).

* **`Pi1OverPerm D P1 P1k`**: `P1` is `P1k` with its two calls answered over `π` (Keccak-256 the sponge over `π`,
  Keccak-f[1600] `π` itself; `keccakCallsOverQueryPermutation`). A concrete prover proves it by writing its code over
  any monad with the two functions explicit and showing it commutes with `simulateQ` (as UniKeccakComplete's
  `simulateQ_rec3_flockProveH` for π1-rec3's). For a prover whose Fiat–Shamir is the pure `keccak256` (the
  recursion's: π1-rec4's graph hashes with the real Keccak-f[1600]) the Fiat–Shamir hashes are not queries of `P1k`
  at all, only its trees' hashes and WHIR's permutation are.
* **`Pi1Disc D P1k`**: every Keccak-f[1600] query of `P1k` continues a duplex or starts one (`E2ECompleteness.Disc`,
  mumbai's `DuplexVm` discipline), from every history of earlier answers. Its permutation queries are WHIR's sponge and
  proofs of work; a prover proves it opening by opening (`E2ECompleteness.disc_proveOpeningWithH`), its hashes by
  `disc_of_hOnly`.
* **`Pi1Cost D P1k`**: at most `2^47` block calls (`E2ECompleteness.Cost.QC` at `hashBlocks`: a Keccak-256 of `n`
  bytes costs `⌊n / 136⌋ + 1`, a Keccak-f[1600] one). π1-rec3's prover's count was below `2^47`
  (UniKeccakComplete's `cost_rec3_flockProveH`), nearly all of it its three WHIR provers' proof-of-work budgets
  (about `2^46.70`), which do not depend on the VM nor on the Fiat–Shamir shape.
* **`Pi1HashShort D P1k`**: every Keccak-256 query of `P1k` is shorter than `2^26` bytes (`E2ECompleteness.HashOK`),
  the length of π2's `σ` hash. A prover's trees hash `512`-byte leaves and `64`-byte nodes, its WHIR openings short
  inputs; its Fiat–Shamir, if it queries it, its stream's pieces.

`Pi1ProverFacts D P1 P1k` bundles the four. Nothing else about π1's prover is used: in particular not that its proofs
are accepted (`RecCompleteness2`'s event asks π1-rec4's graph to accept; that π1's proofs are accepted is
`RecStatement.Pi1CompletenessKeccak`, a premise of the end-to-end theorem).
-/

namespace RecCompose.Pi2G

open RecStatement LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open LeanVM

/-- **π1-rec4's prover over the two calls**: from the public input, the row counts and a stack of the Keccak VM's
layout, a Keccak proof (or none), its Keccak-256 and Keccak-f[1600] queries explicit. -/
abbrev Pi1ProverK (D : RecDeployment) : Type :=
  Vector UInt8 32 → (rows : List ℕ) → D.pi1.Stack rows → OracleComp KeccakCalls (Option UniKeccak.KeccakProof)

/-- **Named: `P1` is `P1k` answered over `π`**, on honest statements. -/
def Pi1OverPerm (D : RecDeployment) (P1 : Pi1Prover D) (P1k : Pi1ProverK D) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    P1 input rows q = simulateQ keccakCallsOverQueryPermutation (P1k input rows q)

/-- **Named: `P1k`'s permutation queries follow the duplex discipline**, on honest statements. -/
def Pi1Disc (D : RecDeployment) (P1k : Pi1ProverK D) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q → E2ECompleteness.Disc (P1k input rows q)

/-- **Named: `P1k` makes at most `2^47` block calls**, on honest statements. -/
def Pi1Cost (D : RecDeployment) (P1k : Pi1ProverK D) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q → E2ECompleteness.Cost.QC (P1k input rows q) (2 ^ 47)

/-- **Named: `P1k` hashes only inputs shorter than `2^26` bytes**, on honest statements. -/
def Pi1HashShort (D : RecDeployment) (P1k : Pi1ProverK D) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows), D.pi1.shape.RowsFit rows →
    D.pi1.HonestRelation D.flock rows input q →
    E2ECompleteness.HashOK (fun x ↦ x.length < 2 ^ 26) (P1k input rows q)

/-- **The four named facts about π1-rec4's prover** π2's completeness uses. -/
structure Pi1ProverFacts (D : RecDeployment) (P1 : Pi1Prover D) (P1k : Pi1ProverK D) : Prop where
  overPerm : Pi1OverPerm D P1 P1k
  disc : Pi1Disc D P1k
  cost : Pi1Cost D P1k
  hashShort : Pi1HashShort D P1k

end RecCompose.Pi2G
