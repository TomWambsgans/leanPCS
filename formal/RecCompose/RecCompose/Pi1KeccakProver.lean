-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec3's honest prover is `formal/UniKeccakComplete`'s
-- (`K/Rec3Prover.lean`, `proveRec3With`, after `crates/leanvm/univariate`'s `KECCAK_REC3`); here with two hashes, as
-- the recursion runs it (`crates/leanvm/rec`: π1's Fiat–Shamir is the real Keccak-256, which π2's circuit recomputes;
-- its Merkle trees and WHIR openings are those the block proves the claims by, in the random-permutation model).
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`,
-- commit 6175f1a0, MIT OR Apache-2.0): Keccak-256 over Keccak-f[1600] (`keccak256`), the two calls `KeccakCalls` and
-- their simulation lemmas.
import UniKeccakComplete.K.Rec3ProverSim
import RecStatement.Security

/-!
# π1-rec3's honest prover in the recursion: its Fiat–Shamir over Keccak-f[1600]

`UniKeccakComplete.Rec3.uniProverRec3RP flockProveH D` (the prover of `uniCompletenessKeccakRec3_closed`) hashes its
Fiat–Shamir (IV, seed, stream, Flock's draws) with Keccak-256 over the random permutation `π`. π1-rec3's graph
(`RecGraph.evalGraphDeployed RecGraphKeccak.Pi1.pi1GraphK`) and `RecStatement.pi1KeccakVerifierWith` hash it with
Keccak-256 over the **real** Keccak-f[1600]: the recursion's π1 prover is that prover with its Fiat–Shamir over
Keccak-f[1600], its trees and openings over `π`. As on the membership side, the deployed Rust prover is trusted for
completeness; the Lean prover is a transcription of `prove.rs` and `batch.rs` at `KECCAK_REC3` (UniKeccakComplete's).

* **`proveRec3With2 Hfs Hm F`**: `UniKeccakComplete.Rec3.proveRec3With` with two hashes, `Hfs` for the Fiat–Shamir
  (the Keccak contract's IV `contractIvOf`, the seed `seedOf`, the stream's draws, Flock's prover) and `Hm` for the
  Merkle trees (the setup's `setupTreeOf`, the commitments `commitReal`) and the WHIR openings
  (`proveOpeningWithH Hm F`). At one hash it is UniKeccakComplete's prover, by `rfl` (**`proveRec3With2_self`**).
* **`pi1ProverFs Hfs D`**: the prover over the random permutation with its Fiat–Shamir hash `Hfs`.
* **`pi1Rec3ProverK D = pi1ProverFs hKF D`**, `hKF x = pure (keccak256 x)`: **its Fiat–Shamir over Keccak-f[1600]**, a
  pure function, no query; its trees and openings over `π`. This is the `Pi1Prover` of `RecStatement`'s docstring.
* **`pi1ProverFs_rpm`**: at `Hfs = keccak256With queryPermutation` (Keccak-f[1600] read as the random permutation) it is
  `uniProverRec3RP flockProveH D.pi1`, by `rfl`.
* **`p1kK D`**: the same over the two calls (Keccak-256 `callKeccak256` for the trees, the permutation for WHIR), the
  Fiat–Shamir pure; **`pi1Rec3ProverK_eq`**: over `π` (`keccakCallsOverQueryPermutation`) it is `pi1Rec3ProverK`
  (`simulateQ_p1kK`, from **`app_proveRec3With2`**: the prover commutes with every monad morphism).
-/

set_option autoImplicit false

namespace RecCompose.Pi1K

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open UniKeccakComplete
open LeanVM.Protocol.Compile.Rom (implH implF)
open RecStatement (RecDeployment Pi1Prover)

/-! ## The prover with two hashes -/

section With

variable {m : Type → Type} [Monad m] (Hfs Hm : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **π1-rec3's honest prover with two hashes**: the setup's tree over `Hm`, the Keccak contract's IV and the seed over
`Hfs`, the stream (its draws over `Hfs`, its commitments' trees over `Hm`), then the three WHIR openings over `Hm`, `F`;
`UniKeccakComplete.Rec3.proveRec3With` with its hash split. -/
def proveRec3With2 (fuel : ℕ) (flock : FlockProver m) (programIv : List UInt8) (tr : Trace) :
    m (Option UniKeccak.KeccakProof) := do
  let tree ← setupTreeOf Hm tr
  let iv ← contractIvOf Hfs tr.shape UniKeccak.keccakRec3 programIv ⟨tree.root⟩
  let seed ← seedOf Hfs iv tr.publicInput
  let (out, _) ← (Rec3.proveStreamRec3With Hfs (commitReal Hm) flock tr).run (UniComplete.Wr.start seed)
  let words := UniKeccak.layoutWordsK tr.shape
  let openOne (c : Commitment) (pt : List E) (value : E) : m (Option Compile.Proof) :=
    let (stack, tree, word) : Array K × LeanVM.Prover.Tree × List UInt8 := match c with
      | .c1 => (out.c1.1, out.c1.2.tree, words.getD 0 [])
      | .c2 => (out.c2.1, out.c2.2.tree, words.getD 1 [])
      | .setup => (out.setup, tree, words.getD 2 [])
    E2ECompleteness.proveOpeningWithH Hm F fuel (plainLayout (layoutWordVars word)) tree stack [⟨pt, value⟩]
  let p1 ← match out.claims.find? (·.1 == .c1) with
    | some (_, pt, v) => openOne .c1 pt v
    | none => pure none
  let p2 ← match out.claims.find? (·.1 == .c2) with
    | some (_, pt, v) => openOne .c2 pt v
    | none => pure none
  let p3 ← match out.claims.find? (·.1 == .setup) with
    | some (_, pt, v) => openOne .setup pt v
    | none => pure none
  return do
    let c1 ← p1
    let c2 ← p2
    let s ← p3
    pure ⟨out.stream, c1, c2, s⟩

/-- **π1-rec3's honest prover on a witness, two hashes**: `proveRec3With2` on the placed trace, `nonceFuel` nonces a
proof of work, the deployment's `A0`, `B0` constants in the IV. -/
def uniProverRec3With2 (flock : FlockProver m) (D : UniKeccak.KDeployment) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) : m (Option UniKeccak.KeccakProof) :=
  proveRec3With2 Hfs Hm F PcsQuotient.nonceFuel flock D.programIv (honestTrace D input rows q)

end With

/-- **At one hash, UniKeccakComplete's prover.** -/
theorem proveRec3With2_self {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)
    (F : KeccakState → m KeccakState) : proveRec3With2 H H F = Rec3.proveRec3With H F := rfl

theorem uniProverRec3With2_self {m : Type → Type} [Monad m] (H : List UInt8 → m Digest)
    (F : KeccakState → m KeccakState) : uniProverRec3With2 H H F = Rec3.uniProverRec3With H F := rfl

/-! ## The recursion's π1 prover -/

/-- **Keccak-256 over the real Keccak-f[1600]**, as a pure call in any monad (`keccak256`: what π2's circuit, π1-rec3's
graph and `RecStatement.pi1Iv`, `UniKeccak.runK` compute). -/
def hKF {m : Type → Type} [Monad m] (x : List UInt8) : m Digest := pure (keccak256 x)

/-- **π1's prover in the recursion with its Fiat–Shamir hash `Hfs`**: the setup's tree, the commitments and the WHIR
openings over the random permutation (Keccak-256 the sponge over `π`), Flock's honest prover at `Hfs`. -/
def pi1ProverFs (Hfs : List UInt8 → OracleComp Common.RandomPermutationOracles Digest) (D : RecDeployment) :
    Pi1Prover D :=
  uniProverRec3With2 Hfs (keccak256With Common.queryPermutation) Common.queryPermutation (flockProveH Hfs) D.pi1

/-- **π1-rec3's honest prover in the recursion**: its Fiat–Shamir (IV, seed, stream, Flock's draws) Keccak-256 over the
real Keccak-f[1600], a pure function; its trees and its three WHIR openings over the random permutation. -/
def pi1Rec3ProverK (D : RecDeployment) : Pi1Prover D := pi1ProverFs hKF D

/-- **Keccak-f[1600] read as the random permutation**: UniKeccakComplete's π1-rec3 prover over `π`, whose completeness
is `uniCompletenessKeccakRec3_closed`. -/
theorem pi1ProverFs_rpm (D : RecDeployment) :
    pi1ProverFs (keccak256With Common.queryPermutation) D = Rec3.uniProverRec3RP flockProveH D.pi1 := rfl

/-- **π1-rec3's honest prover in the recursion over the two calls**: Fiat–Shamir pure (`hKF`), the trees Keccak-256
calls, WHIR's sponge and grinding permutation calls. -/
def p1kK (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) :
    OracleComp KeccakCalls (Option UniKeccak.KeccakProof) :=
  uniProverRec3With2 hKF callKeccak256 callKeccakF1600 (flockProveH hKF) D.pi1 input rows q

/-! ## Commutation with monad morphisms -/

section Top

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
  (Hfs Hm : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **The two-hash prover commutes with a monad morphism** that commutes with Flock's prover and with the opening. -/
theorem app_proveRec3With2
    (hopen : ∀ (fuel : ℕ) (L : PcsQuotient.Layout) (tree : LeanVM.Prover.Tree) (stack : Array K)
      (claims : List PcsQuotient.Claim),
      φ.app (E2ECompleteness.proveOpeningWithH Hm F fuel L tree stack claims) =
        E2ECompleteness.proveOpeningWithH (fun x ↦ φ.app (Hm x)) (fun s ↦ φ.app (F s)) fuel L tree stack claims)
    (flock : FlockProver m) (flock' : FlockProver n) (hflock : ∀ logN v q, φ.wr (flock logN v q) = flock' logN v q)
    (fuel : ℕ) (programIv : List UInt8) (tr : Trace) :
    φ.app (proveRec3With2 Hfs Hm F fuel flock programIv tr) =
      proveRec3With2 (fun x ↦ φ.app (Hfs x)) (fun x ↦ φ.app (Hm x)) (fun s ↦ φ.app (F s)) fuel flock'
        programIv tr := by
  have hs : ∀ seed, φ.app ((Rec3.proveStreamRec3With Hfs (commitReal Hm) flock tr).run (UniComplete.Wr.start seed)) =
      (Rec3.proveStreamRec3With (fun x ↦ φ.app (Hfs x)) (commitReal fun x ↦ φ.app (Hm x)) flock' tr).run
        (UniComplete.Wr.start seed) := fun seed ↦ by
    rw [← Morph.wr_run, Rec3.wr_proveStreamRec3With φ Hfs _ _ (Morph.app_commitReal φ Hm) flock flock' hflock]
  simp only [proveRec3With2, φ.app_bind, Morph.app_setupTreeOf, Morph.app_contractIvOf, Morph.app_seedOf, hs]
  refine bind_congr fun tree ↦ bind_congr fun iv ↦ bind_congr fun seed ↦ bind_congr fun x ↦ ?_
  obtain ⟨out, _⟩ := x
  dsimp only
  generalize List.find? (fun x ↦ x.1 == Commitment.c1) out.claims = o1
  generalize List.find? (fun x ↦ x.1 == Commitment.c2) out.claims = o2
  generalize List.find? (fun x ↦ x.1 == Commitment.setup) out.claims = o3
  rcases o1 with _ | ⟨_, pt1, v1⟩ <;> rcases o2 with _ | ⟨_, pt2, v2⟩ <;> rcases o3 with _ | ⟨_, pt3, v3⟩ <;>
    simp only [φ.app_bind, φ.app_pure, hopen]

end Top

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- A pure call is kept by a simulation. -/
theorem sim_hKF : (fun x ↦ (Morph.sim impl).app (hKF (m := OracleComp KeccakCalls) x)) = hKF := by
  funext x
  exact simulateQ_pure impl _

/-- **The recursion's π1 prover over the two calls commutes with any simulation**: simulated by `impl`, its trees and
openings over `impl`'s two calls, its Fiat–Shamir still `hKF`. -/
theorem simulateQ_p1kK (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) :
    simulateQ impl (p1kK D input rows q) =
      uniProverRec3With2 hKF (implH impl) (implF impl) (flockProveH hKF) D.pi1 input rows q := by
  have h := app_proveRec3With2 (Morph.sim impl) hKF callKeccak256 callKeccakF1600
    (fun fuel L tree stack claims ↦ by
      rw [Morph.sim_H, Morph.sim_F]
      exact E2ECompleteness.simulateQ_proveOpeningWithH impl fuel L tree stack claims)
    (flockProveH hKF) (flockProveH hKF)
    (fun logN v q ↦ by rw [flockCommutes_flockProveH, sim_hKF]) PcsQuotient.nonceFuel
    D.pi1.programIv (honestTrace D.pi1 input rows q)
  rw [Morph.sim_H, Morph.sim_F, sim_hKF] at h
  exact h

end Commute

/-- **Over `π`, the two-call program is the recursion's π1 prover.** -/
theorem pi1Rec3ProverK_eq (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) :
    pi1Rec3ProverK D input rows q = simulateQ keccakCallsOverQueryPermutation (p1kK D input rows q) := by
  rw [simulateQ_p1kK]
  rfl

end RecCompose.Pi1K

/-- info: 'RecCompose.Pi1K.app_proveRec3With2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.app_proveRec3With2

/-- info: 'RecCompose.Pi1K.pi1Rec3ProverK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1Rec3ProverK_eq
