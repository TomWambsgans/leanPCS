-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's honest prover is `formal/UniKeccakComplete`'s
-- (`K/Rec4Prover.lean`, `proveRec4With`, after `crates/leanvm/univariate`'s `KECCAK_REC4`); here with its Fiat–Shamir
-- hash and rate apart from its trees' hash, as the recursion runs it (`crates/leanvm/rec`: π1's Fiat–Shamir is the real
-- Keccak-256, which π2's circuit recomputes; its Merkle trees and WHIR openings are those the block proves the claims
-- by, in the random-permutation model). Ported from this library's π1-rec3 version (`Pi1KeccakProver.lean`, retired).
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- Keccak-256 over Keccak-f[1600] (`keccak256`), the two calls `KeccakCalls` and their simulation lemmas.
import UniKeccakComplete.K.Rec4Prover
import RecStatement.Security
import RecCompose.Pi2P1

/-!
# π1-rec4's honest prover in the recursion: its Fiat–Shamir over Keccak-f[1600]

`UniKeccakComplete.Rec4.uniProverRec4RP D` (the prover of `uniCompletenessKeccakRec4_closed`) hashes its Fiat–Shamir
(IV, seed, the stream's wide draws and Flock's draws) with Keccak-256 and its rate over the random permutation `π`.
π1-rec4's graph (`RecGraph.evalGraphDeployed (RecStatement.pi1GraphAt roots)`) and `RecStatement.pi1KeccakVerifierWith`
hash it over the **real** Keccak-f[1600]: the recursion's π1 prover is that prover with its Fiat–Shamir over
Keccak-f[1600], its trees and openings over `π`. As on the membership side, the deployed Rust prover is trusted for
completeness; the Lean prover is a transcription of `prove.rs` at `KECCAK_REC4` (UniKeccakComplete's).

* **`proveRec4With2 Hfs W Hm F`**: `UniKeccakComplete.Rec4.proveRec4With` with its hash split: `Hfs` and its rate `W`
  for the Fiat–Shamir (the Keccak contract's IV `contractIvOf`, the seed `seedOf`, the stream's draws), `Hm` for the
  Merkle trees (the setup's `setupTreeOf`, the commitments `commitReal`) and the PCS claims' openings
  (`openingsTail3 Hm F`). At one hash it is UniKeccakComplete's prover, by `rfl` (**`proveRec4With2_self`**).
* **`pi1ProverFs4 Hfs W D`**: the prover over the random permutation with its Fiat–Shamir hash `Hfs` and rate `W`.
* **`pi1Rec4ProverK D = pi1ProverFs4 hKF wKF D`**, `hKF x = pure (keccak256 x)`, `wKF x = pure (rateKF x)` (the rate of
  Keccak-256 over Keccak-f[1600]): **its Fiat–Shamir over Keccak-f[1600]**, a pure function, no query; its trees and
  openings over `π`.
* **`pi1ProverFs4_rpm`**: at `Hfs = keccak256With π`, `W = rateWith π` it is `uniProverRec4RP D.pi1`, by `rfl`.
* **`p1kK4 D`**: the same over the two calls (Keccak-256 `callKeccak256` for the trees, the permutation for WHIR), the
  Fiat–Shamir pure; **`pi1Rec4ProverK_eq`**: over `π` (`keccakCallsOverQueryPermutation`) it is `pi1Rec4ProverK`
  (`simulateQ_p1kK4`, from **`app_proveRec4With2`**: the prover commutes with every monad morphism).
-/

set_option autoImplicit false

namespace RecCompose.Pi1K

open UniStatement LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open UniKeccakComplete UniKeccakComplete.Rec4
open LeanVM.Protocol.Compile.Rom (implH implF)
open RecStatement (RecDeployment Pi1Prover)

/-! ## The prover with its Fiat–Shamir apart -/

section With

variable {m : Type → Type} [Monad m] (Hfs : List UInt8 → m Digest) (W : List UInt8 → m RateB)
  (Hm : List UInt8 → m Digest) (F : KeccakState → m KeccakState)

/-- **π1-rec4's honest prover with its Fiat–Shamir apart**: the setup's tree over `Hm`, the Keccak contract's IV at
`keccakRec4` and the seed over `Hfs` (at the setup's commitment `setupRootsOf`), the stream (its draws over `Hfs` and
`W`, its commitments' trees over `Hm`), then the three PCS claims' openings over `Hm`, `F` (`openingsTail3`);
`UniKeccakComplete.Rec4.proveRec4With` with its hash split. -/
def proveRec4With2 (fuel : ℕ) (programIv : List UInt8) (tr : Trace) : m (Option UniKeccak.KeccakProof) := do
  let tree ← setupTreeOf Hm tr
  let iv ← contractIvOf Hfs tr.shape UniKeccak.keccakRec4 programIv (setupRootsOf tr tree)
  let seed ← seedOf Hfs iv tr.publicInput
  let (out, _) ← (proveStreamRec4With Hfs W (commitReal Hm) tr).run (UniComplete.Wr.start seed)
  Rec3.openingsTail3 Hm F fuel tr tree out

/-- **π1-rec4's honest prover on a witness, its Fiat–Shamir apart**: `proveRec4With2` on the placed trace,
`nonceFuel` nonces a proof of work. -/
def uniProverRec4With2 (D : UniKeccak.KDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    m (Option UniKeccak.KeccakProof) :=
  proveRec4With2 Hfs W Hm F PcsQuotient.nonceFuel D.programIv (honestTrace D input rows q)

end With

/-- **At one hash, UniKeccakComplete's prover.** -/
theorem proveRec4With2_self {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (W : List UInt8 → m RateB)
    (F : KeccakState → m KeccakState) : proveRec4With2 H W H F = proveRec4With H W F := rfl

theorem uniProverRec4With2_self {m : Type → Type} [Monad m] (H : List UInt8 → m Digest) (W : List UInt8 → m RateB)
    (F : KeccakState → m KeccakState) : uniProverRec4With2 H W H F = uniProverRec4With H W F := rfl

/-! ## The recursion's π1 prover -/

/-- **Keccak-256 over the real Keccak-f[1600]**, as a pure call in any monad (`keccak256`: what π2's circuit, π1-rec4's
graph and `RecStatement.pi1Iv`, `UniKeccak.runK4` compute). -/
def hKF {m : Type → Type} [Monad m] (x : List UInt8) : m Digest := pure (keccak256 x)

/-- **Keccak-256's rate over the real Keccak-f[1600]** (`keccak256_rate`, what π1-rec4's wide draws read). -/
def rateKF (x : List UInt8) : RateB := Id.run (rateWith (m := Id) (fun s ↦ pure (keccakF1600 s)) x)

/-- The rate over the real Keccak-f[1600], as a pure call in any monad. -/
def wKF {m : Type → Type} [Monad m] (x : List UInt8) : m RateB := pure (rateKF x)

/-- **π1-rec4's prover in the recursion with its Fiat–Shamir hash `Hfs` and rate `W`**: the setup's tree, the
commitments and the WHIR openings over the random permutation (Keccak-256 the sponge over `π`). -/
def pi1ProverFs4 (Hfs : List UInt8 → OracleComp Common.RandomPermutationOracles Digest)
    (W : List UInt8 → OracleComp Common.RandomPermutationOracles RateB) (D : RecDeployment) : Pi1Prover D :=
  uniProverRec4With2 Hfs W (keccak256With Common.queryPermutation) Common.queryPermutation D.pi1

/-- **π1-rec4's honest prover in the recursion**: its Fiat–Shamir (IV, seed, the stream's draws) Keccak-256 and its rate
over the real Keccak-f[1600], pure functions; its trees and its three PCS openings over the random permutation. -/
def pi1Rec4ProverK (D : RecDeployment) : Pi1Prover D := pi1ProverFs4 hKF wKF D

/-- **Keccak-f[1600] read as the random permutation**: UniKeccakComplete's π1-rec4 prover over `π`, whose completeness
is `uniCompletenessKeccakRec4_closed`. -/
theorem pi1ProverFs4_rpm (D : RecDeployment) :
    pi1ProverFs4 (keccak256With Common.queryPermutation) (rateWith Common.queryPermutation) D =
      uniProverRec4RP D.pi1 := rfl

/-- **π1-rec4's honest prover in the recursion over the two calls**: Fiat–Shamir pure (`hKF`, `wKF`), the trees
Keccak-256 calls, WHIR's sponge and grinding permutation calls. -/
def p1kK4 (D : RecDeployment) : Pi2G.Pi1ProverK D := fun input rows q ↦
  uniProverRec4With2 hKF wKF callKeccak256 callKeccakF1600 D.pi1 input rows q

/-! ## Commutation with monad morphisms -/

section Top

variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (φ : Morph m n)
  (Hfs : List UInt8 → m Digest) (W : List UInt8 → m RateB) (Hm : List UInt8 → m Digest)
  (F : KeccakState → m KeccakState)

/-- **The prover with its Fiat–Shamir apart commutes with a monad morphism** that commutes with the opening. -/
theorem app_proveRec4With2
    (hopen : ∀ (fuel n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E),
      φ.app (pcsProveH Hm F fuel n tree stack pt v) =
        pcsProveH (fun x ↦ φ.app (Hm x)) (fun s ↦ φ.app (F s)) fuel n tree stack pt v)
    (fuel : ℕ) (programIv : List UInt8) (tr : Trace) :
    φ.app (proveRec4With2 Hfs W Hm F fuel programIv tr) =
      proveRec4With2 (fun x ↦ φ.app (Hfs x)) (fun x ↦ φ.app (W x)) (fun x ↦ φ.app (Hm x)) (fun s ↦ φ.app (F s))
        fuel programIv tr := by
  have hs : ∀ seed, φ.app ((proveStreamRec4With Hfs W (commitReal Hm) tr).run (UniComplete.Wr.start seed)) =
      (proveStreamRec4With (fun x ↦ φ.app (Hfs x)) (fun x ↦ φ.app (W x)) (commitReal fun x ↦ φ.app (Hm x)) tr).run
        (UniComplete.Wr.start seed) := fun seed ↦ by
    rw [← Morph.wr_run, wr_proveStreamRec4With φ Hfs W _ _ (Morph.app_commitReal φ Hm)]
  simp only [proveRec4With2, φ.app_bind, Morph.app_setupTreeOf, Morph.app_contractIvOf, Morph.app_seedOf, hs]
  refine bind_congr fun tree ↦ bind_congr fun iv ↦ bind_congr fun seed ↦ bind_congr fun x ↦ ?_
  exact app_openingsTail3 φ Hm F hopen fuel tr tree x.1

end Top

section Commute

/-- A pure call is kept by a simulation. -/
theorem sim_hKF {ι : Type} {spec : OracleSpec.{0, 0} ι} {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl spec r) : (fun x ↦ (Morph.sim impl).app (hKF (m := OracleComp spec) x)) = hKF := by
  funext x
  exact simulateQ_pure impl _

/-- A pure rate is kept by a simulation. -/
theorem sim_wKF {ι : Type} {spec : OracleSpec.{0, 0} ι} {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl spec r) : (fun x ↦ (Morph.sim impl).app (wKF (m := OracleComp spec) x)) = wKF := by
  funext x
  exact simulateQ_pure impl _

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- **The recursion's π1 prover over the two calls commutes with any simulation**: simulated by `impl`, its trees and
openings over `impl`'s two calls, its Fiat–Shamir still `hKF`, `wKF`. -/
theorem simulateQ_p1kK4 (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) :
    simulateQ impl (p1kK4 D input rows q) =
      uniProverRec4With2 hKF wKF (implH impl) (implF impl) D.pi1 input rows q := by
  have h := app_proveRec4With2 (Morph.sim impl) hKF wKF callKeccak256 callKeccakF1600
    (fun fuel n tree stack pt v ↦ by
      rw [Morph.sim_H, Morph.sim_F]
      exact simulateQ_pcsProveH impl fuel n tree stack pt v)
    PcsQuotient.nonceFuel D.pi1.programIv (honestTrace D.pi1 input rows q)
  rw [Morph.sim_H, Morph.sim_F, sim_hKF, sim_wKF] at h
  exact h

end Commute

/-- **Over `π`, the two-call program is the recursion's π1 prover.** -/
theorem pi1Rec4ProverK_eq (D : RecDeployment) (input : Vector UInt8 32) (rows : List ℕ) (q : D.pi1.Stack rows) :
    pi1Rec4ProverK D input rows q = simulateQ keccakCallsOverQueryPermutation (p1kK4 D input rows q) := by
  rw [simulateQ_p1kK4]
  rfl

end RecCompose.Pi1K

/-- info: 'RecCompose.Pi1K.app_proveRec4With2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.app_proveRec4With2

/-- info: 'RecCompose.Pi1K.pi1Rec4ProverK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.Pi1K.pi1Rec4ProverK_eq
