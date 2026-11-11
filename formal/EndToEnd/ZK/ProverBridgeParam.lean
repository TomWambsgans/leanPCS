-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The proof pattern (one commutation lemma per function, pushed through the binds; the run by induction
-- on the program) is adapted from `formal/EndToEnd/Completeness/E2ECompleteness/WithHash.lean`
-- (`simulateQ_runFromWithHash`, `simulateQ_proveWithH`), with a monad morphism for `simulateQ`. The
-- functions are leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0: `Statement/Keccak.lean`'s
-- `absorbBlockWith`, `absorbWith`, `keccak256With`; `Statement/LeanVmVerifier.lean`'s `duplex`, `absorb`,
-- `squeeze`; `Statement/Prover/Run.lean`'s `leafDigestsM`, `parentsM`, `levelsM`, `buildTreeM`,
-- `powStepM`, `searchM`, `findNonceM`, `runFrom`) and `formal/Statement`'s.
import ZK.ProverBridgeHom

/-!
# Keccak-256 over the permutation is parametric in its monad

Read through a monad morphism `φ : m → n` (`MHom`), Keccak-256 over a permutation `F` is Keccak-256 over
`φ ∘ F`: `absorbBlockWith_hom`, `absorbWith_hom`, `keccak256With_hom`.

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient PcsQuotient.Transcript

set_option autoImplicit false

namespace PcsQuotient.EndToEnd.Param

section Programs

variable {m n : Type → Type} [Monad m] [Monad n] (φ : MHom m n) (F : KeccakState → m KeccakState)

/-! ### Keccak-256 over the permutation -/

theorem absorbBlockWith_hom (state : KeccakState) (block : List UInt8) :
    φ.app (absorbBlockWith F state block) = absorbBlockWith (fun x ↦ φ.app (F x)) state block :=
  rfl

theorem absorbWith_hom : ∀ (blocks : ℕ) (state : KeccakState) (data : List UInt8),
    φ.app (absorbWith F blocks state data) = absorbWith (fun x ↦ φ.app (F x)) blocks state data
  | 0, state, data => by simp only [absorbWith, absorbBlockWith_hom]
  | blocks + 1, state, data => by
    simp only [absorbWith, φ.app_bind, absorbBlockWith_hom, absorbWith_hom blocks]

theorem keccak256With_hom (data : List UInt8) :
    φ.app (keccak256With F data) = keccak256With (fun x ↦ φ.app (F x)) data := by
  simp only [keccak256With, φ.app_bind, φ.app_pure, absorbWith_hom]

end Programs

end PcsQuotient.EndToEnd.Param
