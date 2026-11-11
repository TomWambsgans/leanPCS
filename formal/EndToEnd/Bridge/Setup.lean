-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Uses leanerVM `mumbai` (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR
-- Apache-2.0): `buildTreeM_eq_withHash`, `Enc.stackWordFast_eq`, `simulateQ_buildTreeM`,
-- `stackWord`, `Column`, `KeccakCalls`.
import Bridge.Ntt
import PcsQuotient.Security
import Compose.WiringSetup
import LeanVM.Prover.Ntt
import Bridge.Opening
import Compose.Claims
import Compose.Rpm
import QuotientSecurity.DeployedConcrete
import Shared.SoundnessDefs

/-!
# The statement's WHIR commitment is mumbai's tree

A table as WHIR's column (`columnOf`, `columnOf_toArray_getD`), the fast stack word is mumbai's
(`stackWordFast_eq_columnOf`, `stackWordFast_congr`), and **`commitWith_eq`**: the statement's `commitWith`
over `F` is mumbai's tree of `stackWord`, Keccak-256 the sponge over `F`.

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

set_option linter.unusedSectionVars false

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete
open LeanVM.Prover (Tree buildTreeM buildTreeWithHash stackWordFast stackCodes)
open PcsQuotient PcsQuotient.Domain QuotientSecurity Finset OracleComp

namespace Bridge.Setup

/-! ## A stack as a `Column` -/

/-- **A stack as mumbai's `Column μ`**: its first `2^μ` entries, zero past its end. -/
def columnOf (μ : ℕ) (a : Array K) : Column μ := ⟨Vector.ofFn fun i : Fin (2 ^ μ) ↦ a.getD i 0⟩

theorem columnOf_toArray_getD (μ : ℕ) (a : Array K) {i : ℕ} (hi : i < 2 ^ μ) :
    (columnOf μ a).values.toArray.getD i 0 = a.getD i 0 := by
  simp [columnOf, Array.getD_eq_getD_getElem?, hi]

/-- **The NTT's word reads the stack's first `2^μ` entries only.** -/
theorem stackWordFast_congr (μ R : ℕ) (h6 : 6 ≤ μ) {a b : Array K}
    (h : ∀ i < 2 ^ μ, a.getD i 0 = b.getD i 0) : stackWordFast μ R a = stackWordFast μ R b := by
  have hsplit : 2 ^ μ = 2 ^ (μ - 6) * 64 := by
    rw [show (64 : ℕ) = 2 ^ 6 from rfl, ← pow_add]; congr 1; omega
  have hidx : ∀ v u : ℕ, v < 2 ^ (μ - 6) → u < 64 → v + 2 ^ (μ - 6) * u < 2 ^ μ := by
    intro v u hv hu
    rw [hsplit]
    calc v + 2 ^ (μ - 6) * u < 2 ^ (μ - 6) + 2 ^ (μ - 6) * u := by omega
      _ = 2 ^ (μ - 6) * (u + 1) := by ring
      _ ≤ 2 ^ (μ - 6) * 64 := Nat.mul_le_mul_left _ hu
  have hcodes : stackCodes μ R a = stackCodes μ R b := by
    simp only [stackCodes]
    congr 1
    funext u
    congr 2
    funext v
    exact h _ (hidx v u v.isLt u.isLt)
  funext p
  simp only [stackWordFast, stackWordFast.stackWordOf, hcodes]
  split
  · rfl
  · refine congrArg List.reverse (List.map_congr_left fun u hu ↦ ?_)
    refine congrArg (fun g ↦ encKAt (μ - 6) g p) (funext fun x ↦ ?_)
    exact h _ (hidx _ u (LeanVM.Protocol.Whir.bitsToNat_lt x) (List.mem_range.mp hu))

/-- **The NTT's word is mumbai's specification's** (`stackWord`) of the stack as a `Column`. -/
theorem stackWordFast_eq_columnOf (μ R : ℕ) (h6 : 6 ≤ μ) (h64 : μ ≤ 64) (a : Array K) :
    stackWordFast μ R a = stackWord μ (columnOf μ a) := by
  rw [stackWordFast_congr μ R h6 (b := (columnOf μ a).values.toArray)
    (fun i hi ↦ (columnOf_toArray_getD μ a hi).symm)]
  exact LeanVM.Prover.Enc.stackWordFast_eq h64 R _

section With

variable {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState)

/-- **The statement's WHIR commitment is mumbai's tree of `stackWord`**, Keccak-256 the sponge over
`F`. -/
theorem commitWith_eq (μ : ℕ) (h6 : 6 ≤ μ) (h64 : μ ≤ 64) (a : Array K) :
    commitWith F μ a = buildTreeWithHash (keccak256With F) (μ - 6 + 1) (stackWord μ (columnOf μ a)) := by
  rw [commitWith, show logInvRate = 1 from rfl, show laneFold = 6 from rfl,
    stackWordFast_eq_columnOf μ 1 h6 h64, LeanVM.Prover.buildTreeM_eq_withHash]

end With

end Bridge.Setup

/-! ## Axioms -/

/-- info: 'Bridge.Setup.stackWordFast_eq_columnOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.Setup.stackWordFast_eq_columnOf
