-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Transcribed from `formal/Statement` (`PcsQuotient`: `Transcript.lean`, `Reduction.lean`,
-- `Opening.lean`, `Verifier.lean`, `Circuit.lean`, `Prover.lean`, `Security.lean`), with Keccak-256 an
-- explicit call. Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit
-- 6175f1a0, MIT OR Apache-2.0): the runners with a hash (`runWithHash`, `runFromWithHash`,
-- `buildTreeWithHash`), their equalities with the runners over a permutation
-- (`run_eq_withHash`, `runFrom_eq_withHash`, `buildTreeM_eq_withHash`) and their simulation
-- lemmas (`simulateQ_run`, `simulateQ_buildTreeM`, `simulateQ_absorb`, `simulateQ_findNonceM`).
import PcsQuotient.Security
import LeanVM.Protocol.WithHashBridge
import LeanVM.Protocol.Compile.Rom.Bridge
import LeanVM.Protocol.Compile.Rom.Prover

/-!
# The layout opening with the hash as a parameter

`commitWith`, `openingSpongeWith`, `openingWith` and `proveOpeningWith` over a hash `H` (`commitWithH`,
`openingSpongeWithH`, `openingWithH`, `proveOpeningWithH`), each the statement's at `H = keccak256With F`
(`*_eqH`) and commuting with a simulation (`simulateQ_*`, `simulateQ_runWithHash`, `simulateQ_runFromWithHash`).

Pruned to what the leanVM line uses (`formal/Uni*`, `formal/Rec*`); the previous membership protocol's declarations
that were here are in the git history.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF simulateQ_absorb
  simulateQ_squeeze simulateQ_run)

set_option autoImplicit false

namespace E2ECompleteness

section With

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- `openingSpongeWith` with Keccak-256 `H`. -/
def openingSpongeWithH (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim) : m Sponge := do
  let pre := openingLabel ++ u64Bytes openingVersion ++ digestBytes L.id ++ u64Bytes L.logN ++
    u64Bytes logInvRate
  let iv ← H (pre ++ claimBytes claims)
  return ⟨← F (seedInput iv zeroDigest), []⟩

/-- `openingWith` with Keccak-256 `H`. -/
def openingWithH (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim) (proof : Compile.Proof) :
    m Bool := do
  if claims ≠ [] ∧ claims.all (·.point.length = L.vars) then
    match proof.stream with
    | x0 :: x1 :: rest =>
      let sp ← openingSpongeWithH H F L claims
      let sp ← absorb F sp x0 dsObserve
      let sp ← absorb F sp x1 dsObserve
      match digestOfScalars (x0, x1) with
      | some r =>
        if r.toList = root.toList then
          let program := verifyStackedOpening L.logN logInvRate
            (stackClaims L claims)
          let height := L.logN - laneFold + logInvRate
          match ← runWithHash H F program ⟨sp, rest, proof.openings, [(root, height, 2 ^ laneFold)]⟩ with
          | some (_, s) => return s.stream.isEmpty && s.openings.isEmpty
          | none => return false
        else return false
      | none => return false
    | _ => return false
  else return false

/-- `commitWith` with Keccak-256 `H`. -/
def commitWithH (μ : ℕ) (stack : Array K) : m Tree :=
  buildTreeWithHash H (μ - 6 + 1) (stackWordFast μ 1 stack)

end With

section Eq

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem openingWith_eqH (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim) (proof : Compile.Proof) :
    openingWith F L root claims proof = openingWithH (keccak256With F) F L root claims proof := by
  simp only [openingWith, openingWithH, run_eq_withHash]
  rfl

theorem commitWith_eqH (μ : ℕ) (stack : Array K) :
    commitWith F μ stack = commitWithH (keccak256With F) μ stack :=
  buildTreeM_eq_withHash F _ _

end Eq

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

theorem simulateQ_openingSpongeWithH (L : PcsQuotient.Layout) (claims : List PcsQuotient.Claim) :
    simulateQ impl (openingSpongeWithH callKeccak256 callKeccakF1600 L claims) =
      openingSpongeWithH (implH impl) (implF impl) L claims := by
  simp only [openingSpongeWithH, simulateQ_bind, simulateQ_queryH, simulateQ_queryF,
    simulateQ_pure]

/-- mumbai's `simulateQ_run`, for a program of any result type. -/
theorem simulateQ_runWithHash {α : Type} :
    ∀ (p : Prog α) (s : ProgState),
      simulateQ impl (runWithHash callKeccak256 callKeccakF1600 p s) =
        runWithHash (implH impl) (implF impl) p s
  | .ret a, s => by simp [runWithHash]
  | .fail, s => by simp [runWithHash]
  | .read k, s => by
    simp only [runWithHash]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_absorb]
      congr 1; funext sp; exact simulateQ_runWithHash _ _
  | .sample k, s => by
    simp only [runWithHash, simulateQ_bind, simulateQ_squeeze]
    congr 1; funext r; exact simulateQ_runWithHash _ _
  | .grind bits k, s => by
    simp only [runWithHash]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_absorb, simulateQ_squeeze]
      congr 1; funext sp; congr 1; funext r
      split
      · exact simulateQ_runWithHash _ _
      · simp
  | .commit ht w k, s => by
    simp only [runWithHash]
    split
    · simp only [simulateQ_bind, simulateQ_absorb]
      congr 1; funext sp0; congr 1; funext sp1
      split
      · exact simulateQ_runWithHash _ _
      · simp
    · simp
  | .query i ps k, s => by
    simp only [runWithHash]
    split
    · simp
    · simp only [simulateQ_bind, LeanVM.Protocol.Compile.Rom.simulateQ_openAll]
      congr 1; funext o
      split
      · exact simulateQ_runWithHash _ _
      · simp

theorem simulateQ_openingWithH (L : PcsQuotient.Layout) (root : Digest) (claims : List PcsQuotient.Claim)
    (proof : Compile.Proof) :
    simulateQ impl (openingWithH callKeccak256 callKeccakF1600 L root claims proof) =
      openingWithH (implH impl) (implF impl) L root claims proof := by
  unfold openingWithH
  split
  · split
    · simp only [simulateQ_bind, simulateQ_openingSpongeWithH, simulateQ_absorb]
      congr 1; funext sp; congr 1; funext sp; congr 1; funext sp
      split
      · split
        · simp only [simulateQ_bind]
          congr 1
          · exact simulateQ_runWithHash impl _ _
          · funext z
            split <;> simp
        · simp
      · simp
    · simp
  · simp

theorem simulateQ_commitWithH (μ : ℕ) (stack : Array K) :
    simulateQ impl (commitWithH callKeccak256 μ stack) = commitWithH (implH impl) μ stack :=
  simulateQ_buildTreeM impl _ _

end Commute

section ProverWith

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- `proveOpeningWith` with Keccak-256 `H`. -/
def proveOpeningWithH (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree) (stack : Array K)
    (claims : List PcsQuotient.Claim) : m (Option Compile.Proof) := do
  let (r0, r1) := digestScalars tree.root
  let sp ← openingSpongeWithH H F L claims
  let sp ← absorb F sp r0 dsObserve
  let sp ← absorb F sp r1 dsObserve
  let program := verifyStackedOpening L.logN logInvRate
    (stackClaims L claims)
  let r ← runFromWithHash H F fuel program (some (openingScript L stack claims)) sp [tree]
  return r.map fun t ↦ ⟨r0 :: r1 :: t.1, t.2⟩

end ProverWith

section ProverEq

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem proveOpeningWith_eqH (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree) (stack : Array K)
    (claims : List PcsQuotient.Claim) :
    proveOpeningWith F fuel L tree stack claims =
      proveOpeningWithH (keccak256With F) F fuel L tree stack claims := by
  simp only [proveOpeningWith, proveOpeningWithH, runFrom_eq_withHash]
  rfl

end ProverEq

section ProverCommute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

/-- The script runner commutes with simulation. -/
theorem simulateQ_runFromWithHash (fuel : ℕ) {α β : Type} (P : Prog α) :
    ∀ (S : Option (Script β)) (sp : Sponge) (cs : List Tree),
      simulateQ impl (runFromWithHash callKeccak256 callKeccakF1600 fuel P S sp cs) =
        runFromWithHash (implH impl) (implF impl) fuel P S sp cs := by
  induction P with
  | ret a => intro S sp cs; simp [runFromWithHash]
  | fail => intro S sp cs; simp [runFromWithHash]
  | read k ih =>
    intro S sp cs
    simp only [runFromWithHash, simulateQ_bind, simulateQ_absorb, simulateQ_pure, ih]
  | sample k ih =>
    intro S sp cs
    simp only [runFromWithHash, simulateQ_bind, simulateQ_squeeze, ih]
  | grind bits k ih =>
    intro S sp cs
    simp only [runFromWithHash, simulateQ_bind, simulateQ_findNonceM]
    congr 1; funext o
    cases o with
    | none => simp
    | some n => simp only [simulateQ_bind, simulateQ_powStepM, simulateQ_pure, ih]
  | commit ht w k ih =>
    intro S sp cs
    simp only [runFromWithHash, simulateQ_bind, simulateQ_buildTreeM, simulateQ_absorb,
      simulateQ_pure, ih]
  | query i ps k ih =>
    intro S sp cs
    simp only [runFromWithHash]
    split
    · simp
    · simp only [simulateQ_bind, simulateQ_pure, ih]

theorem simulateQ_proveOpeningWithH (fuel : ℕ) (L : PcsQuotient.Layout) (tree : Tree)
    (stack : Array K) (claims : List PcsQuotient.Claim) :
    simulateQ impl (proveOpeningWithH callKeccak256 callKeccakF1600 fuel L tree stack claims) =
      proveOpeningWithH (implH impl) (implF impl) fuel L tree stack claims := by
  simp only [proveOpeningWithH, simulateQ_bind, simulateQ_openingSpongeWithH, simulateQ_absorb,
    simulateQ_runFromWithHash, simulateQ_pure]

end ProverCommute

end E2ECompleteness
