-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The verifier's and the setup's part of `formal/EndToEnd/Completeness/E2ECompleteness/PcsWithHash.lean` (at the
-- protocol of `f96a7938`), transcribed from `formal/Statement` (`PcsQuotient`: `Transcript.lean`, `Reduction.lean`,
-- `PcsOpening.lean`, `Verifier.lean`, `Security.lean`) of the deployed protocol, with Keccak-256 an explicit
-- call, as `E2ECompleteness/WithHash.lean` did for the previous protocol. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- the runners with a hash (`runWithHash`, `runFromWithHash`, `buildTreeWithHash`), their equalities
-- with the runners over a permutation (`run_eq_withHash`, `runFrom_eq_withHash`,
-- `buildTreeM_eq_withHash`) and their simulation lemmas (`simulateQ_buildTreeM`, `simulateQ_absorb`,
-- `simulateQ_findNonceM`, `simulateQ_powStepM`, `simulateQ_openAll`).
import PcsQuotient.Security
import LeanVM.Protocol.WithHashBridge
import LeanVM.Protocol.Compile.Rom.Bridge
import LeanVM.Protocol.Compile.Rom.Prover

/-!
# The Statement's verifier with Keccak-256 an explicit call (the PCS claims)

The Statement's setup and verifier are written over a permutation `F`, Keccak-256 the sponge over it
(`keccak256With F`). Here each is rewritten with Keccak-256 a separate function `H` (`…H H F`), as mumbai's
runners are:

* **`…_eqH`**: at `H = keccak256With F` it is the Statement's (`rfl`, or mumbai's `…_eq_withHash`);
* **`simulateQ_…`**: over the two calls (`callKeccak256`, `callKeccakF1600`) it commutes with any
  simulation (`implH`, `implF`).

So the Statement's verifier over `π` is the two-call code answered over `π`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Prover
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript
open LeanVM.Protocol.Compile.Rom (implH implF simulateQ_queryH simulateQ_queryF simulateQ_absorb
  simulateQ_squeeze)

set_option autoImplicit false

namespace PcsKS.VH

section With

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- `Chain.startWith` with Keccak-256 `H`. -/
def startWithH (label : List UInt8) : m Chain := do
  return ⟨← H label, []⟩

/-- `Chain.squeezeWith` with Keccak-256 `H`. -/
def squeezeWithH (c : Chain) : m (E × Chain) := do
  let state ← H (digestBytes c.state ++ c.pending.flatMap scalarBytes)
  return (challengeOf state, ⟨state, []⟩)

/-- `reduceWith` with Keccak-256 `H`. -/
def reduceWithH (logRows : ℕ) (index : Commitment) (stmt : Statement) (p : ReductionProof) :
    m (Option Reduced) := do
  if ¬ Supported logRows then return none
  let c ← startWithH H (label index stmt)
  let some (witness, c) := readCommitment c p.witness | return none
  let (α, c) ← squeezeWithH H c
  let (β, c) ← squeezeWithH H c
  let (μ, c) ← squeezeWithH H c
  let some (table, c) := readCommitment c p.table | return none
  let (t, c) ← squeezeWithH H c
  let c := (p.values.toList.foldl Chain.absorb c).absorb p.next
  let (ρ, _) ← squeezeWithH H c
  return (claimsAt logRows stmt α β μ t ρ p.values p.next).map fun claims ↦ ⟨⟨witness, table⟩, claims⟩

/-- `oodPointWith` with Keccak-256 `H`. -/
def oodPointWithH (n : ℕ) (root : Digest) : m (List E) :=
  (List.range n).mapM fun j ↦ do
    return elementOf ((digestBytes (← H (oodInput n root j))).drop 8)

/-- `commitWith` with Keccak-256 `H`. -/
def commitWithH (μ : ℕ) (table : Array K) : m Tree :=
  buildTreeWithHash H (μ - laneFold + logInvRate) (stackWordFast μ logInvRate table)

/-- `commitmentWith` with Keccak-256 `H`. -/
def commitmentWithH (μ : ℕ) (table : Array K) : m (Tree × Commitment) := do
  let tree ← commitWithH H μ table
  let z ← oodPointWithH H μ tree.root
  return (tree, ⟨tree.root, tableEval table z⟩)

/-- `pcsSpongeWith` with Keccak-256 `H`. -/
def pcsSpongeWithH (c : Commitment) (claim : Claim) : m Sponge := do
  let iv ← H (pcsClaimBytes c claim)
  return ⟨← F (seedInput iv zeroDigest), []⟩

/-- `pcsOpeningWith` with Keccak-256 `H`. -/
def pcsOpeningWithH (c : Commitment) (claim : Claim) (proof : Compile.Proof) : m Bool := do
  let n := claim.point.length
  if minVars ≤ n ∧ n ≤ maxVars then
    let sp ← pcsSpongeWithH H F c claim
    match proof.stream with
    | x0 :: x1 :: rest =>
      let sp ← absorb F sp x0 dsObserve
      let sp ← absorb F sp x1 dsObserve
      if digestOfScalars (x0, x1) = some c.root then
        let z ← oodPointWithH H n c.root
        let program := verifyStackedOpening n logInvRate (pcsStackClaims z c claim)
        let height := n - laneFold + logInvRate
        match ← runWithHash H F program ⟨sp, rest, proof.openings, [(c.root, height, 2 ^ laneFold)]⟩ with
        | some (_, s) => return s.stream.isEmpty && s.openings.isEmpty
        | none => return false
      else return false
    | _ => return false
  else return false

/-- `checkAllWith` with Keccak-256 `H`. -/
def checkAllWithH : List (Commitment × Claim × Compile.Proof) → m Bool
  | [] => return true
  | (c, claim, proof) :: rest => do
    if !(← pcsOpeningWithH H F c claim proof) then return false
    checkAllWithH rest

/-- `verifyWith` with Keccak-256 `H`. -/
def verifyWithH (logRows : ℕ) (index : Commitment) (stmt : Statement) (proof : PcsQuotient.Proof) :
    m Bool := do
  match ← reduceWithH H logRows index stmt proof.reduction with
  | none => return false
  | some r => checkAllWithH H F (r.checks index proof.openings)

/-- `setupWith` with Keccak-256 `H`. -/
def setupWithH : m (Tree × Commitment) :=
  commitmentWithH H (cellVars logRows) (membership logRows).wiringTable

end With

/-! ## At `H = keccak256With F` -/

section Eq

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

theorem startWith_eqH (label : List UInt8) :
    Chain.startWith F label = startWithH (keccak256With F) label := rfl

theorem squeezeWith_eqH (c : Chain) : c.squeezeWith F = squeezeWithH (keccak256With F) c := rfl

theorem reduceWith_eqH (logRows : ℕ) (index : Commitment) (stmt : Statement) (p : ReductionProof) :
    reduceWith F logRows index stmt p = reduceWithH (keccak256With F) logRows index stmt p := rfl

theorem oodPointWith_eqH (n : ℕ) (root : Digest) :
    oodPointWith F n root = oodPointWithH (keccak256With F) n root := rfl

theorem commitWith_eqH (μ : ℕ) (table : Array K) :
    commitWith F μ table = commitWithH (keccak256With F) μ table :=
  buildTreeM_eq_withHash F _ _

theorem commitmentWith_eqH (μ : ℕ) (table : Array K) :
    commitmentWith F μ table = commitmentWithH (keccak256With F) μ table := by
  simp only [commitmentWith, commitmentWithH, commitWith_eqH, oodPointWith_eqH]

theorem pcsSpongeWith_eqH (c : Commitment) (claim : Claim) :
    pcsSpongeWith F c claim = pcsSpongeWithH (keccak256With F) F c claim := rfl

theorem pcsOpeningWith_eqH (c : Commitment) (claim : Claim) (proof : Compile.Proof) :
    pcsOpeningWith F c claim proof = pcsOpeningWithH (keccak256With F) F c claim proof := by
  simp only [pcsOpeningWith, pcsOpeningWithH, run_eq_withHash]
  rfl

theorem checkAllWith_eqH : ∀ l : List (Commitment × Claim × Compile.Proof),
    checkAllWith F l = checkAllWithH (keccak256With F) F l
  | [] => rfl
  | (c, claim, proof) :: rest => by
    simp only [checkAllWith, checkAllWithH, pcsOpeningWith_eqH, checkAllWith_eqH rest]

theorem verifyWith_eqH (logRows : ℕ) (index : Commitment) (stmt : Statement)
    (proof : PcsQuotient.Proof) :
    verifyWith F logRows index stmt proof =
      verifyWithH (keccak256With F) F logRows index stmt proof := by
  simp only [PcsQuotient.verifyWith, verifyWithH, reduceWith_eqH, checkAllWith_eqH]
  rfl

theorem setupWith_eqH : setupWith F = setupWithH (keccak256With F) := by
  simp only [setupWith, setupWithH, commitmentWith_eqH]

end Eq

/-! ## Simulation -/

section Commute

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl KeccakCalls r)

theorem simulateQ_startWithH (label : List UInt8) :
    simulateQ impl (startWithH callKeccak256 label) = startWithH (implH impl) label := by
  simp only [startWithH, simulateQ_bind, simulateQ_queryH, simulateQ_pure]

theorem simulateQ_squeezeWithH (c : Chain) :
    simulateQ impl (squeezeWithH callKeccak256 c) = squeezeWithH (implH impl) c := by
  simp only [squeezeWithH, simulateQ_bind, simulateQ_queryH, simulateQ_pure]

theorem simulateQ_reduceWithH (logRows : ℕ) (index : Commitment) (stmt : Statement)
    (p : ReductionProof) :
    simulateQ impl (reduceWithH callKeccak256 logRows index stmt p) =
      reduceWithH (implH impl) logRows index stmt p := by
  unfold reduceWithH
  by_cases hs : Supported logRows
  · simp only [hs, not_true_eq_false, ite_false, simulateQ_bind, simulateQ_startWithH]
    congr 1; funext c
    rcases hw : readCommitment c p.witness with _ | ⟨w, c₁⟩
    · simp
    simp only [simulateQ_bind, simulateQ_squeezeWithH]
    congr 1; funext x₁; congr 1; funext x₂; congr 1; funext x₃
    rcases hh : readCommitment x₃.2 p.table with _ | ⟨h, c₂⟩
    · simp
    simp only [simulateQ_bind, simulateQ_squeezeWithH, simulateQ_pure]
  · simp [hs]

theorem simulateQ_oodPointWithH (n : ℕ) (root : Digest) :
    simulateQ impl (oodPointWithH callKeccak256 n root) = oodPointWithH (implH impl) n root := by
  unfold oodPointWithH
  generalize List.range n = l
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_queryH, simulateQ_pure, ih]

theorem simulateQ_commitWithH (μ : ℕ) (table : Array K) :
    simulateQ impl (commitWithH callKeccak256 μ table) = commitWithH (implH impl) μ table :=
  LeanVM.Protocol.Compile.simulateQ_buildTreeM impl _ _

theorem simulateQ_commitmentWithH (μ : ℕ) (table : Array K) :
    simulateQ impl (commitmentWithH callKeccak256 μ table) =
      commitmentWithH (implH impl) μ table := by
  simp only [commitmentWithH, simulateQ_bind, simulateQ_commitWithH, simulateQ_oodPointWithH,
    simulateQ_pure]

theorem simulateQ_pcsSpongeWithH (c : Commitment) (claim : Claim) :
    simulateQ impl (pcsSpongeWithH callKeccak256 callKeccakF1600 c claim) =
      pcsSpongeWithH (implH impl) (implF impl) c claim := by
  simp only [pcsSpongeWithH, simulateQ_bind, simulateQ_queryH, simulateQ_queryF, simulateQ_pure]

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

theorem simulateQ_pcsOpeningWithH (c : Commitment) (claim : Claim) (proof : Compile.Proof) :
    simulateQ impl (pcsOpeningWithH callKeccak256 callKeccakF1600 c claim proof) =
      pcsOpeningWithH (implH impl) (implF impl) c claim proof := by
  unfold pcsOpeningWithH
  by_cases hn : minVars ≤ claim.point.length ∧ claim.point.length ≤ maxVars
  · simp only [hn, and_self, ite_true, simulateQ_bind, simulateQ_pcsSpongeWithH]
    congr 1; funext sp
    rcases hs : proof.stream with _ | ⟨x0, _ | ⟨x1, rest⟩⟩
    · simp
    · simp
    simp only [simulateQ_bind, simulateQ_absorb]
    congr 1; funext sp₁; congr 1; funext sp₂
    by_cases hd : digestOfScalars (x0, x1) = some c.root
    · simp only [hd, ite_true, simulateQ_bind, simulateQ_oodPointWithH, simulateQ_runWithHash]
      congr 1; funext z; congr 1; funext o
      rcases o with _ | ⟨_, s⟩ <;> simp
    · simp [hd]
  · simp [hn]

theorem simulateQ_checkAllWithH : ∀ l : List (Commitment × Claim × Compile.Proof),
    simulateQ impl (checkAllWithH callKeccak256 callKeccakF1600 l) =
      checkAllWithH (implH impl) (implF impl) l
  | [] => by simp [checkAllWithH]
  | (c, claim, proof) :: rest => by
    simp only [checkAllWithH, simulateQ_bind, simulateQ_pcsOpeningWithH]
    congr 1; funext b
    split
    · simp
    · exact simulateQ_checkAllWithH rest

theorem simulateQ_verifyWithH (logRows : ℕ) (index : Commitment) (stmt : Statement)
    (proof : PcsQuotient.Proof) :
    simulateQ impl (verifyWithH callKeccak256 callKeccakF1600 logRows index stmt proof) =
      verifyWithH (implH impl) (implF impl) logRows index stmt proof := by
  unfold verifyWithH
  simp only [simulateQ_bind, simulateQ_reduceWithH]
  congr 1; funext z
  split
  · simp
  · exact simulateQ_checkAllWithH impl _

theorem simulateQ_setupWithH :
    simulateQ impl (setupWithH callKeccak256) = setupWithH (implH impl) :=
  simulateQ_commitmentWithH impl _ _

end Commute


/-! ## The claims' points -/

/-- **The claims' points**: `W`'s and the wiring's `m = logRows + 2` coordinates, `T`'s `m + 4`. -/
theorem claimsAt_lengths {logRows : ℕ} {stmt : Statement} {α β μ t ρ : E} {v : Vector E 3} {next : E}
    {cl : Claims} (h : claimsAt logRows stmt α β μ t ρ v next = some cl) :
    cl.witness.point.length = cellVars logRows ∧ cl.wiring.point.length = cellVars logRows ∧
      cl.copy.point.length = cellVars logRows + 4 := by
  unfold claimsAt at h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    have hm : 2 ≤ cellVars logRows := by simp only [cellVars]; omega
    simp only [copyPoint, List.length_append, List.length_cons, List.length_nil, List.length_take,
      List.length_drop, List.length_map, List.length_range]
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega

/-! ## The opening's program -/

/-- `15 ≤ n ≤ 28` (`minVars`, `maxVars`) is WHIR-admissible at rate `1/2`. -/
theorem admissible_of_vars {n : ℕ} (h : minVars ≤ n ∧ n ≤ maxVars) :
    Whir.Admissible n PcsQuotient.logInvRate := by
  simp only [minVars, maxVars] at h
  simp only [Whir.Admissible, Whir.minLogStack, Whir.maxLogStack, Whir.minLogInvRate,
    Whir.maxLogInvRate, PcsQuotient.logInvRate]
  omega

/-- Running a sequence is running its first part, then the rest from the state it leaves (copied
from Bridge-Defs). -/
theorem runWithHash_bind {m : Type → Type} [Monad m] [LawfulMonad m] (H : Bytes → m Digest)
    (F : KeccakState → m KeccakState) {α β : Type} (P : Prog α) (f : α → Prog β) :
    ∀ s : ProgState, runWithHash H F (P.bind f) s = runWithHash H F P s >>= fun o => match o with
      | some (a, s') => runWithHash H F (f a) s'
      | none => pure none := by
  induction P with
  | ret a => intro s; simp [Prog.bind, runWithHash]
  | fail => intro s; simp [Prog.bind, runWithHash]
  | read k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split <;> simp [ih]
  | sample k ih =>
    intro s
    simp [Prog.bind, runWithHash, ih]
  | grind b k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split
    · simp
    · simp only [bind_assoc]
      congr 1; funext sp; congr 1; funext cs
      split <;> simp [ih]
  | commit h w k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split
    · simp only [bind_assoc]
      congr 1; funext sp0; congr 1; funext sp1
      split <;> simp [ih]
    · simp
  | query i ps k ih =>
    intro s
    simp only [Prog.bind, runWithHash]
    split
    · simp
    · simp only [bind_assoc]
      congr 1; funext o
      split <;> simp [ih]

theorem dot_powers_two (lam a b : E) : dot (powers lam 2) [a, b] = a + lam * b := by
  simp [powers, powersFrom, dot]

end PcsKS.VH
