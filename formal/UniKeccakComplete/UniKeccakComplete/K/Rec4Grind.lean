-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's analogue of `Rec3Hyp.lean` (the deterministic
-- core's named facts) and `Rec3ProbGrind.lean` (`runAt_stagedU3`, `one_le_powPot_of_rejectedU3`, `rejectGood3`), on
-- the five-digest reading; uses `ProbGrind.lean`'s `winState`, `one_le_powPot_of_pcs_none` and leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the
-- proof-of-work potential `powPot`, the logged random oracle and its potential engine, the run at a log's answers.
import UniKeccakComplete.K.Rec4Split
import UniKeccakComplete.K.Rec3ProbGrind

/-!
# π1-rec4's grinding at good challenges

**The deterministic core** (at every pure rate function `W`, the hash its digest `hOf W`, and permutation `F`):
`CoreAccepts4` (at good bus challenges, `proverChallenges4`, and a good `t`, `proverTChallenge4`, the honest proof is
accepted by π1-rec4's verifier) and `CoreFailsOnlyAtPow4` (the prover fails only at an opening).

**`rejectGood4`**: in leanerVM's two-call random-oracle model, π1-rec4's staged run (`stagedU4`, the five-digest
reading) is rejected while its bus challenges avoid `BadFp` and `t` avoids `BadT` with probability at most
`Q · (1 − 2^-17)^(2^25)`, `Q` its query count: π1-rec3's argument (`Rec3ProbGrind.lean`). At the pure hash `Ht` of a
log's extension the five-digest reading is the experiment at the rate `rate5P Ht` (whose digest is `Ht`,
`hOf_rate5P`), the staged challenges the prover's (`runAt_stagedU4`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open UniStatement UniKeccak
open E2ECompleteness (ro runAt)
open UniKeccakComplete.Prob (winState one_le_powPot_of_pcs_none BadT ProverA firstInput tInput)
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Rec4

open UniComplete

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Rate functions -/

/-- **The digest of a rate function.** -/
def hOf (W : Bytes → RateB) (x : Bytes) : Digest := digestOfRate (W x)

/-- **The rate of five digests of a hash function** (the five-digest reading, pure). -/
def rate5P (Ht : Bytes → Digest) (x : Bytes) : RateB :=
  mkRate (Ht x) (Ht (extIn 1 x)) (Ht (extIn 2 x)) (Ht (extIn 3 x)) (Ht (extIn 4 x))

theorem hOf_rate5P (Ht : Bytes → Digest) : hOf (rate5P Ht) = Ht :=
  funext fun _ ↦ digestOfRate_mkRate _ _ _ _ _

theorem runAt_rate5 (Ht : Bytes → Digest) (Ft : KeccakState → KeccakState) (x : Bytes) :
    runAt Ht Ft (rate5 x) = rate5P Ht x := by
  simp only [runAt, rate5, simulateQ_bind, simulateQ_pure, simulateQ_queryH, implH_totalImpl]
  rfl

theorem runAt_hash5 (Ht : Bytes → Digest) (Ft : KeccakState → KeccakState) (x : Bytes) :
    runAt Ht Ft (hash5 x) = Ht x := by
  simp only [hash5, runAt, simulateQ_map]
  show digestOfRate (runAt Ht Ft (rate5 x)) = Ht x
  rw [runAt_rate5]
  exact digestOfRate_mkRate _ _ _ _ _

/-! ## The prover's challenges -/

variable (D : KDeployment)

/-- **π1-rec4's bus challenges** at a rate function (at `Id`): `α = squares c 4` and `β`, challenges `0` and `1` of the
rate of the bus draw's input. -/
def proverChallenges4 (W : Bytes → RateB) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : List E × E :=
  let a := proverA4 (m := Id) (hOf W) D input rows q
  let r₁ := W (firstInput rows a)
  (alphaOf4 r₁, challengeAt r₁.toList 1)

/-- **π1-rec4's `t`-stage challenge** at a rate function (at `Id`): Flock's point on `q_flock` (fixed before the point
draw) and `t`, challenge `0` of the point draw's rate. -/
def proverTChallenge4 (W : Bytes → RateB) (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) : List E × E :=
  let a := proverA4 (m := Id) (hOf W) D input rows q
  let r₁ := W (firstInput rows a)
  let x := (midB4 (m := Id) (hOf W) (commitReal (m := Id) (hOf W)) (honestTrace D input rows q) (busOf r₁)).run
    (writerAfter4 rows a.c1 a.ood r₁)
  (x.1.1.1, challengeAt (W (tInput x.2)).toList 0)

/-! ## The deterministic core -/

/-- **π1-rec4's PIOP's completeness at a pure rate function and permutation**: at good bus challenges and a good `t`,
the honest proof is accepted by π1-rec4's deployed verifier. -/
def CoreAccepts4 : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation KeccakFlock.keccakFlockSpec rows input q →
    ∀ (W : Bytes → RateB) (F : KeccakState → KeccakState) (π : KeccakProof),
      uniProverRec4With (m := Id) (hOf W) W F D input rows q = some π →
      ¬ BadFp (honestTrace D input rows q) (proverChallenges4 D W input rows q).1
        (proverChallenges4 D W input rows q).2 →
      ¬ BadT D.shape (proverTChallenge4 D W input rows q).1 (proverTChallenge4 D W input rows q).2 →
      KDeployment.verifierWith4H (m := Id) (hOf W) W F D (D.setupRoots (setupTreeKWithH (m := Id) (hOf W) F D))
        input π = true

/-- **π1-rec4's prover fails only at an opening**, at a pure rate function and permutation and good challenges. -/
def CoreFailsOnlyAtPow4 : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation KeccakFlock.keccakFlockSpec rows input q →
    ∀ (W : Bytes → RateB) (F : KeccakState → KeccakState),
      ¬ BadFp (honestTrace D input rows q) (proverChallenges4 D W input rows q).1
        (proverChallenges4 D W input rows q).2 →
      ¬ BadT D.shape (proverTChallenge4 D W input rows q).1 (proverTChallenge4 D W input rows q).2 →
      uniProverRec4With (m := Id) (hOf W) W F D input rows q = none →
      ∃ (n : ℕ) (tree : LeanVM.Prover.Tree) (stack : Array K) (pt : List E) (v : E), pt.length = n ∧
        pcsProveH (m := Id) (hOf W) F PcsQuotient.nonceFuel n tree stack pt v = none

/-! ## The staged run at a pure hash and permutation -/

theorem runAt_comp_tauW {α : Type} (Ht : Bytes → Digest) (Ft : KeccakState → KeccakState)
    (X : OracleComp KeccakCallsW α) :
    runAt Ht Ft (simulateQ tauW X) = simulateQ (totalImpl Ht Ft ∘ₛ tauW) X := by
  rw [runAt, QueryImpl.simulateQ_compose]

/-- **The five-digest experiment at a pure hash and permutation** is the experiment at the rate `rate5P Ht`. -/
theorem runAt_expW45 (Ht : Bytes → Digest) (Ft : KeccakState → KeccakState) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) :
    runAt Ht Ft (expW4 hash5 rate5 callKeccakF1600 D input rows q) =
      expW4 (m := Id) Ht (rate5P Ht) Ft D input rows q := by
  rw [← simulateQ_tauW_expWW, runAt_comp_tauW, simulateQ_expWW]
  have hH : (fun x ↦ simulateQ (totalImpl Ht Ft ∘ₛ tauW) (hashW x)) = Ht := by
    funext x
    rw [QueryImpl.simulateQ_compose, simulateQ_tauW_hashW]
    exact runAt_hash5 Ht Ft x
  have hW : (fun x ↦ simulateQ (totalImpl Ht Ft ∘ₛ tauW) (callRate x)) = rate5P Ht := by
    funext x
    rw [QueryImpl.simulateQ_compose, simulateQ_tauW_callRate]
    exact runAt_rate5 Ht Ft x
  have hF : (fun s ↦ simulateQ (totalImpl Ht Ft ∘ₛ tauW) (callFW s)) = Ft := by
    funext s
    rw [QueryImpl.simulateQ_compose, simulateQ_tauW_callFW]
    rfl
  rw [hH, hW, hF]

theorem sim_app {ι : Type} {spec : OracleSpec.{0, 0} ι} {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl spec r) {α : Type} (x : OracleComp spec α) : (Morph.sim impl).app x = simulateQ impl x := rfl

theorem sim_hash5 (Ht : Bytes → Digest) (Ft : KeccakState → KeccakState) :
    (fun x ↦ (Morph.sim (totalImpl Ht Ft)).app (hash5 x)) = Ht := by
  funext x
  rw [sim_app]
  exact runAt_hash5 Ht Ft x

theorem runAt_proverA4 (Ht : Bytes → Digest) (Ft : KeccakState → KeccakState) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) :
    runAt Ht Ft (proverA4 hash5 D input rows q) = proverA4 (m := Id) Ht D input rows q := by
  have h := (show (Morph.sim (totalImpl Ht Ft)).app (proverA4 hash5 D input rows q) =
      proverA4 (fun x ↦ (Morph.sim (totalImpl Ht Ft)).app (hash5 x)) D input rows q by
    simp only [proverA4, (Morph.sim (totalImpl Ht Ft)).app_bind, Morph.app_setupTreeOf, Morph.app_contractIvOf,
      Morph.app_seedOf, Morph.app_commitWithH, (Morph.sim (totalImpl Ht Ft)).app_pure])
  rw [sim_hash5] at h
  rw [sim_app] at h
  exact h

theorem runAt_midB4 (Ht : Bytes → Digest) (Ft : KeccakState → KeccakState) (tr : Trace) (bus : List E) (w : Wr) :
    runAt Ht Ft ((midB4 hash5 (commitReal hash5) tr bus).run w) =
      (midB4 (m := Id) Ht (commitReal (m := Id) Ht) tr bus).run w := by
  have h := wr_midB4 (Morph.sim (totalImpl Ht Ft)) hash5 (commitReal hash5)
    (commitReal fun x ↦ (Morph.sim (totalImpl Ht Ft)).app (hash5 x))
    (Morph.app_commitReal (Morph.sim (totalImpl Ht Ft)) hash5) tr bus
  rw [sim_hash5] at h
  rw [← h, Morph.wr_run, sim_app]

/-- **A staged run at a pure hash and permutation**, stage by stage. -/
theorem runAt_run4 (S : KStaged4) (Ht : Bytes → Digest) (Ft : KeccakState → KeccakState) :
    runAt Ht Ft S.run =
      ((runAt Ht Ft (S.C (runAt Ht Ft (S.B (runAt Ht Ft S.A) (runAt Ht Ft (rate5 (S.inp (runAt Ht Ft S.A))))))
          (runAt Ht Ft (rate5 (S.tin (runAt Ht Ft (S.B (runAt Ht Ft S.A)
            (runAt Ht Ft (rate5 (S.inp (runAt Ht Ft S.A)))))))))),
        (S.pr (runAt Ht Ft (S.B (runAt Ht Ft S.A) (runAt Ht Ft (rate5 (S.inp (runAt Ht Ft S.A)))))),
          challengeAt (runAt Ht Ft (rate5 (S.tin (runAt Ht Ft (S.B (runAt Ht Ft S.A)
            (runAt Ht Ft (rate5 (S.inp (runAt Ht Ft S.A))))))))).toList 0)),
        (alphaOf4 (runAt Ht Ft (rate5 (S.inp (runAt Ht Ft S.A)))),
          challengeAt (runAt Ht Ft (rate5 (S.inp (runAt Ht Ft S.A)))).toList 1)) := by
  simp only [KStaged4.run, runAt, simulateQ_bind, simulateQ_pure]
  rfl

theorem runAt_bind {α β : Type} (Ht : Bytes → Digest) (Ft : KeccakState → KeccakState)
    (X : OracleComp KeccakCalls α) (f : α → OracleComp KeccakCalls β) :
    runAt Ht Ft (X >>= f) = runAt Ht Ft (f (runAt Ht Ft X)) := by
  simp only [runAt, simulateQ_bind]
  rfl

theorem runAt_pure {α : Type} (Ht : Bytes → Digest) (Ft : KeccakState → KeccakState) (a : α) :
    runAt Ht Ft (pure a : OracleComp KeccakCalls α) = a := by
  simp only [runAt, simulateQ_pure]
  rfl

/-- **The staged run, written out.** -/
theorem stagedU4_run (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) :
    (stagedU4 D input rows q).run = (do
      let tree ← setupTreeKWithH hash5 callKeccakF1600 D
      let a ← proverA4 hash5 D input rows q
      let r₁ ← rate5 (firstInput rows a)
      let mw ← (midB4 hash5 (commitReal hash5) (honestTrace D input rows q) (busOf r₁)).run
        (writerAfter4 rows a.c1 a.ood r₁)
      let r₂ ← rate5 (tInput mw.2)
      let z ← (do
        let o ← proverD4 hash5 rate5 callKeccakF1600 D input rows q a r₁ mw r₂
        verdictW4 hash5 rate5 callKeccakF1600 D tree input o)
      return ((z, (mw.1.1.1, challengeAt r₂.toList 0)), (alphaOf4 r₁, challengeAt r₁.toList 1))) := by
  simp only [KStaged4.run, stagedU4, bind_assoc, pure_bind]

/-- **The staged run at a pure hash and permutation**: the experiment at the rate `rate5P Ht`, the prover's point
challenge with Flock's point, and its bus challenges. -/
theorem runAt_stagedU4 (Ht : Bytes → Digest) (Ft : KeccakState → KeccakState) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) :
    runAt Ht Ft (stagedU4 D input rows q).run =
      ((expW4 (m := Id) Ht (rate5P Ht) Ft D input rows q, proverTChallenge4 D (rate5P Ht) input rows q),
        proverChallenges4 D (rate5P Ht) input rows q) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · have h := congrArg (fun X ↦ runAt Ht Ft X) (expW4_eq_staged4 D input rows q)
    simp only [runAt, simulateQ_map] at h
    rw [← runAt_expW45]
    exact h.symm
  · rw [stagedU4_run]
    simp only [runAt_bind, runAt_pure, runAt_proverA4, runAt_rate5, runAt_midB4]
    unfold proverTChallenge4
    rw [hOf_rate5P]
  · rw [stagedU4_run]
    simp only [runAt_bind, runAt_pure, runAt_proverA4, runAt_rate5]
    unfold proverChallenges4
    rw [hOf_rate5P]

/-- The good outcomes: neither the bus challenges nor `t` bad. -/
abbrev GoodU4 (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows)
    (z : (Bool × (List E × E)) × (List E × E)) : Prop :=
  ¬ BadFp (honestTrace D input rows q) z.2.1 z.2.2 ∧ ¬ BadT D.shape z.1.2.1 z.1.2.2

/-- **A run rejected at good challenges puts the potential at one.** -/
theorem one_le_powPot_of_rejectedU4 (hacc : CoreAccepts4 D) (hpow : CoreFailsOnlyAtPow4 D)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) {ℓ : Log}
    {z : (Bool × (List E × E)) × (List E × E)}
    (hz : simulateQ (lookImpl ℓ) (stagedU4 D input rows q).run = some z)
    (hrej : z.1.1 = false) (hgood : GoodU4 D input rows q z) :
    1 ≤ powPot Whir.queryGrindingBits PcsQuotient.nonceFuel ℓ := by
  let Ht : Bytes → Digest := fun x ↦ (lookH ℓ x).getD default
  let Ft : KeccakState → KeccakState := fun s ↦ (lookF ℓ s).getD winState
  have hH : ∀ x u, lookH ℓ x = some u → Ht x = u := fun x u hx ↦ by simp [Ht, hx]
  have hF : ∀ s u, lookF ℓ s = some u → Ft s = u := fun s u hs ↦ by simp [Ft, hs]
  have hrun : runAt Ht Ft (stagedU4 D input rows q).run = z := simulateQ_id_of_look ℓ Ht Ft hH hF _ z hz
  rw [runAt_stagedU4] at hrun
  subst hrun
  obtain ⟨hab, ht⟩ := hgood
  dsimp only at hrej hab ht
  have hHt : hOf (rate5P Ht) = Ht := hOf_rate5P Ht
  cases hπ : uniProverRec4With (m := Id) (hOf (rate5P Ht)) (rate5P Ht) Ft D input rows q with
  | none =>
    obtain ⟨n, tree, stack, pt, v, hpt, hfail⟩ := hpow input rows q hfit hrel (rate5P Ht) Ft hab ht hπ
    rw [hHt] at hfail
    exact one_le_powPot_of_pcs_none ℓ Ht hpt hfail
  | some π =>
    exfalso
    have hacc' := hacc input rows q hfit hrel (rate5P Ht) Ft π hπ hab ht
    rw [hHt] at hacc' hπ
    have hexp : expW4 (m := Id) Ht (rate5P Ht) Ft D input rows q = true := by
      show verdictW4 (m := Id) Ht (rate5P Ht) Ft D (setupTreeKWithH (m := Id) Ht Ft D) input
        (uniProverRec4With (m := Id) Ht (rate5P Ht) Ft D input rows q) = true
      rw [hπ]
      exact hacc'
    rw [hexp] at hrej
    cases hrej

/-- **π1-rec4's grinding at good challenges**: in leanerVM's two-call random-oracle model the staged run is rejected
while its bus challenges avoid `BadFp` and `t` avoids `BadT` with probability at most `Q · (1 − 2^-17)^(2^25)`, `Q`
its query count. -/
theorem rejectGood4 (hacc : CoreAccepts4 D) (hpow : CoreFailsOnlyAtPow4 D) (input : Vector UInt8 32)
    (rows : List ℕ) (q : D.Stack rows) (hfit : D.shape.RowsFit rows)
    (hrel : D.HonestRelation KeccakFlock.keccakFlockSpec rows input q) {Q : ℕ}
    (hQ : IsTotalQueryBound (stagedU4 D input rows q).run Q) :
    Pr{let z ← (simulateQ ro (stagedU4 D input rows q).run).run' ∅}[
      z.1.1 = false ∧ ¬ BadFp (honestTrace D input rows q) z.2.1 z.2.2 ∧ ¬ BadT D.shape z.1.2.1 z.1.2.2] ≤
      (Q : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel := by
  have hfuel : PcsQuotient.nonceFuel ≤ 2 ^ 64 := by norm_num [PcsQuotient.nonceFuel]
  have hstep : LogFreshStepBound (powPot Whir.queryGrindingBits PcsQuotient.nonceFuel)
      (missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel) := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ x _ ↦ ?_, fun ℓ s hs' ↦ ?_⟩
    · simp only [powPot_append_inl]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · exact powPot_stepF (by decide) (by decide) hfuel ((lookR_eq_none_iff ℓ s).mpr hs')
  have e : Pr{let z ← (simulateQ ro (stagedU4 D input rows q).run).run' ∅}[
      z.1.1 = false ∧ ¬ BadFp (honestTrace D input rows q) z.2.1 z.2.2 ∧ ¬ BadT D.shape z.1.2.1 z.1.2.2] =
      Pr{let z ← (simulateQ loggedRO (stagedU4 D input rows q).run).run []}[
        z.1.1.1 = false ∧ GoodU4 D input rows q z.1] := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_run_randomOracle_eq_loggedRO _
      (fun (z : (Bool × (List E × E)) × (List E × E)) _ ↦ z.1.1 = false ∧ GoodU4 D input rows q z)
  rw [e]
  refine (prEvent_run_loggedRO_le_of_freshStepBound hstep _ Q hQ []
    (fun (z : (Bool × (List E × E)) × (List E × E)) _ ↦ z.1.1 = false ∧ GoodU4 D input rows q z)
    fun z hz hev ↦ ?_).trans ?_
  · have hlook := (simulateQ_look_of_mem_support _ [] z hz).2 z.2 (List.prefix_refl _)
    exact one_le_powPot_of_rejectedU4 D hacc hpow input rows q hfit hrel hlook hev.1 hev.2
  · rw [powPot_nil, zero_add]

/-- **`2^51` queries' grinding** is below `2^-304` (`(3/8)^(2^8)`, as `E2ECompleteness.grinding_le` for `2^48`). -/
theorem grinding_le51 : ((2 ^ 51 : ℕ) : ℝ≥0∞) * missProb Whir.queryGrindingBits ^ PcsQuotient.nonceFuel ≤
    (2 : ℝ≥0∞)⁻¹ ^ 304 := by
  have hb : Whir.queryGrindingBits = 17 := rfl
  have hf : PcsQuotient.nonceFuel = 2 ^ 17 * 2 ^ 8 := by norm_num [PcsQuotient.nonceFuel]
  have hy : (0 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ 17 := by norm_num
  have h38 : (1 - (1 / 2 : ℝ) ^ 17) ^ (2 ^ 17) ≤ 3 / 8 := one_sub_pow_le_three_eighths 17
  have hreal : (2 : ℝ) ^ 51 * ((1 - (1 / 2 : ℝ) ^ 17) ^ (2 ^ 17)) ^ (2 ^ 8) ≤ (1 / 2) ^ 304 := by
    calc (2 : ℝ) ^ 51 * ((1 - (1 / 2 : ℝ) ^ 17) ^ (2 ^ 17)) ^ (2 ^ 8)
        ≤ (2 : ℝ) ^ 51 * (3 / 8) ^ (2 ^ 8) := by gcongr
      _ ≤ ((1 / 2) ^ 152) ^ 2 := by norm_num
      _ = (1 / 2) ^ 304 := by rw [← pow_mul]
  rw [hb, hf, pow_mul, missProb_eq_ofReal, ← ENNReal.ofReal_pow hy,
    ← ENNReal.ofReal_pow (pow_nonneg hy _)]
  calc ((2 ^ 51 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (((1 - (1 / 2 : ℝ) ^ 17) ^ 2 ^ 17) ^ 2 ^ 8)
      = ENNReal.ofReal ((2 : ℝ) ^ 51 * ((1 - (1 / 2 : ℝ) ^ 17) ^ 2 ^ 17) ^ 2 ^ 8) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        norm_num
    _ ≤ ENNReal.ofReal ((1 / 2) ^ 304) := ENNReal.ofReal_le_ofReal hreal
    _ = (2 : ℝ≥0∞)⁻¹ ^ 304 := by
        rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.rejectGood4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.rejectGood4
