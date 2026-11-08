-- Part of this repository. MIT OR Apache-2.0; see NOTICE.md. `formal/UniComplete`'s `UniComplete/ProbStaged.lean`
-- (`UniStaged`, `UniStaged.Holds`, `prEvent_run_false_le`, `uniCompleteness_of_staged`) at the Keccak verifier's
-- completeness experiment (`UniKeccak.keccakCompletenessExperiment`); it follows
-- `formal/EndToEnd/Completeness/E2ECompleteness/End.lean` and uses its `rpm_le_rom` (`Transfer.lean`) and leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the two calls
-- and their random-permutation model, `rpmError`, the duplex discipline `DuplexVm` and the block cost `hashBlocks`.
import UniKeccakComplete.Chain
import E2ECompleteness.Transfer
import UniKeccak.Security

/-!
# `UniCompletenessKeccakWith`, from the staged two-call experiment

The Keccak verifier's completeness experiment (`keccakCompletenessExperiment D v P`: the setup, the prover `P`, the
Keccak verifier of variant `v`, all over one random permutation `π`) has the univariate verifier's shape: the bus
challenges `α₁ … α₄, β` are five chained Keccak-256 answers right after `C1`'s root (the first input `88` bytes: the
state, the six row counts, the root word), then Flock's point, then the point challenge `t`. **What is proved here**
(`uniCompletenessKeccak_of_staged`): if for every honest witness the experiment is the verdict of a two-call
computation of this shape (`KStaged`, `KStaged.Holds`), then

  `δ = Nbad / 2^192 + 6 / 2^256 + (ct / 2^192 + εt) + εpow + N² / 2^508`,

the four terms of `UniComplete`'s bound: the bus challenges bad (`Nbad` bad `β` per `α`), `t` bad (`ct` per prior)
or its query not fresh (`εt`), the grinding (`εpow`), and the transfer from the random permutation to two random
oracles over `N` block calls (`E2ECompleteness.rpm_le_rom`). The proof is `UniComplete`'s, whose probability lemmas
(`Chain.lean`) are instruction-set independent; only the experiment `Holds.experiment` equates is the Keccak
verifier's.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open UniStatement UniKeccak
open E2ECompleteness (ro HashOK)
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Prob

/-- **The experiment's stages** (no coins): `A` up to the first bus-challenge input (`inp`, `88` bytes), the five
chained answers, `B` up to `t`'s input (`tin`; `pr` the prior `t`'s bad set depends on, Flock's point), `t`'s answer,
`C` the rest (the prover's tail and the verifier), its output the verdict. -/
structure KStaged where
  α : Type
  β : Type
  inp : α → Bytes
  A : OracleComp KeccakCalls α
  B : α → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls β
  tin : β → Bytes
  pr : β → List E
  C : β → Digest → OracleComp KeccakCalls Bool

/-- After the bus challenges: `B`, `t`'s query, `C`; the verdict and `(pr b, t)`. -/
def KStaged.tail (S : KStaged) (a : S.α) (s₁ s₂ s₃ s₄ s₅ : Digest) :
    OracleComp KeccakCalls (Bool × (List E × E)) := do
  let b ← S.B a s₁ s₂ s₃ s₄ s₅
  let st ← callKeccak256 (S.tin b)
  let z ← S.C b st
  return (z, (S.pr b, PcsQuotient.Transcript.challengeOf st))

/-- The two-call run: the verdict with `t`'s stage, and the bus challenges `(α, β)`. -/
def KStaged.run (S : KStaged) : OracleComp KeccakCalls ((Bool × (List E × E)) × (List E × E)) :=
  staged5 PcsQuotient.Transcript.challengeOf S.inp S.A S.tail

/-- **The run up to `t`'s query**: `B`'s output and the bus challenges. -/
def KStaged.pre (S : KStaged) : OracleComp KeccakCalls (S.β × (List E × E)) := do
  let a ← S.A
  let s₁ ← callKeccak256 (S.inp a)
  let s₂ ← callKeccak256 (digestBytes s₁)
  let s₃ ← callKeccak256 (digestBytes s₂)
  let s₄ ← callKeccak256 (digestBytes s₃)
  let s₅ ← callKeccak256 (digestBytes s₄)
  let b ← S.B a s₁ s₂ s₃ s₄ s₅
  return (b, ([PcsQuotient.Transcript.challengeOf s₁, PcsQuotient.Transcript.challengeOf s₂,
    PcsQuotient.Transcript.challengeOf s₃, PcsQuotient.Transcript.challengeOf s₄],
    PcsQuotient.Transcript.challengeOf s₅))

/-- **The run, cut at `t`.** -/
theorem KStaged.run_eq_pre (S : KStaged) :
    S.run = S.pre >>= fun x ↦ callKeccak256 (S.tin x.1) >>= fun st ↦ S.C x.1 st >>= fun z ↦
      pure ((z, (S.pr x.1, PcsQuotient.Transcript.challengeOf st)), x.2) := by
  simp only [KStaged.run, staged5, KStaged.tail, KStaged.pre, bind_assoc, pure_bind]

/-- **The probability conditions** of a staged run: bad sets `bad` (bus challenges, at most `Nbad` values of `β` per
`α`) and `badT` (`t`, at most `ct` values per prior), `N` block calls, `t`'s cache-hit probability `εt` and a
proof-of-work error `εpow`. -/
structure KStaged.Good (S : KStaged) (bad badT : List E → E → Prop) (Nbad ct N : ℕ) (εt εpow : ℝ≥0∞) :
    Prop where
  /-- Every permutation call continues a duplex or starts one (`DuplexVm`). -/
  duplex : DuplexVm S.run []
  /-- At most `N` block calls (`hashBlocks`). -/
  cost : Common.QueryCostAtMost S.run hashBlocks N
  /-- The first bus-challenge input has `88` bytes. -/
  inp_length : ∀ a, (S.inp a).length = 88
  /-- Before it, nothing of the chain's lengths (`32`, `88`) is hashed. -/
  hashA : HashOK (GoodL 88) S.A
  /-- At most `Nbad` bad values of `β` for each `α`. -/
  badCard : ∀ alphas, ∃ T : Finset E, T.card ≤ Nbad ∧ ∀ b, bad alphas b → b ∈ T
  /-- At most `ct` bad values of `t` for each prior. -/
  badTCard : ∀ fp, ∃ T : Finset E, T.card ≤ ct ∧ ∀ t, badT fp t → t ∈ T
  /-- `t`'s input is already hashed before its query with probability at most `εt`. -/
  tFresh : Pr{let p ← (simulateQ ro S.pre).run ∅}[p.2 (.inl (S.tin p.1.1)) ≠ none] ≤ εt
  /-- **Grinding**: in the two-call random-oracle model the honest proof is rejected at good challenges with
  probability at most `εpow`. -/
  rejectGood : Pr{let z ← (simulateQ ro S.run).run' ∅}[
    z.1.1 = false ∧ ¬ bad z.2.1 z.2.2 ∧ ¬ badT z.1.2.1 z.1.2.2] ≤ εpow

/-- **The code-level bridge** of the Keccak experiment of variant `v` for `(input, rows, q)`: the experiment is the
verdict of the staged run against the random permutation, and the run's probability conditions hold. -/
structure KStaged.Holds (S : KStaged) (D : KDeployment) (v : KeccakVariant) (P : KProver D)
    (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows) (bad badT : List E → E → Prop) (Nbad ct N : ℕ)
    (εt εpow : ℝ≥0∞) : Prop where
  /-- The experiment is the verdict of the two-call run against the random permutation. -/
  experiment : keccakCompletenessExperiment D v P input rows q =
    (fun z ↦ z.1.1) <$> (simulateQ keccakCallsOverRandomPermutation S.run).run' []
  /-- The run's probability conditions. -/
  good : S.Good bad badT Nbad ct N εt εpow

/-- **One staged run**: it is rejected with probability at most the bus challenges' `Nbad / 2^192 + 6 / 2^256`,
`t`'s `ct / 2^192 + εt`, `εpow` and the transfer's `rpmError N`. -/
theorem prEvent_run_false_le (S : KStaged) {bad badT : List E → E → Prop} {Nbad ct N : ℕ} {εt εpow : ℝ≥0∞}
    (h : S.Good bad badT Nbad ct N εt εpow) :
    Pr{let z ← (simulateQ keccakCallsOverRandomPermutation S.run).run' []}[z.1.1 = false] ≤
      ((Nbad : ℝ≥0∞) / 2 ^ 192 + 6 / 2 ^ 256 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) + εpow) + rpmError N := by
  refine E2ECompleteness.rpm_le_rom S.run h.duplex h.cost (fun z ↦ z.1.1 = false) ?_
  have hab : Pr{let z ← (simulateQ ro S.run).run' ∅}[bad z.2.1 z.2.2] ≤
      6 / 2 ^ 256 + (Nbad : ℝ≥0∞) / 2 ^ 192 := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_staged5_le _ E2ECompleteness.challengeOf_regular (by norm_num) bad Nbad h.badCard S.inp
      h.inp_length S.A S.tail h.hashA ∅ fun m hm ↦ absurd rfl hm
  have ht : Pr{let z ← (simulateQ ro S.run).run' ∅}[badT z.1.2.1 z.1.2.2] ≤
      εt + (ct : ℝ≥0∞) / 2 ^ 192 := by
    rw [StateT.run'_eq, prEvent_map, S.run_eq_pre]
    refine (prEvent_tquery_le _ E2ECompleteness.challengeOf_regular badT ct h.badTCard S.pre
      (fun x ↦ S.tin x.1) (fun x ↦ S.pr x.1) (fun x st ↦ S.C x.1 st)
      (fun x st z ↦ ((z, (S.pr x.1, PcsQuotient.Transcript.challengeOf st)), x.2))
      (fun w ↦ badT w.1.2.1 w.1.2.2) (fun _ _ _ hw ↦ hw) ∅).trans ?_
    exact add_le_add h.tFresh le_rfl
  have hsplit : Pr{let z ← (simulateQ ro S.run).run' ∅}[z.1.1 = false] ≤
      Pr{let z ← (simulateQ ro S.run).run' ∅}[bad z.2.1 z.2.2] +
        (Pr{let z ← (simulateQ ro S.run).run' ∅}[badT z.1.2.1 z.1.2.2] +
          Pr{let z ← (simulateQ ro S.run).run' ∅}[
            z.1.1 = false ∧ ¬ bad z.2.1 z.2.2 ∧ ¬ badT z.1.2.1 z.1.2.2]) := by
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _ (fun z : (Bool × (List E × E)) × (List E × E) ↦
      bad z.2.1 z.2.2)).trans (add_le_add le_rfl ?_)
    refine (prEvent_le_prEvent_add_prEvent_and_not _ _ (fun z : (Bool × (List E × E)) × (List E × E) ↦
      badT z.1.2.1 z.1.2.2)).trans (add_le_add le_rfl (le_of_eq ?_))
    simp only [and_assoc]
  refine hsplit.trans ?_
  calc _ ≤ (6 / 2 ^ 256 + (Nbad : ℝ≥0∞) / 2 ^ 192) + ((εt + (ct : ℝ≥0∞) / 2 ^ 192) + εpow) :=
        add_le_add hab (add_le_add ht h.rejectGood)
    _ = (Nbad : ℝ≥0∞) / 2 ^ 192 + 6 / 2 ^ 256 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) + εpow := by
        rw [add_comm (6 / 2 ^ 256 : ℝ≥0∞), add_comm εt]
        ac_rfl

/-- **The staged premise**: for every honest witness (row counts fitting the shape, a `KvHonest F` stack), the
Keccak experiment of variant `v` is a staged run with these probability conditions. -/
def KStagedHolds (F : KeccakVm.KeccakFlockSpec) (D : KDeployment) (v : KeccakVariant) (P : KProver D)
    (Nbad ct N : ℕ) (εt εpow : ℝ≥0∞) : Prop :=
  ∀ (input : Vector UInt8 32) (rows : List ℕ) (q : D.Stack rows), D.shape.RowsFit rows →
    D.HonestRelation F rows input q →
    ∃ (S : KStaged) (bad badT : List E → E → Prop), S.Holds D v P input rows q bad badT Nbad ct N εt εpow

/-- **`UniCompletenessKeccakWith` in the random-permutation model, from the staged experiment.** -/
theorem uniCompletenessKeccak_of_staged {F : KeccakVm.KeccakFlockSpec} {D : KDeployment} {v : KeccakVariant}
    {P : KProver D} {Nbad ct N : ℕ} {εt εpow : ℝ≥0∞} (hS : KStagedHolds F D v P Nbad ct N εt εpow) :
    UniCompletenessKeccakWith F D v P
      ((Nbad : ℝ≥0∞) / 2 ^ 192 + 6 / 2 ^ 256 + ((ct : ℝ≥0∞) / 2 ^ 192 + εt) + εpow + rpmError N) := by
  intro input rows q hfit hrel
  obtain ⟨S, bad, badT, h⟩ := hS input rows q hfit hrel
  rw [h.experiment, prEvent_map]
  exact prEvent_run_false_le S h.good

end UniKeccakComplete.Prob
