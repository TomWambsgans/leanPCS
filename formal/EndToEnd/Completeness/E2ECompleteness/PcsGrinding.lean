-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from the previous protocol's `E2ECompleteness/Grinding.lean` (itself adapted from leanerVM,
-- https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0,
-- `lean_vm/LeanVM/Protocol/Compile/Rom/Complete.lean`: `one_le_powPot`). Uses, from the same commit: the
-- proof-of-work potential `powPot` and its step (`powPot_stepF`, `powPot_append_inl`), the logged random oracle
-- and its potential engine (`prEvent_run_loggedRO_le_of_freshStepBound`, `prEvent_run_randomOracle_eq_loggedRO`),
-- the bridge from a logged run to the run at the log's answers (`simulateQ_look_of_mem_support`,
-- `simulateQ_id_of_look`).
import E2ECompleteness.Grinding
import E2ECompleteness.PcsOpening
import E2ECompleteness.PcsStaging
import LeanVM.Protocol.Compile.Rom.Complete

/-!
# The grinding at non-degenerate challenges (the PCS claims)

`RejectGood bad 2^-304`: in the two-call random-oracle model the deployed staged run (`stagedRun`) is rejected
while its challenges `(α, β, t, ρ)` avoid `bad` with probability at most `2^-304`. **`rejectGood_of_tail`**, from
the block count (`2^48`) and two facts about the pure run at every hash function `H` and permutation `F`, given
the stages' run there (`StagesAt`):

* **`TailAcceptsG`** (Acc): when the prover's tail returns a proof and the challenges avoid `bad`, the verifier
  accepts it;
* **`TailReducesG`** (Red): when the challenges avoid `bad`, the prover's two reductions return claims.

So a rejected run at non-degenerate challenges had one of its six openings fail at a `17`-bit proof of work
(`proveClaimWithH_eq_some_none`), every nonce below `2^25` failing in the log: mumbai's potential `powPot` of the
log is at least `1`, which happens with probability below `2^48 · (1 − 2^-17)^(2^25) ≤ 2^-304` (`grinding_le`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Rom
open LeanVM.Prover (Tree findNonceM powStepM Script)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript
open E2ECompleteness (runAt grinding_le isTotalQueryBound_of_queryCostAtMost ro)
open scoped ENNReal

set_option autoImplicit false

namespace E2ECompleteness.Pcs

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## Runs at a log (copied from the previous `Grinding.lean`) -/

theorem look_bind {α β : Type} {ℓ : Log} {oa : OracleComp KeccakCalls α}
    {f : α → OracleComp KeccakCalls β} {b : β}
    (h : simulateQ (lookImpl ℓ) (oa >>= f) = some b) :
    ∃ a, simulateQ (lookImpl ℓ) oa = some a ∧ simulateQ (lookImpl ℓ) (f a) = some b := by
  rw [simulateQ_bind] at h
  exact Option.bind_eq_some_iff.mp h

theorem look_pure {α : Type} {ℓ : Log} {a b : α}
    (h : simulateQ (lookImpl ℓ) (pure a : OracleComp KeccakCalls α) = some b) : a = b := by
  rw [simulateQ_pure] at h
  exact Option.some.inj h

theorem look_callKeccak256 {ℓ : Log} {x : Bytes} {u : Digest}
    (h : simulateQ (lookImpl ℓ) (callKeccak256 x) = some u) : lookH ℓ x = some u := by
  rw [simulateQ_queryH] at h
  exact h


/-! ## A failed search puts the potential at one -/

/-- **A failed proof-of-work search in the log** puts the potential at least at `1` (the end of
mumbai's `one_le_powPot`): every nonce below `fuel` at the search's position is in the log, and
fails. -/
theorem one_le_powPot_of_findNonceM {ℓ : Log} {bits fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64)
    (hfuel0 : fuel ≠ 0) {sp : Sponge} (hsp : ProverSp sp)
    (hf : findNonceM (lookF ℓ) bits sp fuel = some none) : 1 ≤ powPot bits fuel ℓ := by
  obtain ⟨-, hall⟩ := findNonceM_eq_some_none hf
  -- The position of the search, the same for every nonce.
  obtain ⟨κ, hκ, hnon⟩ : ∃ κ : PowKey, KeyOk κ ∧ ∀ n < fuel, ∃ u,
      lookF ℓ (nonceInput κ.1 κ.2 n) = some u ∧ powOk bits (nonceOf n) (challengeOf u) = false := by
    by_cases h4 : sp.pending.length = 4
    · obtain ⟨r0, hr0, -⟩ := hall 0 (Nat.pos_of_ne_zero hfuel0)
      obtain ⟨c0, ps0, u0, -, -, hif⟩ := powStepM_option hr0
      simp only [h4, ↓reduceIte] at hif
      obtain ⟨-, v, hv, -⟩ := hif
      refine ⟨(capOf v, []), ⟨by simp, by simp⟩, fun n hn ↦ ?_⟩
      obtain ⟨r, hr, hp⟩ := hall n hn
      obtain ⟨c, ps, u, hu, hru, hif⟩ := powStepM_option hr
      simp only [h4, ↓reduceIte] at hif
      obtain ⟨rfl, v', hv', rfl⟩ := hif
      rw [hv] at hv'
      cases hv'
      exact ⟨u, hu, by rw [← hru]; exact hp⟩
    · refine ⟨(capOf sp.state, sp.pending), ⟨by dsimp only; have := hsp.1; omega, hsp.2⟩,
        fun n hn ↦ ?_⟩
      obtain ⟨r, hr, hp⟩ := hall n hn
      obtain ⟨c, ps, u, hu, hru, hif⟩ := powStepM_option hr
      simp only [h4, ↓reduceIte] at hif
      obtain ⟨rfl, rfl⟩ := hif
      exact ⟨u, hu, by rw [← hru]; exact hp⟩
  -- Its term is `1`.
  have hS : ¬ Solved bits fuel ℓ κ := by
    rintro ⟨n, hn, d, hd, hp⟩
    obtain ⟨d', hd', hp'⟩ := hnon n hn
    rw [hd'] at hd
    cases hd
    rw [hp'] at hp
    cases hp
  have hT : (tried fuel ℓ κ).card = fuel := by
    have : tried fuel ℓ κ = Finset.range fuel := by
      refine Finset.filter_true_of_mem fun n hn ↦ ?_
      obtain ⟨d, hd, -⟩ := hnon n (Finset.mem_range.mp hn)
      simp [hd]
    rw [this, Finset.card_range]
  have hterm : powTerm bits fuel ℓ κ = 1 := by
    simp [powTerm, hS, hT]
  have hmem : κ ∈ keys fuel ℓ := by
    obtain ⟨u, hu, -⟩ := hnon 0 (Nat.pos_of_ne_zero hfuel0)
    obtain ⟨i, hi, hei, -⟩ := (lookF_eq_some_iff ℓ _ u).mp hu
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨_, mem_fIns_of_getElem hi hei,
      keyOf_nonceInput hfuel hκ (Nat.pos_of_ne_zero hfuel0)⟩)
  rw [← hterm]
  exact Finset.single_le_sum (fun _ _ ↦ bot_le) hmem

/-- **A failed opening in the log** puts the potential at least at `1`. -/
theorem one_le_powPot_of_proveClaim {ℓ : Log} {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64)
    (hfuel0 : fuel ≠ 0) {tree : Tree} {table : Array K} {c : Commitment} {claim : Claim}
    (h : simulateQ (lookImpl ℓ) (proveClaimWithH callKeccak256 callKeccakF1600 fuel tree table c
      claim) = some none) :
    1 ≤ powPot Whir.queryGrindingBits fuel ℓ := by
  rw [simulateQ_proveClaimWithH] at h
  obtain ⟨sp, hsp, hf⟩ := proveClaimWithH_eq_some_none h
  exact one_le_powPot_of_findNonceM hfuel hfuel0 hsp hf

/-! ## The staged run -/

section Generic

variable (setup : OracleComp KeccakCalls (Tree × Commitment)) (circuit : Circuit) (cells₀ : Array K)
  (coins : Coins) (fuel vLogRows : ℕ) (stmt : Statement)

/-- **The stages at a hash function and a permutation.** -/
structure StagesAt (H : Bytes → Digest) (F : KeccakState → KeccakState)
    (x : AuxA × Digest × CommitmentScalars) (s₁ s₂ s₃ : Digest) (y : AuxB × Scalars9) (s₄ : Digest)
    (z : AuxC × Digest × (Vector E 4 × E)) (s₅ : Digest) : Prop where
  hA : runAt H F (stageAG setup circuit cells₀ coins stmt) = x
  h₁ : H (in3 x.2.1 x.2.2) = s₁
  h₂ : H (digestBytes s₁) = s₂
  h₃ : H (digestBytes s₂) = s₃
  hB : runAt H F (stageBG circuit cells₀ coins x.1 s₁ s₂ s₃) = y
  h₄ : H (in9 s₃ y.2) = s₄
  hC : runAt H F (stageCG circuit cells₀ coins stmt x.1 y.1 s₁ s₂ s₃ s₄) = z
  h₅ : H (in5 z.2.1 z.2.2) = s₅

/-- **(Acc)**: at every hash function and permutation, when the prover's tail returns a proof and the
challenges avoid `bad`, the verifier accepts it. -/
def TailAcceptsG (bad : Finset (E × E × E × E)) : Prop :=
  ∀ (H : Bytes → Digest) (F : KeccakState → KeccakState) x s₁ s₂ s₃ y s₄ z s₅,
    StagesAt setup circuit cells₀ coins stmt H F x s₁ s₂ s₃ y s₄ z s₅ →
    (challengeOf s₁, challengeOf s₂, challengeOf s₄, challengeOf s₅) ∉ bad →
    ∀ π : PcsQuotient.Proof,
      runAt H F (proverTailG circuit cells₀ coins fuel stmt x.1 y.1 z.1 s₁ s₂ s₃ s₄ s₅) = some π →
      runAt H F (verifyWithH callKeccak256 callKeccakF1600 vLogRows x.1.1 stmt π) = true

/-- **(Red)**: at every hash function and permutation, when the challenges avoid `bad`, the prover's first
claims exist and its second reduction returns claims. -/
def TailReducesG (bad : Finset (E × E × E × E)) : Prop :=
  ∀ (H : Bytes → Digest) (F : KeccakState → KeccakState) x s₁ s₂ s₃ y s₄ z s₅,
    StagesAt setup circuit cells₀ coins stmt H F x s₁ s₂ s₃ y s₄ z s₅ →
    (challengeOf s₁, challengeOf s₂, challengeOf s₄, challengeOf s₅) ∉ bad →
    ∃ r₀, claims₀Of circuit cells₀ coins stmt x.1 y.1 z.1 s₄ s₅ = some r₀ ∧
      runAt H F (reduceWithH callKeccak256 circuit.logRows x.1.2.2.1 stmt
        { proof₀Of circuit cells₀ coins x.1 y.1 s₄ with
          qValue := tableEval (tablesAt circuit cells₀ coins s₁ s₂ s₃).2.1 r₀.claims.q.point,
          gValue := tableEval (tablesAt circuit cells₀ coins s₁ s₂ s₃).2.2 r₀.claims.g.point }) ≠ none

/-- **The prover's tail fails only at an opening**, when its claims and its second reduction exist. -/
theorem opening_fails_of_proverTailG {ℓ : Log} (a : AuxA) (b : AuxB) (c : AuxC)
    (s₁ s₂ s₃ s₄ s₅ : Digest)
    (h : simulateQ (lookImpl ℓ) (proverTailG circuit cells₀ coins fuel stmt a b c s₁ s₂ s₃ s₄ s₅) =
      some none)
    (r₀ : Reduced) (hr₀ : claims₀Of circuit cells₀ coins stmt a b c s₄ s₅ = some r₀)
    (hred : simulateQ (lookImpl ℓ) (reduceWithH callKeccak256 circuit.logRows a.2.2.1 stmt
        { proof₀Of circuit cells₀ coins a b s₄ with
          qValue := tableEval (tablesAt circuit cells₀ coins s₁ s₂ s₃).2.1 r₀.claims.q.point,
          gValue := tableEval (tablesAt circuit cells₀ coins s₁ s₂ s₃).2.2 r₀.claims.g.point }) ≠
      some none) :
    ∃ (tree : Tree) (table : Array K) (cm : Commitment) (claim : Claim),
      simulateQ (lookImpl ℓ) (proveClaimWithH callKeccak256 callKeccakF1600 fuel tree table cm
        claim) = some none := by
  unfold proverTailG at h
  rw [hr₀] at h
  obtain ⟨red, hr, h⟩ := look_bind h
  rcases red with _ | r
  · exact absurd hr hred
  obtain ⟨o₁, h₁, h⟩ := look_bind h
  rcases o₁ with _ | p₁
  · exact ⟨_, _, _, _, h₁⟩
  obtain ⟨o₂, h₂, h⟩ := look_bind h
  rcases o₂ with _ | p₂
  · exact ⟨_, _, _, _, h₂⟩
  obtain ⟨o₃, h₃, h⟩ := look_bind h
  rcases o₃ with _ | p₃
  · exact ⟨_, _, _, _, h₃⟩
  obtain ⟨o₄, h₄, h⟩ := look_bind h
  rcases o₄ with _ | p₄
  · exact ⟨_, _, _, _, h₄⟩
  obtain ⟨o₅, h₅, h⟩ := look_bind h
  rcases o₅ with _ | p₅
  · exact ⟨_, _, _, _, h₅⟩
  obtain ⟨o₆, h₆, h⟩ := look_bind h
  rcases o₆ with _ | p₆
  · exact ⟨_, _, _, _, h₆⟩
  cases look_pure h

/-- **A run rejected at non-degenerate challenges puts the potential at one.** -/
theorem one_le_powPot_of_rejected {bad : Finset (E × E × E × E)} (hfuel : fuel ≤ 2 ^ 64)
    (hfuel0 : fuel ≠ 0)
    (hacc : TailAcceptsG setup circuit cells₀ coins fuel vLogRows stmt bad)
    (hred : TailReducesG setup circuit cells₀ coins stmt bad)
    {ℓ : Log} {zz : Bool × (E × E × E × E)}
    (hz : simulateQ (lookImpl ℓ)
      (stagedRunG setup circuit cells₀ coins fuel vLogRows stmt) = some zz)
    (hrej : zz.1 = false) (hgood : zz.2 ∉ bad) :
    1 ≤ powPot Whir.queryGrindingBits fuel ℓ := by
  let Ht : Bytes → Digest := fun x ↦ (lookH ℓ x).getD default
  let Ft : KeccakState → KeccakState := fun s ↦ (lookF ℓ s).getD default
  have hH : ∀ x u, lookH ℓ x = some u → Ht x = u := fun x u hx ↦ by simp [Ht, hx]
  have hF : ∀ s u, lookF ℓ s = some u → Ft s = u := fun s u hs ↦ by simp [Ft, hs]
  have hid : ∀ {β : Type} (oa : OracleComp KeccakCalls β) (r : β),
      simulateQ (lookImpl ℓ) oa = some r → runAt Ht Ft oa = r :=
    fun oa r h ↦ simulateQ_id_of_look ℓ Ht Ft hH hF oa r h
  unfold stagedRunG staged4 at hz
  obtain ⟨x, hx, hz⟩ := look_bind hz
  obtain ⟨s₁, hs₁, hz⟩ := look_bind hz
  obtain ⟨s₂, hs₂, hz⟩ := look_bind hz
  obtain ⟨s₃, hs₃, hz⟩ := look_bind hz
  obtain ⟨y, hy, hz⟩ := look_bind hz
  obtain ⟨s₄, hs₄, hz⟩ := look_bind hz
  obtain ⟨z, hzz, hz⟩ := look_bind hz
  obtain ⟨s₅, hs₅, hz⟩ := look_bind hz
  obtain ⟨v, hv, hz⟩ := look_bind hz
  obtain rfl := look_pure hz
  have hst : StagesAt setup circuit cells₀ coins stmt Ht Ft x s₁ s₂ s₃ y s₄ z s₅ :=
    ⟨hid _ _ hx, hH _ _ (look_callKeccak256 hs₁), hH _ _ (look_callKeccak256 hs₂),
      hH _ _ (look_callKeccak256 hs₃), hid _ _ hy, hH _ _ (look_callKeccak256 hs₄), hid _ _ hzz,
      hH _ _ (look_callKeccak256 hs₅)⟩
  unfold stageDG at hv
  obtain ⟨o, ho, hv⟩ := look_bind hv
  rcases o with _ | π
  · obtain ⟨r₀, hr₀, hr⟩ := hred Ht Ft x s₁ s₂ s₃ y s₄ z s₅ hst hgood
    obtain ⟨tree, table, cm, claim, hfail⟩ :=
      opening_fails_of_proverTailG circuit cells₀ coins fuel stmt x.1 y.1 z.1 _ _ _ _ _ ho r₀ hr₀
        fun h ↦ hr (hid _ _ h)
    exact one_le_powPot_of_proveClaim hfuel hfuel0 hfail
  · exfalso
    have hver := hid _ _ hv
    have hacc' := hacc Ht Ft x s₁ s₂ s₃ y s₄ z s₅ hst hgood π (hid _ _ ho)
    have hvt : v = true := hver.symm.trans hacc'
    simp only at hrej
    rw [hvt] at hrej
    cases hrej

end Generic

/-! ## The deployed instance -/

/-- **The grinding at non-degenerate challenges**, for degenerate sets `bad`. -/
def RejectGood (bad : Secret → Coins → Finset (E × E × E × E)) (εpow : ℝ≥0∞) : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w → ∀ c : Coins,
    Pr{let z ← (simulateQ ro (stagedRun stmt w c)).run' ∅}[z.1 = false ∧ z.2 ∉ bad w c] ≤ εpow

/-- **`RejectGood bad 2^-304`**, from the block count `2^48` of the deployed staged run, (Acc) and (Red). -/
theorem rejectGood_of_tail (bad : Secret → Coins → Finset (E × E × E × E))
    (hcost : ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) hashBlocks (2 ^ 48))
    (hacc : ∀ stmt w, Relation stmt w → ∀ coins, TailAcceptsG (setupWithH callKeccak256)
      (membership logRows) (cellsOf w) coins nonceFuel logRows stmt (bad w coins))
    (hred : ∀ stmt w, Relation stmt w → ∀ coins, TailReducesG (setupWithH callKeccak256)
      (membership logRows) (cellsOf w) coins stmt (bad w coins)) :
    RejectGood bad ((2 : ℝ≥0∞)⁻¹ ^ 304) := by
  intro stmt w hrel c
  have hfuel : nonceFuel ≤ 2 ^ 64 := by norm_num [nonceFuel]
  have hfuel0 : nonceFuel ≠ 0 := by norm_num [nonceFuel]
  have hstep : LogFreshStepBound (powPot Whir.queryGrindingBits nonceFuel)
      (missProb Whir.queryGrindingBits ^ nonceFuel) := by
    rw [logFreshStepBound_iff]
    refine ⟨fun ℓ x _ ↦ ?_, fun ℓ s hs' ↦ ?_⟩
    · simp only [powPot_append_inl]
      exact (avg_le_of_le fun _ ↦ le_rfl).trans le_self_add
    · exact powPot_stepF (by decide) (by decide) hfuel ((lookR_eq_none_iff ℓ s).mpr hs')
  have e : Pr{let z ← (simulateQ ro (stagedRun stmt w c)).run' ∅}[z.1 = false ∧ z.2 ∉ bad w c] =
      Pr{let z ← (simulateQ loggedRO (stagedRun stmt w c)).run []}[
        z.1.1 = false ∧ z.1.2 ∉ bad w c] := by
    rw [StateT.run'_eq, prEvent_map]
    exact prEvent_run_randomOracle_eq_loggedRO _
      (fun (z : Bool × (E × E × E × E)) _ ↦ z.1 = false ∧ z.2 ∉ bad w c)
  rw [e]
  refine (prEvent_run_loggedRO_le_of_freshStepBound hstep _ (2 ^ 48)
    (isTotalQueryBound_of_queryCostAtMost (hcost stmt w c)) []
    (fun (z : Bool × (E × E × E × E)) _ ↦ z.1 = false ∧ z.2 ∉ bad w c)
    fun z hz hev ↦ ?_).trans ?_
  · have hlook := (simulateQ_look_of_mem_support _ [] z hz).2 z.2 (List.prefix_refl _)
    exact one_le_powPot_of_rejected _ _ _ _ _ _ _ hfuel hfuel0 (hacc stmt w hrel c)
      (hred stmt w hrel c) hlook hev.1 hev.2
  · rw [powPot_nil, zero_add]
    exact grinding_le

end E2ECompleteness.Pcs
