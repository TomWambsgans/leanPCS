-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/{Deployed,DeployedWired,Claims}.lean` of this repository
-- (`knowledgeSoundness_deployed`, `knowledgeSoundness_wired`, `knowledgeSoundness_deployed_rust`) to the six PCS
-- openings of the EIP's claims; the fresh-query engine is `Compose/TwoOracle.lean`'s.
import SoundPcs.Claims
import SoundPcs.Opening

/-!
# Knowledge soundness of the deployed verifier of the EIP's PCS claims

**`knowledgeSoundness_deployed_pcs`**: in leanerVM `mumbai`'s two-oracle model (`KeccakCalls`: Keccak-256 and
Keccak-f[1600], independent lazily sampled random oracles), the setup commits to the honest wiring table
(`setupPcs (wiringCol hc σ)`: its Merkle tree, `2^20` queries, and its out-of-domain answer, `24` more); the
adversary, of at most `Q` queries, is given the circuit's commitment and outputs a statement, four commitments,
the values and six opening proofs; the verifier (`dExp`) runs the four-root chain over Keccak-256, the claims of
`PcsQuotient.claimsAt` at `2^22` rows, and the six openings (`pcsOpen`: `pcsVerifierO`, the out-of-domain point
read off Keccak-256). The probability that it accepts while no message the extractor reads off the adversary's
Keccak-256 log (the witness root's Merkle word decoded by the computable `colCode`, each candidate read as its
four row polynomials) is a witness of the statement is at most `deployedBound Q`:

* six opening terms, `openingBound (N₀ + k · 10150)`, `k = 0 … 5`, `N₀ = 2^20 + 24 + Q + 6` (F2's
  `pcs_sound_oracle` for each opening, the run before it as its adversary);
* the binding of `H`'s two openings, `N · δc 27 + N (N + 1) / 2^256`, `N = N₀ + 6 · 10150`
  (`ood_binding_coords` at `27` variables, `δc 27 ≤ 2^-168`);
* the chain, `N (2^-114 + 8 N / 2^256)` (the four certified lists `7908 · 4473 · 3564 · 7908 < 2^50` times F1's
  round error `2^-164`, and the collisions).

At `Q = 2^64` the bound is about `2^-50` (the chain term `2^64 · 2^-114`; each opening term about `2^-64`).
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace SoundPcs

open Compose ComposePcs Compose.Reduce QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol
open LeanVM.Semantics LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open WhirBridge.Pcs PcsBridge

-- The runs are kept folded: no unification evaluates them.
attribute [local irreducible] stage DA4 e1 e2 e3 e4 e5 dExp withSetup4 setupPcs loggedKC

/-- The queries before the openings: the setup's `2^20 + 24`, the adversary's `Q`, the chain's `6`. -/
abbrev N₀ (Q : ℕ) : ℕ := 2 ^ 20 + 24 + Q + 6

/-- All the queries: and the six openings', `10150` each. -/
abbrev Nall (Q : ℕ) : ℕ := N₀ Q + 10150 + 10150 + 10150 + 10150 + 10150 + 10150

/-- **The deployed bound.** -/
noncomputable def deployedBound (Q : ℕ) : ℝ≥0∞ :=
  openingBound (N₀ Q) + openingBound (N₀ Q + 10150) + openingBound (N₀ Q + 10150 + 10150) +
    openingBound (N₀ Q + 10150 + 10150 + 10150) + openingBound (N₀ Q + 10150 + 10150 + 10150 + 10150) +
    openingBound (N₀ Q + 10150 + 10150 + 10150 + 10150 + 10150) +
    (((Nall Q : ℕ) : ℝ≥0∞) * δc 27 + ((Nall Q * (Nall Q + 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256) +
    ((Nall Q : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 114 : ℝ≥0) : ℝ≥0∞) + 8 * ((Nall Q : ℕ) : ℝ≥0∞) / 2 ^ 256)

variable (hc : IsCantor statementConsts.beta) (σ : Equiv.Perm (Fin (22 + 2) → Bool))
  (W : Wire (rustInstance statementConsts hc σ).params (rustInstance statementConsts hc σ).bounds)
  (hdec : ∀ sb, W.decode sb = stmtWords sb) (hτ : RowVanishing statementConsts 22)

/-- **Knowledge soundness of the deployed verifier of the EIP's PCS claims**, in mumbai's two-oracle model, at
`2^22` rows, on F1's instance of `beta()` (`rustInstance`) and the statement's constants. -/
theorem knowledgeSoundness_deployed_pcs
    (A₀ : QuotientRpm.Bytes32 × E → OracleComp KeccakCalls (RootProof4 E × Rest)) (Q : ℕ)
    (hQ : ∀ c, IsTotalQueryBound (A₀ c) Q) :
    Pr{let z ← (simulateQ randomOracle
        (dExp W pcsOpen (withSetup4 (setupPcs (wiringCol hc σ)) A₀))).run' ∅}[
        BreaksD W (claimsMatch hc σ W hdec hτ).cW z] ≤ deployedBound Q := by
  have hA : IsTotalQueryBound (withSetup4 (setupPcs (wiringCol hc σ)) A₀) (2 ^ 20 + 24 + Q) :=
    isTotalQueryBound_withSetup4 _ A₀ _ Q (setupPcs_queryBound _) hQ
  have hpub := membershipPub_hPub (rustInstance statementConsts hc σ).basis
    (invSeq (rustInstance statementConsts hc σ).basis.β) (rustInstance statementConsts hc σ).c le24
    (invSeq_zero _) fun d hd _ => invSeq_sum (rustInstance statementConsts hc σ).basis.β
      (rustInstance statementConsts hc σ).basis.zero d hd
  have hN : (rustInstance statementConsts hc σ).params.nCells = 2 ^ 24 :=
    Params.ofCantor_nCells (rustInstance statementConsts hc σ).basis le24
      (rustInstance statementConsts hc σ).wiring 8 _ _ hpub
  have hd : (rustInstance statementConsts hc σ).bounds.identity ≤ 2 ^ 28 :=
    Params.ofCantor_identity_le_margin (rustInstance statementConsts hc σ).basis le24
      (rustInstance statementConsts hc σ).wiring _ _ hpub
      (natDegree_membershipPub_le (invSeq (rustInstance statementConsts hc σ).basis.β)
        (rustInstance statementConsts hc σ).c)
  have hLW : (claimsMatch hc σ W hdec hτ).K.CW.bound ≤ 7908 := by
    show (colCode 25 adm25 (readW hc σ)).commit.bound ≤ 7908
    rw [colCode_bound]
    exact listHi_parts.1.le
  have hLH : (claimsMatch hc σ W hdec hτ).K.CH.bound ≤ 4473 := by
    show (colCode 27 adm27 id).commit.bound ≤ 4473
    rw [colCode_bound]
    exact listHi_parts.2.1.le
  have hLQ : (claimsMatch hc σ W hdec hτ).K.CQ.bound ≤ 3564 := by
    show (colCode 28 adm28 id).commit.bound ≤ 3564
    rw [colCode_bound]
    exact listHi_parts.2.2.le
  have hLG : (claimsMatch hc σ W hdec hτ).K.CG.bound ≤ 7908 := by
    show (colCode 25 adm25 id).commit.bound ≤ 7908
    rw [colCode_bound]
    exact listHi_parts.1.le
  -- The rest: a bad fresh query.
  have hrest : Pr{let z ← (simulateQ randomOracle
      (dExp W pcsOpen (withSetup4 (setupPcs (wiringCol hc σ)) A₀))).run' ∅}[
      BreaksD W (claimsMatch hc σ W hdec hτ).cW z ∧ ¬ EW pcsOpen z ∧ ¬ Eσ pcsOpen z ∧ ¬ EH pcsOpen z ∧
        ¬ EQ pcsOpen z ∧ ¬ EG pcsOpen z ∧ ¬ ES pcsOpen z ∧ ¬ EB z] ≤
      ((Nall Q : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 114 : ℝ≥0) : ℝ≥0∞) + 8 * ((Nall Q : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
    refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls)
      (dExp W pcsOpen (withSetup4 (setupPcs (wiringCol hc σ)) A₀)) (Nall Q)
      (qb_dExp W pcsOpen _ _ hA)
      (Set.range fun v : QuotientRpm.Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
      (Set.finite_range _) _ (advBad4 W (claimsMatch hc σ W hdec hτ).K
        (withSetup4 (setupPcs (wiringCol hc σ)) A₀)) _ (fun S hS c t ht hcard => ?_)
      (fun T h => trace_dExp W pcsOpen (claimsMatch hc σ W hdec hτ) A₀ T h)
    have hS' : ∀ v : QuotientRpm.Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
      fun v => hS _ ⟨v, rfl⟩
    refine (prob_advBad4 W (claimsMatch hc σ W hdec hτ).K _ S hS' c t ht).trans ?_
    rw [add_comm]
    gcongr
    · exact listError4_le_certified card_E hN rfl hd hLW hLH hLQ hLG
    · have h10 : 10 ≤ Nall Q := by simp only [Nall, N₀]; omega
      have : 7 * (cacheDom c).card + 10 ≤ 8 * Nall Q := by omega
      calc ((7 * (cacheDom c).card + 10 : ℕ) : ℝ≥0∞) ≤ ((8 * Nall Q : ℕ) : ℝ≥0∞) := by
            exact_mod_cast this
        _ = 8 * ((Nall Q : ℕ) : ℝ≥0∞) := by push_cast; ring
  -- The split.
  set mx := (simulateQ randomOracle
    (dExp W pcsOpen (withSetup4 (setupPcs (wiringCol hc σ)) A₀))).run' ∅ with hmx
  have hsplit : ∀ z, BreaksD W (claimsMatch hc σ W hdec hτ).cW z → EW pcsOpen z ∨ Eσ pcsOpen z ∨
      EH pcsOpen z ∨ EQ pcsOpen z ∨ EG pcsOpen z ∨ ES pcsOpen z ∨ EB z ∨
      (BreaksD W (claimsMatch hc σ W hdec hτ).cW z ∧ ¬ EW pcsOpen z ∧ ¬ Eσ pcsOpen z ∧ ¬ EH pcsOpen z ∧
        ¬ EQ pcsOpen z ∧ ¬ EG pcsOpen z ∧ ¬ ES pcsOpen z ∧ ¬ EB z) := by
    intro z hb
    by_cases h1 : EW pcsOpen z
    · exact Or.inl h1
    by_cases h2 : Eσ pcsOpen z
    · exact Or.inr (Or.inl h2)
    by_cases h3 : EH pcsOpen z
    · exact Or.inr (Or.inr (Or.inl h3))
    by_cases h4 : EQ pcsOpen z
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    by_cases h5 : EG pcsOpen z
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    by_cases h6 : ES pcsOpen z
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h6)))))
    by_cases h7 : EB z
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hb, h1, h2, h3, h4, h5, h6, h7⟩))))))
  refine (prEvent_mono mx _ _ hsplit).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  refine (add_le_add (prEvent_EW_le W pcsOpen _ _ hA) ((prEvent_or_le _ _ _).trans
    (add_le_add (prEvent_Eσ_le W pcsOpen _ _ hA) ((prEvent_or_le _ _ _).trans
    (add_le_add (prEvent_EH_le W pcsOpen _ _ hA) ((prEvent_or_le _ _ _).trans
    (add_le_add (prEvent_EQ_le W pcsOpen _ _ hA) ((prEvent_or_le _ _ _).trans
    (add_le_add (prEvent_EG_le W pcsOpen _ _ hA) ((prEvent_or_le _ _ _).trans
    (add_le_add (prEvent_ES_le W pcsOpen _ _ hA) ((prEvent_or_le _ _ _).trans
    (add_le_add (prEvent_EB_le W pcsOpen _ _ hA) hrest))))))))))))).trans (le_of_eq ?_)
  simp only [deployedBound, add_assoc]
  rfl

/-- **The same, the binding's coordinate error at `27` variables bounded** (`δc_27`: `C(4473, 2) / 2^192 ≤
2^-168`). -/
theorem knowledgeSoundness_deployed_pcs_168
    (A₀ : QuotientRpm.Bytes32 × E → OracleComp KeccakCalls (RootProof4 E × Rest)) (Q : ℕ)
    (hQ : ∀ c, IsTotalQueryBound (A₀ c) Q) :
    Pr{let z ← (simulateQ randomOracle
        (dExp W pcsOpen (withSetup4 (setupPcs (wiringCol hc σ)) A₀))).run' ∅}[
        BreaksD W (claimsMatch hc σ W hdec hτ).cW z] ≤
      openingBound (N₀ Q) + openingBound (N₀ Q + 10150) + openingBound (N₀ Q + 10150 + 10150) +
        openingBound (N₀ Q + 10150 + 10150 + 10150) +
        openingBound (N₀ Q + 10150 + 10150 + 10150 + 10150) +
        openingBound (N₀ Q + 10150 + 10150 + 10150 + 10150 + 10150) +
        (((Nall Q : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 168 +
          ((Nall Q * (Nall Q + 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256) +
        ((Nall Q : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 114 : ℝ≥0) : ℝ≥0∞) + 8 * ((Nall Q : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  refine (knowledgeSoundness_deployed_pcs hc σ W hdec hτ A₀ Q hQ).trans ?_
  unfold deployedBound
  gcongr
  exact δc_27

end SoundPcs
