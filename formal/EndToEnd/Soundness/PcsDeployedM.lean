-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- `formal/SoundPcs/SoundPcs/Final.lean`'s `knowledgeSoundness_deployed_pcs` of this repository, its proof unchanged,
-- stated for any committed wiring table `q₀` and any `ClaimsMatch` of it (there: the honest table `wiringCol`, chosen
-- by `exists_table`, and its `claimsMatch`).
import SoundPcs

/-!
# The deployed composition, for any committed wiring table

`SoundPcs.knowledgeSoundness_deployed_pcs` is stated for the honest wiring table `wiringCol hc σ` (a table chosen to
carry `σ`) and its `claimsMatch`; its proof reads them only through `ClaimsMatch` (`trace_dExp` is generic in the
table and the match). **`knowledgeSoundness_deployed_pcsM`** is the same theorem for any table `q₀` and any
`M : ClaimsMatch W q₀`: the end theorem commits the Statement's own wiring table.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace SoundPcs

open Compose ComposePcs Compose.Reduce QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol
open LeanVM.Semantics LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open WhirBridge.Pcs PcsBridge

attribute [local irreducible] stage DA4 e1 e2 e3 e4 e5 dExp withSetup4 setupPcs loggedKC

variable (hc : IsCantor statementConsts.beta) (σ : Equiv.Perm (Fin (22 + 2) → Bool))
  (W : Wire (rustInstance statementConsts hc σ).params (rustInstance statementConsts hc σ).bounds)
  (q₀ : Column 24) (M : ClaimsMatch W q₀)

/-- **Knowledge soundness of the deployed verifier of the EIP's PCS claims**, for any committed wiring table and
any match of the claims (`SoundPcs.knowledgeSoundness_deployed_pcs`'s proof). -/
theorem knowledgeSoundness_deployed_pcsM
    (A₀ : QuotientRpm.Bytes32 × E → OracleComp KeccakCalls (RootProof4 E × Rest)) (Q : ℕ)
    (hQ : ∀ c, IsTotalQueryBound (A₀ c) Q) :
    Pr{let z ← (simulateQ randomOracle
        (dExp W pcsOpen (withSetup4 (setupPcs q₀) A₀))).run' ∅}[
        BreaksD W M.cW z] ≤ deployedBound Q := by
  have hA : IsTotalQueryBound (withSetup4 (setupPcs q₀) A₀) (2 ^ 20 + 24 + Q) :=
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
  have hLW : M.K.CW.bound ≤ 7908 := by
    show (colCode 25 adm25 M.readW).commit.bound ≤ 7908
    rw [colCode_bound]
    exact listHi_parts.1.le
  have hLH : M.K.CH.bound ≤ 4473 := by
    show (colCode 27 adm27 id).commit.bound ≤ 4473
    rw [colCode_bound]
    exact listHi_parts.2.1.le
  have hLQ : M.K.CQ.bound ≤ 3564 := by
    show (colCode 28 adm28 id).commit.bound ≤ 3564
    rw [colCode_bound]
    exact listHi_parts.2.2.le
  have hLG : M.K.CG.bound ≤ 7908 := by
    show (colCode 25 adm25 id).commit.bound ≤ 7908
    rw [colCode_bound]
    exact listHi_parts.1.le
  -- The rest: a bad fresh query.
  have hrest : Pr{let z ← (simulateQ randomOracle
      (dExp W pcsOpen (withSetup4 (setupPcs q₀) A₀))).run' ∅}[
      BreaksD W M.cW z ∧ ¬ EW pcsOpen z ∧ ¬ Eσ pcsOpen z ∧ ¬ EH pcsOpen z ∧
        ¬ EQ pcsOpen z ∧ ¬ EG pcsOpen z ∧ ¬ ES pcsOpen z ∧ ¬ EB z] ≤
      ((Nall Q : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 114 : ℝ≥0) : ℝ≥0∞) + 8 * ((Nall Q : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
    refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls)
      (dExp W pcsOpen (withSetup4 (setupPcs q₀) A₀)) (Nall Q)
      (qb_dExp W pcsOpen _ _ hA)
      (Set.range fun v : QuotientRpm.Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState))
      (Set.finite_range _) _ (advBad4 W M.K
        (withSetup4 (setupPcs q₀) A₀)) _ (fun S hS c t ht hcard => ?_)
      (fun T h => trace_dExp W pcsOpen M A₀ T h)
    have hS' : ∀ v : QuotientRpm.Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
      fun v => hS _ ⟨v, rfl⟩
    refine (prob_advBad4 W M.K _ S hS' c t ht).trans ?_
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
    (dExp W pcsOpen (withSetup4 (setupPcs q₀) A₀))).run' ∅ with hmx
  have hsplit : ∀ z, BreaksD W M.cW z → EW pcsOpen z ∨ Eσ pcsOpen z ∨
      EH pcsOpen z ∨ EQ pcsOpen z ∨ EG pcsOpen z ∨ ES pcsOpen z ∨ EB z ∨
      (BreaksD W M.cW z ∧ ¬ EW pcsOpen z ∧ ¬ Eσ pcsOpen z ∧ ¬ EH pcsOpen z ∧
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


end SoundPcs

/-- info: 'SoundPcs.knowledgeSoundness_deployed_pcsM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SoundPcs.knowledgeSoundness_deployed_pcsM
