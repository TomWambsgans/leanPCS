-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/{Deployed,DeployedWired,Claims}.lean` of this repository
-- (`knowledgeSoundness_deployed`, `knowledgeSoundness_wired`, `knowledgeSoundness_deployed_rust`) to the three PCS
-- openings of the deployed protocol's claims; the fresh-query engine is `Compose/TwoOracle.lean`'s.
import SoundPcs.Trace
import SoundPcs.Opening

/-!
# Knowledge soundness of the deployed verifier of the EIP's PCS claims

**`knowledgeSoundness_deployed_pcs_of`**: in leanerVM `mumbai`'s two-oracle model (`KeccakCalls`: Keccak-256 and
Keccak-f[1600], independent lazily sampled random oracles), the setup commits to a wiring table `q₀`
(`setupPcs q₀`: its Merkle tree, `2^20` queries, and its out-of-domain answer, `24` more); the adversary, of at most
`Q` queries, is given the circuit's commitment and outputs a statement, two commitments, the values and three opening
proofs; the verifier (`dExp`) runs the two-root chain over Keccak-256, the claims of `PcsQuotient.claimsAt` at `2^22`
rows, and the three openings (`pcsOpen`: `pcsVerifierO`, the out-of-domain point read off Keccak-256). For any read
of the claims as F1's decision (`ClaimsMatch`) and F1's round counts (`ComposePcs.RoundsSound`) at a round error at
most `2^-164`, the probability that it accepts while no message the extractor reads off the adversary's Keccak-256
log (the witness root's Merkle word decoded by the computable `colCode`) is a witness of the statement is at most
`deployedBound Q`:

* three opening terms, `openingBound (N₀ + k · 10150)`, `k = 0, 1, 2`, `N₀ = 2^20 + 24 + Q + 6` (F2's
  `pcs_sound_oracle` for each opening, the run before it as its adversary);
* the binding of the two roots' lists at their out-of-domain points, `N · δc n + N (N + 1) / 2^256` for `n = 24`
  (`W`) and `28` (`T`), `N = N₀ + 3 · 10150` (`ood_binding_coords`; `δc 24 ≤ 2^-165`, `δc 28 ≤ 2^-169`);
* the chain, `N (2^-164 + 8 N / 2^256)`: each challenge bounded for the one candidate pair the two out-of-domain
  answers pin (`ComposePcs.Chain2`), F1's round error at most `2^-164`, and the collisions.

So the chain and the binding cost about `2^-163.5` a query; the three opening terms, `2^-128` a query each,
dominate.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace SoundPcs

open Compose ComposePcs QuotientRpm LeanVM LeanVM.Protocol
open LeanVM.Semantics LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open WhirBridge.Pcs

-- The runs are kept folded: no unification evaluates them.
attribute [local irreducible] stage DA2 e1 e2 dExp withSetup2 setupPcs loggedKC

/-- The queries before the openings: the setup's `2^20 + 24`, the adversary's `Q`, the chain's `6`. -/
abbrev N₀ (Q : ℕ) : ℕ := 2 ^ 20 + 24 + Q + 6

/-- All the queries: and the three openings', `10150` each. -/
abbrev Nall (Q : ℕ) : ℕ := N₀ Q + 10150 + 10150 + 10150

/-- The binding term at `n` variables, over the whole run. -/
noncomputable def bindTerm (n Q : ℕ) : ℝ≥0∞ :=
  ((Nall Q : ℕ) : ℝ≥0∞) * δc n + ((Nall Q * (Nall Q + 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256

/-- **The deployed bound.** -/
noncomputable def deployedBound (Q : ℕ) : ℝ≥0∞ :=
  openingBound (N₀ Q) + openingBound (N₀ Q + 10150) + openingBound (N₀ Q + 10150 + 10150) +
    bindTerm 24 Q + bindTerm 28 Q +
    ((Nall Q : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 164 : ℝ≥0) : ℝ≥0∞) + 8 * ((Nall Q : ℕ) : ℝ≥0∞) / 2 ^ 256)

/-- **At `n = 24`**: `C(L, 2) / 2^192 ≤ 2^-165`. -/
theorem δc_24 : δc 24 ≤ (2 : ℝ≥0∞)⁻¹ ^ 165 := by
  have hw := admissible_v1 24 (by decide) (by decide)
  refine δc_le_of (k := 27) (by norm_num) ?_
  refine le_trans (Nat.choose_le_choose 2 (listMax_le_listHi hw)) ?_
  rw [Nat.choose_two_right]
  exact listHi_choose_24

/-- **At `n = 28`**: `C(3564, 2) / 2^192 ≤ 2^-169`. -/
theorem δc_28 : δc 28 ≤ (2 : ℝ≥0∞)⁻¹ ^ 169 := by
  have hw := admissible_v1 28 (by decide) (by decide)
  refine δc_le_of (k := 23) (by norm_num) ?_
  refine le_trans (Nat.choose_le_choose 2 (listMax_le_listHi hw)) ?_
  rw [Nat.choose_two_right, listHi_28]
  norm_num

/-- The inputs the bad events may read: the `32`-byte states and the out-of-domain inputs (`46` bytes). -/
def S₀ : Set (List UInt8 ⊕ KeccakState) :=
  Set.range (fun v : QuotientRpm.Bytes32 => (Sum.inl v.toList : List UInt8 ⊕ KeccakState)) ∪
    Sum.inl '' {x : List UInt8 | x.length = 46}

theorem S₀_finite : S₀.Finite :=
  (Set.finite_range _).union ((List.finite_length_eq UInt8 46).image _)

variable {P : Kc3.Params E} (W : Wire2 P) (hR : RoundsSound P)
  (hre : P.roundError ≤ ((1 / 2 ^ 164 : ℝ≥0) : ℝ≥0∞))
include hR hre

/-- **Knowledge soundness of the deployed verifier of the EIP's PCS claims**, for any committed wiring table `q₀`,
any match `M` of the claims to F1's decision and F1's round counts, in mumbai's two-oracle model, at `2^22` rows. -/
theorem knowledgeSoundness_deployed_pcs_of (q₀ : Column 24) (M : ClaimsMatch W q₀)
    (A₀ : QuotientRpm.Bytes32 × E → OracleComp KeccakCalls (RootProof2 E × Rest)) (Q : ℕ)
    (hQ : ∀ c, IsTotalQueryBound (A₀ c) Q) :
    Pr{let z ← (simulateQ randomOracle (dExp W pcsOpen (withSetup2 (setupPcs q₀) A₀))).run' ∅}[
        BreaksD W M.cW z] ≤ deployedBound Q := by
  have hA : IsTotalQueryBound (withSetup2 (setupPcs q₀) A₀) (2 ^ 20 + 24 + Q) :=
    isTotalQueryBound_withSetup2 _ A₀ _ Q (setupPcs_queryBound _) hQ
  -- The rest: a bad fresh query.
  have hrest : Pr{let z ← (simulateQ randomOracle (dExp W pcsOpen (withSetup2 (setupPcs q₀) A₀))).run' ∅}[
      BreaksD W M.cW z ∧ ¬ EW pcsOpen z ∧ ¬ Eσ pcsOpen z ∧ ¬ ET pcsOpen z ∧ ¬ EBn 24 z ∧ ¬ EBn 28 z] ≤
      ((Nall Q : ℕ) : ℝ≥0∞) * (((1 / 2 ^ 164 : ℝ≥0) : ℝ≥0∞) + 8 * ((Nall Q : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
    refine prEvent_randomOracle_le_of_freshBad_dep (R := KeccakCalls)
      (dExp W pcsOpen (withSetup2 (setupPcs q₀) A₀)) (Nall Q) (qb_dExp W pcsOpen _ _ hA) S₀ S₀_finite _
      (advBad2P W M.KP (withSetup2 (setupPcs q₀) A₀)) _ (fun S hS c t ht hcard => ?_)
      (fun T h => trace_dExp W pcsOpen M A₀ T h)
    have hS' : ∀ v : QuotientRpm.Bytes32, (Sum.inl v.toList : List UInt8 ⊕ KeccakState) ∈ S :=
      fun v => hS _ (Or.inl ⟨v, rfl⟩)
    have hSz : ∀ x, M.KP.zin x → (Sum.inl x : List UInt8 ⊕ KeccakState) ∈ S :=
      fun x hx => hS _ (Or.inr ⟨x, hx, rfl⟩)
    refine (prob_advBad2P W M.KP hR _ S hS' hSz c t ht).trans ?_
    rw [add_comm]
    gcongr
    · have h10 : 10 ≤ Nall Q := by simp only [Nall, N₀]; omega
      have : 7 * (cacheDom c).card + 8 ≤ 8 * Nall Q := by omega
      calc ((7 * (cacheDom c).card + 8 : ℕ) : ℝ≥0∞) ≤ ((8 * Nall Q : ℕ) : ℝ≥0∞) := by
            exact_mod_cast this
        _ = 8 * ((Nall Q : ℕ) : ℝ≥0∞) := by push_cast; ring
  -- The split.
  set mx := (simulateQ randomOracle (dExp W pcsOpen (withSetup2 (setupPcs q₀) A₀))).run' ∅ with hmx
  have hsplit : ∀ z, BreaksD W M.cW z → EW pcsOpen z ∨ Eσ pcsOpen z ∨ ET pcsOpen z ∨ EBn 24 z ∨ EBn 28 z ∨
      (BreaksD W M.cW z ∧ ¬ EW pcsOpen z ∧ ¬ Eσ pcsOpen z ∧ ¬ ET pcsOpen z ∧ ¬ EBn 24 z ∧ ¬ EBn 28 z) := by
    intro z hb
    by_cases h1 : EW pcsOpen z
    · exact Or.inl h1
    by_cases h2 : Eσ pcsOpen z
    · exact Or.inr (Or.inl h2)
    by_cases h3 : ET pcsOpen z
    · exact Or.inr (Or.inr (Or.inl h3))
    by_cases h4 : EBn 24 z
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    by_cases h5 : EBn 28 z
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hb, h1, h2, h3, h4, h5⟩))))
  refine (prEvent_mono mx _ _ hsplit).trans ?_
  refine (prEvent_or_le _ _ _).trans ?_
  refine (add_le_add (prEvent_EW_le W pcsOpen _ _ hA) ((prEvent_or_le _ _ _).trans
    (add_le_add (prEvent_Eσ_le W pcsOpen _ _ hA) ((prEvent_or_le _ _ _).trans
    (add_le_add (prEvent_ET_le W pcsOpen _ _ hA) ((prEvent_or_le _ _ _).trans
    (add_le_add (prEvent_EBn_le W pcsOpen _ _ hA 24 adm24) ((prEvent_or_le _ _ _).trans
    (add_le_add (prEvent_EBn_le W pcsOpen _ _ hA 28 adm28) hrest))))))))).trans (le_of_eq ?_)
  simp only [deployedBound, bindTerm, add_assoc]
  rfl

end SoundPcs
