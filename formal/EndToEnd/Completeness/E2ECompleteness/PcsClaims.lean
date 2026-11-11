-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from the previous protocol's prover bridge (`E2ECompleteness/ProverClaims.lean`,
-- `ProverAccept.lean`: `claimsAt_honest`, `reduce_honest`) to the PCS claims. Uses leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0): the
-- multilinear evaluation of an array (`mleK_eq`, `multilinearEval_eq_sum`).
import E2ECompleteness.PcsAccept
import E2ECompleteness.PcsTable
import E2ECompleteness.PcsValues
import E2ECompleteness.PcsStatement
import E2ECompleteness.PcsQuotient
import E2ECompleteness.PcsQuotientTable
import PcsBridge.Claims
import LeanVM.Prover.Mle
import LeanVM.Protocol.Whir.Complete.Tables

/-!
# The honest tables satisfy the six claims

**`honestClaims : HonestClaims`** (`PcsAccept.lean`): at non-degenerate challenges `(α, β, t, ρ)` (`badSet`), the
reduction (`claimsAt`, through `PcsBridge.claimsAt_eq`: Compose's `claimsOf` with the quotient table's claim split
over its parts) returns claims for every value of `Q`'s and `G`'s claims, and at their own values the six claims
hold of the honest tables:

* the witness and wiring claims, and the quotient table's two claims, are F1's (`Compose.Reduce`'s
  `witness_point`, …, `sum_value`), true of the honest tables by F1's completeness for the blinded second message
  (`honestB_accepts`) read as claims (`Completeness.claims_iff_accepts`) on the quotient table assembled from the
  three parts (`quotientsOfTable_honest`, `PcsQuotientTable.lean`);
* the claim on `H` at the quotient point follows from the quotient table's claim and `Q`'s and `G`'s values
  (`PcsBridge.mle_assemble`: `T(P) = w_H H(P_H) + w_Q Q(P_Q) + w_G G(P_G)`, `w_H ≠ 0`), the sum claim on `H` from the
  quotient table's sum claim (`w_H = 1` there).

A table's claim (`tableEval`, the array's multilinear extension) is F1's `mle` of the table read on the cube
(`tableEval_eq_mle`).
-/

open Finset Polynomial
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open PcsQuotient PcsQuotient.Domain QuotientSecurity

set_option autoImplicit false

namespace E2ECompleteness.Pcs

/-! ## Claims on arrays are claims on tables -/

/-- **An array's claim is F1's `mle` of the table it holds.** -/
theorem tableEval_eq_mle {V : ℕ} (A : Array K) (hsz : A.size = 2 ^ V) (c : (Fin V → Bool) → K)
    (hA : ∀ i, A.getD i 0 = Completeness.natTable c i) (p : List E) (hp : p.length = V) :
    tableEval A p = mle (fun b ↦ ofK (c b)) (fun k : Fin V ↦ p.getD k 0) := by
  rw [Completeness.mle_eq_tableEvalN]
  have hl : List.ofFn (fun k : Fin V ↦ p.getD k 0) = p := by
    apply List.ext_getElem (by simp [hp])
    intro i h1 h2
    simp [List.getElem?_eq_getElem h2]
  rw [hl, tableEval, LeanVM.Prover.mleK_eq,
    Whir.Complete.multilinearEval_eq_sum V _ _ (by simp [hsz]) hp, Completeness.tableEvalN]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' : i < 2 ^ V := Finset.mem_range.1 hi
  have h2 : (A.toList.map ofK).getD i 0 = ofK (A.getD i 0) := by
    simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, hi', hsz]
  rw [h2, hA]

/-- An array read as a table on `V` digits. -/
def arrTable {V : ℕ} (A : Array K) : (Fin V → Bool) → K := fun b ↦ A.getD (Completeness.idx b) 0

theorem getD_eq_natTable_arr {V : ℕ} (A : Array K) (hsz : A.size = 2 ^ V) (i : ℕ) :
    A.getD i 0 = Completeness.natTable (arrTable (V := V) A) i := by
  unfold Completeness.natTable arrTable
  split_ifs with h
  · rw [Completeness.idx_bitsOf V i h]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl

/-- **An array's claim is F1's `mle` of the array read on the cube.** -/
theorem tableEval_eq_mle_arr {V : ℕ} (A : Array K) (hsz : A.size = 2 ^ V) (p : List E)
    (hp : p.length = V) :
    tableEval A p = mle (fun b ↦ ofK (arrTable (V := V) A b)) (fun k : Fin V ↦ p.getD k 0) :=
  tableEval_eq_mle A hsz _ (getD_eq_natTable_arr A hsz) p hp

/-! ## Lists and points -/

theorem ofFn_getD {V : ℕ} (p : List E) (hp : p.length = V) :
    List.ofFn (fun k : Fin V ↦ p.getD k 0) = p := by
  apply List.ext_getElem (by simp [hp])
  intro i h1 h2
  simp [List.getElem?_eq_getElem h2]

theorem getD_ofFn_fun {V : ℕ} (u : Fin V → E) : (fun k : Fin V ↦ (List.ofFn u).getD k 0) = u := by
  funext k
  simp [List.getD_eq_getElem?_getD]

/-! ## The parts' claims from the quotient table's -/

section Parts

variable {m : ℕ} (cH : (Fin (m + 1 + 1 + 1) → Bool) → E) (cQ : (Fin (m + 1 + 1 + 1 + 1) → Bool) → E)
  (cG : (Fin (m + 1) → Bool) → E)

/-- **`H`'s claim from the quotient table's**, `Q`'s and `G`'s (`T(P) = w_H H + w_Q Q + w_G G`). -/
theorem h_claim_of (low : Fin m → E) (d₀ d₁ k₀ k₁ e₀ e₁ v qv gv hInv : E)
    (hT : mle (PcsBridge.assemble cH cQ cG)
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc low d₀) d₁) k₀) k₁) e₀) e₁) = v)
    (hq : mle cQ (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc low d₀) d₁) e₀) e₁) = qv)
    (hg : mle cG (Fin.snoc low d₀) = gv) (hinv : (1 + d₁) * (1 + k₀) * (1 + k₁) * hInv = 1) :
    mle cH (Fin.snoc (Fin.snoc (Fin.snoc low d₀) e₀) e₁) =
      (v + k₀ * (1 + k₁) * qv + (1 + d₁) * (1 + k₀) * k₁ * (1 + e₀) * (1 + e₁) * gv) * hInv := by
  rw [PcsBridge.mle_assemble, hq, hg] at hT
  rw [← hT]
  linear_combination (-(mle cH (Fin.snoc (Fin.snoc (Fin.snoc low d₀) e₀) e₁))) * hinv -
    (k₀ * (1 + k₁) * qv + (1 + d₁) * (1 + k₀) * k₁ * (1 + e₀) * (1 + e₁) * gv) * hInv *
      LeanVM.Protocol.Whir.Complete.two_eq_zero_E

/-- **`H`'s sum claim from the quotient table's.** -/
theorem sum_claim_of (low : Fin m → E) (e₀ e₁ v : E)
    (hT : mle (PcsBridge.assemble cH cQ cG)
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc low 0) 0) 0) 0) e₀) e₁) = v) :
    mle cH (Fin.snoc (Fin.snoc (Fin.snoc low 0) e₀) e₁) = v := by
  rw [PcsBridge.mle_assemble] at hT
  rw [← hT]
  ring

end Parts

theorem ofFn_snoc {α : Type} {n : ℕ} (f : Fin n → α) (x : α) :
    List.ofFn (Fin.snoc f x : Fin (n + 1) → α) = List.ofFn f ++ [x] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

/-- **The parts' points and weights** of a point given as its coordinates. -/
theorem quotientParts_ofFn (low : Fin 24 → E) (d₀ d₁ k₀ k₁ e₀ e₁ : E) :
    quotientParts (List.ofFn low ++ [d₀, d₁, k₀, k₁, e₀, e₁]) 24 =
      ((List.ofFn low ++ [d₀, e₀, e₁], (1 + d₁) * (1 + k₀) * (1 + k₁)),
        (List.ofFn low ++ [d₀, d₁, e₀, e₁], k₀ * (1 + k₁)),
        (List.ofFn low ++ [d₀], (1 + d₁) * (1 + k₀) * k₁ * (1 + e₀) * (1 + e₁))) := by
  have hl : (List.ofFn low).length = 24 := List.length_ofFn
  simp only [quotientParts, List.take_left' hl]
  have hg : ∀ k (x : E) (l : List E), (List.ofFn low ++ l).getD (24 + k) x = l.getD k x := by
    intro k x l
    rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.add_sub_cancel_left]
  simp only [hg]
  rfl

/-- `w_H⁻¹`, from the denominators: `hInvOf` inverts `H`'s weight at the quotient point. -/
theorem hInv_mul (w₂₅ w₂₄ P ρ hInv : E) (h1 : 1 + w₂₅ ≠ 0) (h2 : P + w₂₄ ≠ 0) (h3 : P ≠ 0)
    (h4 : 1 + ρ ≠ 0) (hI : hInv = (1 + w₂₅) * (P + w₂₄) * P⁻¹ * (1 + ρ)⁻¹) :
    (1 + w₂₅ / (1 + w₂₅)) * (1 + w₂₄ / (P + w₂₄)) * (1 + ρ) * hInv = 1 := by
  have two := LeanVM.Protocol.Whir.Complete.two_eq_zero_E
  have e1 : 1 + w₂₅ / (1 + w₂₅) = 1 / (1 + w₂₅) := by
    rw [eq_div_iff h1, add_mul, one_mul, div_mul_cancel₀ _ h1]; linear_combination w₂₅ * two
  have e2 : 1 + w₂₄ / (P + w₂₄) = P / (P + w₂₄) := by
    rw [eq_div_iff h2, add_mul, one_mul, div_mul_cancel₀ _ h2]
    linear_combination w₂₄ * two
  rw [e1, e2, hI]
  field_simp

/-! ## The reduction on the honest values -/

/-- The instance. -/
local notation "I" => Completeness.deployedInstanceE

theorem stmtConsts_eq : stmtConsts = PcsBridge.statementConsts := rfl

/-- `d d'` at `t`, for any parameters. -/
theorem dd_eval (P : Params E) (g : Fin 4 → E[X]) (α β t : E) :
    (Params.dPoly P g α β * Params.dNextPoly P g α β).eval t =
      (α + (Params.cellPoly P g 0).eval t + β * t) *
        (α + (Params.cellPoly P g 0).eval t + β * P.sigmaPoly.eval t) := by
  simp [Params.dPoly, Params.dNextPoly]

/-- **The reduction on the honest values returns F1's claims, split over the parts**, at non-degenerate
challenges: Compose's `claimsOf` with `newClaims`. -/
theorem claimsAt_newClaims (stmt : Statement) (g : Fin 4 → E[X]) (α β γ t ρ : E) (a : Vector E 4)
    (next qv gv : E) (ha : (fun i ↦ a.get i) = Params.opened g t)
    (hnext : next = (I).params.sigmaPoly.eval t)
    (hdeg : ¬ Completeness.Reduction.Degenerate I g α β t)
    (hprod : (Params.dPoly (I).params g α β * Params.dNextPoly (I).params g α β).eval t ≠ 0)
    (hρ : ρ ≠ 1) :
    claimsAt 22 stmt α β γ t ρ a next qv gv = some (PcsBridge.newClaims
      (Compose.Reduce.claimsOf PcsBridge.statementConsts 24
        (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) α β γ t (Params.opened g t) next ρ)
      (PcsBridge.hInvOf α β t ρ (Params.opened g t) next) qv gv) := by
  have hM := matches_deployed constants
  rw [stmtConsts_eq] at hM
  set A := Params.opened g t with hA
  have hx : ∀ i, Compose.Reduce.rowCells PcsBridge.statementConsts t A i = (I).params.cellAt A t i :=
    Compose.Reduce.rowCells_eq PcsBridge.statementConsts (I).params hM.theta t A
  have hvc : (I).params.vCells.eval t = sq^[22 + 2] t := by rw [hM.vCells, digitPoly_eval]
  have hden : (I).params.claimDen α β t A next =
      Compose.Reduce.product PcsBridge.statementConsts α β t A next + sq^[22 + 2] t := by
    rw [Params.claimDen, hvc, Compose.Reduce.product, hx 0]
  have hrc := (Completeness.Reduction.rustCheck_honest I g α β t).mpr hdeg
  obtain ⟨hw, hcd⟩ := hrc
  have hcd' : (I).params.claimDen α β t A next * (I).params.vRows.eval t ≠ 0 := by
    rw [hnext]; exact hcd
  have hnz : (Compose.Reduce.denominators PcsBridge.statementConsts (22 + 2) α β t A next).prod ≠ 0 := by
    refine List.prod_ne_zero fun h0 ↦ ?_
    rw [Compose.Reduce.denominators, List.mem_append, List.mem_map] at h0
    rcases h0 with ⟨k, hk, hk0⟩ | h0
    · rw [Compose.Reduce.wChain_eq] at hk0
      exact hw ⟨k, List.mem_range.mp hk⟩ hk0
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h0
      rcases h0 with h0 | h0
      · rw [Compose.Reduce.wChain_eq, ← hden] at h0
        exact hcd' (by rw [← h0, zero_mul])
      · rw [← hM.rows] at h0
        exact hcd' (by rw [← h0, mul_zero])
  have hP : Compose.Reduce.product PcsBridge.statementConsts α β t A next ≠ 0 := by
    rw [Compose.Reduce.product, hx 0, hA, Params.cellAt_opened, hnext, ← dd_eval]
    exact hprod
  have h1ρ : 1 + ρ ≠ 0 := fun h ↦ hρ (by
    linear_combination h - LeanVM.Protocol.Whir.Complete.two_eq_zero_E)
  rw [PcsBridge.claimsAt_eq, ha, if_neg]
  rintro (h | h | h)
  · exact hnz h
  · exact hP h
  · exact h1ρ h

/-! ## The quotient table -/

theorem newClaims_q_point (old : Compose.Reduce.Reduced) (hInv qv gv : E) :
    (PcsBridge.newClaims old hInv qv gv).q.point = (quotientParts old.quotient.point 24).2.1.1 := rfl

theorem newClaims_g_point (old : Compose.Reduce.Reduced) (hInv qv gv : E) :
    (PcsBridge.newClaims old hInv qv gv).g.point = (quotientParts old.quotient.point 24).2.2.1 := rfl

theorem newClaims_witness (old : Compose.Reduce.Reduced) (hInv qv gv : E) :
    (PcsBridge.newClaims old hInv qv gv).witness = ⟨old.witness.point, old.witness.value⟩ := rfl

theorem newClaims_wiring (old : Compose.Reduce.Reduced) (hInv qv gv : E) :
    (PcsBridge.newClaims old hInv qv gv).wiring = ⟨old.wiring.point, old.wiring.value⟩ := rfl

theorem newClaims_h (old : Compose.Reduce.Reduced) (hInv qv gv : E) :
    (PcsBridge.newClaims old hInv qv gv).h = ⟨(quotientParts old.quotient.point 24).1.1,
      (old.quotient.value + (quotientParts old.quotient.point 24).2.1.2 * qv +
        (quotientParts old.quotient.point 24).2.2.2 * gv) * hInv⟩ := rfl

theorem newClaims_q (old : Compose.Reduce.Reduced) (hInv qv gv : E) :
    (PcsBridge.newClaims old hInv qv gv).q = ⟨(quotientParts old.quotient.point 24).2.1.1, qv⟩ := rfl

theorem newClaims_g (old : Compose.Reduce.Reduced) (hInv qv gv : E) :
    (PcsBridge.newClaims old hInv qv gv).g = ⟨(quotientParts old.quotient.point 24).2.2.1, gv⟩ := rfl

theorem newClaims_sum (old : Compose.Reduce.Reduced) (hInv qv gv : E) :
    (PcsBridge.newClaims old hInv qv gv).sum = ⟨PcsQuotient.sumPoint 22, old.sum.value⟩ := rfl

/-- The quotient table's parts as tables over `E`. -/
noncomputable def cHT (T : Array K × Array K × Array K) : (Fin (24 + 1 + 1 + 1) → Bool) → E :=
  fun b ↦ ofK (arrTable T.1 b)

noncomputable def cQT (T : Array K × Array K × Array K) : (Fin (24 + 1 + 1 + 1 + 1) → Bool) → E :=
  fun b ↦ ofK (arrTable T.2.1 b)

noncomputable def cGT (T : Array K × Array K × Array K) : (Fin (24 + 1) → Bool) → E :=
  fun b ↦ ofK (arrTable T.2.2 b)

/-- **The honest quotient table holds the blinded honest second message** (`PcsQuotientTable.lean`). -/
def QuotientTableHonest : Prop :=
  ∀ (stmt : Statement) (w : Secret), Relation stmt w → ∀ (coins : Coins) (α β γ : E),
    ¬ Completeness.Reduction.BadAB I (gW w coins) α β →
    quotientsOfTable y (PcsBridge.assemble
        (cHT (quotientTables (membership logRows) (cellsOf w) coins α β γ))
        (cQT (quotientTables (membership logRows) (cellsOf w) coins α β γ))
        (cGT (quotientTables (membership logRows) (cellsOf w) coins α β γ))) =
      honestB (I).params (gW w coins) α β γ (blindPoly coins.blind)

/-! ## The six claims -/

/-- The witness table read as F1's (`Completeness.witnessTable`), entry by entry. -/
theorem witnessTable_natTable (w : Secret) (coins : Coins) (i : ℕ) :
    (witnessTable (membership logRows) (cellsOf w) coins).getD i 0 =
      Completeness.natTable (Completeness.witnessTable deployedBasis (cellFn w coins) coins.masks) i := by
  have hWe := ProverTables.witness_table constants (cellFn w coins) _ (cellsR_size w coins)
    (fun _ ↦ rfl) coins.masks i
  rw [witnessTable_eq]
  by_cases hi : i < 2 * 2 ^ cellVars (membership logRows).logRows
  · rw [getD_ofFn₂ _ _ hi]
    exact hWe
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega)]
    unfold Completeness.natTable
    rw [if_neg (by rw [cellVars_membership] at hi; simp only [pow_succ]; omega)]
    rfl

theorem membership_sigmaPoly :
    (I).params.sigmaPoly = tablePoly fun b ↦ algebraMap K E (Completeness.wiringTableK deployedBasis
      deployedSigma b) := by
  rw [Completeness.sigmaPoly_eq_wiringTableK (algebraMap K E) I deployedBasis (fun _ ↦ rfl),
    Completeness.deployedInstanceE_wiring]

theorem wiringTable_natTable (i : ℕ) :
    (membership logRows).wiringTable.getD i 0 =
      Completeness.natTable (Completeness.wiringTableK deployedBasis deployedSigma) i := by
  rw [wiringTable_eq]
  exact (ProverTables.wiring_table constants _ sigma_size sigma_point).2 i

/-- **The honest tables satisfy the six claims**, given the quotient table's second message. -/
theorem honestClaims_of (hQ : QuotientTableHonest) : HonestClaims := by
  intro stmt w hrel coins α β γ t ρ hgood
  have hb : ¬ BadP4 I (gW w coins) (α, β, t, ρ) := by
    simpa only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] using hgood
  unfold BadP4 at hb
  have e₁ : ((α, β, t, ρ) : E × E × E × E).1 = α := rfl
  have e₂ : ((α, β, t, ρ) : E × E × E × E).2.1 = β := rfl
  have e₃ : ((α, β, t, ρ) : E × E × E × E).2.2.1 = t := rfl
  have e₄ : ((α, β, t, ρ) : E × E × E × E).2.2.2 = ρ := rfl
  rw [e₁, e₂, e₃, e₄] at hb
  have hab : ¬ Completeness.Reduction.BadAB I (gW w coins) α β := fun h ↦ hb (Or.inl h)
  have hdeg : ¬ Completeness.Reduction.Degenerate I (gW w coins) α β t := fun h ↦ hb (Or.inr (Or.inl h))
  have hprod : (Params.dPoly (I).params (gW w coins) α β * Params.dNextPoly (I).params (gW w coins) α β).eval
      t ≠ 0 := fun h ↦ hb (Or.inr (Or.inr (Or.inl h)))
  have hρ : ρ ≠ 1 := fun h ↦ hb (Or.inr (Or.inr (Or.inr h)))
  set g := gW w coins with hg
  set cWK := Completeness.witnessTable deployedBasis (cellFn w coins) coins.masks with hcWK
  set cσK := Completeness.wiringTableK deployedBasis deployedSigma with hcσK
  have hWe := ProverTables.witness_table constants (cellFn w coins) _ (cellsR_size w coins)
    (fun _ ↦ rfl) coins.masks
  -- The values.
  have ha : (fun i ↦ (rowValues (membership logRows) (cellsOf w) coins t).1.get i) =
      Params.opened g t :=
    funext fun j ↦ rowValues_fst cWK (membership logRows) (cellsOf w) coins rfl hWe t j
  have hnext : (rowValues (membership logRows) (cellsOf w) coins t).2 = (I).params.sigmaPoly.eval t := by
    rw [rowValues_snd cσK (membership logRows) (cellsOf w) coins rfl wiringTable_natTable t,
      membership_sigmaPoly]
  -- The claims.
  refine ⟨fun qv gv ↦ PcsBridge.newClaims (Compose.Reduce.claimsOf PcsBridge.statementConsts 24
      (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) α β γ t (Params.opened g t)
      (rowValues (membership logRows) (cellsOf w) coins t).2 ρ)
      (PcsBridge.hInvOf α β t ρ (Params.opened g t) (rowValues (membership logRows) (cellsOf w) coins t).2)
      qv gv,
    fun qv gv ↦ claimsAt_newClaims stmt g α β γ t ρ _ _ qv gv ha hnext hdeg hprod hρ,
    fun qv gv ↦ ⟨(newClaims_q_point _ _ _ _).trans (newClaims_q_point _ _ _ _).symm,
      (newClaims_g_point _ _ _ _).trans (newClaims_g_point _ _ _ _).symm⟩, ?_⟩
  rw [hnext]
  set old := Compose.Reduce.claimsOf PcsBridge.statementConsts 24
    (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) α β γ t (Params.opened g t)
    ((I).params.sigmaPoly.eval t) ρ with hold
  -- F1's completeness, as claims on the tables.
  set stmtW := statementWords Primitives.F192.G Primitives.F192.Y (secretOf w).statement.y
    (secretOf w).statement.root with hstmtW
  have hsat : (I).Relation stmtW ((I).cellsOf g) := by
    have e : (I).cellsOf g = deployed.cellsRandomized (deployedAssign (secretOf w).toPcs)
        (fun r ↦ algebraMap K E (rndOf coins r)) := funext fun x ↦
      (Completeness.cellsOf_honest (algebraMap K E) I deployedBasis (fun _ ↦ rfl) (cellFn w coins)
        coins.masks x).trans (cellsR_getD_E w coins x)
    rw [e]
    exact Completeness.honest_relation_deployed_random (secretOf w) _
  have hacc := honestB_accepts I stmtW g hsat α β γ t ρ (blindPoly coins.blind) hab hdeg
  rw [← hQ stmt w hrel coins α β γ hab] at hacc
  have ht' : ∀ i : Fin (22 + 2 + 1 + 1), 1 + sq^[(i : ℕ)] t ≠ 0 := fun i h ↦ hdeg (Or.inl ⟨i, h⟩)
  have hnz : (I).params.claimDen α β t (Params.opened g t) ((I).params.sigmaPoly.eval t) *
      (I).params.vRows.eval t ≠ 0 := by
    rw [Completeness.Reduction.claimDen_honest]
    exact fun h ↦ hdeg (Or.inr h)
  obtain ⟨c1, c2, c3, c4⟩ := (claims_iff_accepts (I).params (I).basis le24 (I).cellEquiv
    (fun x ↦ cantorCells_point (n := 22) (I).basis le24 x) rfl
    (fun b ↦ algebraMap K E (cWK b)) (fun b ↦ algebraMap K E (cσK b)) membership_sigmaPoly
    (PcsBridge.assemble (cHT (quotientTables (membership logRows) (cellsOf w) coins α β γ))
      (cQT (quotientTables (membership logRows) (cellsOf w) coins α β γ))
      (cGT (quotientTables (membership logRows) (cellsOf w) coins α β γ)))
    y Completeness.one_add_y_ne (by simpa using Completeness.one_add_y_sq_ne) stmtW
    α β γ t ρ ((I).params.sigmaPoly.eval t) (Params.opened g t) ht' hnz).mpr hacc
  -- What `claimsOf` gives (Compose's transcription of the claims).
  have F1 : (fun k : Fin (22 + 1 + 1 + 1) ↦ old.witness.point.getD k 0) =
      Fin.cons ρ (Fin.cons (ρ ^ 2) (claimPoint 2 (22 + 1) t)) :=
    Compose.Reduce.witness_point PcsBridge.statementConsts 22
      (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) α β γ t (Params.opened g t)
      ((I).params.sigmaPoly.eval t) ρ
  have F2 : old.witness.value =
      (∑ j, Params.opening ρ j * Params.opened g t j) / claimScale 2 (22 + 1) t :=
    Compose.Reduce.witness_value PcsBridge.statementConsts 22
      (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) α β γ t (Params.opened g t)
      ((I).params.sigmaPoly.eval t) ρ (by norm_num)
  have F3 : (fun k : Fin (22 + 2) ↦ old.wiring.point.getD k 0) = claimPoint 0 (22 + 2) t :=
    Compose.Reduce.wiring_point PcsBridge.statementConsts 22
      (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) α β γ t (Params.opened g t)
      ((I).params.sigmaPoly.eval t) ρ
  have F4 : old.wiring.value = (I).params.sigmaPoly.eval t / claimScale 0 (22 + 2) t :=
    Compose.Reduce.wiring_value PcsBridge.statementConsts 22
      (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) α β γ t (Params.opened g t)
      ((I).params.sigmaPoly.eval t) ρ (by norm_num)
  have F5 : (fun k : Fin (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) ↦ old.quotient.point.getD k 0) =
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (claimPoint 0 (22 + 2 + 1 + 1) t)
        (sq^[22 + 2] t / (Compose.Reduce.product PcsBridge.statementConsts α β t (Params.opened g t)
          ((I).params.sigmaPoly.eval t) + sq^[22 + 2] t))) ρ) (y / (1 + y)))
        (y ^ 2 / (1 + y ^ 2)) : Fin (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) → E) :=
    Compose.Reduce.quotient_point PcsBridge.statementConsts 22
      (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) α β γ t (Params.opened g t)
      ((I).params.sigmaPoly.eval t) ρ
  have F6 : old.quotient.value =
      Compose.Reduce.identities PcsBridge.statementConsts (22 + 2) α β t (Params.opened g t)
          ((I).params.sigmaPoly.eval t) γ ρ /
        (Compose.Reduce.product PcsBridge.statementConsts α β t (Params.opened g t)
          ((I).params.sigmaPoly.eval t) + sq^[22 + 2] t) /
        Compose.Reduce.rows PcsBridge.statementConsts (22 + 2) t / ((1 + y) * (1 + y ^ 2)) /
        claimScale 0 (22 + 2 + 1 + 1) t :=
    Compose.Reduce.quotient_value PcsBridge.statementConsts 22
      (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) α β γ t (Params.opened g t)
      ((I).params.sigmaPoly.eval t) ρ (by norm_num)
  have F7 : old.sum.value =
      Compose.Reduce.target (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) γ /
        ((1 + y) * (1 + y ^ 2)) :=
    Compose.Reduce.sum_value PcsBridge.statementConsts 22
      (Compose.Reduce.stmtHalves (stmt.y ++ stmt.root)) α β γ t (Params.opened g t)
      ((I).params.sigmaPoly.eval t) ρ
  have L1 : old.witness.point.length = 22 + 1 + 1 + 1 := by
    show (Compose.Reduce.claimsOf _ _ _ _ _ _ _ _ _ _).witness.point.length = _
    rw [Compose.Reduce.witness_point_eq]; simp
  have L2 : old.wiring.point.length = 22 + 2 := by
    show (Compose.Reduce.claimsOf _ _ _ _ _ _ _ _ _ _).wiring.point.length = _
    rw [Compose.Reduce.wiring_point_eq]; simp
  have L3 : old.quotient.point.length = 22 + 2 + 1 + 1 + 1 + 1 + 1 + 1 := by
    show (Compose.Reduce.claimsOf _ _ _ _ _ _ _ _ _ _).quotient.point.length = _
    rw [Compose.Reduce.quotient_point_eq]; simp
  -- The quotient point and the inverse weight, before `old` is opaque.
  have hM := matches_deployed constants
  rw [stmtConsts_eq] at hM
  set P := Compose.Reduce.product PcsBridge.statementConsts α β t (Params.opened g t)
    ((I).params.sigmaPoly.eval t) with hP
  have hx : ∀ i, Compose.Reduce.rowCells PcsBridge.statementConsts t (Params.opened g t) i =
      (I).params.cellAt (Params.opened g t) t i :=
    Compose.Reduce.rowCells_eq PcsBridge.statementConsts (I).params hM.theta t _
  have hvc : (I).params.vCells.eval t = sq^[22 + 2] t := by rw [hM.vCells, digitPoly_eval]
  have hden : (I).params.claimDen α β t (Params.opened g t) ((I).params.sigmaPoly.eval t) =
      P + sq^[22 + 2] t := by
    rw [Params.claimDen, hvc, hP, Compose.Reduce.product, hx 0]
  have hval : (I).params.claimValue α β γ t ρ (Params.opened g t) ((I).params.sigmaPoly.eval t) =
      Compose.Reduce.identities PcsBridge.statementConsts (22 + 2) α β t (Params.opened g t)
          ((I).params.sigmaPoly.eval t) γ ρ / (P + sq^[22 + 2] t) /
        Compose.Reduce.rows PcsBridge.statementConsts (22 + 2) t := by
    rw [Params.claimValue, hden, hM.pub, hM.rows, Compose.Reduce.identities, hP,
      Compose.Reduce.product, Compose.Reduce.gate4, ← hx 0, ← hx 1, ← hx 2, ← hx 3, div_div]
    rfl
  have hP0 : P ≠ 0 := by
    rw [hP, Compose.Reduce.product, hx 0, Params.cellAt_opened, ← dd_eval]
    exact hprod
  have hden0 : P + sq^[22 + 2] t ≠ 0 := by
    rw [← hden]; exact left_ne_zero_of_mul hnz
  have h1ρ : 1 + ρ ≠ 0 := fun h ↦ hρ (by
    linear_combination h - LeanVM.Protocol.Whir.Complete.two_eq_zero_E)
  have hInvE : PcsBridge.hInvOf α β t ρ (Params.opened g t) ((I).params.sigmaPoly.eval t) =
      (1 + sq^[25] t) * (P + sq^[24] t) * P⁻¹ * (1 + ρ)⁻¹ := by
    rw [PcsBridge.hInvOf, Compose.Reduce.wChain_eq, Compose.Reduce.wChain_eq]
  clear_value old
  intro T c
  -- The quotient point by its coordinates.
  set cp := claimPoint 0 (22 + 2 + 1 + 1) t with hcpd
  set low := Fin.init (Fin.init cp) with hlow
  set d₀ := Fin.init cp (Fin.last _) with hd₀
  set d₁ := cp (Fin.last _) with hd₁
  set e := sq^[22 + 2] t / (P + sq^[22 + 2] t) with he
  have hcp : cp = Fin.snoc (Fin.snoc low d₀) d₁ := by simp only [hlow, hd₀, hd₁, Fin.snoc_init_self]
  have hu : (fun k : Fin (22 + 2 + 1 + 1 + 1 + 1 + 1 + 1) ↦ old.quotient.point.getD k 0) =
      Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc low d₀) d₁) e) ρ) (y / (1 + y)))
        (y ^ 2 / (1 + y ^ 2)) := by rw [F5, hcp]
  have hpt : old.quotient.point = List.ofFn low ++ [d₀, d₁, e, ρ, y / (1 + y), y ^ 2 / (1 + y ^ 2)] := by
    rw [← ofFn_getD old.quotient.point L3, hu]
    simp only [ofFn_snoc, List.append_assoc, List.cons_append, List.nil_append]
  have hparts := quotientParts_ofFn low d₀ d₁ e ρ (y / (1 + y)) (y ^ 2 / (1 + y ^ 2))
  rw [← hpt] at hparts
  -- The sizes.
  have hsW : (witnessTable (membership logRows) (cellsOf w) coins).size = 2 ^ (22 + 1 + 1 + 1) := by
    rw [witnessTable_eq, Array.size_ofFn, pow_succ, mul_comm]; rfl
  have hsσ : (membership logRows).wiringTable.size = 2 ^ (22 + 2) := by
    rw [wiringTable_eq, Bridge.Ntt.coefficients_size, Array.size_map, sigma_size]
  have hsT : T.1.size = 2 ^ (24 + 1 + 1 + 1) ∧ T.2.1.size = 2 ^ (24 + 1 + 1 + 1 + 1) ∧
      T.2.2.size = 2 ^ (24 + 1) := by
    show (quotientTables (membership logRows) (cellsOf w) coins α β γ).1.size = _ ∧
      (quotientTables (membership logRows) (cellsOf w) coins α β γ).2.1.size = _ ∧
      (quotientTables (membership logRows) (cellsOf w) coins α β γ).2.2.size = _
    rw [quotientTables_eq]
    simp only [hTableOf, qTableOf, gTableOf, Array.size_ofFn]
    refine ⟨?_, ?_, ?_⟩ <;> rw [membership_logRows] <;> rfl
  -- The claims, by their parts.
  have hc : c = PcsBridge.newClaims old
      (PcsBridge.hInvOf α β t ρ (Params.opened g t) ((I).params.sigmaPoly.eval t))
      (tableEval T.2.1 (quotientParts old.quotient.point 24).2.1.1)
      (tableEval T.2.2 (quotientParts old.quotient.point 24).2.2.1) := rfl
  rw [hc, newClaims_witness, newClaims_wiring, newClaims_h, newClaims_q, newClaims_g, newClaims_sum,
    hparts]
  dsimp only
  -- The tables as F1's.
  have tH : ∀ (l : List E), l.length = 24 + 1 + 1 + 1 →
      tableEval T.1 l = mle (cHT T) (fun k ↦ l.getD k 0) := fun l hl ↦
    tableEval_eq_mle_arr T.1 hsT.1 l hl
  have tQ : ∀ (l : List E), l.length = 24 + 1 + 1 + 1 + 1 →
      tableEval T.2.1 l = mle (cQT T) (fun k ↦ l.getD k 0) := fun l hl ↦
    tableEval_eq_mle_arr T.2.1 hsT.2.1 l hl
  have tG : ∀ (l : List E), l.length = 24 + 1 →
      tableEval T.2.2 l = mle (cGT T) (fun k ↦ l.getD k 0) := fun l hl ↦
    tableEval_eq_mle_arr T.2.2 hsT.2.2 l hl
  have lH : List.ofFn low ++ [d₀, y / (1 + y), y ^ 2 / (1 + y ^ 2)] =
      List.ofFn (Fin.snoc (Fin.snoc (Fin.snoc low d₀) (y / (1 + y))) (y ^ 2 / (1 + y ^ 2))) := by
    simp only [ofFn_snoc, List.append_assoc, List.cons_append, List.nil_append]
  have lQ : List.ofFn low ++ [d₀, d₁, y / (1 + y), y ^ 2 / (1 + y ^ 2)] =
      List.ofFn (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc low d₀) d₁) (y / (1 + y)))
        (y ^ 2 / (1 + y ^ 2))) := by
    simp only [ofFn_snoc, List.append_assoc, List.cons_append, List.nil_append]
  have lG : List.ofFn low ++ [d₀] = List.ofFn (Fin.snoc low d₀) := by
    simp only [ofFn_snoc]
  refine ⟨⟨L1, ?_⟩, ⟨L2, ?_⟩, ⟨by rw [lH, List.length_ofFn], ?_⟩, ⟨by rw [lQ, List.length_ofFn], rfl⟩,
    ⟨by rw [lG, List.length_ofFn], rfl⟩, ⟨by rw [PcsBridge.ClaimsAux.sumPoint_eq]; simp, ?_⟩⟩
  · -- The witness claim.
    exact (tableEval_eq_mle _ hsW _ (witnessTable_natTable w coins) _ L1).trans
      ((congrArg (mle _) F1).trans (c1.trans F2.symm))
  · -- The wiring claim.
    exact (tableEval_eq_mle _ hsσ _ wiringTable_natTable _ L2).trans
      ((congrArg (mle _) F3).trans (c2.trans F4.symm))
  · -- `H`'s claim at the quotient point.
    rw [lH, lQ, lG, tH _ (by rw [List.length_ofFn]), tQ _ (by rw [List.length_ofFn]),
      tG _ (by rw [List.length_ofFn]), getD_ofFn_fun, getD_ofFn_fun, getD_ofFn_fun]
    refine h_claim_of (cHT T) (cQT T) (cGT T) low d₀ d₁ e ρ (y / (1 + y)) (y ^ 2 / (1 + y ^ 2)) _ _ _ _
      ?_ rfl rfl ?_
    · rw [F6]
      rw [hvc, hden, hval, hcp] at c3
      exact c3
    · rw [hInvE]
      exact hInv_mul (sq^[25] t) (sq^[24] t) P ρ _ (ht' 25) hden0 hP0 h1ρ rfl
  · -- The sum claim.
    have hs : PcsQuotient.sumPoint 22 = List.ofFn (Fin.snoc (Fin.snoc (Fin.snoc
        (fun _ : Fin 24 ↦ (1 : E)) 0) (y / (1 + y))) (y ^ 2 / (1 + y ^ 2))) := by
      rw [PcsBridge.ClaimsAux.sumPoint_eq, Compose.Reduce.extension_eq]
      simp only [ofFn_snoc, List.ofFn_const, List.append_assoc, List.cons_append, List.nil_append]
    rw [hs, tH _ (by rw [List.length_ofFn]), getD_ofFn_fun, F7,
      ← target_stmt_reduce w stmt hrel γ]
    exact sum_claim_of (cHT T) (cQT T) (cGT T) _ _ _ _ c4

/-! ## The quotient table, discharged -/

/-- The honest cells satisfy the gates (the relation's first part). -/
theorem gate_cellFn (w : Secret) (coins : Coins) (yb : Fin 22 → Bool) :
    gate (ofK (cellFn w coins (cellBits (yb, 0)))) (ofK (cellFn w coins (cellBits (yb, 1))))
      (ofK (cellFn w coins (cellBits (yb, 2)))) (ofK (cellFn w coins (cellBits (yb, 3)))) = 0 := by
  have h := (Completeness.honest_relation_deployed_random (secretOf w)
    (fun r ↦ algebraMap K E (rndOf coins r))).1 yb
  have e : ∀ z, ofK (cellFn w coins z) = deployed.cellsRandomized (deployedAssign (secretOf w).toPcs)
      (fun r ↦ algebraMap K E (rndOf coins r)) z := fun z ↦ cellsR_getD_E w coins z
  rw [e, e, e, e]
  exact h

theorem membership_logRows' : (membership logRows).logRows = 22 := by rw [membership_logRows]

theorem cellVars22' : cellVars 22 = 24 := by norm_num [cellVars]

theorem two_six : (24 : ℕ) + 2 = 26 := by norm_num

theorem cHT_eq (T : Array K × Array K × Array K) :
    cHT T = fun b ↦ ofK (T.1.getD (Completeness.idx b) 0) := rfl

theorem cQT_eq (T : Array K × Array K × Array K) :
    cQT T = fun b ↦ ofK (T.2.1.getD (Completeness.idx b) 0) := rfl

theorem cGT_eq (T : Array K × Array K × Array K) :
    cGT T = fun b ↦ ofK (T.2.2.getD (Completeness.idx b) 0) := rfl

theorem quotientTables_eq' (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (α β γ : E) :
    quotientTables circuit cells₀ coins α β γ =
      (hTableOf circuit.logRows (hHatOf circuit cells₀ coins α β γ) coins.blind,
        qTableOf circuit.logRows (qHatOf circuit cells₀ coins α β γ),
        gTableOf circuit.logRows (qGateHatOf circuit cells₀ coins γ)) := by
  rw [quotientTables_eq]

theorem gW_eq (w : Secret) (coins : Coins) : gW w coins = ProverQuotient.gOf (cellFn w coins) coins.masks := by
  rw [gW, ProverQuotient.gOf]

/-- **The honest quotient table holds the blinded honest second message**, discharged. -/
theorem quotientTableHonest : QuotientTableHonest := by
  intro stmt w _ coins α β γ hab
  have h := quotientsOfTable_honest constants (cellFn w coins)
    (cellsR (membership logRows) (cellsOf w) coins) (cellsR_size w coins) (fun _ ↦ rfl)
    (membership logRows).sigma sigma_size sigma_point coins.masks coins.blind (gate_cellFn w coins)
    α β γ (by rw [← gW_eq]; exact hab)
  rw [cHT_eq, cQT_eq, cGT_eq, quotientTables_eq']
  simp only [hHatOf, qHatOf, qGateHatOf, wValuesC, membership_logRows', cellVars22', two_six,
    wiringTable_eq, gW_eq]
  exact h

/-- **The honest tables satisfy the six claims.** -/
theorem honestClaims : HonestClaims := honestClaims_of quotientTableHonest

end E2ECompleteness.Pcs

/-- info: 'E2ECompleteness.Pcs.honestClaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.honestClaims
