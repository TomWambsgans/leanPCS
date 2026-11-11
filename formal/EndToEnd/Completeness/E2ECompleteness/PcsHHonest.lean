-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here: the honest tables satisfy the deployed claims off the degenerate challenges. `tableEval_eq_mle` and
-- `tableEval_eq_mle_arr` are copied from `formal/EndToEnd/Soundness/PcsSetup.lean`.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the fields `K`, `E`, `mleK`.
import E2ECompleteness.PcsHValues
import E2ECompleteness.PcsHCells
import E2ECompleteness.PcsHDeg
import E2ECompleteness.PcsAccept
import Completeness.Read
import LeanVM.Prover.Mle
import LeanVM.Protocol.Whir.Complete.Tables

/-!
# The honest tables satisfy the claims

For a secret of the statement and any coins, at challenges `α, β, t, ρ` where no denominator vanishes (`GoodAt`:
the cells' copy denominators, `γ = (E /ₘ Z)(0)`, and `claimsAt`'s at `t`), for every `μ`: `claimsAt` returns
claims, and the witness, wiring and quotient tables satisfy them (**`honest_claims`**). The chain:

* the witness table's first message satisfies F1's relation (F0's `sat_honest`, `PcsHCells.lean`);
* the prover's `q` is `Z q = numer … (b₀ + b₁ X + b₂ (X² + X))` with `(q /ₘ Z)(0) = 0` (`PcsHQuot.lean`), so its
  second message `honestMsg` is consistent (`PcsKc3.lean`), and the quotient table holds it (`PcsHSlots.lean`);
* `h`'s top coefficient is zero: the logarithmic derivatives sum to zero over the cells (`sum_h_zero`);
* a consistent message is accepted (`accepts_of_consistent`), and accepted tables satisfy the claims
  (`claims_of_accepts`, `PcsKc3Claims.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

open Finset Polynomial
open LeanVM LeanVM.Parameters PcsQuotient PcsQuotient.Domain QuotientSecurity

-- The membership circuit is a closed term of `2^22` rows: never evaluate it.
attribute [local irreducible] PcsQuotient.membership PcsQuotient.membershipBuilder

namespace E2ECompleteness.Pcs.H

/-! ## Claims on arrays are claims on tables (`Soundness/PcsSetup.lean`'s) -/

theorem tableEval_eq_mle {V : ℕ} (A : Array K) (hsz : A.size = 2 ^ V) (c : (Fin V → Bool) → K)
    (hA : ∀ i, A.getD i 0 = Completeness.natTable c i) (p : List E) (hp : p.length = V) :
    PcsQuotient.tableEval A p = mle (fun b ↦ ofK (c b)) (fun k : Fin V ↦ p.getD k 0) := by
  rw [Completeness.mle_eq_tableEvalN]
  have hl : List.ofFn (fun k : Fin V ↦ p.getD k 0) = p := by
    apply List.ext_getElem (by simp [hp])
    intro i h1 h2
    simp [List.getElem?_eq_getElem h2]
  rw [hl, PcsQuotient.tableEval, LeanVM.Prover.mleK_eq,
    LeanVM.Protocol.Whir.Complete.multilinearEval_eq_sum V _ _ (by simp [hsz]) hp, Completeness.tableEvalN]
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

theorem tableEval_eq_mle_arr {V : ℕ} (A : Array K) (hsz : A.size = 2 ^ V) (p : List E)
    (hp : p.length = V) :
    PcsQuotient.tableEval A p = mle (fun b ↦ ofK (arrTable (V := V) A b)) (fun k : Fin V ↦ p.getD k 0) :=
  tableEval_eq_mle A hsz _ (getD_eq_natTable_arr A hsz) p hp

/-! ## The sum of the logarithmic derivatives -/

/-- **`h` sums to zero over the cells**: σ keeps the cells' values and permutes the cells. -/
theorem sum_h_zero (P : _root_.Kc3.Params E) (S : _root_.Kc3.Params.Stmt E) (g : Fin 4 → E[X])
    (hsat : P.Sat S (P.cells g)) (α β : E) (H : E[X])
    (hh : ∀ i, H.eval (P.pt i) = (α + P.cells g i + β * P.pt i)⁻¹ + (α + P.cells g i + β * P.pt (P.σ i))⁻¹) :
    ∑ i, H.eval (P.pt i) = 0 := by
  have hc := hsat.2.1
  have e : ∀ i, (α + P.cells g i + β * P.pt (P.σ i))⁻¹ = (α + P.cells g (P.σ i) + β * P.pt (P.σ i))⁻¹ :=
    fun i => by rw [hc i]
  simp only [hh, e, Finset.sum_add_distrib]
  rw [Equiv.sum_comp P.σ (fun i => (α + P.cells g i + β * P.pt i)⁻¹)]
  exact CharTwo.add_self_eq_zero _

/-- The index of the all-ones bits. -/
theorem idx_ones (m : ℕ) : Completeness.idx (fun _ : Fin m => true) = 2 ^ m - 1 := by
  have := _root_.Kc3.sum_two_pow_fin_add_one m
  unfold Completeness.idx
  simp only [ite_true]
  omega

/-- **The top coefficient of a table is the sum of its polynomial over the cells.** -/
theorem top_eq_sum (hHat : Array E) :
    hHat.getD (2 ^ 24 - 1) 0 = ∑ x : Fin 24 → Bool, (Novel.nov 0 24 fun j => hHat.getD j 0).eval (BE.point x) := by
  rw [← tablePoly_idx 24, sum_tablePoly BE (by norm_num), mle_ones, idx_ones]

/-! ## Unfolding `N0` and `Epoly` without unfolding the parameters -/

theorem N0_eq (P : _root_.Kc3.Params E) (cir : Circuit) (cells₀ : Array K) (coins : Coins) (stmt : Statement)
    (α β μ : E) (c : (Fin 24 → Bool) → E) :
    N0 P cir cells₀ coins stmt α β μ c = Kc3.Honest.numer P (Kc3Deployed.stmtOf stmt) (witnessOfTable (k := 22) c)
      α β μ (Hp cir cells₀ coins α β) (blindPoly coins) := rfl

theorem Epoly_eq (P : _root_.Kc3.Params E) (α β : E) (c : (Fin 24 → Bool) → E) :
    Epoly P α β c =
      (X ^ 2 + X) * P.dPoly (witnessOfTable (k := 22) c) α β * P.dNextPoly (witnessOfTable (k := 22) c) α β := rfl

theorem Qp_eq_nov (cir : Circuit) (cells₀ : Array K) (coins : Coins) (stmt : Statement) (α β μ : E) :
    Qp cir cells₀ coins stmt α β μ = Novel.nov 0 26 fun j => (qHatOf cir stmt cells₀ coins α β μ).getD j 0 := rfl

theorem witnessParts_fst (cir : Circuit) (cells₀ : Array K) (coins : Coins) :
    (witnessParts cir cells₀ coins).1 = randomizeCells cir cells₀ coins.rows := by
  simp only [witnessParts]

/-! ## The deployed circuit's facts -/

section Deployed

variable (w : Secret) (coins : Coins) (α β : E)

theorem hl_m : (membership logRows).logRows = 22 := membership_logRows'

theorem hw_m : (witnessParts (membership logRows) (cellsOf w) coins).2.size = 2 ^ 24 :=
  E2ECompleteness.Pcs.witnessTable_size w coins

theorem hs_m : (membership logRows).wiringTable.size = 2 ^ 24 := E2ECompleteness.Pcs.wiringTable_size

theorem hWc_m : Wp (membership logRows) (cellsOf w) coins = tablePoly (cW w coins) := by
  rw [Wp, tablePoly_cW,
    show (witnessParts (membership logRows) (cellsOf w) coins).2 = witnessTable (membership logRows) (cellsOf w) coins
      from rfl, witnessTable_eq]

theorem hS_m (t : E) : (Sp (membership logRows)).eval t = P0.sigmaPoly.eval t := by
  rw [Sp, ← tablePoly_idx 24]
  exact (P0_matches.sigma t).symm

theorem card_T_P0 : P0.T.card = 2 ^ 22 := P0_matches.card

theorem nCells_P0 : P0.nCells = 2 ^ 24 := by
  rw [_root_.Kc3.Params.nCells_eq, card_T_P0]; norm_num

/-- The honest first message, with its degree bound. -/
noncomputable def gMsg : P0.Msg₁ :=
  ⟨witnessOfTable (k := 22) (cW w coins), fun j => by
    rw [card_T_P0]; exact PcsBridge.Kc3.natDegree_witnessOfTable_lt _ j⟩

theorem hh_P0 (i : P0.T × Fin 4) :
    (Hp (membership logRows) (cellsOf w) coins α β).eval (P0.pt i) =
      (α + P0.cells (witnessOfTable (k := 22) (cW w coins)) i + β * P0.pt i)⁻¹ +
        (α + P0.cells (witnessOfTable (k := 22) (cW w coins)) i + β * P0.pt (P0.σ i))⁻¹ := by
  have hc : (Kc3Deployed.idxE BE hm28 i : ℕ) < 2 ^ 24 := by
    have := Kc3Deployed.idx_lt BE hm28 i; omega
  have h3 : (Kc3Deployed.idxE BE hm28 (P0.σ i) : ℕ) = sig (Kc3Deployed.idxE BE hm28 i) :=
    (Kc3Deployed.idx_sigma BE hm28 i).trans (sig_eq_sigC _).symm
  have e1 : P0.pt i = ofK (point (Kc3Deployed.idxE BE hm28 i)) := pt_idx i
  have e2 : P0.pt (P0.σ i) = ofK (point (sig (Kc3Deployed.idxE BE hm28 i))) :=
    (pt_idx (P0.σ i)).trans (congrArg (fun n => ofK (point n)) h3)
  have e3 : P0.cells (witnessOfTable (k := 22) (cW w coins)) i =
      ofK ((cellsR w coins).getD (Kc3Deployed.idxE BE hm28 i) 0) :=
    cells_cW w coins i
  have e4 : (witnessParts (membership logRows) (cellsOf w) coins).1 = cellsR w coins := by
    rw [witnessParts_fst, cellsR]
  rw [e3, e2, e1, Hp_eval_point _ _ _ _ _ hl_m hc, hArr_getD _ _ _ _ _ hl_m hc, e4]
  rfl

theorem sat_P0 {stmt : Statement} (h : Relation stmt w) :
    P0.Sat (Kc3Deployed.stmtOf stmt) (P0.cells (witnessOfTable (k := 22) (cW w coins))) := sat_cW h coins

/-- **`h`'s top coefficient is zero.** -/
theorem hHat_top {stmt : Statement} (h : Relation stmt w) :
    (hHatOf (membership logRows) (cellsOf w) coins α β).getD (2 ^ 24 - 1) 0 = 0 := by
  rw [top_eq_sum, ← Hp]
  have e : ∑ x : Fin 24 → Bool, (Hp (membership logRows) (cellsOf w) coins α β).eval (BE.point x) =
      ∑ i : P0.T × Fin 4, (Hp (membership logRows) (cellsOf w) coins α β).eval (P0.pt i) :=
    Fintype.sum_equiv (cantorCells BE hm28) (fun x => (Hp (membership logRows) (cellsOf w) coins α β).eval (BE.point x))
      (fun i : P0.T × Fin 4 => (Hp (membership logRows) (cellsOf w) coins α β).eval (P0.pt i)) fun x => by
        show _ = Polynomial.eval (((cantorCells BE hm28 x).1 : E) + shift (BE.β 1) (cantorCells BE hm28 x).2) _
        rw [cantorCells_point BE hm28 x]
  rw [e]
  exact sum_h_zero P0 _ _ (sat_P0 w coins h) α β _ (hh_P0 w coins α β)

end Deployed

/-! ## The honest claims, for any parameters matching the deployed circuit -/

section Claims

variable (w : Secret) (coins : Coins)

/-- The honest first message. -/
noncomputable abbrev gH : Fin 4 → E[X] := witnessOfTable (k := 22) (cW w coins)

/-- **The challenges where no denominator vanishes**: the cells' copy denominators at `α, β`, `γ = (E /ₘ Z)(0)`,
and `claimsAt`'s at `t, ρ` for the honest values. -/
structure GoodAt (P : _root_.Kc3.Params E) (α β t ρ : E) : Prop where
  cells : ∀ i : P.T × Fin 4, α + P.cells (gH w coins) i + β * P.pt i ≠ 0 ∧
    α + P.cells (gH w coins) i + β * P.pt (P.σ i) ≠ 0
  gamma : (Epoly P α β (cW w coins) /ₘ P.vCells).eval 0 ≠ 0
  nondeg : NonDeg α β t ρ (P.rowValues (_root_.Kc3.Params.opened (gH w coins) t) t) (P.sigmaPoly.eval t)

theorem hn_m : 2 ^ cellVars (membership logRows).logRows = 2 ^ 24 := by rw [hl_m]; rfl

theorem hHat_size (α β : E) : (hHatOf (membership logRows) (cellsOf w) coins α β).size = 2 ^ 24 := by
  unfold hHatOf
  rw [Bridge.Ntt.coefficients_size, hArr_size _ _ _ _ _ hl_m]

theorem slotOf_ff (n : ℕ) (hHat qHat : Array E) (b2 : E) (i : ℕ) :
    slotOf n hHat qHat b2 coins false false i = qHat.getD i 0 := rfl
theorem slotOf_tf (n : ℕ) (hHat qHat : Array E) (b2 : E) (i : ℕ) :
    slotOf n hHat qHat b2 coins true false i = (divX (qhOf n qHat)).getD i 0 := rfl
theorem slotOf_ft (n : ℕ) (hHat qHat : Array E) (b2 : E) (i : ℕ) :
    slotOf n hHat qHat b2 coins false true i = (mulX hHat).getD i 0 := rfl
theorem slotOf_tt (n : ℕ) (hHat qHat : Array E) (b2 : E) (i : ℕ) :
    slotOf n hHat qHat b2 coins true true i = b1Of coins b2 i := rfl

theorem nCells_of (P : _root_.Kc3.Params E) (hM : PcsBridge.Kc3.Matches P s₀) : P.nCells = 2 ^ 24 := by
  rw [_root_.Kc3.Params.nCells_eq, hM.card]; norm_num

theorem hS_of (P : _root_.Kc3.Params E) (hM : PcsBridge.Kc3.Matches P s₀) (t : E) : (Sp (membership logRows)).eval t = P.sigmaPoly.eval t := by
  rw [Sp, ← tablePoly_idx 24]
  exact (hM.sigma t).symm

theorem natDegree_Epoly_gen (P : _root_.Kc3.Params E) (hM : PcsBridge.Kc3.Matches P s₀) (α β : E)
    (c : (Fin 24 → Bool) → E) : (Epoly P α β c).natDegree ≤ 2 ^ 25 := by
  rw [Epoly_eq]
  obtain ⟨gm, hgm⟩ : ∃ gm : P.Msg₁, gm.1 = witnessOfTable (k := 22) c :=
    ⟨⟨witnessOfTable (k := 22) c, fun j => by rw [hM.card]; exact PcsBridge.Kc3.natDegree_witnessOfTable_lt _ j⟩, rfl⟩
  rw [← hgm]
  have := Kc3.Honest.natDegree_Epoly_le P gm α β
  rw [nCells_of P hM] at this
  exact this.trans (by norm_num)

theorem natDegree_numer_gen (P : _root_.Kc3.Params E) (hM : PcsBridge.Kc3.Matches P s₀) (S : _root_.Kc3.Params.Stmt E)
    (α β μ : E) (c : (Fin 24 → Bool) → E) (h ε : E[X]) (hh : h.natDegree < P.nCells) (hε : ε.natDegree ≤ 1) :
    (Kc3.Honest.numer P S (witnessOfTable (k := 22) c) α β μ h ε).natDegree < 3 * 2 ^ 24 := by
  obtain ⟨gm, hgm⟩ : ∃ gm : P.Msg₁, gm.1 = witnessOfTable (k := 22) c :=
    ⟨⟨witnessOfTable (k := 22) c, fun j => by rw [hM.card]; exact PcsBridge.Kc3.natDegree_witnessOfTable_lt _ j⟩, rfl⟩
  rw [← hgm]
  have := Kc3.Honest.natDegree_numer_lt P S gm α β μ h ε hh hε
  rw [nCells_of P hM] at this
  exact this

theorem opened_eq (t : E) (j : Fin 4) :
    _root_.Kc3.Params.opened (gH w coins) t j =
      (Novel.nov 0 22 (fun i => ofK ((witnessParts (membership logRows) (cellsOf w) coins).2.getD (j + 4 * i) 0))).eval
        (sq^[2] t) := by
  have e : (witnessParts (membership logRows) (cellsOf w) coins).2 = coefficients 24 0 (cellsR w coins) := by
    rw [show (witnessParts (membership logRows) (cellsOf w) coins).2 = witnessTable (membership logRows) (cellsOf w) coins
      from rfl, witnessTable_eq]
  rw [e]
  show (((gH w coins) j).comp rowPoly).eval t = _
  rw [Polynomial.eval_comp, rowPoly_eval]
  exact congrArg (fun p : E[X] => p.eval (sq^[2] t)) (witnessOfTable_nov (k := 22) (coefficients 24 0 (cellsR w coins)) j)

section Gen

variable (P : _root_.Kc3.Params E) (hM : PcsBridge.Kc3.Matches P s₀) (hZ : P.vCells = digitPoly 24)
  {stmt : Statement} (hsat : P.Sat (Kc3Deployed.stmtOf stmt) (P.cells (gH w coins)))
  (α β μ t ρ : E)
  (hh : ∀ i, (Hp (membership logRows) (cellsOf w) coins α β).eval (P.pt i) =
    (α + P.cells (gH w coins) i + β * P.pt i)⁻¹ + (α + P.cells (gH w coins) i + β * P.pt (P.σ i))⁻¹)
  (htop : (hHatOf (membership logRows) (cellsOf w) coins α β).getD (2 ^ 24 - 1) 0 = 0)
  (hG : GoodAt w coins P α β t ρ)
include hM hZ hsat hh htop hG

/-- **The prover's `q`**: `Z q` is the numerator with the whole blinding, `(q /ₘ Z)(0) = 0`, and `q`'s entries vanish
past `2^25`. -/
theorem quot_gen :
    P.vCells * Qp (membership logRows) (cellsOf w) coins stmt α β μ =
      Kc3.Honest.numer P (Kc3Deployed.stmtOf stmt) (gH w coins) α β μ (Hp (membership logRows) (cellsOf w) coins α β)
        (blindPoly coins + C (b2Of (membership logRows) stmt (cellsOf w) coins α β μ) * (X ^ 2 + X)) ∧
    (Qp (membership logRows) (cellsOf w) coins stmt α β μ /ₘ P.vCells).eval 0 = 0 ∧
    ∀ j, 2 ^ 25 < j → j < 2 ^ 26 → (qHatOf (membership logRows) stmt (cellsOf w) coins α β μ).getD j 0 = 0 := by
  have hθ : P.θ = ofK (betaAt 1) := hM.theta
  have hn := nCells_of P hM
  have hdvd : P.vCells ∣ N0 P (membership logRows) (cellsOf w) coins stmt α β μ (cW w coins) := by
    rw [N0_eq]
    exact Kc3.Honest.vCells_dvd_numer P _ _ hsat α β μ _ _ (fun i => (hG.cells i).1) (fun i => (hG.cells i).2) hh
  have gM : P.Msg₁ := ⟨gH w coins, fun j => by rw [hM.card]; exact PcsBridge.Kc3.natDegree_witnessOfTable_lt _ j⟩
  have hdegN : (N0 P (membership logRows) (cellsOf w) coins stmt α β μ (cW w coins)).natDegree < 3 * 2 ^ 24 := by
    rw [N0_eq]
    have hHd : (Hp (membership logRows) (cellsOf w) coins α β).natDegree < P.nCells := by
      rw [hn]; exact Novel.natDegree_nov_lt 24 _
    have hbd : (blindPoly coins).natDegree ≤ 1 := by
      unfold blindPoly
      exact natDegree_add_le_of_degree_le ((natDegree_C _).le.trans (by norm_num))
        ((natDegree_C_mul_le _ _).trans natDegree_X_le)
    exact natDegree_numer_gen P hM _ α β μ _ _ _ hHd hbd
  have hdegE : (Epoly P α β (cW w coins)).natDegree ≤ 2 ^ 25 := natDegree_Epoly_gen P hM α β _
  have hZQ := Z_mul_Qp P (membership logRows) (cellsOf w) coins stmt α β μ (cW w coins) hθ hl_m (hw_m w coins) hs_m
    (hWc_m w coins) (hS_of P hM) hZ hM.vRows hM.pins hdvd hdegN hdegE
  have hQ0 := Qp_div_eval_zero P (membership logRows) (cellsOf w) coins stmt α β μ (cW w coins) hθ hl_m (hw_m w coins)
    hs_m (hWc_m w coins) (hS_of P hM) hZ hM.vRows hM.pins hdvd hdegN hdegE
    hG.gamma
  exact ⟨hZQ, hQ0, fun j h1 h2 => Qp_entries P (membership logRows) (cellsOf w) coins stmt α β μ (cW w coins) hθ hl_m
    (hw_m w coins) hs_m (hWc_m w coins) (hS_of P hM) hZ hM.vRows hM.pins hdvd hdegN hdegE h1 h2⟩

/-- **The honest second message is consistent**, its `q` the prover's. -/
theorem consistent_gen : P.Consistent (Kc3Deployed.stmtOf stmt) (gH w coins)
    (Kc3.Honest.honestMsg P (Qp (membership logRows) (cellsOf w) coins stmt α β μ)
      (Hp (membership logRows) (cellsOf w) coins α β)
      (blindPoly coins + C (b2Of (membership logRows) stmt (cellsOf w) coins α β μ) * (X ^ 2 + X))) α β μ := by
  obtain ⟨hZQ, hQ0, -⟩ := quot_gen w coins (P := P) (hM := hM) (hZ := hZ) (hsat := hsat) (hh := hh) (htop := htop) (hG := hG) (t := t) (ρ := ρ) (μ := μ)
  exact Kc3.Honest.consistent_honest P (Kc3Deployed.stmtOf stmt) (gH w coins) α β μ _ _ _ hZQ hQ0

/-- The quotient table in `E`, by bits. -/
noncomputable def cTq (stmt : Statement) (α β μ : E) : (Fin 28 → Bool) → E :=
  fun b => ofK ((quotientTable (membership logRows) stmt (cellsOf w) coins α β μ).getD (Completeness.idx b) 0)

/-- **The quotient table holds the honest second message.** -/
theorem readTM_gen : PcsBridge.Kc3.readTM (cTq w coins stmt α β μ) =
    Kc3.Honest.honestMsg P (Qp (membership logRows) (cellsOf w) coins stmt α β μ)
      (Hp (membership logRows) (cellsOf w) coins α β)
      (blindPoly coins + C (b2Of (membership logRows) stmt (cellsOf w) coins α β μ) * (X ^ 2 + X)) := by
  obtain ⟨-, hQ0, hq⟩ := quot_gen w coins (P := P) (hM := hM) (hZ := hZ) (hsat := hsat) (hh := hh) (htop := htop) (hG := hG) (t := t) (ρ := ρ) (μ := μ)
  have hcT : ∀ b, cTq w coins stmt α β μ b = ofK ((tableOf (2 ^ cellVars (membership logRows).logRows)
      (hHatOf (membership logRows) (cellsOf w) coins α β) (qHatOf (membership logRows) stmt (cellsOf w) coins α β μ)
      (b2Of (membership logRows) stmt (cellsOf w) coins α β μ) coins).getD (Completeness.idx b) 0) := fun b => by
    rw [cTq, quotientTable_eq]
  have hq' : ∀ j, 2 ^ (24 + 1) < j → j < 2 ^ (24 + 2) →
      (qHatOf (membership logRows) stmt (cellsOf w) coins α β μ).getD j 0 = 0 := hq
  have hQ : Qp (membership logRows) (cellsOf w) coins stmt α β μ =
      Novel.nov 0 (24 + 2) fun j => (qHatOf (membership logRows) stmt (cellsOf w) coins α β μ).getD j 0 := Qp_eq_nov _ _ _ _ _ _ _
  have h1 : PcsBridge.Kc3.limbPoly (k := 24) ey (cTq w coins stmt α β μ) false false =
      Qp (membership logRows) (cellsOf w) coins stmt α β μ %ₘ P.vCells := by
    rw [limbPoly_ff _ hn_m _ _ _ coins _ hcT, slot_q 24 _ hq', hQ, hZ]
  have h2 : PcsBridge.Kc3.limbPoly (k := 24) ey (cTq w coins stmt α β μ) true false =
      (Qp (membership logRows) (cellsOf w) coins stmt α β μ /ₘ P.vCells) /ₘ X := by
    rw [limbPoly_tf _ hn_m _ _ _ coins _ hcT]
    rw [hQ, hZ] at hQ0
    rw [slot_a1 24 (by norm_num) _ hq' hQ0, hQ, hZ]
  have h3 : PcsBridge.Kc3.limbPoly (k := 24) ey (cTq w coins stmt α β μ) false true =
      X * Hp (membership logRows) (cellsOf w) coins α β := by
    rw [limbPoly_ft _ hn_m _ _ _ coins _ hcT, slot_b0 24 (by norm_num) _ (hHat_size w coins α β) htop, Hp]
  have h4 : PcsBridge.Kc3.limbPoly (k := 24) ey (cTq w coins stmt α β μ) true true =
      blindPoly coins + C (b2Of (membership logRows) stmt (cellsOf w) coins α β μ) * (X ^ 2 + X) := by
    rw [limbPoly_tt _ hn_m _ _ _ coins _ hcT, slot_b1 24 (by norm_num)]
  unfold PcsBridge.Kc3.readTM Kc3.Honest.honestMsg
  rw [h1, h2, h3, h4]


theorem valuesAt_fst_gen :
    (valuesAt (membership logRows) (cellsOf w) coins t).1 =
      Vector.ofFn (P.rowValues (_root_.Kc3.Params.opened (gH w coins) t) t) := by
  have hfun : (fun j : Fin 4 => (Novel.nov 0 22 (fun i => ofK ((witnessParts (membership logRows) (cellsOf w)
      coins).2.getD (j + 4 * i) 0))).eval (sq^[2] t)) = _root_.Kc3.Params.opened (gH w coins) t :=
    (funext fun j => (opened_eq w coins t j).symm)
  rw [valuesAt_fst _ _ _ hl_m, P.rowValues_eq, hM.theta, hfun]

theorem valuesAt_snd_gen : (valuesAt (membership logRows) (cellsOf w) coins t).2 = P.sigmaPoly.eval t := by
  rw [valuesAt_snd _ _ _ hl_m, hS_of P hM]

/-- **F1's verifier accepts the honest tables.** -/
theorem accepts_gen : P.Accepts (Kc3Deployed.stmtOf stmt) (gH w coins) (PcsBridge.Kc3.readTM (cTq w coins stmt α β μ))
    α β μ t (P.rowValues (_root_.Kc3.Params.opened (gH w coins) t) t) (P.sigmaPoly.eval t) ρ := by
  have hCons := consistent_gen w coins (P := P) (hM := hM) (hZ := hZ) (hsat := hsat) (hh := hh) (htop := htop) (hG := hG) (t := t) (ρ := ρ) (μ := μ)
  rw [← readTM_gen w coins (P := P) (hM := hM) (hZ := hZ) (hsat := hsat) (hh := hh) (htop := htop) (hG := hG) (t := t) (ρ := ρ) (μ := μ)] at hCons
  have hN := hG.nondeg
  have hconic : _root_.Kc3.Params.conic P.θ t ρ = witnessConic t (QuotientSecurity.sq t) ρ := by
    rw [hM.theta]
    simp only [witnessConic, _root_.Kc3.Params.conic, QuotientSecurity.sq]
  have hD : _root_.Kc3.conicDen P.θ t ρ ≠ 0 := by
    unfold _root_.Kc3.conicDen
    rw [hconic]
    exact hN.conic
  have hv0 : P.rowValues (_root_.Kc3.Params.opened (gH w coins) t) t 0 = (P.cellPoly (gH w coins) 0).eval t := by
    show P.cellAt (_root_.Kc3.Params.opened (gH w coins) t) t 0 = _
    exact P.cellAt_opened _ t 0
  have hC := hN.copy
  rw [hv0] at hC
  have hC' : P.vCells.eval t * t + (α + (P.cellPoly (gH w coins) 0).eval t + β * t) *
      (α + (P.cellPoly (gH w coins) 0).eval t + β * P.sigmaPoly.eval t) ≠ 0 := by
    rw [hM.vCells]; exact hC
  have hR : P.vRows.eval t ≠ 0 := by rw [hM.vRows]; exact hN.rows
  have hP : P.vPins.eval t ≠ 0 := by
    unfold _root_.Kc3.Params.vPins
    rw [Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hM.pins, CharTwo.sub_eq_add]
    exact hN.pins k k.2
  exact Kc3.Honest.accepts_of_consistent P _ _ _ α β μ t ρ hCons hD hC' hR hP

/-- **The honest tables satisfy the claims**, for parameters matching the deployed circuit. -/
theorem claims_gen :
    ∃ cl : Claims,
      claimsAt 22 stmt α β μ t ρ (valuesAt (membership logRows) (cellsOf w) coins t).1
        (valuesAt (membership logRows) (cellsOf w) coins t).2 = some cl ∧
      tableEval (witnessTable (membership logRows) (cellsOf w) coins) cl.witness.point = cl.witness.value ∧
      tableEval (membership logRows).wiringTable cl.wiring.point = cl.wiring.value ∧
      tableEval (quotientTable (membership logRows) stmt (cellsOf w) coins α β μ) cl.copy.point = cl.copy.value := by
  obtain ⟨cl, hcl⟩ := claimsAt_isSome stmt (μ := μ) hG.nondeg
  have hA := accepts_gen w coins (P := P) (hM := hM) (hZ := hZ) (hsat := hsat) (hh := hh) (htop := htop) (hG := hG) (t := t) (ρ := ρ) (μ := μ)
  obtain ⟨hW, hS, hT⟩ := claims_of_accepts P hM hcl (cW w coins) (cTq w coins stmt α β μ) hA
  obtain ⟨l1, l2, l3⟩ := claimsAt_lengths hcl (by decide)
  refine ⟨cl, ?_, ?_, ?_, ?_⟩
  · rw [valuesAt_fst_gen w coins (P := P) (hM := hM) (hZ := hZ) (hsat := hsat) (hh := hh) (htop := htop) (hG := hG) (t := t) (ρ := ρ),
      valuesAt_snd_gen w coins (P := P) (hM := hM) (hZ := hZ) (hsat := hsat) (hh := hh) (htop := htop) (hG := hG) (t := t) (ρ := ρ)]
    exact hcl
  · rw [witnessTable_eq, tableEval_eq_mle_arr (V := 24) _ (by rw [Bridge.Ntt.coefficients_size, cellsR_size]) _ l1]
    exact hW
  · rw [tableEval_eq_mle_arr (V := 24) _ hs_m _ l2]
    exact hS
  · rw [tableEval_eq_mle_arr (V := 28) _ (by rw [E2ECompleteness.Pcs.quotientTable_size, hl_m]; rfl) _ l3]
    exact hT

end Gen

end Claims

/-! ## The deployed parameters -/

/-- **The honest tables satisfy the claims** at every challenge where no denominator vanishes. -/
theorem honest_claims (w : Secret) (coins : Coins) {stmt : Statement} (hrel : Relation stmt w) (α β μ t ρ : E)
    (hG : GoodAt w coins P0 α β t ρ) :
    ∃ cl : Claims,
      claimsAt 22 stmt α β μ t ρ (valuesAt (membership logRows) (cellsOf w) coins t).1
        (valuesAt (membership logRows) (cellsOf w) coins t).2 = some cl ∧
      tableEval (witnessTable (membership logRows) (cellsOf w) coins) cl.witness.point = cl.witness.value ∧
      tableEval (membership logRows).wiringTable cl.wiring.point = cl.wiring.value ∧
      tableEval (quotientTable (membership logRows) stmt (cellsOf w) coins α β μ) cl.copy.point = cl.copy.value :=
  claims_gen w coins (P := P0) (hM := P0_matches) (hZ := vCells_eq) (hsat := sat_P0 w coins hrel)
    (hh := hh_P0 w coins α β) (htop := hHat_top w coins α β hrel) (hG := hG) (μ := μ)

/-- The challenges where a denominator vanishes. -/
def IsBad (w : Secret) (coins : Coins) (x : E × E × E × E) : Prop := ¬ GoodAt w coins P0 x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The elements of a finite type with a property. -/
noncomputable def setOf' {F : Type} [Fintype F] (p : F → Prop) : Finset F :=
  @Finset.filter _ p (fun _ => Classical.propDecidable _) Finset.univ

theorem mem_setOf' {F : Type} [Fintype F] (p : F → Prop) (x : F) : x ∈ setOf' p ↔ p x := by
  unfold setOf'
  rw [@Finset.mem_filter _ p (fun _ => Classical.propDecidable _)]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **The degenerate challenges**: those where a denominator vanishes. -/
@[irreducible] noncomputable def badSet (w : Secret) (coins : Coins) : Finset (E × E × E × E) :=
  setOf' (IsBad w coins)

theorem mem_badSet {w : Secret} {coins : Coins} {x : E × E × E × E} : x ∈ badSet w coins ↔ IsBad w coins x := by
  unfold badSet
  exact mem_setOf' _ x

theorem isBad_mk {w : Secret} {coins : Coins} (α β t ρ : E) :
    IsBad w coins (α, β, t, ρ) ↔ ¬ GoodAt w coins P0 α β t ρ := by
  unfold IsBad
  dsimp only
  exact Iff.rfl

theorem not_goodAt_of_mem {w : Secret} {coins : Coins} (α β t ρ : E) (hx : (α, β, t, ρ) ∈ badSet w coins) :
    ¬ GoodAt w coins P0 α β t ρ := (isBad_mk α β t ρ).mp (mem_badSet.mp hx)

/-- **The honest claims** (`PcsAccept.lean`'s `HonestClaims`) off `badSet`. -/
theorem honestClaims_badSet : HonestClaims badSet := by
  intro stmt w hrel coins α β μ t ρ hx
  have hG : GoodAt w coins P0 α β t ρ := by
    by_contra hng
    exact hx (mem_badSet.mpr ((isBad_mk α β t ρ).mpr hng))
  exact honest_claims w coins hrel α β μ t ρ hG

end E2ECompleteness.Pcs.H
