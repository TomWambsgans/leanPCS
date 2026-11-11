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

end E2ECompleteness.Pcs.H
