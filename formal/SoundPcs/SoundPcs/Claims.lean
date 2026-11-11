-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `formal/Compose/Compose/Claims.lean` of this repository (`read₁`, `read₂`, the claims discharged
-- through `Compose.Reduce`, `rustInstance`, `wiringStack`) to the EIP's PCS claims: the claims of
-- `PcsQuotient.claimsAt` through `PcsBridge.claimsAt_eq`, the quotient table assembled from its three parts.
import SoundPcs.Trace

/-!
# The claims, discharged

`ClaimsMatch` (`Trace.lean`) at F1's instance of `beta()` and `coordinate_weight` (`Compose.rustInstance`), on the
statement's constants (`PcsBridge.statementConsts`), the circuit's wiring table the honest one (`wiringCol`):

* the witness table read as its four row polynomials (`readW`), the parts assembled into the quotient table
  (`PcsBridge.assemble`) read as F1's second message (`asmQ`);
* **`claimsMatch`**: the four statements, through `PcsBridge.claimsAt_eq` (the claims are `Compose.Reduce`'s,
  the parts' by `quotientParts`), `colEval_eq_mle`, `Reduce.witness_iff`, `Reduce.wiring_iff`,
  `assemble_claims` and `Reduce.quotientClaims_of`; the reduction's own check from the nonzero denominators.

What remains as hypotheses is the old composition's: `beta()` is a Cantor basis (`IsCantor`), `tau` solves
`row_vanishing`'s system (`RowVanishing`), and the wire reads the statement as its halves then `1, 0, 0, 0`.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

namespace SoundPcs

open Compose Compose.Reduce QuotientRpm QuotientSecurity QuotientSecurity.Params LeanVM LeanVM.Protocol LeanVM.Parameters
open LeanVM.Protocol.Compile WhirBridge WhirBridge.Pcs PcsBridge Finset

/-! ## The statement and the values -/

theorem stmtOf_append (sb : Vector UInt8 64) : (stmtOf sb).y ++ (stmtOf sb).root = sb := by
  ext i hi
  by_cases h : i < 32
  · rw [Vector.getElem_append_left h]
    simp [stmtOf, Vector.get_eq_getElem]
  · rw [Vector.getElem_append_right (by omega) (by omega)]
    have h32 : 32 + (i - 32) = i := by omega
    simp only [stmtOf, Vector.getElem_ofFn, Vector.get_eq_getElem, h32]

theorem get_ofFn_fun (f : Fin 4 → E) : (fun i => (Vector.ofFn f).get i) = f := by
  funext i
  simp [Vector.get_eq_getElem]

/-- **The deployed claims through `Compose.Reduce`.** -/
theorem claimsD_eq (a : S0) {cl : PcsQuotient.Claims} (h : claimsD a = some cl) :
    ¬ ((denominators statementConsts 24 a.ch.α a.ch.β a.ch.t a.π.v.1 a.π.v.2).prod = 0 ∨
        product statementConsts a.ch.α a.ch.β a.ch.t a.π.v.1 a.π.v.2 = 0 ∨ 1 + a.ch.ρ = 0) ∧
      cl = newClaims (claimsOf statementConsts 24 (stmtHalves a.π.stmt) a.ch.α a.ch.β a.ch.γ a.ch.t a.π.v.1
        a.π.v.2 a.ch.ρ) (hInvOf a.ch.α a.ch.β a.ch.t a.ch.ρ a.π.v.1 a.π.v.2) a.rest.qv a.rest.gv := by
  unfold claimsD at h
  rw [claimsAt_eq, stmtOf_append, get_ofFn_fun] at h
  split_ifs at h with hb
  exact ⟨hb, (Option.some.inj h).symm⟩

/-! ## The reads -/

variable (hc : IsCantor statementConsts.beta) (σ : Equiv.Perm (Fin (22 + 2) → Bool))

/-- **A witness table read as F1's first message**: its four row polynomials. -/
noncomputable def readW : Column 25 → (rustInstance statementConsts hc σ).bounds.Msg₁ := fun q =>
  ⟨witnessOfTable (k := 22 + 1) (colFn q), fun j => (natDegree_witnessOfTable_le _ j).trans le_rfl⟩

/-- **The parts read as F1's second message**: the quotient table they assemble (`assemble`), read at the
extension's `Y`. -/
noncomputable def asmQ : Column 27 → Column 28 → Column 25 → (rustInstance statementConsts hc σ).bounds.Msg₂ :=
  fun qH qQ qG =>
    ⟨quotientsOfTable (m := 22 + 2) y (assemble (m := 24) (colFn qH) (colFn qQ) (colFn qG)),
      (tables_within_bounds (rustInstance statementConsts hc σ).params (rustInstance statementConsts hc σ).bounds le_rfl le_rfl y
        (fun _ => 0) (assemble (m := 24) (colFn qH) (colFn qQ) (colFn qG))).2⟩

/-! ## The honest wiring table -/

/-- **The honest wiring table** (`Index::new`'s): the column whose table holds, over `K`, a polynomial carrying
the wiring `σ` on the cells of `beta()`. -/
noncomputable def wiringCol : Column 24 :=
  ⟨Vector.ofFn fun t : Fin (2 ^ 24) =>
    ((basisK statementConsts hc).exists_table le24 fun x => (basisK statementConsts hc).point (σ x)).choose
      ((Whir.bitsEquiv 24).symm t)⟩

/-- **The honest wiring table carries the wiring.** -/
theorem wiringCol_carries (x : Fin (22 + 2) → Bool) :
    (tablePoly (colFn (wiringCol hc σ))).eval ((rustInstance statementConsts hc σ).basis.point x) =
      (rustInstance statementConsts hc σ).basis.point (σ x) := by
  set cK := ((basisK statementConsts hc).exists_table le24 fun x => (basisK statementConsts hc).point (σ x)).choose with hcK
  have hspec : ∀ x, (tablePoly cK).eval ((basisK statementConsts hc).point x) = (basisK statementConsts hc).point (σ x) :=
    ((basisK statementConsts hc).exists_table le24 fun x => (basisK statementConsts hc).point (σ x)).choose_spec
  have hfn : colFn (wiringCol hc σ) = fun b => ofK (cK b) := by
    funext b
    show ofK (Vector.ofFn (fun t : Fin (2 ^ 24) => cK ((Whir.bitsEquiv 24).symm t)))[Whir.bitsEquiv 24 b] = _
    simp
  show (tablePoly (colFn (wiringCol hc σ))).eval ((basisE statementConsts hc).point x) = (basisE statementConsts hc).point (σ x)
  rw [hfn, ← map_tablePoly, point_basisE, point_basisE, Polynomial.eval_map,
    show ofK ((basisK statementConsts hc).point x) = algebraMap K E ((basisK statementConsts hc).point x) from rfl,
    Polynomial.eval₂_at_apply, hspec]
  rfl

/-! ## The claims, discharged -/

variable (W : Wire (rustInstance statementConsts hc σ).params (rustInstance statementConsts hc σ).bounds)
  (hdec : ∀ sb, W.decode sb = stmtWords sb)

theorem matchesI (hτ : RowVanishing statementConsts 22) : Matches (rustInstance statementConsts hc σ).params statementConsts 22 :=
  matches_params _ statementConsts (rustInstance_basis statementConsts hc σ)
    (rustInstance_weights statementConsts hc σ) hτ

/-- **The claims are F1's** at the instance of `beta()`, the honest wiring table committed. -/
noncomputable def claimsMatch (hτ : RowVanishing statementConsts 22) : ClaimsMatch W (wiringCol hc σ) where
  readW := readW hc σ
  asm := asmQ hc σ
  witness a cl q hcl hl hv := by
    obtain ⟨hb, rfl⟩ := claimsD_eq a hcl
    have hnz : (denominators statementConsts 24 a.ch.α a.ch.β a.ch.t a.π.v.1 a.π.v.2).prod ≠ 0 :=
      fun h => hb (Or.inl h)
    rw [colEval_eq_mle q _ hl] at hv
    exact (witness_iff statementConsts 22 (stmtHalves a.π.stmt) a.ch.α a.ch.β a.ch.γ a.ch.t a.π.v.1 a.π.v.2
      a.ch.ρ (by norm_num) hnz (colFn q)).mp hv
  wiring a cl hcl hl hv := by
    obtain ⟨hb, rfl⟩ := claimsD_eq a hcl
    have hnz : (denominators statementConsts 24 a.ch.α a.ch.β a.ch.t a.π.v.1 a.π.v.2).prod ≠ 0 :=
      fun h => hb (Or.inl h)
    rw [colEval_eq_mle _ _ hl] at hv
    have hev := (wiring_iff statementConsts 22 (stmtHalves a.π.stmt) a.ch.α a.ch.β a.ch.γ a.ch.t a.π.v.1
      a.π.v.2 a.ch.ρ (by norm_num) hnz (colFn (wiringCol hc σ))).mp hv
    have hs : tablePoly (wiringTable (rustInstance statementConsts hc σ).basis le24
        (rustInstance statementConsts hc σ).wiring) = tablePoly (colFn (wiringCol hc σ)) :=
      (rustInstance statementConsts hc σ).basis.tablePoly_ext le24 _ _ fun x => by
        rw [wiringTable_eval, wiringCol_carries]
        rfl
    unfold wiringClaim
    rw [sigmaPoly_params, hs]
    exact hev
  check a cl hcl := by
    obtain ⟨hb, -⟩ := claimsD_eq a hcl
    have hnz : (denominators statementConsts 24 a.ch.α a.ch.β a.ch.t a.π.v.1 a.π.v.2).prod ≠ 0 :=
      fun h => hb (Or.inl h)
    obtain ⟨-, hden, hrows⟩ := prod_denominators_ne_zero hnz
    have hM := matchesI hc σ hτ
    have hx := rowCells_eq statementConsts _ hM.theta a.ch.t a.π.v.1 0
    unfold reductionCheck
    simp only
    rw [hM.rows, hM.vCells, digitPoly_eval, ← hx]
    exact mul_ne_zero hden hrows
  quotient a cl qH qQ qG hcl lH lS lQ lG hH hS hQ hG := by
    obtain ⟨hb, rfl⟩ := claimsD_eq a hcl
    simp only [not_or] at hb
    obtain ⟨hnz, hp, hρ⟩ := hb
    rw [colEval_eq_mle _ _ lH] at hH
    rw [colEval_eq_mle _ _ lS] at hS
    rw [colEval_eq_mle _ _ lQ] at hQ
    rw [colEval_eq_mle _ _ lG] at hG
    obtain ⟨h1, h2⟩ := assemble_claims (stmtHalves a.π.stmt) a.ch.α a.ch.β a.ch.γ a.ch.t a.ch.ρ a.π.v.1 a.π.v.2
      a.rest.qv a.rest.gv hnz hp hρ (colFn qH) (colFn qQ) (colFn qG) hH hQ hG hS
    have htarget : (rustInstance statementConsts hc σ).params.target (W.decode a.π.stmt) a.ch.γ =
        Reduce.target (stmtHalves a.π.stmt) a.ch.γ := by
      rw [hdec]
      refine (membership_target (rustInstance statementConsts hc σ).basis le24 (rustInstance statementConsts hc σ).wiring (invSeq (rustInstance statementConsts hc σ).basis.β) (rustInstance statementConsts hc σ).c (invSeq_zero _)
        (fun d hd _ => invSeq_sum (rustInstance statementConsts hc σ).basis.β (rustInstance statementConsts hc σ).basis.zero d hd) (stmtHalves a.π.stmt) a.ch.γ).trans ?_
      unfold Reduce.target
      ring
    exact quotientClaims_of statementConsts 22 (stmtHalves a.π.stmt) a.ch.α a.ch.β a.ch.γ a.ch.t a.π.v.1
      a.π.v.2 a.ch.ρ (by norm_num) (rustInstance statementConsts hc σ).params (matchesI hc σ hτ) (rustInstance statementConsts hc σ).basis le24 (cantorCells (rustInstance statementConsts hc σ).basis le24)
      (fun x => Params.ofCantor_pt (rustInstance statementConsts hc σ).basis le24 (rustInstance statementConsts hc σ).wiring 8 _ _
        (membershipPub_hPub (rustInstance statementConsts hc σ).basis (invSeq (rustInstance statementConsts hc σ).basis.β) (rustInstance statementConsts hc σ).c le24 (invSeq_zero _)
          fun d hd _ => invSeq_sum (rustInstance statementConsts hc σ).basis.β (rustInstance statementConsts hc σ).basis.zero d hd) x)
      (W.decode a.π.stmt) htarget hnz _ h1 h2

end SoundPcs
