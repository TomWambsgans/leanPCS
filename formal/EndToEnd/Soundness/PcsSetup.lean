-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Bridge/Setup.lean` (`setupBridge`: the wiring column carries the
-- deployed σ; `wiringSetup_eq`) at commit abe22812 and `formal/SoundPcs/SoundPcs/Claims.lean` (`claimsMatch`) to the
-- EIP's PCS claims: the Statement's setup (`setupWith`, the commitment with its out-of-domain answer) is `SoundPcs`'s
-- `setupPcs` of the Statement's wiring table, and the claims match for it.
import Soundness.PcsExtract
import Soundness.PcsDeployedM
import Bridge.Setup
import E2ECompleteness.PcsCircuit
import E2ECompleteness.PcsClaims

/-!
# The circuit's commitment

* `wcol`: the Statement's wiring table (`(membership 22).wiringTable`, `2^24` entries) as a column;
* **`setupPcs_eq`**: `SoundPcs`'s setup of `wcol` is the Statement's setup with Keccak-256 a call
  (`setupWithH callKeccak256`), its tree's root as bytes and its out-of-domain answer (`stackWordFast` is mumbai's
  `stackWord`, `oodPointWithH_eq`, `tableEval` is the column's polynomial on the points it asks);
* **`wcol_carries`**: `wcol`'s polynomial carries the deployed wiring on the cells of `beta()` (the additive
  transform of the σ-points, `Bridge.Ntt.tablePoly_coefficients_cantor`);
* **`claimsMatchK`**: the claims match (`SoundPcs.ClaimsMatch`) for `wcol`: `SoundPcs.claimsMatch`'s proof, the
  table's wiring from `wcol_carries`.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

open OracleSpec OracleComp

namespace PcsKS

open QuotientRpm QuotientSecurity Compose Compose.Reduce ComposePcs LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge WhirBridge.Pcs SoundPcs PcsBridge

/-! ## A computation's continuation on its support -/

/-- Two continuations equal on the support give one computation. -/
theorem bind_congr_support {α β : Type} (mx : OracleComp KeccakCalls α) (f g : α → OracleComp KeccakCalls β)
    (h : ∀ x ∈ support mx, f x = g x) : mx >>= f = mx >>= g := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa using h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    refine bind_congr fun u => ih u fun x hx => h x ?_
    rw [mem_support_bind_iff]
    exact ⟨u, by simp, hx⟩

/-! ## The wiring table -/

/-- **The Statement's wiring table as a column** of `2^24` words. -/
def wcol : Column 24 := Bridge.Setup.columnOf 24 (PcsQuotient.membership PcsQuotient.logRows).wiringTable

theorem wiringTable_size : (PcsQuotient.membership PcsQuotient.logRows).wiringTable.size = 2 ^ 24 := by
  rw [E2ECompleteness.Pcs.wiringTable_eq, Bridge.Ntt.coefficients_size, Array.size_map,
    E2ECompleteness.Pcs.sigma_size]

theorem bitsToNat_eq_idx {m : ℕ} (b : Fin m → Bool) :
    LeanVM.Protocol.Whir.bitsToNat b = Completeness.idx b := by
  rw [LeanVM.Protocol.Whir.bitsToNat, Completeness.idx]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  cases b k <;> simp

theorem colFn_wcol (b : Fin 24 → Bool) :
    colFn wcol b = ofK ((PcsQuotient.membership PcsQuotient.logRows).wiringTable.getD (Completeness.idx b) 0) := by
  unfold colFn tabFn wcol Bridge.Setup.columnOf
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, LeanVM.Protocol.Whir.bitsEquiv_val, bitsToNat_eq_idx]

/-- **The column's polynomial is the table's**, at a point of `24` coordinates. -/
theorem colEval_wcol (z : List E) (hz : z.length = 24) :
    colEval wcol z = PcsQuotient.tableEval (PcsQuotient.membership PcsQuotient.logRows).wiringTable z := by
  rw [colEval_eq_mle wcol z hz, E2ECompleteness.Pcs.tableEval_eq_mle_arr _ wiringTable_size z hz]
  refine congrArg (fun f => mle f (fun k : Fin 24 => z.getD k 0)) (funext fun b => ?_)
  rw [colFn_wcol]
  rfl

/-! ## The setup -/

theorem length_oodPointO {n : ℕ} {r : Digest} {z : List E} (hz : z ∈ support (oodPointO n r)) :
    z.length = n := by
  have := length_of_mem_support_mapM (coordQ n r) (List.range n) z hz
  rwa [List.length_range] at this

/-- **`SoundPcs`'s setup of the Statement's wiring table is the Statement's setup**, its tree's root as bytes and
its out-of-domain answer. -/
theorem setupPcs_eq :
    setupPcs wcol = (fun x : LeanVM.Prover.Tree × PcsQuotient.Commitment => (toB x.2.root, x.2.ood)) <$>
      E2ECompleteness.Pcs.setupWithH callKeccak256 := by
  unfold setupPcs E2ECompleteness.Pcs.setupWithH E2ECompleteness.Pcs.commitmentWithH
    E2ECompleteness.Pcs.commitWithH wiringSetup
  rw [show PcsQuotient.cellVars PcsQuotient.logRows = 24 from rfl,
    Bridge.Setup.stackWordFast_eq_columnOf 24 PcsQuotient.logInvRate (by norm_num) (by norm_num)]
  simp only [bind_map_left, map_bind, map_pure]
  refine bind_congr fun t => ?_
  rw [show ofB (toB t.root) = t.root from LeanVM.Rpm.digestOfRpm_toRpm _, oodPointWithH_eq, oodPointM_eq]
  refine bind_congr_support _ _ _ fun z hz => ?_
  rw [colEval_wcol z (length_oodPointO hz)]

/-! ## The wiring -/

variable (hc : IsCantor statementConsts.beta)

theorem getD_map_point (s : Array ℕ) {i : ℕ} (hi : i < s.size) :
    (s.map PcsQuotient.Domain.point).getD i 0 = PcsQuotient.Domain.point (s.getD i 0) := by
  simp [Array.getD_eq_getD_getElem?, hi]

/-- **The Statement's wiring table carries the deployed wiring** on the cells of `beta()`. -/
theorem wcol_carries (x : Fin (22 + 2) → Bool) :
    (tablePoly (colFn wcol)).eval ((instR hc).basis.point x) = (instR hc).basis.point (deployedSigma x) := by
  have hσ' : (PcsQuotient.membership PcsQuotient.logRows).sigma = PcsCircuit.membership.sigma :=
    Bridge.Circuit.membership_sigma
  have hB : Bridge.Ntt.CantorUpTo 24 := cantorUpTo hc
  have hvsz : ((PcsQuotient.membership PcsQuotient.logRows).sigma.map PcsQuotient.Domain.point).size = 2 ^ 24 := by
    rw [Array.size_map, E2ECompleteness.Pcs.sigma_size]
  have hpt : ∀ y : Fin (22 + 2) → Bool,
      (basisK statementConsts hc).point y = (Bridge.Ntt.cantorOf hB).point y := by
    intro y
    simp only [CantorBasis.point, basisK, Bridge.Ntt.cantorOf]
    rfl
  have hfn : colFn wcol = fun b => ofK ((PcsQuotient.Domain.coefficients 24 0
      ((PcsQuotient.membership PcsQuotient.logRows).sigma.map PcsQuotient.Domain.point)).getD
        (Completeness.idx b) 0) := by
    funext b
    rw [colFn_wcol, E2ECompleteness.Pcs.wiringTable_eq]
  have hofK : ∀ a : K, ofK a = algebraMap K E a := fun _ ↦ rfl
  have hL := Bridge.Ntt.tablePoly_coefficients_cantor hB (by decide) _ hvsz x
  have hx : Completeness.idx x < (PcsQuotient.membership PcsQuotient.logRows).sigma.size := by
    rw [E2ECompleteness.Pcs.sigma_size]; exact Completeness.idx_lt x
  rw [getD_map_point _ hx] at hL
  show (tablePoly (colFn wcol)).eval ((basisE statementConsts hc).point x) =
    (basisE statementConsts hc).point (deployedSigma x)
  rw [hfn, ← map_tablePoly, point_basisE, point_basisE, hofK, hofK, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, hpt, hpt]
  congr 1
  refine hL.trans ?_
  have hn : PcsCircuit.membership.sigma.getD (Completeness.idx x) 0 < 2 ^ 24 :=
    PcsCircuit.membership_sigma_lt _ (lt_of_lt_of_eq (Completeness.idx_lt x) (by rfl))
  conv_rhs => rw [← E2ECompleteness.Pcs.cellOf_idx x, deployedSigma_cellOf (Completeness.idx_lt x)]
  rw [hσ', Bridge.Ntt.point_eq_cantor hB (by decide) hn]
  rfl

/-! ## The claims -/

variable (W : Wire (instR hc).params (instR hc).bounds) (hdec : ∀ sb, W.decode sb = stmtWords sb)

/-- **The claims match for the Statement's wiring table** (`SoundPcs.claimsMatch`'s fields, the wiring from
`wcol_carries`). -/
noncomputable def claimsMatchK (hτ : RowVanishing statementConsts 22) : ClaimsMatch W wcol where
  readW := readW hc deployedSigma
  asm := asmQ hc deployedSigma
  witness := (claimsMatch hc deployedSigma W hdec hτ).witness
  wiring a cl hcl hl hv := by
    obtain ⟨hb, rfl⟩ := claimsD_eq a hcl
    have hnz : (denominators statementConsts 24 a.ch.α a.ch.β a.ch.t a.π.v.1 a.π.v.2).prod ≠ 0 :=
      fun h => hb (Or.inl h)
    rw [colEval_eq_mle _ _ hl] at hv
    have hev := (wiring_iff statementConsts 22 (stmtHalves a.π.stmt) a.ch.α a.ch.β a.ch.γ a.ch.t a.π.v.1
      a.π.v.2 a.ch.ρ (by norm_num) hnz (colFn wcol)).mp hv
    have hs : tablePoly (QuotientSecurity.wiringTable (instR hc).basis le24 (instR hc).wiring) =
        tablePoly (colFn wcol) :=
      (instR hc).basis.tablePoly_ext le24 _ _ fun x => by
        rw [wiringTable_eval, wcol_carries]
        rfl
    unfold wiringClaim
    rw [sigmaPoly_params, hs]
    exact hev
  check := (claimsMatch hc deployedSigma W hdec hτ).check
  quotient := (claimsMatch hc deployedSigma W hdec hτ).quotient

theorem claimsMatchK_cW (hτ : RowVanishing statementConsts 22) :
    (claimsMatchK hc W hdec hτ).cW = cWK hc := rfl

end PcsKS
