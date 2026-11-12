-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from this repository's `formal/EndToEnd/Bridge/Setup.lean` (`wiringSetup_eq`) at commit abe22812 to the
-- EIP's PCS claims: the Statement's setup (`setupWith`, the commitment with its out-of-domain answer) is `SoundPcs`'s
-- `setupPcs` of the Statement's wiring table. `wiringTable_eq` and `tableEval_eq_mle` are copies of
-- `formal/EndToEnd/Completeness/E2ECompleteness/{PcsCircuit,PcsClaims}.lean`'s, so that this line does not import
-- the completeness line.
import Soundness.PcsExtract
import Bridge.Setup
import Completeness.Read
import LeanVM.Prover.Mle
import LeanVM.Protocol.Whir.Complete.Tables

/-!
# The circuit's commitment

* `wcol`: the Statement's wiring table (`(membership 22).wiringTable`, `2^24` entries) as a column;
* **`colEval_wcol`**: the column's polynomial is the table's (`tableEval`) at every point of `24` coordinates;
* **`setupPcs_eq`**: `SoundPcs`'s setup of `wcol` is the Statement's setup with Keccak-256 a call
  (`PcsKS.VH.setupWithH callKeccak256`), its tree's root as bytes and its out-of-domain answer.
-/

set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

open OracleSpec OracleComp

namespace PcsKS

open QuotientRpm QuotientSecurity Compose ComposePcs LeanVM LeanVM.Parameters
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile WhirBridge WhirBridge.Pcs SoundPcs

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

/-! ## The Statement's σ and wiring table -/

/-- **The hypothesis that σ has `2^24` entries** (`F0`'s `formal/Kc3Circuit` proves it of the deployed circuit). -/
def SigmaSize : Prop := (PcsQuotient.membership PcsQuotient.logRows).sigma.size = 2 ^ 24

/-- **The wiring table** is the coefficients of the σ-points (`m = 24` variables). -/
theorem wiringTable_eq : (PcsQuotient.membership PcsQuotient.logRows).wiringTable =
    PcsQuotient.Domain.coefficients 24 0
      ((PcsQuotient.membership PcsQuotient.logRows).sigma.map PcsQuotient.Domain.point) := by
  rw [PcsQuotient.Circuit.wiringTable]
  rfl

theorem wiringTable_size (hσ : SigmaSize) :
    (PcsQuotient.membership PcsQuotient.logRows).wiringTable.size = 2 ^ 24 := by
  rw [wiringTable_eq, Bridge.Ntt.coefficients_size, Array.size_map, hσ]

theorem cellOf_idx (x : Fin (22 + 2) → Bool) : QuotientSecurity.cellOf (Completeness.idx x) = x :=
  funext fun k ↦ Completeness.testBit_idx x k

/-! ## Claims on arrays are claims on tables -/

/-- **An array's claim is F1's `mle` of the table it holds.** -/
theorem tableEval_eq_mle {V : ℕ} (A : Array K) (hsz : A.size = 2 ^ V) (c : (Fin V → Bool) → K)
    (hA : ∀ i, A.getD i 0 = Completeness.natTable c i) (p : List E) (hp : p.length = V) :
    PcsQuotient.tableEval A p = mle (fun b ↦ ofK (c b)) (fun k : Fin V ↦ p.getD k 0) := by
  rw [Completeness.mle_eq_tableEvalN]
  have hl : List.ofFn (fun k : Fin V ↦ p.getD k 0) = p := by
    apply List.ext_getElem (by simp [hp])
    intro i h1 h2
    simp [List.getElem?_eq_getElem h2]
  rw [hl, PcsQuotient.tableEval, LeanVM.Prover.mleK_eq,
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
    PcsQuotient.tableEval A p = mle (fun b ↦ ofK (arrTable (V := V) A b)) (fun k : Fin V ↦ p.getD k 0) :=
  tableEval_eq_mle A hsz _ (getD_eq_natTable_arr A hsz) p hp

/-! ## The wiring table as a column -/

/-- **The Statement's wiring table as a column** of `2^24` words. -/
def wcol : Column 24 := Bridge.Setup.columnOf 24 (PcsQuotient.membership PcsQuotient.logRows).wiringTable

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
theorem colEval_wcol (hσ : SigmaSize) (z : List E) (hz : z.length = 24) :
    colEval wcol z = PcsQuotient.tableEval (PcsQuotient.membership PcsQuotient.logRows).wiringTable z := by
  rw [colEval_eq_mle wcol z hz, tableEval_eq_mle_arr _ (wiringTable_size hσ) z hz]
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
theorem setupPcs_eq (hσ : SigmaSize) :
    setupPcs wcol = (fun x : LeanVM.Prover.Tree × PcsQuotient.Commitment => (toB x.2.root, x.2.ood)) <$>
      VH.setupWithH callKeccak256 := by
  unfold setupPcs VH.setupWithH VH.commitmentWithH VH.commitWithH wiringSetup
  rw [show PcsQuotient.cellVars PcsQuotient.logRows = 24 from rfl,
    Bridge.Setup.stackWordFast_eq_columnOf 24 PcsQuotient.logInvRate (by norm_num) (by norm_num)]
  simp only [bind_map_left, map_bind, map_pure]
  refine bind_congr fun t => ?_
  rw [show ofB (toB t.root) = t.root from LeanVM.Rpm.digestOfRpm_toRpm _, oodPointWithH_eq, oodPointM_eq]
  refine bind_congr_support _ _ _ fun z hz => ?_
  rw [colEval_wcol hσ z (length_oodPointO hz)]

end PcsKS

/-- info: 'PcsKS.setupPcs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PcsKS.setupPcs_eq
