-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md; conventions: see AGENTS.md. π2's PCS claims' opening with
-- the out-of-domain point read off Keccak-256 (`RecStatement.pcsOpenKO`, `WhirBridge.Pcs.pcsVerifierO`) as an oracle
-- computation, after `formal/UniKeccakSound/UniKeccakSound/Fs/PcsOpK.lean` (`pcsOpenC`, its query bound, duplex
-- discipline, short queries, `pcsOpenK_eq`); the query bound follows the membership line's `SoundPcs/Opening.lean`
-- (`pcsVerifierO_queryBound`).
import UniKeccakSound.Fs.PcsOpK
import WhirBridge.PcsUnionOracle
import RecStatement.Security

/-!
# π2's openings with the out-of-domain point read off Keccak-256

* **`pcsOpenCO n root ood pt v p`**: `RecStatement.pcsOpenKO` (the PCS claim's opening, the out-of-domain point computed
  by the verifier with `n` Keccak-256 calls) as a computation of the two calls: `WhirBridge.Pcs.pcsVerifierO`; over
  `π` it is the contract's (`pcsOpenKO_eq`). It makes at most `10150` queries (`isTotalQueryBound_pcsOpenCO`: the
  seed's two, the point's `n ≤ 28`, the program's `10120`), follows the duplex discipline (`duplexVm_pcsOpenCO`) and
  asks short inputs only (`allQ_pcsOpenCO`).
* `simulateQ_pcsVerifierO`: run with any answers to the two calls, it is `pcsVerifyWithHashO` with those answers.
-/

namespace RecCompose

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The out-of-domain point, asked -/

/-- One coordinate, asked. -/
def coordC (n : ℕ) (r : Digest) (j : ℕ) : OracleComp KeccakCalls E := do
  return Pcs.elemOf ((digestBytes (← callKeccak256 (Pcs.oodInput n r j))).drop 8)

theorem oodPointM_eqC (n : ℕ) (r : Digest) :
    Pcs.oodPointM callKeccak256 n r = (List.range n).mapM (coordC n r) := rfl

theorem coordC_queryBound (n : ℕ) (r : Digest) (j : ℕ) : IsTotalQueryBound (coordC n r j) 1 := by
  unfold coordC callKeccak256
  exact isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩

theorem mapM_coordC_queryBound (n : ℕ) (r : Digest) :
    ∀ l : List ℕ, IsTotalQueryBound (l.mapM (coordC n r)) l.length
  | [] => trivial
  | j :: l => by
    rw [List.mapM_cons, List.length_cons, Nat.add_comm]
    exact isTotalQueryBound_bind (coordC_queryBound n r j) fun _ =>
      isTotalQueryBound_bind (n₂ := 0) (mapM_coordC_queryBound n r l) fun _ => trivial

theorem length_of_mem_support_mapM {α : Type} (f : ℕ → OracleComp KeccakCalls α) :
    ∀ (l : List ℕ) (z : List α), z ∈ support (l.mapM f) → z.length = l.length
  | [], z, hz => by
    rw [List.mapM_nil, mem_support_pure_iff] at hz
    subst hz
    rfl
  | j :: l, z, hz => by
    rw [List.mapM_cons, mem_support_bind_iff] at hz
    obtain ⟨a, -, hz⟩ := hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨xs, has, hz⟩ := hz
    rw [mem_support_pure_iff] at hz
    subst hz
    rw [List.length_cons, List.length_cons, length_of_mem_support_mapM f l xs has]

/-! ## The opening -/

/-- **`verify_claim` with the point read off Keccak-256 asks at most `10150` queries.** -/
theorem pcsVerifierO_queryBound {n : ℕ} (w : Pcs.Claim1 n × Proof) :
    IsTotalQueryBound (Pcs.pcsVerifierO w) 10150 := by
  unfold Pcs.pcsVerifierO Pcs.pcsVerifyWithHashO
  split_ifs with hn hr
  rotate_left
  · simp only [callKeccak256, callKeccakF1600]
    refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun iv => ?_⟩
    exact isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩
  · trivial
  simp only [callKeccak256, callKeccakF1600]
  refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun iv => ?_⟩
  refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun seed => ?_⟩
  have hz : ∀ z ∈ support (Pcs.oodPointM callKeccak256 n w.1.root),
      IsTotalQueryBound (runProofWithHash callKeccak256 callKeccakF1600 (Pcs.prog n logInvRate z w.1) seed w.2)
        ((2 + (4 + (2 + Verifier.whirBound))) / 4) := by
    intro z hzs
    rw [oodPointM_eqC] at hzs
    have hl : z.length = n := by
      have := length_of_mem_support_mapM (coordC n w.1.root) (List.range n) z hzs
      rwa [List.length_range] at this
    have hv : (⟨z.toArray, by simp [hl]⟩ : Vector E n).toList = z := by simp
    rw [← hv, Pcs.prog_eq]
    exact isTotalQueryBound_runProof (costLE_variant _ _ _) seed w.2
  have hb := isTotalQueryBound_bind_of_mem_support
    (by rw [oodPointM_eqC]; have := mapM_coordC_queryBound n w.1.root (List.range n); rwa [List.length_range] at this) hz
  refine hb.mono ?_
  have hn' : n ≤ 28 := hn.2
  have hw : (2 + (4 + (2 + Verifier.whirBound))) / 4 = 10120 := by
    have := variantQueries_eq
    unfold variantQueries at this
    omega
  omega

/-- **`verify_claim` with the point read off Keccak-256 follows the duplex discipline**: the seed's permutation call
after the IV's hash, then hashes only (the point), then the program. -/
theorem duplexVm_pcsVerifierO {n : ℕ} (w : Pcs.Claim1 n × Proof) :
    LeanVM.Rpm.DuplexVm (Pcs.pcsVerifierO w) [] := by
  rw [LeanVM.Rpm.duplexVm_iff_duplexP]
  unfold Pcs.pcsVerifierO Pcs.pcsVerifyWithHashO
  split_ifs
  · refine ((LeanVM.Rpm.hOnly_queryH _).duplexP []).bind fun iv h' hh => ?_
    subst hh
    refine (LeanVM.Rpm.duplexP_queryF_bind _ _ _ _).mpr
      ⟨LeanVM.Rpm.admissibleVm_seedInput _ _ _, fun seed => ?_⟩
    refine ((LeanVM.Rpm.hOnly_mapM _ (fun j => (LeanVM.Rpm.hOnly_queryH _).bind fun _ =>
      LeanVM.Rpm.hOnly_pure _) _).duplexP _).bind fun z h'' hh => ?_
    subst hh
    exact LeanVM.Rpm.duplexP_runProof _ List.mem_cons_self _
  · refine ((LeanVM.Rpm.hOnly_queryH _).duplexP []).bind fun iv h' hh => ?_
    subst hh
    exact (LeanVM.Rpm.duplexP_queryF_bind _ _ _ _).mpr
      ⟨LeanVM.Rpm.admissibleVm_seedInput _ _ _, fun seed => trivial⟩
  · trivial

theorem allQ_mapM_coordC (n : ℕ) (r : Digest) :
    ∀ l : List ℕ, AllQueriesSatisfy (l.mapM (coordC n r)) LeanVM.Rpm.Short
  | [] => LeanVM.Rpm.allQ_pure _
  | j :: l => by
    rw [List.mapM_cons]
    refine allQueriesSatisfy_bind ?_ fun _ => allQueriesSatisfy_bind (allQ_mapM_coordC n r l) fun _ =>
      LeanVM.Rpm.allQ_pure _
    unfold coordC
    refine allQueriesSatisfy_bind (LeanVM.Rpm.allQ_queryH ?_) fun _ => LeanVM.Rpm.allQ_pure _
    have : (Pcs.oodInput n r j).length = 46 := by simp [Pcs.oodInput, Pcs.oodTag, Pcs.digestBytes_length']
    omega

/-- The program past the root commits widths of at most `192`, at any out-of-domain point. -/
theorem widthsLE_prog (n R : ℕ) (z : List E) (x : Pcs.Claim1 n) :
    LeanVM.Rpm.WidthsLE LeanVM.Rpm.maxWidth (Pcs.prog n R z x) := by
  unfold Pcs.prog Pcs.check
  refine LeanVM.Rpm.WidthsLE.seq (LeanVM.Rpm.widthsLE_commitStack _ _) fun _ => ?_
  refine LeanVM.Rpm.WidthsLE.seq ?_ fun _ => trivial
  exact LeanVM.Rpm.WidthsLE.seq
    (LeanVM.Rpm.WidthsLE.of_moves (g := fun _ ↦ True) LeanVM.Protocol.EndToEnd.Sound.MovesOK.sampleE)
    fun _ ↦ by rw [LeanVM.Protocol.Verifier.verifyWhir_eq_target]; exact LeanVM.Rpm.widthsLE_verifyWhir _ _ _ _

/-- **`verify_claim` with the point read off Keccak-256 asks short inputs only.** -/
theorem allQ_pcsVerifierO {n : ℕ} (w : Pcs.Claim1 n × Proof) :
    AllQueriesSatisfy (Pcs.pcsVerifierO w) LeanVM.Rpm.Short := by
  unfold Pcs.pcsVerifierO Pcs.pcsVerifyWithHashO
  by_cases hn : Pcs.minVars ≤ n ∧ n ≤ Pcs.maxVars
  · simp only [hn, and_self, ↓reduceIte]
    refine allQueriesSatisfy_bind (LeanVM.Rpm.allQ_queryH ?_) fun iv => ?_
    · rw [Pcs.claimBytes_length]
      have := hn.2
      unfold Pcs.maxVars at this
      omega
    refine allQueriesSatisfy_bind (LeanVM.Rpm.allQ_queryF _) fun seed => ?_
    by_cases hr : rootOf w.2 = some w.1.root
    · simp only [hr, ↓reduceIte]
      refine allQueriesSatisfy_bind (by rw [oodPointM_eqC]; exact allQ_mapM_coordC _ _ _) fun z => ?_
      exact LeanVM.Rpm.allQ_runProof _ seed _ (widthsLE_prog _ _ _ _)
    · simp only [hr, ↓reduceIte]
      trivial
  · simp only [hn, ↓reduceIte]
    trivial

/-- `verify_claim` with the point read off Keccak-256, run with any answers to the two calls, is
`pcsVerifyWithHashO` with those answers. -/
theorem simulateQ_pcsVerifierO {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl LeanVM.KeccakCalls r) {n : ℕ} (x : Pcs.Claim1 n) (π : Proof) :
    simulateQ impl (Pcs.pcsVerifierO (x, π)) =
      Pcs.pcsVerifyWithHashO (Compile.Rom.implH impl) (Compile.Rom.implF impl) x π := by
  have hpt : ∀ l : List ℕ, simulateQ impl (l.mapM (coordC n x.root)) =
      l.mapM fun j => do return Pcs.elemOf ((digestBytes (← Compile.Rom.implH impl (Pcs.oodInput n x.root j))).drop 8) := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, ih, coordC, Compile.Rom.simulateQ_queryH]
  unfold Pcs.pcsVerifierO Pcs.pcsVerifyWithHashO
  by_cases hn : Pcs.minVars ≤ n ∧ n ≤ Pcs.maxVars
  · simp only [hn, and_self, ↓reduceIte]
    simp only [simulateQ_bind, Compile.Rom.simulateQ_queryH, Compile.Rom.simulateQ_queryF]
    refine bind_congr fun iv => bind_congr fun seed => ?_
    by_cases hr : rootOf π = some x.root
    · simp only [hr, ↓reduceIte, simulateQ_bind]
      rw [oodPointM_eqC, hpt]
      refine bind_congr fun z => ?_
      exact Compile.Rom.simulateQ_runProof impl _ _ _
    · simp only [hr, ↓reduceIte]
      simp
  · simp only [hn, ↓reduceIte]
    simp

/-! ## π2's claims' opening -/

/-- **A point claim's PCS opening with the point read off Keccak-256**, as a computation of Keccak-256 and
Keccak-f[1600]: `pcsVerifierO` on the claim `(root, ood, pt, v)` of `n` variables; `false` if the point has not `n`
coordinates. -/
def pcsOpenCO (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    OracleComp KeccakCalls Bool :=
  if h : pt.length = n then Pcs.pcsVerifierO (⟨root, ood, pt, v, h⟩, p) else pure false

theorem isTotalQueryBound_pcsOpenCO (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E)
    (p : Compile.Proof) : IsTotalQueryBound (pcsOpenCO n root ood pt v p) 10150 := by
  unfold pcsOpenCO
  split
  · exact pcsVerifierO_queryBound _
  · trivial

theorem duplexVm_pcsOpenCO (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    LeanVM.Rpm.DuplexVm (pcsOpenCO n root ood pt v p) [] := by
  unfold pcsOpenCO
  split
  · exact duplexVm_pcsVerifierO _
  · trivial

theorem allQ_pcsOpenCO (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    AllQueriesSatisfy (pcsOpenCO n root ood pt v p) LeanVM.Rpm.Short := by
  unfold pcsOpenCO
  split
  · exact allQ_pcsVerifierO _
  · trivial

/-- **The contract's opening with the point read off Keccak-256, over `π`, is `pcsOpenCO` answered over `π`.** -/
theorem pcsOpenKO_eq (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    RecStatement.pcsOpenKO Common.queryPermutation n root ood pt v p =
      simulateQ keccakCallsOverQueryPermutation (pcsOpenCO n root ood pt v p) := by
  unfold RecStatement.pcsOpenKO pcsOpenCO
  split
  · rw [simulateQ_pcsVerifierO]
    rfl
  · simp

end RecCompose

/-- info: 'RecCompose.pcsVerifierO_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pcsVerifierO_queryBound

/-- info: 'RecCompose.duplexVm_pcsVerifierO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.duplexVm_pcsVerifierO

/-- info: 'RecCompose.pcsOpenKO_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.pcsOpenKO_eq
