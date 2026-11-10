-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The PCS claim's opening is `formal/WhirBridge`'s
-- (`WhirBridge.Pcs`, `crates/pcs_claim`'s `verify_claim`); the query bound and the duplex discipline follow
-- `Compose/Deployed.lean`'s `ourVerifier_queryBound` and `Compose/Rpm.lean`'s `duplexVm_ourVerifier`.
import Compose.GOps
import WhirBridge.PcsUnion
import UniKeccakSound.Fs.Whir23
import UniKeccak.Pcs
import Soundness.Cost

/-!
# The Keccak verifier's PCS openings as oracle computations

* **`pcsOpenC n root ood pt v p`**: `UniKeccak.pcsOpenK` (a point claim on a commitment `(root, ood)` of a stack of
  `n` variables, the point required to have `n` coordinates, opened by `verify_claim`) as a computation of the two
  calls; over `π` it is the verifier's (`pcsOpenK_eq`). It makes at most `10122` queries
  (`isTotalQueryBound_pcsOpenC`) and follows the duplex discipline (`duplexVm_pcsOpenC`).
* **`pcsKShapes`**: version 1's sizes `2^23 ..= 2^28` at the per-group bound `εExact = 269 · 2^-137`
  (`WhirBridge.whirEps_le_exact`, `Whir23.lean`'s `whirEps_le_exact23`), distinct: the union of
  `WhirBridge.Pcs.pcs_union_sound`. `pcsIdxK n` is size `n`'s index.
* `romExperiment_le_map`: a verifier that is another's on a map of its statement, where a condition holds, and
  rejects elsewhere, accepts with an event at most as often as the other with an event implied.
-/

namespace UniKeccakSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement UniKeccak
open LeanVM.Protocol.Rom (romExperiment romExperiment_map romExperiment_eq)
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The opening -/

/-- **A point claim's PCS opening**, as a computation of Keccak-256 and Keccak-f[1600]: `verify_claim` on the claim
`(root, ood, pt, v)` of `n` variables, the out-of-domain point `oodPoint n`; `false` if the point has not `n`
coordinates. -/
def pcsOpenC (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    OracleComp KeccakCalls Bool :=
  if h : pt.length = n then Pcs.pcsVerifier (Pcs.oodPoint n) (⟨root, ood, pt, v, h⟩, p) else pure false

/-- `verify_claim` makes at most `10122` queries (F2's `variantQueries`). -/
theorem isTotalQueryBound_pcsVerifier {n : ℕ} (zOf : Digest → Vector E n) (w : Pcs.Claim1 n × Proof) :
    IsTotalQueryBound (Pcs.pcsVerifier zOf w) 10122 := by
  rw [Pcs.pcsVerifier_eq]
  by_cases hn : Pcs.minVars ≤ n ∧ n ≤ Pcs.maxVars
  · simp only [hn, and_self, ↓reduceIte]
    by_cases hc : rootOf w.2 = some w.1.root
    · simp only [hc, ↓reduceIte]
      rw [← Pcs.verifierFam_seeds_eq (R := logInvRate), ← variantQueries_eq]
      exact Pcs.isTotalQueryBound_seeds zOf w
    · simp only [hc, ↓reduceIte]
      simp only [Pcs.seedComp1, callKeccak256, callKeccakF1600, bind_assoc]
      refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => ?_⟩
      exact isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩
  · simp only [hn, ↓reduceIte]
    trivial

theorem isTotalQueryBound_pcsOpenC (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E)
    (p : Compile.Proof) : IsTotalQueryBound (pcsOpenC n root ood pt v p) 10122 := by
  unfold pcsOpenC
  split
  · exact isTotalQueryBound_pcsVerifier _ _
  · trivial

/-- **`verify_claim` follows the duplex discipline.** -/
theorem duplexVm_pcsVerifier {n : ℕ} (zOf : Digest → Vector E n) (w : Pcs.Claim1 n × Proof) :
    LeanVM.Rpm.DuplexVm (Pcs.pcsVerifier zOf w) [] := by
  rw [LeanVM.Rpm.duplexVm_iff_duplexP]
  unfold Pcs.pcsVerifier Pcs.pcsVerifyWithHash
  split_ifs
  · refine ((LeanVM.Rpm.hOnly_queryH _).duplexP []).bind fun iv h' hh => ?_
    subst hh
    exact (LeanVM.Rpm.duplexP_queryF_bind _ _ _ _).mpr
      ⟨LeanVM.Rpm.admissibleVm_seedInput _ _ _, fun seed =>
        LeanVM.Rpm.duplexP_runProof _ List.mem_cons_self _⟩
  · refine ((LeanVM.Rpm.hOnly_queryH _).duplexP []).bind fun iv h' hh => ?_
    subst hh
    exact (LeanVM.Rpm.duplexP_queryF_bind _ _ _ _).mpr
      ⟨LeanVM.Rpm.admissibleVm_seedInput _ _ _, fun seed => trivial⟩
  · trivial

theorem duplexVm_pcsOpenC (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    LeanVM.Rpm.DuplexVm (pcsOpenC n root ood pt v p) [] := by
  unfold pcsOpenC
  split
  · exact duplexVm_pcsVerifier _ _
  · trivial

/-- **`verify_claim`'s queries are short**: its IV hashes the claim's `82 + 24 n ≤ 754` bytes, then the program's. -/
theorem allQ_pcsVerifier {n : ℕ} (zOf : Digest → Vector E n) (w : Pcs.Claim1 n × Proof) :
    AllQueriesSatisfy (Pcs.pcsVerifier zOf w) LeanVM.Rpm.Short := by
  rw [Pcs.pcsVerifier_eq]
  by_cases hn : Pcs.minVars ≤ n ∧ n ≤ Pcs.maxVars
  · simp only [hn, and_self, ↓reduceIte]
    rw [Pcs.seedComp1]
    refine allQueriesSatisfy_bind (allQueriesSatisfy_bind (LeanVM.Rpm.allQ_queryH ?_)
      fun _ => LeanVM.Rpm.allQ_queryF _) fun seed => ?_
    · rw [Pcs.claimBytes_length]
      have := hn.2
      unfold Pcs.maxVars at this
      omega
    · by_cases hr : rootOf w.2 = some w.1.root
      · simp only [hr, ↓reduceIte]
        exact LeanVM.Rpm.allQ_runProof _ seed _ (Soundness.widthsLE_variantProg _ _ _)
      · simp only [hr, ↓reduceIte]
        trivial
  · simp only [hn, ↓reduceIte]
    trivial

theorem allQ_pcsOpenC (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    AllQueriesSatisfy (pcsOpenC n root ood pt v p) LeanVM.Rpm.Short := by
  unfold pcsOpenC
  split
  · exact allQ_pcsVerifier _ _
  · trivial

/-- `verify_claim`, run with any answers to the two calls, is `pcsVerifyWithHash` with those answers. -/
theorem simulateQ_pcsVerifier {r : Type → Type} [Monad r] [LawfulMonad r]
    (impl : QueryImpl LeanVM.KeccakCalls r) {n : ℕ} (zOf : Digest → Vector E n) (x : Pcs.Claim1 n)
    (π : Proof) :
    simulateQ impl (Pcs.pcsVerifier zOf (x, π)) =
      Pcs.pcsVerifyWithHash (Compile.Rom.implH impl) (Compile.Rom.implF impl) zOf x π := by
  unfold Pcs.pcsVerifier Pcs.pcsVerifyWithHash
  by_cases hn : Pcs.minVars ≤ n ∧ n ≤ Pcs.maxVars
  · simp only [hn, and_self, ↓reduceIte]
    simp only [simulateQ_bind, Compile.Rom.simulateQ_queryH, Compile.Rom.simulateQ_queryF]
    refine bind_congr fun iv => bind_congr fun seed => ?_
    by_cases hr : rootOf π = some x.root
    · simp only [hr, ↓reduceIte]
      exact Compile.Rom.simulateQ_runProof impl _ _ _
    · simp only [hr, ↓reduceIte]
      simp
  · simp only [hn, ↓reduceIte]
    simp

/-- **The verifier's opening over `π` is `pcsOpenC` answered over `π`.** -/
theorem pcsOpenK_eq (n : ℕ) (root : Digest) (ood : E) (pt : List E) (v : E) (p : Compile.Proof) :
    pcsOpenK Common.queryPermutation n root ood pt v p =
      simulateQ keccakCallsOverQueryPermutation (pcsOpenC n root ood pt v p) := by
  unfold pcsOpenK pcsOpenC
  split
  · rw [simulateQ_pcsVerifier]
    rfl
  · simp

/-! ## The sizes -/

/-- **Size `n` of version 1 at `εExact`**, for `23 ≤ n ≤ 28`: the deployed codes meet `269 · 2^-137` per group
above the batching lead (`whirEps_le_exact`, at `2^23` `whirEps_le_exact23`), `10122` queries. -/
noncomputable def pcsShapeK (n : ℕ) (h1 : 23 ≤ n) (h2 : n ≤ 28) : Pcs.PcsShape εExact where
  n := n
  lo := by unfold Pcs.minVars; omega
  hi := by unfold Pcs.maxVars; omega
  hε c hc := by
    rcases Nat.lt_or_ge n 24 with h | h
    · obtain rfl : n = 23 := by omega
      exact whirEps_le_exact23 hc
    · exact whirEps_le_exact h h2 hc
  hB J hJ := by
    rcases Nat.lt_or_ge n 24 with h | h
    · obtain rfl : n = 23 := by omega
      exact eBatch_le_exact23 hJ
    · exact eBatch_le_exact h h2 hJ
  QO := 10122
  queries zOf w := by
    rw [← variantQueries_eq]
    exact Pcs.isTotalQueryBound_seeds zOf w

/-- **Version 1's sizes `2^23 ..= 2^28`**, distinct. -/
noncomputable def pcsKShapes : Pcs.PcsShapes εExact where
  shs := [pcsShapeK 24 (by norm_num) (by norm_num), pcsShapeK 25 (by norm_num) (by norm_num),
    pcsShapeK 26 (by norm_num) (by norm_num), pcsShapeK 27 (by norm_num) (by norm_num),
    pcsShapeK 28 (by norm_num) (by norm_num), pcsShapeK 23 (by norm_num) (by norm_num)]
  nodup := by decide

theorem pcsKShapes_length : pcsKShapes.shs.length = 6 := rfl

/-- **Size `n`'s index** in `pcsKShapes`. -/
def pcsIdxK (n : ℕ) : Fin pcsKShapes.shs.length := ⟨if n = 23 then 5 else min (n - 24) 4, by
  rw [pcsKShapes_length]; split <;> omega⟩

theorem pcsIdxK_n (n : ℕ) (h1 : 23 ≤ n) (h2 : n ≤ 28) : (pcsKShapes.shs.get (pcsIdxK n)).n = n := by
  interval_cases n <;> rfl

theorem pcsKShapes_QO : ∀ s ∈ pcsKShapes.shs, s.QO ≤ 10122 := by
  intro s hs
  simp only [pcsKShapes, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> exact le_rfl

/-! ## A verifier on a map of its statements -/

/-- **A verifier on a map of its statements**: if `V a` is `V' (f a)` where `ok a` holds and rejects elsewhere, then
`V` accepting while `bad` holds is at most as likely as `V'` on the mapped adversary accepting while `bad'` holds,
for `bad` implying `bad'` along `f` where `ok` holds. -/
theorem romExperiment_le_map {α β : Type} (A : OracleComp KeccakCalls α)
    (V : α → OracleComp KeccakCalls Bool) (V' : β → OracleComp KeccakCalls Bool) (f : α → β)
    (ok : α → Prop) [DecidablePred ok] (hV : ∀ a, V a = if ok a then V' (f a) else pure false)
    (bad : α → KeccakCalls.QueryCache → Prop) (bad' : β → KeccakCalls.QueryCache → Prop)
    (himp : ∀ a c, ok a → bad a c → bad' (f a) c) :
    Pr{let z ← romExperiment A V}[z.1.2 = true ∧ bad z.1.1 z.2] ≤
      Pr{let z ← romExperiment (f <$> A) V'}[z.1.2 = true ∧ bad' z.1.1 z.2] := by
  rw [romExperiment_map, prEvent_map, romExperiment_eq, romExperiment_eq]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun p ↦ ?_
  rw [prEvent_map, prEvent_map, hV]
  by_cases hok : ok p.1
  · simp only [hok, ↓reduceIte]
    exact prEvent_mono _ _ _ fun r hr ↦ ⟨hr.1, himp _ _ hok hr.2⟩
  · simp only [hok, ↓reduceIte]
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun r hr hev ↦ ?_) bot_le
    rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    rw [hr] at hev
    exact Bool.false_ne_true hev.1

end UniKeccakSound
