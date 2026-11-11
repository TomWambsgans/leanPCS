-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- The deployed opening of this repository's `formal/WhirBridge/WhirBridge/PcsOracle.lean` (`pcsVerifierO`,
-- `PcsDoomedO`, `pcs_sound_oracle`) as an `OpenSpec`; the costs are leanerVM `mumbai`'s
-- (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0: `isTotalQueryBound_runProof`).
import SoundPcs.Deployed
import WhirBridge.PcsOracle

/-!
# The deployed opening

Version 1's opening with the out-of-domain point read off Keccak-256 by the verifier (`WhirBridge.Pcs.pcsVerifierO`,
`crates/pcs_claim/src/lib.rs`'s `verify_claim`, the Statement's `pcsOpeningWith` over a hash and a permutation),
its doom `PcsDoomedO` (the point read off the cache, `zOfCache`) and its soundness `pcs_sound_oracle`
(`openingBound QA`) make the `OpenSpec` of the deployed composition (`pcsOpen`):

* **`pcsVerifierO_queryBound`**: an opening asks at most `10150` queries: the seed's two, the out-of-domain
  point's `n ≤ 28`, the program's `10120` (`costLE_variant`);
* **`pcsVerifierO_asks`**: an accepting opening asks the out-of-domain inputs of its root;
* the doom reads Keccak-256's answers only, and an undoomed opening has a candidate satisfying both claims, the
  point `zOfCache` being `oodPointWith` of the cache's answers.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace SoundPcs

open Compose LeanVM LeanVM.Protocol LeanVM.Semantics LeanVM.Parameters LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd WhirBridge WhirBridge.Pcs LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-- The verifier's out-of-domain point over Keccak-256 is `oodPointO`. -/
theorem oodPointM_eq (n : ℕ) (r : Digest) : oodPointM callKeccak256 n r = oodPointO n r := by
  unfold oodPointM oodPointO coordQ
  congr 1

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
    obtain ⟨as, has, hz⟩ := hz
    rw [mem_support_pure_iff] at hz
    subst hz
    rw [List.length_cons, List.length_cons, length_of_mem_support_mapM f l as has]

/-- **An opening asks at most `10150` queries.** -/
theorem pcsVerifierO_queryBound {n : ℕ} (w : Claim1 n × Proof) :
    IsTotalQueryBound (pcsVerifierO w) 10150 := by
  unfold pcsVerifierO pcsVerifyWithHashO
  split_ifs with hn hr
  rotate_left
  · simp only [callKeccak256, callKeccakF1600]
    refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun iv => ?_⟩
    exact isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun _ => trivial⟩
  · trivial
  simp only [callKeccak256, callKeccakF1600]
  refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun iv => ?_⟩
  refine isTotalQueryBound_query_bind_iff.mpr ⟨by norm_num, fun seed => ?_⟩
  have hz : ∀ z ∈ support (oodPointM callKeccak256 n w.1.root),
      IsTotalQueryBound (runProofWithHash callKeccak256 callKeccakF1600 (prog n logInvRate z w.1) seed w.2)
        ((2 + (4 + (2 + whirBound))) / 4) := by
    intro z hzs
    rw [oodPointM_eq] at hzs
    have hl : z.length = n := by
      have := length_of_mem_support_mapM (coordQ n w.1.root) (List.range n) z hzs
      rwa [List.length_range] at this
    have hv : (⟨z.toArray, by simp [hl]⟩ : Vector E n).toList = z := by simp
    rw [← hv, prog_eq]
    exact isTotalQueryBound_runProof (costLE_variant (stacking n) logInvRate _) seed w.2
  have hb := isTotalQueryBound_bind_of_mem_support
    (by rw [oodPointM_eq]; exact oodPointO_queryBound n w.1.root) hz
  refine hb.mono ?_
  have hn' : n ≤ 28 := hn.2
  have hw : (2 + (4 + (2 + whirBound))) / 4 = 10120 := by
    have := variantQueries_eq
    unfold variantQueries at this
    omega
  omega

/-- **An accepting opening asks the out-of-domain inputs of its root.** -/
theorem pcsVerifierO_asks {n : ℕ} (w : Claim1 n × Proof) (T : KTable)
    (h : evalWithAnswerFn (QueryImpl.ofFn T) (pcsVerifierO w) = true) (j : Fin n) :
    (Sum.inl (oodInput n w.1.root j) : List UInt8 ⊕ KeccakState) ∈
      (tableQueryLog (pcsVerifierO w) T).map Sigma.fst := by
  unfold pcsVerifierO pcsVerifyWithHashO at h ⊢
  split_ifs at h ⊢ with hn hr
  · simp only [callKeccak256, callKeccakF1600] at h ⊢
    rw [tableQueryLog_query_bind, tableQueryLog_query_bind]
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
    rw [tableQueryLog_bind, List.map_append]
    refine List.mem_append_left _ ?_
    rw [oodPointM_eq, (oodPointO_run T n w.1.root).1]
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr j.isLt, rfl⟩
  · simp [callKeccak256, callKeccakF1600] at h
  · simp at h

/-- **The deployed opening, as an `OpenSpec`.** -/
def pcsOpen : OpenSpec where
  V _ := pcsVerifierO
  Doom _ := PcsDoomedO
  QO := 10150
  queryBound _ w := pcsVerifierO_queryBound w
  sound _ h1 h2 A QA hA := pcs_sound_oracle h1 h2 A QA hA
  readsInl n w c c' h := by
    simp only [PcsDoomedO, zOfCache, h]
  undoomed n w c hd _ := by
    simp only [PcsDoomedO, not_forall, not_or, not_not] at hd
    obtain ⟨q, hq, h1, h2⟩ := hd
    exact ⟨q, hq, h2, h1⟩
  asks n w T h j := pcsVerifierO_asks w T h j

end SoundPcs
