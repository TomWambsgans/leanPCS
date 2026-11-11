-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The contract's calls are `formal/RecStatement`'s
-- (`Calls.lean`: `pcsCalls`, `claimWords`; `Security.lean`: `claimOfWords`, `pcsOpenWords`); the words' read-backs
-- are `RecCompose.Pi1Decode`'s (`elementOfWord_elementWord`, `mapM_elementOfWord`, `digestOfBytes32_rootWord`,
-- `digestOfBytes32_digestBytes`).
import RecCompose.Pi1Decode
import RecCompose.OpeningsAgree
import RecCompose.Pi2Whir
import UniKeccakComplete.K.VerifierHCost
import UniKeccakComplete.K.ProverCost
import E2ECompleteness.Grinding

/-!
# π2's five claims decoded

The contract's last five claims (`pcsCalls`: `W`'s, the setup's, `Q`'s identity, pushes' and sum claims) are each a PCS
claim's words: the root's 32 bytes, the out-of-domain answer's element word, the point's coordinates and the value as
element words (`claimWords`). They decode (`claimOfWords`) to the root those bytes name, the answer, the point and the
value (**`claimOfWords_claim`**). A root the stream carries as the prover sends it (`rootHalves`, its bytes as they
are) names the digest (**`rootOfWord_rootWord_rootHalves`**); the setup's root, the constant's 32 bytes, too
(`rootOfWord_digestBytes`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose.Pi2C

open RecStatement LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Pi1Decode (elementOfWord_elementWord mapM_elementOfWord)

/-! ## Claims' words -/

theorem length_claimWords (c : List E × E) : (claimWords c).length = c.1.length + 1 := by
  simp [claimWords]

theorem claimWords_getD_lt (x : List E × E) {j : ℕ} (hj : j < x.1.length) :
    (claimWords x).getD j [] = UniStatement.elementWord (x.1.getD j 0) := by
  have hj' : j < (x.1.map UniStatement.elementWord).length := by simpa using hj
  rw [claimWords, List.map_append, List.getD_eq_getElem?_getD, List.getElem?_append_left hj', List.getElem?_map,
    List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
  rfl

theorem claimWords_getD_last (x : List E × E) : (claimWords x).getD x.1.length [] = UniStatement.elementWord x.2 := by
  simp [claimWords, List.getD_eq_getElem?_getD]

/-- **A PCS claim's words read back**: the root's 32 bytes, the answer's word, then `claimWords` of the claim decode to
the root the bytes name, the answer, the point and the value. -/
theorem claimOfWords_claim (rootB : List UInt8) (hr : rootB.length = 32) (ood : E) (c : List E × E) :
    claimOfWords ([rootB, UniStatement.elementWord ood] ++ claimWords c) = some (rootOfWord rootB, ood, c.1, c.2) := by
  obtain ⟨pt, v⟩ := c
  set W : List (List UInt8) := [rootB, UniStatement.elementWord ood] ++ claimWords (pt, v) with hW
  unfold claimOfWords
  have h0 : W.head? = some rootB := rfl
  have h1 : W[1]? = some (UniStatement.elementWord ood) := rfl
  have hl : W.getLast? = some (UniStatement.elementWord v) := by
    rw [hW, List.getLast?_append, claimWords, List.map_append, List.getLast?_append]
    simp
  have hd : (W.drop 2).dropLast = pt.map UniStatement.elementWord := by simp [hW, claimWords]
  have hc : (3 ≤ W.length ∧ rootB.length = 32) := ⟨by simp [hW, claimWords], hr⟩
  have hm : pt.mapM (elementOfWord ∘ UniStatement.elementWord) = some pt := by
    rw [← mapM_elementOfWord pt, List.mapM_map]
  simp [h0, h1, hl, hd, hc, elementOfWord_elementWord, hm]

/-! ## Roots -/

/-- **A root the stream carries as the prover sends it names the digest** (`rootHalves`: its bytes as they are). -/
theorem rootOfWord_rootWord_rootHalves (d : Digest) : rootOfWord (UniStatement.rootWord (UniStatement.rootHalves d)) = d := by
  unfold rootOfWord
  rw [digestOfBytes32_rootWord, UniComplete.rootOf_rootHalves]

/-- **The setup's root word names the setup's root** (its 32 bytes as they are). -/
theorem rootOfWord_digestBytes (d : Digest) : rootOfWord (digestBytes d) = d := digestOfBytes32_digestBytes d

theorem length_rootWord (h : E × E) : (UniStatement.rootWord h).length = 32 := by
  simp [UniStatement.rootWord, UniStatement.be64]

/-- The stream's 32 bytes at the end of a prefix. -/
theorem streamWord_of (S : Array UInt8) (P B Q : List UInt8) (hS : S.toList = P ++ (B ++ Q)) (hB : B.length = 32) :
    streamWord S P.length = B := by
  unfold streamWord
  rw [Array.toList_extract, hS, List.extract_eq_take_drop, List.drop_left, Nat.add_sub_cancel_left]
  exact List.take_left' hB

end RecCompose.Pi2C

/-- info: 'RecCompose.Pi2C.claimOfWords_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2C.claimOfWords_claim

/-- info: 'RecCompose.Pi2C.rootOfWord_rootWord_rootHalves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2C.rootOfWord_rootWord_rootHalves
