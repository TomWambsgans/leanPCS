-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The transfer is
-- `formal/Compose/Compose/ListChainKRpmS.lean`'s `rpm_le_kcS`, the two-oracle theorem
-- `ListChainUDoom.lean`'s `knowledgeSoundness_listChainU_closed`.
import UniSound.FsCost
import Soundness.TreeLog
import Bridge.Chain

/-!
# The Fiat–Shamir layer's pieces for the contract's IV computed by the verifier

`FsProof.lean`'s coupling with the composed random-permutation game whose adversary computes the contract's IV
would put the IV's calls of `π` in the adversary's log, which the composed extractor replays
(`keccakEvaluationsOfTranscript`): a fresh IV answer extends sponge paths the univariate extractor, reading the
adversary's log alone, never sees, so that coupling fails event by event by a margin near `2^-230`. The Keccak
verifier's layers (`UniKeccakSound.Fs.GameK`, `GameK3`) compute the IV **by the verifier** instead, then move it into
the two-oracle adversary; this file has the pieces they share:

* the proof with an IV (`setIv`, `ivOut`) and the setup's root as the proof records it (`rootsOfS`);
* **`extractorK_append`**: a log entry of neither a Merkle node's `64` bytes nor a leaf's length leaves `C1`'s
  extractor's word unchanged (the IV's entry);
* `logImplKC_bind`, and **`le_uniBoundV`**: the composed bound with the IV in the verifier is at most `uniBound`.
-/

namespace UniSound

open Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge UniStatement
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState UniStatement.setupStack

/-! ## The contract's IV -/

theorem length_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  rw [← Bridge.toB_toList]
  simp

theorem length_ivTag : ivTag.length = 16 := by decide +kernel

theorem length_shapeBytes (s : UniStatement.Shape) : (shapeBytes s).length = 8 := by
  simp [shapeBytes]

theorem length_layoutWord (s : UniStatement.Shape) (code vars placed : ℕ) :
    (layoutWord s code vars placed).length = 32 := by
  simp [layoutWord, length_shapeBytes]

/-- The proof with an IV. -/
def setIv (iv : Vector UInt8 32) (π : UPf) : UPf := { π with iv := iv }

/-- The setup's root as the proof records it: the setup tree's root, one 32-byte word. -/
def rootsOfS (s : Bytes32) : SetupRoots := ⟨ofB s⟩

/-- The outcome with the IV written in the proof. -/
def ivOut (z : UPf × (Bytes32 × (List (List E) × List Bool))) : UPf × (List (List E) × List Bool) :=
  (setIv z.2.1 z.1, z.2.2)

/-! ## An entry of no Merkle length leaves the extractor's word -/

theorem below_insert (H : Hist) (T T' : QuotientRpm.Table) (x d : List UInt8) (n : ℕ) (hn : x.length ≠ n)
    (hT : ∀ z ∈ H, T' z = T z) : below (insert x H) T' d n = below H T d n := by
  unfold below
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hz, h1, h2⟩
    · exact absurd h2 hn
    · exact ⟨hz, by rw [← hT z hz]; exact h1, h2⟩
  · rintro ⟨hz, h1, h2⟩
    exact ⟨Or.inr hz, by rw [hT z hz]; exact h1, h2⟩

theorem leafAt_insert (H : Hist) (T T' : QuotientRpm.Table) (x : List UInt8) (leafLen : ℕ)
    (h64 : x.length ≠ 64) (hl : x.length ≠ leafLen) (hT : ∀ z ∈ H, T' z = T z) :
    ∀ (k : ℕ) (d : List UInt8) (bs : List Bool),
      leafAt (insert x H) T' leafLen k d bs = leafAt H T leafLen k d bs
  | 0, d, _ => below_insert H T T' x d leafLen hl hT
  | _ + 1, _, [] => rfl
  | k + 1, d, b :: bs => by
    simp only [leafAt, below_insert H T T' x d 64 h64 hT]
    congr 1
    funext y
    exact leafAt_insert H T T' x leafLen h64 hl hT k _ bs

theorem histOfTr_append_single (tr : Transcript) (e : List UInt8 × Bytes32) :
    histOfTr (tr ++ [e]) = insert e.1 (histOfTr tr) := by
  ext z
  simp [histOfTr]

theorem tableOfTr_append_single (tr : Transcript) (e : List UInt8 × Bytes32) (z : List UInt8)
    (hz : z ∈ histOfTr tr) : tableOfTr (tr ++ [e]) z = tableOfTr tr z := by
  unfold tableOfTr
  obtain ⟨a, ha, rfl⟩ : ∃ a ∈ tr, a.1 = z := by
    simpa [histOfTr] using hz
  have hs : (tr.find? fun e => decide (e.1 = a.1)).isSome :=
    List.find?_isSome.mpr ⟨a, ha, by simp⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
  rw [List.find?_append, hb]
  rfl

/-- **The extractor reads the same word** after a transcript entry of neither a node's nor a leaf's
length. -/
theorem extractorK_append {Pf F M St β : Type} (tc : ℕ → TableCode M)
    (view : Pf → St × List (RMsg F)) (z : Pf × (List (List F) × β)) (tr : Transcript)
    (e : List UInt8 × Bytes32) (h64 : e.1.length ≠ 64) (hl : e.1.length ≠ (tc 0).leafLen) :
    extractorK (fun i => (tc i).commit) view (z, tr ++ [e]) =
      extractorK (fun i => (tc i).commit) view (z, tr) := by
  show optC ((tc 0).commit) (histOfTr (tr ++ [e])) (tableOfTr (tr ++ [e])) (msgK view z.1 0) =
    optC ((tc 0).commit) (histOfTr tr) (tableOfTr tr) (msgK view z.1 0)
  unfold optC
  split
  · next r _ =>
    show ((tc 0).dec (merkleWord _ _ _ _ r)).map some = ((tc 0).dec (merkleWord _ _ _ _ r)).map some
    congr 2
    funext p
    unfold merkleWord
    rw [histOfTr_append_single]
    exact leafAt_insert _ _ _ _ _ h64 hl (fun y hy => tableOfTr_append_single tr e y hy) _ _ _
  · rfl

/-! ## The IV moved into the adversary, in the two-oracle game -/

theorem logImplKC_bind {α β : Type} (oa : OracleComp KeccakCalls α)
    (f : α → OracleComp KeccakCalls β) (l : Transcript) :
    (simulateQ logImplKC (oa >>= f)).run l =
      (simulateQ logImplKC oa).run l >>= fun p => (simulateQ logImplKC (f p.1)).run p.2 := by
  rw [simulateQ_bind, StateT.run_bind]

/-! ## The bound -/

/-- **The composed bound, the IV in the verifier, is at most `uniBound`**: `le_uniBound` with the
adversary's `Q + 8` calls and `2^80` verifier calls traded for `Q + 1` Keccak-256 calls of the
two-oracle adversary and `2^80 + 8` verifier calls. -/
theorem le_uniBoundV (e : ℝ≥0∞) (Q QS nQ SQO nRf : ℕ) (hQS : QS ≤ 3 * 2 ^ 24) (hnQ : nQ ≤ 2 ^ 10)
    (hSQO : SQO ≤ 5 * 10122) (hr : nRf ≤ 6) (d m t : ℝ≥0∞)
    (hd : d ≤ 5 * openingBoundAt 10122 (uniN Q)) (hm : m ≤ ((9952 ^ 2 : ℕ) : ℝ≥0∞) * e)
    (ht : t = ((256 ^ 16 : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    d + ((QS + (QS + Q + 1) + nQ + SQO : ℕ) : ℝ≥0∞) *
        (m + t + (((nRf + 2) * (QS + (QS + Q + 1) + nQ + SQO) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
      ((QS * 2 ^ 32 + Q + (2 ^ 80 + 8) : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 508 ≤ uniBound e Q := by
  have hN : QS + (QS + Q + 1) + nQ + SQO ≤ QS + (QS + (Q + 8)) + nQ + SQO := by omega
  have hR : QS * 2 ^ 32 + Q + (2 ^ 80 + 8) = QS * 2 ^ 32 + (Q + 8) + 2 ^ 80 := by ring
  refine le_trans ?_ (le_uniBound e Q QS nQ SQO nRf hQS hnQ hSQO hr d m t hd hm ht)
  rw [hR]
  refine add_le_add (add_le_add le_rfl (mul_le_mul' (Nat.cast_le.mpr hN) ?_)) le_rfl
  exact add_le_add le_rfl (ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left _ hN)) _)

/-! ## The Fiat–Shamir layer -/

end UniSound

/-- info: 'UniSound.extractorK_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.extractorK_append
