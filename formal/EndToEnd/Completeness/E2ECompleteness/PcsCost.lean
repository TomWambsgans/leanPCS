-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Adapted from `E2ECompleteness/Cost.lean` (the previous protocol's block count) to the PCS claims:
-- its generic calculus (`QC`, `WordsLE`, `OWordsLE`, `cost_runFromWithHash`, `cost_runWithHash`,
-- `qc_buildTree`, `qc_openAll`) is copied, the protocol's parts rewritten.
-- Uses leanerVM (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0,
-- MIT OR Apache-2.0): the block cost `hashBlocks` and the weight calculus `Common.QueryCostAtMost`;
-- the cost calculus of the verifier's programs (`Prog.Costs`, `costs_verifyStackedOpening`,
-- `ladder_cost`, `costHeight`, `whirBound`); the widths of WHIR's commitments (`WidthsLE`,
-- `widthsLE_verifyWhir`, `ladder_folds`). The weighted bounds of the prover's runner and of the
-- verifier's run are adapted from mumbai's query counts (`isTotalQueryBound_proveFromM`,
-- `Compile/Rom/Prover.lean`; `allQ_run`, `allQ_openAll`, `Rpm/Cost.lean`).
import E2ECompleteness.PcsStaging
import E2ECompleteness.PcsOpening
import LeanVM.Protocol.Rpm.Cost
import LeanVM.Protocol.Verifier.Cost

/-!
# The block count of the staged run (the PCS claims)

**`hcost_deployed`**: the deployed staged run (`stagedRun`, `PcsStaging.lean`) makes at most `2^48`
block calls (`hashBlocks`: a Keccak-256 of `n` bytes costs `⌊n / 136⌋ + 1`, a Keccak-f[1600] one).

The cost is weighted, as in the previous protocol's `Cost.lean`:

* **Every hash is short.** The tables' Merkle leaves are `64` words (`512` bytes, `4` blocks),
  WHIR's at most `192` words (`1536` bytes, `12` blocks: `WordsLE` for the honest script
  `pcsOpeningScript`, from `ladder_folds`; `WidthsLE` for the verifier's program), the nodes `64`
  bytes, the out-of-domain inputs `46` bytes, the chain's inputs at most `320` bytes, the label
  `136` bytes, the openings' IVs (`pcsClaimBytes`) `82 + 24 · n` bytes for points of `n ≤ 28`
  coordinates (`claimsAt_len`; the verifier checks `n ≤ maxVars`).
* **The prover's runner** (`cost_runFromWithHash`): a program of cost `n` quarters
  (`Prog.Costs`) at height `h` costs at most `n · (13 · 2^h + 2 · fuel + 2)` blocks
  (`blockFactor`).
* **The verifier's run** (`cost_runWithHash`): at most `3 · n` blocks.
* **The stages** (`cost_stagedRunG`, generic in the setup, circuit and cells): the setup's
  commitment, the index, `W`, `H`, `Q`, `G` commitments (a tree of `5 · 2^(μ - 5)` blocks and `μ`
  out-of-domain hashes each, `comCost`), the chain's six hashes, the prover's reduction twice and the
  verifier's (`10` blocks each), the six openings proved (`pOpen`) and verified (`vOpen`).
  Instantiated at the deployed sizes (`cellVars 22 = 24`, `fuel = 2^25`); nothing of the deployed
  circuit is evaluated.

The total is `228 197 329 439 321 < 2^48` blocks, nearly all of it the six WHIR provers'
`6 · 40481 · (14 · 2^26 + 2)`.
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Rpm (hashBlocks)
open LeanVM.Prover (Tree Script)
open PcsQuotient PcsQuotient.Domain PcsQuotient.Transcript

set_option autoImplicit false

namespace E2ECompleteness.Pcs

namespace Cost

/-- At most `n` block calls. -/
abbrev QC {α : Type} (X : OracleComp KeccakCalls α) (n : ℕ) : Prop :=
  Common.QueryCostAtMost X hashBlocks n

/-! ## The calculus -/

theorem qc_pure {α : Type} (a : α) (n : ℕ) : QC (pure a : OracleComp KeccakCalls α) n := trivial

theorem QC.mono {α : Type} {X : OracleComp KeccakCalls α} {a b : ℕ} (h : QC X a) (hab : a ≤ b) :
    QC X b :=
  Common.QueryCostAtMost.mono h hab

theorem QC.bind {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    {a b : ℕ} (hX : QC X a) (hf : ∀ x, QC (f x) b) : QC (X >>= f) (a + b) :=
  Common.QueryCostAtMost.bind hX hf

theorem QC.bind_le {α β : Type} {X : OracleComp KeccakCalls α} {f : α → OracleComp KeccakCalls β}
    {a b c : ℕ} (hX : QC X a) (hf : ∀ x, QC (f x) b) (h : a + b ≤ c) : QC (X >>= f) c :=
  (hX.bind hf).mono h

theorem QC.map {α β : Type} {X : OracleComp KeccakCalls α} (f : α → β) {a : ℕ} (hX : QC X a) :
    QC (f <$> X) a :=
  Common.isWeightBound_map f hX

theorem qc_F (s : KeccakState) : QC (callKeccakF1600 s) 1 :=
  Common.isWeightBound_query hashBlocks (Sum.inr s)

theorem qc_H (x : Bytes) : QC (callKeccak256 x) (x.length / 136 + 1) :=
  Common.isWeightBound_query hashBlocks (Sum.inl x)

/-- A hash of at most `136 · k - 1` bytes costs at most `k` blocks. -/
theorem qc_H_le {x : Bytes} {k : ℕ} (hx : x.length < 136 * k) : QC (callKeccak256 x) k :=
  (qc_H x).mono (by omega)

/-! ## The sponge -/

theorem qc_duplex (sp : Sponge) : QC (duplex callKeccakF1600 sp) 1 :=
  ((qc_F _).bind fun _ ↦ qc_pure _ 0).mono le_rfl

theorem qc_absorb (sp : Sponge) (x : E) (tag : ℕ) :
    QC (Compile.absorb callKeccakF1600 sp x tag) 1 := by
  unfold Compile.absorb
  split
  · exact (qc_duplex sp).bind_le (fun _ ↦ qc_pure _ 0) le_rfl
  · exact (qc_pure _ 1).bind_le (fun _ ↦ qc_pure _ 0) le_rfl

theorem qc_squeeze (sp : Sponge) : QC (squeeze callKeccakF1600 sp) 1 :=
  (qc_duplex sp).bind_le (fun _ ↦ qc_pure _ 0) le_rfl

theorem qc_powStepM (sp : Sponge) (n : E) : QC (LeanVM.Prover.powStepM callKeccakF1600 sp n) 2 :=
  (qc_absorb _ _ _).bind_le (fun _ ↦ qc_squeeze _) le_rfl

theorem qc_searchM (bits : ℕ) (sp : Sponge) :
    ∀ (count n : ℕ), QC (LeanVM.Prover.searchM callKeccakF1600 bits sp n count) (2 * count)
  | 0, _ => trivial
  | count + 1, n => by
    simp only [LeanVM.Prover.searchM]
    refine (qc_powStepM _ _).bind_le (fun r ↦ ?_) (show 2 + 2 * count ≤ 2 * (count + 1) by omega)
    split
    · exact qc_pure _ _
    · exact qc_searchM bits sp count (n + 1)

theorem qc_findNonceM (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    QC (LeanVM.Prover.findNonceM callKeccakF1600 bits sp fuel) (2 * fuel) := by
  unfold LeanVM.Prover.findNonceM
  split
  · exact qc_pure _ _
  · exact qc_searchM _ _ _ _

/-! ## Merkle trees -/

theorem qc_listMapM {β γ : Type} (f : β → OracleComp KeccakCalls γ) (c : ℕ)
    (hf : ∀ a, QC (f a) c) : ∀ l : List β, QC (l.mapM f) (l.length * c)
  | [] => by rw [List.mapM_nil]; exact qc_pure _ _
  | a :: l => by
    rw [List.mapM_cons, List.length_cons]
    exact (hf a).bind_le (fun _ ↦ (qc_listMapM f c hf l).bind_le (fun _ ↦ qc_pure _ 0) le_rfl)
      (by rw [Nat.succ_mul]; omega)

theorem qc_arrayMapM {β γ : Type} (f : β → OracleComp KeccakCalls γ) (c : ℕ)
    (hf : ∀ a, QC (f a) c) (xs : Array β) : QC (xs.mapM f) (xs.size * c) := by
  rw [Array.mapM_eq_mapM_toList, ← Array.length_toList]
  exact (qc_listMapM f c hf _).map _

theorem qc_parents (level : Array Digest) (n : ℕ) :
    QC (LeanVM.Prover.parentsWithHash callKeccak256 level n) n := by
  unfold LeanVM.Prover.parentsWithHash
  refine (qc_arrayMapM _ 1 (fun j ↦ qc_H_le ?_) _).mono (by simp)
  rw [List.length_append, length_digestBytes, length_digestBytes]
  omega

theorem qc_levels : ∀ (k : ℕ) (level : Array Digest),
    QC (LeanVM.Prover.levelsWithHash callKeccak256 k level) (2 ^ k)
  | 0, _ => qc_pure _ _
  | k + 1, level => by
    simp only [LeanVM.Prover.levelsWithHash]
    exact (qc_parents _ _).bind_le (fun _ ↦ (qc_levels k _).bind_le (fun _ ↦ qc_pure _ 0)
      le_rfl) (by rw [pow_succ]; omega)

theorem length_flatMap_kBytes (row : List K) : (row.flatMap kBytes).length = 8 * row.length := by
  induction row with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [kBytes, LeanVM.Rpm.wordBytes_len]
    ring

/-- **A Merkle tree** of rows of fewer than `136 · c` bytes: `2^height` leaves of at most `c`
blocks, fewer than `2^height` nodes of one. -/
theorem qc_buildTree (height : ℕ) (word : Word) (c : ℕ)
    (hw : ∀ p, 8 * (word p).length < 136 * c) :
    QC (LeanVM.Prover.buildTreeWithHash callKeccak256 height word) ((c + 1) * 2 ^ height) := by
  unfold LeanVM.Prover.buildTreeWithHash LeanVM.Prover.leafDigestsWithHash
  refine (qc_arrayMapM _ c (fun i ↦ qc_H_le ?_) _).bind_le (fun _ ↦ (qc_levels _ _).bind_le
    (fun _ ↦ qc_pure _ 0) le_rfl) (by rw [Array.size_range]; ring_nf; omega)
  rw [length_flatMap_kBytes]
  exact hw i

theorem length_stackWordFast (μ R : ℕ) (stack : Array K) (p : ℕ) :
    (LeanVM.Prover.stackWordFast μ R stack p).length = 64 := by
  unfold LeanVM.Prover.stackWordFast LeanVM.Prover.stackWordFast.stackWordOf
  split <;> simp

/-- A table's tree: `2^(μ − 5)` leaves of `64` words (`4` blocks) and its nodes. -/
theorem qc_commitWithH (μ : ℕ) (stack : Array K) :
    QC (commitWithH callKeccak256 μ stack) (5 * 2 ^ (μ - 6 + 1)) :=
  qc_buildTree _ _ 4 fun p ↦ by rw [length_stackWordFast]; omega

/-! ## The out-of-domain points and the commitments -/

theorem length_oodInput (n : ℕ) (root : Digest) (j : ℕ) : (oodInput n root j).length = 46 := by
  have h11 : oodTag.length = 11 := by decide +kernel
  simp only [oodInput, List.length_append, h11, length_digestBytes, List.length_cons,
    List.length_nil]

/-- **The out-of-domain point** of `n` coordinates: `n` hashes of `46` bytes. -/
theorem qc_oodPointWithH (n : ℕ) (root : Digest) : QC (oodPointWithH callKeccak256 n root) n := by
  unfold oodPointWithH
  refine (qc_listMapM _ 1 (fun j ↦ (qc_H_le (k := 1) ?_).bind_le (fun _ ↦ qc_pure _ 0) le_rfl)
    _).mono (by simp)
  rw [length_oodInput]; omega

/-- The block cost of a table's commitment on `2^μ` words: its tree and its out-of-domain point. -/
def comCost (μ : ℕ) : ℕ := 5 * 2 ^ (μ - 6 + 1) + μ

theorem qc_commitmentWithH (μ : ℕ) (table : Array K) :
    QC (commitmentWithH callKeccak256 μ table) (comCost μ) := by
  unfold commitmentWithH comCost
  exact (qc_commitWithH _ _).bind_le (fun _ ↦ (qc_oodPointWithH _ _).bind_le
    (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl

/-! ## The honest script commits rows of at most `192` words -/

/-- Every matrix the script commits has rows of at most `W` words. -/
def WordsLE (W : ℕ) {β : Type} : Script β → Prop
  | .ret _ => True
  | .send _ k => WordsLE W k
  | .sample k => ∀ c, WordsLE W (k c)
  | .grind k => WordsLE W k
  | .commit w k => (∀ p, (w p).length ≤ W) ∧ WordsLE W k
  | .query k => ∀ rows, WordsLE W (k rows)

namespace WordsLE

variable {W : ℕ} {β γ : Type}

theorem bind {x : Script β} {f : β → Script γ} (hx : WordsLE W x) (hf : ∀ a, WordsLE W (f a)) :
    WordsLE W (x >>= f) := by
  show WordsLE W (x.bind f)
  induction x with
  | ret a => exact hf a
  | send y k ih => exact ih hx
  | sample k ih => exact fun c ↦ ih c (hx c)
  | grind k ih => exact ih hx
  | commit w k ih => exact ⟨hx.1, ih hx.2⟩
  | query k ih => exact fun rows ↦ ih rows (hx rows)

theorem ret' (a : β) : WordsLE W (pure a : Script β) := trivial

theorem sendE (x : E) : WordsLE W (Script.sendE x) := trivial

theorem sendList : ∀ xs : List E, WordsLE W (Script.sendList xs)
  | [] => trivial
  | _ :: xs => sendList xs

theorem sampleE : WordsLE W Script.sampleE := fun _ ↦ trivial

theorem sampleN : ∀ n : ℕ, WordsLE W (Script.sampleN n)
  | 0 => trivial
  | n + 1 => bind sampleE fun _ ↦ bind (sampleN n) fun _ ↦ trivial

theorem grindS : WordsLE W Script.grindS := trivial

theorem queryS : WordsLE W Script.queryS := fun _ ↦ trivial

theorem commitS {w : Word} (hw : ∀ p, (w p).length ≤ W) : WordsLE W (Script.commitS w) :=
  ⟨hw, trivial⟩

end WordsLE

theorem wordsLE_roundA {W : ℕ} (claim : E) (Wt g : Array E) :
    WordsLE W (LeanVM.Prover.roundA claim Wt g) :=
  WordsLE.bind (WordsLE.sendE _) fun _ ↦ WordsLE.bind (WordsLE.sendList _) fun _ ↦ trivial

theorem wordsLE_foldRoundsA {W : ℕ} :
    ∀ (n : ℕ) (s : WhirState) (lf : List E) (Wt gt : Array E),
      WordsLE W (LeanVM.Prover.foldRoundsA n s lf Wt gt)
  | 0, _, _, _, _ => trivial
  | n + 1, s, lf, Wt, gt => by
    simp only [LeanVM.Prover.foldRoundsA]
    exact WordsLE.bind WordsLE.sampleE fun _ ↦ WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦
      wordsLE_foldRoundsA n _ _ _ _

theorem wordsLE_tailRoundsA {W : ℕ} :
    ∀ (n : ℕ) (quad : List E) (Wt gt : Array E),
      WordsLE W (LeanVM.Prover.tailRoundsA n quad Wt gt)
  | 0, _, _, _ => trivial
  | n + 1, quad, Wt, gt => by
    simp only [LeanVM.Prover.tailRoundsA]
    refine WordsLE.bind WordsLE.sampleE fun c ↦ ?_
    split
    · trivial
    · exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦ wordsLE_tailRoundsA n _ _ _

theorem wordsLE_sampleQueriesS {W : ℕ} (depth : ℕ) :
    ∀ (fuel remaining : ℕ), WordsLE W (LeanVM.Prover.sampleQueriesS depth fuel remaining)
  | 0, _ => trivial
  | fuel + 1, remaining => by
    simp only [LeanVM.Prover.sampleQueriesS]
    split
    · trivial
    · exact WordsLE.bind WordsLE.sampleE fun _ ↦
        WordsLE.bind (wordsLE_sampleQueriesS depth fuel _) fun _ ↦ trivial

theorem length_levelWordFast (κ k R : ℕ) (g : Array E) (p : ℕ) :
    (LeanVM.Prover.levelWordFast κ k R g p).length = 3 * 2 ^ k := by
  unfold LeanVM.Prover.levelWordFast LeanVM.Prover.levelWordFast.levelWordOf
  split
  · simp [List.length_flatMap, mul_comm]
  · simp [LeanVM.Protocol.Whir.Complete.levelWord, LeanVM.Protocol.Whir.Complete.laneCodes,
      LeanVM.Protocol.Whir.Complete.limbsOf, List.length_flatMap, Function.comp_def,
      List.sum_replicate, mul_comm]

/-- **The WHIR levels commit rows of at most `192` words** when every level folds at most `6`
variables (`3 · 2^fold` words a row). -/
theorem wordsLE_levelsA (μ : ℕ) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (Wt gt : Array E),
      (∀ l ∈ levels, l.fold ≤ 6) → WordsLE 192 (LeanVM.Prover.levelsA μ index levels s Wt gt) := by
  intro levels
  induction levels with
  | nil => intros; trivial
  | cons level rest ih =>
    intro index s Wt gt hf
    cases rest with
    | nil =>
      rw [LeanVM.Prover.levelsA]
      refine WordsLE.bind (wordsLE_foldRoundsA _ _ _ _ _) fun ⟨s', lf, Wt', g'⟩ ↦ ?_
      dsimp only
      refine WordsLE.bind (WordsLE.sendList _) fun _ ↦
        WordsLE.bind (WordsLE.ret' _) fun ⟨r, pd, tb⟩ ↦ ?_
      dsimp only
      refine WordsLE.bind WordsLE.grindS fun _ ↦ ?_
      refine WordsLE.bind (wordsLE_sampleQueriesS _ _ _) fun _ ↦ ?_
      refine WordsLE.bind WordsLE.sampleE fun _ ↦ ?_
      refine WordsLE.bind WordsLE.queryS fun _ ↦ ?_
      exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦ wordsLE_tailRoundsA _ _ _ _
    | cons next rest =>
      have hn : next.fold ≤ 6 := hf next (by simp)
      rw [LeanVM.Prover.levelsA]
      refine WordsLE.bind (wordsLE_foldRoundsA _ _ _ _ _) fun ⟨s', lf, Wt', g'⟩ ↦ ?_
      dsimp only
      refine WordsLE.bind (WordsLE.commitS fun p ↦ ?_) fun _ ↦ ?_
      · rw [length_levelWordFast]
        have : 2 ^ next.fold ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
        omega
      refine WordsLE.bind (WordsLE.sampleN _) fun _ ↦ WordsLE.bind (WordsLE.sendE _) fun _ ↦
        WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦ WordsLE.bind (WordsLE.ret' _)
          fun ⟨r, pd, tb⟩ ↦ ?_
      dsimp only
      refine WordsLE.bind WordsLE.grindS fun _ ↦ ?_
      refine WordsLE.bind (wordsLE_sampleQueriesS _ _ _) fun _ ↦ ?_
      refine WordsLE.bind WordsLE.sampleE fun _ ↦ ?_
      refine WordsLE.bind WordsLE.queryS fun _ ↦ ?_
      exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦
        ih _ _ _ _ fun l hl ↦ hf l (List.mem_cons_of_mem _ hl)

/-- **The honest PCS opening script commits rows of at most `192` words** (`ladder_folds`). -/
theorem wordsLE_pcsOpeningScript (n : ℕ) (table : Array K) (z : List E) (c : Commitment)
    (claim : Claim) : WordsLE 192 (pcsOpeningScript n table z c claim) := by
  unfold pcsOpeningScript
  refine WordsLE.bind WordsLE.sampleE fun lam ↦ ?_
  split
  · trivial
  · rename_i config hc
    exact WordsLE.bind (wordsLE_roundA _ _ _) fun _ ↦
      wordsLE_levelsA _ _ _ _ _ _ (LeanVM.Rpm.ladder_folds _ _ _ hc)

/-! ## The prover's runner -/

/-- The runner's current node commits rows of at most `W` words. -/
def OWordsLE (W : ℕ) {β : Type} : Option (Script β) → Prop
  | none => True
  | some S => WordsLE W S

section OWords

variable {W : ℕ} {β : Type}

theorem oWordsLE_afterSend {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterSend S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> trivial

theorem oWordsLE_afterSample (c : E) {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterSample c S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> first | trivial | exact h c

theorem oWordsLE_afterGrind {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterGrind S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> trivial

theorem oWordsLE_afterCommit {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterCommit S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> first | trivial | exact h.2

theorem oWordsLE_afterQuery (rows : List (List K)) {S : Option (Script β)} (h : OWordsLE W S) :
    OWordsLE W (Script.afterQuery rows S) := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> first | trivial | exact h rows

theorem length_wordOf_le {S : Option (Script β)} (h : OWordsLE W S) (p : ℕ) :
    (Script.wordOf S p).length ≤ W := by
  rcases S with _ | (_ | _ | _ | _ | _ | _) <;> first | exact Nat.zero_le _ | exact h.1 p

end OWords

/-- **The prover's factor**: what one quarter of the program's cost costs the prover, in blocks.
A commitment (two quarters) builds a tree of at most `13 · 2^height` blocks and absorbs its root;
a proof of work (five quarters) searches `fuel` nonces, two permutations each, then steps once. -/
def blockFactor (height fuel : ℕ) : ℕ := 13 * 2 ^ height + 2 * fuel + 2

/-- **The prover's runner**, against a program of cost `n` quarters at height `height`, from a
script whose commitments have rows of at most `192` words, makes at most
`n · blockFactor height fuel` block calls (mumbai's `isTotalQueryBound_proveFromM`, weighted). -/
theorem cost_runFromWithHash (fuel height : ℕ) {α β : Type} :
    ∀ (P : Prog α) (S : Option (Script β)) (sp : Sponge) (cs : List Tree) (n : ℕ)
      (Q : α → Prop), P.Costs height n Q → OWordsLE 192 S →
      QC (LeanVM.Prover.runFromWithHash callKeccak256 callKeccakF1600 fuel P S sp cs)
        (n * blockFactor height fuel) := by
  intro P
  have hF : 1 ≤ blockFactor height fuel := by unfold blockFactor; omega
  induction P with
  | ret a => intros; exact qc_pure _ _
  | fail => intros; exact qc_pure _ _
  | read k ih =>
    intro S sp cs n Q hp hS
    simp only [LeanVM.Prover.runFromWithHash]
    refine (qc_absorb _ _ _).bind_le (fun sp' ↦ (ih _ _ _ cs (n - 1) Q (hp.2 _)
      (oWordsLE_afterSend hS)).bind_le (fun _ ↦ qc_pure _ 0) le_rfl) ?_
    have h1 := hp.1
    generalize blockFactor height fuel = F at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.succ_mul]
    omega
  | sample k ih =>
    intro S sp cs n Q hp hS
    simp only [LeanVM.Prover.runFromWithHash]
    refine (qc_squeeze _).bind_le (fun r ↦ ih _ _ _ cs (n - 4) Q (hp.2 _)
      (oWordsLE_afterSample _ hS)) ?_
    have h1 := hp.1
    generalize blockFactor height fuel = F at *
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 4 := ⟨n - 4, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul]
    omega
  | grind bits k ih =>
    intro S sp cs n Q hp hS
    simp only [LeanVM.Prover.runFromWithHash]
    refine (qc_findNonceM _ _ _).bind_le (b := 2 + ((n - 5) * blockFactor height fuel + 0))
      (fun o ↦ ?_) ?_
    · split
      · exact qc_pure _ _
      · exact (qc_powStepM _ _).bind_le (fun r ↦ (ih _ _ cs (n - 5) Q hp.2
          (oWordsLE_afterGrind hS)).bind_le (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl
    · have h1 := hp.1
      have hfuel : 2 * fuel + 2 ≤ blockFactor height fuel := by unfold blockFactor; omega
      generalize blockFactor height fuel = F at *
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 5 := ⟨n - 5, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_mul]
      omega
  | commit ht w k ih =>
    intro S sp cs n Q hp hS
    simp only [LeanVM.Prover.runFromWithHash]
    refine (qc_buildTree ht _ 12 fun p ↦ ?_).bind_le (b := 1 + (1 + ((n - 2) *
      blockFactor height fuel + 0))) (fun tree ↦ (qc_absorb _ _ _).bind_le (fun _ ↦
        (qc_absorb _ _ _).bind_le (fun _ ↦ (ih _ _ _ (n - 2) Q hp.2.2
          (oWordsLE_afterCommit hS)).bind_le (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl) le_rfl) ?_
    · have := length_wordOf_le hS p
      omega
    · have h1 := hp.2.1
      have h2 : 2 ^ ht ≤ 2 ^ height := Nat.pow_le_pow_right (by norm_num) hp.1
      have htree : 13 * 2 ^ height + 2 ≤ blockFactor height fuel := by unfold blockFactor; omega
      generalize blockFactor height fuel = F at *
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_mul n' 2]
      omega
  | query i ps k ih =>
    intro S sp cs n Q hp hS
    simp only [LeanVM.Prover.runFromWithHash]
    split
    · exact qc_pure _ _
    · exact (ih _ _ _ cs (n - Prog.openCost height ps.length) Q (hp.2 _)
        (oWordsLE_afterQuery _ hS)).bind_le (fun _ ↦ qc_pure _ 0)
          (by rw [Nat.add_zero]; exact Nat.mul_le_mul_right _ (Nat.sub_le _ _))

/-! ## The verifier's run -/

theorem qc_climb : ∀ (node : Digest) (q : ℕ) (ss : List Digest),
    QC (climbWithHash callKeccak256 node q ss) ss.length
  | _, _, [] => qc_pure _ _
  | node, q, s :: ss => by
    simp only [climbWithHash, List.length_cons]
    have hn (a b : Digest) : QC (callKeccak256 (digestBytes a ++ digestBytes b)) 1 :=
      qc_H_le (by rw [List.length_append, length_digestBytes, length_digestBytes]; omega)
    rw [Nat.add_comm]
    split <;> exact (hn _ _).bind fun _ ↦ qc_climb _ _ ss

/-- One opening: a leaf of at most `192` words (`12` blocks) and its path. -/
theorem qc_openOne (root : Digest) (height width q : ℕ) (o : Compile.Opening)
    (hw : width ≤ 192) :
    QC (openOneWithHash callKeccak256 root height width q o) (12 + height) := by
  unfold openOneWithHash
  split
  · rename_i h
    refine (qc_H_le (k := 12) ?_).bind_le (fun _ ↦ (qc_climb _ _ _).bind_le
      (fun _ ↦ qc_pure _ 0) le_rfl) (by rw [h.2]; omega)
    rw [length_flatMap_kBytes, h.1]
    omega
  · exact qc_pure _ _

theorem qc_openAll (root : Digest) (height width : ℕ) (hw : width ≤ 192) :
    ∀ (ps : List ℕ) (os : List Compile.Opening),
      QC (openAllWithHash callKeccak256 root height width ps os) (ps.length * (12 + height))
  | [], _ => qc_pure _ _
  | _ :: _, [] => qc_pure _ _
  | q :: qs, o :: os => by
    simp only [openAllWithHash, List.length_cons]
    refine (qc_openOne root height width q o hw).bind_le (b := qs.length * (12 + height))
      (fun b ↦ ?_) (by rw [Nat.succ_mul]; omega)
    split
    · exact (qc_openAll root height width hw qs os).bind_le (fun _ ↦ qc_pure _ 0) le_rfl
    · exact qc_pure _ _

/-- **The verifier's run**, of a program of cost `n` quarters at height `height` whose
commitments have width at most `192`, from roots of height at most `12 · height` and width at
most `192`, makes at most `3 · n` block calls. -/
theorem cost_runWithHash (height : ℕ) {α : Type} :
    ∀ (P : Prog α) (s : ProgState) (n : ℕ) (Q : α → Prop), P.Costs height n Q →
      LeanVM.Rpm.WidthsLE LeanVM.Rpm.maxWidth P →
      (∀ r ∈ s.roots, r.2.1 ≤ 12 * height ∧ r.2.2 ≤ 192) →
      QC (runWithHash callKeccak256 callKeccakF1600 P s) (3 * n)
  | .ret _, _, _, _, _, _, _ => qc_pure _ _
  | .fail, _, _, _, _, _, _ => qc_pure _ _
  | .read k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    split
    · exact qc_pure _ _
    · exact (qc_absorb _ _ _).bind_le (fun sp ↦ cost_runWithHash height _ _ (n - 1) Q (hp.2 _)
        (hW _) hr) (by have := hp.1; omega)
  | .sample k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    refine (qc_squeeze _).bind_le (b := 3 * (n - 4)) (fun r ↦ ?_) (by have := hp.1; omega)
    obtain ⟨c, sp⟩ := r
    exact cost_runWithHash height _ _ (n - 4) Q (hp.2 _) (hW _) hr
  | .grind bits k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    split
    · exact qc_pure _ _
    · refine (qc_absorb _ _ _).bind_le (fun sp ↦ (qc_squeeze _).bind_le (b := 3 * (n - 5))
        (fun r ↦ ?_) le_rfl) (by have := hp.1; omega)
      obtain ⟨c, sp'⟩ := r
      dsimp only
      split
      · exact cost_runWithHash height _ _ (n - 5) Q hp.2 hW hr
      · exact qc_pure _ _
  | .commit ht w k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    split
    · refine (qc_absorb _ _ _).bind_le (fun sp ↦ (qc_absorb _ _ _).bind_le (b := 3 * (n - 2))
        (fun sp' ↦ ?_) le_rfl) (by have := hp.2.1; omega)
      split
      · refine cost_runWithHash height _ _ (n - 2) Q hp.2.2 hW.2 fun r hr' ↦ ?_
        rcases List.mem_append.mp hr' with h | h
        · exact hr r h
        · simp only [List.mem_singleton] at h
          subst h
          exact ⟨by have := hp.1; dsimp only; omega, hW.1⟩
      · exact qc_pure _ _
    · exact qc_pure _ _
  | .query i ps k, s, n, Q, hp, hW, hr => by
    simp only [runWithHash]
    split
    · exact qc_pure _ _
    · next root h' w hi =>
      have hrw := hr _ (List.mem_of_getElem? hi)
      refine (qc_openAll root h' w hrw.2 ps s.openings).bind_le
        (b := 3 * (n - Prog.openCost height ps.length)) (fun o ↦ ?_) ?_
      · split
        · exact cost_runWithHash height _ _ _ Q (hp.2 _) (hW _) hr
        · exact qc_pure _ _
      · have h1 := hp.1
        have hm : ps.length * h' ≤ ps.length * (12 * height) := Nat.mul_le_mul_left _ hrw.1
        have e1 : ps.length * (12 + h') = 12 * ps.length + ps.length * h' := by ring
        have e2 : ps.length * (12 * height) = 12 * (ps.length * height) := by ring
        have e3 : Prog.openCost height ps.length = 4 * ps.length + 4 * (ps.length * height) := by
          unfold Prog.openCost; ring
        rw [e1]
        rw [e2] at hm
        rw [e3] at h1 ⊢
        omega

/-- The stacked opening's cost in quarters. -/
abbrev whirQ : ℕ := 4 + (2 + whirBound)

/-- The stacked opening's cost: the batching challenge and WHIR, at height `26` (mumbai's
`costs_verifyStackedOpening` with `ladder_cost`). -/
theorem costs_vso (logN R : ℕ) (claims : List StackClaim) :
    Prog.Costs costHeight (verifyStackedOpening logN R claims) whirQ fun _ ↦ True :=
  costs_verifyStackedOpening (height := costHeight) logN R claims whirBound fun levels h ↦
    ⟨(ladder_cost _ _ levels h).1, (ladder_cost _ _ levels h).2.2.1,
      (ladder_cost _ _ levels h).2.2.2⟩

/-- The stacked opening's commitments have width at most `192` (mumbai's
`widthsLE_verifyWhir`). -/
theorem widthsLE_vso (logN R : ℕ) (claims : List StackClaim) :
    LeanVM.Rpm.WidthsLE LeanVM.Rpm.maxWidth (verifyStackedOpening logN R claims) := by
  rw [verifyStackedOpening_eq_target]
  exact LeanVM.Rpm.WidthsLE.seq (LeanVM.Rpm.WidthsLE.of_moves (g := fun _ ↦ True)
    LeanVM.Protocol.EndToEnd.Sound.MovesOK.sampleE) fun _ ↦ LeanVM.Rpm.widthsLE_verifyWhir _ _ _ _

/-! ## The openings' IVs -/

theorem length_elementBytes (x : E) : (elementBytes x).length = 24 := by
  simp [elementBytes, beBytes, LeanVM.Rpm.wordBytes_len]

theorem length_flatMap_elementBytes (l : List E) :
    (l.flatMap elementBytes).length = 24 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, ih, length_elementBytes, List.length_cons]
    ring

/-- `PCS_claim`: `82 + 24 · n` bytes. -/
theorem length_pcsClaimBytes (c : Commitment) (claim : Claim) :
    (pcsClaimBytes c claim).length = 82 + 24 * claim.point.length := by
  simp only [pcsClaimBytes, List.length_append, List.length_cons, List.length_nil,
    length_digestBytes, length_elementBytes, length_flatMap_elementBytes]
  omega

/-- The opening's sponge: the IV's hash and one permutation. -/
theorem qc_pcsSpongeWithH (c : Commitment) (claim : Claim) (B : ℕ)
    (hB : 82 + 24 * claim.point.length < 136 * B) :
    QC (pcsSpongeWithH callKeccak256 callKeccakF1600 c claim) (B + 1) := by
  unfold pcsSpongeWithH
  refine (qc_H_le (k := B) ?_).bind_le (fun iv ↦ (qc_F _).bind_le (fun _ ↦ qc_pure _ 0) le_rfl)
    le_rfl
  rw [length_pcsClaimBytes]
  exact hB

/-- The verifier's cost of one opening: its IV (`6` blocks), its seed's permutation, the root's two
absorptions, the out-of-domain point (at most `28` hashes) and the run. -/
def vOpen : ℕ := 6 + 1 + 2 + 28 + 3 * whirQ

/-- **The verifier's opening**: the claim has at most `maxVars = 28` coordinates, or it is rejected
at once. -/
theorem cost_pcsOpeningWithH (c : Commitment) (claim : Claim) (proof : Compile.Proof) :
    QC (pcsOpeningWithH callKeccak256 callKeccakF1600 c claim proof) vOpen := by
  unfold pcsOpeningWithH
  by_cases hn : minVars ≤ claim.point.length ∧ claim.point.length ≤ maxVars
  · simp only [hn, and_self, ↓reduceIte]
    have hn' : claim.point.length ≤ 28 := hn.2
    refine (qc_pcsSpongeWithH c claim 6 (by omega)).bind_le (b := 2 + (28 + 3 * whirQ))
      (fun sp ↦ ?_) (by unfold vOpen; omega)
    split
    · refine (qc_absorb _ _ _).bind_le (fun sp ↦ (qc_absorb _ _ _).bind_le
        (b := 28 + 3 * whirQ) (fun sp ↦ ?_) le_rfl) (by omega)
      split
      · refine ((qc_oodPointWithH _ _).mono hn').bind_le (b := 3 * whirQ) (fun z ↦ ?_) le_rfl
        refine (cost_runWithHash costHeight _ _ _ _ (costs_vso _ _ _) (widthsLE_vso _ _ _)
          ?_).bind_le (b := 0) (fun r ↦ ?_) (by omega)
        · intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          refine ⟨?_, show 2 ^ laneFold ≤ 192 by decide⟩
          show claim.point.length - laneFold + logInvRate ≤ 12 * costHeight
          simp only [laneFold, logInvRate, costHeight]
          omega
        · split <;> exact qc_pure _ _
      · exact qc_pure _ _
    · exact qc_pure _ _
  · simp only [hn, ↓reduceIte]
    exact qc_pure _ _

/-- The verifier's openings, one after another. -/
theorem cost_checkAllWithH : ∀ l : List (Commitment × Claim × Compile.Proof),
    QC (checkAllWithH callKeccak256 callKeccakF1600 l) (l.length * vOpen)
  | [] => qc_pure _ _
  | (c, claim, proof) :: rest => by
    simp only [checkAllWithH, List.length_cons]
    refine (cost_pcsOpeningWithH c claim proof).bind_le (b := rest.length * vOpen)
      (fun b ↦ ?_) (by rw [Nat.succ_mul]; omega)
    split
    · exact qc_pure _ _
    · exact cost_checkAllWithH rest

/-- **The prover's opening**: its IV (at most `B` blocks), its seed's permutation, the root's two
absorptions, the out-of-domain point (at most `v` hashes), and the runner on the stacked opening at
height `26` from the honest script. -/
theorem cost_proveClaimWithH (fuel : ℕ) (tree : Tree) (table : Array K) (c : Commitment)
    (claim : Claim) (v B : ℕ) (hv : claim.point.length ≤ v) (hB : 82 + 24 * v < 136 * B) :
    QC (proveClaimWithH callKeccak256 callKeccakF1600 fuel tree table c claim)
      (B + 1 + 2 + v + whirQ * blockFactor costHeight fuel) := by
  unfold proveClaimWithH
  refine (qc_pcsSpongeWithH c claim B (by omega)).bind_le (fun sp ↦ (qc_absorb _ _ _).bind_le
    (fun sp ↦ (qc_absorb _ _ _).bind_le (fun sp ↦ ((qc_oodPointWithH _ _).mono hv).bind_le
      (fun z ↦ (cost_runFromWithHash fuel costHeight _ _ sp [tree] _ _ (costs_vso _ _ _)
        (wordsLE_pcsOpeningScript _ table z c claim)).bind_le
          (fun _ ↦ qc_pure _ 0) le_rfl) le_rfl) le_rfl) le_rfl) (by omega)

/-! ## The reduction -/

/-- The label: `136` bytes. -/
theorem length_label (index : Commitment) (stmt : Statement) : (label index stmt).length = 136 := by
  simp only [label, List.length_append, length_digestBytes, length_elementBytes,
    Vector.length_toList]
  have h16 : "pcs-quotient-kc1".toUTF8.toList.length = 16 := by decide +kernel
  omega

/-- The six claims' points have at most `v` coordinates. -/
def ClaimsLen (v : ℕ) (cl : Claims) : Prop :=
  cl.witness.point.length ≤ v ∧ cl.wiring.point.length ≤ v ∧ cl.h.point.length ≤ v ∧
    cl.q.point.length ≤ v ∧ cl.g.point.length ≤ v ∧ cl.sum.point.length ≤ v

/-- What the reduction may return: claims whose points have at most `m + 4` coordinates. -/
def RedOK (logRows : ℕ) (o : Option Reduced) : Prop :=
  ∀ r, o = some r → ClaimsLen (cellVars logRows + 4) r.claims

/-- **The claims' points**: `W`'s at most `m + 1` coordinates, the wiring's `m`, `H`'s `m + 3`, `Q`'s
`m + 4`, `G`'s `m + 1`, the sum's `m + 3`. -/
theorem claimsAt_len {logRows : ℕ} {stmt : Statement} {α β γ t ρ : E} {a : Vector E 4}
    {next qv gv : E} {cl : Claims} (h : claimsAt logRows stmt α β γ t ρ a next qv gv = some cl) :
    ClaimsLen (cellVars logRows + 4) cl := by
  unfold claimsAt at h
  extract_lets m w wAt theta cell x y c v gate b gamma2 gammas outside publicWeight target tau
    rows d dNext product copies denominators at h
  by_cases hd : (denominators.any fun x ↦ decide (x = 0)) = true
  · simp [hd] at h
  simp only [hd, Bool.false_eq_true, ↓reduceIte, quotientParts, Option.some.injEq] at h
  subst h
  change ClaimsLen (m + 4) _
  simp [ClaimsLen, sumPoint, m]
  omega

theorem redOK_none (logRows : ℕ) : RedOK logRows none := fun _ h ↦ by cases h

theorem redOK_map {logRows : ℕ} {stmt : Statement} {α β γ t ρ : E} {a : Vector E 4}
    {next qv gv : E} (cs : Commitments) :
    RedOK logRows ((claimsAt logRows stmt α β γ t ρ a next qv gv).map
      fun claims ↦ (⟨cs, claims⟩ : Reduced)) := by
  intro r hr
  rcases hc : claimsAt logRows stmt α β γ t ρ a next qv gv with _ | cl
  · rw [hc] at hr
    cases hr
  · rw [hc] at hr
    cases hr
    exact claimsAt_len hc

/-- A commitment read adds its three scalars to the pending ones. -/
theorem readCommitment_pending {c c' : Chain} {s : CommitmentScalars} {com : Commitment}
    (h : readCommitment c s = some (com, c')) :
    c'.state = c.state ∧ c'.pending.length = c.pending.length + 3 := by
  unfold readCommitment at h
  rcases hr : rootOfHalves s.root with _ | r
  · rw [hr] at h
    cases h
  · rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Chain.absorb]

theorem length_squeezeIn (c : Chain) :
    (digestBytes c.state ++ c.pending.flatMap scalarBytes).length = 32 + 32 * c.pending.length := by
  rw [List.length_append, length_digestBytes, length_flatMap_scalarBytes]

/-- **The reduction's transcript**, then a continuation charged only at what the reduction may
return: the label (`136` bytes, two blocks), `α` after three scalars (`128` bytes), `β`, `γ`, `t`
after nine scalars (`320` bytes, three blocks), `ρ` after five values (`192` bytes, two blocks). -/
theorem qc_reduceWithH_bind {β : Type} (logRows : ℕ) (index : Commitment) (stmt : Statement)
    (p : ReductionProof) (f : Option Reduced → OracleComp KeccakCalls β) (b : ℕ)
    (hf : ∀ o, RedOK logRows o → QC (f o) b) :
    QC (reduceWithH callKeccak256 logRows index stmt p >>= f) (10 + b) := by
  by_cases hs : Supported logRows
  · simp only [reduceWithH, hs, not_true_eq_false, ↓reduceIte, startWithH, squeezeWithH,
      bind_assoc, pure_bind]
    refine (qc_H_le (k := 2) ?_).bind_le (b := 8 + b) (fun s₀ ↦ ?_) (by omega)
    · rw [length_label]; omega
    split
    next w c₁ hc₁ =>
      have e₁ := (readCommitment_pending hc₁).2
      simp only [bind_assoc]
      refine (qc_H_le (k := 1) ?_).bind_le (b := 7 + b) (fun s₁ ↦ ?_) (by omega)
      · rw [length_squeezeIn, e₁]; simp
      refine (qc_H_le (k := 1) ?_).bind_le (b := 6 + b) (fun s₂ ↦ ?_) (by omega)
      · simp [length_digestBytes]
      refine (qc_H_le (k := 1) ?_).bind_le (b := 5 + b) (fun s₃ ↦ ?_) (by omega)
      · simp [length_digestBytes]
      split
      next h c₂ hc₂ =>
        split
        next q c₃ hc₃ =>
          split
          next g c₄ hc₄ =>
            have e₂ := (readCommitment_pending hc₂).2
            have e₃ := (readCommitment_pending hc₃).2
            have e₄ := (readCommitment_pending hc₄).2
            simp only [bind_assoc]
            refine (qc_H_le (k := 3) ?_).bind_le (b := 2 + b) (fun s₄ ↦ ?_) (by omega)
            · rw [length_squeezeIn, e₄, e₃, e₂]; simp
            refine (qc_H_le (k := 2) ?_).bind_le (b := b) (fun s₅ ↦ ?_) (by omega)
            · rw [length_squeezeIn]
              simp only [Chain.absorb, foldl_absorb, List.length_append, List.nil_append,
                Vector.length_toList, List.length_cons, List.length_nil]
              omega
            rw [pure_bind]
            exact hf _ (redOK_map _)
          next => rw [pure_bind]; exact (hf none (redOK_none _)).mono (by omega)
        next => rw [pure_bind]; exact (hf none (redOK_none _)).mono (by omega)
      next => rw [pure_bind]; exact (hf none (redOK_none _)).mono (by omega)
    next => rw [pure_bind]; exact (hf none (redOK_none _)).mono (by omega)
  · simp only [reduceWithH, hs, not_false_eq_true, ↓reduceIte, pure_bind]
    exact (hf none (redOK_none _)).mono (by omega)

/-! ## The prover's tail and the verifier -/

/-- The prover's cost of one opening of a claim of at most `28` coordinates. -/
def pOpen (fuel : ℕ) : ℕ := 6 + 1 + 2 + 28 + whirQ * blockFactor costHeight fuel

theorem cost_proveClaimWithH28 (fuel : ℕ) (tree : Tree) (table : Array K) (c : Commitment)
    (claim : Claim) (hv : claim.point.length ≤ 28) :
    QC (proveClaimWithH callKeccak256 callKeccakF1600 fuel tree table c claim) (pOpen fuel) :=
  cost_proveClaimWithH fuel tree table c claim 28 6 hv (by norm_num)

/-- **The prover's last stretch**: its second reduction, then the six openings, their points of at
most `cellVars logRows + 4 ≤ 28` coordinates. -/
theorem cost_proverTailG (circuit : Circuit) (hr : cellVars circuit.logRows ≤ 24) (cells₀ : Array K)
    (coins : Coins) (fuel : ℕ) (stmt : Statement) (a : AuxA) (b : AuxB) (c : AuxC)
    (s₁ s₂ s₃ s₄ s₅ : Digest) :
    QC (proverTailG circuit cells₀ coins fuel stmt a b c s₁ s₂ s₃ s₄ s₅) (10 + 6 * pOpen fuel) := by
  unfold proverTailG
  split
  next r₀ _ =>
    refine qc_reduceWithH_bind _ _ _ _ _ _ fun o ho ↦ ?_
    split
    next r =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ho r rfl
      have hv : cellVars circuit.logRows + 4 ≤ 28 := by omega
      refine (cost_proveClaimWithH28 _ _ _ _ _ (h1.trans hv)).bind_le (b := 5 * pOpen fuel)
        (fun o₁ ↦ ?_) (by omega)
      split
      next =>
        refine (cost_proveClaimWithH28 _ _ _ _ _ (h2.trans hv)).bind_le (b := 4 * pOpen fuel)
          (fun o₂ ↦ ?_) (by omega)
        split
        next =>
          refine (cost_proveClaimWithH28 _ _ _ _ _ (h3.trans hv)).bind_le (b := 3 * pOpen fuel)
            (fun o₃ ↦ ?_) (by omega)
          split
          next =>
            refine (cost_proveClaimWithH28 _ _ _ _ _ (h4.trans hv)).bind_le (b := 2 * pOpen fuel)
              (fun o₄ ↦ ?_) (by omega)
            split
            next =>
              refine (cost_proveClaimWithH28 _ _ _ _ _ (h5.trans hv)).bind_le (b := pOpen fuel)
                (fun o₅ ↦ ?_) (by omega)
              split
              next =>
                refine (cost_proveClaimWithH28 _ _ _ _ _ (h6.trans hv)).bind_le (b := 0)
                  (fun o₆ ↦ ?_) (by omega)
                split <;> exact qc_pure _ _
              next => exact qc_pure _ _
            next => exact qc_pure _ _
          next => exact qc_pure _ _
        next => exact qc_pure _ _
      next => exact qc_pure _ _
    next => exact qc_pure _ _
  next => exact qc_pure _ _

/-- **The verifier**: the reduction, then the six openings. -/
theorem cost_verifyWithH (logRows : ℕ) (index : Commitment) (stmt : Statement)
    (proof : PcsQuotient.Proof) :
    QC (verifyWithH callKeccak256 callKeccakF1600 logRows index stmt proof) (10 + 6 * vOpen) := by
  unfold verifyWithH
  refine qc_reduceWithH_bind _ _ _ _ _ _ fun o _ ↦ ?_
  split
  · exact qc_pure _ _
  · exact (cost_checkAllWithH _).mono (by simp [Reduced.checks])

/-! ## The stages -/

/-- **Stage A**: the setup, the index and witness commitments, the label's hash. -/
theorem cost_stageAG (setup : OracleComp KeccakCalls (Tree × Commitment)) (Cs : ℕ)
    (hs : QC setup Cs) (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (stmt : Statement) :
    QC (stageAG setup circuit cells₀ coins stmt)
      (Cs + (comCost (cellVars circuit.logRows) + (comCost (cellVars circuit.logRows + 1) +
        (2 + 0)))) := by
  unfold stageAG
  exact (hs.map _).bind fun _ ↦ (qc_commitmentWithH _ _).bind fun _ ↦
    (qc_commitmentWithH _ _).bind fun _ ↦
      (qc_H_le (k := 2) (by rw [length_label]; omega)).bind fun _ ↦ qc_pure _ 0

/-- **Stage B**: the three parts' commitments. -/
theorem cost_stageBG (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (a : AuxA)
    (s₁ s₂ s₃ : Digest) :
    QC (stageBG circuit cells₀ coins a s₁ s₂ s₃)
      (comCost (cellVars circuit.logRows + 3) + (comCost (cellVars circuit.logRows + 4) +
        (comCost (cellVars circuit.logRows + 1) + 0))) := by
  unfold stageBG
  exact (qc_commitmentWithH _ _).bind fun _ ↦ (qc_commitmentWithH _ _).bind fun _ ↦
    (qc_commitmentWithH _ _).bind fun _ ↦ qc_pure _ 0

/-- **Stage C**: the prover's reduction up to `ρ`'s query: the label (`2` blocks), `α`'s, `β`'s,
`γ`'s (one each) and `t`'s (`3`) queries. -/
theorem cost_stageCG (circuit : Circuit) (cells₀ : Array K) (coins : Coins) (stmt : Statement)
    (a : AuxA) (b : AuxB) (s₁ s₂ s₃ s₄ : Digest) :
    QC (stageCG circuit cells₀ coins stmt a b s₁ s₂ s₃ s₄) (2 + (1 + (1 + (1 + (3 + 0))))) := by
  unfold stageCG
  exact (qc_H_le (k := 2) (by rw [length_label]; omega)).bind fun _ ↦
    (qc_H_le (k := 1) (by rw [length_in3]; omega)).bind fun _ ↦
    (qc_H_le (k := 1) (by rw [length_digestBytes]; omega)).bind fun _ ↦
    (qc_H_le (k := 1) (by rw [length_digestBytes]; omega)).bind fun _ ↦
    (qc_H_le (k := 3) (by rw [length_in9]; omega)).bind fun _ ↦ qc_pure _ 0

/-- **Stage D**: the prover's tail, then the verifier. -/
theorem cost_stageDG (circuit : Circuit) (hr : cellVars circuit.logRows ≤ 24) (cells₀ : Array K)
    (coins : Coins) (fuel vLogRows : ℕ) (stmt : Statement) (a : AuxA) (b : AuxB) (c : AuxC)
    (s₁ s₂ s₃ s₄ s₅ : Digest) :
    QC (stageDG circuit cells₀ coins fuel vLogRows stmt a b c s₁ s₂ s₃ s₄ s₅)
      (10 + 6 * pOpen fuel + (10 + 6 * vOpen)) := by
  unfold stageDG
  refine (cost_proverTailG circuit hr cells₀ coins fuel stmt a b c s₁ s₂ s₃ s₄ s₅).bind fun o ↦ ?_
  split
  · exact qc_pure _ _
  · exact cost_verifyWithH _ _ _ _

/-- **The chain's shape**: the stages and the chain's six hashes (`128`, `32`, `32`, `320` and `192`
bytes). -/
theorem cost_staged4 {α β γ δ : Type} (chal : Digest → E)
    (A : OracleComp KeccakCalls (α × Digest × CommitmentScalars))
    (B : α → Digest → Digest → Digest → OracleComp KeccakCalls (β × Scalars9))
    (C : α → β → Digest → Digest → Digest → Digest →
      OracleComp KeccakCalls (γ × Digest × (Vector E 4 × E)))
    (D : α → β → γ → Digest → Digest → Digest → Digest → Digest → OracleComp KeccakCalls δ)
    (a b c d : ℕ) (hA : QC A a) (hB : ∀ x s₁ s₂ s₃, QC (B x s₁ s₂ s₃) b)
    (hC : ∀ x y s₁ s₂ s₃ s₄, QC (C x y s₁ s₂ s₃ s₄) c)
    (hD : ∀ x y z s₁ s₂ s₃ s₄ s₅, QC (D x y z s₁ s₂ s₃ s₄ s₅) d) :
    QC (staged4 chal A B C D)
      (a + (1 + (1 + (1 + (b + (3 + (c + (2 + (d + 0))))))))) := by
  unfold staged4
  have h32 (s : Digest) : QC (callKeccak256 (digestBytes s)) 1 :=
    qc_H_le (by rw [length_digestBytes]; omega)
  exact hA.bind fun x ↦ (qc_H_le (k := 1) (by rw [length_in3]; omega)).bind fun s₁ ↦
    (h32 _).bind fun s₂ ↦ (h32 _).bind fun s₃ ↦ (hB _ _ _ _).bind fun y ↦
    (qc_H_le (k := 3) (by rw [length_in9]; omega)).bind fun s₄ ↦ (hC _ _ _ _ _ _).bind fun z ↦
    (qc_H_le (k := 2) (by rw [length_in5]; omega)).bind fun s₅ ↦
    (hD _ _ _ _ _ _ _ _).bind fun _ ↦ qc_pure _ 0

/-- **The staged run, for any setup, circuit and cells**: the setup's cost, the index, `W`, `H`, `Q`,
`G` commitments, the chain's hashes, the prover's reduction twice, its six openings, and the
verifier. -/
theorem cost_stagedRunG (setup : OracleComp KeccakCalls (Tree × Commitment)) (Cs : ℕ)
    (hs : QC setup Cs) (circuit : Circuit) (hr : cellVars circuit.logRows ≤ 24) (cells₀ : Array K)
    (coins : Coins) (fuel vLogRows : ℕ) (stmt : Statement) :
    QC (stagedRunG setup circuit cells₀ coins fuel vLogRows stmt)
      (Cs + comCost (cellVars circuit.logRows) + 2 * comCost (cellVars circuit.logRows + 1) +
        comCost (cellVars circuit.logRows + 3) + comCost (cellVars circuit.logRows + 4) + 38 +
        6 * pOpen fuel + 6 * vOpen) := by
  unfold stagedRunG
  refine (cost_staged4 _ _ _ _ _ _ _ _ _ (cost_stageAG setup Cs hs circuit cells₀ coins stmt)
    (fun a s₁ s₂ s₃ ↦ cost_stageBG circuit cells₀ coins a s₁ s₂ s₃)
    (fun a b s₁ s₂ s₃ s₄ ↦ cost_stageCG circuit cells₀ coins stmt a b s₁ s₂ s₃ s₄)
    (fun a b c s₁ s₂ s₃ s₄ s₅ ↦ cost_stageDG circuit hr cells₀ coins fuel vLogRows stmt a b c
      s₁ s₂ s₃ s₄ s₅)).mono ?_
  omega

end Cost

open Cost in
/-- **The deployed staged run makes at most `2^48` block calls** (`228 197 329 439 321`): the setup's
and the prover's commitments, the chain, the reductions, the six openings proved and verified. The
circuit's size is read off its record (`membership_logRows`, `rfl`); nothing of the deployed circuit
is evaluated. -/
theorem hcost_deployed :
    ∀ stmt w coins, Common.QueryCostAtMost (stagedRun stmt w coins) hashBlocks (2 ^ 48) := by
  intro stmt w coins
  refine (cost_stagedRunG _ _ (qc_commitmentWithH _ _) (membership logRows)
    (by rw [membership_logRows]; decide) (cellsOf w) coins nonceFuel logRows stmt).mono ?_
  rw [membership_logRows]
  norm_num [comCost, pOpen, vOpen, blockFactor, whirQ, whirBound, costHeight, nonceFuel, cellVars,
    PcsQuotient.logRows]

end E2ECompleteness.Pcs

/-- info: 'E2ECompleteness.Pcs.hcost_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms E2ECompleteness.Pcs.hcost_deployed
