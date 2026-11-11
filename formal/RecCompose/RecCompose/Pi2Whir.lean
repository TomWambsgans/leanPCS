-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows `crates/leanvm/rec/src/pi2/prover.rs` (`claims`,
-- `open`: one PCS claim per claim, `pcs_claim::open_words` on the plain stacks of `stack_vars`) and uses
-- `formal/UniKeccakComplete` (`K/PcsProver.lean`: `pcsProveH`, `pcsProveH_fails_only_at_pow`; `K/Core.lean`:
-- `pcsOpenKH_of`) and `formal/EndToEnd/Completeness` (`stackWordFast_colOf`, `commitWith_eqH`).
import RecCompose.Pi2Prover
import UniKeccakComplete.K.Core
import UniSound.PendingLink

/-!
# Honest PCS openings at π2's stacks

π2 opens its five claims (`W`'s, the setup's, `Q`'s three) as the EIP draft's PCS claims, each on its commitment's
whole stack (`stackVars`: at `m = 24`, `W` on `2^24` words, `Q` on `2^28`, the setup on `2^25`), by UniKeccakComplete's
honest PCS prover (`pcsProveH`). Here, at a pure Keccak-256 `H` and permutation `F`:

* **`pi2PcsOpen_honest`**: every proof `pcsProveH` makes of `⟨point, stackEval stack point⟩` on a stack of `2^n` words
  (`23 ≤ n ≤ 28`) is accepted by the claim check `pcsOpenKH` against the commitment's root and the stack's
  out-of-domain answer (`UniKeccakComplete.Core.pcsOpenKH_of`); **`pi2PcsOpen_fails_only_at_pow`**: if it makes none, a
  `17`-bit proof of work failed for every nonce below `fuel`;
* **the stacks** (`padStack`): `padStack_size`, `getD_padStack`; **`commitWithH_padStack`**: the commitment of a table
  padded with zeros is that of the table (the WHIR stack word reads past the end as zero, `stackWordFast_colOf`), so
  that the setup's tree (`Pi2Circuit.setupTreeWith`, of `setupStack`'s `2^(m+1)` words) is that of its padded stack;
  **`setupOod_eq`**: the setup's out-of-domain answer (`Pi2Circuit.setupOod`) is the PCS prover's `pcsOod` of the
  padded stack;
* `stackVars_24`: `(24, 28, 25)`.

No stack is evaluated: the stacks are arbitrary.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

set_option autoImplicit false

namespace RecCompose.Pi2W

/-- π2's stacks' variables at `m = 24`: `W` `24`, `Q` `28`, the setup `25`. -/
theorem stackVars_24 : RecStatement.stackVars 24 = (24, 28, 25) := rfl

/-! ## The stacks -/

theorem padStack_size (vars : ℕ) (T : ℕ → K) : (padStack vars T).size = 2 ^ vars := by
  simp [padStack]

theorem getD_padStack (vars : ℕ) (T : ℕ → K) (i : ℕ) :
    (padStack vars T).getD i 0 = if i < 2 ^ vars then T i else 0 := by
  unfold padStack
  split
  · rename_i h
    simp [Array.getD, h]
  · rename_i h
    simp [Array.getD, h]

/-- **A table padded with zeros has the table's commitment** (`6 ≤ vars`; both read the first `2^vars` words). -/
theorem commitWithH_padStack {m : Type → Type} [Monad m] (H : Bytes → m Digest) {vars : ℕ} (h6 : 6 ≤ vars)
    (a : Array K) :
    E2ECompleteness.commitWithH H vars (padStack vars fun i ↦ a.getD i 0) =
      E2ECompleteness.commitWithH H vars a := by
  have hc : E2ECompleteness.colOf vars (padStack vars fun i ↦ a.getD i 0) = E2ECompleteness.colOf vars a := by
    unfold E2ECompleteness.colOf
    congr 1
    exact Vector.ext fun i hi ↦ by simp only [Vector.getElem_ofFn]; simp only [getD_padStack, hi, ↓reduceIte]
  unfold E2ECompleteness.commitWithH
  rw [E2ECompleteness.stackWordFast_colOf h6 1 a,
    E2ECompleteness.stackWordFast_colOf h6 1 (padStack vars fun i ↦ a.getD i 0), hc]

/-- `multilinearEval` reads a list padded with zeros as the list (a list of `2^vars` entries). -/
theorem setupOod_eq (c : RecStatement.Pi2Circuit) (root : Digest)
    (hsz : c.setupStack.size ≤ 2 ^ (RecStatement.stackVars c.circuit.logN).2.2) :
    c.setupOod root = UniKeccakComplete.pcsOod (RecStatement.stackVars c.circuit.logN).2.2
      (padStack (RecStatement.stackVars c.circuit.logN).2.2 fun i ↦ c.setupStack.getD i 0) root := by
  unfold RecStatement.Pi2Circuit.setupOod UniKeccakComplete.pcsOod UniComplete.stackEval UniKeccakComplete.pcsZ
  dsimp only
  congr 1
  refine List.ext_getElem ?_ fun i h1 h2 ↦ ?_
  · simp only [List.length_append, List.length_map, Array.length_toList, List.length_replicate, padStack,
      Array.size_ofFn]
    omega
  · rw [List.getElem_append]
    split_ifs with hi
    · simp only [List.length_map, Array.length_toList] at hi
      simp [padStack, Array.getD, hi]
    · simp only [List.length_map, Array.length_toList] at hi
      simp [padStack, Array.getD, hi]

/-- **`stackEval` is the PCS claim's multilinear value** (`UniSound.mleStk`), on a stack of `2^|pt|` words. -/
theorem stackEval_eq_mleStk (stack : Array K) (pt : List E) (hs : stack.size = 2 ^ pt.length) :
    UniComplete.stackEval stack pt = UniSound.mleStk (fun j ↦ stack.getD j 0) pt.length pt := by
  unfold UniComplete.stackEval UniSound.mleStk
  rw [UniSound.multilinearEval_eq_sum _ _ (Or.inl (by simp [hs])),
    ← Finset.sum_range (fun x ↦ UniSound.cubeEq pt pt.length x * ofK (stack.getD x 0))]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  congr 1
  have hx' : x < stack.size := hs ▸ Finset.mem_range.1 hx
  simp [List.getD_eq_getElem?_getD, Array.getD, hx']

/-- `mleStk` reads its stack below `2^n` only. -/
theorem mleStk_congr {c c' : UniSound.Stk} {n : ℕ} (h : ∀ j < 2 ^ n, c j = c' j) (pt : List E) :
    UniSound.mleStk c n pt = UniSound.mleStk c' n pt := by
  unfold UniSound.mleStk
  exact Finset.sum_congr rfl fun x _ ↦ by rw [h x x.isLt]

/-! ## The openings -/

/-- **The honest PCS opening of a π2 claim is accepted** (pure `H`, `F`; `23 ≤ n ≤ 28`, a stack of `2^n` words). -/
theorem pi2PcsOpen_honest (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {n : ℕ}
    (h1 : 23 ≤ n) (h2 : n ≤ 28) (stack : Array K) (hs : stack.size = 2 ^ n) (pt : List E) (hpt : pt.length = n)
    {π : Compile.Proof}
    (hπ : UniKeccakComplete.pcsProveH (m := Id) H F fuel n (E2ECompleteness.commitWithH (m := Id) H n stack) stack pt
      (UniComplete.stackEval stack pt) = some π) :
    UniKeccakComplete.pcsOpenKH (m := Id) (fun b ↦ pure (H b)) (fun s ↦ pure (F s)) n
      (E2ECompleteness.commitWithH (m := Id) H n stack).root
      (UniKeccakComplete.pcsOod n stack (E2ECompleteness.commitWithH (m := Id) H n stack).root) pt
      (UniComplete.stackEval stack pt) π = true :=
  UniKeccakComplete.Core.pcsOpenKH_of H F fuel h1 h2 stack hs pt hpt hπ

/-- **π2's PCS opening prover fails only at a proof of work.** -/
theorem pi2PcsOpen_fails_only_at_pow (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ) {n : ℕ}
    (h1 : 23 ≤ n) (h2 : n ≤ 28) (stack : Array K) (pt : List E) (hpt : pt.length = n) (v : E)
    (hn : UniKeccakComplete.pcsProveH (m := Id) H F fuel n (E2ECompleteness.commitWithH (m := Id) H n stack) stack pt v =
      none) :
    ∃ (sc : List LeanVM.Protocol.Verifier.StackClaim) (hist : List Ev) (k : Prog Bool) (sp : Sponge),
      (Whir.Complete.openingProgram n PcsQuotient.logInvRate sc).after hist =
          some (.grind Whir.queryGrindingBits k) ∧
        ∀ i < fuel, powOk Whir.queryGrindingBits (Compile.nonceOf i)
          (Compile.powStep F sp (Compile.nonceOf i)).1 = false :=
  UniKeccakComplete.pcsProveH_fails_only_at_pow H F fuel h1 h2 stack pt hpt v hn

end RecCompose.Pi2W

/-! ## Axioms -/

/-- info: 'RecCompose.Pi2W.commitWithH_padStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2W.commitWithH_padStack

/-- info: 'RecCompose.Pi2W.setupOod_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2W.setupOod_eq

/-- info: 'RecCompose.Pi2W.pi2PcsOpen_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2W.pi2PcsOpen_honest

/-- info: 'RecCompose.Pi2W.pi2PcsOpen_fails_only_at_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms RecCompose.Pi2W.pi2PcsOpen_fails_only_at_pow
