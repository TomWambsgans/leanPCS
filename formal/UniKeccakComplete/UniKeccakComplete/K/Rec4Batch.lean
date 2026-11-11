-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. π1-rec4's batch, `λ` given: `Rec3BatchSync.lean`'s
-- `batchProver3`, `batchSyncs3` and `Rec3BatchZero.lean`'s `batchTerminal3_eq_zero` without the batch's own draw of
-- `λ` (π1-rec4 draws it in its late wide draw), against `Rec4VerifierH.lean`'s `batchKH4`.
import UniKeccakComplete.K.Rec3BatchZero
import UniKeccakComplete.K.Rec4Prover

/-!
# π1-rec4's batching sumcheck in step, `λ` given: `batchKH4` reads `batchProver4`

π1-rec4's batch is π1-rec3's paired batch with `λ` drawn before it (the late wide draw), so its prover
`batchProver4 λ` is `batchProver3` without the draw and its verifier `batchKH4 λ` is `batchKH … .rec3` without it.
At a pure Keccak-256 `H` (`Id`), at every `λ` and writer:

* **`batchSyncs4`**: `batchKH4 (pure ∘ H) λ combined layouts ringMap` reads `batchProver4`'s rounds and values,
  returns the prover's point claims (`pointOpening`) and collects one value, `batchTerminal4 λ … w`;
* **`batchTerminal4_eq_zero`**: on the honest batch (`BatchHolds`) that value is zero, at every `λ` (π1-rec3's
  argument, `λ` arbitrary there too).
-/

namespace UniKeccakComplete.Rec4

open UniComplete UniComplete.Rec3 UniKeccakComplete.Rec3

open UniStatement LeanVM.Parameters Finset
open LeanVM.Protocol (Digest)
open UniSound (pairCoeffs cantorBeta1_spec foldAll)

set_option linter.unusedSimpArgs false

section BatchProver

variable {m : Type → Type} [Monad m] (H' : List UInt8 → m Digest)

/-- **π1-rec4's batching sumcheck's prover**, `λ` given (`tailT4`'s batch): the paired rounds on the combined claims'
dense weights and the stacks, each stack's value at its part of the point; the point claims. -/
def batchProver4 (lambda : E) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E)) :
    WrM m (List (Commitment × List E × E)) := do
  let vars := (stackLayouts.map (·.2.vars)).foldl max 0
  let st : BatchState := ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), none, 0, []⟩
  let r ← batchRounds3 H' lambda vars st
  let claims : List (Commitment × List E × E) := combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)
  sendScalars (claims.map (·.2.2))
  return claims

end BatchProver

variable (H : List UInt8 → Digest)

/-- **What `batchKH4` collects** at `λ` and the writer `w`: `sum + last`, `last` the claim it reaches on the prover's
messages from the target, `sum` its weighted values at the point. -/
def batchTerminal4 (lambda : E) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (w : Wr) : E :=
  let R := batch3Run H lambda (batchVars stackLayouts) (batchZ combined stackLayouts stackOf ringMap)
    (targetFold lambda combined).1 w
  (sumFold combined stackLayouts ringMap lambda (batchVars stackLayouts) R.1
    ((claimsOf combined stackLayouts stackOf R.1).map (·.2.2))).1 + R.2.1

/-- **The batching sumcheck's prover synchronises with `batchKH4`** at `λ`: from any writer, the verifier returns
the prover's point claims (`pointOpening`), and collects one value, `terminal w`. -/
def BatchSyncs4 (lambda : E) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (terminal : Wr → E) : Prop :=
  ∀ w : Wr, Syncs (batchKH4 (m := Id) (Pure.pure ∘ H) lambda combined stackLayouts ringMap)
    (batchProver4 (m := Id) (Pure.pure ∘ H) lambda combined stackLayouts stackOf ringMap) w
    (((batchProver4 (m := Id) (Pure.pure ∘ H) lambda combined stackLayouts stackOf ringMap).run w).1.map
      pointOpening)
    [terminal w]

/-- The prover's point claims at its point. -/
theorem batchProver4_run (lambda : E) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (w : Wr) :
    ((batchProver4 (m := Id) (Pure.pure ∘ H) lambda combined stackLayouts stackOf ringMap).run w).1 =
      claimsOf combined stackLayouts stackOf (batch3Run H lambda (batchVars stackLayouts)
        (batchZ combined stackLayouts stackOf ringMap) (targetFold lambda combined).1 w).1 := by
  unfold batchProver4
  dsimp only
  rw [batchInit_stOf, wr_run_bind, batchRounds3_run H _ _ _ (targetFold lambda combined).1]
  rfl

/-- **`batchKH4` reads the honest paired batch** (`BatchSyncs4` at `batchTerminal4`). -/
theorem batchSyncs4 (lambda : E) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E)) :
    BatchSyncs4 H lambda combined stackLayouts stackOf ringMap
      (batchTerminal4 H lambda combined stackLayouts stackOf ringMap) := by
  intro w
  rw [batchProver4_run]
  unfold batchKH4 batchProver4
  dsimp only
  rw [batchInit_stOf]
  refine Syncs.bind (syncs_sumcheckPairs H lambda _ (batchZ combined stackLayouts stackOf ringMap)
    (List.foldl (fun (acc : E × E) (x : Commitment × Combined) ↦ (acc.1 + acc.2 * x.2.value, acc.2 * lambda)) (0, 1)
      combined).1 w) ?_
  rw [batchRounds3_run H _ _ _ (List.foldl (fun (acc : E × E) (x : Commitment × Combined) ↦
    (acc.1 + acc.2 * x.2.value, acc.2 * lambda)) (0, 1) combined).1]
  generalize hR : batch3Run H lambda (List.foldl max 0 (List.map (fun x ↦ x.2.vars) stackLayouts))
    (batchZ combined stackLayouts stackOf ringMap) (List.foldl (fun (acc : E × E) (x : Commitment × Combined) ↦
      (acc.1 + acc.2 * x.2.value, acc.2 * lambda)) (0, 1) combined).1 w = R
  simp only [pure_bind]
  refine Syncs.bind (Syncs.congr_v (syncs_scalars _ _) (by simp)) ?_
  refine Syncs.congr (syncs_requireZero_last _ _ _ _) ?_ ?_
  · rw [← hR]
    exact sumFold_openings combined stackLayouts stackOf ringMap lambda (batchVars stackLayouts) _
  · unfold batchTerminal4
    dsimp only
    rw [← hR]
    rfl

/-- **What `batchKH4` collects on the honest batch is zero**, at every `λ` and writer. -/
theorem batchTerminal4_eq_zero (lambda : E) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (h : BatchHolds combined stackLayouts stackOf ringMap) (w : Wr) :
    batchTerminal4 H lambda combined stackLayouts stackOf ringMap w = 0 := by
  unfold batchTerminal4
  dsimp only
  set pairs : List (Array E × Array E × ℕ) := combined.map fun x ↦
    (denseWeight x.2 (layoutIn stackLayouts x.1) ringMap, (stackOf x.1).map ofK, (layoutIn stackLayouts x.1).vars)
    with hpairs
  have hZ : batchZ combined stackLayouts stackOf ringMap = pairs.map fun p ↦ (p.1, p.2.1) := by
    simp [batchZ, hpairs, List.map_map, Function.comp_def]
  rw [target_eq_T combined stackLayouts stackOf ringMap h lambda]
  obtain ⟨hlen, hlast⟩ := batch3Run_honest H lambda (batchVars stackLayouts)
    (batchZ combined stackLayouts stackOf ringMap) w
  rw [hlast]
  generalize (batch3Run H lambda (batchVars stackLayouts) (batchZ combined stackLayouts stackOf ringMap)
    ((prodOf lambda (batchVars stackLayouts) (batchZ combined stackLayouts stackOf ringMap)).T []) w).1 = rs
    at hlen ⊢
  have hpairsWF : ∀ p ∈ pairs, p.1.size = 2 ^ p.2.2 ∧ p.2.1.size = 2 ^ p.2.2 ∧ p.2.2 ≤ batchVars stackLayouts := by
    intro p hp
    rw [hpairs] at hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    obtain ⟨-, -, -, hsz⟩ := h.claims x hx
    exact ⟨denseWeight_size _ _ _, by rw [Array.size_map, hsz], layoutIn_vars_le _ _⟩
  rw [hZ, prodOf_T_full lambda _ pairs hpairsWF rs hlen]
  set S := wsum lambda (pairs.map fun p ↦
    tableEval p.1 (rs.take p.2.2) * tableEval p.2.1 (rs.take p.2.2) * extOf rs p.2.2 ^ 2) with hS
  have hsum : (sumFold combined stackLayouts ringMap lambda (batchVars stackLayouts) rs
      ((claimsOf combined stackLayouts stackOf rs).map (·.2.2))).1 = S := by
    rw [sumFold_eq, claimsOf_values, zip_map_self, hS, hpairs]
    dsimp only
    simp only [List.map_map]
    refine wsum_congr _ _ _ _ fun x hx ↦ ?_
    obtain ⟨-, hwf, hal, -⟩ := h.claims x hx
    have hd := layoutIn_vars_le stackLayouts x.1
    simp only [Function.comp_apply]
    rw [weightAtK_eq_mle x.2 _ rs ringMap hal (by omega) hwf,
      mleAt_eq_tableEval _ _ (denseWeight_size _ _ _) rs (by omega), extensionAt_eq rs _ _ hlen]
    ring
  rw [hsum]
  simp only [terminalOf, mul_zero, add_zero, ← hS]
  exact add_self_E S

/-- **`batchKH4` accepts the honest paired batch**: `BatchSyncs4` at the zero terminal, every `λ`. -/
theorem batchSyncs4_honest (lambda : E) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (h : BatchHolds combined stackLayouts stackOf ringMap) :
    BatchSyncs4 H lambda combined stackLayouts stackOf ringMap (fun _ ↦ 0) := by
  intro w
  have := batchSyncs4 H lambda combined stackLayouts stackOf ringMap w
  rwa [batchTerminal4_eq_zero H lambda combined stackLayouts stackOf ringMap h w] at this

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.batchSyncs4_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.batchSyncs4_honest
