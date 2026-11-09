-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- Ported to the Keccak VM from `formal/UniComplete/UniComplete/BatchProof.lean`.
import UniKeccakComplete.K.BatchProofSync

/-!
# `batchKH` accepts the honest batching sumcheck (`BatchSyncs`)

On a channel synchronised with the prover's writer before step 9, at a pure Keccak-256 `H`, the Keccak verifier's
`batchKH (pure ∘ H) .main combined layouts ringMap` reads back the prover's messages (`batchProver`, SyncBasic's
transcription of `proveStreamWith`'s step 9): `λ`, the rounds, the stacks' values; it returns the prover's point claims
(`pointOpening`: `(c, .point (r.take vars_c) value_c none)`, `value_c` the stack's multilinear extension at
`r.take vars_c`), and collects one value, `batchTerminal` (`batchSyncs`, SyncBasic's `BatchSyncs`). **That value is
zero** (`batchTerminal_eq_zero`, at every writer: at every `λ` and every challenge list of the batch's length,
`collectedAt_eq_zero`) given `BatchHolds`: every combined claim holds of its stack (`Combined.Holds`), is well formed
for its layout (`WeightWF`: slot points of `v − 11` coordinates, so `weightAtK`'s slot bits are `11`), on an aligned
layout (`Aligned`; `StackLayout.new`'s are, `aligned_new`), its stack of `2^vars` words.

The batch has no pending matrices (no `λ^n` product term, no `a`, `b`, no matrices' claim), its
weight is `weightAtK`, its sumcheck `sumcheckDrawnH … .main.narrow` (= `sumcheckH`, `sumcheckDrawnH_main`).

The value is `sum + last`: `last` is the sumcheck's terminal (`batch_rounds`: `Σ_k λ^k W̃_k C̃_k ext_k²`), `sum` the
verifier's `Σ_k λ^k weightAtK · extension · value` (`weightAtK_eq_mle`: `W̃_k ext_k`; the extension `ext_k`; the value
`C̃_k`): each part twice, zero in characteristic two.

Decisions: the verifier's and the prover's sub-computations are named by their text (`targetFold`, `sumFold`,
`claimsOf`, `extensionAt`), so that the synchronisation reads them by definitional unfolding and the algebra rewrites
them by closed forms (`targetFold_eq`, `sumFold_eq`, `extensionAt_eq`).
-/

open LeanVM.Parameters LeanVM.Protocol.KeccakHash
open LeanVM.Protocol (Digest)
open LeanVM.Protocol.EndToEnd (boolPoint)
open UniStatement
open Finset

namespace UniKeccakComplete

open UniComplete

/-! ## The verifier's and the prover's sub-computations, by their text -/

/-- `batchKH`'s target and scale (its text). -/
def targetFold (lambda : E) (combined : List (Commitment × Combined)) : E × E :=
  combined.foldl (fun (acc : E × E) (_, claim) ↦ (acc.1 + acc.2 * claim.value, acc.2 * lambda)) (0, 1)

/-- `batchKH`'s zero extension past `from` of the batch's `vars` (its text). -/
def extensionAt (r : List E) (fromVar vars : ℕ) : E :=
  (List.range' fromVar (vars - fromVar)).foldl (fun e j ↦ e * (1 + r.getD j 0)) 1

/-- `batchKH`'s terminal sum, scale and openings over the values read (its text). -/
def sumFold (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) (lambda : E) (vars : ℕ) (r : List E) (values : List E) :
    E × E × Array (Commitment × Opening) :=
  let layoutOf (c : Commitment) : StackLayout := ((layouts.find? (·.1 == c)).map (·.2)).getD default
  (combined.zip values).foldl
    (fun (acc : E × E × Array (Commitment × Opening)) ((commitment, claim), value) ↦
      let (sum, scale, openings) := acc
      let layout := layoutOf commitment
      let weight := UniKeccak.weightAtK claim layout r ringMap
      let extension := (List.range' layout.vars (vars - layout.vars)).foldl
        (fun e j ↦ e * (1 + r.getD j 0)) 1
      (sum + scale * weight * extension * value, scale * lambda,
        openings.push (commitment, .point (r.take layout.vars) value none)))
    (0, 1, #[])

/-- The prover's point claims at the point `r` (`batchProver`'s text). -/
def claimsOf (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (r : List E) : List (Commitment × List E × E) :=
  combined.map fun (c, _) ↦
    let pt := r.take (layoutIn stackLayouts c).vars
    (c, pt, multilinearEval ((stackOf c).toList.map ofK) pt)

/-- The batch's variables (`batchKH`'s and `batchProver`'s). -/
def batchVars (stackLayouts : List (Commitment × StackLayout)) : ℕ := (stackLayouts.map (·.2.vars)).foldl max 0

/-- The prover's state before the rounds (`batchProver`'s text; no matrices). -/
def batchInit (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) : BatchState :=
  ⟨combined.map (fun (c, claim) ↦ denseWeight claim (layoutIn stackLayouts c) ringMap),
    combined.map (fun (c, _) ↦ (stackOf c).map ofK), none, 0, []⟩

/-- **What `batchKH` collects** at `λ` and the challenges `rs`, on the honest messages: `sum + last`. -/
def collectedAt (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) (lambda : E) (rs : List E) : E :=
  let vars := batchVars stackLayouts
  let st := batchInit combined stackLayouts stackOf ringMap
  let last := claimRun lambda 0 rs st (targetFold lambda combined).1
  (sumFold combined stackLayouts ringMap lambda vars rs ((claimsOf combined stackLayouts stackOf rs).map (·.2.2))).1 +
    last

/-- **The collected value at the writer `w`**: at its `λ` (`Wr.sampled`) and the rounds' challenges from there. -/
def batchTerminal (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (w : Wr) : E :=
  collectedAt combined stackLayouts stackOf ringMap (Wr.sampled H w).1
    (loopChallenges H (Wr.sampled H w).1 (batchVars stackLayouts) 0
      (batchInit combined stackLayouts stackOf ringMap) (Wr.sampled H w).2)

/-! ## Closed forms -/

theorem foldl_scaled {α : Type} (lambda : E) (f : α → E) (step : E × E → α → E × E)
    (hstep : ∀ acc x, step acc x = (acc.1 + acc.2 * f x, acc.2 * lambda)) :
    ∀ (L : List α) (a s : E), L.foldl step (a, s) = (a + s * wsum lambda (L.map f), s * lambda ^ L.length)
  | [], a, s => by simp [wsum]
  | x :: L, a, s => by
    rw [List.foldl_cons, hstep, foldl_scaled lambda f step hstep L]
    simp only [List.map_cons, wsum, List.length_cons, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩

theorem targetFold_eq (lambda : E) (combined : List (Commitment × Combined)) :
    targetFold lambda combined =
      (wsum lambda (combined.map fun x ↦ x.2.value), lambda ^ combined.length) := by
  unfold targetFold
  refine (foldl_scaled lambda (fun x ↦ x.2.value) _ (fun _ _ ↦ ?_) combined 0 1).trans ?_
  · rfl
  · rw [zero_add, one_mul, one_mul]

theorem foldl_three {α : Type} (lambda : E) (f : α → E) (o : α → Commitment × Opening)
    (step : E × E × Array (Commitment × Opening) → α → E × E × Array (Commitment × Opening))
    (hstep : ∀ a s arr x, step (a, s, arr) x = (a + s * f x, s * lambda, arr.push (o x))) :
    ∀ (L : List α) (a s : E) (arr : Array (Commitment × Opening)), L.foldl step (a, s, arr) =
      (a + s * wsum lambda (L.map f), s * lambda ^ L.length, arr ++ (L.map o).toArray)
  | [], a, s, arr => by simp [wsum]
  | x :: L, a, s, arr => by
    rw [List.foldl_cons, hstep, foldl_three lambda f o step hstep L]
    simp only [List.map_cons, wsum, List.length_cons]
    refine Prod.ext (by dsimp only; ring) (Prod.ext (by dsimp only; ring) ?_)
    apply Array.toList_inj.mp
    simp

/-- **`batch`'s terminal fold**: the sum `Σ_k λ^k weight · extension · value`, the scale `λ^n`, the openings. -/
theorem sumFold_eq (combined : List (Commitment × Combined)) (layouts : List (Commitment × StackLayout))
    (ringMap : Option (List E)) (lambda : E) (vars : ℕ) (r : List E) (values : List E) :
    sumFold combined layouts ringMap lambda vars r values =
      (wsum lambda ((combined.zip values).map fun x ↦
          UniKeccak.weightAtK x.1.2 (layoutIn layouts x.1.1) r ringMap *
            extensionAt r (layoutIn layouts x.1.1).vars vars * x.2),
        lambda ^ (combined.zip values).length,
        ((combined.zip values).map fun x ↦
          (x.1.1, Opening.point (r.take (layoutIn layouts x.1.1).vars) x.2 none)).toArray) := by
  unfold sumFold
  refine (foldl_three lambda (fun x ↦
      UniKeccak.weightAtK x.1.2 (layoutIn layouts x.1.1) r ringMap *
        extensionAt r (layoutIn layouts x.1.1).vars vars * x.2)
    (fun x ↦ (x.1.1, Opening.point (r.take (layoutIn layouts x.1.1).vars) x.2 none)) _
    (fun a s arr x ↦ ?_) (combined.zip values) 0 1 #[]).trans ?_
  · obtain ⟨⟨c, claim⟩, value⟩ := x
    dsimp only
    refine Prod.ext ?_ rfl
    simp only [extensionAt, layoutIn]
    ring
  · simp only [zero_add, one_mul, Array.empty_append]

/-! ## Extensions, sizes, values -/

theorem prod_map_getD (f : E → E) : ∀ l : List E, (l.map f).prod = ∏ i ∈ range l.length, f (l.getD i 0)
  | [] => by simp
  | x :: l => by
    rw [List.map_cons, List.prod_cons, prod_map_getD f l, List.length_cons, prod_range_succ']
    simp [mul_comm]

/-- `Π_{j ≥ d} (1 + r_j)` as a product over the coordinates past `d`. -/
theorem extOf_eq (r : List E) (d : ℕ) :
    extOf r d = ∏ i ∈ range (r.length - d), (1 + r.getD (d + i) 0) := by
  unfold extOf
  rw [prod_map_getD, List.length_drop]
  refine prod_congr rfl fun i _ ↦ ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **`batch`'s extension is the zero extension's factor** (the point of the batch's `vars` coordinates). -/
theorem extensionAt_eq (r : List E) (d vars : ℕ) (hr : r.length = vars) : extensionAt r d vars = extOf r d := by
  unfold extensionAt
  rw [List.range'_eq_map_range, List.foldl_map, foldl_mul_map, one_mul, prod_map_range, extOf_eq, hr]

theorem selector_zero (r : List E) (d : ℕ) : UniStatement.selector r d 0 = extOf r d := by
  rw [selector_eq, extOf_eq]
  simp

/-- **A table's extension over the batch's variables**, zero past its `2^d` entries: its extension at `r_{<d}`
times `Π_{j ≥ d} (1 + r_j)`. -/
theorem mleAt_eq_tableEval (W : Array E) (d : ℕ) (hW : W.size = 2 ^ d) (r : List E) (hd : d ≤ r.length) :
    mleAt r.length r W = tableEval W (r.take d) * extOf r d := by
  unfold mleAt
  have hle : 2 ^ d ≤ 2 ^ r.length := Nat.pow_le_pow_right (by norm_num) hd
  rw [← sum_range_add_sum_Ico _ hle, sum_eq_zero (s := Ico _ _) (fun x hx ↦ by
    rw [getD_ge W (by rw [hW]; exact (mem_Ico.mp hx).1), zero_mul]), add_zero]
  have hl : (r.take d).length = d := by simp [hd]
  unfold tableEval UniStatement.multilinearEval
  rw [Array.toArray_toList, foldl_foldOnce _ _ (by rw [hl, hW]), hl, sum_mul, ← selector_zero]
  refine sum_congr rfl fun x hx ↦ ?_
  have h0 := eqEval_block (r := r) (off := 0) hd (dvd_zero _) (mem_range.mp hx)
  rw [zero_add] at h0
  rw [h0, mul_assoc]

theorem foldl_size {α : Type} (f : Array E → α → Array E) (hf : ∀ W a, (f W a).size = W.size) :
    ∀ (l : List α) (W : Array E), (l.foldl f W).size = W.size
  | [], _ => rfl
  | a :: l, W => by rw [List.foldl_cons, foldl_size f hf l, hf]

/-- The dense weight has the stack's `2^vars` words. -/
theorem denseWeight_size (claim : Combined) (layout : StackLayout) (ringMap : Option (List E)) :
    (denseWeight claim layout ringMap).size = 2 ^ layout.vars := by
  rw [denseWeight_eq_fold, foldl_size _ (fun W t ↦ ?_), Array.size_replicate]
  obtain ⟨c, p, tw, co⟩ := t
  unfold denseStep
  dsimp only
  split
  all_goals
    refine foldl_size _ (fun W b ↦ ?_) _ _
    exact foldl_size _ (fun W u ↦ addAt_size _ _ _) _ _

/-- The pairing of a weight with a stack's words is `dotE` against the words in `E`. -/
theorem ofK_zero' : ofK (0 : K) = 0 := by
  have h := LeanVM.Parameters.ofK_add (0 : K) 0
  rw [add_zero] at h
  have : ofK (0 : K) + ofK 0 = ofK 0 + 0 := by rw [← h, add_zero]
  exact add_left_cancel this

theorem dotK_eq (w : Array E) (s : Array K) : dotK w s = dotE w (s.map ofK) := by
  unfold dotK dotE
  rw [foldl_add_map, zero_add, sum_map_range]
  refine sum_congr rfl fun u _ ↦ ?_
  congr 1
  by_cases hu : u < s.size
  · simp [Array.getD_eq_getD_getElem?, hu]
  · rw [getD_ge _ (by simpa using hu)]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (show s.size ≤ u by omega), Option.getD_none]
    exact ofK_zero'

theorem foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => ⟨le_rfl, by simp⟩
  | x :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max a x)
    rw [List.foldl_cons]
    refine ⟨le_trans (le_max_left a x) h1, fun y hy ↦ ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_trans (le_max_right a y) h1
    · exact h2 y hy

/-- Every commitment's layout has at most the batch's variables. -/
theorem layoutIn_vars_le (stackLayouts : List (Commitment × StackLayout)) (c : Commitment) :
    (layoutIn stackLayouts c).vars ≤ batchVars stackLayouts := by
  unfold layoutIn batchVars
  cases h : stackLayouts.find? (·.1 == c) with
  | none => exact Nat.zero_le _
  | some x =>
    simp only [Option.map_some, Option.getD_some]
    exact (foldl_max_ge _ 0).2 _ (List.mem_map.mpr ⟨x, List.mem_of_find?_eq_some h, rfl⟩)

theorem zip_map_self {α β : Type} (v : α → β) : ∀ l : List α, l.zip (l.map v) = l.map fun x ↦ (x, v x)
  | [] => rfl
  | x :: l => by simp [zip_map_self v l]

theorem claimsOf_values (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (r : List E) :
    (claimsOf combined stackLayouts stackOf r).map (·.2.2) =
      combined.map fun x ↦ tableEval ((stackOf x.1).map ofK) (r.take (layoutIn stackLayouts x.1).vars) := by
  unfold claimsOf tableEval
  simp [List.map_map, Function.comp_def, Array.toList_map]

/-- **A commitment's layout is aligned** when every listed layout is (`StackLayout.new`'s are, `aligned_new`; the
default, for an unlisted commitment, has no block). -/
theorem aligned_layoutIn (stackLayouts : List (Commitment × StackLayout)) (h : ∀ x ∈ stackLayouts, Aligned x.2)
    (c : Commitment) : Aligned (layoutIn stackLayouts c) := by
  unfold layoutIn
  cases hf : stackLayouts.find? (·.1 == c) with
  | none => intro _ _ _ _ hb; exact absurd hb (List.not_mem_nil)
  | some x => exact h x (List.mem_of_find?_eq_some hf)

/-- **The verifier's layouts are aligned** (`layoutsK`: three `StackLayout.new`). -/
theorem aligned_layouts (shape : Shape) (c2Columns : List (Column × ℕ × Bool)) :
    ∀ x ∈ UniKeccak.layoutsK shape c2Columns, Aligned x.2 := by
  intro x hx
  simp only [UniKeccak.layoutsK, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact aligned_new _

/-- The verifier's stacks have at least `15` variables (`StackLayout.new`'s `MIN_STACKED_LOG`). -/
theorem batchVars_layouts_ge (shape : Shape) (c2Columns : List (Column × ℕ × Bool)) :
    15 ≤ batchVars (UniKeccak.layoutsK shape c2Columns) := by
  have hmem : (Commitment.c2, StackLayout.new c2Columns) ∈ UniKeccak.layoutsK shape c2Columns := by
    simp [UniKeccak.layoutsK]
  have h15 : 15 ≤ (StackLayout.new c2Columns).vars := by
    unfold StackLayout.new
    simp only
    exact le_max_right _ _
  exact le_trans h15 ((foldl_max_ge _ 0).2 _ (List.mem_map.mpr ⟨_, hmem, rfl⟩))

/-! ## The collected value is zero -/

/-- **The honest batch's hypotheses**: every combined claim holds of its stack, is well formed for its aligned
layout, its stack of `2^vars` words. -/
structure BatchHolds (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) : Prop where
  claims : ∀ x ∈ combined, Combined.Holds (layoutIn stackLayouts x.1) (stackOf x.1) ringMap x.2 ∧
    WeightWF x.2 (layoutIn stackLayouts x.1) ringMap ∧ Aligned (layoutIn stackLayouts x.1) ∧
    (stackOf x.1).size = 2 ^ (layoutIn stackLayouts x.1).vars

/-- **What `batchKH` collects on the honest messages is zero**, at every `λ` and every challenge list of the batch's
length. -/
theorem collectedAt_eq_zero (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (h : BatchHolds combined stackLayouts stackOf ringMap) (lambda : E) (rs : List E)
    (hrs : rs.length = batchVars stackLayouts) :
    collectedAt combined stackLayouts stackOf ringMap lambda rs = 0 := by
  set pairs : List (Array E × Array E × ℕ) := combined.map fun x ↦
    (denseWeight x.2 (layoutIn stackLayouts x.1) ringMap, (stackOf x.1).map ofK, (layoutIn stackLayouts x.1).vars)
    with hpairs
  have hinit : batchInit combined stackLayouts stackOf ringMap = initState pairs none := by
    simp [batchInit, initState, hpairs, List.map_map, Function.comp_def]
  -- The pairs' part of the terminal.
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
      mleAt_eq_tableEval _ _ (denseWeight_size _ _ _) rs (by omega), extensionAt_eq rs _ _ hrs]
    ring
  -- The pairs' part of the target.
  have htarget : (targetFold lambda combined).1 = wsum lambda (pairs.map fun p ↦ dotE p.1 p.2.1) := by
    rw [targetFold_eq, hpairs, List.map_map]
    refine wsum_congr _ _ _ _ fun x hx ↦ ?_
    obtain ⟨hh, -, -, -⟩ := h.claims x hx
    simp only [Function.comp_apply]
    rw [← hh, dotK_eq]
  have hpairsWF : ∀ q ∈ pairs, q.1.size = 2 ^ q.2.2 ∧ q.2.1.size = 2 ^ q.2.2 ∧ q.2.2 ≤ batchVars stackLayouts := by
    intro q hq
    rw [hpairs] at hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    obtain ⟨-, -, -, hsz⟩ := h.claims x hx
    exact ⟨denseWeight_size _ _ _, by rw [Array.size_map, hsz], layoutIn_vars_le _ _⟩
  have hwf : BatchWF 0 (batchVars stackLayouts) pairs none := ⟨hpairsWF, fun t ht ↦ by simp at ht⟩
  have hlast := batch_rounds lambda 0 _ pairs none hwf rs hrs
  unfold collectedAt
  dsimp only
  rw [hsum, hinit, htarget, show wsum lambda (pairs.map fun p ↦ dotE p.1 p.2.1) = targetOf lambda pairs none by
    simp [targetOf], hlast]
  simp only [terminalOf, mul_zero, add_zero, ← hS]
  exact add_self_E S

/-! ## The synchronisation -/

/-- **The last step**: the verifier collects `x` and returns, the prover returns. -/
theorem syncs_requireZero_last {α β : Type} (x : E) (a : α) (b : β) (w : Wr) :
    Syncs (requireZero (m := Id) x >>= fun _ ↦ Pure.pure a) (Pure.pure b : WrM Id β) w a [x] := by
  have h := Syncs.bind (f := fun _ ↦ Pure.pure a) (g := fun _ ↦ (Pure.pure b : WrM Id β))
    (syncs_requireZero x w) (syncs_pure a b _)
  refine Syncs.congr_p (Syncs.congr h rfl (by simp)) ?_
  rw [pure_bind]

/-- **The prover's output**: its point claims at its challenges. -/
theorem batchProver_run (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (w : Wr) :
    ((batchProver (m := Id) (Pure.pure ∘ H) combined stackLayouts stackOf ringMap).run w).1 =
      claimsOf combined stackLayouts stackOf (loopChallenges H (Wr.sampled H w).1 (batchVars stackLayouts) 0
          (batchInit combined stackLayouts stackOf ringMap) (Wr.sampled H w).2) := by
  unfold batchProver
  rw [wr_run_bind, sampleW_run]
  dsimp only
  rw [wr_run_bind, batchRounds_run H _ _ _ rfl]
  rfl

/-- The verifier's openings are the prover's point claims. -/
theorem sumFold_openings (combined : List (Commitment × Combined)) (stackLayouts : List (Commitment × StackLayout))
    (stackOf : Commitment → Array K) (ringMap : Option (List E)) (lambda : E) (vars : ℕ) (rs : List E) :
    (sumFold combined stackLayouts ringMap lambda vars rs
        ((claimsOf combined stackLayouts stackOf rs).map (·.2.2))).2.2.toList =
      (claimsOf combined stackLayouts stackOf rs).map pointOpening := by
  rw [sumFold_eq]
  dsimp only
  rw [claimsOf_values, zip_map_self, List.map_map]
  simp only [claimsOf, List.map_map]
  refine List.map_congr_left fun x _ ↦ ?_
  simp [pointOpening, tableEval, Array.toList_map]

/-- The main line's sumcheck (`FsShape.main`, wide challenges) is `sumcheckH`. -/
theorem sumcheckDrawnH_main (H : List UInt8 → Digest) (target : E) (count : ℕ) (eqs : List (Option E)) :
    sumcheckDrawnH (m := Id) (Pure.pure ∘ H) target count eqs FsShape.main.narrow =
      sumcheckH (m := Id) (Pure.pure ∘ H) target count eqs := rfl

/-- **`batchKH .main` reads the honest batching sumcheck** (`BatchSyncs`): from any writer, the verifier returns the
prover's point claims and collects `batchTerminal` at that writer. -/
theorem batchSyncs (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E)) :
    BatchSyncs H combined stackLayouts stackOf ringMap (batchTerminal H combined stackLayouts stackOf ringMap) := by
  intro w
  rw [batchProver_run]
  unfold batchKH batchProver
  refine Syncs.bind (syncs_sample H w) ?_
  rw [sampleW_run]
  generalize hlam : (Wr.sampled H w).1 = lam
  generalize hw1 : (Wr.sampled H w).2 = w1
  dsimp only
  refine Syncs.bind (Syncs.congr_v (syncs_sumcheck H lam _ (batchVars stackLayouts)
    (batchInit combined stackLayouts stackOf ringMap) w1) rfl) ?_
  rw [batchRounds_run H _ _ _ rfl]
  generalize hrs : loopChallenges H lam (batchVars stackLayouts) 0
    (batchInit combined stackLayouts stackOf ringMap) w1 = rs
  generalize hw2 : ((batchRounds (m := Id) (Pure.pure ∘ H) lam (batchVars stackLayouts)
    (batchInit combined stackLayouts stackOf ringMap)).run w1).2 = w2
  dsimp only
  refine Syncs.bind (Syncs.congr_v (syncs_scalars _ _) (by simp)) ?_
  refine Syncs.congr (syncs_requireZero_last _ _ _ _) ?_ ?_
  · exact sumFold_openings combined stackLayouts stackOf ringMap lam (batchVars stackLayouts) rs
  · unfold batchTerminal
    rw [hlam, hw1, hrs]
    rfl

/-- **The collected value is zero** at every writer, for the honest batch. -/
theorem batchTerminal_eq_zero (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (h : BatchHolds combined stackLayouts stackOf ringMap) (w : Wr) :
    batchTerminal H combined stackLayouts stackOf ringMap w = 0 :=
  collectedAt_eq_zero combined stackLayouts stackOf ringMap h _ _ (loopChallenges_length H _ _ _ _ _)

/-- **`batchKH .main` accepts the honest batching sumcheck**: the verifier returns the prover's point claims and
collects zero (`BatchSyncs` at the zero terminal), for the honest batch (`BatchHolds`: every combined claim holds and
is well formed on its aligned layout, its stack of `2^vars` words). -/
theorem batchSyncs_honest (H : List UInt8 → Digest) (combined : List (Commitment × Combined))
    (stackLayouts : List (Commitment × StackLayout)) (stackOf : Commitment → Array K) (ringMap : Option (List E))
    (h : BatchHolds combined stackLayouts stackOf ringMap) :
    BatchSyncs H combined stackLayouts stackOf ringMap (fun _ ↦ 0) := by
  intro w
  have := batchSyncs H combined stackLayouts stackOf ringMap w
  rwa [batchTerminal_eq_zero H combined stackLayouts stackOf ringMap h w] at this

end UniKeccakComplete

/-- info: 'UniKeccakComplete.batchSyncs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.batchSyncs

/-- info: 'UniKeccakComplete.batchTerminal_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.batchTerminal_eq_zero

/-- info: 'UniKeccakComplete.batchSyncs_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.batchSyncs_honest

/-- info: 'UniKeccakComplete.collectedAt_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniKeccakComplete.collectedAt_eq_zero
