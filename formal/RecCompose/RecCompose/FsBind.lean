-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md; conventions: see AGENTS.md. `Q`'s three claims on one
-- root: `formal/WhirBridge/WhirBridge/PcsBindingCoords.lean`'s `ood_binding_coords` (the out-of-domain answer binds a
-- root whose list is separated at its point, the point read off Keccak-256) in the composed game, after
-- `formal/Compose/Compose/GOps.lean`'s `prEvent_doomFG_le_union` (the event at the run's end read off the cache,
-- `expLG_replayF`).
import RecCompose.FsOps

/-!
# `Q`'s three claims, one stack: the out-of-domain answer's binding

π2's contract opens `Q`'s three claims (the identity's, the pushes', the sum) separately, each the EIP's PCS claim on
`Q`'s commitment `(root, ood)` (`qIdOp`, `qPushOp`, `qSumOp`), each reading `Q`'s out-of-domain point off Keccak-256
(`RecStatement.pcsOpenKO`, `pcsOpenCO`: `28` queries `oodInput 28 root j`). The chain's composition needs one candidate
of `Q`'s root satisfying all three (`p2Good 1`): it opens them as one (`qOp`, whose claims are the three on one stack).
Its doom is the eight single openings' (charged once, `prEvent_doomH_le`: each opening's PCS claim's two claims, the
point read off the final cache), or **`Q`'s root's list is not separated at its out-of-domain point**
(`WhirBridge.Pcs.BindBadC 28`): three single openings that accept and are not doomed have candidates with the same answer
`ood` at `z`, the point read off the final cache (all of whose coordinates the accepting openings asked:
`PcsOp.present`), one candidate when the list is separated there.

* `expLG_p2Ops`: the run with `qOp` is the run with the eight single openings, `Q`'s three verdicts and-ed (`mergeB`);
* `doomFG_p2Ops_cases`: its doom is the eight's (`DoomH`) or `BindBadC 28` at the final cache;
* **`qOodBinding`**: `BindBadC 28` at the end of a computation of `QA` queries has probability at most
  `δBind QA = QA · δc 28 + QA (QA + 1) / 2^256` (`WhirBridge.Pcs.ood_binding_coords`; `δc 28 = C(L_Q, 2) / 2^192 ≤
  2^-160`, `L_Q = 3564`): the premise `QOodBinding` of the earlier form, proved, the point being read off the
  permutation the model idealizes;
* **`prEvent_doomFG_p2Ops_le`**: at most `bndU (QX + 81200) + δBind (QX + 81200)` for a run before the openings of
  `QX` queries.
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The binding -/

/-- **The binding's bound** (`WhirBridge.Pcs.ood_binding_coords` at `28` variables). -/
noncomputable def δBind (QA : ℕ) : ℝ≥0∞ :=
  (QA : ℝ≥0∞) * Pcs.δc 28 + ((QA * (QA + 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256

/-- **The out-of-domain answer binds a commitment of `28` variables**, the point read off Keccak-256: a computation of
at most `QA` queries of Keccak-256 and Keccak-f[1600] ends with a root all of whose `28` out-of-domain coordinates it
asked and whose list (read off the final Keccak-256 answers) is not separated at the point they give with
probability at most `δBind QA`. -/
theorem qOodBinding {α : Type} (A : OracleComp KeccakCalls α) (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← (simulateQ randomOracle A).run ∅}[Pcs.BindBadC 28 z.2] ≤ δBind QA :=
  Pcs.ood_binding_coords (Pcs.admissible_v1 28 (by decide) (by decide)) A QA hA

/-- `δc 28 ≤ 2^-160`. -/
theorem δc_28_le : Pcs.δc 28 ≤ (2 : ℝ≥0∞)⁻¹ ^ 160 := Pcs.δc_le (by decide) (by decide)

/-! ## The run with `Q`'s three as one -/

/-- The run's outcome with `Q`'s three verdicts and-ed. -/
def remapO (z : OutK P2Pf E (List Bool) × Transcript) : OutK P2Pf E (List Bool) × Transcript :=
  (((z.1.1.1, (z.1.1.2.1, mergeB z.1.1.2.2)), z.1.2), z.2)

/-- **The run with `qOp` is the run with the eight single openings**, `Q`'s three verdicts and-ed. -/
theorem expLG_p2Ops (D : RecDeployment) (X : OracleComp KeccakCalls (PreK P2Pf E)) :
    expLG p2View X (p2Ops D) = remapO <$> expLG p2View X (p2Ops8 D) := by
  unfold expLG
  have e : (X >>= fun x => opsOut x <$> gopsRun p2View (p2Ops D) x.1 x.2.1) =
      (fun o : OutK P2Pf E (List Bool) => ((o.1.1, (o.1.2.1, mergeB o.1.2.2)), o.2)) <$>
        (X >>= fun x => opsOut x <$> gopsRun p2View (p2Ops8 D) x.1 x.2.1) := by
    simp only [gopsRun_p2Ops, map_bind, Functor.map_map]
    rfl
  rw [e, simulateQ_map, StateT.run_map]
  rfl

/-- The root `Q`'s openings read. -/
noncomputable def qRoot (π : P2Pf) : Digest := ofB (GOp.root p2View qOp π)

/-- **An accepting opening at π2's sizes asked its root's out-of-domain point**: a run that returns `true` from the
cache `c` without changing it finds every coordinate's input in `c`. -/
theorem PcsOp.present (o : PcsOp) (hs : RecStatement.pi2Size o.n = true) (π : P2Pf) (ch : List (List E))
    (c : KeccakCalls.QueryCache) (h : (simulateQ randomOracle (GOp.run p2View o.gop π ch)).run c = pure (true, c)) :
    ∀ j < o.n, c (.inl (Pcs.oodInput o.n (ofB (o.rootB π)) j)) ≠ none := by
  have hmem : ((true, c) : Bool × KeccakCalls.QueryCache) ∈
      support ((simulateQ randomOracle (GOp.run p2View o.gop π ch)).run c) := by
    rw [h]
    simp
  unfold GOp.run at hmem
  rw [PcsOp.root_gop] at hmem
  change (true, c) ∈ support ((simulateQ randomOracle (o.ver (ofB (o.rootB π)) π ch)).run c) at hmem
  unfold PcsOp.ver at hmem
  rcases hc : o.cl π ch with _ | ⟨ood, pt, v⟩
  · rw [hc] at hmem
    simp at hmem
  · rw [hc] at hmem
    dsimp only at hmem
    rw [ite_eq_left hs] at hmem
    unfold pcsOpenCO at hmem
    by_cases hl : pt.length = o.n
    · rw [dite_eq_left hl] at hmem
      exact Pcs.UnionO.verifierO_present_of Pcs.UnionO.grows_randomOracle _ c (true, c) hmem rfl
    · rw [dite_eq_right hl] at hmem
      simp at hmem

/-- With every coordinate asked, the point read off the answers is `zOfH`. -/
theorem oodPointOf_eq_zOfH (H : Bytes → Option Digest) (n : ℕ) (r : Digest)
    (h : ∀ j < n, H (Pcs.oodInput n r j) ≠ none) : Pcs.oodPointOf H n r = some (zOfH H n r) := by
  have hs : ∀ j : Fin n, (H (Pcs.oodInput n r j)).isSome := fun j => Option.isSome_iff_ne_none.mpr (h j j.isLt)
  unfold Pcs.oodPointOf
  rw [dite_eq_left hs, Option.some.injEq]
  unfold zOfH
  refine congrArg Vector.ofFn (funext fun j => ?_)
  rw [Option.get_eq_getD (fallback := default)]
  rfl

/-- A `Q` opening not doomed has a candidate of `Q`'s root on which its two claims hold, the point read off `H`. -/
theorem cand_of_not_doomedH (o : PcsOp) (π : P2Pf) (ch : List (List E)) (H : Bytes → Option Digest)
    (h : ¬ o.DoomedH π ch H) :
    ∃ q ∈ Candidates o.n logInvRate (code₀ o.n logInvRate).thr
        (Rom.extract H (ofB (o.rootB π)) (rootHeight o.n logInvRate) (2 ^ laneFold)),
      ∃ ood pt v, o.cl π ch = some (ood, pt, v) ∧ pt.length = o.n ∧
        Pcs.colEval q (ptAt o.n H (ofB (o.rootB π))).toList = ood ∧ Pcs.colEval q pt = v := by
  unfold PcsOp.DoomedH at h
  push Not at h
  exact h

/-- **`qOp`'s doom is the eight's, or `Q`'s binding fails**, at the end of the run with the eight single openings
(the outcome `p.1`, the final cache `p.2`). -/
theorem doomFG_p2Ops_cases (D : RecDeployment) (X : OracleComp KeccakCalls (PreK P2Pf E))
    (p : (OutK P2Pf E (List Bool) × Transcript) × KeccakCalls.QueryCache)
    (hp : p ∈ support ((simulateQ randomOracle (expLG p2View X (p2Ops8 D))).run ∅))
    (hd : DoomFG p2View (p2Ops D) (remapO p.1)) :
    DoomH (p2Pcs D) p.1 (fun x ↦ p.2 (.inl x)) ∨ Pcs.BindBadC 28 p.2 := by
  classical
  obtain ⟨hcons, hrep⟩ := expLG_replayF p2View X (p2Ops8 D) p hp
  have hc : (fun x ↦ p.2 (.inl x)) = fun x ↦ cacheOfTr p.1.2 (.inl x) :=
    funext fun x ↦ (hcons x).trans (cacheOfTr_inl _ _).symm
  by_contra hn
  push Not at hn
  obtain ⟨h8, hsep⟩ := hn
  obtain ⟨k, hk, hacc, hdoom⟩ := hd
  have hdoom' : GDoomed p2View (p2Ops D)[k] p.1.1.1.1 p.1.1.1.2.1 p.2 := by
    have h' : GDoomed p2View (p2Ops D)[k] p.1.1.1.1 p.1.1.1.2.1 (cacheOfTr p.1.2) := hdoom
    unfold GDoomed at h' ⊢
    rw [hc]
    exact h'
  have hk6 : k < 6 := by simpa [p2Ops, p2Pcs5] using hk
  set bs := p.1.1.1.2.2 with hbs
  have hacc' : (mergeB bs).getD k false = true := hacc
  have hm : ∀ j < 5, (mergeB bs).getD j false = bs.getD j false := by
    intro j hj
    interval_cases j <;> rfl
  have h8' : ∀ j (hj : j < (p2Pcs D).length), bs.getD j false = true →
      ¬ (p2Pcs D)[j].DoomedH p.1.1.1.1 p.1.1.1.2.1 (fun x ↦ p.2 (.inl x)) :=
    fun j hj hb hdj => h8 ⟨j, hj, hb, hdj⟩
  rcases Nat.lt_or_ge k 5 with h5 | h5
  · -- one of the first five: the eight's
    refine h8' k (by simp [p2Pcs, p2Pcs5]; omega) ((hm k h5).symm.trans hacc') ?_
    interval_cases k <;> exact PcsOp.doomedH_of_gDoomed _ _ _ _ hdoom'
  · -- `Q`'s: three accepting single openings, not doomed, one candidate
    obtain rfl : k = 5 := by omega
    have hacc5 : (bs.getD 5 false && (bs.getD 6 false && bs.getD 7 false)) = true := hacc'
    rw [Bool.and_eq_true, Bool.and_eq_true] at hacc5
    obtain ⟨a5, a6, a7⟩ := hacc5
    have n5 : ¬ qIdOp.DoomedH p.1.1.1.1 p.1.1.1.2.1 (fun x ↦ p.2 (.inl x)) :=
      h8' 5 (by simp [p2Pcs, p2Pcs5]) a5
    have n6 : ¬ qPushOp.DoomedH p.1.1.1.1 p.1.1.1.2.1 (fun x ↦ p.2 (.inl x)) :=
      h8' 6 (by simp [p2Pcs, p2Pcs5]) a6
    have n7 : ¬ qSumOp.DoomedH p.1.1.1.1 p.1.1.1.2.1 (fun x ↦ p.2 (.inl x)) :=
      h8' 7 (by simp [p2Pcs, p2Pcs5]) a7
    -- the first `Q` opening accepted: its point's coordinates are in the cache
    have hr5 := hrep 5 (by simp [p2Ops8, p2Pcs, p2Pcs5])
    have hr5' : (simulateQ randomOracle (GOp.run p2View qIdOp.gop p.1.1.1.1 p.1.1.1.2.1)).run p.2 =
        pure (true, p.2) := by
      rw [← a5]
      exact hr5
    have hpres := PcsOp.present qIdOp (by decide) _ _ _ hr5'
    have hpt : Pcs.oodPointOf (fun x ↦ p.2 (.inl x)) 28 (qRoot p.1.1.1.1) =
        some (zOfH (fun x ↦ p.2 (.inl x)) 28 (qRoot p.1.1.1.1)) :=
      oodPointOf_eq_zOfH _ 28 _ hpres
    have hS : Pcs.SepAt (Pcs.rootList (n := 28) (fun x ↦ p.2 (.inl x)) (qRoot p.1.1.1.1))
        (zOfH (fun x ↦ p.2 (.inl x)) 28 (qRoot p.1.1.1.1)) := by
      by_contra hns
      exact hsep ⟨_, _, hpt, hns⟩
    obtain ⟨q1, hq1, o1, p1, v1, c1, l1, z1, e1⟩ := cand_of_not_doomedH qIdOp _ _ _ n5
    obtain ⟨q2, hq2, o2, p2, v2, c2, l2, z2, e2⟩ := cand_of_not_doomedH qPushOp _ _ _ n6
    obtain ⟨q3, hq3, o3, p3, v3, c3, l3, z3, e3⟩ := cand_of_not_doomedH qSumOp _ _ _ n7
    simp only [ptAt] at z1 z2 z3
    simp only [qIdOp, qPushOp, qSumOp, qIdCl, qPushCl, qSumCl, Option.some.injEq, Prod.mk.injEq] at c1 c2 c3
    obtain ⟨rfl, rfl, rfl⟩ := c1
    obtain ⟨rfl, rfl, rfl⟩ := c2
    obtain ⟨rfl, rfl, rfl⟩ := c3
    have e12 : q1 = q2 := hS q1 hq1 q2 hq2 (z1.trans z2.symm)
    have e13 : q1 = q3 := hS q1 hq1 q3 hq3 (z1.trans z3.symm)
    subst e12 e13
    exact hdoom' q1 hq1 ⟨⟨_, _, _, rfl, l1, e1⟩, ⟨_, _, _, rfl, l2, e2⟩, ⟨_, _, _, rfl, l3, e3⟩⟩

/-! ## The doom, charged -/

/-- The eight openings' query counts. -/
theorem sumQO_p2Ops8 (D : RecDeployment) : ((p2Ops8 D).map fun o => o.QO).sum = 81200 := by
  simp [p2Ops8, p2Pcs, p2Pcs5, PcsOp.gop]

/-- **The composition's openings' doom, charged**: the eight single openings once (`prEvent_doomH_le`), and `Q`'s
binding (`qOodBinding`). -/
theorem prEvent_doomFG_p2Ops_le (D : RecDeployment) (X : OracleComp KeccakCalls (PreK P2Pf E)) (QX : ℕ)
    (hX : IsTotalQueryBound X QX) :
    Pr{let z ← (simulateQ randomOracle (expLG p2View X (p2Ops D))).run' ∅}[DoomFG p2View (p2Ops D) z] ≤
      bndU (QX + 81200) + δBind (QX + 81200) := by
  rw [expLG_p2Ops, run'_simulateQ_map, prEvent_map, StateT.run'_eq, prEvent_map]
  refine (prEvent_mono_of_support _ _ _ fun p hp hd => doomFG_p2Ops_cases D X p hp hd).trans
    ((prEvent_or_le _ _ _).trans (add_le_add ?_ ?_))
  · have h := prEvent_doomH_le (p2Pcs D) X QX hX
    change _ ≤ bndU (QX + ((p2Ops8 D).map fun o => o.QO).sum) at h
    rwa [sumQO_p2Ops8] at h
  · have hA := isTotalQueryBound_expLG p2View X (p2Ops8 D) QX hX
    rw [sumQO_p2Ops8] at hA
    exact qOodBinding _ _ hA

end RecCompose

/-- info: 'RecCompose.qOodBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.qOodBinding

/-- info: 'RecCompose.prEvent_doomFG_p2Ops_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.prEvent_doomFG_p2Ops_le
