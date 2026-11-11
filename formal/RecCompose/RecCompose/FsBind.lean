-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md; conventions: see AGENTS.md. `Q`'s three claims on one
-- root: `formal/WhirBridge/WhirBridge/PcsBinding.lean`'s `two_openings_one_polynomial` (the out-of-domain answer binds
-- a root whose list is separated at its point) in the composed game, after `formal/Compose/Compose/GOps.lean`'s
-- `prEvent_doomFG_le_union` (the event at the run's end read off the cache, `expLG_replayF`).
import RecCompose.FsOps

/-!
# `Q`'s three claims, one stack: the out-of-domain answer's binding

π2's contract opens `Q`'s three claims (the identity's, the pushes', the sum) separately, each the EIP's PCS claim on
`Q`'s commitment `(root, ood)` (`qIdOp`, `qPushOp`, `qSumOp`). The chain's composition needs one candidate of `Q`'s
root satisfying all three (`p2Good 1`): it opens them as one (`qOp`, whose claims are the three on one stack). Its
doom is the eight single openings' (charged once, `hU_pcs`), or **`Q`'s root's list is not separated at its
out-of-domain point** (`QBindBad`): three single openings that accept and are not doomed have candidates with the
same answer `ood` at `z = oodPoint 28 root`, one candidate when the list is separated there.

* `expLG_p2Ops`: the run with `qOp` is the run with the eight single openings, `Q`'s three verdicts and-ed (`mergeB`);
* `doomFG_p2Ops`: its doom is the eight's or `QBindBad`;
* **`prEvent_doomFG_p2Ops_le`**: at most `bndU (QX + 80976) + δ (QX + 80976)` for a run before the openings of `QX`
  queries, under **`QOodBinding δ`**: every computation of `QA` queries ends with a root whose list, read off the final
  Keccak-256 answers, is separated at `Pcs.oodPoint 28 root` but with probability at most `δ QA`.

**`QOodBinding` is a premise.** `WhirBridge.Pcs.ood_binding_rom` proves it at
`δ QA = QA · δood 28 + QA (QA + 1) / 2^256` (`δood 28 ≤ 2^-156`, `δood_le`) for the out-of-domain point a random
oracle of the root. The Statement's contract derives the point with `keccak256` (`WhirBridge.Pcs.oodPoint`:
Keccak-f[1600] itself, not the permutation the model idealizes), a fixed function of the root in the
random-permutation model, so the binding cannot be proved there: it is the out-of-domain point's random-oracle
heuristic, the one the EIP's security claim makes (`docs/PCS_CLAIM.md`).
-/

set_option linter.unusedSectionVars false

namespace RecCompose

open RecStatement Compose QuotientRpm LeanVM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd WhirBridge
open OracleSpec OracleComp
open scoped ENNReal

attribute [local irreducible] LeanVM.Protocol.Compile.instFintypeDigest
  LeanVM.Protocol.Compile.instFintypeKState

/-! ## The premise -/

/-- **The out-of-domain answer binds a commitment of `28` variables**, at the deployed out-of-domain point: a
computation of at most `QA` queries of Keccak-256 and Keccak-f[1600] ends with a root whose list (the candidates of the
word under it, read off the final Keccak-256 answers, `Pcs.rootList`) is not separated at `Pcs.oodPoint 28 root` with
probability at most `δ QA`. -/
def QOodBinding (δ : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : OracleComp KeccakCalls Digest) (QA : ℕ), IsTotalQueryBound A QA →
    Pr{let z ← (simulateQ randomOracle A).run ∅}[
      ¬ Pcs.SepAt (Pcs.rootList (n := 28) (fun x ↦ z.2 (.inl x)) z.1) (Pcs.oodPoint 28 z.1)] ≤ δ QA

/-- The binding's bound of the random-oracle theorem (`WhirBridge.Pcs.ood_binding_rom`) at `28` variables. -/
noncomputable def δBind (QA : ℕ) : ℝ≥0∞ :=
  (QA : ℝ≥0∞) * Pcs.δood 28 + ((QA * (QA + 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256

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

/-- **`Q`'s root's list is not separated at its out-of-domain point**, in a cache. -/
def QBindBad (π : P2Pf) (c : KeccakCalls.QueryCache) : Prop :=
  ¬ Pcs.SepAt (Pcs.rootList (n := 28) (fun x ↦ c (.inl x)) (qRoot π)) (Pcs.oodPoint 28 (qRoot π))

/-- A `Q` opening that accepts and is not doomed has a candidate of `Q`'s root its claim holds of. -/
theorem holds_of_not_doomed (lo : 23 ≤ 28) (hi : 28 ≤ 28) (cl : P2Pf → List (List E) → Option (E × List E × E))
    (prf : P2Pf → Compile.Proof) (tgt : Tgt P2Pf Stk 28) (π : P2Pf) (ch : List (List E))
    (c : KeccakCalls.QueryCache) (hr : PcsOp.rootB ⟨28, lo, hi, cl, prf, tgt⟩ π = GOp.root p2View qOp π)
    (h : ¬ GDoomed p2View (PcsOp.gop ⟨28, lo, hi, cl, prf, tgt⟩) π ch c) :
    ∃ q : Column 28, q ∈ Pcs.rootList (n := 28) (fun x ↦ c (.inl x)) (qRoot π) ∧
      PcsOp.holds ⟨28, lo, hi, cl, prf, tgt⟩ π ch q := by
  unfold GDoomed at h
  push Not at h
  obtain ⟨q, hq, hh⟩ := h
  rw [PcsOp.root_gop, hr] at hq
  exact ⟨q, hq, hh⟩

/-- **`qOp`'s doom is the eight's, or `Q`'s binding fails.** -/
theorem doomFG_p2Ops (D : RecDeployment) (z : OutK P2Pf E (List Bool) × Transcript)
    (hd : DoomFG p2View (p2Ops D) (remapO z)) :
    DoomFG p2View (p2Ops8 D) z ∨ QBindBad z.1.1.1 (cacheOfTr z.2) := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨h8, hsep⟩ := hn
  unfold QBindBad at hsep
  push Not at hsep
  obtain ⟨k, hk, hacc, hdoom⟩ := hd
  have hk6 : k < 6 := by simpa [p2Ops, p2Pcs5] using hk
  set bs := z.1.1.2.2 with hbs
  have hm : ∀ j < 5, (mergeB bs).getD j false = bs.getD j false := by
    intro j hj
    interval_cases j <;> rfl
  have h8' : ∀ j (hj : j < (p2Ops8 D).length), bs.getD j false = true →
      ¬ GDoomed p2View (p2Ops8 D)[j] z.1.1.1 z.1.1.2.1 (cacheOfTr z.2) :=
    fun j hj hb hdj => h8 ⟨j, hj, hb, hdj⟩
  rcases Nat.lt_or_ge k 5 with h5 | h5
  · -- one of the first five: the eight's
    refine h8' k (by simp [p2Ops8, p2Pcs, p2Pcs5]; omega) ((hm k h5).symm.trans hacc) ?_
    have e : (p2Ops D)[k] = (p2Ops8 D)[k]'(by simp [p2Ops8, p2Pcs, p2Pcs5]; omega) := by
      interval_cases k <;> rfl
    rw [← e]
    exact hdoom
  · -- `Q`'s: three accepting single openings, not doomed, one candidate
    obtain rfl : k = 5 := by omega
    have hacc' : (bs.getD 5 false && (bs.getD 6 false && bs.getD 7 false)) = true := hacc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hacc'
    obtain ⟨a5, a6, a7⟩ := hacc'
    have n5 : ¬ GDoomed p2View qIdOp.gop z.1.1.1 z.1.1.2.1 (cacheOfTr z.2) :=
      h8' 5 (by simp [p2Ops8, p2Pcs, p2Pcs5]) a5
    have n6 : ¬ GDoomed p2View qPushOp.gop z.1.1.1 z.1.1.2.1 (cacheOfTr z.2) :=
      h8' 6 (by simp [p2Ops8, p2Pcs, p2Pcs5]) a6
    have n7 : ¬ GDoomed p2View qSumOp.gop z.1.1.1 z.1.1.2.1 (cacheOfTr z.2) :=
      h8' 7 (by simp [p2Ops8, p2Pcs, p2Pcs5]) a7
    obtain ⟨q1, hq1, h1⟩ := holds_of_not_doomed (by norm_num) le_rfl qIdCl (fun π => π.proof.qId)
      (.round 1 (rdP 28)) _ _ _ rfl n5
    obtain ⟨q2, hq2, h2⟩ := holds_of_not_doomed (by norm_num) le_rfl qPushCl (fun π => π.proof.qPush)
      (.round 1 (rdP 28)) _ _ _ rfl n6
    obtain ⟨q3, hq3, h3⟩ := holds_of_not_doomed (by norm_num) le_rfl qSumCl (fun π => π.proof.qSum)
      (.round 1 (rdP 28)) _ _ _ rfl n7
    obtain ⟨o1, p1, v1, c1, -, z1, -⟩ := id h1
    obtain ⟨o2, p2, v2, c2, -, z2, -⟩ := id h2
    obtain ⟨o3, p3, v3, c3, -, z3, -⟩ := id h3
    simp only [qIdCl, qPushCl, qSumCl, Option.some.injEq, Prod.mk.injEq] at c1 c2 c3
    obtain ⟨rfl, -, -⟩ := c1
    obtain ⟨rfl, -, -⟩ := c2
    obtain ⟨rfl, -, -⟩ := c3
    have e12 : q1 = q2 := hsep q1 hq1 q2 hq2 (z1.trans z2.symm)
    have e13 : q1 = q3 := hsep q1 hq1 q3 hq3 (z1.trans z3.symm)
    subst e12 e13
    exact hdoom q1 hq1 ⟨h1, h2, h3⟩

/-! ## The doom, charged -/

/-- The eight openings' query counts. -/
theorem sumQO_p2Ops8 (D : RecDeployment) : ((p2Ops8 D).map fun o => o.QO).sum = 80976 := by
  simp [p2Ops8, p2Pcs, p2Pcs5, PcsOp.gop]

/-- **`Q`'s binding fails at the run's end** with probability at most `δ (QX + 80976)`. -/
theorem prEvent_qBindBad_le (D : RecDeployment) (X : OracleComp KeccakCalls (PreK P2Pf E)) (QX : ℕ)
    (hX : IsTotalQueryBound X QX) (δ : ℕ → ℝ≥0∞) (hB : QOodBinding δ) :
    Pr{let z ← (simulateQ randomOracle (expLG p2View X (p2Ops8 D))).run' ∅}[QBindBad z.1.1.1 (cacheOfTr z.2)] ≤
      δ (QX + 80976) := by
  have hA := isTotalQueryBound_expLG p2View X (p2Ops8 D) QX hX
  rw [sumQO_p2Ops8] at hA
  refine le_trans ?_ (hB ((fun z => qRoot z.1.1.1) <$> expLG p2View X (p2Ops8 D)) _
    ((isQueryBound_map_iff _ _ _ _ _).mpr hA))
  rw [StateT.run'_eq, prEvent_map, simulateQ_map, StateT.run_map, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun p hp hbad => ?_
  have hcons := (expLG_replayF p2View X (p2Ops8 D) p hp).1
  have hc : (fun x ↦ p.2 (.inl x)) = fun x ↦ cacheOfTr p.1.2 (.inl x) :=
    funext fun x ↦ (hcons x).trans (cacheOfTr_inl _ _).symm
  show ¬ Pcs.SepAt (Pcs.rootList (n := 28) (fun x ↦ p.2 (.inl x)) (qRoot p.1.1.1.1))
    (Pcs.oodPoint 28 (qRoot p.1.1.1.1))
  rw [hc]
  exact hbad

/-- **The composition's openings' doom, charged**: the eight single openings once (`hU_pcs`), and `Q`'s binding. -/
theorem prEvent_doomFG_p2Ops_le (D : RecDeployment) (X : OracleComp KeccakCalls (PreK P2Pf E)) (QX : ℕ)
    (hX : IsTotalQueryBound X QX) (δ : ℕ → ℝ≥0∞) (hB : QOodBinding δ) :
    Pr{let z ← (simulateQ randomOracle (expLG p2View X (p2Ops D))).run' ∅}[DoomFG p2View (p2Ops D) z] ≤
      bndU (QX + 80976) + δ (QX + 80976) := by
  rw [expLG_p2Ops, run'_simulateQ_map, prEvent_map]
  refine (prEvent_mono _ _ _ fun z hz => doomFG_p2Ops D z hz).trans ((prEvent_or_le _ _ _).trans
    (add_le_add ?_ (prEvent_qBindBad_le D X QX hX δ hB)))
  have h := prEvent_doomFG_le p2View (p2Ops8 D) bndU (hU_pcs (p2Pcs D)) X QX hX
  rwa [sumQO_p2Ops8] at h

end RecCompose

/-- info: 'RecCompose.prEvent_doomFG_p2Ops_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecCompose.prEvent_doomFG_p2Ops_le
