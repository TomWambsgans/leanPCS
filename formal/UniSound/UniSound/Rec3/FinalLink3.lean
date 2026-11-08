-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The statement is `Rec3/Fs3.lean`'s `UniFinal3`; the
-- proof follows `FinalLink.lean`'s `uniFinal` (the main line's), without the pending matrices' term.
import UniSound.Rec3.CodeLink3
import UniSound.Ids.Build
import UniSound.Rec3.BusSq
import UniSound.Rec3.Piop3
import FlockSoundUni.Rec3Catch
import UniSound.Prog
import UniSound.FlockInterface
import UniStatement.RecSecurity
import UniSound.Rec3.Batch3
import UniSound.Ids.Align
import FlockSoundUni.Good

/-!
# The last link at π1-rec3 (`UniFinal3`)

**`uniFinal3`**: for π1-rec3's identity model `ids3Of D N h d n g tx hw np hV` (the main line's at the expanded
transcripts, `Rec3/Ids3.lean`), Flock's phase `flockSound3_of tx hw`, the paired batch `pairBatchRec3 np` and the
code-level link `uniCode3At`, on a completed transcript whose zeros vanish and whose three claims are true:

* **the pending claim is its sum**: Flock's segment of the transcript has its zeros among the chain program's
  (`zeros3`: rounds `1 … nF`, and the tail zeros in `C2`'s round), so the walk (`FlockSound3.walk`) applies;
* **the batch's last state holds** (`BatchState3 cantorBeta1 narrowE` at the batch's point `pointAfter3`), unless `t`
  is a root of the merge polynomial: the terminal zero `sum + last = 0` is `last = Σ_k λ^k W_k(r) ext_k(r) v_k`, the
  claims give `v_k = Ĉ_k(r)`, the weights are multilinear at `r` (`WeightMle`, the main line's, at the expanded
  transcripts: the batch's point is any point of `E^V`), so `last` is the products' partial sum at the full point
  (`batchState3_full_np`, `terminal3`). The identity model's batch is the verifier's (`main3Out_aligned`: the run's
  claims are `combAt` at `expandCh`, `expandFd`, `runClaims_eq`; Flock's result the main line's, `flockGood`), so the
  main line's `BatchIsVerifiers` is not a hypothesis here.

**Hypotheses** (the main line's, unchanged): `WeightMle` at the main line's Flock instance and merge polynomial, and
`LayoutVarsSmall`. Both are discharged at the reference deployment (`Rec3/FinalRef3.lean`).
-/

namespace UniSound

open UniStatement LeanVM.Parameters LeanVM.Semantics Finset FlockSound.Uni UniSound.Ids

/-! ## The terminal -/

/-- The batch's target over one claim per commitment. -/
theorem batchTarget_commitments (f : Commitment → Combined) (lam : E) :
    (batchTarget (commitments.map fun c => (c, f c)) lam).1 = ∑ k ∈ range 3, lam ^ k * (f (cm k)).value := by
  simp only [batchTarget, commitments, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    Finset.sum_range_succ, Finset.sum_range_zero, cm, List.getD_cons_zero, List.getD_cons_succ]
  ring

/-- **The batch's terminal check with true claims is the last claim's value** (the algebra of `UniFinal3`): the
terminal `sum + last = 0` with the stacks' point claims and the weights multilinear at the point makes `last` the
products' value there. -/
theorem terminal3 (f : Commitment → Combined) (L : List (Commitment × StackLayout)) (bs : Option Combined)
    (rm : Option (List E)) (lam : E) (brs : Done) (tl : List E) (stk : Commitment → Stk) (np : ℕ)
    (hnp : varsOf L / 2 = np) (htl : tl.length = 3)
    (hrl : (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)).length = varsOf L)
    (hz : ∀ z ∈ (batchPureW narrowE (commitments.map fun c => (c, f c)) L bs rm lam brs tl).1, z = 0)
    (hclaims : ∀ o ∈ (batchPureW narrowE (commitments.map fun c => (c, f c)) L bs rm lam brs tl).2,
      ∀ pt v bs', o.2 = .point pt v bs' → mleStk (stk o.1) (layoutOf L o.1).vars pt = v)
    (hW : ∀ c, foldAll (fun u => weightAt (f c) (layoutOf L c) (bitsE u (varsOf L)) rm)
        (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) 0 =
      weightAt (f c) (layoutOf L c) (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) rm) :
    claimAfter3 narrowE np (batchTarget (commitments.map fun c => (c, f c)) lam).1 (roundsOf brs) =
      ∑ k ∈ range 3, lam ^ k *
        (foldAll (fun u => weightAt (f (cm k)) (layoutOf L (cm k)) (bitsE u (varsOf L)) rm)
            (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) 0 *
          foldAll (fun u => stE (stk (cm k)) (layoutOf L (cm k)).vars u)
            (pointAfter3 cantorBeta1 narrowE np (roundsOf brs)) 0) := by
  subst hnp
  unfold batchPureW at hz hclaims
  generalize pointAfter3 cantorBeta1 narrowE (varsOf L / 2) (roundsOf brs) = r at hz hclaims hrl hW ⊢
  generalize claimAfter3 narrowE (varsOf L / 2) (batchTarget (commitments.map fun c => (c, f c)) lam).1
    (roundsOf brs) = cl at hz ⊢
  rcases tl with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, tl'⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at htl <;> try omega
  simp only [commitments, List.map_cons, List.map_nil, batchFold, List.length_cons, List.length_nil,
    List.take_succ_cons, List.take_zero, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons,
    List.foldl_nil] at hz hclaims
  have hcl := eq_of_add_eq_zero_char2 (hz _ (List.mem_singleton_self _))
  simp only [Array.toList_push, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hclaims
  obtain ⟨hc1, hc2, hc3⟩ := hclaims
  have hc1 := hc1 _ _ _ rfl
  have hc2 := hc2 _ _ _ rfl
  have hc3 := hc3 _ _ _ rfl
  have hv1 := layoutOf_vars_le L .c1
  have hv2 := layoutOf_vars_le L .c2
  have hv3 := layoutOf_vars_le L .setup
  rw [hcl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cm, commitments, List.getD_cons_zero,
    List.getD_cons_succ, zero_add]
  rw [hW .c1, hW .c2, hW .setup]
  unfold stE
  rw [foldAll_stackExt _ _ r (by omega), foldAll_stackExt _ _ r (by omega), foldAll_stackExt _ _ r (by omega),
    hc1, hc2, hc3, ← hrl, extension_eq_cubeEq, extension_eq_cubeEq, extension_eq_cubeEq]
  ring

/-! ## The run's claims are the identity model's -/

/-- `flockClaim` reads only Flock's point and end. -/
theorem flockClaim_congr (rels : Array Relation) {fl fl' : List E × Option Flock.End × Flock.Pending}
    (h1 : fl.1 = fl'.1) (h2 : fl.2.1 = fl'.2.1) : flockClaim rels fl = flockClaim rels fl' := by
  obtain ⟨a, b, p⟩ := fl
  obtain ⟨a', b', p'⟩ := fl'
  simp only at h1 h2
  subst h1 h2
  rfl

/-! ## Flock's zeros in the chain program's -/

/-- **Flock's segment's zeros are the chain program's** there: a program whose zeros after `x0 :: e` are Flock's after
`e` (for `e` shorter than Flock's rounds) and whose zeros after `x0 :: G` are Flock's tail zeros has, on a transcript
`x0 :: (G ++ x2 :: R)` whose zeros vanish, Flock's zeros vanishing on `G`. -/
theorem zerosVanish_flock {α β : Type} (P : ChainProg α) (Pf : ChainProg β) (x0 x2 : UMsg × List E) (G R : Done)
    (hG : G.length = Pf.rounds.length)
    (hzf : ∀ e msg, e.length < Pf.rounds.length → P.zeros (x0 :: e) msg = Pf.zeros e msg)
    (hzt : ∀ msg, P.zeros (x0 :: G) msg = Pf.tailZeros G [])
    (hz : ∀ j (h : j < (x0 :: (G ++ x2 :: R)).length),
      ∀ z ∈ P.zeros ((x0 :: (G ++ x2 :: R)).take j) ((x0 :: (G ++ x2 :: R))[j]'h).1, z = 0) :
    Pf.ZerosVanish G [] := by
  refine ⟨fun j hj z hzj => ?_, fun z hzt' => ?_⟩
  · have h1 := hz (j + 1) (by simp; omega) z
    simp only [List.take_succ_cons, List.getElem_cons_succ] at h1
    rw [List.take_append_of_le_length (by omega), List.getElem_append_left hj,
      hzf _ _ (by rw [List.length_take]; omega)] at h1
    exact h1 hzj
  · have h1 := hz (G.length + 1) (by simp) z
    simp only [List.take_succ_cons, List.getElem_cons_succ] at h1
    rw [List.take_append_of_le_length le_rfl, List.take_length, hzt] at h1
    exact h1 hzt'

/-! ## The last link -/

end UniSound

/-- info: 'UniSound.terminal3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UniSound.terminal3
