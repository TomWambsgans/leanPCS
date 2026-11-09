-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The two transcriptions are
-- `Rels.lean`'s `relsOf` (the identity model's) and `CodeLink.lean`'s `mainRels`, `flockClaim` (the
-- code-level link's), both of `formal/UniStatement`'s `reduceWith`, steps 4–7.
import UniSound.FinalLink
import UniSound.Ids.Build

/-!
# The identity model's batch is the verifier's (`BatchIsVerifiers`)

The relations at `t` are transcribed twice: by the identity model (`relsOf`: `tablePartOf` consumes
the values at `t` from a list, `flushStep` a fingerprint at a time) and by the code-level link
(`mainRels`: `tablePartPure` reads each table's `tableReads` values as one chunk, `consumeFold`).
**`relsAt_eq`**: they state the same relations, in the same order (a table's part reads exactly its
`tableReads` values, `tablePartOf_eq`; the values after the tables are `vals.drop tablesReads`).

Then the run's combined claims are the identity model's (`runClaims_eq`), and
**`batchIsVerifiers_of`**: an identity model whose batch is `Model.lean`'s `prodOf`, `targetOf` has the
verifier's batch (`batchProd`, `batchTargetOf`) where the counts are in range and Flock's result is the
main line's (`FlockGood`); `batchIsVerifiers_ids` for `idsRestOf`. **`nVOf_eq_of`**: the model's number
of values at `t` is the code's (`valsCount`) once the tables read at most `4096` values.
-/

namespace UniSound.Ids

open LeanVM.Parameters UniStatement Finset

/-! ## Lists -/

namespace Align

theorem headD_drop : ∀ (V : List E) (i : ℕ), (V.drop i).headD 0 = V.getD i 0
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | _ :: _, _ + 1 => by simp

theorem take_one_headD : ∀ (V : List E), (V.take 1).headD 0 = V.headD 0
  | [] => rfl
  | _ :: _ => rfl

theorem getD_take (V : List E) (a j : ℕ) (h : j < a) : (V.take a).getD j 0 = V.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, ↓reduceIte]

theorem getD_drop : ∀ (V : List E) (i j : ℕ), (V.drop i).getD j 0 = V.getD (i + j) 0
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: V, i + 1, j => by
    rw [show i + 1 + j = (i + j) + 1 by omega]
    simp

theorem take_take_add : ∀ (X : List E) (a m : ℕ), (X.take (a + m)).take a = X.take a
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: X, a + 1, m => by
    rw [show a + 1 + m = (a + m) + 1 by omega]
    simp [take_take_add X a m]

theorem drop_take_add : ∀ (X : List E) (a m : ℕ), (X.take (a + m)).drop a = (X.drop a).take m
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: X, a + 1, m => by
    rw [show a + 1 + m = (a + m) + 1 by omega]
    simp [drop_take_add X a m]

theorem drop_drop_add : ∀ (X : List E) (a b : ℕ), (X.drop a).drop b = X.drop (a + b)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: X, a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp [drop_drop_add X a b]

/-! ## A table's part -/

/-- **The sent columns, one value each** (`tablePartPure`'s first loop) from position `i`: the
columns set and their `equal` relations, as `sentOf` and `tablePartOf`'s first relations read them. -/
theorem sent_consume (t : Table) (pt : List E) : ∀ (l : List ℕ) (i : ℕ) (A : Array (Option E))
    (R : Array Relation) (V W : List E), (∀ j, i ≤ j → j < i + l.length → V.getD j 0 = W.getD j 0) →
    (consumeFold (fun _ => 1) (_root_.UniSound.sentStep t pt) l (A, R) (V.drop i)).1 =
        (l.zip (List.range' i l.length)).foldl (fun a p => a.set! p.1 (some (W.getD p.2 0))) A ∧
      (consumeFold (fun _ => 1) (_root_.UniSound.sentStep t pt) l (A, R) (V.drop i)).2.toList =
        R.toList ++ (l.zip (List.range' i l.length)).map fun p =>
          Relation.equal (.table t.opcode p.1) pt (W.getD p.2 0)
  | [], i, A, R, V, W, _ => by simp [consumeFold]
  | c :: l, i, A, R, V, W, h => by
    have hv : ((V.drop i).take 1).headD 0 = W.getD i 0 := by
      rw [take_one_headD, headD_drop, h i le_rfl (by simp only [List.length_cons]; omega)]
    have ih := sent_consume t pt l (i + 1) (A.set! c (some (W.getD i 0)))
      (R.push (Relation.equal (.table t.opcode c) pt (W.getD i 0))) V W
      (fun j h1 h2 => h j (by omega) (by simp only [List.length_cons]; omega))
    simp only [consumeFold, _root_.UniSound.sentStep, hv, drop_drop_add, List.length_cons,
      List.range'_succ, List.zip_cons_cons, List.foldl_cons, List.map_cons]
    refine ⟨ih.1, ?_⟩
    rw [ih.2, Array.toList_push, List.append_assoc]
    rfl

/-- **One flush**: `flushStep` (the identity model's) is `CodeTables.lean`'s `flushStep` on the
fingerprints it sends (`flushReads`), the values left after them. -/
theorem flush_step (t : Table) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) (x : List Form × List Form) (R : Array Relation) (P Q : E) (a b : ℕ)
    (X : List E) :
    Ids.flushStep (fun c ↦ .table t.opcode c) pt weights beta sent ⟨P, Q, a, b, R.toList, X⟩ x =
      ⟨(_root_.UniSound.flushStep t pt weights beta sent x (R, P, Q, a, b)
          (X.take (flushReads weights sent x))).2.1,
        (_root_.UniSound.flushStep t pt weights beta sent x (R, P, Q, a, b)
          (X.take (flushReads weights sent x))).2.2.1,
        (_root_.UniSound.flushStep t pt weights beta sent x (R, P, Q, a, b)
          (X.take (flushReads weights sent x))).2.2.2.1,
        (_root_.UniSound.flushStep t pt weights beta sent x (R, P, Q, a, b)
          (X.take (flushReads weights sent x))).2.2.2.2,
        (_root_.UniSound.flushStep t pt weights beta sent x (R, P, Q, a, b)
          (X.take (flushReads weights sent x))).1.toList,
        X.drop (flushReads weights sent x)⟩ := by
  rcases hA : (linearise x.1 weights sent).2.isEmpty <;>
    rcases hB : (linearise (difference x.2 x.1) weights sent).2.isEmpty <;>
    rcases X with _ | ⟨x0, _ | ⟨x1, X⟩⟩ <;>
    simp [Ids.flushStep, _root_.UniSound.flushStep, flushReads, hA, hB]

/-- **The flushes**: the identity model's fold is `consumeFold` of the code's flushes, the values
left after their sent fingerprints. -/
theorem flush_fold (t : Table) (pt : List E) (weights : Array E) (beta : E)
    (sent : Array (Option E)) :
    ∀ (fls : List (List Form × List Form)) (R : Array Relation) (P Q : E) (a b : ℕ) (X : List E),
      fls.foldl (Ids.flushStep (fun c ↦ .table t.opcode c) pt weights beta sent)
          ⟨P, Q, a, b, R.toList, X⟩ =
        ⟨(consumeFold (flushReads weights sent) (_root_.UniSound.flushStep t pt weights beta sent) fls
            (R, P, Q, a, b) (X.take (fls.map (flushReads weights sent)).sum)).2.1,
          (consumeFold (flushReads weights sent) (_root_.UniSound.flushStep t pt weights beta sent) fls
            (R, P, Q, a, b) (X.take (fls.map (flushReads weights sent)).sum)).2.2.1,
          (consumeFold (flushReads weights sent) (_root_.UniSound.flushStep t pt weights beta sent) fls
            (R, P, Q, a, b) (X.take (fls.map (flushReads weights sent)).sum)).2.2.2.1,
          (consumeFold (flushReads weights sent) (_root_.UniSound.flushStep t pt weights beta sent) fls
            (R, P, Q, a, b) (X.take (fls.map (flushReads weights sent)).sum)).2.2.2.2,
          (consumeFold (flushReads weights sent) (_root_.UniSound.flushStep t pt weights beta sent) fls
            (R, P, Q, a, b) (X.take (fls.map (flushReads weights sent)).sum)).1.toList,
          X.drop (fls.map (flushReads weights sent)).sum⟩
  | [], R, P, Q, a, b, X => by simp [consumeFold]
  | x :: fls, R, P, Q, a, b, X => by
    rw [List.foldl_cons, flush_step, flush_fold t pt weights beta sent fls]
    simp only [consumeFold, List.map_cons, List.sum_cons, take_take_add, drop_take_add, drop_drop_add,
      Prod.mk.eta]

end Align

open Align in
/-- **A table's part reads exactly its `tableReads` values**: `tablePartOf` on a list is
`tablePartPure` on its first `tableReads t` values, the rest left. -/
theorem tablePartOf_eq (t : Table) (lh : ℕ) (weights : Array E) (beta : E) (w X : List E) :
    tablePartOf t lh weights beta w X =
      ((tablePartPure t lh weights beta w (X.take (tableReads t))).1,
        (tablePartPure t lh weights beta w (X.take (tableReads t))).2, X.drop (tableReads t)) := by
  have hk : tableReads t = (sentColumns t).length +
      ((t.flushes.pull.zip t.flushes.push).map (flushReads #[] (sentPat t))).sum := rfl
  obtain ⟨hs1, hs2⟩ := sent_consume t (w.take lh) (sentColumns t) 0 (Array.replicate t.width none) #[]
    ((X.take (tableReads t)).take (sentColumns t).length) X (fun j _ hj => by
      rw [Nat.zero_add] at hj
      rw [getD_take _ _ _ hj, getD_take _ _ _ (by omega)])
  rw [List.drop_zero, ← List.range_eq_range'] at hs1 hs2
  have hsent : (consumeFold (fun _ => 1) (_root_.UniSound.sentStep t (w.take lh)) (sentColumns t)
      (Array.replicate t.width none, #[]) ((X.take (tableReads t)).take (sentColumns t).length)).1 =
      sentOf t X := hs1
  have hpat : SamePat (sentOf t X) (sentPat t) := by
    rw [← hsent]
    exact samePat_consume_sent t (sentColumns t) (w.take lh) [] _ _ _ [] (samePat_refl _)
  have hsum := sum_flushReads t weights (sentOf t X) hpat
  have hfold := flush_fold t (w.take lh) weights beta (sentOf t X) (t.flushes.pull.zip t.flushes.push)
    (consumeFold (fun _ => 1) (_root_.UniSound.sentStep t (w.take lh)) (sentColumns t)
      (Array.replicate t.width none, #[]) ((X.take (tableReads t)).take (sentColumns t).length)).2
    1 1 1 0 (X.drop (sentColumns t).length)
  rw [hs2, Array.toList_empty, List.nil_append] at hfold
  have hdrop : (X.take (tableReads t)).drop (sentColumns t).length =
      (X.drop (sentColumns t).length).take
        ((t.flushes.pull.zip t.flushes.push).map (flushReads weights (sentOf t X))).sum := by
    rw [hsum, hk, drop_take_add]
  unfold tablePartOf tablePartPure
  simp only []
  rw [hfold, hsent, hdrop]
  simp only [drop_drop_add, hsum, ← hk]

open Align in
/-- **The tables' parts**: `tablesPart` on a list is `consumeFold tableReads (tablesStep …)` on its
first values, the rest left. -/
theorem tablesPart_eq (S : Shape) (weights : Array E) (beta : E) (w : List E) :
    ∀ (ts : List Table) (R : Array Relation) (P : Array TablePart) (X : List E),
      (consumeFold tableReads (tablesStep S.heights weights beta w) ts (R, P)
          (X.take (ts.map tableReads).sum)).1.toList = R.toList ++ (tablesPart S weights beta w ts X).2.1 ∧
        (consumeFold tableReads (tablesStep S.heights weights beta w) ts (R, P)
          (X.take (ts.map tableReads).sum)).2.toList = P.toList ++ (tablesPart S weights beta w ts X).1 ∧
        (tablesPart S weights beta w ts X).2.2 = X.drop (ts.map tableReads).sum
  | [], R, P, X => by simp [consumeFold, tablesPart]
  | t :: ts, R, P, X => by
    obtain ⟨i1, i2, i3⟩ := tablesPart_eq S weights beta w ts
      (R ++ (tablePartPure t (S.heights.getD t.opcode 0) weights beta w (X.take (tableReads t))).2.toArray)
      (P.push (tablePartPure t (S.heights.getD t.opcode 0) weights beta w (X.take (tableReads t))).1)
      (X.drop (tableReads t))
    have ht := tablePartOf_eq t (S.heights.getD t.opcode 0) weights beta w X
    simp only [consumeFold, List.map_cons, List.sum_cons, take_take_add, drop_take_add, tablesStep]
    simp only [tablesPart, ht]
    refine ⟨?_, ?_, ?_⟩
    · rw [i1]
      simp
    · rw [i2]
      simp
    · rw [i3, drop_drop_add]

/-! ## The relations at `t` -/

namespace Align

/-- The digits `t` is read through. -/
def wOf (shape : Shape) (t : E) : List E := digits t (max shape.heap.h (shape.constraintVars + 4) + 2)

/-- `tablesPart_eq` from the empty arrays, for any tables (a variable list: `tables` itself is never
reduced). -/
theorem tablesPart_fst (S : Shape) (w8 : Array E) (beta : E) (w : List E) (ts : List Table) (X : List E) :
    (consumeFold tableReads (tablesStep S.heights w8 beta w) ts (#[], #[])
      (X.take (ts.map tableReads).sum)).1.toList = (tablesPart S w8 beta w ts X).2.1 := by
  have k := (tablesPart_eq S w8 beta w ts #[] #[] X).1
  simp only [List.nil_append] at k
  exact k

theorem tablesPart_snd (S : Shape) (w8 : Array E) (beta : E) (w : List E) (ts : List Table) (X : List E) :
    (consumeFold tableReads (tablesStep S.heights w8 beta w) ts (#[], #[])
      (X.take (ts.map tableReads).sum)).2.toList = (tablesPart S w8 beta w ts X).1 := by
  have k := (tablesPart_eq S w8 beta w ts #[] #[] X).2.1
  simp only [List.nil_append] at k
  exact k

theorem alphasOf_eq (ch : List E) (h : 4 ≤ ch.length) : alphasOf ch = ch.take 4 := by
  rcases ch with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · simp at h
  · simp at h
  · simp at h
  · simp at h
  · rfl

theorem filterMap_commitments (f : Commitment → Option Combined)
    (h : (commitments.filterMap fun c => (f c).map fun x => (c, x)).length = 3) :
    (commitments.filterMap fun c => (f c).map fun x => (c, x)) =
      commitments.map fun c => (c, (f c).getD zeroClaim) := by
  simp only [commitments] at h ⊢
  rcases h1 : f .c1 with _ | x1 <;> rcases h2 : f .c2 with _ | x2 <;> rcases h3 : f .setup with _ | x3 <;>
    simp_all [List.filterMap]

end Align

open Align

section Model

variable {κ : ℕ}

theorem ProdSum.ext' {P Q : ProdSum} (h1 : P.vars = Q.vars) (h2 : P.n = Q.n) (h3 : P.coef = Q.coef)
    (h4 : P.A = Q.A) (h5 : P.B = Q.B) : P = Q := by
  obtain ⟨_, _, _, _, _⟩ := P
  obtain ⟨_, _, _, _, _⟩ := Q
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

theorem getD_cmb (f : Commitment → Combined) (k : ℕ) (hk : k < 3) :
    (commitments.map fun c => (c, f c)).getD k default = (cm k, f (cm k)) := by
  interval_cases k <;> rfl

end Model

end UniSound.Ids
