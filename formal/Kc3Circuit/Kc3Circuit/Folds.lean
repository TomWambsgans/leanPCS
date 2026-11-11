-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Nodup

/-!
# Folds of `Array.set!`

The Statement's `Circuit.outputs` and `Circuit.outputsK` set the rows of a list one after the other, each to a
value computed from the array so far (`foldl_set`): when no row reads a row set after it, and a row that reads
itself reads only itself (`g r v = v[r]`), every row of the list ends holding its value computed from the final
array, a row reading itself its first value. `foldl_setPairs`: setting distinct positions to given values.
-/

namespace Kc3Fold

variable {α : Type*}

theorem getD_set_ne (v : Array α) (r r' : ℕ) (a d : α) (h : r ≠ r') : (v.set! r a).getD r' d = v.getD r' d := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h]

theorem getD_set_eq (v : Array α) (r : ℕ) (a d : α) (h : r < v.size) : (v.set! r a).getD r d = a := by
  simp [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_self_of_lt h]

theorem size_foldl_set (g : ℕ → Array α → α) :
    ∀ (L : List ℕ) (v : Array α), (L.foldl (fun v r => v.set! r (g r v)) v).size = v.size
  | [], _ => rfl
  | r :: L, v => by rw [List.foldl_cons, size_foldl_set g L]; simp [Array.set!]

theorem foldl_set_out (g : ℕ → Array α → α) (d : α) :
    ∀ (L : List ℕ) (v : Array α) (r : ℕ), r ∉ L → (L.foldl (fun v r => v.set! r (g r v)) v).getD r d = v.getD r d
  | [], _, _, _ => rfl
  | r0 :: L, v, r, h => by
    rw [List.foldl_cons, foldl_set_out g d L _ r (fun hm => h (List.mem_cons_of_mem _ hm)),
      getD_set_ne _ _ _ _ _ (fun e => h (by rw [e]; exact List.mem_cons_self ..))]

/-- **A fold of sets**, its rows read only rows set before them, or (only) themselves. -/
theorem foldl_set (g : ℕ → Array α → α) (d : α) (dep : ℕ → ℕ → Prop)
    (hloc : ∀ r v v', (∀ r', dep r r' → v.getD r' d = v'.getD r' d) → g r v = g r v') :
    ∀ (L : List ℕ) (v : Array α), L.Pairwise (fun a b => a ≠ b ∧ ¬ dep a b) → (∀ r ∈ L, r < v.size) →
      (∀ r ∈ L, dep r r → ∀ v, g r v = v.getD r d) →
      ∀ r ∈ L, (L.foldl (fun v r => v.set! r (g r v)) v).getD r d = g r (L.foldl (fun v r => v.set! r (g r v)) v) ∧
        (dep r r → (L.foldl (fun v r => v.set! r (g r v)) v).getD r d = v.getD r d)
  | [], _, _, _, _, r, hr => absurd hr (List.not_mem_nil)
  | r0 :: L, v, hp, hs, hself, r, hr => by
    rw [List.pairwise_cons] at hp
    have hs1 : ∀ r ∈ L, r < (v.set! r0 (g r0 v)).size := fun r h => by
      simpa [Array.set!] using hs r (List.mem_cons_of_mem _ h)
    have hself1 : ∀ r ∈ L, dep r r → ∀ v, g r v = v.getD r d := fun r h => hself r (List.mem_cons_of_mem _ h)
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hr with rfl | hrL
    · have hn : r ∉ L := fun h => (hp.1 r h).1 rfl
      have hv1 : (L.foldl (fun v r => v.set! r (g r v)) (v.set! r (g r v))).getD r d = g r v := by
        rw [foldl_set_out g d L _ r hn, getD_set_eq _ _ _ _ (hs r (List.mem_cons_self ..))]
      by_cases hd : dep r r
      · have e := hself r (List.mem_cons_self ..) hd
        refine ⟨(e _).symm, fun _ => ?_⟩
        rw [hv1, e v]
      · refine ⟨?_, fun h => absurd h hd⟩
        rw [hv1]
        refine hloc r _ _ fun r' hr' => ?_
        have hne : r ≠ r' := fun e => hd (e ▸ hr')
        have hnL : r' ∉ L := fun h => (hp.1 r' h).2 hr'
        rw [foldl_set_out g d L _ r' hnL, getD_set_ne _ _ _ _ _ hne]
    · have ih := foldl_set g d dep hloc L _ hp.2 hs1 hself1 r hrL
      refine ⟨ih.1, fun h => ?_⟩
      rw [ih.2 h, getD_set_ne _ _ _ _ _ (fun e => (hp.1 r hrL).1 e)]

theorem size_foldl_setPairs : ∀ (l : List (ℕ × α)) (v : Array α),
    (l.foldl (fun v p => v.set! p.1 p.2) v).size = v.size
  | [], _ => rfl
  | p :: l, v => by rw [List.foldl_cons, size_foldl_setPairs l]; simp [Array.set!]

theorem foldl_setPairs_out (d : α) : ∀ (l : List (ℕ × α)) (v : Array α) (r : ℕ), r ∉ l.map Prod.fst →
    (l.foldl (fun v p => v.set! p.1 p.2) v).getD r d = v.getD r d
  | [], _, _, _ => rfl
  | p :: l, v, r, h => by
    rw [List.foldl_cons, foldl_setPairs_out d l _ r (fun hm => h (List.mem_cons_of_mem _ hm)),
      getD_set_ne _ _ _ _ _ (fun e => h (by rw [List.map_cons, e]; exact List.mem_cons_self ..))]

/-- **Setting distinct positions**: each ends holding its value. -/
theorem foldl_setPairs (d : α) : ∀ (l : List (ℕ × α)) (v : Array α), (l.map Prod.fst).Nodup →
    ∀ p ∈ l, p.1 < v.size → (l.foldl (fun v p => v.set! p.1 p.2) v).getD p.1 d = p.2
  | [], _, _, _, hp, _ => absurd hp (List.not_mem_nil)
  | q :: l, v, hn, p, hp, hs => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hpl
    · rw [foldl_setPairs_out d l _ _ hn.1, getD_set_eq _ _ _ _ hs]
    · exact foldl_setPairs d l _ hn.2 p hpl (by simpa [Array.set!] using hs)

end Kc3Fold
