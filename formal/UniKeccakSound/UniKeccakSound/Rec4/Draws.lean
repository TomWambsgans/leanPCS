-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
import UniSound.Prob

/-!
# Draws split: a wide draw's challenges as independent groups

A round of π1-rec4 draws several challenges from one call, which serve several purposes (`t` and the ring map's
`f_0 … f_3`; `ρ, λ` and `f_4, f_5`). Its error is the sum of theirs because the challenges are independent:

* **`draws_split`**: `a + b` uniform draws are `a` uniform draws and, independently, `b` more;
* **`prEvent_draws_take`**, **`prEvent_draws_drop`**: the first `a`, and the last `b`, are uniform draws;
* **`prEvent_draws_fubini`**: an event of both groups bounded for every value of the second group, uniformly over the
  first, is bounded.
-/

namespace UniKeccakSound.Rec4

open UniStatement LeanVM.Parameters OracleComp
open scoped ENNReal

/-- **`a + b` uniform draws are `a` uniform draws, then `b` more.** -/
theorem draws_split (a b : ℕ) :
    ((fun l : List E => (l.take a, l.drop a)) <$> Compose.draws E (a + b)) =ᵈ
      (Compose.draws E a >>= fun x => Compose.draws E b >>= fun y => (pure (x, y) : ProbComp _)) := by
  induction a with
  | zero =>
    simp only [Nat.zero_add, List.take_zero, List.drop_zero, Compose.draws, pure_bind]
    rw [map_eq_bind_pure_comp]
    rfl
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    have e1 : ((fun l : List E => (l.take (a + 1), l.drop (a + 1))) <$> Compose.draws E (a + b + 1)) =
        ($ᵗ E : ProbComp E) >>= fun u => (fun p : List E × List E => (u :: p.1, p.2)) <$>
          ((fun l : List E => (l.take a, l.drop a)) <$> Compose.draws E (a + b)) := by
      simp only [Compose.draws, map_bind, map_pure, Functor.map_map, List.take_succ_cons, List.drop_succ_cons]
      refine bind_congr fun u => ?_
      rw [map_eq_bind_pure_comp]
      rfl
    have e2 : (Compose.draws E (a + 1) >>= fun x => Compose.draws E b >>= fun y =>
        (pure (x, y) : ProbComp _)) = ($ᵗ E : ProbComp E) >>= fun u =>
          (fun p : List E × List E => (u :: p.1, p.2)) <$>
            (Compose.draws E a >>= fun x => Compose.draws E b >>= fun y => (pure (x, y) : ProbComp _)) := by
      simp only [Compose.draws, bind_assoc, pure_bind, map_bind, map_pure]
    rw [e1, e2]
    exact EvalDistEq.bind_right _ fun u => ih.map _

/-- An event of the first `a` of `a + b` uniform draws. -/
theorem prEvent_draws_take (a b : ℕ) (P : List E → Prop) :
    Pr{let l ← Compose.draws E (a + b)}[P (l.take a)] = Pr{let x ← Compose.draws E a}[P x] := by
  have h := (draws_split a b).prEvent_eq (fun p => P p.1)
  rw [prEvent_map] at h
  rw [h]
  have h2 : (Prod.fst <$> (Compose.draws E a >>= fun x => Compose.draws E b >>= fun y =>
      (pure (x, y) : ProbComp _))) =ᵈ Compose.draws E a := by
    simp only [map_bind, map_pure]
    refine (EvalDistEq.bind_right _ fun x => OracleComp.EvalDistEq.bind_const _ _).trans ?_
    rw [bind_pure]
  exact (prEvent_map _ Prod.fst P).symm.trans (h2.prEvent_eq P)

/-- An event of the last `b` of `a + b` uniform draws. -/
theorem prEvent_draws_drop (a b : ℕ) (P : List E → Prop) :
    Pr{let l ← Compose.draws E (a + b)}[P (l.drop a)] = Pr{let y ← Compose.draws E b}[P y] := by
  have h := (draws_split a b).prEvent_eq (fun p => P p.2)
  rw [prEvent_map] at h
  rw [h]
  have h2 : (Prod.snd <$> (Compose.draws E a >>= fun x => Compose.draws E b >>= fun y =>
      (pure (x, y) : ProbComp _))) =ᵈ Compose.draws E b := by
    simp only [map_bind, map_pure, bind_pure]
    exact OracleComp.EvalDistEq.bind_const _ _
  exact (prEvent_map _ Prod.snd P).symm.trans (h2.prEvent_eq P)

/-- **An event of both groups**, bounded for every value of the last `b` draws over the first `a`, is bounded. -/
theorem prEvent_draws_fubini (a b : ℕ) (P : List E → List E → Prop) (ε : ℝ≥0∞)
    (h : ∀ y, Pr{let x ← Compose.draws E a}[P x y] ≤ ε) :
    Pr{let l ← Compose.draws E (a + b)}[P (l.take a) (l.drop a)] ≤ ε := by
  have hs := (draws_split a b).prEvent_eq (fun p => P p.1 p.2)
  rw [prEvent_map] at hs
  rw [hs]
  let : MeasurableSpace (List E × List E) := ⊤
  have hswap := OracleComp.evalDist_bind_bind_swap (Compose.draws E a) (Compose.draws E b)
    (fun x y => (pure (x, y) : ProbComp (List E × List E)))
  have e : Pr{let p ← (Compose.draws E a >>= fun x => Compose.draws E b >>= fun y =>
      (pure (x, y) : ProbComp _))}[P p.1 p.2] =
      Pr{let p ← (Compose.draws E b >>= fun y => Compose.draws E a >>= fun x =>
        (pure (x, y) : ProbComp _))}[P p.1 p.2] :=
    (EvalDistEq.of_evalDist_eq hswap).prEvent_eq _
  rw [e]
  refine prEvent_bind_le_of_forall_le _ _ _ fun y => ?_
  rw [bind_pure_comp, prEvent_map]
  exact h y

end UniKeccakSound.Rec4
