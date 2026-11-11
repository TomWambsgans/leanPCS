-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here.
import ZK.PcsPhi

/-!
# The ideal run's challenges are uniform

**`ideal_challenges`**: the challenges of the ideal run of `phaseF` (tracked answers independent and uniform) have
the distribution of `sampleChallenges`: they are the stream's elements at `Φ` (`stream`, `phaseF_challenges`),
and the stream's other elements are drawn and dropped.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open FProg

theorem iidE_add (a b : ℕ) : iidE (a + b) = (do let l ← iidE a; let l' ← iidE b; pure (l ++ l')) := by
  simp only [iidE, List.range_add, List.mapM_append, List.mapM_map]
  rfl

theorem length_of_mem_iidE (n : ℕ) (l : List E) (hl : l ∈ support (iidE n)) : l.length = n := by
  induction n generalizing l with
  | zero => simp [iidE_zero] at hl; simp [hl]
  | succ n ih =>
    rw [iidE_succ] at hl
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hl
    obtain ⟨e, -, l', hl', rfl⟩ := hl
    simp [ih l' hl']

theorem iidE_one : iidE 1 = (do let e ← eDist; pure [e]) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, iidE_succ, iidE_zero]
  simp

theorem evalDistEq_bind_drop {α β : Type} (X : ProbComp α) (Y : ProbComp β) : (X >>= fun _ ↦ Y) =ᵈ Y :=
  fun p ↦ by rw [map_bind]; exact prEvent_bind_const X (p <$> Y)

theorem coinsOf_coinEs (n : ℕ) : simulateQ coinsOf (coinEs n) = iidE n := by
  simp only [coinEs, simulateQ_list_mapM, iidE, eDist]

theorem cellVars_logRows : cellVars logRows = 24 := rfl

/-- The simulator's challenges as `ProbComp`: `sampleChallenges` with its coins run by `ProbComp`. -/
theorem sampleChallenges_eq : sampleChallenges =
    (do let zW ← iidE 25; let α ← eDist; let β ← eDist; let γ ← eDist; let zH ← iidE 27; let zQ ← iidE 28
        let zG ← iidE 25; let t ← eDist; let ρ ← eDist
        pure (⟨zW, zH, zQ, zG, α, β, γ, t, ρ⟩ : Challenges)) := by
  have h : ∀ G : OracleComp RandomPermutationOracles Challenges,
      StateIndep (simulateQ lazyRandomPermutationOracles G) (simulateQ coinsOf G) →
      runWithRandomPermutation G = simulateQ coinsOf G := fun G hG ↦ runWithRandomPermutation_of_indep hG
  unfold sampleChallenges
  rw [h]
  · simp only [simulateQ_bind, simulateQ_pure, coinsOf_coinEs, cellVars_logRows]
    rfl
  · simp only [simulateQ_bind, simulateQ_pure]
    have hE := indep_coinE _ lazy_coin
    have hEs := indep_coinEs _ lazy_coin
    exact (hEs _).bind' fun _ ↦ hE.bind' fun _ ↦ hE.bind' fun _ ↦ hE.bind' fun _ ↦ (hEs _).bind' fun _ ↦
      (hEs _).bind' fun _ ↦ (hEs _).bind' fun _ ↦ hE.bind' fun _ ↦ hE.bind' fun _ ↦ StateIndep.pure' _

theorem getD_seg (pre l r : List E) (k : ℕ) (hk : k < l.length) :
    (pre ++ (l ++ r)).getD (pre.length + k) 0 = l[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, List.getElem?_append_left, hk]

theorem map_seg (pre l r : List E) :
    (List.range l.length).map (fun j ↦ (pre ++ (l ++ r)).getD (pre.length + j) 0) = l := by
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  simp only [List.getElem_map, List.getElem_range]
  exact getD_seg pre l r i h2

theorem phi_concat (l1 l2 l3 l4 l5 l6 : List E) (h1 : l1.length = 25) (h2 : l2.length = 3) (h3 : l3.length = 27)
    (h4 : l4.length = 28) (h5 : l5.length = 25) (h6 : l6.length = 5) :
    Φ 24 (l1 ++ (l2 ++ (l3 ++ (l4 ++ (l5 ++ l6))))) =
      ⟨l1, l3, l4, l5, l2.getD 0 0, l2.getD 1 0, l2.getD 2 0, l6.getD 2 0, l6.getD 4 0⟩ := by
  have hzW := map_seg [] l1 (l2 ++ (l3 ++ (l4 ++ (l5 ++ l6))))
  have hzH := map_seg (l1 ++ l2) l3 (l4 ++ (l5 ++ l6))
  have hzQ := map_seg (l1 ++ l2 ++ l3) l4 (l5 ++ l6)
  have hzG := map_seg (l1 ++ l2 ++ l3 ++ l4) l5 l6
  have hα := getD_seg l1 l2 (l3 ++ (l4 ++ (l5 ++ l6))) 0 (by omega)
  have hβ := getD_seg l1 l2 (l3 ++ (l4 ++ (l5 ++ l6))) 1 (by omega)
  have hγ := getD_seg l1 l2 (l3 ++ (l4 ++ (l5 ++ l6))) 2 (by omega)
  have ht := getD_seg (l1 ++ l2 ++ l3 ++ l4 ++ l5) l6 [] 2 (by omega)
  have hρ := getD_seg (l1 ++ l2 ++ l3 ++ l4 ++ l5) l6 [] 4 (by omega)
  simp only [List.append_assoc, List.length_append, List.nil_append, List.length_nil, Nat.zero_add,
    List.append_nil, h1, h2, h3, h4, h5] at hzW hzH hzQ hzG hα hβ hγ ht hρ
  simp only [Φ, Challenges.mk.injEq]
  refine ⟨hzW, hzH, hzQ, hzG, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hα, hβ, hγ, ht, hρ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : 0 < l2.length),
      List.getElem?_eq_getElem (by omega : 1 < l2.length), List.getElem?_eq_getElem (by omega : 2 < l2.length),
      List.getElem?_eq_getElem (by omega : 2 < l6.length), List.getElem?_eq_getElem (by omega : 4 < l6.length),
      Option.getD_some]

theorem iidE_three : iidE 3 = (do let a ← eDist; let b ← eDist; let c ← eDist; pure [a, b, c]) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iidE_succ, show (2 : ℕ) = 1 + 1 from rfl, iidE_succ, iidE_one]
  simp

theorem iidE_five : iidE 5 =
    (do let a ← eDist; let b ← eDist; let c ← eDist; let d ← eDist; let x ← eDist; pure [a, b, c, d, x]) := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, iidE_succ, show (4 : ℕ) = 3 + 1 from rfl, iidE_succ, iidE_three]
  simp

/-- **The stream's challenge positions are uniform challenges.** -/
theorem phi_iidE : Φ 24 <$> iidE 113 =ᵈ sampleChallenges := by
  rw [show (113 : ℕ) = 25 + (3 + (27 + (28 + (25 + 5)))) from rfl]
  simp only [iidE_add, map_bind, map_pure, bind_assoc, pure_bind]
  rw [sampleChallenges_eq]
  have hL : ∀ l1 ∈ support (iidE 25), (do
      let a ← iidE 3
      let a_1 ← iidE 27
      let a_2 ← iidE 28
      let a_3 ← iidE 25
      let a_4 ← iidE 5
      pure (Φ 24 (l1 ++ (a ++ (a_1 ++ (a_2 ++ (a_3 ++ a_4))))))) = (do
      let a ← iidE 3
      let a_1 ← iidE 27
      let a_2 ← iidE 28
      let a_3 ← iidE 25
      let a_4 ← iidE 5
      pure (⟨l1, a_1, a_2, a_3, a.getD 0 0, a.getD 1 0, a.getD 2 0, a_4.getD 2 0, a_4.getD 4 0⟩ : Challenges)) := by
    intro l1 h1
    refine bind_congr_of_forall_mem_support _ fun a h2 ↦ bind_congr_of_forall_mem_support _ fun a1 h3 ↦
      bind_congr_of_forall_mem_support _ fun a2 h4 ↦ bind_congr_of_forall_mem_support _ fun a3 h5 ↦
      bind_congr_of_forall_mem_support _ fun a4 h6 ↦ ?_
    rw [phi_concat _ _ _ _ _ _ (length_of_mem_iidE _ _ h1) (length_of_mem_iidE _ _ h2) (length_of_mem_iidE _ _ h3)
      (length_of_mem_iidE _ _ h4) (length_of_mem_iidE _ _ h5) (length_of_mem_iidE _ _ h6)]
  rw [bind_congr_of_forall_mem_support _ hL, iidE_three, iidE_five]
  simp only [bind_assoc, pure_bind, List.getD_cons_zero, List.getD_cons_succ]
  refine EvalDistEq.bind_right _ fun l1 ↦ EvalDistEq.bind_right _ fun x ↦ EvalDistEq.bind_right _ fun y ↦
    EvalDistEq.bind_right _ fun z ↦ EvalDistEq.bind_right _ fun l3 ↦ EvalDistEq.bind_right _ fun l4 ↦
    EvalDistEq.bind_right _ fun l5 ↦ ?_
  refine (evalDistEq_bind_drop _ _).trans ((evalDistEq_bind_drop _ _).trans ?_)
  refine EvalDistEq.bind_right _ fun r ↦ ?_
  exact evalDistEq_bind_drop _ _

theorem membership_logRows : (membership logRows).logRows = logRows := rfl

theorem prEvent_const {γ : Type} (X : ProbComp γ) (P : Prop) [Decidable P] :
    Pr{let _x ← X}[P] = if P then 1 else 0 := by
  split_ifs with h
  · exact (prEvent_eq_one_iff _ _).2 fun _ _ ↦ h
  · exact (prEvent_eq_zero_iff _ _).2 fun _ _ ↦ h

/-- **The ideal run's challenges are uniform.** -/
theorem ideal_challenges {A : Type} (a₀ : A) (stmt : Statement) (B : Challenges → Prop) :
    Pr{let x ← (interpI (phaseF (A := A) (membership logRows) stmt)).run' ([], a₀)}[B x.1] =
      Pr{let c ← sampleChallenges}[B c] := by
  classical
  have hcount := countQ_phaseF (A := A) (membership logRows) stmt
  rw [membership_logRows, cellVars_logRows] at hcount
  have hrun : (interpI (phaseF (A := A) (membership logRows) stmt)).run' ([], a₀) =
      Prod.fst <$> (interpI (phaseF (A := A) (membership logRows) stmt)).run ([], a₀) := rfl
  rw [hrun, prEvent_map, (stream _ _ hcount _).prEvent_eq (fun o ↦ B o.1.1)]
  rw [prEvent_bind_congr _ _ (fun es ↦ (pure (Φ 24 es) : ProbComp Challenges)) _ B fun es ↦ ?_]
  · refine Eq.trans ?_ (phi_iidE.prEvent_eq B)
    rw [prEvent_map, prEvent_bind_eq_tsum]
    simp only [prEvent_pure]
    rw [prEvent_eq_tsum_ite]
    exact tsum_congr fun x ↦ by split_ifs <;> simp
  · rw [prEvent_congr_of_support _ _ (fun _ ↦ B (Φ 24 es)) fun o ho ↦ by
      rw [phaseF_challenges _ _ _ _ _ ho, membership_logRows, cellVars_logRows], prEvent_const, prEvent_pure]

end PcsQuotient.EndToEnd
