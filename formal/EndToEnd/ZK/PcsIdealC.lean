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
    (do let zW ← iidE 24; let α ← eDist; let β ← eDist; let μ ← eDist; let zT ← iidE 28
        let t ← eDist; let ρ ← eDist
        pure (⟨zW, zT, α, β, μ, t, ρ⟩ : Challenges)) := by
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
      hE.bind' fun _ ↦ hE.bind' fun _ ↦ StateIndep.pure' _

theorem getD_seg (pre l r : List E) (k : ℕ) (hk : k < l.length) :
    (pre ++ (l ++ r)).getD (pre.length + k) 0 = l[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, List.getElem?_append_left, hk]

theorem map_seg (pre l r : List E) :
    (List.range l.length).map (fun j ↦ (pre ++ (l ++ r)).getD (pre.length + j) 0) = l := by
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  simp only [List.getElem_map, List.getElem_range]
  exact getD_seg pre l r i h2

theorem split_concat (l1 l2 l3 l4 l5 l6 l7 l8 : List E) (h1 : l1.length = 24) (h2 : l2.length = 1)
    (h3 : l3.length = 3) (h4 : l4.length = 28) (h5 : l5.length = 1) (h6 : l6.length = 1) (h7 : l7.length = 3)
    (h8 : l8.length = 2) :
    (Φ 24 (l1 ++ (l2 ++ (l3 ++ (l4 ++ (l5 ++ (l6 ++ (l7 ++ l8))))))),
      Aof 24 (l1 ++ (l2 ++ (l3 ++ (l4 ++ (l5 ++ (l6 ++ (l7 ++ l8)))))))) =
      ((⟨l1, l4, l3.getD 0 0, l3.getD 1 0, l3.getD 2 0, l6.getD 0 0, l8.getD 1 0⟩ : Challenges),
        [l2.getD 0 0, l5.getD 0 0, l7.getD 0 0, l7.getD 1 0, l7.getD 2 0]) := by
  have hzW := map_seg [] l1 (l2 ++ (l3 ++ (l4 ++ (l5 ++ (l6 ++ (l7 ++ l8))))))
  have hzT := map_seg (l1 ++ l2 ++ l3) l4 (l5 ++ (l6 ++ (l7 ++ l8)))
  have hoW := getD_seg l1 l2 (l3 ++ (l4 ++ (l5 ++ (l6 ++ (l7 ++ l8))))) 0 (by omega)
  have hα := getD_seg (l1 ++ l2) l3 (l4 ++ (l5 ++ (l6 ++ (l7 ++ l8)))) 0 (by omega)
  have hβ := getD_seg (l1 ++ l2) l3 (l4 ++ (l5 ++ (l6 ++ (l7 ++ l8)))) 1 (by omega)
  have hμ := getD_seg (l1 ++ l2) l3 (l4 ++ (l5 ++ (l6 ++ (l7 ++ l8)))) 2 (by omega)
  have hoT := getD_seg (l1 ++ l2 ++ l3 ++ l4) l5 (l6 ++ (l7 ++ l8)) 0 (by omega)
  have ht := getD_seg (l1 ++ l2 ++ l3 ++ l4 ++ l5) l6 (l7 ++ l8) 0 (by omega)
  have hv1 := getD_seg (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6) l7 l8 0 (by omega)
  have hv2 := getD_seg (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6) l7 l8 1 (by omega)
  have hv0 := getD_seg (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6) l7 l8 2 (by omega)
  have hρ := getD_seg (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7) l8 [] 1 (by omega)
  simp only [List.append_assoc, List.length_append, List.nil_append, List.length_nil, Nat.zero_add,
    List.append_nil, h1, h2, h3, h4, h5, h6, h7] at hzW hzT hoW hα hβ hμ hoT ht hv1 hv2 hv0 hρ
  simp only [Φ, Aof, Prod.mk.injEq, Challenges.mk.injEq, List.cons.injEq, and_true]
  have g : ∀ (l : List E) (k : ℕ) (hk : k < l.length), l.getD k 0 = l[k] := fun l k hk ↦ by
    simp [List.getD_eq_getElem?_getD, hk]
  refine ⟨⟨hzW, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hzT
  · rw [g l3 0 (by omega)]; simpa using hα
  · rw [g l3 1 (by omega)]; simpa using hβ
  · rw [g l3 2 (by omega)]; simpa using hμ
  · rw [g l6 0 (by omega)]; simpa using ht
  · rw [g l8 1 (by omega)]; simpa using hρ
  · rw [g l2 0 (by omega)]; simpa using hoW
  · rw [g l5 0 (by omega)]; simpa using hoT
  · rw [g l7 0 (by omega)]; simpa using hv1
  · rw [g l7 1 (by omega)]; simpa using hv2
  · rw [g l7 2 (by omega)]; simpa using hv0

theorem iidE_two : iidE 2 = (do let a ← eDist; let b ← eDist; pure [a, b]) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iidE_succ, iidE_one]
  simp

theorem iidE_three : iidE 3 = (do let a ← eDist; let b ← eDist; let c ← eDist; pure [a, b, c]) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iidE_succ, iidE_two]
  simp

theorem iidE_five : iidE 5 =
    (do let a ← eDist; let b ← eDist; let c ← eDist; let d ← eDist; let x ← eDist; pure [a, b, c, d, x]) := by
  rw [show (5 : ℕ) = 2 + 3 from rfl, iidE_add, iidE_two, iidE_three]
  simp

/-- **The stream's challenge and scalar positions are independent uniform challenges and scalars.** -/
theorem joint_iidE : (fun es ↦ (Φ 24 es, Aof 24 es)) <$> iidE 63 =ᵈ
    (do let c ← sampleChallenges; let a ← iidE 5; pure (c, a)) := by
  rw [show (63 : ℕ) = 24 + (1 + (3 + (28 + (1 + (1 + (3 + 2)))))) from rfl]
  simp only [iidE_add, map_bind, map_pure, bind_assoc, pure_bind]
  have hL : ∀ l1 ∈ support (iidE 24), (do
      let l2 ← iidE 1
      let l3 ← iidE 3
      let l4 ← iidE 28
      let l5 ← iidE 1
      let l6 ← iidE 1
      let l7 ← iidE 3
      let l8 ← iidE 2
      pure (Φ 24 (l1 ++ (l2 ++ (l3 ++ (l4 ++ (l5 ++ (l6 ++ (l7 ++ l8))))))),
        Aof 24 (l1 ++ (l2 ++ (l3 ++ (l4 ++ (l5 ++ (l6 ++ (l7 ++ l8)))))))) : ProbComp _) = (do
      let l2 ← iidE 1
      let l3 ← iidE 3
      let l4 ← iidE 28
      let l5 ← iidE 1
      let l6 ← iidE 1
      let l7 ← iidE 3
      let l8 ← iidE 2
      pure ((⟨l1, l4, l3.getD 0 0, l3.getD 1 0, l3.getD 2 0, l6.getD 0 0, l8.getD 1 0⟩ : Challenges),
        [l2.getD 0 0, l5.getD 0 0, l7.getD 0 0, l7.getD 1 0, l7.getD 2 0])) := by
    intro l1 h1
    refine bind_congr_of_forall_mem_support _ fun l2 h2 ↦ bind_congr_of_forall_mem_support _ fun l3 h3 ↦
      bind_congr_of_forall_mem_support _ fun l4 h4 ↦ bind_congr_of_forall_mem_support _ fun l5 h5 ↦
      bind_congr_of_forall_mem_support _ fun l6 h6 ↦ bind_congr_of_forall_mem_support _ fun l7 h7 ↦
      bind_congr_of_forall_mem_support _ fun l8 h8 ↦ ?_
    rw [split_concat _ _ _ _ _ _ _ _ (length_of_mem_iidE _ _ h1) (length_of_mem_iidE _ _ h2)
      (length_of_mem_iidE _ _ h3) (length_of_mem_iidE _ _ h4) (length_of_mem_iidE _ _ h5)
      (length_of_mem_iidE _ _ h6) (length_of_mem_iidE _ _ h7) (length_of_mem_iidE _ _ h8)]
  rw [bind_congr_of_forall_mem_support _ hL, iidE_one, iidE_two, iidE_three, sampleChallenges_eq, iidE_five]
  simp only [bind_assoc, pure_bind, List.getD_cons_zero, List.getD_cons_succ]
  refine EvalDistEq.bind_right _ fun l1 ↦ ?_
  -- `W`'s answer past `α, β, μ` and `T`'s point.
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine (EvalDistEq.bind_right _ fun _ ↦ OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine (EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine (EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  -- `t` before both answers.
  refine (EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine (EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  -- `ρ`'s first block dropped.
  refine (EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ evalDistEq_bind_drop _ _).trans ?_
  -- `ρ` before the answers.
  refine (EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine (EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine (EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine (EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine (EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    EvalDistEq.bind_right _ fun _ ↦ EvalDistEq.bind_right _ fun _ ↦
    OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  exact EvalDistEq.refl _

theorem membership_logRows : (membership logRows).logRows = logRows := rfl

/-- An expectation over a run whose observation is constant on its support. -/
theorem tsum_const_on_support {γ : Type} (X : ProbComp γ) (g : γ → ℝ≥0∞) (v : ℝ≥0∞)
    (h : ∀ o ∈ support X, g o = v) : ∑' o, Pr{let y ← X}[y = o] * g o = v := by
  calc ∑' o, Pr{let y ← X}[y = o] * g o = ∑' o, Pr{let y ← X}[y = o] * v := by
        refine tsum_congr fun o ↦ ?_
        by_cases ho : o ∈ support X
        · rw [h o ho]
        · rw [prEvent_eq_zero_of_not_mem_support _ ho, zero_mul, zero_mul]
    _ = v := by rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

/-- Expectations agree in distribution. -/
theorem tsum_evalDistEq {γ : Type} {X Y : ProbComp γ} (h : X =ᵈ Y) (g : γ → ℝ≥0∞) :
    ∑' o, Pr{let y ← X}[y = o] * g o = ∑' o, Pr{let y ← Y}[y = o] * g o :=
  tsum_congr fun o ↦ by rw [h.prEvent_eq (· = o)]

/-- **The ideal run's challenges and revealed scalars are independent and uniform**, on every observation. -/
theorem ideal_joint {A : Type} (a₀ : A) (stmt : Statement) (h : Challenges → List E → ℝ≥0∞) :
    ∑' o, Pr{let y ← (interpI (phaseF (A := A) (membership logRows) stmt)).run ([], a₀)}[y = o] *
        h o.1.1 (answersOf o.1.2) =
      ∑' c, ∑' a, Pr{let y ← sampleChallenges}[y = c] * Pr{let y ← runWithRandomPermutation (coinEs 5)}[y = a] *
        h c a := by
  classical
  have hcount := countQ_phaseF (A := A) (membership logRows) stmt
  rw [membership_logRows, cellVars_logRows] at hcount
  rw [tsum_evalDistEq (stream _ _ hcount _) (fun o ↦ h o.1.1 (answersOf o.1.2)), tsum_prEvent_bind_mul]
  have hes : ∀ es, ∑' o, Pr{let y ← (interpS (phaseF (A := A) (membership logRows) stmt) es).run ([], a₀)}[y = o] *
      h o.1.1 (answersOf o.1.2) = h (Φ 24 es) (Aof 24 es) := fun es ↦
    tsum_const_on_support _ _ _ fun o ho ↦ by
      obtain ⟨e1, e2⟩ := phaseF_outputs _ _ _ _ o ho
      rw [e1, e2, membership_logRows, cellVars_logRows]
  simp only [hes]
  rw [show (∑' es, Pr{let y ← iidE 63}[y = es] * h (Φ 24 es) (Aof 24 es)) =
      ∑' z, Pr{let y ← (fun es ↦ (Φ 24 es, Aof 24 es)) <$> iidE 63}[y = z] * h z.1 z.2 from
    (tsum_map (iidE 63) (fun es ↦ (Φ 24 es, Aof 24 es)) fun z : Challenges × List E ↦ h z.1 z.2).symm,
    tsum_evalDistEq joint_iidE (fun z : Challenges × List E ↦ h z.1 z.2), tsum_prEvent_bind_mul]
  refine tsum_congr fun c ↦ ?_
  rw [tsum_prEvent_bind_mul, ← ENNReal.tsum_mul_left, runWithRandomPermutation_coinEs]
  refine tsum_congr fun a ↦ ?_
  rw [tsum_const_on_support (pure (c, a) : ProbComp _) (fun z : Challenges × List E ↦ h z.1 z.2) (h c a) fun o ho ↦ by
    simp only [support_pure, Set.mem_singleton_iff] at ho; rw [ho]]
  simp only [iidE]
  ring

end PcsQuotient.EndToEnd
