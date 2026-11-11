-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. The probability laws are VCVio's (pinned by leanerVM `mumbai` 6175f1a0, Apache-2.0).
import PcsQuotient.Zk
import VCVio.OracleComp.EvalDist.Sum

/-!
# Revealed values that depend adaptively on the challenges

The adaptivity argument of the zero-knowledge theorem, for any program. A program (`RProg`) runs black-box
stateful steps (`step`: any computation of `StateT σ ProbComp`) and asks **reveal queries** (`rev q`): the
honest prover answers them by a function `g c` of its randomness `c` (drawn first from `μ`), the simulator by
fresh samples of `ν`. The queries may depend on earlier answers and on everything the steps did (the challenges
are the oracle's answers on inputs holding earlier answers).

* `semL ν P s L`: the run with answers drawn from `ν`, the reveal queries and their answers logged after `L`.
* **`factor`**: for every outcome, the run answering by `g` weighted by the answers' `ν`-masses equals the run
  answering by `ν` times the indicator that `g` gives the logged answers (the steps are common to both and
  black boxes; the answers' log determines the path).
* **`mix_eq`**: with `g = g c`, `c ← μ`, the mixture's mass of an outcome is the `ν`-run's, wherever the log is
  `Good`: the logged queries' answers under `g c` (`c ← μ`) have the `ν`-masses jointly (`Good`).
* **`trace_le`**: on every event the two runs differ by at most the `ν`-run's probability that its log is not
  `Good`.

For the theorem: the hybrid prover's revealed scalars are `revealAnswer` of its coins, the simulator's uniform; a
log is good when its queries are those of challenges at which the revealed scalars are uniform
(`RevealedUniform`).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace PcsQuotient.EndToEnd

/-- **A program with black-box steps and reveal queries**: return a value; run a step of `StateT σ ProbComp`
and continue with its value; ask a reveal query and continue with its answer. -/
inductive RProg (σ Q R α : Type) : Type 1 where
  | ret (a : α)
  | step {β : Type} (m : StateT σ ProbComp β) (k : β → RProg σ Q R α)
  | rev (q : Q) (k : R → RProg σ Q R α)

namespace RProg

open Classical

variable {σ Q R α β : Type}

/-- The program run, its reveal queries answered by `ans`. -/
def interp (ans : Q → StateT σ ProbComp R) : RProg σ Q R α → StateT σ ProbComp α
  | ret a => pure a
  | step m k => m >>= fun b ↦ interp ans (k b)
  | rev q k => ans q >>= fun r ↦ interp ans (k r)

/-- Sequencing programs. -/
def bind : RProg σ Q R α → (α → RProg σ Q R β) → RProg σ Q R β
  | ret a, f => f a
  | step m k, f => step m fun b ↦ bind (k b) f
  | rev q k, f => rev q fun r ↦ bind (k r) f

/-- **The logged run**: the reveal queries answered by draws of `ν`, each query and its answer appended to the
log. The outcome: the value, the state, the log. -/
def semL (ν : Q → ProbComp R) : RProg σ Q R α → σ → List (Q × R) → ProbComp (α × σ × List (Q × R))
  | ret a, s, L => pure (a, s, L)
  | step m k, s, L => m.run s >>= fun p ↦ semL ν (k p.1) p.2 L
  | rev q k, s, L => ν q >>= fun r ↦ semL ν (k r) s (L ++ [(q, r)])

/-- Answers drawn from `ν`, the state unchanged. -/
def liftAns (ν : Q → ProbComp R) (q : Q) : StateT σ ProbComp R := fun s ↦ (fun r ↦ (r, s)) <$> ν q

theorem interp_bind (ans : Q → StateT σ ProbComp R) (P : RProg σ Q R α) (f : α → RProg σ Q R β) :
    interp ans (P.bind f) = interp ans P >>= fun a ↦ interp ans (f a) := by
  induction P with
  | ret a => simp [bind, interp]
  | step m k ih => simp [bind, interp, ih]
  | rev q k ih => simp [bind, interp, ih]

theorem semL_bind (ν : Q → ProbComp R) (P : RProg σ Q R α) (f : α → RProg σ Q R β) (s : σ)
    (L : List (Q × R)) :
    semL ν (P.bind f) s L = semL ν P s L >>= fun o ↦ semL ν (f o.1) o.2.1 o.2.2 := by
  induction P generalizing s L with
  | ret a => simp [bind, semL]
  | step m k ih => simp [bind, semL, ih]
  | rev q k ih => simp [bind, semL, ih]

/-- **The logged run forgets to the run**: with answers drawn from `ν`, the run is the logged run without its
log. -/
theorem interp_liftAns_run (ν : Q → ProbComp R) (P : RProg σ Q R α) (s : σ) (L : List (Q × R)) :
    (interp (liftAns ν) P).run s = (fun o ↦ (o.1, o.2.1)) <$> semL ν P s L := by
  induction P generalizing s L with
  | ret a => simp [interp, semL]
  | step m k ih =>
    simp only [interp, semL, StateT.run_bind, map_bind]
    exact congrArg _ (funext fun p ↦ ih p.1 p.2 L)
  | rev q k ih =>
    have hq : (liftAns (σ := σ) ν q).run s = (fun r ↦ (r, s)) <$> ν q := rfl
    simp only [interp, semL, StateT.run_bind, hq, map_bind, bind_map_left]
    exact congrArg _ (funext fun r ↦ ih r s (L ++ [(q, r)]))

/-- The log only grows. -/
theorem prefix_of_mem_support (ν : Q → ProbComp R) (P : RProg σ Q R α) (s : σ) (L : List (Q × R))
    (o : α × σ × List (Q × R)) (ho : o ∈ support (semL ν P s L)) : L <+: o.2.2 := by
  induction P generalizing s L with
  | ret a =>
    simp only [semL, support_pure, Set.mem_singleton_iff] at ho
    subst ho
    exact List.prefix_refl L
  | step m k ih =>
    simp only [semL, mem_support_bind_iff] at ho
    obtain ⟨p, -, hp⟩ := ho
    exact ih p.1 p.2 L hp
  | rev q k ih =>
    simp only [semL, mem_support_bind_iff] at ho
    obtain ⟨r, -, hr⟩ := ho
    exact (List.prefix_append L [(q, r)]).trans (ih r s (L ++ [(q, r)]) hr)

/-- **Steps without reveals keep the log.** -/
theorem prEvent_semL_bind_step {γ : Type} (ν : Q → ProbComp R) (P : RProg σ Q R α)
    (m : α → StateT σ ProbComp γ) (s : σ) (L : List (Q × R)) (p : List (Q × R) → Prop) :
    Pr{let y ← semL ν (P.bind fun a ↦ .step (m a) .ret) s L}[p y.2.2] =
      Pr{let o ← semL ν P s L}[p o.2.2] := by
  classical
  rw [semL_bind]
  conv_rhs => rw [← bind_pure (semL ν P s L)]
  refine prEvent_bind_congr _ _ _ _ _ fun o ↦ ?_
  simp only [semL]
  rw [prEvent_pure]
  split_ifs with h
  · exact (prEvent_eq_one_iff _ _).2 fun y hy ↦ by
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
      obtain ⟨q, -, rfl⟩ := hy
      exact h
  · exact (prEvent_eq_zero_iff _ _).2 fun y hy ↦ by
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
      obtain ⟨q, -, rfl⟩ := hy
      exact h

/-! ### The factorization -/

/-- The `ν`-masses of the answers logged after the first `n` entries. -/
noncomputable def weight (ν : Q → ProbComp R) (L' : List (Q × R)) (n : ℕ) : ℝ≥0∞ :=
  ((L'.drop n).map fun x ↦ Pr{let y ← ν x.1}[y = x.2]).prod

/-- Whether `g` gives the answers logged after the first `n` entries. -/
noncomputable def agrees (g : Q → R) (L' : List (Q × R)) (n : ℕ) : ℝ≥0∞ :=
  if ∀ x ∈ L'.drop n, g x.1 = x.2 then 1 else 0

theorem drop_eq_cons_of_prefix {L L' : List (Q × R)} {x : Q × R} (h : L ++ [x] <+: L') :
    L'.drop L.length = x :: L'.drop (L.length + 1) := by
  obtain ⟨t, rfl⟩ := h
  simp

theorem weight_cons {ν : Q → ProbComp R} {L L' : List (Q × R)} {x : Q × R} (h : L ++ [x] <+: L') :
    weight ν L' L.length = Pr{let y ← ν x.1}[y = x.2] * weight ν L' (L.length + 1) := by
  simp [weight, drop_eq_cons_of_prefix h]

theorem agrees_cons {g : Q → R} {L L' : List (Q × R)} {x : Q × R} (h : L ++ [x] <+: L') :
    agrees g L' L.length = (if g x.1 = x.2 then 1 else 0) * agrees g L' (L.length + 1) := by
  classical
  simp only [agrees, drop_eq_cons_of_prefix h, List.mem_cons, forall_eq_or_imp]
  by_cases h1 : g x.1 = x.2 <;> by_cases h2 : ∀ y ∈ L'.drop (L.length + 1), g y.1 = y.2 <;> simp [h1]

theorem prEvent_pure_eq {γ : Type} (a o : γ) :
    Pr{let y ← (pure a : ProbComp γ)}[y = o] = if a = o then 1 else 0 := by
  classical
  rw [prEvent_pure]

/-- **The factorization**: answering by `g`, weighted by the logged answers' `ν`-masses, is answering by `ν`,
times whether `g` gives the logged answers. -/
theorem factor (ν : Q → ProbComp R) (g : Q → R) (P : RProg σ Q R α) (s : σ) (L : List (Q × R))
    (o : α × σ × List (Q × R)) :
    Pr{let y ← semL (fun q ↦ pure (g q)) P s L}[y = o] * weight ν o.2.2 L.length =
      Pr{let y ← semL ν P s L}[y = o] * agrees g o.2.2 L.length := by
  classical
  induction P generalizing s L with
  | ret a =>
    simp only [semL, prEvent_pure_eq]
    by_cases h : (a, s, L) = o
    · subst h
      simp [weight, agrees]
    · simp [h]
  | step m k ih =>
    simp only [semL, prEvent_bind_eq_tsum]
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun p ↦ ?_
    rw [mul_assoc, mul_assoc, ih p.1 p.2 L]
  | rev q k ih =>
    simp only [semL, pure_bind, prEvent_bind_eq_tsum]
    set L₁ := L ++ [(q, g q)]
    have hL₁ : L₁.length = L.length + 1 := by simp [L₁]
    -- The left side.
    have hleft : Pr{let y ← semL (fun q ↦ pure (g q)) (k (g q)) s L₁}[y = o] * weight ν o.2.2 L.length =
        Pr{let y ← ν q}[y = g q] *
          (Pr{let y ← semL (fun q ↦ pure (g q)) (k (g q)) s L₁}[y = o] * weight ν o.2.2 (L.length + 1)) := by
      by_cases hz : Pr{let y ← semL (fun q ↦ pure (g q)) (k (g q)) s L₁}[y = o] = 0
      · simp [hz]
      · have hmem := (mem_support_iff_prEvent_ne_zero _ _).2 hz
        have hpre := prefix_of_mem_support _ _ _ _ _ hmem
        rw [weight_cons hpre]
        ring
    rw [hleft, ← hL₁, ih (g q) s L₁, hL₁]
    -- The right side, term by term: only `r = g q` survives.
    rw [← ENNReal.tsum_mul_right]
    have hterm : ∀ r, Pr{let y ← ν q}[y = r] * Pr{let y ← semL ν (k r) s (L ++ [(q, r)])}[y = o] *
        agrees g o.2.2 L.length =
        if r = g q then Pr{let y ← ν q}[y = g q] *
          (Pr{let y ← semL ν (k (g q)) s L₁}[y = o] * agrees g o.2.2 (L.length + 1)) else 0 := by
      intro r
      by_cases hz : Pr{let y ← semL ν (k r) s (L ++ [(q, r)])}[y = o] = 0
      · split_ifs with hr
        · subst hr
          simp [L₁, hz]
        · simp [hz]
      · have hmem := (mem_support_iff_prEvent_ne_zero _ _).2 hz
        have hpre := prefix_of_mem_support _ _ _ _ _ hmem
        rw [agrees_cons hpre]
        by_cases hr : r = g q
        · subst hr
          simp [L₁, mul_assoc]
        · have hr' : ¬ g q = r := fun h ↦ hr h.symm
          simp [hr, hr']
    rw [tsum_congr hterm, tsum_ite_eq]

/-! ### The mixture over the randomness -/

/-- **A good log** for the randomness `μ` and the answers `g`: the answers `g c` gives to its queries, `c ← μ`,
are its answers with the joint probability of their `ν`-masses (nonzero). -/
def Good (ν : Q → ProbComp R) {C : Type} (μ : ProbComp C) (g : C → Q → R) (L : List (Q × R)) : Prop :=
  (∑' c, Pr{let x ← μ}[x = c] * agrees (g c) L 0) = weight ν L 0 ∧ weight ν L 0 ≠ 0

theorem weight_le_one (ν : Q → ProbComp R) (L : List (Q × R)) (n : ℕ) : weight ν L n ≤ 1 := by
  unfold weight
  generalize L.drop n = l
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mul_le_one' (prEvent_le_one _) ih

/-- **The mixture's mass is the `ν`-run's on good logs.** -/
theorem mix_eq {C : Type} (ν : Q → ProbComp R) (μ : ProbComp C) (g : C → Q → R) (P : RProg σ Q R α)
    (s : σ) (o : α × σ × List (Q × R)) (hg : Good ν μ g o.2.2) :
    Pr{let y ← (μ >>= fun c ↦ semL (fun q ↦ pure (g c q)) P s [])}[y = o] =
      Pr{let y ← semL ν P s []}[y = o] := by
  have hW := hg.2
  have hWt : weight ν o.2.2 0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (weight_le_one _ _ _)
  have h : Pr{let y ← (μ >>= fun c ↦ semL (fun q ↦ pure (g c q)) P s [])}[y = o] * weight ν o.2.2 0 =
      Pr{let y ← semL ν P s []}[y = o] * weight ν o.2.2 0 := by
    rw [prEvent_bind_eq_tsum, ← ENNReal.tsum_mul_right]
    conv_rhs => rw [← hg.1, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun c ↦ ?_
    have := factor ν (g c) P s [] o
    simp only [List.length_nil] at this
    rw [mul_assoc, this]
    ring
  exact (ENNReal.mul_left_inj hW hWt).1 h

/-- **The two runs differ by at most the `ν`-run's bad logs**, on every event. -/
theorem trace_le {C : Type} (ν : Q → ProbComp R) (μ : ProbComp C) (g : C → Q → R) (P : RProg σ Q R α)
    (s : σ) (A : α × σ × List (Q × R) → Prop) :
    Pr{let y ← (μ >>= fun c ↦ semL (fun q ↦ pure (g c q)) P s [])}[A y] ≤
        Pr{let y ← semL ν P s []}[A y] + Pr{let y ← semL ν P s []}[¬ Good ν μ g y.2.2] ∧
      Pr{let y ← semL ν P s []}[A y] ≤
        Pr{let y ← (μ >>= fun c ↦ semL (fun q ↦ pure (g c q)) P s [])}[A y] +
          Pr{let y ← semL ν P s []}[¬ Good ν μ g y.2.2] := by
  classical
  set X := (μ >>= fun c ↦ semL (fun q ↦ pure (g c q)) P s [])
  set Y := semL ν P s []
  set G : α × σ × List (Q × R) → Prop := fun y ↦ Good ν μ g y.2.2
  have hmix : ∀ o, G o → Pr{let y ← X}[y = o] = Pr{let y ← Y}[y = o] := fun o h ↦ mix_eq ν μ g P s o h
  -- The good mass is the same in both.
  have hgood : Pr{let y ← X}[G y] = Pr{let y ← Y}[G y] := by
    rw [prEvent_eq_tsum_ite, prEvent_eq_tsum_ite]
    refine tsum_congr fun o ↦ ?_
    split_ifs with h
    · exact hmix o h
    · rfl
  have hbad : Pr{let y ← X}[¬ G y] = Pr{let y ← Y}[¬ G y] := by
    rw [prEvent_not_eq_one_sub, prEvent_not_eq_one_sub, hgood]
  -- An event splits into its good and its bad part.
  have hsplit : ∀ (Z : ProbComp (α × σ × List (Q × R))),
      Pr{let y ← Z}[A y] ≤ Pr{let y ← Z}[A y ∧ G y] + Pr{let y ← Z}[¬ G y] := by
    intro Z
    refine (prEvent_mono Z (fun y ↦ A y) (fun y ↦ (A y ∧ G y) ∨ ¬ G y) fun y hy ↦ ?_).trans
      (prEvent_or_le Z _ _)
    by_cases h : G y
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr h
  have hAG : Pr{let y ← X}[A y ∧ G y] = Pr{let y ← Y}[A y ∧ G y] := by
    rw [prEvent_eq_tsum_ite, prEvent_eq_tsum_ite]
    refine tsum_congr fun o ↦ ?_
    split_ifs with h
    · exact hmix o h.2
    · rfl
  refine ⟨?_, ?_⟩
  · refine (hsplit X).trans ?_
    rw [hAG, hbad]
    gcongr
    exact prEvent_mono Y _ _ fun _ h ↦ h.1
  · refine (hsplit Y).trans ?_
    rw [← hAG]
    gcongr
    exact prEvent_mono X _ _ fun _ h ↦ h.1

end RProg

end PcsQuotient.EndToEnd
