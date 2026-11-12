-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. The probability laws are VCVio's (pinned by leanerVM `mumbai` 6175f1a0, Apache-2.0).
import ZK.PcsExtract

/-!
# Ideal answers from a stream of uniform elements

With `n` tracked queries on every path (`CountQ`), the ideal run is, in distribution, a stream of `n` uniform
elements of `E` drawn first and the run whose `i`-th tracked answer is `mk` of the `i`-th element and fresh
words (`interpS`; **`stream`**). So the challenges an ideal run reads from its answers are functions of the stream.
-/

open OracleComp OracleSpec Common
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open scoped ENNReal

namespace PcsQuotient.EndToEnd

open FProg

variable {A α β : Type}

/-- The ideal answer from the element `e`: `mk e` of uniform words, recorded. -/
noncomputable def idealPermE (e : E) (x : KeccakState) : StateT (Edges × A) ProbComp KeccakState :=
  fun s ↦ (fun w ↦ (mk e w, ((x, mk e w) :: s.1, s.2))) <$> wDist

/-- The run whose tracked answers take their elements from the stream `es`, in order. -/
noncomputable def interpS : FProg A α → List E → StateT (Edges × A) ProbComp α
  | .ret a, _ => pure a
  | .step m k, es => m >>= fun b ↦ interpS (k b) es
  | .q x k, es => idealPermE (es.headD 0) x >>= fun y ↦ interpS (k y) es.tail
  | .r k, es => interpS (k (es.headD 0)) es.tail

/-- **Exactly `n` tracked queries on every path.** -/
def CountQ : FProg A α → ℕ → Prop
  | .ret _, n => n = 0
  | .step _ k, n => ∀ b, CountQ (k b) n
  | .q _ k, n => ∃ n', n = n' + 1 ∧ ∀ y, CountQ (k y) n'
  | .r k, n => ∃ n', n = n' + 1 ∧ ∀ e, CountQ (k e) n'

/-- `n` uniform elements. -/
noncomputable def iidE (n : ℕ) : ProbComp (List E) := (List.range n).mapM fun _ ↦ eDist

theorem iidE_zero : iidE 0 = pure [] := rfl

theorem iidE_succ (n : ℕ) : iidE (n + 1) = (do let e ← eDist; let es ← iidE n; pure (e :: es)) := by
  rw [iidE, List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
  rfl

theorem CountQ.bind {P : FProg A α} {a b : ℕ} (hP : CountQ P a) {f : α → FProg A β} (hf : ∀ x, CountQ (f x) b) :
    CountQ (P.bind f) (a + b) := by
  induction P generalizing a with
  | ret x => simp only [CountQ] at hP; subst hP; simpa [FProg.bind] using hf x
  | step m k ih => exact fun c ↦ ih c (hP c)
  | q x k ih =>
    obtain ⟨n', rfl, hk⟩ := hP
    exact ⟨n' + b, by omega, fun y ↦ ih y (hk y)⟩
  | r k ih =>
    obtain ⟨n', rfl, hk⟩ := hP
    exact ⟨n' + b, by omega, fun y ↦ ih y (hk y)⟩

/-- **The stream lemma.** -/
theorem stream (P : FProg A α) : ∀ (n : ℕ), CountQ P n → ∀ s : Edges × A,
    (interpI P).run s =ᵈ (do let es ← iidE n; (interpS P es).run s) := by
  induction P with
  | ret a =>
    intro n hn s
    simp only [CountQ] at hn
    subst hn
    rw [iidE_zero, pure_bind]
    rfl
  | step m k ih =>
    intro n hn s
    have e1 : (interpI (FProg.step m k)).run s = m.run s >>= fun p ↦ (interpI (k p.1)).run p.2 :=
      StateT.run_bind _ _ _
    have e2 : ∀ es, (interpS (FProg.step m k) es).run s = m.run s >>= fun p ↦ (interpS (k p.1) es).run p.2 :=
      fun es ↦ StateT.run_bind _ _ _
    rw [e1]
    simp only [e2]
    refine EvalDistEq.trans (EvalDistEq.bind_right _ ?_) (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
    intro p
    exact ih p.1 n (hn p.1) p.2
  | q x k ih =>
    intro n hn s
    obtain ⟨n', rfl, hk⟩ := hn
    have e1 : (interpI (FProg.q x k)).run s =
        uState >>= fun y ↦ (interpI (k y)).run ((x, y) :: s.1, s.2) := by
      show (idealPerm x >>= fun y ↦ interpI (k y)).run s = _
      rw [StateT.run_bind, show (idealPerm (A := A) x).run s = (fun y ↦ (y, ((x, y) :: s.1, s.2))) <$> uState
        from rfl, bind_map_left]
    have e2 : ∀ e es, (interpS (FProg.q x k) (e :: es)).run s =
        wDist >>= fun w ↦ (interpS (k (mk e w)) es).run ((x, mk e w) :: s.1, s.2) := by
      intro e es
      show (idealPermE e x >>= fun y ↦ interpS (k y) es).run s = _
      rw [StateT.run_bind, show (idealPermE (A := A) e x).run s =
        (fun w ↦ (mk e w, ((x, mk e w) :: s.1, s.2))) <$> wDist from rfl, bind_map_left]
    rw [e1, iidE_succ]
    simp only [bind_assoc, pure_bind, e2]
    refine (EvalDistEq.bind_left uState_eq_mkDist _).trans ?_
    simp only [mkDist, bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun e ↦ ?_
    exact (EvalDistEq.bind_right _ fun w ↦ ih _ n' (hk _) _).trans (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  | r k ih =>
    intro n hn s
    obtain ⟨n', rfl, hk⟩ := hn
    have e1 : (interpI (FProg.r k)).run s = eDist >>= fun e ↦ (interpI (k e)).run s := by
      show (rDraw >>= fun e ↦ interpI (k e)).run s = _
      rw [StateT.run_bind, show (rDraw (A := A)).run s = (fun e ↦ (e, s)) <$> eDist from rfl, bind_map_left]
    have e2 : ∀ e es, (interpS (FProg.r k) (e :: es)).run s = (interpS (k e) es).run s := fun _ _ ↦ rfl
    rw [e1, iidE_succ]
    simp only [bind_assoc, pure_bind, e2]
    exact EvalDistEq.bind_right _ fun e ↦ ih e n' (hk e) s

end PcsQuotient.EndToEnd
