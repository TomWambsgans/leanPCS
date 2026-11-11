-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-- New here. The lazily sampled permutation is leanerVM's (branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0:
-- `Statement/RandomPermutation.lean`); the probability laws are VCVio's.
import ZK.PcsReplay
import ZK.PcsCoins

/-!
# The lazily sampled permutation against independent uniform answers

A program (`FProg`) runs black-box steps on the state `Edges × A` and **tracked queries** `q x` of the
permutation. Run for real (`interpR`), a tracked query is the lazily sampled permutation's forward call
(`edgePerm`); run ideally (`interpI`), it is an independent uniform state, recorded as an edge without looking at
the edges (`idealPerm`).

**`close`**: on every event, the real run is at most as likely as the ideal one plus `badB P s`, the expectation
along the ideal run of the tracked queries' local costs: `1` if the input is already an edge's input, else the
fraction of states already used as answers (`εq`). The argument is functional closeness (`CloseF`), which a
common prefix (with costs averaged) and a common continuation preserve; one tracked query is close to its ideal
answer because a fresh lazy answer is uniform among the unused states, at least as likely as a uniform state on
each of them (`close_query`).
-/

open OracleComp OracleSpec Common
open LeanVM.Semantics LeanVM.Protocol
open scoped ENNReal

namespace PcsQuotient.EndToEnd

/-! ### Functional closeness -/

/-- **`X` is within `ε` of `Y`** on every `[0, 1]`-valued observation. -/
def CloseF {γ : Type} (X Y : ProbComp γ) (ε : ℝ≥0∞) : Prop :=
  ∀ h : γ → ℝ≥0∞, (∀ a, h a ≤ 1) →
    ∑' a, Pr{let y ← X}[y = a] * h a ≤ ∑' a, Pr{let y ← Y}[y = a] * h a + ε

namespace CloseF

variable {γ δ : Type}

theorem tsum_mul_le_one (X : ProbComp γ) (h : γ → ℝ≥0∞) (hh : ∀ a, h a ≤ 1) :
    ∑' a, Pr{let y ← X}[y = a] * h a ≤ 1 :=
  (ENNReal.tsum_le_tsum fun a ↦ mul_le_of_le_one_right' (hh a)).trans (tsum_prEvent_eq_one X).le

theorem refl (X : ProbComp γ) : CloseF X X 0 := fun _ _ ↦ by simp

theorem mono {X Y : ProbComp γ} {ε ε' : ℝ≥0∞} (h : CloseF X Y ε) (hε : ε ≤ ε') : CloseF X Y ε' :=
  fun g hg ↦ (h g hg).trans (by gcongr)

theorem of_one_le {X Y : ProbComp γ} {ε : ℝ≥0∞} (hε : 1 ≤ ε) : CloseF X Y ε :=
  fun g hg ↦ (tsum_mul_le_one X g hg).trans (hε.trans le_add_self)

theorem trans {X Y Z : ProbComp γ} {ε₁ ε₂ : ℝ≥0∞} (h₁ : CloseF X Y ε₁) (h₂ : CloseF Y Z ε₂) :
    CloseF X Z (ε₁ + ε₂) := fun g hg ↦ by
  calc ∑' a, Pr{let y ← X}[y = a] * g a ≤ ∑' a, Pr{let y ← Y}[y = a] * g a + ε₁ := h₁ g hg
    _ ≤ (∑' a, Pr{let y ← Z}[y = a] * g a + ε₂) + ε₁ := by gcongr; exact h₂ g hg
    _ = ∑' a, Pr{let y ← Z}[y = a] * g a + (ε₁ + ε₂) := by ring

/-- **A common continuation.** -/
theorem bind_right {X Y : ProbComp γ} {ε : ℝ≥0∞} (h : CloseF X Y ε) (f : γ → ProbComp δ) :
    CloseF (X >>= f) (Y >>= f) ε := fun g hg ↦ by
  rw [tsum_prEvent_bind_mul, tsum_prEvent_bind_mul]
  exact h _ fun a ↦ tsum_mul_le_one (f a) g hg

/-- **A common prefix**, the continuations' distances averaged. -/
theorem bind_left (X : ProbComp γ) {f f' : γ → ProbComp δ} (ε : γ → ℝ≥0∞)
    (h : ∀ a, CloseF (f a) (f' a) (ε a)) :
    CloseF (X >>= f) (X >>= f') (∑' a, Pr{let y ← X}[y = a] * ε a) := fun g hg ↦ by
  rw [tsum_prEvent_bind_mul, tsum_prEvent_bind_mul, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a ↦ ?_
  rw [← mul_add]
  gcongr
  exact h a g hg

/-- **Dominance off a bad set**: if `Y` is at most `X` on every good outcome and `Y`'s bad outcomes weigh at
most `ε`, then `X` is within `ε` of `Y`. -/
theorem of_dom {X Y : ProbComp γ} (G : γ → Prop) [DecidablePred G]
    (hdom : ∀ a, G a → Pr{let y ← Y}[y = a] ≤ Pr{let y ← X}[y = a])
    {ε : ℝ≥0∞} (hbad : ∑' a, (if G a then 0 else Pr{let y ← Y}[y = a]) ≤ ε) :
    CloseF X Y ε := fun g hg ↦ by
  have hsplit : ∀ Z : ProbComp γ,
      ∑' a, Pr{let y ← Z}[y = a] * g a + ∑' a, Pr{let y ← Z}[y = a] * (1 - g a) = 1 := fun Z ↦ by
    rw [← ENNReal.tsum_add]
    simp_rw [← mul_add, add_tsub_cancel_of_le (hg _), mul_one]
    exact tsum_prEvent_eq_one Z
  have hY : ∑' a, Pr{let y ← Y}[y = a] * (1 - g a) ≤ ∑' a, Pr{let y ← X}[y = a] * (1 - g a) + ε := by
    refine le_trans ?_ (add_le_add_right hbad _)
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun a ↦ ?_
    split_ifs with ha
    · rw [add_zero]
      gcongr
      exact hdom a ha
    · exact le_add_left (mul_le_of_le_one_right' tsub_le_self)
  have hfin : ∑' a, Pr{let y ← Y}[y = a] * (1 - g a) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (tsum_mul_le_one Y _ fun _ ↦ tsub_le_self)
  refine (ENNReal.add_le_add_iff_right hfin).1 ?_
  calc ∑' a, Pr{let y ← X}[y = a] * g a + ∑' a, Pr{let y ← Y}[y = a] * (1 - g a)
      ≤ ∑' a, Pr{let y ← X}[y = a] * g a + (∑' a, Pr{let y ← X}[y = a] * (1 - g a) + ε) := by gcongr
    _ = 1 + ε := by rw [← add_assoc, hsplit X]
    _ = (∑' a, Pr{let y ← Y}[y = a] * g a + ∑' a, Pr{let y ← Y}[y = a] * (1 - g a)) + ε := by
      rw [hsplit Y]
    _ = ∑' a, Pr{let y ← Y}[y = a] * g a + ε + ∑' a, Pr{let y ← Y}[y = a] * (1 - g a) := by ring

/-- **An event**, from closeness. -/
theorem prEvent_le {X Y : ProbComp γ} {ε : ℝ≥0∞} (h : CloseF X Y ε) (p : γ → Prop) :
    Pr{let y ← X}[p y] ≤ Pr{let y ← Y}[p y] + ε := by
  classical
  have := h (fun a ↦ if p a then 1 else 0) fun a ↦ by split_ifs <;> simp
  simp only [mul_ite, mul_one, mul_zero] at this
  rwa [prEvent_eq_tsum_ite X p, prEvent_eq_tsum_ite Y p]

end CloseF

/-! ### Programs with tracked queries -/

/-- A uniform Keccak state. -/
noncomputable def uState : ProbComp KeccakState := $ᵗ KeccakState

/-- **A program with tracked queries**: return; a black-box step on the state; a tracked forward query. -/
inductive FProg (A α : Type) : Type 1 where
  | ret (a : α)
  | step {β : Type} (m : StateT (Edges × A) ProbComp β) (k : β → FProg A α)
  | q (x : KeccakState) (k : KeccakState → FProg A α)

namespace FProg

variable {A α β : Type}

/-- Sequencing. -/
def bind : FProg A α → (α → FProg A β) → FProg A β
  | ret a, f => f a
  | step m k, f => step m fun b ↦ bind (k b) f
  | q x k, f => q x fun y ↦ bind (k y) f

/-- The program run with the tracked queries answered by `P`. -/
def interpWith (P : KeccakState → StateT (Edges × A) ProbComp KeccakState) : FProg A α → StateT (Edges × A) ProbComp α
  | ret a => pure a
  | step m k => m >>= fun b ↦ interpWith P (k b)
  | q x k => P x >>= fun y ↦ interpWith P (k y)

theorem interpWith_bind (P : KeccakState → StateT (Edges × A) ProbComp KeccakState) (X : FProg A α)
    (f : α → FProg A β) : interpWith P (X.bind f) = interpWith P X >>= fun a ↦ interpWith P (f a) := by
  induction X with
  | ret a => simp [bind, interpWith]
  | step m k ih => simp [bind, interpWith, ih]
  | q x k ih => simp [bind, interpWith, ih]

end FProg

open FProg

/-- **The ideal answer**: a uniform state, recorded as an edge, the edges not looked at. -/
noncomputable def idealPerm {A : Type} (x : KeccakState) : StateT (Edges × A) ProbComp KeccakState :=
  fun s ↦ (fun y ↦ (y, ((x, y) :: s.1, s.2))) <$> uState

/-- The real run: tracked queries are the lazily sampled permutation's. -/
noncomputable abbrev interpR {A α : Type} (P : FProg A α) : StateT (Edges × A) ProbComp α := interpWith edgePerm P

/-- The ideal run: tracked queries are independent uniform answers. -/
noncomputable abbrev interpI {A α : Type} (P : FProg A α) : StateT (Edges × A) ProbComp α := interpWith idealPerm P

/-- **The local cost of a tracked query** at `s`: `1` if `x` is an edge's input, else the fraction of states that
are answers. -/
noncomputable def εq {A : Type} (s : Edges × A) (x : KeccakState) : ℝ≥0∞ :=
  (if (forwardLookup s.1 x).isSome then 1 else 0) + (s.1.length : ℝ≥0∞) * (Fintype.card KeccakState : ℝ≥0∞)⁻¹

/-- **The cost of a program** from `s`: the tracked queries' local costs, expected along the ideal run (its
steps run as they are, its tracked queries answered by independent uniform states). -/
noncomputable def badB {A α : Type} : FProg A α → (Edges × A) → ℝ≥0∞
  | .ret _, _ => 0
  | .step m k, s => ∑' p, Pr{let y ← m.run s}[y = p] * badB (k p.1) p.2
  | .q x k, s => εq s x + ∑' p, Pr{let y ← (idealPerm x).run s}[y = p] * badB (k p.1) p.2

/-! ### One tracked query -/

theorem prEvent_uState (y : KeccakState) :
    Pr{let z ← uState}[z = y] = (Fintype.card KeccakState : ℝ≥0∞)⁻¹ :=
  SampleableType.prEvent_uniformSample_eq_singleton y

theorem uniform_le_uniformAvoiding {S : Type} [DecidableEq S] [Fintype S] [SampleableType S] (l : List S) (y : S)
    (hy : y ∉ l) : Pr{let z ← ($ᵗ S : ProbComp S)}[z = y] ≤ Pr{let z ← uniformAvoiding l}[z = y] := by
  have h : ∃ y, y ∉ l := ⟨y, hy⟩
  rw [SampleableType.prEvent_uniformSample_eq_singleton, uniformAvoiding, dite_eq_left_of_eq_true (eq_true h)]
  have : Nonempty {x // x ∉ l} := ⟨⟨y, hy⟩⟩
  rw [show y = Subtype.val (⟨y, hy⟩ : {y // y ∉ l}) from rfl, prEvent_map_injective _ Subtype.val_injective]
  refine le_of_le_of_eq ?_ (@SampleableType.prEvent_uniformSample_eq_singleton _
    (SampleableType.subtype S (· ∉ l)) _ ⟨y, hy⟩).symm
  exact ENNReal.inv_le_inv.2 (Nat.cast_le.2 (Fintype.card_subtype_le _))

theorem uState_le_uniformAvoiding (l : List KeccakState) (y : KeccakState) (hy : y ∉ l) :
    Pr{let z ← uState}[z = y] ≤ Pr{let z ← uniformAvoiding l}[z = y] :=
  uniform_le_uniformAvoiding l y hy

theorem prEvent_uState_mem (l : List KeccakState) :
    Pr{let z ← uState}[z ∈ l] ≤ (l.length : ℝ≥0∞) * (Fintype.card KeccakState : ℝ≥0∞)⁻¹ := by
  induction l with
  | nil =>
    rw [(prEvent_eq_zero_iff _ _).2 fun z _ h ↦ List.not_mem_nil h]
    exact zero_le
  | cons a l ih =>
    calc Pr{let z ← uState}[z ∈ a :: l] ≤ Pr{let z ← uState}[z = a] + Pr{let z ← uState}[z ∈ l] := by
          refine (prEvent_mono _ _ (fun z ↦ z = a ∨ z ∈ l) fun z hz ↦ List.mem_cons.1 hz).trans
            (prEvent_or_le _ _ _)
      _ ≤ (Fintype.card KeccakState : ℝ≥0∞)⁻¹ + (l.length : ℝ≥0∞) * (Fintype.card KeccakState : ℝ≥0∞)⁻¹ := by
          rw [prEvent_uState]; gcongr
      _ = ((a :: l).length : ℝ≥0∞) * (Fintype.card KeccakState : ℝ≥0∞)⁻¹ := by
          rw [List.length_cons, Nat.cast_succ]; ring

/-- **One tracked query is close to its ideal answer.** -/
theorem close_query {A : Type} (x : KeccakState) (s : Edges × A) :
    CloseF ((edgePerm x).run s) ((idealPerm x).run s) (εq s x) := by
  cases hx : forwardLookup s.1 x with
  | some y =>
    refine CloseF.of_one_le ?_
    have h1 : εq s x = 1 + (s.1.length : ℝ≥0∞) * (Fintype.card KeccakState : ℝ≥0∞)⁻¹ := by
      simp only [εq, hx, Option.isSome_some, ite_true]
    rw [h1]
    exact le_self_add
  | none =>
    have h0 : εq s x = (s.1.length : ℝ≥0∞) * (Fintype.card KeccakState : ℝ≥0∞)⁻¹ := by
      simp only [εq, hx, Option.isSome_none, Bool.false_eq_true, ite_false, zero_add]
    rw [h0]
    have hR : (edgePerm (A := A) x).run s =
        (fun y ↦ (y, ((x, y) :: s.1, s.2))) <$> uniformAvoiding (s.1.map Prod.snd) := by
      rw [edgePerm_run, lazy_run_none hx, Functor.map_map]
    have hI : (idealPerm (A := A) x).run s = (fun y ↦ (y, ((x, y) :: s.1, s.2))) <$> uState := rfl
    have hinj : Function.Injective fun y : KeccakState ↦ (y, ((x, y) :: s.1, s.2)) :=
      fun a b h ↦ (Prod.ext_iff.1 h).1
    refine CloseF.of_dom (fun o ↦ o.1 ∉ s.1.map Prod.snd) ?_ ?_
    · rintro ⟨y, s'⟩ hy
      rw [hR, hI]
      by_cases hs : s' = ((x, y) :: s.1, s.2)
      · subst hs
        rw [prEvent_map_injective _ hinj, prEvent_map_injective _ hinj]
        exact uState_le_uniformAvoiding _ _ hy
      · rw [(prEvent_eq_zero_iff _ _).2 fun z hz h ↦ ?_]
        · exact zero_le
        · rw [support_map] at hz
          obtain ⟨y', -, rfl⟩ := hz
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hs rfl
    · rw [hI]
      calc ∑' o, (if o.1 ∉ s.1.map Prod.snd then 0
              else Pr{let z ← (fun y ↦ (y, ((x, y) :: s.1, s.2))) <$> uState}[z = o])
          = Pr{let z ← (fun y ↦ (y, ((x, y) :: s.1, s.2))) <$> uState}[z.1 ∈ s.1.map Prod.snd] := by
            rw [prEvent_eq_tsum_ite]
            refine tsum_congr fun o ↦ ?_
            by_cases h : o.1 ∈ s.1.map Prod.snd <;>
              simp only [h, not_true_eq_false, not_false_eq_true, ite_true, ite_false]
        _ = Pr{let z ← uState}[z ∈ s.1.map Prod.snd] := by rw [prEvent_map]
        _ ≤ _ := (prEvent_uState_mem _).trans_eq (by rw [List.length_map])

/-! ### The real run against the ideal run -/

/-- **The real run is within `badB P s` of the ideal run.** -/
theorem close {A α : Type} (P : FProg A α) (s : Edges × A) :
    CloseF ((interpR P).run s) ((interpI P).run s) (badB P s) := by
  induction P generalizing s with
  | ret a => exact CloseF.refl _
  | step m k ih =>
    have e1 : (interpR (FProg.step m k)).run s = m.run s >>= fun p ↦ (interpR (k p.1)).run p.2 :=
      StateT.run_bind _ _ _
    have e2 : (interpI (FProg.step m k)).run s = m.run s >>= fun p ↦ (interpI (k p.1)).run p.2 :=
      StateT.run_bind _ _ _
    have e3 : badB (FProg.step m k) s = ∑' p, Pr{let y ← m.run s}[y = p] * badB (k p.1) p.2 := by
      rw [badB]
    rw [e1, e2, e3]
    exact CloseF.bind_left (m.run s) (fun p ↦ badB (k p.1) p.2) fun p ↦ ih p.1 p.2
  | q x k ih =>
    have e1 : (interpR (FProg.q x k)).run s = (edgePerm x).run s >>= fun p ↦ (interpR (k p.1)).run p.2 :=
      StateT.run_bind _ _ _
    have e2 : (interpI (FProg.q x k)).run s = (idealPerm x).run s >>= fun p ↦ (interpI (k p.1)).run p.2 :=
      StateT.run_bind _ _ _
    have e3 : badB (FProg.q x k) s =
        εq s x + ∑' p, Pr{let y ← (idealPerm x).run s}[y = p] * badB (k p.1) p.2 := by
      rw [badB]
    rw [e1, e2, e3]
    exact ((close_query x s).bind_right _).trans
      (CloseF.bind_left ((idealPerm x).run s) (fun p ↦ badB (k p.1) p.2) fun p ↦ ih p.1 p.2)

end PcsQuotient.EndToEnd
