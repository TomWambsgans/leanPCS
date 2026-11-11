-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The lazy-to-eager step is `TwoOracle.lean`'s
-- (`prEvent_randomOracle_le_of_freshBad_dep`), after VCVio's `randomOracle_restrictQueries` and
-- `evalDist_simulateQ_randomOracle_run'_eq_completeTable` (https://github.com/Verified-zkEVM/VCVio, Apache-2.0).
import Compose.WideSpec

/-!
# The rate model's events from the two-oracle model's, tail by tail

A computation of the rate model (`KeccakCallsR`) whose event the two-oracle model bounds for **every** fixed answer
of the tails is bounded in the rate model: **`prEvent_rate_le`**,

`Pr_R[P] ≤ b`  when  `∀ τ, Pr[P (simulateQ (instR τ) oa)] ≤ b`.

The rate model's lazy oracle is a uniform table on the computation's finite set of possible queries
(`possibleQueryKeys`); such a table is a uniform two-oracle table and an independent uniform table of tails
(`rateEquiv`); the computation on it is its split (`instR τ`, `eval_instR`) on the two-oracle table, for the tails
`τ` the tail table gives. Averaging over the tails gives the bound. It is how the openings' doom and the seed's pair,
bounded in the two-oracle model for any computation, are bounded in the rate model (π1-rec4).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics

/-! ## The split asks the same queries -/

theorem allQueriesSatisfy_instR (τ : List UInt8 → TailP) {α : Type} (p : List UInt8 ⊕ KeccakState → Prop) :
    ∀ (oa : OracleComp KeccakCallsR α), AllQueriesSatisfy oa p →
      AllQueriesSatisfy (simulateQ (instR τ) oa) p := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro _; exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    intro h
    obtain ⟨ht, hk⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
    rcases t with x | s
    · have e : simulateQ (instR τ) (liftM (KeccakCallsR.query (.inl x)) >>= k) =
          liftM (KeccakCalls.query (.inl x)) >>= fun dg => simulateQ (instR τ) (k (dg, τ x)) := by
        rw [simulateQ_bind, simulateQ_spec_query]
        show ((fun d => (d, τ x)) <$> (liftM (KeccakCalls.query (.inl x)) : OracleComp KeccakCalls Digest)) >>= _ = _
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
        rfl
      rw [e]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨ht, fun dg => ih _ (hk _)⟩
    · have e : simulateQ (instR τ) (liftM (KeccakCallsR.query (.inr s)) >>= k) =
          liftM (KeccakCalls.query (.inr s)) >>= fun y => simulateQ (instR τ) (k y) := by
        rw [simulateQ_bind, simulateQ_spec_query]
        rfl
      rw [e]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨ht, fun y => ih _ (hk _)⟩

/-- **Tables agreeing on the queries a computation may ask give it one result.** -/
theorem eval_congr_on {D : Type} {R : D → Type} {α : Type} (S : Finset D) (T T' : ∀ d, R d)
    (hT : ∀ d ∈ S, T d = T' d) :
    ∀ (oa : OracleComp (OracleSpec.ofFn R) α), AllQueriesSatisfy oa (· ∈ S) →
      evalWithAnswerFn (QueryImpl.ofFn T) oa = evalWithAnswerFn (QueryImpl.ofFn T') oa := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure a => intro _; rfl
  | query_bind t k ih =>
    intro h
    obtain ⟨ht, hk⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
    rw [hT t ht]
    exact ih _ (hk _)

/-! ## The eager form -/

section Eager

variable {D : Type} {R : D → Type} [DecidableEq D] [∀ d, Fintype (R d)] [∀ d, Nonempty (R d)]
  [∀ d, SampleableType (R d)]

/-- **The lazy oracle is a uniform table on a finite set holding every query.** -/
theorem prEvent_eager {α : Type} (oa : OracleComp (OracleSpec.ofFn R) α) (S : Finset D)
    (hS : AllQueriesSatisfy oa (· ∈ S)) (P : α → Prop) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[P r] =
      Pr{let g ← $ᵗ ((d : ↥S) → R d.1)}[P (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) oa)] := by
  classical
  let small := restrictQueries S oa hS
  have hrun : (simulateQ randomOracle small).run' ∅ = (simulateQ randomOracle oa).run' ∅ := by
    rw [← randomOracle_restrictQueries S oa hS ∅, restrictCache_empty_dep]
  rw [← hrun]
  let : MeasurableSpace α := ⊤
  have heager := evalDist_simulateQ_randomOracle_run'_eq_completeTable small ∅
  simp only [completeTable_empty] at heager
  rw [(EvalDistEq.of_evalDist_eq heager).prEvent_eq P]
  simp only [prEvent_norm]
  have hfun : (fun g : (d : ↥S) → R d.1 => P (evalWithAnswerFn (QueryImpl.ofFn g) small)) =
      fun g => P (evalWithAnswerFn (QueryImpl.ofFn (extendTable S g)) oa) := by
    funext g
    have hg : (fun d : ↥S => extendTable S g d.1) = g := funext (extendTable_subtype S g)
    have heval := evalWithAnswerFn_restrictQueries S oa hS (extendTable S g)
    rw [hg] at heval
    rw [heval]
  rw [hfun]

end Eager

/-! ## A rate table is a two-oracle table and a tail table -/

section Split

open Classical

variable (S : Finset (List UInt8 ⊕ KeccakState))

/-- The tails a tail table on `S`'s Keccak-256 inputs gives (fixed elsewhere). -/
noncomputable def tailsOf (gT : ↥(viewH S) → TailP) (x : List UInt8) : TailP :=
  if h : Sum.inl x ∈ S then gT ⟨x, mem_viewH.mpr h⟩ else (Classical.arbitrary (KeccakCallsR (.inl x))).2

/-- A two-oracle table with tails, as a rate table. -/
def joinR (TD : KTable) (τ : List UInt8 → TailP) : KTableR
  | .inl x => (TD (.inl x), τ x)
  | .inr s => TD (.inr s)

/-- **The rate table on `S` of a tail table and a two-oracle table.** -/
noncomputable def rateJoin (p : (↥(viewH S) → TailP) × ((d : ↥S) → KeccakCalls d.1)) :
    (d : ↥S) → KeccakCallsR d.1 :=
  fun d => joinR (extendTable S p.2) (tailsOf S p.1) d.1

/-- Its inverse. -/
noncomputable def rateSplit (g : (d : ↥S) → KeccakCallsR d.1) :
    (↥(viewH S) → TailP) × ((d : ↥S) → KeccakCalls d.1) :=
  (fun x => (g ⟨.inl x.1, mem_viewH.mp x.2⟩).2, fun d => splitD (extendTable S g) d.1)

/-- **A rate table on `S` is a tail table and a two-oracle table.** -/
noncomputable def rateEquiv :
    ((↥(viewH S) → TailP) × ((d : ↥S) → KeccakCalls d.1)) ≃
      ((d : ↥S) → KeccakCallsR d.1) where
  toFun := rateJoin S
  invFun := rateSplit S
  left_inv p := by
    obtain ⟨gT, gD⟩ := p
    refine Prod.ext ?_ ?_
    · funext x
      show (joinR (extendTable S gD) (tailsOf S gT) (.inl x.1)).2 = gT x
      simp [joinR, tailsOf, mem_viewH.mp x.2]
    · funext d
      obtain ⟨d, hd⟩ := d
      show splitD (extendTable S (rateJoin S (gT, gD))) d = gD ⟨d, hd⟩
      rcases d with x | s
      · simp [splitD, extendTable, hd, rateJoin, joinR]
      · simp [splitD, extendTable, hd, rateJoin, joinR]
  right_inv g := by
    funext d
    obtain ⟨d, hd⟩ := d
    rcases d with x | s
    · show joinR (extendTable S (rateSplit S g).2) (tailsOf S (rateSplit S g).1) (.inl x) = g ⟨.inl x, hd⟩
      simp [joinR, rateSplit, splitD, extendTable, hd, tailsOf]
    · show joinR (extendTable S (rateSplit S g).2) (tailsOf S (rateSplit S g).1) (.inr s) = g ⟨.inr s, hd⟩
      simp [joinR, rateSplit, splitD, extendTable, hd]

/-- The rate table's tails are the tail table's. -/
theorem splitT_rateJoin (p : (↥(viewH S) → TailP) × ((d : ↥S) → KeccakCalls d.1)) :
    splitT (extendTable S (rateJoin S p)) = tailsOf S p.1 := by
  funext x
  by_cases h : Sum.inl x ∈ S
  · simp [splitT, extendTable, h, rateJoin, joinR]
  · simp [splitT, extendTable, h, tailsOf]

/-- The rate table's digests are the two-oracle table's, on `S`. -/
theorem splitD_rateJoin (p : (↥(viewH S) → TailP) × ((d : ↥S) → KeccakCalls d.1)) :
    ∀ d ∈ S, splitD (extendTable S (rateJoin S p)) d = extendTable S p.2 d := by
  intro d hd
  rcases d with x | s
  · simp [splitD, extendTable, hd, rateJoin, joinR]
  · simp [splitD, extendTable, hd, rateJoin, joinR]

end Split

/-! ## The bound -/

/-- **An event of the rate model bounded for every fixed answer of the tails is bounded.** -/
theorem prEvent_rate_le {α : Type} (oa : OracleComp KeccakCallsR α) (P : α → Prop) (b : ℝ≥0∞)
    (h : ∀ τ : List UInt8 → TailP,
      Pr{let r ← (simulateQ randomOracle (simulateQ (instR τ) oa)).run' ∅}[P r] ≤ b) :
    Pr{let r ← (simulateQ randomOracle oa).run' ∅}[P r] ≤ b := by
  classical
  let S := possibleQueryKeys oa
  have hS : AllQueriesSatisfy oa (· ∈ S) := allQueriesSatisfy_possibleQueryKeys oa
  rw [prEvent_eager oa S hS P]
  -- The uniform rate table as a uniform tail table and a uniform two-oracle table.
  have hU : ∀ Q : ((d : ↥S) → KeccakCallsR d.1) → Prop,
      Pr{let g ← $ᵗ ((d : ↥S) → KeccakCallsR d.1)}[Q g] =
        Pr{let p ← $ᵗ ((↥(viewH S) → TailP) × ((d : ↥S) → KeccakCalls d.1))}[
          Q (rateEquiv S p)] := by
    intro Q
    symm
    refine prEvent_uniform_balanced (rateEquiv S) 1 (fun g => ?_) Q
    rw [Finset.card_eq_one]
    refine ⟨(rateEquiv S).symm g, ?_⟩
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hp
      rw [← hp, Equiv.symm_apply_apply]
    · intro hp
      rw [hp, Equiv.apply_symm_apply]
  rw [hU, SampleableType.uniformSample_prod_eq_bind]
  refine prEvent_bind_le_of_forall_le _ _ _ fun gT => ?_
  -- For the tails `gT`: the two-oracle model's event.
  have hτ := h (tailsOf S gT)
  have hS' : AllQueriesSatisfy (simulateQ (instR (tailsOf S gT)) oa) (· ∈ S) :=
    allQueriesSatisfy_instR _ _ oa hS
  rw [prEvent_eager _ S hS' P] at hτ
  have key : ∀ gD : (d : ↥S) → KeccakCalls d.1,
      evalWithAnswerFn (QueryImpl.ofFn (extendTable S (rateEquiv S (gT, gD)))) oa =
        evalWithAnswerFn (QueryImpl.ofFn (extendTable S gD)) (simulateQ (instR (tailsOf S gT)) oa) := by
    intro gD
    show evalWithAnswerFn (QueryImpl.ofFn (extendTable S (rateJoin S (gT, gD)))) oa = _
    rw [eval_instR, splitT_rateJoin S (gT, gD),
      eval_congr_on S _ _ (splitD_rateJoin S (gT, gD)) _ hS']
  calc _ = Pr{let gD ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[
          P (evalWithAnswerFn (QueryImpl.ofFn (extendTable S (rateEquiv S (gT, gD)))) oa)] := by
        rw [bind_pure_comp, prEvent_map]
    _ = Pr{let gD ← $ᵗ ((d : ↥S) → KeccakCalls d.1)}[
          P (evalWithAnswerFn (QueryImpl.ofFn (extendTable S gD)) (simulateQ (instR (tailsOf S gT)) oa))] := by
        simp only [key]
    _ ≤ b := hτ

end Compose

/-- info: 'Compose.prEvent_rate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compose.prEvent_rate_le
