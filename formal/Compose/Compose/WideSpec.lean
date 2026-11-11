-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. The two-oracle model is leanerVM `mumbai`'s
-- (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0: `KeccakCalls`), with Keccak-256's
-- whole rate as its answer (`formal/UniKeccakSound/UniKeccakSound/Rec4/RateTransfer.lean`'s `Keccak256RateTransfer`).
import Compose.TwoOracle
import Compose.ListChainK

/-!
# The rate model: Keccak-256 answering its whole rate (π1-rec4's wide draws)

π1-rec4's wide draws (`UniStatement.sampleWide`) read several challenges off one Keccak-256 call: the sponge's rate
after the last permutation, its first 32 bytes the digest. In the two-oracle random-oracle model the rate transfer
(`Keccak256RateTransfer`) gives, Keccak-256 answers the whole rate, uniform. Here:

* **the tail** (`TailP`): the rate past the digest as the challenges read it: four limb triples (lanes `4 … 15`, each
  challenge's three limbs) and lane `16`; **a wide draw's challenges** (`chalW`): challenge `0` the digest's
  (`chalL`), challenge `k + 1` the tail's triple `k`; **`wide_evalDistEq`**: on a uniform answer, at most five of them
  are independent uniform challenges (`draws`);
* **the rate model** (`KeccakCallsR`): Keccak-256 answering a digest and a tail, Keccak-f[1600] as before;
  `hashR` (the chain's reading), `liftKC` (a computation of the two-oracle model reads the digest only);
* **the split** (`instR τ`): a computation of the rate model, its tails answered by a fixed `τ`, is one of the
  two-oracle model; a table of the rate model is a two-oracle table (`splitD`) and a tail table (`splitT`), and the
  computation's result and log on the one are the split computation's on the other (`eval_instR`, `log_instR`);
* **the log** (`loggedKCR`): every Keccak-256 query with its digest, as `loggedKC` logs it (`instR_loggedKCR`).
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp NNReal
open scoped ENNReal

namespace Compose

open QuotientRpm LeanVM LeanVM.Protocol LeanVM.Semantics

/-! ## The tail and a wide draw's challenges -/

/-- **The rate past the digest, as the challenges read it**: the limbs of challenges `1 … 4` (each the low, middle and
high limb), and the last lane. -/
abbrev TailP := Limbs × Limbs × Limbs × Limbs × UInt64

/-- The tail's four limb triples. -/
def tailList (tl : TailP) : List Limbs := [tl.1, tl.2.1, tl.2.2.1, tl.2.2.2.1]

variable {F : Type}

/-- **Challenge `k` of a wide draw** on the answer `(d, tl)`: challenge `0` the digest's (`chalL`), challenge `k + 1`
the tail's triple `k` (for `k ≥ 4`, the digest's again: a draw never reads it). -/
def chalW (lim : F ≃ Limbs) (d : Bytes32) (tl : TailP) : ℕ → F
  | 0 => chalL lim d
  | k + 1 => if k < 4 then lim.symm ((tailList tl).getD k (0, 0, 0)) else chalL lim d

/-- **A wide draw's `n` challenges.** -/
def chalsW (lim : F ≃ Limbs) (n : ℕ) (d : Bytes32) (tl : TailP) : List F :=
  (List.range n).map (chalW lim d tl)

theorem length_chalsW (lim : F ≃ Limbs) (n : ℕ) (d : Bytes32) (tl : TailP) :
    (chalsW lim n d tl).length = n := by
  simp [chalsW]

/-- A wide draw's first challenge is the digest's. -/
theorem chalsW_succ (lim : F ≃ Limbs) (n : ℕ) (d : Bytes32) (tl : TailP) :
    chalsW lim (n + 1) d tl = chalL lim d :: (List.range n).map fun k => chalW lim d tl (k + 1) := by
  simp only [chalsW, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-- **The tail's challenges**: the first `n` limb triples, as field elements. -/
theorem tail_chals (lim : F ≃ Limbs) (n : ℕ) (hn : n ≤ 4) (d : Bytes32) (tl : TailP) :
    ((List.range n).map fun k => chalW lim d tl (k + 1)) = ((tailList tl).take n).map lim.symm := by
  apply List.ext_getElem
  · simp [tailList]
    omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, chalW]
    rw [ite_eq_left (show i < 4 by omega)]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [tailList]; omega)]
    rfl

section Uniform

variable [Fintype F] [DecidableEq F] [SampleableType F]

/-- **A bijection sends the uniform distribution to the uniform one.** -/
theorem equiv_symm_evalDistEq (lim : F ≃ Limbs) :
    (lim.symm <$> ($ᵗ Limbs : ProbComp Limbs)) =ᵈ ($ᵗ F : ProbComp F) := fun p => by
  classical
  rw [prEvent_map]
  refine prEvent_uniform_balanced lim.symm 1 (fun x => ?_) p
  rw [Finset.card_eq_one]
  refine ⟨lim x, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    rw [← h, Equiv.apply_symm_apply]
  · intro h
    rw [h, Equiv.symm_apply_apply]

/-- **A uniform pair, its first read by `f` and its second by `g`, cons'd.** -/
theorem cons_evalDistEq {X Y : Type} [SampleableType X] [SampleableType Y] (f : X → F) (g : Y → List F) (n : ℕ)
    (hf : (f <$> ($ᵗ X : ProbComp X)) =ᵈ ($ᵗ F : ProbComp F)) (hg : (g <$> ($ᵗ Y : ProbComp Y)) =ᵈ draws F n) :
    ((fun p : X × Y => f p.1 :: g p.2) <$> ($ᵗ (X × Y) : ProbComp (X × Y))) =ᵈ draws F (n + 1) := by
  have e1 : ((fun p : X × Y => f p.1 :: g p.2) <$> ($ᵗ (X × Y) : ProbComp (X × Y))) =
      (f <$> ($ᵗ X : ProbComp X)) >>= fun a => (g <$> ($ᵗ Y : ProbComp Y)) >>= fun l => pure (a :: l) := by
    simp only [SampleableType.uniformSample_prod_eq_bind, map_bind, map_pure, bind_map_left]
  have e2 : draws F (n + 1) = ($ᵗ F : ProbComp F) >>= fun a => draws F n >>= fun l => pure (a :: l) := rfl
  rw [e1, e2]
  exact EvalDistEq.bind hf fun a => EvalDistEq.bind hg fun l => EvalDistEq.rfl

/-- **Nothing read of a uniform draw is no challenge.** -/
theorem nil_evalDistEq {X : Type} [SampleableType X] :
    ((fun _ : X => ([] : List F)) <$> ($ᵗ X : ProbComp X)) =ᵈ draws F 0 :=
  OracleComp.EvalDistEq.map_const _ _

/-- **`n ≤ 4` of a uniform tail's limb triples, as field elements, are `n` uniform challenges.** -/
theorem tail_evalDistEq (lim : F ≃ Limbs) (n : ℕ) (hn : n ≤ 4) :
    ((fun tl : TailP => ((tailList tl).take n).map lim.symm) <$> ($ᵗ TailP : ProbComp TailP)) =ᵈ
      draws F n := by
  have hU := equiv_symm_evalDistEq lim
  have h0 : ((fun _ : Limbs × Limbs × Limbs × Limbs × UInt64 => ([] : List F)) <$>
      ($ᵗ TailP : ProbComp TailP)) =ᵈ draws F 0 := nil_evalDistEq
  have h1 := cons_evalDistEq lim.symm (fun _ : Limbs × Limbs × Limbs × UInt64 => ([] : List F)) 0 hU
    nil_evalDistEq
  have h2 := cons_evalDistEq lim.symm (fun p : Limbs × Limbs × Limbs × UInt64 => [lim.symm p.1]) 1 hU
    (cons_evalDistEq lim.symm (fun _ : Limbs × Limbs × UInt64 => ([] : List F)) 0 hU nil_evalDistEq)
  have h3 := cons_evalDistEq lim.symm
    (fun p : Limbs × Limbs × Limbs × UInt64 => [lim.symm p.1, lim.symm p.2.1]) 2 hU
    (cons_evalDistEq lim.symm (fun p : Limbs × Limbs × UInt64 => [lim.symm p.1]) 1 hU
      (cons_evalDistEq lim.symm (fun _ : Limbs × UInt64 => ([] : List F)) 0 hU nil_evalDistEq))
  have h4 := cons_evalDistEq lim.symm
    (fun p : Limbs × Limbs × Limbs × UInt64 => [lim.symm p.1, lim.symm p.2.1, lim.symm p.2.2.1]) 3 hU
    (cons_evalDistEq lim.symm (fun p : Limbs × Limbs × UInt64 => [lim.symm p.1, lim.symm p.2.1]) 2 hU
      (cons_evalDistEq lim.symm (fun p : Limbs × UInt64 => [lim.symm p.1]) 1 hU
        (cons_evalDistEq lim.symm (fun _ : UInt64 => ([] : List F)) 0 hU nil_evalDistEq)))
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) with rfl | rfl | rfl | rfl | rfl
  · refine EvalDistEq.trans (EvalDistEq.of_forall_prEvent_eq fun p => ?_) h0
    rfl
  · refine EvalDistEq.trans (EvalDistEq.of_forall_prEvent_eq fun p => ?_) h1
    rfl
  · refine EvalDistEq.trans (EvalDistEq.of_forall_prEvent_eq fun p => ?_) h2
    rfl
  · refine EvalDistEq.trans (EvalDistEq.of_forall_prEvent_eq fun p => ?_) h3
    rfl
  · refine EvalDistEq.trans (EvalDistEq.of_forall_prEvent_eq fun p => ?_) h4
    rfl

/-- **At most five challenges of a wide draw on a uniform answer are independent uniform challenges.** -/
theorem wide_evalDistEq (lim : F ≃ Limbs) (n : ℕ) (hn : n ≤ 4) :
    ((fun p : Bytes32 × TailP => chalsW lim (n + 1) p.1 p.2) <$> ($ᵗ (Bytes32 × TailP) :
      ProbComp (Bytes32 × TailP))) =ᵈ draws F (n + 1) := by
  have e : (fun p : Bytes32 × TailP => chalsW lim (n + 1) p.1 p.2) =
      fun p => chalL lim p.1 :: ((tailList p.2).take n).map lim.symm := by
    funext p
    rw [chalsW_succ, tail_chals lim n hn]
  rw [e]
  exact cons_evalDistEq (chalL lim) (fun tl => ((tailList tl).take n).map lim.symm) n (chalL_evalDistEq lim)
    (tail_evalDistEq lim n hn)

theorem prEvent_wide (lim : F ≃ Limbs) (n : ℕ) (hn : n ≤ 4) (Q : List F → Prop) :
    Pr{let p ← $ᵗ (Bytes32 × TailP)}[Q (chalsW lim (n + 1) p.1 p.2)] = Pr{let l ← draws F (n + 1)}[Q l] := by
  rw [← prEvent_map]
  exact (wide_evalDistEq lim n hn).prEvent_eq Q

end Uniform

/-! ## The rate model -/

/-- **The rate model's two oracles**: Keccak-256 answering its rate (the digest and the tail), Keccak-f[1600]. -/
abbrev KeccakCallsR : OracleSpec (List UInt8 ⊕ KeccakState) :=
  (List UInt8 →ₒ (Digest × TailP)) + (KeccakState →ₒ KeccakState)

noncomputable instance instFintypeKeccakCallsR : ∀ t, Fintype (KeccakCallsR.Range t)
  | .inl _ => (inferInstance : Fintype (Digest × TailP))
  | .inr _ => (inferInstance : Fintype KeccakState)

instance instFiniteKeccakCallsR (t : List UInt8 ⊕ KeccakState) : Finite (KeccakCallsR.Range t) :=
  Finite.of_fintype _

instance instNonemptyKeccakCallsR : ∀ t, Nonempty (KeccakCallsR.Range t)
  | .inl _ => (inferInstance : Nonempty (Digest × TailP))
  | .inr _ => (inferInstance : Nonempty KeccakState)

noncomputable instance instSampleableKeccakCallsR : ∀ t, SampleableType (KeccakCallsR.Range t)
  | .inl _ => (inferInstance : SampleableType (Digest × TailP))
  | .inr _ => (inferInstance : SampleableType KeccakState)

instance instDecEqKeccakCallsR : ∀ t, DecidableEq (KeccakCallsR.Range t)
  | .inl _ => (inferInstance : DecidableEq (Digest × TailP))
  | .inr _ => (inferInstance : DecidableEq KeccakState)

/-- A call to the hash, its whole rate. -/
def callKeccak256R (x : List UInt8) : OracleComp KeccakCallsR (Digest × TailP) :=
  liftM (KeccakCallsR.query (.inl x))

/-- **Keccak-256 as a wide draw reads it**: the digest's 32 bytes and the tail. -/
def hashR (x : List UInt8) : OracleComp KeccakCallsR (Bytes32 × TailP) :=
  callKeccak256R x >>= fun u => pure (toB u.1, u.2)

/-- **A computation of the two-oracle model in the rate model**: Keccak-256 reads the digest only. -/
def liftKC : QueryImpl KeccakCalls (OracleComp KeccakCallsR)
  | .inl x => Prod.fst <$> (liftM (KeccakCallsR.query (.inl x)) : OracleComp KeccakCallsR (Digest × TailP))
  | .inr s => (liftM (KeccakCallsR.query (.inr s)) : OracleComp KeccakCallsR KeccakState)

/-- **The split**: a computation of the rate model in the two-oracle model, its tails answered by `τ`. -/
def instR (τ : List UInt8 → TailP) : QueryImpl KeccakCallsR (OracleComp KeccakCalls)
  | .inl x => (fun d => (d, τ x)) <$> (liftM (KeccakCalls.query (.inl x)) : OracleComp KeccakCalls Digest)
  | .inr s => (liftM (KeccakCalls.query (.inr s)) : OracleComp KeccakCalls KeccakState)

/-- A table of the rate model's oracles. -/
abbrev KTableR := (d : List UInt8 ⊕ KeccakState) → KeccakCallsR d

/-- **A rate table's two-oracle table**: the digests, the permutation's answers. -/
def splitD (T : KTableR) : KTable
  | .inl x => (T (.inl x)).1
  | .inr s => T (.inr s)

/-- **A rate table's tails.** -/
def splitT (T : KTableR) (x : List UInt8) : TailP := (T (.inl x)).2

/-- The split of a lifted computation is the computation. -/
theorem instR_liftKC (τ : List UInt8 → TailP) {α : Type} (oa : OracleComp KeccakCalls α) :
    simulateQ (instR τ) (simulateQ liftKC oa) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with x | s
    · simp only [simulateQ_bind, simulateQ_spec_query, liftKC, simulateQ_map, instR, ih,
        Functor.map_map, bind_map_left]
    · simp only [simulateQ_bind, simulateQ_spec_query, liftKC, instR, ih]

/-- **A rate computation on a rate table is its split on the split table.** -/
theorem eval_instR {α : Type} (T : KTableR) (oa : OracleComp KeccakCallsR α) :
    evalWithAnswerFn (QueryImpl.ofFn T) oa =
      evalWithAnswerFn (QueryImpl.ofFn (splitD T)) (simulateQ (instR (splitT T)) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with x | s
    · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, simulateQ_bind,
        simulateQ_spec_query, instR, evalWithAnswerFn_map, ih]
      rfl
    · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, simulateQ_bind,
        simulateQ_spec_query, instR, ih]
      rfl

/-- **The split asks the same queries.** -/
theorem log_instR {α : Type} (T : KTableR) (oa : OracleComp KeccakCallsR α) :
    (tableQueryLog oa T).map Sigma.fst =
      (tableQueryLog (simulateQ (instR (splitT T)) oa) (splitD T)).map Sigma.fst := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with x | s
    · simp only [tableQueryLog_query_bind, simulateQ_bind, simulateQ_spec_query, instR, bind_map_left,
        List.map_cons, ih]
      rfl
    · simp only [tableQueryLog_query_bind, simulateQ_bind, simulateQ_spec_query, instR, List.map_cons, ih]
      rfl

/-! ## The log -/

/-- A Keccak-256 query's transcript entry, its digest as 32 bytes; nothing for Keccak-f. -/
def inlEntryR (q : (d : List UInt8 ⊕ KeccakState) × KeccakCallsR d) : Option (List UInt8 × Bytes32) :=
  match q with
  | ⟨.inl x, u⟩ => some (x, toB u.1)
  | ⟨.inr _, _⟩ => none

/-- Both oracles, logging every Keccak-256 query and its digest. -/
def logImplKCR : QueryImpl KeccakCallsR (StateT Transcript (OracleComp KeccakCallsR)) := fun d l =>
  (fun u => (u, l ++ (inlEntryR ⟨d, u⟩).toList)) <$> liftM (KeccakCallsR.query d)

/-- A computation of the rate model with the transcript of its Keccak-256 queries' digests. -/
def loggedKCR {α : Type} (oa : OracleComp KeccakCallsR α) : OracleComp KeccakCallsR (α × Transcript) :=
  (simulateQ logImplKCR oa).run []

theorem loggedKCR_run_query_bind {α : Type} (d : List UInt8 ⊕ KeccakState)
    (k : KeccakCallsR d → OracleComp KeccakCallsR α) (l : Transcript) :
    (simulateQ logImplKCR (liftM (KeccakCallsR.query d) >>= k)).run l =
      liftM (KeccakCallsR.query d) >>= fun u =>
        (simulateQ logImplKCR (k u)).run (l ++ (inlEntryR ⟨d, u⟩).toList) := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change ((fun u => (u, l ++ (inlEntryR ⟨d, u⟩).toList)) <$> liftM (KeccakCallsR.query d)) >>= _ = _
  rw [bind_map_left]

/-- **The split of a logged computation is the logged split.** -/
theorem instR_loggedKCR_run (τ : List UInt8 → TailP) {α : Type} (oa : OracleComp KeccakCallsR α) :
    ∀ l : Transcript, simulateQ (instR τ) ((simulateQ logImplKCR oa).run l) =
      (simulateQ logImplKC (simulateQ (instR τ) oa)).run l := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro l; simp
  | query_bind t k ih =>
    intro l
    rw [loggedKCR_run_query_bind]
    rcases t with x | s
    · have e : simulateQ (instR τ) (liftM (KeccakCallsR.query (.inl x)) >>= k) =
          liftM (KeccakCalls.query (.inl x)) >>= fun dg => simulateQ (instR τ) (k (dg, τ x)) := by
        rw [simulateQ_bind, simulateQ_spec_query]
        show ((fun d => (d, τ x)) <$> (liftM (KeccakCalls.query (.inl x)) : OracleComp KeccakCalls Digest)) >>= _ = _
        simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
        rfl
      rw [e, loggedKC_run_query_bind, simulateQ_bind, simulateQ_spec_query]
      show ((fun d => (d, τ x)) <$> (liftM (KeccakCalls.query (.inl x)) : OracleComp KeccakCalls Digest)) >>= _ = _
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      refine bind_congr fun dg => ?_
      rw [ih]
      rfl
    · have e : simulateQ (instR τ) (liftM (KeccakCallsR.query (.inr s)) >>= k) =
          liftM (KeccakCalls.query (.inr s)) >>= fun y => simulateQ (instR τ) (k y) := by
        rw [simulateQ_bind, simulateQ_spec_query]
        rfl
      rw [e, loggedKC_run_query_bind, simulateQ_bind, simulateQ_spec_query]
      refine bind_congr fun y => ?_
      rw [ih]
      rfl

theorem instR_loggedKCR (τ : List UInt8 → TailP) {α : Type} (oa : OracleComp KeccakCallsR α) :
    simulateQ (instR τ) (loggedKCR oa) = loggedKC (simulateQ (instR τ) oa) :=
  instR_loggedKCR_run τ oa []

end Compose
