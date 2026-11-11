-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Adapted from this repository's
-- `formal/Compose/Compose/Rpm.lean` and `formal/Compose/Compose/ListChainKRpmS.lean` (`adv_relabelC`, `hEmbed2_toRH`,
-- `rpmThreadedS_evalDistEq`, `duplex_postBS`, `cost_gameBS`) and from leanerVM `mumbai`
-- (https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0: `common/Common/Lanes.lean`'s
-- `absorbWith_lanePerm`, `absorbAll_rel`, `fwd_rel`; `lean_vm/LeanVM/Protocol/Rpm/RpmRelabel.lean`'s `post_relabel`,
-- `realGame2_eq`; `Rpm/Duplex.lean`'s `DuplexVm`; `LeanVMRpm.lean`'s `duplex_toRHF`, `duplex_map`,
-- `isWeightBound_advEmbed`, `isWeightBound_hfEmbed_toRHF`), on `RState` and the rate model in place of
-- `Common.KState` and the digest model.
import UniKeccakSound.Rec4.RpmRateBytes

/-!
# The rate model's random-permutation game is the real world of a transfer game on `RState`

* `keccakCallsROverQueryPermutation`: the rate model's two calls over `π` (Keccak-256's last state read as
  `rateOfState`, Keccak-f `= π`); over the digest it is the two-oracle model's (`simulateQ_liftR`);
* `toRHFR`, `toRHR`, `relPR`, `logRelCR`: the calls, the setup and the adversary on `RState`;
* **`post_relabelR`**, **`adv_relabelCR`**: in the real world of `RState`'s transfer (`RRR`) they are the
  calls and the adversary over the lazily sampled permutation of the lane states;
* `DuplexVmR`: the duplex discipline for the rate model; `duplex_toRHFR`: on `RState` it is `Common.Duplex` at
  `keccakNFR`; `hashBlocksR`: the calls of `π`.
-/

set_option linter.unusedSectionVars false

open OracleSpec OracleComp
open scoped ENNReal

namespace UniKeccakSound.Rec4

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open Common (KCap)
open Compose (TailP KeccakCallsR liftR)
open LeanVM.Rpm (HOnly DuplexVm AdmissibleVm StRel)

/-! ## The sponge on `RState` -/

theorem toRBlock_rxor (a b : Common.KBlock) :
    toRBlock (Common.rxor a b) = Common.rxor (toRBlock a) (toRBlock b) := by
  refine Prod.ext ?_ (rate0_eq _ _)
  apply Vector.ext
  intro i hi
  show (toRBlock (Common.rxor a b)).1[i] =
    (Vector.zipWith (· ^^^ ·) (toRBlock a).1 (toRBlock b).1)[i]
  rw [Vector.getElem_zipWith]
  simp only [toRBlock, Vector.getElem_ofFn, Common.rxor]
  split
  · exact Vector.getElem_zipWith ..
  · exact Vector.getElem_zipWith ..

theorem kBlockEquiv_rxor (a b : Common.KBlock) :
    kBlockEquiv (Common.rxor a b) = Common.rxor (kBlockEquiv a) (kBlockEquiv b) := toRBlock_rxor a b

theorem absorb_kEquivR (k : Common.KState) (B : Common.KBlock) :
    Common.absorb (kEquivR k) (kBlockEquiv B) = kEquivR (Common.absorb k B) := by
  simp only [Common.absorb, kEquivR, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
  rw [← kBlockEquiv_rxor]

theorem blockTo_kEquivR (s x : Common.KState) :
    Common.blockTo (kEquivR s) (kEquivR x) = kBlockEquiv (Common.blockTo s x) := by
  simp only [Common.blockTo, kEquivR, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
  rw [← kBlockEquiv_rxor]

theorem kEquivR_zero : kEquivR Common.KState.zero = RState.zero := by
  refine Prod.ext (Prod.ext ?_ (rate0_eq _ _)) rfl
  apply Vector.ext
  intro i hi
  simp only [kEquivR, Equiv.prodCongr_apply, Prod.map, kBlockEquiv, Equiv.coe_fn_mk, toRBlock,
    Vector.getElem_ofFn, Common.KState.zero, RState.zero, Vector.getElem_replicate]
  split <;> rfl

theorem absorbAll_kEquivR {m : Type → Type} [Monad m] [LawfulMonad m] (π : RState → m RState) :
    ∀ (k : Common.KState) (bs : List Common.KBlock),
      Common.absorbAll π (kEquivR k) (bs.map kBlockEquiv) =
        kEquivR <$> Common.absorbAll (fun k ↦ kEquivR.symm <$> π (kEquivR k)) k bs
  | k, [] => by simp
  | k, B :: bs => by
    simp only [List.map_cons, Common.absorbAll_cons, absorb_kEquivR, map_bind, bind_map_left]
    refine bind_congr fun y ↦ ?_
    rw [← absorbAll_kEquivR π _ bs, Equiv.apply_symm_apply]

theorem keccakPaddingR_pad (x : List UInt8) :
    keccakPaddingR.pad x = (Common.toBlocks (Common.keccakPadBytes x)).map kBlockEquiv := rfl

/-- **Keccak-256's last state over a permutation of the lane states is the sponge on `RState`** (Keccak-256's padding
on the rate's blocks, from the zero state), read back on lanes. -/
theorem keccak256StateWith_rEquiv {m : Type → Type} [Monad m] [LawfulMonad m] (π : RState → m RState)
    (x : List UInt8) :
    UniStatement.keccak256StateWith (fun s ↦ rEquiv.symm <$> π (rEquiv s)) x =
      rEquiv.symm <$> Common.absorbAll π RState.zero (keccakPaddingR.pad x) := by
  have hF : (fun s ↦ rEquiv.symm <$> π (rEquiv s)) =
      LeanVM.Rpm.lanePerm (fun k ↦ kEquivR.symm <$> π (kEquivR k)) := by
    funext s
    simp only [LeanVM.Rpm.lanePerm, Functor.map_map, rEquiv_apply]
    rfl
  rw [hF, UniStatement.keccak256StateWith, LeanVM.Rpm.absorbWith_lanePerm _ (x.length / rate) _ x rfl, LeanVM.Rpm.toRpm_zero,
    keccakPaddingR_pad, ← kEquivR_zero, absorbAll_kEquivR, Functor.map_map]
  generalize Common.absorbAll (fun k ↦ kEquivR.symm <$> π (kEquivR k)) Common.KState.zero
    (Common.toBlocks (Common.keccakPadBytes x)) = X
  simp only [rEquiv_symm_apply, Equiv.symm_apply_apply]

/-! ## The rate model's calls over `π` -/

/-- **The rate model's two calls over `π`**: Keccak-256's last sponge state read as digest and tail; Keccak-f
`= π`. -/
def keccakCallsROverQueryPermutation : QueryImpl KeccakCallsR (OracleComp Common.RandomPermutationOracles)
  | .inl x => rateOfState <$> UniStatement.keccak256StateWith Common.queryPermutation x
  | .inr s => Common.queryPermutation s

/-- The rate model's calls over the lazily sampled permutation. -/
noncomputable def keccakCallsROverRandomPermutation :
    QueryImpl KeccakCallsR (StateT (Common.PermutationEdges KeccakState) ProbComp) :=
  Common.lazyRandomPermutationOracles ∘ₛ keccakCallsROverQueryPermutation

theorem keccakCallsROver_comp_liftR :
    keccakCallsROverQueryPermutation ∘ₛ liftR = keccakCallsOverQueryPermutation := by
  funext t
  rcases t with x | s
  · simp only [QueryImpl.apply_compose, liftR, simulateQ_map, simulateQ_spec_query,
      keccakCallsROverQueryPermutation, Functor.map_map]
    show _ = keccak256With Common.queryPermutation x
    rw [UniStatement.keccak256With_eq]
    rfl
  · simp only [QueryImpl.apply_compose, liftR, simulateQ_spec_query, keccakCallsROverQueryPermutation]
    rfl

/-- **Over the digest, the rate model's calls are the two-oracle model's**: Keccak-256 reads the digest of its last
state. -/
theorem simulateQ_liftR {α : Type} (X : OracleComp KeccakCalls α) :
    simulateQ keccakCallsROverQueryPermutation (simulateQ liftR X) =
      simulateQ keccakCallsOverQueryPermutation X := by
  rw [← QueryImpl.simulateQ_compose, keccakCallsROver_comp_liftR]

theorem simulateQ_lazy_keccakCallsROver {α : Type} (X : OracleComp KeccakCallsR α) :
    simulateQ Common.lazyRandomPermutationOracles (simulateQ keccakCallsROverQueryPermutation X) =
      simulateQ keccakCallsROverRandomPermutation X := by
  rw [keccakCallsROverRandomPermutation, QueryImpl.simulateQ_compose]

theorem simulateQ_keccakCallsOver_liftR {α : Type} (X : OracleComp KeccakCalls α) :
    simulateQ keccakCallsOverRandomPermutation X =
      simulateQ keccakCallsROverRandomPermutation (simulateQ liftR X) := by
  rw [← simulateQ_lazy_keccakCallsROver, simulateQ_liftR, simulateQ_lazy_keccakCallsOverQueryPermutation]

/-! ## The transfer game's oracles on `RState` -/

/-- The adversary's oracles on `RState` (coins, `H`, `π`, `π⁻¹`). -/
abbrev RSpecR := Common.dSpec (List UInt8) RateBytes RState

/-- The two random oracles on `RState`, with coins. -/
abbrev HFSpecR := unifSpec + Common.hfSpec (List UInt8) RateBytes RState

/-- The two random oracles on `RState`. -/
abbrev HFSR := Common.hfSpec (List UInt8) RateBytes RState

/-- The game's oracles on `RState`. -/
abbrev D2SpecR := Common.dSpec2 (List UInt8) RateBytes RState

/-- **The real world on `RState`**: `H` the sponge over the lazily sampled permutation, `π`, `π⁻¹`, `F = π`. -/
noncomputable abbrev RRR : QueryImpl D2SpecR (StateT (Common.PermutationEdges RState) ProbComp) :=
  Common.realImpl keccakPaddingR RState.zero ∘ₛ Common.toOne

/-- The edges on `RState`, read on lanes. -/
abbrev projLogR : Common.PermutationEdges RState → Common.PermutationEdges KeccakState :=
  LeanVM.Rpm.logMap rEquiv.symm

/-- The rate model's calls on `RState`: Keccak-256's answer read through `rbij`, Keccak-f through `rEquiv`. -/
def toRHFR : QueryImpl KeccakCallsR (OracleComp HFSpecR)
  | .inl m => rbij <$> Common.hQuery (E := Rate0) (C := KCap) m
  | .inr s => rEquiv.symm <$> Common.fQuery (Msg := List UInt8) (rEquiv s)

/-- The setup's Keccak-256 calls on `RState`, the honest part before the adversary: the digest of `H`'s answer. -/
def toRHR : QueryImpl KeccakCalls (OracleComp (unifSpec + Common.roSpec (List UInt8) RateBytes))
  | .inl m => (fun r ↦ (rbij r).1) <$>
      (liftM ((unifSpec + Common.roSpec (List UInt8) RateBytes).query (.inr m)) : OracleComp _ RateBytes)
  | .inr s => pure s

/-- A permutation query of the adversary, read on `RState`. -/
def relPR : QueryImpl (Common.permutationOracleSpec KeccakState) (OracleComp RSpecR) := fun q ↦
  rEquiv.symm <$> (liftM (RSpecR.query (.inr (.inr (LeanVM.Rpm.mapQ rEquiv q)))) : OracleComp RSpecR RState)

/-- A query of the adversary (coins, `π`, `π⁻¹`), read on `RState`. -/
def relPCR : QueryImpl Common.RandomPermutationOracles (OracleComp RSpecR)
  | .inl n => (liftM (RSpecR.query (.inl n)) : OracleComp RSpecR (Fin (n + 1)))
  | .inr q => relPR q

/-- A permutation query of the adversary, read on `RState`, recorded in the transcript. -/
def logRelR : QueryImpl (Common.permutationOracleSpec KeccakState)
    (StateT PermutationTranscript (OracleComp RSpecR)) := fun q ↦
  StateT.mk fun T ↦ (fun a ↦ (a, T ++ [(q, a)])) <$> relPR q

/-- A query of the adversary read on `RState`, a permutation query recorded in the transcript. -/
def logRelCR : QueryImpl Common.RandomPermutationOracles (StateT PermutationTranscript (OracleComp RSpecR))
  | .inl n => StateT.mk fun T ↦
      (fun u ↦ (u, T)) <$> (liftM (RSpecR.query (.inl n)) : OracleComp RSpecR (Fin (n + 1)))
  | .inr q => logRelR q

/-! ## The real world on `RState` is the lazily sampled permutation of the lane states -/

theorem RRR_hfEmbed_toRHFR_H (m : List UInt8) :
    (RRR ∘ₛ Common.hfEmbed ∘ₛ toRHFR) (.inl m) =
      rbij <$> Common.spongeWith keccakPaddingR RState.zero
        (fun x ↦ Common.lazyRandomPermutation (.forward x)) m := by
  simp [toRHFR, LeanVM.Rpm.hq_eq, Common.hfEmbed, Common.toOne, Common.realImpl]

theorem RRR_hfEmbed_toRHFR_F (x : KeccakState) :
    (RRR ∘ₛ Common.hfEmbed ∘ₛ toRHFR) (.inr x) =
      rEquiv.symm <$> Common.lazyRandomPermutation (.forward (rEquiv x)) := by
  simp [toRHFR, LeanVM.Rpm.hq_eq, Common.hfEmbed, Common.toOne, Common.realImpl]

theorem RRR_advEmbed_perm (q : Common.PermutationQuery RState) :
    (RRR ∘ₛ Common.advEmbed) (.inr (.inr q)) = Common.lazyRandomPermutation q := by
  simp [Common.advEmbed, Common.toOne, Common.realImpl]

theorem RRR_advEmbed_coin (n : ℕ) :
    (RRR ∘ₛ Common.advEmbed) (.inl n) =
      (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
        StateT (Common.PermutationEdges RState) ProbComp (Fin (n + 1))) := by
  simp [Common.advEmbed, Common.toOne, Common.realImpl]

theorem absorbAll_relR {σ₁ σ₂ : Type} {proj : σ₁ → σ₂} (π₁ : RState → StateT σ₁ ProbComp RState)
    (π₂ : RState → StateT σ₂ ProbComp RState) (h : ∀ x, StRel proj (π₁ x) (π₂ x)) :
    ∀ (st : RState) (bs : List RBlock), StRel proj (Common.absorbAll π₁ st bs) (Common.absorbAll π₂ st bs)
  | st, [] => LeanVM.Rpm.StRel.pure proj st
  | st, B :: bs => by
    rw [Common.absorbAll_cons, Common.absorbAll_cons]
    exact LeanVM.Rpm.StRel.bind (h _) fun y ↦ absorbAll_relR π₁ π₂ h y bs

/-- A forward query on `RState` is the forward query on lanes, read on `RState`. -/
theorem fwd_relR (x : RState) :
    StRel projLogR (Common.lazyRandomPermutation (.forward x))
      (rEquiv <$> Common.lazyRandomPermutation (S := KeccakState) (.forward (rEquiv.symm x))) := by
  intro s
  obtain ⟨y, rfl⟩ := rEquiv.surjective x
  rw [Equiv.symm_apply_apply, StateT.run_map]
  have h := (LeanVM.Rpm.lazyPerm_relabel rEquiv (.forward y) s).map (Prod.map rEquiv id)
  rw [Functor.map_map] at h
  have e : (fun a ↦ Prod.map rEquiv id (Prod.map (⇑rEquiv.symm) (LeanVM.Rpm.logMap ⇑rEquiv.symm) a)) =
      Prod.map id projLogR := by
    funext p
    obtain ⟨a, b⟩ := p
    simp only [Prod.map_apply, Equiv.apply_symm_apply, id_eq]
  rw [e] at h
  exact h

/-- **The rate model's calls on `RState` in the real world are its calls over the lazily sampled permutation of the
lane states**, the edges read on lanes. -/
theorem post_relabelR {β : Type} (X : OracleComp KeccakCallsR β) (s : Common.PermutationEdges RState) :
    Prod.map id projLogR <$> (simulateQ (RRR ∘ₛ Common.hfEmbed ∘ₛ toRHFR) X).run s =ᵈ
      (simulateQ keccakCallsROverRandomPermutation X).run (projLogR s) := by
  refine Common.map_run_simulateQ_evalDistEq_of_inv _ _ (fun _ ↦ True) projLogR
    (fun _ _ _ _ _ ↦ trivial) (fun t s' _ ↦ ?_) X s trivial
  rcases t with m | x
  · rw [RRR_hfEmbed_toRHFR_H]
    have hR : keccakCallsROverRandomPermutation (.inl m) =
        rbij <$> (Common.SpState.out <$> Common.absorbAll
          (fun x ↦ rEquiv <$> Common.lazyRandomPermutation (S := KeccakState) (.forward (rEquiv.symm x)))
          RState.zero (keccakPaddingR.pad m)) := by
      have hP : (fun s ↦ rEquiv.symm <$> (rEquiv <$> Common.lazyRandomPermutation (S := KeccakState)
          (.forward (rEquiv.symm (rEquiv s))))) =
          fun s ↦ Common.lazyRandomPermutation (S := KeccakState) (.forward s) := by
        funext s
        rw [Equiv.symm_apply_apply, Functor.map_map]
        simp only [Equiv.symm_apply_apply, id_map']
      have hk := keccak256StateWith_rEquiv
        (fun x ↦ rEquiv <$> Common.lazyRandomPermutation (S := KeccakState) (.forward (rEquiv.symm x))) m
      rw [hP] at hk
      simp only [keccakCallsROverRandomPermutation, QueryImpl.apply_compose, keccakCallsROverQueryPermutation,
        simulateQ_map, UniStatement.keccak256StateWith, Common.simulateQ_absorbWith]
      have hq : (fun x ↦ simulateQ Common.lazyRandomPermutationOracles (Common.queryPermutation x)) =
          fun s ↦ Common.lazyRandomPermutation (S := KeccakState) (.forward s) := by
        funext s
        simp only [Common.queryPermutation, simulateQ_spec_query]
        rfl
      rw [hq, ← UniStatement.keccak256StateWith, hk]
      generalize Common.absorbAll
        (fun x ↦ rEquiv <$> Common.lazyRandomPermutation (S := KeccakState) (.forward (rEquiv.symm x)))
        RState.zero (keccakPaddingR.pad m) = X
      simp only [Functor.map_map, rateOfState_rEquiv_symm]
    rw [hR, Common.spongeWith]
    exact (LeanVM.Rpm.StRel.map (LeanVM.Rpm.StRel.map (absorbAll_relR
      (fun x ↦ Common.lazyRandomPermutation (.forward x))
      (fun x ↦ rEquiv <$> Common.lazyRandomPermutation (S := KeccakState) (.forward (rEquiv.symm x)))
      fwd_relR RState.zero (keccakPaddingR.pad m)) Common.SpState.out) rbij) s'
  · rw [RRR_hfEmbed_toRHFR_F]
    have hR : keccakCallsROverRandomPermutation (.inr x) = Common.lazyRandomPermutation (.forward x) := by
      simp only [keccakCallsROverRandomPermutation, QueryImpl.apply_compose, keccakCallsROverQueryPermutation,
        Common.queryPermutation, simulateQ_spec_query]
      rfl
    rw [hR]
    have h := LeanVM.Rpm.lazyPerm_relabel rEquiv (.forward x) s'
    simp only [LeanVM.Rpm.mapQ] at h
    rw [StateT.run_map, Functor.map_map]
    exact h

theorem post_relabelR' {β : Type} (X : OracleComp KeccakCallsR β) (s : Common.PermutationEdges RState) :
    (simulateQ (RRR ∘ₛ Common.hfEmbed ∘ₛ toRHFR) X).run' s =ᵈ
      (simulateQ keccakCallsROverRandomPermutation X).run' (projLogR s) := by
  have h := (post_relabelR X s).map Prod.fst
  simp only [Functor.map_map] at h
  simpa [StateT.run'_eq] using h

theorem realGame2_eqR {δ : Type} (D : OracleComp D2SpecR δ) :
    Common.realGame2 keccakPaddingR RState.zero D = (simulateQ RRR D).run' [] := by
  rw [Common.realGame2, Common.realGame, QueryImpl.simulateQ_compose]

/-- **The adversary on `RState` with its transcript, in the real world, is the adversary of the experiment** (coins
included), the permutation's edges read on lanes. -/
theorem adv_relabelCR {α : Type} (A : OracleComp Common.RandomPermutationOracles α)
    (s : Common.PermutationEdges RState) (T : PermutationTranscript) :
    (fun p ↦ (p.1.1, (projLogR p.2, p.1.2))) <$>
        (simulateQ (RRR ∘ₛ Common.advEmbed) ((simulateQ logRelCR A).run T)).run s =ᵈ
      (simulateQ loggedRandomPermutationOracles A).run (projLogR s, T) := by
  induction A using OracleComp.inductionOn generalizing s T with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact EvalDistEq.rfl
  | query_bind t k ih =>
    rcases t with n | q
    · simp only [StateT.run_bind, simulateQ_bind, simulateQ_spec_query, logRelCR,
        loggedRandomPermutationOracles, StateT.run_mk, bind_map_left, map_bind, RRR_advEmbed_coin]
      simp only [liftM, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind]
      exact EvalDistEq.bind_right _ fun u => ih u s T
    · have hrel : simulateQ (RRR ∘ₛ Common.advEmbed) (relPR q) =
          rEquiv.symm <$> Common.lazyRandomPermutation (LeanVM.Rpm.mapQ rEquiv q) := by
        rw [relPR, simulateQ_map, simulateQ_spec_query, RRR_advEmbed_perm]
      simp only [StateT.run_bind, simulateQ_bind, simulateQ_spec_query, logRelCR, logRelR,
        loggedRandomPermutationOracles, StateT.run_mk, hrel, bind_map_left, map_bind]
      calc _ =ᵈ ((Common.lazyRandomPermutation (LeanVM.Rpm.mapQ rEquiv q)).run s >>= fun a ↦
              (simulateQ loggedRandomPermutationOracles (k (rEquiv.symm a.1))).run
                (projLogR a.2, T ++ [(q, rEquiv.symm a.1)])) :=
            EvalDistEq.bind_right _ fun a ↦ ih _ _ _
        _ = ((Prod.map rEquiv.symm projLogR <$>
              (Common.lazyRandomPermutation (LeanVM.Rpm.mapQ rEquiv q)).run s) >>=
              fun a ↦ (simulateQ loggedRandomPermutationOracles (k a.1)).run
                (a.2, T ++ [(q, a.1)])) := by
            rw [bind_map_left]; rfl
        _ =ᵈ _ := EvalDistEq.bind_left (LeanVM.Rpm.lazyPerm_relabel rEquiv q s) _

/-- **A computation of Keccak-256 only, as the honest part before the adversary, is the computation lifted to the
rate model as the honest part after it.** -/
theorem hEmbed2_toRHR {α : Type} (X : OracleComp KeccakCalls α) (hX : HOnly X) :
    simulateQ (Common.hEmbed2 (E := Rate0) (C := KCap)) (simulateQ toRHR X) =
      simulateQ Common.hfEmbed (simulateQ toRHFR (simulateQ liftR X)) := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [LeanVM.Rpm.hOnly_query_bind] at hX
    rcases t with m | s
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, toRHR, liftR, bind_map_left, toRHFR]
      simp only [Common.hQuery, LeanVM.Rpm.hq_eq, simulateQ_spec_query, Common.hEmbed2,
        Common.hfEmbed]
      exact bind_congr fun u => ih _ (hX _)
    · exact hX.elim

/-! ## The duplex discipline in the rate model -/

/-- **The duplex discipline of a rate-model computation** (`LeanVM.Rpm.DuplexVm`): along every run, every direct
call of Keccak-f keeps lanes `16 … 24` of the zero state or of an earlier answer. -/
def DuplexVmR {α : Type} : OracleComp KeccakCallsR α → List KeccakState → Prop
  | .pure _, _ => True
  | .liftBind (.inr x) k, hist => AdmissibleVm hist x ∧ ∀ y, DuplexVmR (k y) (y :: hist)
  | .liftBind _ k, hist => ∀ u, DuplexVmR (k u) hist

theorem duplexVmR_query_bind {α : Type} (t : KeccakCallsR.Domain)
    (k : KeccakCallsR.Range t → OracleComp KeccakCallsR α) (h : List KeccakState) :
    DuplexVmR (liftM (KeccakCallsR.query t) >>= k) h ↔
      match t with
      | .inr x => AdmissibleVm h x ∧ ∀ y, DuplexVmR (k y) (y :: h)
      | .inl _ => ∀ u, DuplexVmR (k u) h := by
  rcases t with x | x <;> exact Iff.rfl

theorem duplexVmR_pure {α : Type} (a : α) (h : List KeccakState) :
    DuplexVmR (pure a : OracleComp KeccakCallsR α) h := trivial

theorem DuplexVmR.of_subset {α : Type} {X : OracleComp KeccakCallsR α} {h h' : List KeccakState}
    (hX : DuplexVmR X h) (hs : h ⊆ h') : DuplexVmR X h' := by
  induction X using OracleComp.inductionOn generalizing h h' with
  | pure a => trivial
  | query_bind t k ih =>
    rw [duplexVmR_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u) hs
    · exact ⟨LeanVM.Rpm.admissibleVm_mono hs hX.1, fun y ↦ ih y (hX.2 y) (List.cons_subset_cons y hs)⟩

/-- **Sequencing** (`LeanVM.Rpm.DuplexVm.bind`): a disciplined computation, then disciplined continuations from no
answer. -/
theorem DuplexVmR.bind {α β : Type} {X : OracleComp KeccakCallsR α} {f : α → OracleComp KeccakCallsR β}
    {h : List KeccakState} (hX : DuplexVmR X h) (hf : ∀ a, DuplexVmR (f a) []) : DuplexVmR (X >>= f) h := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => simpa using (hf a).of_subset (List.nil_subset _)
  | query_bind t k ih =>
    rw [bind_assoc]
    rw [duplexVmR_query_bind] at hX ⊢
    rcases t with x | x
    · exact fun u ↦ ih u (hX u)
    · exact ⟨hX.1, fun y ↦ ih y (hX.2 y)⟩

/-- A Keccak-256 call keeps the discipline. -/
theorem duplexVmR_query_inl_bind {α : Type} (x : List UInt8) (k : Digest × TailP → OracleComp KeccakCallsR α)
    (h : List KeccakState) (hk : ∀ u, DuplexVmR (k u) h) :
    DuplexVmR (liftM (KeccakCallsR.query (.inl x)) >>= k) h := hk

/-- **A wide draw keeps the discipline.** -/
theorem duplexVmR_hashR_bind {α : Type} (x : List UInt8) (k : QuotientRpm.Bytes32 × TailP → OracleComp KeccakCallsR α)
    (h : List KeccakState) (hk : ∀ u, DuplexVmR (k u) h) : DuplexVmR (Compose.hashR x >>= k) h := by
  rw [Compose.hashR, Compose.callKeccak256R, bind_assoc]
  exact fun u ↦ by simpa using hk _

/-- **A computation of the two-oracle model keeps the discipline in the rate model.** -/
theorem duplexVmR_liftR {α : Type} {X : OracleComp KeccakCalls α} {h : List KeccakState} (hX : DuplexVm X h) :
    DuplexVmR (simulateQ liftR X) h := by
  induction X using OracleComp.inductionOn generalizing h with
  | pure a => trivial
  | query_bind t k ih =>
    rw [LeanVM.Rpm.duplexVm_query_bind] at hX
    rcases t with x | s
    · simp only [simulateQ_bind, simulateQ_spec_query, liftR, bind_map_left]
      exact fun u ↦ ih _ (hX _)
    · simp only [simulateQ_bind, simulateQ_spec_query, liftR]
      exact ⟨hX.1, fun y ↦ ih y (hX.2 y)⟩

/-- An admissible call on lanes is admissible on `RState`. -/
theorem admissible_rEquiv {hist : List KeccakState} {x : KeccakState} (h : AdmissibleVm hist x) :
    Common.Admissible RState.zero keccakNFR (hist.map rEquiv) (rEquiv x) := by
  have hK := LeanVM.Rpm.admissible_toRpm h
  rcases hK with ⟨h1, h2⟩ | ⟨y, hy, h1, h2⟩
  · left
    refine ⟨h1, ?_⟩
    rw [rEquiv_apply, ← kEquivR_zero, blockTo_kEquivR, keccakNFR_iff]
    exact h2
  · right
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    refine ⟨rEquiv y', List.mem_map_of_mem hy', h1, ?_⟩
    rw [rEquiv_apply, rEquiv_apply, blockTo_kEquivR, keccakNFR_iff]
    exact h2

/-- **The discipline on lanes is the discipline on `RState`.** -/
theorem duplex_toRHFR {β : Type} (V : OracleComp KeccakCallsR β) (hist : List KeccakState) (hV : DuplexVmR V hist) :
    Common.Duplex RState.zero keccakNFR (simulateQ toRHFR V) (hist.map rEquiv) := by
  induction V using OracleComp.inductionOn generalizing hist with
  | pure a => trivial
  | query_bind t k ih =>
    rw [duplexVmR_query_bind] at hV
    rcases t with m | x
    · simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, toRHFR, bind_map_left]
      intro d
      exact ih _ hist (hV _)
    · simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, toRHFR, bind_map_left]
      refine ⟨admissible_rEquiv hV.1, fun y ↦ ?_⟩
      have := ih (rEquiv.symm y) (rEquiv.symm y :: hist) (hV.2 _)
      rw [List.map_cons, Equiv.apply_symm_apply] at this
      exact this

/-- A map keeps the discipline. -/
theorem duplex_mapR {α β : Type} (f : α → β) (X : OracleComp HFSpecR α) (hist : List RState)
    (hX : Common.Duplex RState.zero keccakNFR X hist) : Common.Duplex RState.zero keccakNFR (f <$> X) hist := by
  induction X using OracleComp.inductionOn generalizing hist with
  | pure a => trivial
  | query_bind t k ih =>
    rw [map_bind]
    rcases t with n | m | x
    · exact fun u ↦ ih u hist (hX u)
    · exact fun u ↦ ih u hist (hX u)
    · exact ⟨hX.1, fun y ↦ ih y (y :: hist) (hX.2 y)⟩

/-! ## The calls of `π` -/

/-- **The calls of `π` of a rate-model query**: a Keccak-256 hash of `n` bytes `⌊n / 136⌋ + 1`, Keccak-f one. -/
def hashBlocksR : KeccakCallsR.Domain → ℕ
  | .inl x => x.length / 136 + 1
  | .inr _ => 1

/-- **A computation of the two-oracle model makes as many calls of `π` in the rate model.** -/
theorem cost_liftR {α : Type} {X : OracleComp KeccakCalls α} {n : ℕ}
    (hX : Common.QueryCostAtMost X LeanVM.Rpm.hashBlocks n) :
    Common.QueryCostAtMost (simulateQ liftR X) hashBlocksR n := by
  refine LeanVM.Rpm.isWeightBound_simulateQ' liftR LeanVM.Rpm.hashBlocks hashBlocksR (fun t ↦ ?_) hX
  rcases t with x | s
  · exact Common.isWeightBound_map _ (Common.isWeightBound_query hashBlocksR (.inl x))
  · exact Common.isWeightBound_query hashBlocksR (.inr s)

/-- **A wide draw costs its blocks.** -/
theorem cost_hashR_bind {β : Type} (x : List UInt8) (k : QuotientRpm.Bytes32 × TailP → OracleComp KeccakCallsR β)
    (n : ℕ) (hx : x.length / 136 + 1 ≤ n)
    (hk : ∀ u, Common.QueryCostAtMost (k u) hashBlocksR (n - (x.length / 136 + 1))) :
    Common.QueryCostAtMost (Compose.hashR x >>= k) hashBlocksR n := by
  rw [Compose.hashR, Compose.callKeccak256R, bind_assoc]
  simp only [pure_bind]
  exact (Common.isWeightBound_query_bind_iff hashBlocksR (.inl x) _ n).mpr ⟨hx, fun u => hk _⟩

/-- The cost of the game's queries on `RState`. -/
abbrev gameCostR : D2SpecR.Domain → ℕ := Common.queryCost2 (Dg := RateBytes) keccakPaddingR

/-- The cost of the adversary's queries on `RState`. -/
abbrev advCostR : RSpecR.Domain → ℕ := Common.queryCost (Dg := RateBytes) (St := RState) keccakPaddingR

theorem keccakPaddingR_length (m : List UInt8) : (keccakPaddingR.pad m).length = m.length / 136 + 1 := by
  rw [keccakPaddingR_pad, List.length_map]
  exact Common.keccakPad_length m

theorem isWeightBound_advEmbedR {α : Type} {X : OracleComp RSpecR α} {n : ℕ}
    (hX : Common.QueryCostAtMost X advCostR n) :
    Common.QueryCostAtMost (simulateQ Common.advEmbed X) gameCostR n := by
  refine LeanVM.Rpm.isWeightBound_simulateQ' _ _ _ (fun t ↦ ?_) hX
  rcases t with k | m | q
  · exact Common.isWeightBound_query (spec := D2SpecR) gameCostR (.inl k)
  · exact Common.isWeightBound_query (spec := D2SpecR) gameCostR (.inr (.inl m))
  · exact Common.isWeightBound_query (spec := D2SpecR) gameCostR (.inr (.inr (.inl q)))

theorem isWeightBound_hfEmbed_toRHFR {β : Type} {V : OracleComp KeccakCallsR β} {n : ℕ}
    (hV : Common.QueryCostAtMost V hashBlocksR n) :
    Common.QueryCostAtMost (simulateQ Common.hfEmbed (simulateQ toRHFR V)) gameCostR n := by
  rw [← QueryImpl.simulateQ_compose]
  refine LeanVM.Rpm.isWeightBound_simulateQ' _ _ _ (fun t ↦ ?_) hV
  rcases t with m | x
  · simp only [QueryImpl.apply_compose, toRHFR, simulateQ_map]
    refine Common.isWeightBound_map _ ?_
    simp only [Common.hQuery, LeanVM.Rpm.hq_eq, simulateQ_spec_query]
    have := Common.isWeightBound_query (spec := D2SpecR) gameCostR (.inr (.inl m))
    rwa [show gameCostR (.inr (.inl m)) = hashBlocksR (.inl m) from keccakPaddingR_length m] at this
  · simp only [QueryImpl.apply_compose, toRHFR, simulateQ_map]
    refine Common.isWeightBound_map _ ?_
    simp only [Common.fQuery, LeanVM.Rpm.hq_eq, simulateQ_spec_query]
    exact Common.isWeightBound_query (spec := D2SpecR) gameCostR (.inr (.inr (.inr _)))

end UniKeccakSound.Rec4
