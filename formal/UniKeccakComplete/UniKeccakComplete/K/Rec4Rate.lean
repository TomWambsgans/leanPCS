-- Part of this repository. MIT OR Apache-2.0; see AGENTS.md. Follows leanerVM
-- (https://github.com/Verified-zkEVM/leanerVM, branch `mumbai`, commit 6175f1a0, MIT OR Apache-2.0):
-- `lean_vm/LeanVM/Protocol/Rpm/{Game,RpmRelabel,RomRelabel}.lean` (`toRHF`, `honestGame`, `rpmHonest_evalDistEq`,
-- `cmap`, `run'_toRHF`), `LeanVMRpm.lean` (`duplex_toRHF`, `isWeightBound_hfEmbed_toRHF`) and
-- `common/Common/Lanes.lean` (`keccak256With_rpm`, `absorbAll_rel`, `fwd_rel`), with Keccak-256's whole rate as the
-- hash's answer; and `formal/EndToEnd/Completeness/E2ECompleteness/Transfer.lean` (`rpm_le_rom`). The transfer itself
-- is `formal/UniKeccakSound/UniKeccakSound/Rec4/RateTransfer.lean`'s (`keccak256RateTransfer`).
import E2ECompleteness.Transfer
import UniKeccakSound.Rec4.RateTransfer
import UniStatement.Rec

/-!
# π1-rec4's calls: Keccak-256 with its whole rate, and the permutation

π1-rec4's wide draws (`UniStatement.sampleWide`) read Keccak-256's whole rate after its last permutation (136 bytes),
not its digest. Its honest computation is written over **`KeccakCallsW`**: `H` answers the rate (`RateB`, 136 bytes;
the digest is its first 32, `digestOfRate`), `F` is the permutation. In the random-permutation model `H` is the
sponge over `π` read on its whole rate (`keccakCallsWOverRandomPermutation`, `rateOfState`).

**`rpm_le_romW`**: an honest computation over `KeccakCallsW` that follows the duplex discipline (`DuplexW`) and makes
at most `N` block calls (`hashBlocksW`) is, against the random permutation, as against two random oracles (`H` with
136 uniform bytes, `F` a random function), up to `rpmError N = N² / 2^508`: `UniKeccakSound.Rec4`'s
`keccak256RateTransfer` (leanerVM's `transfer2` with the rate as `H`'s output) read on lanes, as leanerVM reads
`keccak256_transfer2` (`rpmHonestW_evalDistEq`: the experiment is the transfer's real world; `run'_toRHFW`: its ideal
world is the two random oracles of `KeccakCallsW`; `isWeightBound_hfEmbed_toRHFW`, `duplex_toRHFW`).
-/

open OracleComp OracleSpec
open LeanVM LeanVM.Rpm LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile (Bytes)
open UniKeccakSound.Rec4 (RateBytes Rate0 RState RBlock kBlockEquiv keccakPaddingR keccakNFR keccakNFR_iff
  keccak256RateTransfer)
open scoped ENNReal

set_option autoImplicit false

namespace UniKeccakComplete.Rec4

/-! ## The rate and the calls -/

/-- **Keccak-256's rate** after its last permutation: 136 bytes, the digest's 32 first. -/
abbrev RateB := Vector UInt8 136

/-- **π1-rec4's calls**: Keccak-256 answering its whole rate, and Keccak-f[1600]. -/
abbrev KeccakCallsW : OracleSpec (Bytes ⊕ KeccakState) := (Bytes →ₒ RateB) + (KeccakState →ₒ KeccakState)

/-- A call of the hash (its rate). -/
def callRate (x : Bytes) : OracleComp KeccakCallsW RateB := liftM (KeccakCallsW.query (.inl x))

/-- A call of the permutation. -/
def callFW (s : KeccakState) : OracleComp KeccakCallsW KeccakState := liftM (KeccakCallsW.query (.inr s))

/-! ## The byte state split as the whole rate -/

/-- A byte state as the rate's 136 bytes (and nothing), the capacity. -/
def toRS (x : Common.KState) : RState := (kBlockEquiv x.1, x.2)

/-- A rate-split state as a byte state. -/
def ofRS (y : RState) : Common.KState := (kBlockEquiv.symm y.1, y.2)

theorem toRS_ofRS (y : RState) : toRS (ofRS y) = y := by simp [toRS, ofRS]

/-- **The byte state and the rate-split state.** -/
def rsEquiv : Common.KState ≃ RState where
  toFun := toRS
  invFun := ofRS
  left_inv x := by simp [toRS, ofRS]
  right_inv y := by simp [toRS, ofRS]

/-- **The lane state and the rate-split state.** -/
def stateEquivR : KeccakState ≃ RState := stateEquiv.trans rsEquiv

/-- **The rate of a lane state**: its 136 first bytes, little-endian lanes `0 … 16`. -/
def rateOfState (st : KeccakState) : RateB := (stateEquivR st).1.1

/-- **The digest of a rate**: its first 32 bytes as four little-endian lanes. -/
def digestOfRate (r : RateB) : Digest := Digest.ofRpm (Vector.ofFn fun i : Fin 32 ↦ r[i.val])

/-! ## The models -/

/-- **π1-rec4's calls in the random-permutation model**: the rate of Keccak-256 over the random permutation, and the
permutation. -/
noncomputable def keccakCallsWOverRandomPermutation :
    QueryImpl KeccakCallsW (StateT (Common.PermutationEdges KeccakState) ProbComp)
  | .inl x => rateOfState <$> UniStatement.keccak256StateWith lazyPermutationForward x
  | .inr s => lazyPermutationForward s

/-- **π1-rec4's calls over `π`** in the model's oracles. -/
def keccakCallsWOverQueryPermutation : QueryImpl KeccakCallsW (OracleComp Common.RandomPermutationOracles)
  | .inl x => rateOfState <$> UniStatement.keccak256StateWith Common.queryPermutation x
  | .inr s => Common.queryPermutation s

/-- The lazy permutation after the calls over `π` answers them as the model does. -/
theorem lazy_comp_keccakCallsWOverQueryPermutation :
    Common.lazyRandomPermutationOracles ∘ₛ keccakCallsWOverQueryPermutation = keccakCallsWOverRandomPermutation := by
  funext t
  rcases t with x | s
  · show simulateQ Common.lazyRandomPermutationOracles
        (rateOfState <$> UniStatement.keccak256StateWith Common.queryPermutation x) =
      rateOfState <$> UniStatement.keccak256StateWith lazyPermutationForward x
    rw [simulateQ_map]
    congr 1
    unfold UniStatement.keccak256StateWith
    rw [Common.simulateQ_absorbWith]
    congr 1
    funext s
    simp only [Common.queryPermutation, simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose, keccakCallsWOverQueryPermutation, Common.queryPermutation,
      simulateQ_spec_query]
    rfl

/-- A computation over π1-rec4's calls over `π`, run against the lazy permutation, is its run with the model's
answers. -/
theorem simulateQ_lazy_keccakCallsWOverQueryPermutation {α : Type} (oa : OracleComp KeccakCallsW α) :
    simulateQ Common.lazyRandomPermutationOracles (simulateQ keccakCallsWOverQueryPermutation oa) =
      simulateQ keccakCallsWOverRandomPermutation oa := by
  rw [← QueryImpl.simulateQ_compose, lazy_comp_keccakCallsWOverQueryPermutation]

/-- The two random oracles of π1-rec4's calls. -/
noncomputable abbrev roW : QueryImpl KeccakCallsW (StateT KeccakCallsW.QueryCache ProbComp) :=
  KeccakCallsW.randomOracle

/-! ## The discipline and the cost -/

/-- **The duplex discipline** of a computation over π1-rec4's calls (leanerVM's `DuplexVm`): along every run, every
permutation call is admissible after the answers of the earlier ones (newest first). -/
def DuplexW {α : Type} : OracleComp KeccakCallsW α → List KeccakState → Prop
  | .pure _, _ => True
  | .liftBind (.inr x) k, hist => AdmissibleVm hist x ∧ ∀ y, DuplexW (k y) (y :: hist)
  | .liftBind _ k, hist => ∀ u, DuplexW (k u) hist

/-- The block calls of a query: a hash of `n` bytes `⌊n / 136⌋ + 1`, a permutation call one (leanerVM's
`hashBlocks`). -/
def hashBlocksW : KeccakCallsW.Domain → ℕ
  | .inl x => x.length / 136 + 1
  | .inr _ => 1

/-! ## The transfer game -/

/-- The two random oracles of `common` with the rate as `H`'s output, with coins. -/
abbrev HFSpecW := unifSpec + Common.hfSpec Bytes RateBytes RState

/-- The two random oracles of `common` with the rate as `H`'s output. -/
abbrev HFSW := Common.hfSpec Bytes RateBytes RState

/-- The game's oracles in `common`'s two-oracle model with the rate as `H`'s output. -/
abbrev D2SpecW := Common.dSpec2 Bytes RateBytes RState

/-- π1-rec4's calls read on rate-split byte states. -/
def toRHFW : QueryImpl KeccakCallsW (OracleComp HFSpecW)
  | .inl m => Common.hQuery (E := Rate0) (C := Common.KCap) m
  | .inr s => stateEquivR.symm <$> Common.fQuery (Msg := Bytes) (Dg := RateBytes) (stateEquivR s)

/-- **The completeness game**: nothing before, no adversary, then the honest computation with the hash and the
direct permutation calls. -/
def honestGameW {β : Type} (X : OracleComp KeccakCallsW β) : OracleComp D2SpecW β :=
  Common.rpmGame2 (pure ()) (fun _ ↦ (pure () : OracleComp (Common.dSpec Bytes RateBytes RState) Unit))
    (fun _ _ ↦ simulateQ toRHFW X)

/-! ## The sponge on rate-split states -/

theorem xor_toRBlock (a b : Common.KBlock) :
    Common.rxor (kBlockEquiv a) (kBlockEquiv b) = kBlockEquiv (Common.rxor a b) := by
  refine Prod.ext ?_ (UniKeccakSound.Rec4.rate0_eq _ _)
  apply Vector.ext
  intro i hi
  show (Vector.zipWith (· ^^^ ·) (kBlockEquiv a).1 (kBlockEquiv b).1)[i] = (kBlockEquiv (Common.rxor a b)).1[i]
  simp only [Vector.getElem_zipWith]
  show (UniKeccakSound.Rec4.toRBlock a).1[i] ^^^ (UniKeccakSound.Rec4.toRBlock b).1[i] =
    (UniKeccakSound.Rec4.toRBlock (Common.rxor a b)).1[i]
  simp only [UniKeccakSound.Rec4.toRBlock, Vector.getElem_ofFn]
  split
  · show a.1[i] ^^^ b.1[i] = (Vector.zipWith (· ^^^ ·) a.1 b.1)[i]
    simp
  · show a.2[i - 32] ^^^ b.2[i - 32] = (Vector.zipWith (· ^^^ ·) a.2 b.2)[i - 32]
    simp

theorem absorb_toRS (x : Common.KState) (B : Common.KBlock) :
    Common.absorb (toRS x) (kBlockEquiv B) = toRS (Common.absorb x B) := by
  simp only [Common.absorb, toRS, xor_toRBlock]

theorem toRS_zero : toRS Common.KState.zero = UniKeccakSound.Rec4.RState.zero := by
  refine Prod.ext (Prod.ext ?_ (UniKeccakSound.Rec4.rate0_eq _ _)) rfl
  apply Vector.ext
  intro i hi
  simp only [toRS, kBlockEquiv, Equiv.coe_fn_mk, UniKeccakSound.Rec4.toRBlock, Common.KState.zero,
    UniKeccakSound.Rec4.RState.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  split <;> rfl

section Sponge

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- **Absorbing commutes with the rate split.** -/
theorem absorbAll_toRS (π : RState → m RState) :
    ∀ (x : Common.KState) (bs : List Common.KBlock),
      Common.absorbAll (fun y ↦ ofRS <$> π (toRS y)) x bs = ofRS <$> Common.absorbAll π (toRS x) (bs.map kBlockEquiv)
  | x, [] => by simp [Common.absorbAll, ofRS, toRS]
  | x, B :: bs => by
    simp only [Common.absorbAll, List.map_cons, absorb_toRS, bind_map_left, map_bind]
    refine bind_congr fun y ↦ ?_
    rw [absorbAll_toRS π _ bs, toRS_ofRS]

/-- A permutation of the rate-split states, read on lanes. -/
def lanePermR (π : RState → m RState) : KeccakState → m KeccakState :=
  fun s ↦ stateEquivR.symm <$> π (stateEquivR s)

theorem lanePermR_eq (π : RState → m RState) :
    lanePermR π = lanePerm (fun y ↦ ofRS <$> π (toRS y)) := by
  funext s
  simp only [lanePermR, lanePerm, Functor.map_map]
  rfl

/-- **Keccak-256's last state over a permutation of the rate-split states**: the rate-split sponge's state, read on
lanes. -/
theorem keccak256StateWith_rateSplit (π : RState → m RState) (data : List UInt8) :
    UniStatement.keccak256StateWith (lanePermR π) data =
      stateEquivR.symm <$> Common.absorbAll π UniKeccakSound.Rec4.RState.zero (keccakPaddingR.pad data) := by
  rw [UniStatement.keccak256StateWith, lanePermR_eq, absorbWith_lanePerm _ (data.length / rate) _ data rfl,
    toRpm_zero, absorbAll_toRS, toRS_zero, Functor.map_map]
  rfl

theorem rateOfState_comp_symm : (fun a ↦ rateOfState (stateEquivR.symm a)) = Common.SpState.out := by
  funext y
  show (stateEquivR (stateEquivR.symm y)).1.1 = y.1.1
  rw [Equiv.apply_symm_apply]

/-- **The rate of Keccak-256 over a permutation of the rate-split states** is the rate-split sponge. -/
theorem rate_keccak256StateWith (π : RState → m RState) (data : List UInt8) :
    rateOfState <$> UniStatement.keccak256StateWith (lanePermR π) data =
      Common.spongeWith keccakPaddingR UniKeccakSound.Rec4.RState.zero π data := by
  rw [keccak256StateWith_rateSplit, Functor.map_map, Common.spongeWith, rateOfState_comp_symm]

end Sponge

/-! ## The real world -/

/-- The real world of the rate's two-oracle model. -/
noncomputable abbrev RRW : QueryImpl D2SpecW (StateT (Common.PermutationEdges RState) ProbComp) :=
  Common.realImpl keccakPaddingR UniKeccakSound.Rec4.RState.zero ∘ₛ Common.toOne

theorem RRW_hfEmbed_toRHFW_F (x : KeccakState) :
    (RRW ∘ₛ Common.hfEmbed ∘ₛ toRHFW) (.inr x) =
      stateEquivR.symm <$> Common.lazyRandomPermutation (.forward (stateEquivR x)) := by
  simp [toRHFW, hq_eq, Common.hfEmbed, Common.toOne, Common.realImpl]

theorem RRW_hfEmbed_toRHFW_H (m : Bytes) :
    (RRW ∘ₛ Common.hfEmbed ∘ₛ toRHFW) (.inl m) =
      Common.spongeWith keccakPaddingR UniKeccakSound.Rec4.RState.zero
        (fun x ↦ Common.lazyRandomPermutation (.forward x)) m := by
  simp [toRHFW, hq_eq, Common.hfEmbed, Common.toOne, Common.realImpl]

/-- The edges of a rate-split log, read on lanes. -/
abbrev projLogR : Common.PermutationEdges RState → Common.PermutationEdges KeccakState := logMap stateEquivR.symm

theorem absorbAll_relR {σ₁ σ₂ : Type} {proj : σ₁ → σ₂} (π₁ : RState → StateT σ₁ ProbComp RState)
    (π₂ : RState → StateT σ₂ ProbComp RState) (h : ∀ x, StRel proj (π₁ x) (π₂ x)) :
    ∀ (st : RState) (bs : List RBlock), StRel proj (Common.absorbAll π₁ st bs) (Common.absorbAll π₂ st bs)
  | st, [] => StRel.pure proj st
  | st, B :: bs => by
    simp only [Common.absorbAll]
    exact StRel.bind (h _) fun y ↦ absorbAll_relR π₁ π₂ h y bs

/-- A forward query on rate-split states is the forward query on lanes, read on rate-split states. -/
theorem fwd_relR (x : RState) :
    StRel projLogR (Common.lazyRandomPermutation (.forward x))
      (stateEquivR <$> lazyPermutationForward (stateEquivR.symm x)) := by
  intro s
  have h := (lazyPerm_relabel stateEquivR (.forward (stateEquivR.symm x)) s).map (Prod.map stateEquivR id)
  have hq : mapQ stateEquivR (.forward (stateEquivR.symm x)) = .forward x := by
    show Common.PermutationQuery.forward (stateEquivR (stateEquivR.symm x)) = .forward x
    rw [Equiv.apply_symm_apply]
  rw [hq, Functor.map_map] at h
  have e : (fun a ↦ Prod.map stateEquivR id (Prod.map (⇑stateEquivR.symm) (logMap ⇑stateEquivR.symm) a)) =
      Prod.map id projLogR := by
    funext p
    exact Prod.ext (stateEquivR.apply_symm_apply p.1) rfl
  rw [StateT.run_map]
  exact e ▸ h

/-- `π` on lanes is the lane reading of `π` on rate-split states. -/
theorem lazyPermutationForward_eq_lanePermR :
    (lazyPermutationForward : KeccakState → StateT (Common.PermutationEdges KeccakState) ProbComp KeccakState) =
      lanePermR (fun x ↦ stateEquivR <$> lazyPermutationForward (stateEquivR.symm x)) := by
  funext s
  simp only [lanePermR, Functor.map_map, Equiv.symm_apply_apply, id_map']

/-- **The honest computation's queries on rate-split states in the real world are its queries in the
random-permutation model**, the permutation's edges read on lanes. -/
theorem post_relabelW {β : Type} (X : OracleComp KeccakCallsW β) (s : Common.PermutationEdges RState) :
    Prod.map id projLogR <$> (simulateQ (RRW ∘ₛ Common.hfEmbed ∘ₛ toRHFW) X).run s =ᵈ
      (simulateQ keccakCallsWOverRandomPermutation X).run (projLogR s) := by
  refine Common.map_run_simulateQ_evalDistEq_of_inv _ _ (fun _ ↦ True) projLogR
    (fun _ _ _ _ _ ↦ trivial) (fun t s' _ ↦ ?_) X s trivial
  rcases t with m | x
  · rw [RRW_hfEmbed_toRHFW_H]
    change _ =ᵈ (rateOfState <$> UniStatement.keccak256StateWith lazyPermutationForward m).run _
    rw [lazyPermutationForward_eq_lanePermR, rate_keccak256StateWith, Common.spongeWith, Common.spongeWith]
    exact (StRel.map (absorbAll_relR _ _ fwd_relR _ _) _) s'
  · rw [RRW_hfEmbed_toRHFW_F]
    change _ =ᵈ (Common.lazyRandomPermutation (.forward x)).run _
    have h := lazyPerm_relabel stateEquivR (.forward x) s'
    simp only [mapQ] at h
    rw [StateT.run_map, Functor.map_map]
    exact h

theorem realGame2W_eq {δ : Type} (D : OracleComp D2SpecW δ) :
    Common.realGame2 keccakPaddingR UniKeccakSound.Rec4.RState.zero D = (simulateQ RRW D).run' [] := by
  rw [Common.realGame2, Common.realGame, QueryImpl.simulateQ_compose]

/-- **An honest computation over π1-rec4's calls in the random-permutation model is the real world of its game.** -/
theorem rpmHonestW_evalDistEq {β : Type} (X : OracleComp KeccakCallsW β) :
    (simulateQ keccakCallsWOverRandomPermutation X).run' [] =ᵈ
      Common.realGame2 keccakPaddingR UniKeccakSound.Rec4.RState.zero (honestGameW X) := by
  rw [realGame2W_eq, honestGameW, Common.rpmGame2]
  simp only [simulateQ_pure, pure_bind]
  have h := (post_relabelW X []).map Prod.fst
  simp only [Functor.map_map] at h
  have h' : (simulateQ (RRW ∘ₛ Common.hfEmbed ∘ₛ toRHFW) X).run' [] =ᵈ
      (simulateQ keccakCallsWOverRandomPermutation X).run' [] := by
    simpa [StateT.run'_eq, projLogR, logMap] using h
  refine h'.symm.trans ?_
  simp only [QueryImpl.simulateQ_compose]
  exact EvalDistEq.rfl

/-! ## The ideal world -/

/-- A cache of the rate's byte oracles, read on lanes. -/
def cmapW (c : HFSW.QueryCache) : KeccakCallsW.QueryCache :=
  QueryCache.ofFn fun
    | .inl m => c (.inl m)
    | .inr s => (c (.inr (stateEquivR s))).map stateEquivR.symm

@[simp] theorem cmapW_inl (c : HFSW.QueryCache) (m : Bytes) : cmapW c (.inl m) = c (.inl m) := rfl

@[simp] theorem cmapW_inr (c : HFSW.QueryCache) (s : KeccakState) :
    cmapW c (.inr s) = (c (.inr (stateEquivR s))).map stateEquivR.symm := rfl

theorem cmapW_empty : cmapW ∅ = ∅ := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m | s <;> rfl

theorem cmapW_cacheQuery_inl (c : HFSW.QueryCache) (m : Bytes) (u : RateBytes) :
    cmapW (c.cacheQuery (.inl m) u) = (cmapW c).cacheQuery (.inl m) u := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m' | s
  · by_cases h : m' = m
    · subst h; simp
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h), cmapW_inl, cmapW_inl,
        QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp), cmapW_inr, cmapW_inr,
      QueryCache.cacheQuery_of_ne _ _ (by simp)]

theorem cmapW_cacheQuery_inr (c : HFSW.QueryCache) (x : KeccakState) (u : RState) :
    cmapW (c.cacheQuery (.inr (stateEquivR x)) u) = (cmapW c).cacheQuery (.inr x) (stateEquivR.symm u) := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m | s
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp), cmapW_inl, cmapW_inl,
      QueryCache.cacheQuery_of_ne _ _ (by simp)]
  · by_cases h : s = x
    · subst h
      rw [cmapW_inr, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
      rfl
    · have h' : stateEquivR s ≠ stateEquivR x := fun e ↦ h (stateEquivR.injective e)
      rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h), cmapW_inr, cmapW_inr,
        QueryCache.cacheQuery_of_ne _ _ (by simpa using h')]

theorem step_toRHFW (t : KeccakCallsW.Domain) (c : HFSW.QueryCache) :
    Prod.map id cmapW <$> ((HFSW.romImpl ∘ₛ toRHFW) t).run c =ᵈ (KeccakCallsW.randomOracle t).run (cmapW c) := by
  rcases t with m | x
  · rw [QueryImpl.apply_compose]
    simp only [toRHFW, Common.run_hq]
    rw [randomOracle.run_eq, cmapW_inl]
    rcases h : c (.inl m) with _ | u
    · simp only [Common.roStep_of_none h, map_bind, map_pure, Prod.map, id, cmapW_cacheQuery_inl]
      exact EvalDistEq.rfl
    · simp only [Common.roStep_of_some h, map_pure]
      exact EvalDistEq.rfl
  · rw [QueryImpl.apply_compose]
    simp only [toRHFW, simulateQ_map, StateT.run_map, Common.run_hq, Functor.map_map]
    rw [randomOracle.run_eq, cmapW_inr]
    rcases h : c (.inr (stateEquivR x)) with _ | u
    · simp only [Common.roStep_of_none h, Option.map_none, map_bind, map_pure, Prod.map, id,
        cmapW_cacheQuery_inr]
      refine EvalDistEq.trans ?_ (EvalDistEq.bind_left
        (SampleableType.map_uniformSample_evalDistEq_of_bijective stateEquivR.symm.bijective)
        (fun d ↦ (pure (d, (cmapW c).cacheQuery (.inr x) d) : ProbComp _)))
      rw [bind_map_left]
      exact EvalDistEq.rfl
    · simp only [Common.roStep_of_some h, Option.map_some, map_pure]
      exact EvalDistEq.rfl

/-- **The ideal world**: the honest computation's queries read on rate-split states, against `common`'s two random
oracles, give its outputs against π1-rec4's two random oracles, the caches related by `cmapW`. -/
theorem run'_toRHFW {β : Type} (V : OracleComp KeccakCallsW β) (c : HFSW.QueryCache) :
    (simulateQ HFSW.romImpl (simulateQ toRHFW V)).run' c =ᵈ (simulateQ KeccakCallsW.randomOracle V).run' (cmapW c) := by
  rw [← QueryImpl.simulateQ_compose]
  exact Common.run'_simulateQ_evalDistEq_of_inv _ _ (fun _ ↦ True) cmapW
    (fun _ _ _ _ _ ↦ trivial) (fun t c _ ↦ step_toRHFW t c) V c trivial

/-! ## The cost and the discipline of the game -/

/-- The cost of the game's queries (`Common.queryCost2` with the rate's padding). -/
abbrev gameCostW : D2SpecW.Domain → ℕ := Common.queryCost2 (Dg := RateBytes) keccakPaddingR

theorem padR_length (m : Bytes) : (keccakPaddingR.pad m).length = m.length / 136 + 1 := by
  show ((Common.keccakPadding.pad m).map kBlockEquiv).length = _
  rw [List.length_map, Common.keccakPad_length]

theorem isWeightBound_hfEmbed_toRHFW {β : Type} {V : OracleComp KeccakCallsW β} {n : ℕ}
    (hV : Common.QueryCostAtMost V hashBlocksW n) :
    Common.QueryCostAtMost (simulateQ Common.hfEmbed (simulateQ toRHFW V)) gameCostW n := by
  rw [← QueryImpl.simulateQ_compose]
  refine isWeightBound_simulateQ' _ _ _ (fun t ↦ ?_) hV
  rcases t with m | x
  · simp only [QueryImpl.apply_compose, toRHFW]
    simp only [Common.hQuery, hq_eq, simulateQ_spec_query]
    have := Common.isWeightBound_query (spec := D2SpecW) gameCostW (.inr (.inl m))
    rwa [show gameCostW (.inr (.inl m)) = hashBlocksW (.inl m) from padR_length m] at this
  · simp only [QueryImpl.apply_compose, toRHFW, simulateQ_map]
    refine Common.isWeightBound_map _ ?_
    simp only [Common.fQuery, hq_eq, simulateQ_spec_query]
    exact Common.isWeightBound_query (spec := D2SpecW) gameCostW (.inr (.inr (.inr _)))

theorem blockTo_toRS (a b : Common.KState) :
    Common.blockTo (toRS a) (toRS b) = kBlockEquiv (Common.blockTo a b) := by
  simp only [Common.blockTo, toRS, xor_toRBlock]

/-- An admissible permutation call on lanes is admissible on rate-split states. -/
theorem admissible_toRS {hist : List KeccakState} {x : KeccakState} (h : AdmissibleVm hist x) :
    Common.Admissible UniKeccakSound.Rec4.RState.zero keccakNFR (hist.map stateEquivR) (stateEquivR x) := by
  rcases admissible_toRpm h with ⟨h1, h2⟩ | ⟨y, hy, h1, h2⟩
  · left
    refine ⟨h1.trans ?_, ?_⟩
    · rw [← toRS_zero]; rfl
    · rw [← toRS_zero]
      show keccakNFR (Common.blockTo (toRS Common.KState.zero) (toRS (KState.toRpm x)))
      rw [blockTo_toRS, keccakNFR_iff]
      exact h2
  · right
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    refine ⟨stateEquivR y', List.mem_map_of_mem hy', h1, ?_⟩
    show keccakNFR (Common.blockTo (toRS (KState.toRpm y')) (toRS (KState.toRpm x)))
    rw [blockTo_toRS, keccakNFR_iff]
    exact h2

/-- **The discipline on lanes is the discipline on rate-split states.** -/
theorem duplex_toRHFW {β : Type} (V : OracleComp KeccakCallsW β) (hist : List KeccakState) (hV : DuplexW V hist) :
    Common.Duplex UniKeccakSound.Rec4.RState.zero keccakNFR (simulateQ toRHFW V) (hist.map stateEquivR) := by
  induction V using OracleComp.inductionOn generalizing hist with
  | pure a => trivial
  | query_bind t k ih =>
    rcases t with m | x
    · simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, toRHFW]
      intro d
      exact ih _ hist (hV _)
    · simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, toRHFW, bind_map_left]
      refine ⟨admissible_toRS hV.1, fun y ↦ ?_⟩
      have := ih (stateEquivR.symm y) (stateEquivR.symm y :: hist) (hV.2 _)
      rw [List.map_cons, Equiv.apply_symm_apply] at this
      exact this

/-! ## The transfer -/

/-- **The random-permutation model is the rate's two-call random-oracle model, up to `rpmError N`**, for an honest
computation over π1-rec4's calls that follows the duplex discipline and makes at most `N` block calls: any event of
its output. -/
theorem rpm_le_romW {β : Type} (G : OracleComp KeccakCallsW β) {N : ℕ} (hd : DuplexW G [])
    (hN : Common.QueryCostAtMost G hashBlocksW N) (q : β → Prop) {ε : ℝ≥0∞}
    (hrom : Pr{let v ← (simulateQ KeccakCallsW.randomOracle G).run' ∅}[q v] ≤ ε) :
    Pr{let v ← (simulateQ keccakCallsWOverRandomPermutation G).run' []}[q v] ≤ ε + rpmError N := by
  have hG : Common.QueryCostAtMost (honestGameW G) gameCostW N := by
    rw [honestGameW, Common.rpmGame2, simulateQ_pure, pure_bind, simulateQ_pure, pure_bind]
    exact isWeightBound_hfEmbed_toRHFW hN
  rw [(rpmHonestW_evalDistEq _).prEvent_eq, honestGameW]
  obtain ⟨h1, -⟩ := keccak256RateTransfer (pure ())
    (fun _ ↦ (pure () : OracleComp (Common.dSpec Bytes RateBytes RState) Unit)) (fun _ _ ↦ simulateQ toRHFW G)
    (fun _ _ ↦ duplex_toRHFW _ [] hd) N hG q
  refine h1.trans (add_le_add (le_of_eq_of_le ?_ hrom) le_rfl)
  have e1 : Common.romRun2 (simulateQ (Common.hInF (E := Rate0) (C := Common.KCap)) (pure ()) >>= fun x ↦
      Common.advS2 keccakPaddingR UniKeccakSound.Rec4.RState.zero
        ((fun _ ↦ (pure () : OracleComp (Common.dSpec Bytes RateBytes RState) Unit)) x) >>= fun a ↦
          (fun _ _ ↦ simulateQ toRHFW G) x a) =
      (simulateQ HFSW.romImpl (simulateQ toRHFW G)).run' ∅ := by
    simp [Common.romRun2, Common.advS2]
  rw [e1, (run'_toRHFW _ _).prEvent_eq, cmapW_empty]

end UniKeccakComplete.Rec4

/-- info: 'UniKeccakComplete.Rec4.rpm_le_romW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms UniKeccakComplete.Rec4.rpm_le_romW
